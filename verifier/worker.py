"""Opt-in, same-UID RPC wrapper for the trusted persistent certificate checker."""
from __future__ import annotations

import argparse
import errno
import hashlib
import json
import math
import os
from pathlib import Path
import re
import resource
import selectors
import signal
import socket
import stat
import struct
import subprocess
import sys
import time

if __package__:
    from .cache import context_digest
else:
    from cache import context_digest

WALL_SECONDS = 4 * 3600
REQUEST_LIMIT = 16 * 1024
REPORT_LIMIT = 1024 * 1024
INPUT_LIMIT = 512 * 1024**2
DIGEST = re.compile(r"[0-9a-f]{64}\Z")
REQUEST_ID = re.compile(r"[0-9a-f]{32}\Z")


class WorkerError(ValueError):
    pass


def _require_linux() -> None:
    if sys.platform != "linux":
        raise WorkerError("persistent certificate workers require Linux with enforced memory limits")


def _peer_uid(connection: socket.socket) -> int:
    if hasattr(connection, "getpeereid"):
        return connection.getpeereid()[0]
    if sys.platform == "darwin":
        # Python does not expose getpeereid on every macOS build.
        import ctypes
        uid, gid = ctypes.c_uint(), ctypes.c_uint()
        libc = ctypes.CDLL(None, use_errno=True)
        if libc.getpeereid(connection.fileno(), ctypes.byref(uid), ctypes.byref(gid)) != 0:
            raise WorkerError("cannot authenticate Unix peer")
        return uid.value
    if sys.platform == "linux" and hasattr(socket, "SO_PEERCRED"):
        return struct.unpack("3i", connection.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))[1]
    raise WorkerError("Unix peer authentication is unsupported")


def _json(data: bytes) -> dict:
    def unique(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise WorkerError("duplicate JSON field")
            value[key] = item
        return value
    try:
        value = json.loads(data, object_pairs_hook=unique,
                           parse_constant=lambda _: (_ for _ in ()).throw(WorkerError("invalid JSON constant")))
    except (ValueError, UnicodeError, RecursionError) as error:
        raise WorkerError("invalid JSON message") from error
    if not isinstance(value, dict):
        raise WorkerError("JSON message must be an object")
    return value


def _send(connection: socket.socket, message: dict) -> None:
    data = json.dumps(message, separators=(",", ":"), allow_nan=False).encode() + b"\n"
    if len(data) > REPORT_LIMIT:
        raise WorkerError("report exceeds size limit")
    connection.sendall(data)


def _receive(connection: socket.socket, limit: int, deadline: float) -> dict:
    data = bytearray()
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise WorkerError("RPC timed out")
        connection.settimeout(remaining)
        chunk = connection.recv(min(65536, limit + 1 - len(data)))
        if not chunk:
            raise WorkerError("RPC closed before a complete message")
        data.extend(chunk)
        if len(data) > limit:
            raise WorkerError("message exceeds size limit")
        if b"\n" in data:
            if not data.endswith(b"\n") or data.count(b"\n") != 1:
                raise WorkerError("unexpected data after message")
            return _json(bytes(data[:-1]))


def _path(value: str, *, directory: bool = False, own: bool = True, limit: int = INPUT_LIMIT) -> Path:
    if not isinstance(value, str) or not value or "\x00" in value:
        raise WorkerError("invalid input path")
    path = Path(value)
    if not path.is_absolute() or path.resolve() != path:
        raise WorkerError("input paths must be absolute, canonical, and nonsymlink")
    info = path.lstat()
    if directory:
        if not stat.S_ISDIR(info.st_mode):
            raise WorkerError("trusted root must be a directory")
    elif not stat.S_ISREG(info.st_mode) or info.st_size > limit:
        raise WorkerError("input must be a bounded regular file")
    if info.st_uid not in ({os.getuid()} if own else {0, os.getuid()}):
        raise WorkerError("input has an unexpected owner")
    if info.st_mode & 0o022:
        raise WorkerError("input must not be writable by other users")
    return path


def _digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _context(trusted: Path) -> tuple[str, Path]:
    """Use the verifier's actual tool/source identities without importing verify.py."""
    env_path = _path(str(trusted / "verifier" / ".tools" / "env.sh"), own=False, limit=REPORT_LIMIT)
    tools = {}
    for line in env_path.read_text().splitlines():
        if line.startswith("export ") and "=" in line:
            name, value = line[7:].split("=", 1)
            if name in tools:
                raise WorkerError("duplicate trusted tool field")
            tools[name] = value.strip().strip('"')
    for name in ("COMPARATOR_BIN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_LANDRUN", "COMPARATOR_CERTIFICATE_CHECK"):
        path = Path(tools.get(name, ""))
        if not path.is_absolute():
            raise WorkerError(f"{name} must name an absolute installed executable")
        path = _path(str(path.resolve(strict=True)), own=False)
        if not os.access(path, os.X_OK):
            raise WorkerError(f"{name} must be executable")
    return context_digest(trusted, tools), Path(tools["COMPARATOR_CERTIFICATE_CHECK"]).resolve(strict=True)


def _request(request: dict) -> dict:
    if set(request) != {"id", "config", "trusted", "candidate", "fresh_kernel"}:
        raise WorkerError("request fields must be id, config, trusted, candidate, fresh_kernel")
    if not isinstance(request["id"], str) or not REQUEST_ID.fullmatch(request["id"]):
        raise WorkerError("request id must be a supervisor-generated UUID hex string")
    if type(request["fresh_kernel"]) is not bool:
        raise WorkerError("fresh_kernel must be a boolean")
    for key in ("config", "trusted", "candidate"):
        _path(request[key], limit=REPORT_LIMIT if key == "config" else INPUT_LIMIT)
    return request


def _report(report: dict, request_id: str) -> dict:
    if report.get("id") != request_id or not isinstance(report.get("status"), str) or report["status"] not in {"verified", "rejected", "error"}:
        raise WorkerError("checker returned a mismatched id or invalid status")
    if report["status"] == "verified" and report.get("error") is not None:
        raise WorkerError("checker acceptance contains an error")
    return report


def check(socket_path: str | Path, request: dict, expected_checker_digest: str | None = None, *,
          expected_base_digest: str | None = None, expected_context_digest: str | None = None,
          timeout: float = WALL_SECONDS) -> dict:
    """Authenticate the worker and pin its executable before sending a check request."""
    if not isinstance(expected_checker_digest, str) or not DIGEST.fullmatch(expected_checker_digest):
        raise WorkerError("a pinned checker SHA-256 digest is required")
    if not math.isfinite(timeout) or timeout <= 0:
        raise WorkerError("timeout must be positive")
    _request(request)
    path = Path(socket_path)
    _private_directory(path.parent)
    info = path.lstat()
    if not stat.S_ISSOCK(info.st_mode) or info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) != 0o600:
        raise WorkerError("worker socket is not private and owned by this UID")
    deadline = time.monotonic() + timeout
    try:
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as connection:
            connection.settimeout(timeout)
            connection.connect(str(path))
            if _peer_uid(connection) != os.getuid():
                raise WorkerError("worker belongs to another UID")
            identity = _receive(connection, REQUEST_LIMIT, deadline)
            if type(identity.get("protocol")) is not int or identity["protocol"] != 1:
                raise WorkerError("unsupported worker protocol")
            for key, expected in (("checker_digest", expected_checker_digest),
                                  ("base_digest", expected_base_digest),
                                  ("context_digest", expected_context_digest)):
                if not isinstance(identity.get(key), str) or not DIGEST.fullmatch(identity[key]):
                    raise WorkerError("invalid worker identity")
                if expected is not None and identity[key] != expected:
                    raise WorkerError(f"worker {key} does not match pinned identity")
            data = json.dumps(request, separators=(",", ":")).encode() + b"\n"
            if len(data) > REQUEST_LIMIT:
                raise WorkerError("request exceeds size limit")
            connection.sendall(data)
            return _report(_receive(connection, REPORT_LIMIT, deadline), request["id"])
    except (OSError, TimeoutError) as error:
        raise WorkerError(f"worker RPC failed: {error}") from error


def _private_directory(path: Path, *, create: bool = False) -> None:
    if not path.is_absolute() or path.resolve() != path:
        raise WorkerError("socket directory must be absolute, canonical, and nonsymlink")
    if create:
        path.mkdir(mode=0o700, exist_ok=True)
    info = path.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) != 0o700:
        raise WorkerError("socket directory must be owned by this UID with mode 0700")


class Checker:
    def __init__(self, executable: Path, base: Path, trusted: Path, digest: str,
                 base_digest: str, memory_bytes: int):
        self.executable, self.base, self.trusted = executable, base, trusted
        self.digest, self.base_digest, self.memory_bytes = digest, base_digest, memory_bytes
        self.process = None

    def close(self) -> None:
        if self.process is not None:
            process, self.process = self.process, None
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=5)
            process.stdin.close()
            process.stdout.close()

    def run(self, request: dict, timeout: float) -> dict:
        deadline = time.monotonic() + timeout
        try:
            if self.process is None:
                if _digest(self.executable) != self.digest or _digest(self.base) != self.base_digest:
                    raise WorkerError("checker or base changed since startup")
                def limits():
                    resource.setrlimit(resource.RLIMIT_AS, (self.memory_bytes, self.memory_bytes))
                self.process = subprocess.Popen([str(self.executable), "--serve", str(self.base)],
                    cwd=self.trusted, env={"PATH": "/usr/local/bin:/usr/bin:/bin", "HOME": str(self.trusted), "LANG": "C.UTF-8"},
                    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                    start_new_session=True, preexec_fn=limits, bufsize=0)
                os.set_blocking(self.process.stdin.fileno(), False)
                os.set_blocking(self.process.stdout.fileno(), False)
            process = self.process
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout, selectors.EVENT_READ)
                if selector.select(0):
                    raise WorkerError("unexpected checker stdout before request")
                payload = memoryview(json.dumps(request, separators=(",", ":")).encode() + b"\n")
                selector.register(process.stdin, selectors.EVENT_WRITE)
                data = bytearray()
                while True:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise WorkerError("checker request timed out")
                    events = selector.select(remaining)
                    if not events:
                        raise WorkerError("checker request timed out")
                    for key, _ in events:
                        if key.fileobj is process.stdin:
                            written = os.write(process.stdin.fileno(), payload)
                            payload = payload[written:]
                            if not payload:
                                selector.unregister(process.stdin)
                        else:
                            chunk = os.read(process.stdout.fileno(), min(65536, REPORT_LIMIT + 1 - len(data)))
                            if not chunk:
                                raise WorkerError("checker exited without a report")
                            data.extend(chunk)
                            if len(data) > REPORT_LIMIT:
                                raise WorkerError("checker report exceeds size limit")
                            if b"\n" in data:
                                if payload or not data.endswith(b"\n") or data.count(b"\n") != 1:
                                    raise WorkerError("unexpected checker stdout")
                                result = _report(_json(bytes(data[:-1])), request["id"])
                                if selector.select(0) or process.poll() is not None:
                                    raise WorkerError("unexpected checker stdout or exit after report")
                                if time.monotonic() >= deadline:
                                    raise WorkerError("checker request timed out")
                                return result
        except Exception:
            self.close()
            raise


def serve(socket_path: str | Path, base: str | Path, trusted: str | Path, checker: str | Path,
          context_digest: str, *, timeout: float = WALL_SECONDS, memory_bytes: int = 24 * 1024**3) -> None:
    _require_linux()
    if not DIGEST.fullmatch(context_digest) or not math.isfinite(timeout) or timeout <= 0 or memory_bytes < 4 * 1024**3:
        raise WorkerError("invalid context digest, timeout, or memory limit")
    executable = _path(str(checker), own=False)
    if not os.access(executable, os.X_OK):
        raise WorkerError("checker must be executable")
    base_path, trusted_path = _path(str(base), own=False), _path(str(trusted), directory=True, own=False)
    actual_context, installed_checker = _context(trusted_path)
    if actual_context != context_digest:
        raise WorkerError("context digest does not match actual trusted sources and tools")
    if _digest(executable) != _digest(installed_checker):
        raise WorkerError("explicit checker does not match the trusted installed checker")
    path = Path(socket_path)
    _private_directory(path.parent, create=True)
    if path.exists() or path.is_symlink():
        info = path.lstat()
        if not stat.S_ISSOCK(info.st_mode) or info.st_uid != os.getuid():
            raise WorkerError("refusing to replace an unsafe socket path")
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as probe:
            probe.settimeout(1)
            try:
                probe.connect(str(path))
            except OSError as error:
                if error.errno != errno.ECONNREFUSED:
                    raise WorkerError("existing socket is not safely stale") from error
            else:
                raise WorkerError("a worker is already listening on this socket")
        path.unlink()
    identity = {"protocol": 1, "checker_digest": _digest(executable),
                "base_digest": _digest(base_path), "context_digest": context_digest}
    engine = Checker(executable, base_path, trusted_path, identity["checker_digest"], identity["base_digest"], memory_bytes)
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as listener:
        old_umask = os.umask(0o077)
        try:
            listener.bind(str(path))
        finally:
            os.umask(old_umask)
        os.chmod(path, 0o600)
        inode = path.lstat().st_ino
        try:
            listener.listen(8)
            print(json.dumps(identity, separators=(",", ":")), file=sys.stderr, flush=True)
            while True:
                connection, _ = listener.accept()
                with connection:
                    request_id = None
                    try:
                        if _peer_uid(connection) != os.getuid():
                            raise WorkerError("client belongs to another UID")
                        connection.settimeout(10)
                        _send(connection, identity)
                        request = _receive(connection, REQUEST_LIMIT, time.monotonic() + 10)
                        request_id = request.get("id")
                        _request(request)
                        report = engine.run(request, timeout)
                        connection.settimeout(10)
                        _send(connection, report)
                    except (WorkerError, OSError, ValueError, subprocess.SubprocessError) as error:
                        engine.close()
                        try:
                            connection.settimeout(1)
                            _send(connection, {"id": request_id, "status": "error", "error": str(error)[:4096]})
                        except (OSError, WorkerError):
                            pass
        finally:
            engine.close()
            if path.exists() and path.lstat().st_ino == inode:
                path.unlink()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("serve")
    for field in ("socket", "base", "trusted", "checker", "context-digest"):
        command.add_argument(f"--{field}", required=True)
    command.add_argument("--timeout", type=float, default=WALL_SECONDS)
    command.add_argument("--memory-bytes", type=int, default=24 * 1024**3)
    identity = commands.add_parser("identity")
    identity.add_argument("--trusted", required=True)
    identity.add_argument("--base")
    args = parser.parse_args()
    def stop(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, stop)
    try:
        if args.command == "identity":
            trusted = _path(str(Path(args.trusted).resolve()), directory=True, own=False)
            digest, checker = _context(trusted)
            result = {"protocol": 1, "context_digest": digest, "checker_digest": _digest(checker)}
            if args.base:
                result["base_digest"] = _digest(_path(str(Path(args.base).absolute()), own=False))
            print(json.dumps(result, separators=(",", ":")))
        else:
            serve(args.socket, args.base, args.trusted, args.checker, args.context_digest,
                  timeout=args.timeout, memory_bytes=args.memory_bytes)
    except (WorkerError, OSError, ValueError) as error:
        parser.exit(2, f"worker failed: {error}\n")
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
