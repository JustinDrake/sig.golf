"""Exact host-local acceptance cache, never an uploader-provided attestation.

The supervisor must keep this directory inaccessible to candidate processes.
Private permissions do not isolate hostile code running unsandboxed as our UID.
Callers enforce source-size policy and freeze inputs before hashing/checking them.
"""
from __future__ import annotations

from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import stat


VERSION = 1
MAX_MANIFEST_BYTES = 64 * 1024
FIELDS = {"status", "score", "claim", "source_digest", "context_digest",
          "certificate_digest", "mode"}
DIGEST = re.compile(r"[0-9a-f]{64}")
LAYOUT = {"message", "secret_key", "public_key", "cache", "signature", "witness"}
DIRECTORY_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


def _json(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True, allow_nan=False).encode("ascii")


def _frame(h, tag: bytes, data: bytes) -> None:
    h.update(tag)
    h.update(len(data).to_bytes(8, "big"))
    h.update(data)


def _identity(info):
    # Reads can update atime; changes to contents, permissions or links cannot.
    return (info.st_dev, info.st_ino, info.st_mode, info.st_nlink, info.st_uid,
            info.st_gid, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def _file(h, name: bytes, fd: int) -> None:
    before = os.fstat(fd)
    if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1:
        raise ValueError(f"hash input {name!r} must be a regular file without hardlinks")
    _frame(h, b"F", name)
    h.update(before.st_size.to_bytes(8, "big"))
    size = 0
    while chunk := os.read(fd, 1024 * 1024):
        h.update(chunk)
        size += len(chunk)
        if size > before.st_size:
            raise ValueError("hash input grew during reading")
    after = os.fstat(fd)
    if size != before.st_size or _identity(before) != _identity(after):
        raise ValueError("hash input changed during reading")


def tree_digest(root: Path, excluded_top_level=frozenset({"certificate"}), *, include_directories=True) -> str:
    """Hash sorted relative paths, entry kinds, and raw bytes, including empty dirs.

Excluded top-level entries are not traversed; callers validate their separate
policy. All included symlinks, special files, and hardlinked files are rejected.
"""
    return _tree_digest(root, excluded_top_level, include_directories=include_directories)


def _package_link(h, path: bytes, root: Path, root_fd: int) -> None:
    """Resolve only source-file links, with no filesystem symlink following."""
    pending = os.fsdecode(path).split("/")
    stack = [(root_fd, "")]
    opened = []
    links = []
    visited = set()
    try:
        while pending:
            name, pending = pending[0], pending[1:]
            if name in {"", "."}:
                continue
            if name == "..":
                if len(stack) == 1:
                    raise ValueError("package link escapes its source tree")
                stack.pop()
                continue
            if len(stack) == 1 and name in {".git", ".lake"}:
                raise ValueError("package link targets excluded metadata or build artifacts")
            directory = stack[-1][0]
            info = os.stat(name, dir_fd=directory, follow_symlinks=False)
            if stat.S_ISLNK(info.st_mode):
                if pending:
                    raise ValueError("package directory links are forbidden")
                identity = (info.st_dev, info.st_ino)
                if identity in visited or len(visited) >= 40:
                    raise ValueError("package link cycle or excessive chain")
                visited.add(identity)
                target = os.readlink(name, dir_fd=directory)
                links.append((directory, name, info, target))
                link_path = "/".join([item[1] for item in stack[1:]] + [name])
                _frame(h, b"L", os.fsencode(link_path))
                _frame(h, b"R", os.fsencode(target))
                if os.path.isabs(target):
                    try:
                        target = str(Path(target).relative_to(root))
                    except ValueError:
                        raise ValueError("package link escapes its source tree") from None
                    stack = stack[:1]
                pending = target.split("/")
            elif stat.S_ISDIR(info.st_mode) and pending:
                child = os.open(name, DIRECTORY_FLAGS, dir_fd=directory)
                opened.append((child, os.fstat(child)))
                if _identity(info) != _identity(opened[-1][1]):
                    raise ValueError("package link directory changed during resolution")
                stack.append((child, name))
            elif stat.S_ISREG(info.st_mode) and not pending:
                child = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                                dir_fd=directory)
                try:
                    if _identity(info) != _identity(os.fstat(child)):
                        raise ValueError("package link target changed during resolution")
                    _file(h, path, child)
                finally:
                    os.close(child)
                break
            else:
                raise ValueError("package links must resolve to regular source files")
        else:
            raise ValueError("package links must resolve to regular source files")
        for directory, name, before, target in links:
            after = os.stat(name, dir_fd=directory, follow_symlinks=False)
            if (_identity(before) != _identity(after) or
                    os.readlink(name, dir_fd=directory) != target):
                raise ValueError("package link changed during hashing")
        for directory, before in opened:
            if _identity(before) != _identity(os.fstat(directory)):
                raise ValueError("package link directory changed during hashing")
    finally:
        for directory, _ in opened:
            os.close(directory)


def _tree_digest(root: Path, excluded_top_level, *, package=False, include_directories=True) -> str:
    root = Path(os.path.abspath(root))
    excluded = set(excluded_top_level)
    if any(not isinstance(n, str) or not n or n in {".", ".."} or "/" in n
           for n in excluded):
        raise ValueError("exclusions must be top-level names")
    h = hashlib.sha256(b"sig-golf-package-file-links-v1\0" if package else b"sig-golf-tree-v1\0")
    if not include_directories:
        # Git preserves file paths and contents, but does not transport empty directories.
        _frame(h, b"P", b"transport-files-only")

    def walk(fd: int, prefix: bytes) -> None:
        before = os.fstat(fd)
        if include_directories:
            _frame(h, b"D", prefix)
        with os.scandir(fd) as entries:
            names = sorted((entry.name for entry in entries), key=os.fsencode)
        for name in names:
            if not prefix and name in excluded:
                continue
            path = prefix + (b"/" if prefix else b"") + os.fsencode(name)
            info = os.stat(name, dir_fd=fd, follow_symlinks=False)
            if stat.S_ISDIR(info.st_mode):
                child = os.open(name, DIRECTORY_FLAGS, dir_fd=fd)
                try:
                    walk(child, path)
                finally:
                    os.close(child)
            elif stat.S_ISREG(info.st_mode):
                child = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
                try:
                    _file(h, path, child)
                finally:
                    os.close(child)
            elif package and stat.S_ISLNK(info.st_mode):
                _package_link(h, path, root, root_fd)
            else:
                raise ValueError(f"hash input {path!r} cannot be a symlink or special file")
        if _identity(before) != _identity(os.fstat(fd)):
            raise ValueError("hash directory changed during reading")

    root_fd = fd = os.open(root, DIRECTORY_FLAGS)
    try:
        walk(fd, b"")
    finally:
        os.close(fd)
    return h.hexdigest()


def context_digest(trusted: Path, toolpaths: dict) -> str:
    """Hash actual contract/checker inputs and named active executable contents.

Executable locations are deliberately not identities. Trusted executable paths
may resolve installation symlinks. Only trusted package-internal source-file
links are supported: link paths, target text, and contents are explicitly bound.
Dependency pins and installed package source trees are included; package Git
metadata and build artifacts are not. The trusted tree must remain frozen.
"""
    trusted = Path(trusted)
    h = hashlib.sha256(b"sig-golf-context-v1\0")
    for name in ("RULES.md", "SigGolf.lean", "lean-toolchain", "lakefile.lean",
                 "lake-manifest.json", "scripts/run.py", "scripts/setup.sh"):
        fd = os.open(trusted / name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        try:
            _file(h, name.encode("ascii"), fd)
        finally:
            os.close(fd)
    _frame(h, b"T", tree_digest(trusted / "SigGolf", excluded_top_level=()).encode("ascii"))
    folder = trusted / "verifier"
    fd = os.open(folder, DIRECTORY_FLAGS)
    try:
        with os.scandir(fd) as entries:
            names = sorted(entry.name for entry in entries
                           if Path(entry.name).suffix in {".py", ".lean", ".json", ".in"}
                           or entry.name == "setup_tools.sh")
        for name in names:
            child = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
            try:
                _file(h, os.fsencode("verifier/" + name), child)
            finally:
                os.close(child)
    finally:
        os.close(fd)
    try:
        lake = os.open(trusted / ".lake", DIRECTORY_FLAGS)
    except FileNotFoundError:
        lake = None
    if lake is not None:
        try:
            try:
                packages = os.open("packages", DIRECTORY_FLAGS, dir_fd=lake)
            except FileNotFoundError:
                packages = None
            if packages is not None:
                try:
                    before = os.fstat(packages)
                    _frame(h, b"P", b".lake/packages")
                    with os.scandir(packages) as entries:
                        names = sorted((entry.name for entry in entries), key=os.fsencode)
                    for name in names:
                        info = os.stat(name, dir_fd=packages, follow_symlinks=False)
                        if not stat.S_ISDIR(info.st_mode):
                            raise ValueError("installed packages must be ordinary directories")
                        _frame(h, b"P", os.fsencode(name))
                        try:
                            digest = _tree_digest(trusted / ".lake" / "packages" / name,
                                                  {".git", ".lake"}, package=True)
                        except ValueError as exc:
                            raise ValueError(f"installed package {name!r}: {exc}") from exc
                        _frame(h, b"T", digest.encode("ascii"))
                    if _identity(before) != _identity(os.fstat(packages)):
                        raise ValueError("installed package directory changed during hashing")
                finally:
                    os.close(packages)
        finally:
            os.close(lake)
    for name, path in sorted(toolpaths.items()):
        if not isinstance(name, str) or not name:
            raise ValueError("tool identities must have nonempty names")
        _frame(h, b"B", name.encode("utf-8"))
        active = Path(path).resolve(strict=True)
        fd = os.open(active, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        try:
            if not os.fstat(fd).st_mode & 0o111:
                raise ValueError("tool must be executable")
            _file(h, b"", fd)
        finally:
            os.close(fd)
    if 'COMPARATOR_LEAN' in toolpaths:
        # Linux builds can link the kernel/runtime dynamically. A patched shared
        # runtime must invalidate acceptance even when launcher bytes are unchanged.
        prefix = Path(toolpaths['COMPARATOR_LEAN']).resolve(strict=True).parent.parent
        libraries = sorted((prefix / 'lib' / 'lean').glob('libleanshared*'))
        for library in libraries:
            if library.suffix not in {'.so', '.dylib'}:
                continue
            fd = os.open(library, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            try:
                _file(h, ('runtime/' + library.name).encode('ascii'), fd)
            finally:
                os.close(fd)
    return h.hexdigest()


def acceptance_key(context, source, claim, bundleidentity, mode) -> str:
    return hashlib.sha256(_json({"version": VERSION, "context": context,
                                "source": source, "claim": claim,
                                "bundle": bundleidentity, "mode": mode})).hexdigest()


def _validated(key: str, result: dict) -> dict:
    if not isinstance(key, str) or not DIGEST.fullmatch(key):
        raise ValueError("invalid cache key")
    if not isinstance(result, dict) or not FIELDS <= result.keys():
        raise ValueError("incomplete acceptance result")
    value = {field: result[field] for field in FIELDS}
    if value["status"] != "verified":
        raise ValueError("only verified results may be cached")
    for field in ("source_digest", "context_digest"):
        if not isinstance(value[field], str) or not DIGEST.fullmatch(value[field]):
            raise ValueError("invalid result digest")
    certificate = value["certificate_digest"]
    if certificate is not None and (not isinstance(certificate, str)
                                    or not DIGEST.fullmatch(certificate)):
        raise ValueError("invalid certificate digest")
    mode = value["mode"]
    if not isinstance(mode, str) or not mode or len(mode) > 128 or not mode.isascii():
        raise ValueError("invalid verification mode")
    claim = value["claim"]
    if not isinstance(claim, dict) or set(claim) != {"S", "W", "K", "C", "layout"}:
        raise ValueError("invalid claim")
    layout = claim["layout"]
    if not isinstance(layout, dict) or set(layout) != LAYOUT:
        raise ValueError("invalid claim layout")
    if any(type(n) is not int or n < 0 for n in
           [claim[k] for k in ("S", "W", "K", "C")] + list(layout.values())):
        raise ValueError("invalid claim integers")
    if type(value["score"]) is not int or value["score"] != claim["S"] * claim["C"]:
        raise ValueError("invalid acceptance score")
    if key != acceptance_key(value["context_digest"], value["source_digest"],
                             claim, certificate, mode):
        raise ValueError("acceptance result does not match cache key")
    return value


class ResultCache:
    """Private local cache; constructor rejects unsafe directories, reads miss closed."""

    def __init__(self, path: Path):
        self.path = Path(os.path.abspath(Path(path).expanduser()))
        with self._directory(create=True):
            pass

    @contextmanager
    def _directory(self, create=False):
        fd = os.open(self.path.anchor, DIRECTORY_FLAGS)
        try:
            parts = self.path.parts[1:]
            if not parts:
                raise ValueError("cache cannot be filesystem root")
            for index, part in enumerate(parts):
                parent = os.fstat(fd)
                shared_tmp = parent.st_uid == 0 and bool(parent.st_mode & stat.S_ISVTX)
                if parent.st_uid not in {0, os.getuid()} or (
                        parent.st_mode & 0o022 and not shared_tmp):
                    raise ValueError("unsafe cache parent directory")
                if create:
                    try:
                        os.mkdir(part, 0o700, dir_fd=fd)
                    except FileExistsError:
                        pass
                child = os.open(part, DIRECTORY_FLAGS, dir_fd=fd)
                os.close(fd)
                fd = child
                info = os.fstat(fd)
                if index == len(parts) - 1 and (
                        info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) != 0o700):
                    raise ValueError("cache directory must be owned by us with mode 0700")
            yield fd
        finally:
            os.close(fd)

    @staticmethod
    def _entry(fd: int) -> None:
        info = os.fstat(fd)
        # A concurrent atomic replacement can unlink an already opened entry.
        # Its descriptor remains safe; only multiple links violate ownership.
        if (not stat.S_ISREG(info.st_mode) or info.st_nlink > 1 or
                info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) != 0o600 or
                info.st_size > MAX_MANIFEST_BYTES):
            raise ValueError("unsafe cache manifest")

    def get(self, key: str) -> dict | None:
        try:
            if not isinstance(key, str) or not DIGEST.fullmatch(key):
                return None
            with self._directory() as directory:
                fd = os.open(key + ".json", os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                             dir_fd=directory)
                try:
                    self._entry(fd)
                    before = os.fstat(fd)
                    raw = bytearray()
                    while chunk := os.read(fd, min(8192, MAX_MANIFEST_BYTES + 1 - len(raw))):
                        raw.extend(chunk)
                        if len(raw) > MAX_MANIFEST_BYTES:
                            return None
                    if _identity(before) != _identity(os.fstat(fd)):
                        return None
                finally:
                    os.close(fd)
            manifest = json.loads(raw)
            if (not isinstance(manifest, dict) or set(manifest) != {"version", "key", "result"}
                    or type(manifest["version"]) is not int or manifest["version"] != VERSION
                    or manifest["key"] != key or not isinstance(manifest["result"], dict)
                    or set(manifest["result"]) != FIELDS or _json(manifest) != raw):
                return None
            return _validated(key, manifest["result"])
        except (OSError, ValueError, TypeError, OverflowError, RecursionError):
            return None

    def put(self, key: str, result: dict) -> None:
        value = _validated(key, result)
        raw = _json({"version": VERSION, "key": key, "result": value})
        if len(raw) > MAX_MANIFEST_BYTES:
            raise ValueError("cache manifest too large")
        with self._directory() as directory:
            name = key + ".json"
            try:
                existing = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                                   dir_fd=directory)
            except FileNotFoundError:
                pass
            else:
                try:
                    self._entry(existing)
                finally:
                    os.close(existing)
            temporary = "." + secrets.token_hex(16) + ".tmp"
            fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                         0o600, dir_fd=directory)
            try:
                with os.fdopen(fd, "wb") as output:
                    output.write(raw)
                    output.flush()
                    os.fsync(output.fileno())
                # Replacement never follows the destination. Concurrent valid writers
                # publish the same key-bound fields, not a partially written manifest.
                os.replace(temporary, name, src_dir_fd=directory, dst_dir_fd=directory)
                os.fsync(directory)
            finally:
                try:
                    os.unlink(temporary, dir_fd=directory)
                except FileNotFoundError:
                    pass
