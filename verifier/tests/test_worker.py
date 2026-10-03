import hashlib
import json
import os
from pathlib import Path
import selectors
import socket
import stat
import subprocess
import sys
import tempfile
import time
import unittest
import uuid
from unittest.mock import patch

from verifier.cache import context_digest
from verifier.worker import (Checker, WorkerError, _json, _peer_uid, _private_directory,
                             _receive, _report, _request, check)

WORKER = Path(__file__).resolve().parents[1] / "worker.py"
TOY = r'''import json, os, sys, time
assert sys.argv[1] == '--serve'
base = open(sys.argv[2]).read()
counter = 0
for line in sys.stdin:
    request = json.loads(line)
    config = json.load(open(request['config']))
    mode = config.get('mode', 'normal')
    counter += 1
    if mode == 'timeout':
        time.sleep(2)
    if mode == 'exit':
        sys.exit(1)
    if mode == 'noise':
        print('unrequested stdout', flush=True)
        continue
    if mode == 'oversize':
        print('x' * (1024 * 1024 + 1), flush=True)
        continue
    report = {'id': request['id'], 'status': 'verified', 'pid': os.getpid(),
              'counter': counter, 'fresh_kernel': request['fresh_kernel'],
              'base': base, 'environment': sorted(os.environ)}
    if mode == 'wrong-id':
        report['id'] = '0' * 32
    if mode == 'bad-status':
        report['status'] = []
    if mode == 'accept-error':
        report['error'] = 'failed'
    if mode == 'error':
        report.update(status='error', error='proof rejected')
    if mode == 'rejected':
        report.update(status='rejected', error='proof rejected')
    print(json.dumps(report), flush=True)
'''


class WorkerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name).resolve()
        self.checker = self.root / "checker"
        self.checker.write_text(f"#!{sys.executable}\n" + TOY)
        self.checker.chmod(0o700)
        self.base = self.root / "base.export"
        self.base.write_text("immutable trusted base")
        self.config = self.root / "config.json"
        self.config.write_text("{}")
        self.trusted = self.root / "trusted.export"
        self.trusted.write_text("trusted challenge")
        self.candidate = self.root / "candidate.export"
        self.candidate.write_text("candidate declarations")
        self.socket = self.root / "private" / "worker.sock"
        self.digest = hashlib.sha256(self.checker.read_bytes()).hexdigest()
        self.base_digest = hashlib.sha256(self.base.read_bytes()).hexdigest()
        for name in ("RULES.md", "SigGolf.lean", "lean-toolchain", "lakefile.lean", "lake-manifest.json",
                     "scripts/run.py", "scripts/setup.sh", "SigGolf/Certificate.lean"):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("trusted fixture")
        env_path = self.root / "verifier" / ".tools" / "env.sh"
        env_path.parent.mkdir(parents=True)
        self.tools = {name: str(self.checker) for name in
                      ("COMPARATOR_BIN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_LANDRUN", "COMPARATOR_CERTIFICATE_CHECK")}
        env_path.write_text("".join(f'export {name}="{value}"\n' for name, value in self.tools.items()))
        self.context = context_digest(self.root, self.tools)
        self.process = None

    def tearDown(self):
        if self.process is not None:
            self.process.terminate()
            try:
                self.process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.communicate(timeout=5)
        self.temporary.cleanup()

    def command(self):
        prefix = [sys.executable]
        if sys.platform == "darwin":
            # Production workers refuse macOS; exercise the protocol with mocked limits.
            prefix += ["-c", "import sys; from pathlib import Path; from unittest.mock import patch; "
                       "sys.path.insert(0,str(Path(sys.argv[1]).parent.parent)); sys.argv=sys.argv[1:]; "
                       "from verifier import worker; "
                       "exec('with patch(\"verifier.worker._require_linux\"), patch(\"resource.setrlimit\"):\\n worker.main()')"]
        return [*prefix, str(WORKER), "serve", "--socket", str(self.socket),
                "--checker", str(self.checker), "--base", str(self.base), "--trusted", str(self.root),
                "--context-digest", self.context, "--timeout", "0.5"]

    def start(self):
        self.process = subprocess.Popen(self.command(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                        env={**os.environ, "WORKER_SECRET": "must not reach checker"})
        with selectors.DefaultSelector() as ready:
            ready.register(self.process.stderr, selectors.EVENT_READ)
            if not ready.select(5):
                self.fail("worker did not start")
            line = self.process.stderr.readline()
        self.assertEqual(json.loads(line)["protocol"], 1)

    def request(self, fresh=False):
        return {"id": uuid.uuid4().hex, "config": str(self.config), "trusted": str(self.trusted),
                "candidate": str(self.candidate), "fresh_kernel": fresh}

    def call(self, request=None, **kwargs):
        return check(self.socket, self.request() if request is None else request, self.digest,
                     expected_base_digest=self.base_digest, expected_context_digest=self.context,
                     timeout=3, **kwargs)

    def test_reuses_checker_and_forwards_fresh_kernel(self):
        self.start()
        first, second = self.call(), self.call(self.request(fresh=True))
        self.assertEqual(first["status"], "verified")
        self.assertEqual(first["pid"], second["pid"])
        self.assertEqual((first["counter"], second["counter"]), (1, 2))
        self.assertTrue(second["fresh_kernel"])
        self.assertEqual(first["base"], self.base.read_text())
        self.assertNotIn("WORKER_SECRET", first["environment"])
        self.assertLessEqual(set(first["environment"]), {"PATH", "HOME", "LANG", "LC_CTYPE", "__CF_USER_TEXT_ENCODING"})
        self.assertEqual(stat.S_IMODE(self.socket.parent.stat().st_mode), 0o700)
        self.assertEqual(stat.S_IMODE(self.socket.stat().st_mode), 0o600)

    def test_pins_all_identity_fields(self):
        self.start()
        for field in ("checker", "base", "context"):
            with self.subTest(field=field), self.assertRaises(WorkerError):
                check(self.socket, self.request(), "0" * 64 if field == "checker" else self.digest,
                      expected_base_digest="0" * 64 if field == "base" else self.base_digest,
                      expected_context_digest="0" * 64 if field == "context" else self.context, timeout=3)
        with self.assertRaises(WorkerError):
            check(self.socket, self.request())

    def test_bad_checker_reports_are_errors_and_recycle(self):
        self.start()
        for mode in ("wrong-id", "bad-status", "noise", "oversize", "accept-error", "exit"):
            with self.subTest(mode=mode):
                self.config.write_text(json.dumps({"mode": mode}))
                result = self.call()
                self.assertEqual(result["status"], "error")
                self.config.write_text("{}")
                self.assertEqual(self.call()["counter"], 1)

    def test_timeout_recycles_and_never_accepts_late_report(self):
        self.start()
        before = self.call()
        self.config.write_text('{"mode":"timeout"}')
        rejected = self.call()
        self.assertEqual(rejected["status"], "error")
        self.assertIn("timed out", rejected["error"])
        with self.assertRaises(ProcessLookupError):
            os.kill(before["pid"], 0)
        self.config.write_text("{}")
        after = self.call()
        self.assertNotEqual(before["pid"], after["pid"])
        self.assertEqual(after["counter"], 1)

    def test_valid_rejection_does_not_require_recycle(self):
        self.start()
        for mode in ("error", "rejected"):
            self.config.write_text(json.dumps({"mode": mode}))
            result = self.call()
            self.assertEqual(result["status"], mode)
        self.config.write_text("{}")
        self.assertEqual(self.call()["counter"], 3)

    def test_actual_context_and_installed_checker_are_required(self):
        (self.root / "RULES.md").write_text("changed under same checkout")
        result = subprocess.run(self.command(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"actual trusted", result.stderr)
        self.context = context_digest(self.root, self.tools)
        alternate = self.root / "alternate"
        alternate.write_text(f"#!{sys.executable}\nraise SystemExit(1)\n")
        alternate.chmod(0o700)
        command = self.command()
        command[command.index("--checker") + 1] = str(alternate)
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"installed checker", result.stderr)

    def test_identity_cli_reports_actual_hashes(self):
        result = subprocess.run([sys.executable, str(WORKER), "identity", "--trusted", str(self.root),
                                 "--base", str(self.base)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), {"protocol": 1, "checker_digest": self.digest,
                                                    "context_digest": self.context, "base_digest": self.base_digest})

    def test_production_refuses_unsupported_host(self):
        with patch("verifier.worker.sys.platform", "darwin"):
            from verifier.worker import _require_linux
        with self.assertRaisesRegex(WorkerError, "require unprivileged Linux"):
                _require_linux()

    def test_live_socket_is_not_replaced(self):
        self.start()
        inode = self.socket.stat().st_ino
        second = subprocess.run(self.command(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
        self.assertNotEqual(second.returncode, 0)
        self.assertIn(b"already listening", second.stderr)
        self.assertEqual(inode, self.socket.stat().st_ino)
        self.assertEqual(self.call()["status"], "verified")

    def test_stale_socket_can_be_replaced(self):
        self.socket.parent.mkdir(mode=0o700)
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as stale:
            stale.bind(str(self.socket))
        self.start()
        self.assertEqual(self.call()["status"], "verified")

    def test_symlink_and_regular_socket_paths_are_not_removed(self):
        self.socket.parent.mkdir(mode=0o700)
        for symlink in (False, True):
            with self.subTest(symlink=symlink):
                if symlink:
                    self.socket.symlink_to(self.base)
                else:
                    self.socket.write_text("not a socket")
                result = subprocess.run(self.command(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
                self.assertNotEqual(result.returncode, 0)
                self.assertTrue(self.socket.exists())
                self.socket.unlink()

    def test_bad_directory_permissions_rejected(self):
        self.socket.parent.mkdir(mode=0o755)
        result = subprocess.run(self.command(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"0700", result.stderr)

    def test_bad_request_ids_fields_and_types(self):
        for change in ({"id": "not-uuid"}, {"id": "A" * 32}, {"fresh_kernel": 1},
                       {"candidate": "relative.export"}, {"unexpected": True}):
            with self.subTest(change=change), self.assertRaises(WorkerError):
                _request({**self.request(), **change})

    def test_symlink_input_and_foreign_owner_rejected(self):
        link = self.root / "linked.export"
        link.symlink_to(self.candidate)
        with self.assertRaises(WorkerError):
            _request({**self.request(), "candidate": str(link)})
        with patch("verifier.worker.os.getuid", return_value=os.getuid() + 1), self.assertRaises(WorkerError):
            _request(self.request())

    def test_json_and_report_fail_closed(self):
        for data in (b'[]', b'{"id":1,"id":2}', b'{"x":NaN}', b'no json', b'\xff'):
            with self.subTest(data=data), self.assertRaises(WorkerError):
                _json(data)
        with self.assertRaises(WorkerError):
            _report({"id": "wrong", "status": "verified"}, uuid.uuid4().hex)

    def test_peer_uid_and_message_bounds(self):
        left, right = socket.socketpair()
        try:
            self.assertEqual(_peer_uid(left), os.getuid())
            right.sendall(b"x" * 65)
            with self.assertRaises(WorkerError):
                _receive(left, 64, time.monotonic() + 1)
        finally:
            left.close()
            right.close()
        for message in (b'{}\n{}\n', b'{}\ntrailing'):
            left, right = socket.socketpair()
            try:
                right.sendall(message)
                with self.assertRaises(WorkerError):
                    _receive(left, 64, time.monotonic() + 1)
            finally:
                left.close()
                right.close()


if __name__ == "__main__":
    unittest.main()
