"""Real Linux transport-to-pinned-kernel integration, enabled after Lean fixtures exist."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
import uuid

from verifier.worker import _context, _digest, check

ROOT = Path(__file__).resolve().parents[2]


@unittest.skipUnless(sys.platform == 'linux' and os.environ.get('SIG_GOLF_NATIVE_TESTS') == '1',
                     'requires Linux and generated native Lean fixtures')
class NativeWorkerTests(unittest.TestCase):
    def test_real_worker_reused_and_fresh_checks_agree(self):
        folder = ROOT / 'verifier' / '.tools' / 'comparator' / '.lake' / 'certificate-tests'
        context, checker = _context(ROOT)
        base = folder / 'valid-trusted.export'
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary).resolve()
            socket = directory / 'private' / 'checker.sock'
            process = subprocess.Popen([sys.executable, str(ROOT / 'verifier' / 'worker.py'), 'serve',
                '--trusted', str(ROOT), '--checker', str(checker), '--base', str(base),
                '--context-digest', context, '--socket', str(socket), '--timeout', '30'],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
            try:
                deadline = time.monotonic() + 30
                while not socket.exists() and process.poll() is None and time.monotonic() < deadline:
                    time.sleep(0.05)
                self.assertTrue(socket.exists(), 'native worker did not bind')
                reports = []
                for fresh in (False, True, False):
                    reports.append(check(socket, {'id': uuid.uuid4().hex,
                        'config': str(folder / 'valid-config.json'), 'trusted': str(base),
                        'candidate': str(folder / 'valid-candidate.export'), 'fresh_kernel': fresh},
                        _digest(checker), expected_base_digest=_digest(base), expected_context_digest=context, timeout=30))
                self.assertTrue(all(report['status'] == 'verified' for report in reports), reports)
                self.assertGreater(reports[0]['reused_declarations'], 0)
                self.assertEqual(reports[1]['reused_declarations'], 0)
                self.assertTrue(reports[1]['fresh_kernel'])
                self.assertGreater(reports[2]['reused_declarations'], 0)
            finally:
                os.killpg(process.pid, signal.SIGTERM)
                process.communicate(timeout=10)


if __name__ == '__main__':
    unittest.main()
