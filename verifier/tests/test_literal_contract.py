"""Compile generated literal binding against the actual pinned SigGolf definitions."""
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from certificate import binding_module, literal_module

ROOT = Path(__file__).resolve().parents[2]


@unittest.skipUnless(os.environ.get('SIG_GOLF_CONTRACT_TESTS') == '1',
                     'requires the trusted SigGolf library, not only checker tools')
class LiteralContractTests(unittest.TestCase):
    def test_generated_images_and_equality_typecheck_against_actual_contract(self):
        claim = {'S': 8, 'W': 8, 'K': 0, 'C': 100, 'layout':
            {'message': 0, 'secret_key': 32, 'public_key': 64, 'cache': 80, 'signature': 80, 'witness': 88}}
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for program in ('keygen', 'sign', 'expand', 'verify'):
                (directory / f'{program}.code').write_bytes(struct.pack('<I', 0x73))
                (directory / f'{program}.data').write_bytes(bytes([0, 1, 255]))
            source = directory / 'LiteralTest.lean'
            source.write_text(literal_module(directory, claim) + '\n'
                'namespace SigGolf.Challenge\n'
                'noncomputable def submission : SigGolf.Submission := SigGolf.CertifiedImages.submission\n'
                'end SigGolf.Challenge\n' + '\n'.join(binding_module().splitlines()[2:]) + '\n'
                'example : (SigGolf.CertifiedImages.submission.image .verify).code = [115] := by rfl\n'
                'example : (SigGolf.CertifiedImages.submission.image .verify).data = [0, 1, 255] := by rfl\n')
            completed = subprocess.run(['lake', 'env', 'lean', str(source)], cwd=ROOT,
                                       capture_output=True, text=True, timeout=60)
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)


if __name__ == '__main__':
    unittest.main()
