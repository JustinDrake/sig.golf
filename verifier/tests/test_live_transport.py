"""Opt-in public transport smoke test; downloaded data is never executed or scored."""
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from certificate import download_proof


@unittest.skipUnless(os.environ.get('SIG_GOLF_LIVE_TRANSPORT_TEST') == '1', 'requires public network access')
class LiveTransportTests(unittest.TestCase):
    def test_anonymous_github_asset_hash_and_length(self):
        # Public GitHub asset metadata for elan v4.2.4. Only transport is tested;
        # these bytes are not a Lean certificate and are never unpacked or executed.
        proof = {'url': 'https://github.com/leanprover/elan/releases/download/v4.2.4/elan-aarch64-apple-darwin.tar.gz',
                 'bytes': 2190845, 'sha256': '7ad829861392c718dfebde3a83b5c8508df47be02af68894b094b0b3952616e5'}
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary) / 'public-asset'
            download_proof(proof, destination)
            self.assertEqual(destination.stat().st_size, proof['bytes'])


if __name__ == '__main__':
    unittest.main()
