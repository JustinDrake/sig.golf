import gzip
import hashlib
import json
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from cache import tree_digest
from certificate import (CertificateError, challenge_source, expand_proof, inspect_bundle,
                         literal_module, pack, strict_json)
from check_submission import check


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.source = self.root / 'source'
        self.source.mkdir()
        (self.source / 'Solution.lean').write_text('import SigGolf\n')
        self.claim = {'S': 8, 'W': 8, 'K': 0, 'C': 100, 'layout':
            {'message': 0, 'secret_key': 32, 'public_key': 64, 'cache': 80, 'signature': 80, 'witness': 88}}
        (self.source / 'claim.json').write_text(json.dumps(self.claim))
        self.trusted = self.root / 'trusted'
        self.trusted.mkdir()
        (self.trusted / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        self.images = self.root / 'images'
        self.images.mkdir()
        for program in ('keygen', 'sign', 'expand', 'verify'):
            (self.images / f'{program}.code').write_bytes(struct.pack('<I', 0x73))
            (self.images / f'{program}.data').write_bytes(bytes([0, 1, 255]))
        self.export = self.root / 'candidate.export'
        self.export.write_bytes(b'fixture metadata\n{}\n')
        self.output = self.source / 'certificate'
        pack(self.source, self.export, self.images, self.output, self.trusted)
        self.digest = tree_digest(self.source, excluded_top_level={'certificate'}, include_directories=False)

    def tearDown(self):
        self.temp.cleanup()

    def inspect(self):
        return inspect_bundle(self.output, self.claim, self.digest, 'leanprover/lean4:v4.33.1')

    def rewrite(self, modify):
        path = self.output / 'manifest.json'
        manifest = json.loads(path.read_bytes())
        modify(manifest)
        path.write_text(json.dumps(manifest))

    def test_roundtrip_and_policy(self):
        manifest = self.inspect()
        self.assertTrue(check(self.source)['ok'])
        destination = self.root / 'expanded'
        expand_proof(self.output, manifest, destination)
        self.assertEqual(destination.read_bytes(), self.export.read_bytes())

    def test_every_image_part_is_bound(self):
        for program in ('keygen', 'sign', 'expand', 'verify'):
            for part in ('code', 'data'):
                with self.subTest(program=program, part=part):
                    path = self.output / f'{program}.{part}'
                    raw = path.read_bytes()
                    path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
                    with self.assertRaises(CertificateError):
                        self.inspect()
                    path.write_bytes(raw)

    def test_source_claim_and_toolchain_mismatch(self):
        with self.assertRaises(CertificateError):
            inspect_bundle(self.output, self.claim, '0' * 64, 'leanprover/lean4:v4.33.1')
        with self.assertRaises(CertificateError):
            inspect_bundle(self.output, dict(self.claim, C=101), self.digest, 'leanprover/lean4:v4.33.1')
        with self.assertRaises(CertificateError):
            inspect_bundle(self.output, self.claim, self.digest, 'another toolchain')

    def test_malformed_deflate_is_structured_and_partial_output_removed(self):
        raw = bytes.fromhex('1f8b080000000000000007000000000000000000')
        path = self.output / 'proof.export.gz'
        path.write_bytes(raw)
        self.rewrite(lambda m: m['proof'].update(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest()))
        manifest = self.inspect()
        destination = self.root / 'expanded'
        with self.assertRaisesRegex(CertificateError, 'invalid compressed proof'):
            expand_proof(self.output, manifest, destination)
        self.assertFalse(destination.exists())

    def test_expansion_size_and_digest_are_enforced(self):
        self.rewrite(lambda m: m['proof'].update(expanded_bytes=1))
        manifest = self.inspect()
        destination = self.root / 'expanded'
        with self.assertRaises(CertificateError):
            expand_proof(self.output, manifest, destination)
        self.assertFalse(destination.exists())
        self.rewrite(lambda m: m['proof'].update(expanded_bytes=self.export.stat().st_size,
                                               expanded_sha256='0' * 64))
        with self.assertRaises(CertificateError):
            expand_proof(self.output, self.inspect(), destination)
        self.assertFalse(destination.exists())

    def test_duplicate_fields_and_claim_booleans_rejected(self):
        with self.assertRaises(CertificateError):
            strict_json('{"version":1,"version":1}')
        (self.source / 'claim.json').write_text(json.dumps(dict(self.claim, C=True)))
        self.assertFalse(check(self.source)['ok'])

    def test_extra_missing_symlink_and_traversal_files_rejected(self):
        extra = self.output / 'evil.olean'
        extra.write_bytes(b'bad')
        with self.assertRaises(CertificateError):
            self.inspect()
        extra.unlink()
        image = self.output / 'verify.data'
        image.unlink()
        image.symlink_to(self.images / 'verify.data')
        with self.assertRaises(CertificateError):
            self.inspect()
        image.unlink()
        image.write_bytes((self.images / 'verify.data').read_bytes())
        self.rewrite(lambda m: m['images']['verify']['data'].update(file='../images/verify.data'))
        with self.assertRaises(CertificateError):
            self.inspect()

    def test_invalid_alignment_and_image_limit(self):
        (self.images / 'verify.code').write_bytes(b'abc')
        with self.assertRaises(CertificateError):
            literal_module(self.images, self.claim)

    def test_literal_binding_is_to_bytes_not_hash_or_native_evaluation(self):
        literal = literal_module(self.images, self.claim)
        self.assertIn('code := [115]', literal)
        self.assertIn('data := [0, 1, 255]', literal)
        self.assertNotIn('#eval', literal)
        self.assertNotIn('sha256', literal)
        template = (Path(__file__).resolve().parents[1] / 'Challenge.lean.in').read_text()
        challenge = challenge_source(template, self.claim, bind_images=True)
        self.assertIn('theorem image_binding : submission = SigGolf.CertifiedImages.submission', challenge)
        self.assertNotIn('{{', challenge)

    def test_pack_refuses_overwrite_and_is_deterministic(self):
        with self.assertRaises(CertificateError):
            pack(self.source, self.export, self.images, self.output, self.trusted)
        alternate = self.root / 'other'
        pack(self.source, self.export, self.images, alternate, self.trusted)
        self.assertEqual((alternate / 'proof.export.gz').read_bytes(), (self.output / 'proof.export.gz').read_bytes())

    def test_git_transport_does_not_preserve_empty_source_directories(self):
        empty = self.source / 'SigGolfCandidate'
        empty.mkdir()
        alternate = self.root / 'git-bundle'
        pack(self.source, self.export, self.images, alternate, self.trusted)
        empty.rmdir()
        digest = tree_digest(self.source, excluded_top_level={'certificate'}, include_directories=False)
        inspect_bundle(alternate, self.claim, digest, 'leanprover/lean4:v4.33.1')


if __name__ == '__main__':
    unittest.main()
