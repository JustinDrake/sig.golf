import copy
import gzip
import hashlib
import http.client
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch
import urllib.error
import urllib.request

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import certificate
from cache import ResultCache, acceptance_key, tree_digest
from check_submission import check


URL = 'https://github.com/owner/repo/releases/download/v1/proof.export.gz'
TOOLCHAIN = 'leanprover/lean4:v4.33.1'


class Response(io.BytesIO):
    def __init__(self, body, *, url=URL, status=200):
        super().__init__(body)
        self.url = url
        self.status = status
        self.fp = SimpleNamespace(raw=SimpleNamespace(_sock=Mock()))
        self.length = 1
        self.headers = {'Content-Length': '1', 'Authorization': 'untrusted'}

    def geturl(self):
        return self.url


class DetachedCertificateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.source = self.root / 'source'
        self.source.mkdir()
        (self.source / 'Solution.lean').write_text('import SigGolf\n')
        self.claim = {'S': 8, 'W': 8, 'K': 0, 'C': 100, 'layout':
            {'message': 0, 'secret_key': 32, 'public_key': 64, 'cache': 80, 'signature': 80, 'witness': 88}}
        (self.source / 'claim.json').write_text(json.dumps(self.claim))
        self.trusted = self.root / 'trusted'
        self.trusted.mkdir()
        (self.trusted / 'lean-toolchain').write_text(TOOLCHAIN + '\n')
        self.images = self.root / 'images'
        self.images.mkdir()
        for program in certificate.PROGRAMS:
            (self.images / f'{program}.code').write_bytes(struct.pack('<I', 0x73))
            (self.images / f'{program}.data').write_bytes(b'\x00\xff')
        self.export = self.root / 'candidate.export'
        self.export.write_bytes(b'fixture metadata\n{}\n' * 100)
        self.output = self.source / 'certificate'
        self.hosted = self.root / 'hosted.gz'
        certificate.pack(self.source, self.export, self.images, self.output, self.trusted,
                         proof_url=URL, proof_output=self.hosted)
        self.compressed = self.hosted.read_bytes()
        self.digest = tree_digest(self.source, excluded_top_level={'certificate'}, include_directories=False)
        self.manifest = self.inspect()
        self.destination = self.root / 'expanded'

    def inspect(self):
        return certificate.inspect_bundle(self.output, self.claim, self.digest, TOOLCHAIN)

    def rewrite(self, manifest):
        (self.output / 'manifest.json').write_text(json.dumps(manifest))

    def expand(self, body=None, manifest=None, response=None):
        response = response or Response(self.compressed if body is None else body)
        with patch('certificate.urllib.request.build_opener') as build, \
                patch('certificate.download_proof', side_effect=certificate._download_stream):
            build.return_value.open.return_value = response
            certificate.expand_proof(self.output, manifest or self.manifest, self.destination)
        return build

    def assert_clean(self):
        self.assertFalse(self.destination.exists())
        self.assertFalse(list(self.root.glob('.compressed-proof-*')))

    def test_roundtrip_pack_metadata_and_default_embedded_transport(self):
        proof = self.manifest['proof']
        self.assertEqual(set(proof), {'url', 'sha256', 'bytes', 'expanded_sha256', 'expanded_bytes'})
        self.assertEqual(proof['url'], URL)
        self.assertEqual(proof['bytes'], len(self.compressed))
        self.assertEqual(proof['sha256'], hashlib.sha256(self.compressed).hexdigest())
        self.assertEqual(gzip.decompress(self.compressed), self.export.read_bytes())
        self.assertFalse((self.output / 'proof.export.gz').exists())
        self.expand()
        self.assertEqual(self.destination.read_bytes(), self.export.read_bytes())
        self.assertFalse(list(self.root.glob('.compressed-proof-*')))
        embedded = self.root / 'embedded'
        certificate.pack(self.source, self.export, self.images, embedded, self.trusted)
        self.assertEqual((embedded / 'proof.export.gz').read_bytes(), self.compressed)
        self.assertEqual(certificate.MAX_PROOF_BYTES, 16 * 1024**2)
        self.assertEqual(certificate.MAX_EXPORT_BYTES, 4 * 1024**3)

    def test_initial_url_restrictions(self):
        bad = [
            URL.replace('https:', 'http:'), URL.replace('github.com', 'example.com'),
            URL.replace('github.com', 'github.com.evil.test'),
            URL.replace('github.com', 'user:secret@github.com'),
            URL.replace('github.com', 'user@github.com'),
            URL.replace('github.com', 'github.com:444'),
            URL.replace('github.com', 'github.com:'),
            URL + '?token=secret', URL + '?', URL + '#fragment', URL + '#',
            URL.replace('/releases/download/', '/archive/'),
            URL.replace('/v1/', '/../'), URL.replace('/v1/', '/./'),
            URL.replace('/v1/', '/v1%2Fescape/'), URL.replace('/v1/', '/v1%2fescape/'),
            URL.replace('/v1/', '/%2e%2e/'), URL.replace('/v1/', '/v1%0a/'),
            URL.replace('/v1/', '/v1%252fescape/'), URL + '\\evil',
            URL + '\n', '\t' + URL, URL + '\x7f', URL + '/extra',
            URL.replace('/owner/', '//'), URL.replace('/repo/', '/repo name/'),
        ]
        for url in bad:
            with self.subTest(url=url), self.assertRaises(certificate.CertificateError):
                certificate.validate_proof_url(url)
        self.assertEqual(certificate.validate_proof_url(URL), URL)
        explicit = URL.replace('github.com', 'github.com:443')
        self.assertEqual(certificate.validate_proof_url(explicit), explicit)

    def test_redirects_allow_only_anonymous_github_https_hosts(self):
        handler = certificate.ProofRedirectHandler(float('inf'))
        request = urllib.request.Request(URL, headers={'Authorization': 'secret', 'Cookie': 'session=secret'})
        request.timeout = 60
        for host in ('github.com', 'release-assets.githubusercontent.com', 'objects.githubusercontent.com'):
            url = f'https://{host}/asset?signature=public-signed-url'
            redirected = handler.redirect_request(request, None, 302, 'Found', {}, url)
            self.assertEqual(redirected.full_url, url)
            self.assertIsNone(redirected.get_header('Authorization'))
            self.assertIsNone(redirected.get_header('Cookie'))
        for url in ('http://github.com/asset', 'https://example.com/asset',
                    'https://release-assets.githubusercontent.com.evil.test/asset',
                    'https://user:password@objects.githubusercontent.com/asset',
                    'https://objects.githubusercontent.com:444/asset', 'file:///tmp/proof',
                    'https://objects.githubusercontent.com:/asset',
                    'https://objects.githubusercontent.com/asset#fragment',
                    'https://github.com/asset\n'):
            with self.subTest(url=url), self.assertRaises(certificate.CertificateError):
                handler.redirect_request(request, None, 302, 'Found', {}, url)

    def test_redirect_body_is_closed_without_draining(self):
        handler = certificate.ProofRedirectHandler(float('inf'))
        request = urllib.request.Request(URL)
        response = Mock()
        handler.redirect_request(request, response, 302, 'Found', {},
                                 'https://release-assets.githubusercontent.com/asset')
        response.close.assert_called_once()
        response.read.assert_not_called()

    def test_anonymous_request_disables_proxies_and_ignores_headers(self):
        response = Response(self.compressed)
        with patch.dict(os.environ, {'HTTPS_PROXY': 'http://user:password@evil.test',
                                    'GITHUB_TOKEN': 'secret', 'HTTP_PROXY': 'http://evil.test'}):
            build = self.expand(response=response)
        proxy, redirect = build.call_args.args
        self.assertIsInstance(proxy, urllib.request.ProxyHandler)
        self.assertEqual(proxy.proxies, {})
        self.assertIsInstance(redirect, certificate.ProofRedirectHandler)
        request = build.return_value.open.call_args.args[0]
        self.assertEqual(request.full_url, URL)
        self.assertEqual(dict(request.header_items()), {'Accept-encoding': 'identity', 'Connection': 'close'})
        self.assertEqual(build.return_value.open.call_args.kwargs['timeout'], 60)
        self.assertIsNone(response.length)
        self.assertTrue(response.fp.raw._sock.settimeout.called)

    def test_opener_has_no_auth_or_cookie_handlers(self):
        opener = urllib.request.build_opener(urllib.request.ProxyHandler({}),
                                             certificate.ProofRedirectHandler(float('inf')))
        forbidden = (urllib.request.ProxyHandler, urllib.request.HTTPCookieProcessor,
                     urllib.request.HTTPBasicAuthHandler, urllib.request.HTTPDigestAuthHandler)
        self.assertFalse(any(isinstance(handler, forbidden) for handler in opener.handlers))
        self.assertEqual(sum(isinstance(h, urllib.request.HTTPRedirectHandler) for h in opener.handlers), 1)

    def test_compressed_size_and_digest_checked_before_gzip(self):
        variants = [(self.compressed + b'extra', self.manifest),
                    (self.compressed[:-1], self.manifest)]
        wrong_digest = copy.deepcopy(self.manifest)
        wrong_digest['proof']['sha256'] = '0' * 64
        variants.append((self.compressed, wrong_digest))
        for body, manifest in variants:
            with self.subTest(length=len(body)), patch('certificate.gzip.open') as unzip:
                with self.assertRaises(certificate.CertificateError):
                    self.expand(body, manifest)
                unzip.assert_not_called()
                self.assert_clean()

    def test_read_timeout_connection_error_and_http_status_cleanup(self):
        for error in (TimeoutError('read timeout'), urllib.error.URLError('connection failed')):
            response = Response(self.compressed)
            with patch.object(response, 'read1', side_effect=error):
                with self.assertRaises(certificate.CertificateError):
                    self.expand(response=response)
            self.assert_clean()
        with patch('certificate.urllib.request.build_opener') as build, \
                patch('certificate.download_proof', side_effect=certificate._download_stream):
            build.return_value.open.side_effect = TimeoutError('connect timeout')
            with self.assertRaises(certificate.CertificateError):
                certificate.expand_proof(self.output, self.manifest, self.destination)
        self.assert_clean()
        with self.assertRaises(certificate.CertificateError):
            self.expand(response=Response(self.compressed, status=206))
        self.assert_clean()

    def test_download_deadline_and_redirect_deadline(self):
        with patch('certificate.time.monotonic', side_effect=[0, 0, 301]):
            with self.assertRaisesRegex(certificate.CertificateError, 'deadline'):
                self.expand()
        self.assert_clean()
        handler = certificate.ProofRedirectHandler(0)
        request = urllib.request.Request(URL)
        with self.assertRaisesRegex(certificate.CertificateError, 'deadline'):
            handler.redirect_request(request, None, 302, 'Found', {}, URL)

    def test_supervisor_deadline_kills_transport_child_and_cleans_temp(self):
        with patch('certificate.subprocess.run', side_effect=subprocess.TimeoutExpired('transport', 300)) as run:
            with self.assertRaisesRegex(certificate.CertificateError, 'deadline'):
                certificate.expand_proof(self.output, self.manifest, self.destination)
        self.assert_clean()
        self.assertEqual(run.call_args.kwargs['timeout'], 300)
        self.assertEqual(run.call_args.args[0][:3], [sys.executable, '-I', '-B'])
        self.assertEqual(run.call_args.kwargs['env'], {'PATH': os.defpath, 'LANG': 'C.UTF-8'})
        self.assertEqual(json.loads(run.call_args.kwargs['input']), self.manifest['proof'])

    def test_child_failure_is_structured_and_temp_is_removed(self):
        with patch('certificate.subprocess.run', return_value=SimpleNamespace(returncode=1, stderr=b'failure')):
            with self.assertRaisesRegex(certificate.CertificateError, 'proof download failed: failure'):
                certificate.expand_proof(self.output, self.manifest, self.destination)
        self.assert_clean()

    def test_isolated_child_rejects_invalid_url_without_network(self):
        manifest = copy.deepcopy(self.manifest)
        manifest['proof']['url'] = 'file:///forbidden'
        with self.assertRaisesRegex(certificate.CertificateError, 'proof download failed'):
            certificate.expand_proof(self.output, manifest, self.destination)
        self.assert_clean()

    def test_content_encoding_rejected_and_actual_http_body_ignores_length(self):
        response = Response(self.compressed)
        response.headers['Content-Encoding'] = 'gzip'
        with self.assertRaisesRegex(certificate.CertificateError, 'identity content encoding'):
            self.expand(response=response)
        self.assert_clean()
        wire = io.BytesIO(b'HTTP/1.1 200 OK\r\nContent-Length: 1\r\nConnection: close\r\n\r\n' + self.compressed)
        wire.raw = SimpleNamespace(_sock=Mock())
        response = http.client.HTTPResponse(SimpleNamespace(makefile=lambda *args: wire))
        response.begin()
        response.url = URL
        self.expand(response=response)
        self.assertEqual(self.destination.read_bytes(), self.export.read_bytes())

    def test_raw_redirect_header_controls_rejected_before_normalization(self):
        handler = certificate.ProofRedirectHandler(float('inf'))
        request = urllib.request.Request(URL)
        for location in ('https://github.com/asset\n', '\thttps://github.com/asset',
                         'https://github.com/asset\x7f', '//example.com/asset'):
            with self.subTest(location=location), self.assertRaises(certificate.CertificateError):
                handler.http_error_302(request, Mock(), 302, 'Found', {'Location': location})

    def test_bad_gzip_and_expanded_size_or_digest_cleanup(self):
        bad_gzip = b'not a gzip proof'
        manifest = copy.deepcopy(self.manifest)
        manifest['proof'].update(bytes=len(bad_gzip), sha256=hashlib.sha256(bad_gzip).hexdigest())
        with self.assertRaises(certificate.CertificateError):
            self.expand(bad_gzip, manifest)
        self.assert_clean()
        for change in ({'expanded_bytes': 1}, {'expanded_sha256': '0' * 64}):
            manifest = copy.deepcopy(self.manifest)
            manifest['proof'].update(change)
            with self.assertRaises(certificate.CertificateError):
                self.expand(manifest=manifest)
            self.assert_clean()

    def test_existing_output_not_removed_on_failure(self):
        self.destination.write_bytes(b'existing supervisor output')
        with self.assertRaises(certificate.CertificateError):
            self.expand()
        self.assertEqual(self.destination.read_bytes(), b'existing supervisor output')
        self.assertFalse(list(self.root.glob('.compressed-proof-*')))

    def test_inspection_policy_and_exact_cache_lookup_never_fetch(self):
        with patch('certificate.urllib.request.build_opener', side_effect=AssertionError('unexpected network')):
            self.inspect()
            self.assertTrue(check(self.source)['ok'])
            bundle = tree_digest(self.output)
            key = acceptance_key('a' * 64, self.digest, self.claim, bundle, 'certificate')
            cache = ResultCache(self.root / 'accepted')
            self.assertIsNone(cache.get(key))
            record = {'status': 'verified', 'score': 800, 'claim': self.claim,
                      'source_digest': self.digest, 'context_digest': 'a' * 64,
                      'certificate_digest': bundle, 'mode': 'certificate'}
            cache.put(key, record)
            self.assertEqual(cache.get(key), record)
        changed = copy.deepcopy(self.manifest)
        changed['proof']['sha256'] = '0' * 64
        self.rewrite(changed)
        self.assertNotEqual(bundle, tree_digest(self.output))

    def test_manifest_modes_require_exact_files(self):
        zipped = self.output / 'proof.export.gz'
        zipped.write_bytes(self.compressed)
        with self.assertRaises(certificate.CertificateError):
            self.inspect()
        embedded = copy.deepcopy(self.manifest)
        embedded['proof'].pop('url')
        embedded['proof']['file'] = zipped.name
        self.rewrite(embedded)
        self.inspect()
        zipped.unlink()
        with self.assertRaises(certificate.CertificateError):
            self.inspect()
        self.rewrite(self.manifest)
        extra = self.output / 'extra'
        extra.write_bytes(b'forbidden')
        with self.assertRaises(certificate.CertificateError):
            self.inspect()
        extra.unlink()
        image = self.output / 'verify.data'
        image.unlink()
        with self.assertRaises(certificate.CertificateError):
            self.inspect()

    def test_proof_fields_digests_and_bounds(self):
        changes = [{'file': 'proof.export.gz'}, {'bytes': True}, {'bytes': 0}, {'bytes': -1},
                   {'bytes': certificate.MAX_DETACHED_PROOF_BYTES + 1},
                   {'expanded_bytes': certificate.MAX_EXPORT_BYTES + 1},
                   {'expanded_bytes': True}, {'sha256': 'x' * 64},
                   {'expanded_sha256': None}, {'url': URL + '?auth=secret'}]
        for change in changes:
            manifest = copy.deepcopy(self.manifest)
            manifest['proof'].update(change)
            self.rewrite(manifest)
            with self.subTest(change=change), self.assertRaises(certificate.CertificateError):
                self.inspect()
        self.rewrite(self.manifest)
        manifest = copy.deepcopy(self.manifest)
        manifest['proof']['bytes'] = certificate.MAX_DETACHED_PROOF_BYTES
        self.rewrite(manifest)
        self.inspect()

    def test_pack_detached_limit_without_upload_or_required_proof_copy(self):
        alternate = self.root / 'alternate'
        with patch('certificate.urllib.request.build_opener', side_effect=AssertionError('unexpected network')):
            certificate.pack(self.source, self.export, self.images, alternate, self.trusted, proof_url=URL)
        self.assertFalse((alternate / 'proof.export.gz').exists())
        self.assertEqual(json.loads((alternate / 'manifest.json').read_bytes())['proof'], self.manifest['proof'])
        with patch('certificate.MAX_PROOF_BYTES', 1):
            with self.assertRaises(certificate.CertificateError):
                certificate.pack(self.source, self.export, self.images, self.root / 'too-large', self.trusted)
            certificate.pack(self.source, self.export, self.images, self.root / 'detached', self.trusted,
                             proof_url=URL)
        with patch('certificate.MAX_DETACHED_PROOF_BYTES', 1):
            with self.assertRaises(certificate.CertificateError):
                certificate.pack(self.source, self.export, self.images, self.root / 'too-large-remote',
                                 self.trusted, proof_url=URL)
        self.assertFalse((self.root / 'too-large').exists())
        self.assertFalse((self.root / 'too-large-remote').exists())

    def test_pack_output_refuses_overwrite_and_inside_bundle_paths(self):
        alternate = self.root / 'alternate'
        with self.assertRaises(certificate.CertificateError):
            certificate.pack(self.source, self.export, self.images, alternate, self.trusted,
                             proof_url=URL, proof_output=self.hosted)
        self.assertEqual(self.hosted.read_bytes(), self.compressed)
        with self.assertRaises(certificate.CertificateError):
            certificate.pack(self.source, self.export, self.images, alternate, self.trusted,
                             proof_url=URL, proof_output=alternate / 'nested.gz')
        self.assertFalse(alternate.exists())

    def test_pack_failure_removes_owned_external_copy(self):
        alternate = self.root / 'alternate'
        hosted = self.root / 'partial.gz'
        with patch('certificate.shutil.copyfileobj', side_effect=OSError('disk full')):
            with self.assertRaises(OSError):
                certificate.pack(self.source, self.export, self.images, alternate, self.trusted,
                                 proof_url=URL, proof_output=hosted)
        self.assertFalse(hosted.exists())
        self.assertFalse(alternate.exists())

    def test_bounded_manifest_and_hardlink_rejected(self):
        path = self.output / 'manifest.json'
        raw = path.read_bytes()
        path.write_bytes(b' ' * (certificate.MAX_MANIFEST_BYTES + 1))
        with self.assertRaises(certificate.CertificateError):
            self.inspect()
        path.write_bytes(raw)
        os.link(path, self.root / 'manifest-alias')
        with self.assertRaises(certificate.CertificateError):
            self.inspect()


if __name__ == '__main__':
    unittest.main()
