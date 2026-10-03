#!/usr/bin/env python3
"""Bounded, declarative proof bundles and literal binding to the four raw images."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import http.client
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import zlib
from pathlib import Path

PROGRAMS = ('keygen', 'sign', 'expand', 'verify')
MAX_IMAGE_BYTES = 1 << 20
MAX_PROOF_BYTES = 16 * 1024**2
MAX_DETACHED_PROOF_BYTES = 128 * 1024**2
MAX_EXPORT_BYTES = 4 * 1024**3
MAX_MANIFEST_BYTES = 8192
PROOF_READ_TIMEOUT = 60
PROOF_DOWNLOAD_SECONDS = 300
BINDING_MODULE = 'CertificateBinding'
BINDING_THEOREM = 'SigGolf.Challenge.image_binding'
LITERAL_MODULE = 'SigGolf.CertifiedImages'


class CertificateError(ValueError):
    pass


def validate_proof_url(url: str, *, initial: bool = True) -> str:
    """Accept only public release URLs and GitHub's HTTPS asset redirects."""
    if not isinstance(url, str) or any(ord(c) <= 32 or ord(c) >= 127 for c in url) or '\\' in url:
        raise CertificateError('invalid proof URL')
    try:
        parsed = urllib.parse.urlsplit(url)
        hosts = {'github.com'} if initial else {
            'github.com', 'release-assets.githubusercontent.com', 'objects.githubusercontent.com'}
        if (parsed.scheme != 'https' or parsed.hostname not in hosts or
                parsed.username is not None or parsed.password is not None or
                parsed.port not in (None, 443) or
                parsed.netloc.lower() not in (parsed.hostname, f'{parsed.hostname}:443') or
                parsed.fragment or '#' in url):
            raise CertificateError('proof URL must use an allowed anonymous HTTPS host')
        if initial:
            parts = parsed.path.split('/')
            if (parsed.query or '?' in url or len(parts) != 7 or parts[0] != '' or
                    parts[3:5] != ['releases', 'download'] or
                    any(not re.fullmatch(r'[A-Za-z0-9_.~-]+', part) or part in ('.', '..')
                        for part in (parts[1], parts[2], parts[5], parts[6]))):
                raise CertificateError('proof URL must identify a GitHub release asset')
    except ValueError as exc:
        raise CertificateError('invalid proof URL') from exc
    return url


class ProofRedirectHandler(urllib.request.HTTPRedirectHandler):
    max_redirections = 5
    max_repeats = 2

    def __init__(self, deadline: float):
        self.deadline = deadline

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        # urllib otherwise drains an arbitrarily large redirect body before following it.
        if fp is not None:
            fp.close()
        validate_proof_url(newurl, initial=False)
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise CertificateError('proof download deadline exceeded')
        req.timeout = min(PROOF_READ_TIMEOUT, remaining)
        redirected = super().redirect_request(req, fp, code, msg, headers, newurl)
        if redirected is not None:
            redirected.remove_header('Authorization')
            redirected.remove_header('Cookie')
        return redirected

    def http_error_302(self, req, fp, code, msg, headers):
        location = headers.get('Location', headers.get('URI'))
        if location is not None:
            if (not isinstance(location, str) or
                    any(ord(c) <= 32 or ord(c) >= 127 for c in location) or '\\' in location):
                fp.close()
                raise CertificateError('invalid proof redirect URL')
            validate_proof_url(urllib.parse.urljoin(req.full_url, location), initial=False)
        return super().http_error_302(req, fp, code, msg, headers)

    http_error_301 = http_error_303 = http_error_307 = http_error_308 = http_error_302


def download_proof(proof: dict, destination: Path) -> None:
    """Killable transport-only child bounds DNS, TLS, headers, redirects, and reads."""
    try:
        result = subprocess.run(
            [sys.executable, '-I', '-B', str(Path(__file__).resolve()), '_download', str(destination)],
            input=json.dumps(proof, separators=(',', ':')).encode('ascii'),
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=PROOF_DOWNLOAD_SECONDS,
            env={'PATH': os.defpath, 'LANG': 'C.UTF-8'})
    except subprocess.TimeoutExpired as exc:
        raise CertificateError('proof download deadline exceeded') from exc
    if result.returncode:
        raise CertificateError('proof download failed: ' + result.stderr[:1024].decode('utf-8', errors='replace'))


def _download_stream(proof: dict, destination: Path) -> None:
    url = validate_proof_url(proof['url'])
    if type(proof['bytes']) is not int or not 0 < proof['bytes'] <= MAX_DETACHED_PROOF_BYTES:
        raise CertificateError('detached proof exceeds limit')
    deadline = time.monotonic() + PROOF_DOWNLOAD_SECONDS
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), ProofRedirectHandler(deadline))
    request = urllib.request.Request(url, headers={'Accept-Encoding': 'identity', 'Connection': 'close'})
    digest = hashlib.sha256()
    size = 0
    with opener.open(request, timeout=min(PROOF_READ_TIMEOUT, PROOF_DOWNLOAD_SECONDS)) as response:
        validate_proof_url(response.geturl(), initial=False)
        if response.status != 200:
            raise CertificateError('proof download did not return HTTP 200')
        if response.headers.get('Content-Encoding', 'identity').lower() != 'identity':
            raise CertificateError('proof download must use identity content encoding')
        # HTTP headers are not certificate bounds; consume and count the actual body.
        response.length = None
        with destination.open('wb') as output:
            while True:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise CertificateError('proof download deadline exceeded')
                # read1 performs one buffered/socket read, not an unbounded sequence of reads.
                if response.fp is not None:
                    response.fp.raw._sock.settimeout(min(PROOF_READ_TIMEOUT, remaining))
                chunk = response.read1(min(1024**2, proof['bytes'] - size + 1))
                if time.monotonic() >= deadline:
                    raise CertificateError('proof download deadline exceeded')
                if not chunk:
                    break
                size += len(chunk)
                if size > proof['bytes'] or size > MAX_DETACHED_PROOF_BYTES:
                    raise CertificateError('compressed proof exceeds declared size')
                digest.update(chunk)
                output.write(chunk)
    if size != proof['bytes'] or digest.hexdigest() != proof['sha256']:
        raise CertificateError('compressed proof digest or size mismatch')


def strict_json(raw: bytes | str) -> dict:
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise CertificateError(f'duplicate JSON field: {key}')
            result[key] = value
        return result
    value = json.loads(raw, object_pairs_hook=pairs)
    if not isinstance(value, dict):
        raise CertificateError('expected a JSON object')
    return value


def file_record(path: Path) -> dict:
    if path.is_symlink() or not path.is_file() or path.stat().st_nlink != 1:
        raise CertificateError(f'{path.name}: expected an unlinked regular file')
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024**2), b''):
            digest.update(chunk)
    return {'file': path.name, 'sha256': digest.hexdigest(), 'bytes': path.stat().st_size}


def check_record(root: Path, expected: dict, name: str, limit: int) -> Path:
    if not isinstance(expected, dict) or set(expected) != {'file', 'sha256', 'bytes'}:
        raise CertificateError(f'{name}: invalid file record')
    if expected['file'] != name or type(expected['bytes']) is not int or not 0 <= expected['bytes'] <= limit:
        raise CertificateError(f'{name}: invalid name or size')
    path = root / name
    if path.stat().st_size > limit or file_record(path) != expected:
        raise CertificateError(f'{name}: content does not match manifest')
    return path


def inspect_bundle(root: Path, claim: dict, source_digest: str, toolchain: str) -> dict:
    """Validate transport identity; this does not establish source/certificate provenance."""
    if root.is_symlink() or not root.is_dir():
        raise CertificateError('certificate must be a directory')
    manifest_path = root / 'manifest.json'
    if (manifest_path.is_symlink() or not manifest_path.is_file() or
            manifest_path.stat().st_nlink != 1 or manifest_path.stat().st_size > MAX_MANIFEST_BYTES):
        raise CertificateError('invalid certificate manifest')
    with manifest_path.open('rb') as stream:
        raw = stream.read(MAX_MANIFEST_BYTES + 1)
    if len(raw) > MAX_MANIFEST_BYTES:
        raise CertificateError('invalid certificate manifest')
    manifest = strict_json(raw)
    if set(manifest) != {'version', 'source_digest', 'claim', 'lean_toolchain', 'proof', 'images'}:
        raise CertificateError('invalid certificate manifest fields')
    if type(manifest['version']) is not int or manifest['version'] != 1:
        raise CertificateError('unsupported certificate version')
    if manifest['source_digest'] != source_digest or json.dumps(manifest['claim'], sort_keys=True) != json.dumps(claim, sort_keys=True):
        raise CertificateError('certificate does not identify this source tree and claim')
    if manifest['lean_toolchain'] != toolchain:
        raise CertificateError('certificate toolchain does not match the organizer toolchain')
    proof = manifest['proof']
    fields = {'sha256', 'bytes', 'expanded_sha256', 'expanded_bytes'}
    if not isinstance(proof, dict) or set(proof) not in (fields | {'file'}, fields | {'url'}):
        raise CertificateError('invalid proof record')
    if any(not isinstance(proof[key], str) or not re.fullmatch(r'[0-9a-f]{64}', proof[key])
           for key in ('sha256', 'expanded_sha256')):
        raise CertificateError('invalid proof digest')
    if type(proof['expanded_bytes']) is not int or not 0 < proof['expanded_bytes'] <= MAX_EXPORT_BYTES:
        raise CertificateError('expanded proof exceeds limit')
    allowed = {'manifest.json', *(f'{p}.{s}' for p in PROGRAMS for s in ('code', 'data'))}
    if 'file' in proof:
        allowed.add('proof.export.gz')
    if {p.name for p in root.iterdir()} != allowed:
        raise CertificateError('certificate files do not match the proof transport mode')
    if 'url' in proof:
        validate_proof_url(proof['url'])
        if type(proof['bytes']) is not int or not 0 < proof['bytes'] <= MAX_DETACHED_PROOF_BYTES:
            raise CertificateError('detached proof exceeds limit')
    else:
        check_record(root, {k: proof[k] for k in ('file', 'sha256', 'bytes')}, 'proof.export.gz', MAX_PROOF_BYTES)
    images = manifest['images']
    if not isinstance(images, dict) or set(images) != set(PROGRAMS):
        raise CertificateError('exactly four labeled images are required')
    for program in PROGRAMS:
        image = images[program]
        if not isinstance(image, dict) or set(image) != {'code', 'data'}:
            raise CertificateError(f'{program}: invalid image record')
        for part in ('code', 'data'):
            check_record(root, image[part], f'{program}.{part}', MAX_IMAGE_BYTES - 1)
        if image['code']['bytes'] % 4 or image['code']['bytes'] + image['data']['bytes'] >= MAX_IMAGE_BYTES:
            raise CertificateError(f'{program}: instruction alignment or image bound violated')
    return manifest


def expand_proof(root: Path, manifest: dict, destination: Path) -> None:
    digest = hashlib.sha256()
    size = 0
    compressed = None
    created = False
    try:
        proof_path = root / 'proof.export.gz'
        if 'url' in manifest['proof']:
            with tempfile.NamedTemporaryFile(prefix='.compressed-proof-', suffix='.tmp',
                                             dir=destination.parent, delete=False) as temporary:
                compressed = Path(temporary.name)
            download_proof(manifest['proof'], compressed)
            proof_path = compressed
        with destination.open('xb') as output:
            created = True
            with gzip.open(proof_path, 'rb') as source:
                while chunk := source.read(min(1024**2, MAX_EXPORT_BYTES - size + 1)):
                    size += len(chunk)
                    if size > manifest['proof']['expanded_bytes'] or size > MAX_EXPORT_BYTES:
                        raise CertificateError('expanded proof exceeds declared size')
                    digest.update(chunk)
                    output.write(chunk)
        if size != manifest['proof']['expanded_bytes'] or digest.hexdigest() != manifest['proof']['expanded_sha256']:
            raise CertificateError('expanded proof digest or size mismatch')
    except (OSError, EOFError, zlib.error, http.client.HTTPException,
            urllib.error.URLError, CertificateError) as exc:
        if created:
            destination.unlink(missing_ok=True)
        raise CertificateError(f'invalid compressed proof: {exc}') from exc
    finally:
        if compressed is not None:
            compressed.unlink(missing_ok=True)


def literal_module(images: Path, claim: dict) -> str:
    """Literal bytes, not a hash commitment or candidate-native image evaluation."""
    lines = ['import SigGolf', '', 'namespace SigGolf.CertifiedImages', '']
    for program in PROGRAMS:
        code = (images / f'{program}.code').read_bytes()
        data = (images / f'{program}.data').read_bytes()
        if len(code) % 4 or len(code) + len(data) >= MAX_IMAGE_BYTES:
            raise CertificateError(f'{program}: invalid image')
        words = [str(word[0]) for word in struct.iter_unpack('<I', code)]
        lines += [f'def {program} : SigGolf.Riscv.Image :=',
                  '  { code := [' + ', '.join(words) + '],',
                  '    data := [' + ', '.join(map(str, data)) + '] }', '']
    layout = claim['layout']
    lines += ['def submission : SigGolf.Submission :=',
              f'  {{ sizes := {{ signature := {claim["S"]}, witness := {claim["W"]}, cache := {claim["K"]} }},',
              f'    layout := {{ message := {layout["message"]}, secretKey := {layout["secret_key"]}, publicKey := {layout["public_key"]}, cache := {layout["cache"]}, signature := {layout["signature"]}, witness := {layout["witness"]} }},',
              '    image := fun program => match program with',
              *[f'      | .{program} => {program}' for program in PROGRAMS],
              '  }', '', 'end SigGolf.CertifiedImages', '']
    return '\n'.join(lines)


def binding_module() -> str:
    return ('import Solution\nimport SigGolf.CertifiedImages\n\n'
            'theorem SigGolf.Challenge.image_binding :\n'
            '    SigGolf.Challenge.submission = SigGolf.CertifiedImages.submission := by\n'
            '  rfl\n')


def challenge_source(template: str, claim: dict, *, bind_images: bool = False) -> str:
    substitutions = {key: claim[key] for key in ('S', 'W', 'K', 'C')}
    substitutions.update({key.upper(): value for key, value in claim['layout'].items()})
    for key, value in substitutions.items():
        template = template.replace('{{' + key + '}}', str(value))
    if bind_images:
        template = template.replace('import SigGolf\n', 'import SigGolf\nimport SigGolf.CertifiedImages\n', 1)
        template = template.replace('end SigGolf.Challenge',
            'theorem image_binding : submission = SigGolf.CertifiedImages.submission := sorry\n\nend SigGolf.Challenge')
    return template


def pack(source: Path, export: Path, images: Path, output: Path, trusted: Path, *,
         proof_url: str | None = None, proof_output: Path | None = None) -> None:
    from cache import tree_digest
    from check_submission import check
    policy = check(source)
    if not policy['ok']:
        raise CertificateError('; '.join(policy['errors']))
    if output.exists():
        raise CertificateError('output directory already exists; do not overwrite a frozen bundle')
    if export.is_symlink() or not export.is_file() or not 0 < export.stat().st_size <= MAX_EXPORT_BYTES:
        raise CertificateError('invalid exported proof')
    if proof_url is not None:
        validate_proof_url(proof_url)
    if proof_output is not None:
        if proof_output.exists() or proof_output.is_symlink():
            raise CertificateError('proof output already exists; refusing to overwrite it')
        if proof_output.resolve().is_relative_to(output.resolve()):
            raise CertificateError('proof output must be outside the certificate bundle')
    # Freeze the source identity before adding the certificate subdirectory.
    source_digest = tree_digest(source, excluded_top_level={'certificate'}, include_directories=False)
    output.mkdir(mode=0o700)
    external_created = False
    try:
        image_records = {}
        for program in PROGRAMS:
            image_records[program] = {}
            for part in ('code', 'data'):
                original = images / f'{program}.{part}'
                if original.is_symlink() or not original.is_file() or original.stat().st_size >= MAX_IMAGE_BYTES:
                    raise CertificateError(f'{original.name}: invalid raw image file')
                shutil.copyfile(original, output / original.name)
                image_records[program][part] = file_record(output / original.name)
        digest = hashlib.sha256()
        size = 0
        with export.open('rb') as raw, (output / 'proof.export.gz').open('xb') as zipped:
            with gzip.GzipFile(fileobj=zipped, mode='wb', filename='', mtime=0) as compressor:
                for chunk in iter(lambda: raw.read(1024**2), b''):
                    size += len(chunk)
                    if size > MAX_EXPORT_BYTES:
                        raise CertificateError('export exceeds limit')
                    digest.update(chunk)
                    compressor.write(chunk)
        proof = file_record(output / 'proof.export.gz')
        limit = MAX_DETACHED_PROOF_BYTES if proof_url is not None else MAX_PROOF_BYTES
        if proof['bytes'] > limit:
            raise CertificateError('compressed proof exceeds limit')
        proof.update(expanded_sha256=digest.hexdigest(), expanded_bytes=size)
        if proof_url is not None:
            proof.pop('file')
            proof['url'] = proof_url
        manifest = {'version': 1, 'source_digest': source_digest, 'claim': policy['claim'],
                    'lean_toolchain': (trusted / 'lean-toolchain').read_text().strip(),
                    'proof': proof, 'images': image_records}
        (output / 'manifest.json').write_text(json.dumps(manifest, sort_keys=True, separators=(',', ':')) + '\n')
        if proof_output is not None:
            with proof_output.open('xb') as external:
                external_created = True
                with (output / 'proof.export.gz').open('rb') as zipped:
                    shutil.copyfileobj(zipped, external, length=1024**2)
        if proof_url is not None:
            (output / 'proof.export.gz').unlink()
        inspect_bundle(output, policy['claim'], source_digest, manifest['lean_toolchain'])
    except Exception:
        shutil.rmtree(output)
        if external_created:
            proof_output.unlink(missing_ok=True)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    prepare = commands.add_parser('prepare', help='generate literal and equality modules in a development project')
    prepare.add_argument('--images', type=Path, required=True)
    prepare.add_argument('--source', type=Path, default=Path('submission'))
    prepare.add_argument('--project', type=Path, required=True)
    package = commands.add_parser('pack', help='freeze a previously exported CertificateBinding proof')
    package.add_argument('--images', type=Path, required=True)
    package.add_argument('--source', type=Path, default=Path('submission'))
    package.add_argument('--export', type=Path, required=True)
    package.add_argument('--output', type=Path, default=Path('submission/certificate'))
    package.add_argument('--trusted', type=Path, default=Path(__file__).resolve().parent.parent)
    package.add_argument('--proof-url', help='public GitHub release asset URL; no upload is performed')
    package.add_argument('--proof-output', type=Path, help='save compressed proof outside the bundle for hosting')
    base = commands.add_parser('base', help='export organizer definitions for a checked-base worker')
    base.add_argument('--trusted', type=Path, default=Path(__file__).resolve().parent.parent)
    base.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == 'prepare':
            from check_submission import claim
            values = claim(args.source / 'claim.json')
            # This command never compiles or checks solver source on an unsupported host.
            destination = args.project / 'SigGolf' / 'CertifiedImages.lean'
            binding = args.project / f'{BINDING_MODULE}.lean'
            if destination.exists() or binding.exists():
                raise CertificateError('binding modules already exist; refusing to overwrite them')
            destination.write_text(literal_module(args.images, values))
            binding.write_text(binding_module())
        elif args.command == 'pack':
            pack(args.source, args.export, args.images, args.output, args.trusted,
                 proof_url=args.proof_url, proof_output=args.proof_output)
        else:
            from verify import tools_env, export_targets, run_checked
            import os
            trusted = args.trusted.resolve()
            env = tools_env(trusted)
            targets = export_targets({'theorem_names': ['SigGolf.Certificate'], 'permitted_axioms':
                                      ['propext', 'Quot.sound', 'Classical.choice']})
            if args.output.exists():
                raise CertificateError('base output already exists; refusing to replace an active worker base')
            args.output.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
            code, timeout = run_checked([env['COMPARATOR_LAKE'], 'env', env['COMPARATOR_LEAN4EXPORT'],
                                        'SigGolf', '--', *targets], trusted,
                                       {'PATH': os.environ.get('PATH', '/usr/bin:/bin'),
                                        'HOME': str(Path.home()), 'LANG': 'C.UTF-8'},
                                       args.output, limit=MAX_EXPORT_BYTES, seconds=600,
                                       stderr_log=args.output.with_suffix(args.output.suffix + '.stderr'))
            if code or timeout:
                args.output.unlink(missing_ok=True)
                raise CertificateError('organizer base export failed')
        return 0
    except (OSError, ValueError, RecursionError, json.JSONDecodeError) as exc:
        parser.exit(1, f'certificate: {exc}\n')


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == '_download':
        try:
            raw = sys.stdin.buffer.read(MAX_MANIFEST_BYTES + 1)
            if len(raw) > MAX_MANIFEST_BYTES:
                raise CertificateError('invalid proof download request')
            _download_stream(strict_json(raw), Path(sys.argv[2]))
        except Exception as exc:
            # This child executes only trusted transport code and emits one bounded diagnostic.
            sys.stderr.write(str(exc)[:1024] + '\n')
            raise SystemExit(1)
        raise SystemExit(0)
    raise SystemExit(main())
