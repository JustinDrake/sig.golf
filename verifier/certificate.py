#!/usr/bin/env python3
"""Bounded, declarative proof bundles and literal binding to the four raw images."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import shutil
import struct
import zlib
from pathlib import Path

PROGRAMS = ('keygen', 'sign', 'expand', 'verify')
MAX_IMAGE_BYTES = 1 << 20
MAX_PROOF_BYTES = 16 * 1024**2
MAX_EXPORT_BYTES = 4 * 1024**3
MAX_MANIFEST_BYTES = 8192
BINDING_MODULE = 'CertificateBinding'
BINDING_THEOREM = 'SigGolf.Challenge.image_binding'
LITERAL_MODULE = 'SigGolf.CertifiedImages'


class CertificateError(ValueError):
    pass


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
    allowed = {'manifest.json', 'proof.export.gz', *(f'{p}.{s}' for p in PROGRAMS for s in ('code', 'data'))}
    if {p.name for p in root.iterdir()} != allowed:
        raise CertificateError('certificate must contain exactly the manifest, proof, and eight image files')
    manifest_path = root / 'manifest.json'
    if manifest_path.is_symlink() or manifest_path.stat().st_size > MAX_MANIFEST_BYTES:
        raise CertificateError('invalid certificate manifest')
    manifest = strict_json(manifest_path.read_bytes())
    if set(manifest) != {'version', 'source_digest', 'claim', 'lean_toolchain', 'proof', 'images'}:
        raise CertificateError('invalid certificate manifest fields')
    if type(manifest['version']) is not int or manifest['version'] != 1:
        raise CertificateError('unsupported certificate version')
    if manifest['source_digest'] != source_digest or json.dumps(manifest['claim'], sort_keys=True) != json.dumps(claim, sort_keys=True):
        raise CertificateError('certificate does not identify this source tree and claim')
    if manifest['lean_toolchain'] != toolchain:
        raise CertificateError('certificate toolchain does not match the organizer toolchain')
    proof = manifest['proof']
    if not isinstance(proof, dict) or set(proof) != {'file', 'sha256', 'bytes', 'expanded_sha256', 'expanded_bytes'}:
        raise CertificateError('invalid proof record')
    if type(proof['expanded_bytes']) is not int or not 0 < proof['expanded_bytes'] <= MAX_EXPORT_BYTES:
        raise CertificateError('expanded proof exceeds limit')
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
    try:
        with gzip.open(root / 'proof.export.gz', 'rb') as source, destination.open('xb') as output:
            while chunk := source.read(min(1024**2, MAX_EXPORT_BYTES - size + 1)):
                size += len(chunk)
                if size > manifest['proof']['expanded_bytes'] or size > MAX_EXPORT_BYTES:
                    raise CertificateError('expanded proof exceeds declared size')
                digest.update(chunk)
                output.write(chunk)
        if size != manifest['proof']['expanded_bytes'] or digest.hexdigest() != manifest['proof']['expanded_sha256']:
            raise CertificateError('expanded proof digest or size mismatch')
    except (OSError, EOFError, zlib.error, CertificateError) as exc:
        destination.unlink(missing_ok=True)
        raise CertificateError(f'invalid compressed proof: {exc}') from exc


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


def pack(source: Path, export: Path, images: Path, output: Path, trusted: Path) -> None:
    from cache import tree_digest
    from check_submission import check
    policy = check(source)
    if not policy['ok']:
        raise CertificateError('; '.join(policy['errors']))
    if output.exists():
        raise CertificateError('output directory already exists; do not overwrite a frozen bundle')
    if export.is_symlink() or not export.is_file() or not 0 < export.stat().st_size <= MAX_EXPORT_BYTES:
        raise CertificateError('invalid exported proof')
    # Freeze the source identity before adding the certificate subdirectory.
    source_digest = tree_digest(source, excluded_top_level={'certificate'}, include_directories=False)
    output.mkdir(mode=0o700)
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
        proof.update(expanded_sha256=digest.hexdigest(), expanded_bytes=size)
        manifest = {'version': 1, 'source_digest': source_digest, 'claim': policy['claim'],
                    'lean_toolchain': (trusted / 'lean-toolchain').read_text().strip(),
                    'proof': proof, 'images': image_records}
        (output / 'manifest.json').write_text(json.dumps(manifest, sort_keys=True, separators=(',', ':')) + '\n')
        inspect_bundle(output, policy['claim'], source_digest, manifest['lean_toolchain'])
    except Exception:
        shutil.rmtree(output)
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
            pack(args.source, args.export, args.images, args.output, args.trusted)
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
    raise SystemExit(main())
