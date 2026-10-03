#!/usr/bin/env python3
"""Check one frozen beta PR using a trusted challenge and an isolated comparator.

Local mode is for development only. Linux refuses to compile untrusted code without the
systemd + Landlock sandbox; the checker is never given the GitHub token.
"""
from __future__ import annotations

import argparse
import ctypes
import json
import os
import platform
import re
import selectors
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import uuid
import resource
from contextlib import ExitStack
from pathlib import Path

from cache import ResultCache, acceptance_key, context_digest, tree_digest
from certificate import (BINDING_THEOREM, MAX_EXPORT_BYTES, challenge_source,
                         expand_proof, inspect_bundle, literal_module, strict_json)
from check_submission import check
from fetch import FetchError, fetch_pr
from resources import resource_profile

HERE = Path(__file__).resolve().parent
TRUSTED = HERE.parent
LOG_CAP = 4 * 1024 * 1024
WALL_SECONDS = 4 * 3600
MEMORY_BYTES = 24 * 1024**3


class VerifyError(ValueError):
    pass


def tools_env(root: Path) -> dict[str, str]:
    path = root / 'verifier' / '.tools' / 'env.sh'
    if not path.is_file():
        raise VerifyError('verification tools missing; run verifier/setup_tools.sh')
    values = {}
    for line in path.read_text().splitlines():
        if line.startswith('export ') and '=' in line:
            name, value = line[7:].split('=', 1)
            values[name] = value.strip().strip('"')
    for name in ('COMPARATOR_BIN', 'COMPARATOR_LEAN4EXPORT', 'COMPARATOR_LANDRUN',
                 'COMPARATOR_CERTIFICATE_CHECK', 'COMPARATOR_LEAN', 'COMPARATOR_LAKE'):
        file = Path(values.get(name, ''))
        if not file.is_absolute() or not file.is_file() or not os.access(file, os.X_OK):
            raise VerifyError(f'{name} must point to an installed executable')
    return values


def clone_tree(src: Path, dst: Path) -> None:
    if platform.system() == 'Darwin':
        cmd = ['cp', '-c', '-R', str(src), str(dst)]
    else:
        cmd = ['cp', '-a', '--reflink=auto', str(src), str(dst)]
    subprocess.run(cmd, check=True, timeout=600, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)


def linux_preflight(env: dict[str, str]) -> None:
    if os.geteuid() == 0:
        raise VerifyError('refusing to compile candidate code as root')
    if not shutil.which('systemd-run') or not shutil.which('systemctl'):
        raise VerifyError('systemd user services are required on Linux')
    lsm = Path('/sys/kernel/security/lsm')
    if not lsm.is_file() or 'landlock' not in lsm.read_text().strip().split(','):
        raise VerifyError('Landlock is not enabled')
    if Path(env['COMPARATOR_LANDRUN']).open('rb').read(4) != b'\x7fELF':
        raise VerifyError('a compiled Landrun binary is required on Linux')
    if platform.machine() not in {'x86_64', 'aarch64', 'riscv64'}:
        raise VerifyError('unsupported Linux architecture')
    libc = ctypes.CDLL(None, use_errno=True)
    libc.syscall.restype = ctypes.c_long
    abi = int(libc.syscall(ctypes.c_long(444), ctypes.c_void_p(), ctypes.c_size_t(0), ctypes.c_uint(1)))
    if abi < 3:
        raise VerifyError('Landlock ABI 3 or newer is required')


def linux_command(cmd: list[str], project: Path, env: dict[str, str], hidden: list[Path],
                  seconds: int = WALL_SECONDS, lean_path: str | None = None) -> tuple[list[str], dict[str, str]]:
    unit = 'sig-verify-' + uuid.uuid4().hex[:12]
    profile = resource_profile()
    properties = [f'MemoryMax={profile.memory_bytes}', 'MemorySwapMax=0', f'RuntimeMaxSec={seconds}',
                  f'CPUAffinity={" ".join(map(str, profile.cpu_affinity))}',
                  'KillMode=control-group', 'TimeoutStopSec=5', 'SendSIGKILL=yes', 'TasksMax=512',
                  'RestrictAddressFamilies=~AF_UNIX', 'NoNewPrivileges=yes', 'ProtectSystem=strict',
                  f'ReadWritePaths={project / ".lake"}', 'PrivateTmp=yes', 'PrivatePIDs=yes', 'ProcSubset=pid',
                  'InaccessiblePaths=/sys',
                  'InaccessiblePaths=' + ' '.join(f'-{p}' for p in ['/etc/ots', '/etc/sig-golf', *hidden]),
                  'PrivateDevices=yes', 'TemporaryFileSystem=/dev/shm', 'PrivateIPC=yes',
                  'SystemCallErrorNumber=EPERM',
                  'SystemCallFilter=~@network-io @debug ptrace process_vm_readv process_vm_writev '
                  'pidfd_getfd kill tkill tgkill pidfd_send_signal']
    clean = {'PATH': f'{Path(env["COMPARATOR_LEAN"]).parent}:{Path.home() / ".elan/bin"}:{os.environ.get("PATH", "/usr/bin:/bin")}',
             'HOME': str(Path.home()), 'LANG': 'C.UTF-8',
              'COMPARATOR_LANDRUN': env['COMPARATOR_LANDRUN'],
              'COMPARATOR_LEAN4EXPORT': env['COMPARATOR_LEAN4EXPORT'],
              'LEAN_NUM_THREADS': str(profile.build_jobs),
              'LEAN_ABORT_ON_PANIC': '1',
             'SIG_VERIFIER_HOST_DEV': str(Path('/dev').stat().st_dev),
             'SIG_VERIFIER_HOST_PIDNS': str(Path('/proc/self/ns/pid').stat().st_ino),
              'SIG_VERIFIER_HOST_SHM_DEV': str(Path('/dev/shm').stat().st_dev)}
    if lean_path is not None:
        clean['LEAN_PATH'] = lean_path
    command = ['/usr/bin/env', '-i', *[f'{k}={v}' for k, v in clean.items()],
               sys.executable, str(HERE / 'linux_exec.py'), *cmd]
    runtime = os.environ.get('XDG_RUNTIME_DIR', f'/run/user/{os.getuid()}')
    bus_env = {'PATH': clean['PATH'], 'HOME': clean['HOME'], 'XDG_RUNTIME_DIR': runtime,
               'DBUS_SESSION_BUS_ADDRESS': os.environ.get('DBUS_SESSION_BUS_ADDRESS', f'unix:path={runtime}/bus')}
    return (['systemd-run', '--user', '--wait', '--collect', '--pipe', '--quiet', f'--unit={unit}',
             f'--working-directory={project}',
             *[arg for prop in properties for arg in ('-p', prop)], '--', *command], bus_env)


def run_checked(cmd: list[str], cwd: Path, env: dict[str, str], log: Path,
                *, limit: int = LOG_CAP, seconds: int = WALL_SECONDS,
                stderr_log: Path | None = None) -> tuple[int, bool]:
    """Bound output and time; oversized proof exports fail rather than being truncated."""
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (seconds + 1, seconds + 1))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE if stderr_log is not None else subprocess.STDOUT,
                            start_new_session=True, bufsize=0, preexec_fn=limits)
    deadline = time.monotonic() + seconds
    truncated = False
    timed_out = False
    try:
        with ExitStack() as stack:
            selector = stack.enter_context(selectors.DefaultSelector())
            outputs = {'stdout': stack.enter_context(log.open('wb'))}
            caps = {'stdout': limit, 'stderr': LOG_CAP}
            kept = {'stdout': 0, 'stderr': 0}
            streams = [(proc.stdout, 'stdout')]
            if stderr_log is not None:
                outputs['stderr'] = stack.enter_context(stderr_log.open('wb'))
                streams.append((proc.stderr, 'stderr'))
            for stream, channel in streams:
                os.set_blocking(stream.fileno(), False)
                selector.register(stream, selectors.EVENT_READ, channel)
            while selector.get_map() and not timed_out:
                remain = deadline - time.monotonic()
                if remain <= 0:
                    timed_out = True
                    break
                for selected, _events in selector.select(remain):
                    channel = selected.data
                    try:
                        chunk = os.read(selected.fd, 65536)
                    except BlockingIOError:
                        continue
                    if not chunk:
                        selector.unregister(selected.fileobj)
                        continue
                    before = kept[channel]
                    if before < caps[channel]:
                        outputs[channel].write(chunk[:caps[channel] - before])
                        kept[channel] += min(len(chunk), caps[channel] - before)
                    if before + len(chunk) > caps[channel] and channel == 'stdout':
                        truncated = True
                        if limit != LOG_CAP:
                            timed_out = True
                            break
            if truncated:
                outputs['stdout'].write(b'\n[output truncated]\n')
        if not timed_out:
            proc.wait(timeout=max(.1, deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        timed_out = True
    except BaseException:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()
        raise
    finally:
        if timed_out:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
        proc.stdout.close()
        if proc.stderr is not None:
            proc.stderr.close()
    return proc.returncode, timed_out


def export_targets(config: dict) -> list[str]:
    primitives = ['Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod',
                  'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft',
                  'Nat.shiftRight', 'String.ofList', 'Char.ofNat', 'List', 'eagerReduce']
    return config['theorem_names'] + config['permitted_axioms'] + primitives + config.get('definition_names', [])


def landrun_command(cmd: list[str], project: Path, env: dict[str, str], *, build: bool) -> list[str]:
    # Same inner build/export permissions as the pinned comparator. Candidate output is
    # collected by the supervisor outside the writable build tree before kernel checking.
    prefix = subprocess.check_output([env['COMPARATOR_LEAN'], '--print-prefix'], cwd=project, text=True, timeout=30).strip()
    command = [env['COMPARATOR_LANDRUN'], '--best-effort', '--ro', '/', '--rw', '/dev', '-ldd', '-add-exec']
    for name in ('PATH', 'HOME', 'LEAN_PATH', 'LEAN_ABORT_ON_PANIC', 'LEAN_NUM_THREADS'):
        command += ['--env', name]
    command += ['--ro', str(project), '--rox', prefix]
    if build:
        command += ['--rwx', str(project / '.lake'), '--rox', shutil.which('git') or '/usr/bin/git']
        if cmd[1:3] == ['env', '/usr/bin/printenv']:
            command += ['--rox', '/usr/bin/printenv']
    else:
            # Explicitly allow only the pinned exporter, never arbitrary candidate binaries.
        command += ['--rox', env['COMPARATOR_LEAN4EXPORT']]
    return [*command, '--', *cmd]


def tail_text(path: Path, limit: int = 1200) -> str:
    with path.open('rb') as stream:
        stream.seek(max(0, path.stat().st_size - limit))
        return stream.read(limit).decode(errors='replace')


def verify(args: argparse.Namespace) -> dict:
    work = args.work.resolve()
    if work.exists():
        raise VerifyError('work directory must not exist')
    work.mkdir(parents=True)
    log = work / 'verify.log'
    started = time.monotonic()
    result = {'status': 'failed', 'commit': args.commit, 'contract_commit': None,
              'log': str(log), 'claim': None, 'timings_seconds': {}, 'cache_hit': False}
    log.touch()
    try:
        env = tools_env(args.trusted)
        contract = subprocess.run(['git', '-C', str(args.trusted), 'rev-parse', 'HEAD'],
                                  check=True, text=True, capture_output=True, timeout=10).stdout.strip()
        result['contract_commit'] = contract
        if not re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', contract):
            raise VerifyError('trusted checkout has no canonical commit')
        source = work / 'source'
        if args.local:
            shutil.copytree(args.local, source, symlinks=True)
        else:
            fetch_pr(args.repository, args.pr, args.commit, source)
        # Structural bounds are always checked. An exact accepted key already binds
        # the prior full import-policy decision; only a miss repeats that source scan.
        policy = check(source, scan_imports=False)
        result['claim'] = policy['claim']
        if not policy['ok']:
            result.update(status='policy_rejected', errors=policy['errors'])
            log.write_text('\n'.join(policy['errors']) + '\n')
            return result
        mode = 'certificate' if (source / 'certificate').exists() else 'source'
        result.update(mode=mode, source_compiled=mode == 'source')
        preview = args.preview
        if preview and mode != 'certificate':
            raise VerifyError('preview is only available for declarative certificates, never candidate source execution')
        if platform.system() != 'Linux' and not preview:
            raise VerifyError('official verification requires supported Linux; use --preview for a non-scoring certificate check')
        if preview:
            result['preview'] = True
        if platform.system() == 'Linux':
            linux_preflight(env)
        source_hash = tree_digest(source, excluded_top_level={'certificate'}, include_directories=False)
        context_hash = context_digest(args.trusted, env)
        bundle_hash = None
        manifest = None
        if mode == 'certificate':
            manifest = inspect_bundle(source / 'certificate', policy['claim'], source_hash,
                                      (args.trusted / 'lean-toolchain').read_text().strip())
            bundle_hash = tree_digest(source / 'certificate')
        result.update(source_digest=source_hash, context_digest=context_hash, certificate_digest=bundle_hash)
        cache = None
        cache_error = None
        # Source elaborators can inspect arbitrary inputs such as time or process state.
        # Only a frozen declarative certificate has an exact reusable checked object.
        if not args.no_cache and not preview and mode == 'certificate':
            try:
                cache = ResultCache(args.cache_dir)
            except (OSError, ValueError) as exc:
                cache_error = str(exc)
        key = acceptance_key(context_hash, source_hash, policy['claim'], bundle_hash, mode)
        result['acceptance_key'] = key
        if cache is not None and not args.reverify and not args.fresh_kernel:
            accepted = cache.get(key)
            if accepted is not None:
                result.update(accepted, cache_hit=True)
                log.write_text('Exact organizer-owned acceptance record reused; no changed proof accepted.\n')
                return result
        policy = check(source)
        if not policy['ok']:
            result.update(status='policy_rejected', errors=policy['errors'])
            log.write_text('\n'.join(policy['errors']) + '\n')
            return result
        project = work / 'project'
        project.mkdir()
        for name in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'SigGolf.lean'):
            shutil.copy2(args.trusted / name, project / name)
        shutil.copytree(args.trusted / 'SigGolf', project / 'SigGolf')
        profile = resource_profile() if platform.system() == 'Linux' else None
        lakefile = (project / 'lakefile.lean').read_text()
        if profile is not None:
            lakefile = lakefile.replace('package SigGolf where\n',
                f'package SigGolf where\n  moreLeanArgs := #["-j{profile.lean_threads}"]\n', 1)
            result['resources'] = {'profile': profile.name, 'cpus': profile.cpus,
                                  'memory_bytes': profile.memory_bytes, 'build_jobs': profile.build_jobs,
                                  'lean_threads': profile.lean_threads}
        (project / 'lakefile.lean').write_text(lakefile + '\nlean_lib Solution\n')
        challenge = challenge_source((args.trusted / 'verifier' / 'Challenge.lean.in').read_text(),
                                     policy['claim'], bind_images=mode == 'certificate')
        if manifest is not None:
            (project / 'SigGolf' / 'CertifiedImages.lean').write_text(literal_module(source / 'certificate', policy['claim']))
            expand_proof(source / 'certificate', manifest, work / 'candidate.export')
        (project / 'SigGolf' / 'Challenge.lean').write_text(challenge)
        clone_tree(args.trusted / '.lake', project / '.lake')
        # Drop every cached artifact of candidate, solution, and challenge modules: the module
        # directories and the root-module files (.olean, .ilean, .trace, .hash, .c) beside them.
        for folder in (project / '.lake' / 'build' / 'lib' / 'lean', project / '.lake' / 'build' / 'ir'):
            for name in ('SigGolfCandidate', 'Solution'):
                if (folder / name).is_dir():
                    shutil.rmtree(folder / name)
                for stale in folder.glob(f'{name}.*'):
                    stale.unlink()
            for stale in (folder / 'SigGolf').glob('Challenge.*'):
                stale.unlink()
            for stale in (folder / 'SigGolf').glob('CertifiedImages.*'):
                stale.unlink()
        config = strict_json((args.trusted / 'verifier' / 'comparator.json').read_bytes())
        if manifest is not None:
            config['theorem_names'].append(BINDING_THEOREM)
        config_path = work / 'checker.json'
        config_path.write_text(json.dumps(config))
        targets = export_targets(config)
        hidden = [source, cache.path if cache is not None else args.cache_dir.absolute(), *args.hide]
        lean_path = None

        def phase(name: str, command: list[str], output: Path, *, build=False, export=False) -> None:
            remaining = int(WALL_SECONDS - (time.monotonic() - started))
            if remaining < 1:
                raise TimeoutError('overall verification deadline exceeded')
            environment = {'PATH': f'{Path(env["COMPARATOR_LEAN"]).parent}:{Path.home() / ".elan/bin"}:{os.environ.get("PATH", "/usr/bin:/bin")}',
                           'HOME': str(Path.home()), 'LANG': 'C.UTF-8', 'LEAN_ABORT_ON_PANIC': '1'}
            if profile is not None:
                environment['LEAN_NUM_THREADS'] = str(profile.build_jobs)
            if lean_path is not None:
                environment['LEAN_PATH'] = lean_path
            if build or export:
                command = landrun_command(command, project, env, build=build)
            if platform.system() == 'Linux':
                command, environment = linux_command(command, project, env, hidden, seconds=remaining, lean_path=lean_path)
                environment['LEAN_ABORT_ON_PANIC'] = '1'
            began = time.monotonic()
            error_output = output.with_suffix(output.suffix + '.stderr') if export else None
            try:
                code, timeout = run_checked(command, project, environment, output,
                    limit=MAX_EXPORT_BYTES if export else LOG_CAP, seconds=remaining, stderr_log=error_output)
            except BaseException:
                if platform.system() == 'Linux':
                    unit = next(arg.split('=', 1)[1] for arg in command if arg.startswith('--unit='))
                    subprocess.run(['/usr/bin/systemctl', '--user', 'stop', unit], env=environment,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
                raise
            result['timings_seconds'][name] = time.monotonic() - began
            if not export:
                with log.open('ab') as aggregate:
                    aggregate.write(f'\n[{name}]\n'.encode())
                    aggregate.write(output.read_bytes())
            if timeout:
                if platform.system() == 'Linux':
                    unit = next(arg.split('=', 1)[1] for arg in command if arg.startswith('--unit='))
                    subprocess.run(['/usr/bin/systemctl', '--user', 'stop', unit], env=environment,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=30)
                raise TimeoutError(f'{name}: deadline or output limit exceeded')
            if code:
                if name in ('solution_build', 'solution_export', 'checker'):
                    result['status'] = 'rejected'
                diagnostic = tail_text(error_output) if error_output is not None and error_output.exists() else tail_text(output)
                raise VerifyError(f'{name}: child exited with {code}: {diagnostic}')

        # Resolve Lake's environment only while the project contains trusted inputs.
        # Re-running `lake env` after candidate compilation would consult writable config.
        phase('environment', [env['COMPARATOR_LAKE'], 'env', '/usr/bin/printenv', 'LEAN_PATH'],
              work / 'environment.log', build=True)
        path_lines = (work / 'environment.log').read_text().strip().splitlines()
        lean_path = path_lines[-1] if path_lines else ''
        if not lean_path or '\x00' in lean_path:
            raise VerifyError('Lake did not provide a valid Lean search path')
        phase('challenge_build', [env['COMPARATOR_LAKE'], 'build', 'SigGolf.Challenge'], work / 'challenge-build.log', build=True)
        phase('challenge_export', [env['COMPARATOR_LEAN4EXPORT'], 'SigGolf.Challenge', '--', *targets],
              work / 'challenge.export', export=True)
        # Only after freezing the trusted challenge may candidate sources enter the project.
        if mode == 'source':
            if (source / 'SigGolfCandidate').is_dir():
                shutil.copytree(source / 'SigGolfCandidate', project / 'SigGolfCandidate')
            shutil.copy2(source / 'Solution.lean', project / 'Solution.lean')
            phase('solution_build', [env['COMPARATOR_LAKE'], 'build', 'Solution'], work / 'solution-build.log', build=True)
            phase('solution_export', [env['COMPARATOR_LEAN4EXPORT'], 'Solution', '--', *targets],
                  work / 'candidate.export', export=True)
        checker_command = [env['COMPARATOR_CERTIFICATE_CHECK'], str(config_path),
                           str(work / 'challenge.export'), str(work / 'candidate.export')]
        if args.worker and not args.fresh_kernel and not preview:
            from worker import check as worker_check
            import hashlib
            with Path(env['COMPARATOR_CERTIFICATE_CHECK']).open('rb') as checker_file:
                checker_digest = hashlib.file_digest(checker_file, 'sha256').hexdigest()
            began = time.monotonic()
            report = worker_check(args.worker, {'id': uuid.uuid4().hex, 'config': str(config_path),
                'trusted': str(work / 'challenge.export'), 'candidate': str(work / 'candidate.export'), 'fresh_kernel': False},
                checker_digest, expected_context_digest=context_hash,
                timeout=max(1, WALL_SECONDS - (time.monotonic() - started)))
            result['timings_seconds']['checker'] = time.monotonic() - began
        else:
            phase('checker', checker_command, work / 'checker.log')
            report = strict_json((work / 'checker.log').read_bytes())
        if report['status'] != 'verified':
            if report['status'] == 'rejected':
                result['status'] = 'rejected'
            raise VerifyError(f'checker rejected certificate: {report}')
        if context_digest(args.trusted, env) != context_hash:
            raise VerifyError('trusted inputs changed during verification; refusing to publish acceptance')
        result.update(status='kernel_checked' if preview else 'verified', checker=report)
        if not preview:
            result['score'] = policy['score']
        if cache is not None:
            try:
                cache.put(key, result)
            except (OSError, ValueError) as exc:
                cache_error = str(exc)
        if cache_error:
            result['cache_warning'] = cache_error
        return result
    except TimeoutError as exc:
        result.update(status='timeout', reason=str(exc))
        return result
    except (FetchError, VerifyError, OSError, subprocess.SubprocessError, ValueError, RecursionError) as exc:
        result.update(status='rejected' if result['status'] == 'rejected' else 'failed', reason=str(exc)[:1200])
        return result
    finally:
        result['timings_seconds']['total'] = time.monotonic() - started
        (work / 'telemetry-verification.json').write_text(json.dumps(result, sort_keys=True) + '\n')


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--repository', default='leanEthereum/sig.golf-submissions')
    parser.add_argument('--pr', type=int)
    parser.add_argument('--commit')
    parser.add_argument('--local', type=Path)
    parser.add_argument('--trusted', type=Path, default=TRUSTED)
    parser.add_argument('--work', type=Path)
    parser.add_argument('--hide', type=Path, action='append', default=[])
    parser.add_argument('--cleanup', action='store_true')
    parser.add_argument('--cache-dir', type=Path, default=Path.home() / '.cache' / 'sig-golf' / 'accepted')
    parser.add_argument('--no-cache', action='store_true', help='do not read or publish exact acceptance records')
    parser.add_argument('--reverify', action='store_true', help='bypass exact-result reuse and check the proof again')
    parser.add_argument('--fresh-kernel', action='store_true', help='bypass result and worker reuse; replay from empty')
    parser.add_argument('--worker', type=Path, help='optional organizer-owned local checked-base worker socket')
    parser.add_argument('--preview', action='store_true', help='non-scoring certificate check; no production cache or hard memory isolation')
    args = parser.parse_args()
    if bool(args.local) == bool(args.pr and args.commit):
        parser.error('provide either --local or both --pr and --commit')
    args.trusted = args.trusted.resolve()
    if args.work is None:
        args.work = Path(tempfile.mkdtemp(prefix='sig-verify-'))
        args.work.rmdir()
    result = verify(args)
    if args.cleanup and args.work.exists():
        try:
            # Candidate code can change permissions inside its writable build tree.
            for directory, children, _ in os.walk(args.work, followlinks=False):
                os.chmod(directory, os.stat(directory).st_mode | 0o700)
                for child in children:
                    path = Path(directory) / child
                    if not path.is_symlink():
                        os.chmod(path, path.stat().st_mode | 0o700)
            shutil.rmtree(args.work)
        except OSError as exc:
            result.update(status='failed', reason=f'workspace cleanup failed: {exc}')
    print(json.dumps(result, sort_keys=True))
    return 0 if result['status'] in ('verified', 'kernel_checked') else 1


if __name__ == '__main__':
    raise SystemExit(main())
