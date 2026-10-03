import argparse
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from certificate import pack
from verify import verify, landrun_command


class PipelineTests(unittest.TestCase):
    """Supervisor orchestration tests; native kernel correctness is tested separately."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.trusted = self.root / 'trusted'
        (self.trusted / 'SigGolf').mkdir(parents=True)
        for name in ('SigGolf.lean', 'lakefile.lean', 'lake-manifest.json'):
            (self.trusted / name).write_text('package SigGolf where\n' if name == 'lakefile.lean' else '{}')
        (self.trusted / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        (self.trusted / 'verifier').mkdir()
        here = Path(__file__).resolve().parents[1]
        for name in ('Challenge.lean.in', 'comparator.json'):
            (self.trusted / 'verifier' / name).write_bytes((here / name).read_bytes())
        self.source = self.root / 'submission'
        self.source.mkdir()
        (self.source / 'Solution.lean').write_text('import SigGolf\n')
        claim = {'S': 8, 'W': 8, 'K': 0, 'C': 100, 'layout':
                 {'message': 0, 'secret_key': 32, 'public_key': 64, 'cache': 80, 'signature': 80, 'witness': 88}}
        (self.source / 'claim.json').write_text(json.dumps(claim))
        self.calls = []
        self.failure = None
        self.profile = SimpleNamespace(name='conservative', cpus=2, memory_bytes=24 * 1024**3,
                                       build_jobs=4, lean_threads=1, cpu_affinity=(0, 1))
        self.env = {key: str(self.root / key) for key in ('COMPARATOR_BIN', 'COMPARATOR_LEAN4EXPORT',
            'COMPARATOR_LANDRUN', 'COMPARATOR_CERTIFICATE_CHECK', 'COMPARATOR_LEAN', 'COMPARATOR_LAKE')}
        self.patches = [patch('verify.tools_env', return_value=self.env),
            patch('verify.platform.system', return_value='Linux'), patch('verify.linux_preflight'),
            patch('verify.context_digest', return_value='a' * 64),
            patch('verify.subprocess.run', return_value=SimpleNamespace(stdout='b' * 40)),
            patch('verify.resource_profile', return_value=self.profile), patch('verify.clone_tree', side_effect=self.clone),
            patch('verify.landrun_command', side_effect=lambda cmd, *_args, **_kwargs: cmd),
            patch('verify.linux_command', side_effect=lambda cmd, *_args, **_kwargs: (cmd, {})),
            patch('verify.run_checked', side_effect=self.run_phase)]
        for mocked in self.patches:
            mocked.start()

    def tearDown(self):
        for mocked in reversed(self.patches):
            mocked.stop()
        self.temp.cleanup()

    def clone(self, _source, destination):
        (destination / 'build' / 'lib' / 'lean' / 'SigGolf').mkdir(parents=True)
        (destination / 'build' / 'ir' / 'SigGolf').mkdir(parents=True)

    def args(self, number=1, **changes):
        value = argparse.Namespace(work=self.root / f'work-{number}', commit=None, trusted=self.trusted,
            local=self.source, repository=None, pr=None, hide=[], cache_dir=self.root / 'cache',
            no_cache=False, reverify=False, fresh_kernel=False, worker=None, preview=False)
        for key, item in changes.items():
            setattr(value, key, item)
        return value

    def run_phase(self, command, project, environment, output, **kwargs):
        self.calls.append(output.name)
        if output.name == 'challenge-build.log':
            self.assertFalse((project / 'Solution.lean').exists())
            self.assertFalse((project / 'SigGolfCandidate').exists())
        if output.name == 'checker.log':
            output.write_text(json.dumps({'status': 'verified', 'error': None,
                'phases_seconds': {'parse': 0.1, 'compare': 0.1, 'axioms': 0.1, 'kernel': 0.1}}))
        else:
            output.write_text('fixture output\n')
        if output.name == self.failure:
            output.write_text('uncaught exception: fixture rejected\n')
            return 1, False
        return 0, False

    def make_certificate(self):
        images = self.root / 'images'
        images.mkdir()
        for program in ('keygen', 'sign', 'expand', 'verify'):
            (images / f'{program}.code').write_bytes(b'\x73\x00\x00\x00')
            (images / f'{program}.data').write_bytes(b'')
        export = self.root / 'fixture.export'
        export.write_bytes(b'fixture output\n')
        pack(self.source, export, images, self.source / 'certificate', self.trusted)

    def test_source_pipeline_order_and_no_result_reuse(self):
        first = verify(self.args())
        self.assertEqual(first['status'], 'verified', first)
        self.assertEqual(self.calls, ['challenge-build.log', 'challenge.export', 'solution-build.log',
                                     'candidate.export', 'checker.log'])
        self.calls.clear()
        second = verify(self.args(2))
        self.assertFalse(second['cache_hit'], second)
        self.assertEqual(second['contract_commit'], 'b' * 40)
        self.assertIn('solution-build.log', self.calls)
        self.assertTrue((self.root / 'work-2' / 'telemetry-verification.json').exists())

    def test_reverify_and_fresh_kernel_bypass_result_cache(self):
        self.make_certificate()
        verify(self.args())
        for index, option in enumerate(('reverify', 'fresh_kernel'), 2):
            self.calls.clear()
            result = verify(self.args(index, **{option: True}))
            self.assertEqual(result['status'], 'verified')
            self.assertFalse(result['cache_hit'])
            self.assertIn('checker.log', self.calls)

    def test_certificate_skips_candidate_execution(self):
        self.make_certificate()
        result = verify(self.args())
        self.assertEqual(result['status'], 'verified', result)
        self.assertEqual(result['mode'], 'certificate')
        self.assertFalse(result['source_compiled'])
        self.assertEqual(self.calls, ['challenge-build.log', 'challenge.export', 'checker.log'])
        config = json.loads((self.root / 'work-1' / 'checker.json').read_bytes())
        self.assertIn('SigGolf.Challenge.image_binding', config['theorem_names'])
        self.assertNotIn('SigGolf.CertifiedImages.submission', config['definition_names'])

    def test_invalid_certificate_never_falls_back_to_source(self):
        self.make_certificate()
        (self.source / 'certificate' / 'verify.code').write_bytes(b'bad')
        result = verify(self.args())
        self.assertEqual(result['status'], 'policy_rejected', result)
        self.assertEqual(self.calls, [])
        self.assertNotIn('score', result)

    def test_source_and_context_changes_miss_cache(self):
        self.make_certificate()
        verify(self.args())
        (self.source / 'Solution.lean').write_text('import SigGolf\n-- changed\n')
        self.calls.clear()
        changed = verify(self.args(2))
        self.assertEqual(changed['status'], 'policy_rejected')
        (self.source / 'Solution.lean').write_text('import SigGolf\n')
        with patch('verify.context_digest', return_value='c' * 64):
            self.calls.clear()
            result = verify(self.args(3))
            self.assertFalse(result['cache_hit'])
            self.assertIn('checker.log', self.calls)

    def test_exact_certificate_result_reuse(self):
        self.make_certificate()
        first = verify(self.args())
        self.assertEqual(first['status'], 'verified', first)
        self.calls.clear()
        second = verify(self.args(2))
        self.assertTrue(second['cache_hit'], second)
        self.assertEqual(self.calls, [])

    def test_rejection_emits_no_score_and_is_not_cached(self):
        self.make_certificate()
        self.failure = 'checker.log'
        failed = verify(self.args())
        self.assertEqual(failed['status'], 'rejected', failed)
        self.assertNotIn('score', failed)
        self.failure = None
        self.calls.clear()
        result = verify(self.args(2))
        self.assertFalse(result['cache_hit'])
        self.assertIn('checker.log', self.calls)

    def test_source_never_runs_on_unsupported_host(self):
        with patch('verify.platform.system', return_value='Darwin'):
            result = verify(self.args())
        self.assertEqual(result['status'], 'failed')
        self.assertEqual(self.calls, [])

    def test_preview_never_scores_or_populates_acceptance_cache(self):
        self.make_certificate()
        with patch('verify.platform.system', return_value='Darwin'):
            result = verify(self.args(preview=True))
        self.assertEqual(result['status'], 'kernel_checked', result)
        self.assertNotIn('score', result)
        self.assertFalse((self.root / 'cache').exists())

    def test_worker_rejection_is_a_proof_rejection(self):
        self.make_certificate()
        Path(self.env['COMPARATOR_CERTIFICATE_CHECK']).write_bytes(b'fixture checker identity')
        with patch('worker.check', return_value={'status': 'rejected', 'error': 'invalid proof'}):
            result = verify(self.args(worker=self.root / 'worker.sock'))
        self.assertEqual(result['status'], 'rejected', result)
        self.assertNotIn('score', result)

    def test_exporter_has_an_explicit_execute_grant(self):
        # Exercise command construction, which pipeline mocks intentionally isolate.
        with patch('verify.subprocess.check_output', return_value='/trusted/lean\n'):
            command = landrun_command([self.env['COMPARATOR_LAKE'], 'env', self.env['COMPARATOR_LEAN4EXPORT']],
                                      self.trusted, self.env, build=False)
        self.assertIn(['--rox', self.env['COMPARATOR_LEAN4EXPORT']],
                      [command[i:i + 2] for i in range(len(command) - 1)])

    def test_wrapper_help_does_not_remove_previous_score(self):
        import subprocess
        script = Path(__file__).resolve().parents[2] / 'scripts' / 'run.py'
        scripts = self.root / 'scripts'
        scripts.mkdir()
        score = scripts / 'score.json'
        score.write_text('previous score')
        # The test's global subprocess.run patch is only for the verifier's git probe.
        self.patches[4].stop()
        try:
            completed = subprocess.run([sys.executable, str(script), '--help'], cwd=self.root,
                                       capture_output=True, text=True)
        finally:
            self.patches[4].start()
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn('--fresh-kernel', completed.stdout)
        self.assertEqual(score.read_text(), 'previous score')


if __name__ == '__main__':
    unittest.main()
