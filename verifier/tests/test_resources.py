import contextlib
import io
import unittest
from unittest.mock import patch

from verifier.resources import GIB, available_memory_bytes, main, resource_profile


class ResourceTests(unittest.TestCase):
    def test_default_supports_two_cpu_linux_hosts(self):
        value = resource_profile({}, available_cpus=(0, 1), memory_limit_bytes=32 * GIB)
        self.assertEqual(value.cpus, 2)
        self.assertEqual(value.build_jobs, 2)
        self.assertEqual(value.memory_bytes, 24 * GIB)

    def profile(self, env=None, cpus=tuple(range(12)), memory=48 * GIB):
        return resource_profile({} if env is None else env, available_cpus=cpus, memory_limit_bytes=memory)

    def test_default_preserves_conservative_limits(self):
        profile = self.profile()
        self.assertEqual((profile.name, profile.cpus, profile.memory_bytes), ("conservative", 2, 24 * GIB))
        self.assertEqual((profile.build_jobs, profile.lean_threads), (4, 1))

    def test_named_profiles(self):
        for name, cpus, memory in (("conservative", 2, 24), ("balanced", 4, 40), ("large", 8, 80)):
            with self.subTest(name=name):
                profile = self.profile({"SIG_VERIFY_PROFILE": name}, memory=96 * GIB)
                self.assertEqual((profile.cpus, profile.memory_bytes), (cpus, memory * GIB))

    def test_overrides_and_noncontiguous_affinity(self):
        profile = self.profile({"SIG_VERIFY_CPUS": "3", "SIG_VERIFY_MEMORY_GIB": "32",
                                "SIG_VERIFY_BUILD_JOBS": "2", "SIG_VERIFY_LEAN_THREADS": "2"}, cpus=(9, 2, 7, 4))
        self.assertEqual(profile.cpu_affinity, (2, 4, 7))
        self.assertEqual((profile.memory_bytes, profile.build_jobs, profile.lean_threads), (32 * GIB, 2, 2))

    def test_invalid_names(self):
        for name in ("", "Balanced", "unknown", "balanced; id", "balanced\nSIG_VERIFY_CPUS=99"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.profile({"SIG_VERIFY_PROFILE": name})

    def test_invalid_numbers(self):
        for field in ("CPUS", "MEMORY_GIB", "BUILD_JOBS", "LEAN_THREADS"):
            for value in ("", "0", "-1", "+2", "2.0", " 2", "2 ", "2;id", "2\n", "\u0662", "9" * 100):
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    self.profile({f"SIG_VERIFY_{field}": value})

    def test_capacity_bounds(self):
        for env in ({"SIG_VERIFY_CPUS": "13"}, {"SIG_VERIFY_BUILD_JOBS": "13"},
                    {"SIG_VERIFY_LEAN_THREADS": "3"}, {"SIG_VERIFY_MEMORY_GIB": "3"},
                    {"SIG_VERIFY_MEMORY_GIB": "45"}, {"SIG_VERIFY_PROFILE": "large"}):
            with self.subTest(env=env), self.assertRaises(ValueError):
                self.profile(env)
        self.assertEqual(self.profile({"SIG_VERIFY_MEMORY_GIB": "44"}).memory_bytes, 44 * GIB)
        with self.assertRaises(ValueError):
            self.profile(cpus=())
        with self.assertRaises(ValueError):
            self.profile(memory=27 * GIB)

    def test_unknown_environment_is_not_resource_configuration(self):
        self.assertEqual(self.profile({"UNTRUSTED_CPUS": "99", "PATH": "bad"}), self.profile())

    def test_cgroup_restricts_physical_memory(self):
        values = {"/proc/meminfo": "MemTotal: 67108864 kB\n",
                  "/proc/self/cgroup": "0::/user.slice/job\n",
                  "/sys/fs/cgroup/memory.max": "max\n",
                  "/sys/fs/cgroup/user.slice/memory.max": str(48 * GIB),
                  "/sys/fs/cgroup/user.slice/job/memory.max": str(52 * GIB)}
        with patch("verifier.resources.Path.read_text", lambda path: values[str(path)]), \
                patch("verifier.resources.Path.is_file", lambda path: str(path) in values):
            self.assertEqual(available_memory_bytes(), 48 * GIB)

    def test_vm_settings_are_safe_and_allowlisted(self):
        output = io.StringIO()
        with patch.dict("os.environ", {"SIG_VERIFY_PROFILE": "balanced", "UNTRUSTED": "$(id)"}, clear=True), \
                patch("os.sched_getaffinity", return_value=set(range(16)), create=True), \
                patch("verifier.resources.available_memory_bytes", return_value=64 * GIB), \
                patch("sys.argv", ["resources.py", "--vm"]), contextlib.redirect_stdout(output):
            main()
        self.assertEqual(output.getvalue().splitlines(), [
            "SIG_VERIFY_PROFILE=balanced", "SIG_VERIFY_CPUS=4", "SIG_VERIFY_MEMORY_GIB=40",
            "SIG_VERIFY_BUILD_JOBS=4", "SIG_VERIFY_LEAN_THREADS=1",
            "SIG_VERIFY_VM_CPUS=12", "SIG_VERIFY_VM_MEMORY_GIB=48"])

    def test_vm_rejects_overcommit_and_injection(self):
        for env in ({"SIG_VERIFY_VM_CPUS": "17"}, {"SIG_VERIFY_VM_MEMORY_GIB": "57"},
                    {"SIG_VERIFY_VM_MEMORY_GIB": "27"}, {"SIG_VERIFY_VM_CPUS": "12; id"},
                    {"SIG_VERIFY_VM_MEMORY_GIB": "48$(id)"},
                    {"SIG_VERIFY_PROFILE": "balanced", "SIG_VERIFY_VM_CPUS": "3"}):
            with self.subTest(env=env), patch.dict("os.environ", env, clear=True), \
                    patch("os.sched_getaffinity", return_value=set(range(16)), create=True), \
                    patch("verifier.resources.available_memory_bytes", return_value=64 * GIB), \
                    patch("sys.argv", ["resources.py", "--vm"]), contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit) as error:
                main()
            self.assertEqual(error.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
