import concurrent.futures
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from cache import ResultCache, acceptance_key, context_digest, tree_digest


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.source = self.root / "source"
        self.source.mkdir()
        (self.source / "Solution.lean").write_bytes(b"proof")
        self.claim = {"S": 8, "W": 8, "K": 0, "C": 100,
                      "layout": {"message": 0, "secret_key": 32, "public_key": 64,
                                 "cache": 80, "signature": 80, "witness": 88}}
        self.result = {"status": "verified", "score": 800, "claim": self.claim,
                       "source_digest": tree_digest(self.source),
                       "context_digest": "a" * 64, "certificate_digest": "b" * 64,
                       "mode": "certificate"}
        self.key = self.key_for(self.result)
        self.cache = ResultCache(self.root / "accepted")
        self.entry = self.cache.path / (self.key + ".json")

    def tearDown(self):
        self.temp.cleanup()

    @staticmethod
    def key_for(result):
        return acceptance_key(result["context_digest"], result["source_digest"],
                              result["claim"], result["certificate_digest"], result["mode"])

    def test_roundtrip_private_modes_and_stable_fields(self):
        self.cache.put(self.key, {**self.result, "commit": "unrelated", "log": "temporary"})
        self.assertEqual(self.cache.get(self.key), self.result)
        self.assertEqual(self.cache.path.stat().st_mode & 0o777, 0o700)
        self.assertEqual(self.entry.stat().st_mode & 0o777, 0o600)

    def test_tree_deterministic_raw_bytes_and_empty_directories(self):
        digest = tree_digest(self.source)
        other = self.root / "other"
        other.mkdir()
        (other / "Solution.lean").write_bytes(b"proof")
        self.assertEqual(digest, tree_digest(other))
        (other / "empty").mkdir()
        self.assertNotEqual(digest, tree_digest(other))
        (other / "empty").rmdir()
        (other / "Solution.lean").write_bytes(b"proof\x00")
        self.assertNotEqual(digest, tree_digest(other))

    def test_framing_prevents_path_content_boundary_ambiguity(self):
        left, right = self.root / "left", self.root / "right"
        left.mkdir()
        right.mkdir()
        (left / "a").write_bytes(b"bc")
        (right / "ab").write_bytes(b"c")
        self.assertNotEqual(tree_digest(left), tree_digest(right))
        (right / "ab").unlink()
        (right / "a").mkdir()
        (right / "a" / "b").write_bytes(b"c")
        self.assertNotEqual(tree_digest(left), tree_digest(right))

    def test_certificate_exclusion_is_top_level_only(self):
        digest = tree_digest(self.source)
        (self.source / "certificate").mkdir()
        (self.source / "certificate" / "export").write_bytes(b"ignored")
        self.assertEqual(digest, tree_digest(self.source))
        self.assertNotEqual(digest, tree_digest(self.source, excluded_top_level=()))
        (self.source / "module").mkdir()
        (self.source / "module" / "certificate").write_bytes(b"included")
        self.assertNotEqual(digest, tree_digest(self.source))

    def test_tree_rejects_symlink_hardlink_and_special(self):
        alias = self.source / "alias"
        alias.symlink_to("Solution.lean")
        with self.assertRaises((OSError, ValueError)):
            tree_digest(self.source)
        alias.unlink()
        os.link(self.source / "Solution.lean", alias)
        with self.assertRaises(ValueError):
            tree_digest(self.source)
        alias.unlink()
        os.mkfifo(alias)
        with self.assertRaises(ValueError):
            tree_digest(self.source)
        alias.unlink()
        root_alias = self.root / "alias"
        root_alias.symlink_to(self.source, target_is_directory=True)
        with self.assertRaises(OSError):
            tree_digest(root_alias)

    def context_fixture(self):
        trusted = self.root / "trusted"
        for directory in ("SigGolf", "verifier", "scripts", ".git"):
            (trusted / directory).mkdir(parents=True)
        for name in ("RULES.md", "SigGolf.lean", "lean-toolchain", "lakefile.lean",
                     "lake-manifest.json", "scripts/run.py", "scripts/setup.sh",
                     "SigGolf/Statements.lean", "verifier/check.py", "verifier/a.lean",
                     "verifier/config.json", "verifier/Challenge.lean.in", "verifier/setup_tools.sh"):
            (trusted / name).write_bytes(b"original")
        (trusted / ".git" / "HEAD").write_text("fixed-head")
        tool = self.root / "tool"
        tool.write_bytes(b"executable")
        tool.chmod(0o700)
        return trusted, tool

    def test_context_changes_without_git_head_or_path_changes(self):
        trusted, tool = self.context_fixture()
        digest = context_digest(trusted, {"kernel": tool})
        for name in ("RULES.md", "SigGolf/Statements.lean", "verifier/check.py",
                     "verifier/a.lean", "verifier/config.json", "verifier/Challenge.lean.in",
                     "verifier/setup_tools.sh", "scripts/run.py", "lake-manifest.json"):
            path = trusted / name
            path.write_bytes(b"changed")
            self.assertNotEqual(digest, context_digest(trusted, {"kernel": tool}), name)
            path.write_bytes(b"original")
        tool.write_bytes(b"new executable")
        self.assertNotEqual(digest, context_digest(trusted, {"kernel": tool}))
        tool.write_bytes(b"executable")
        (trusted / ".git" / "HEAD").write_text("different-head")
        self.assertEqual(digest, context_digest(trusted, {"kernel": tool}))
        moved = self.root / "moved"
        tool.rename(moved)
        self.assertEqual(digest, context_digest(trusted, {"kernel": moved}))

    def test_context_binds_package_sources_not_builds_or_git(self):
        trusted, tool = self.context_fixture()
        package = trusted / ".lake" / "packages" / "dependency"
        package.mkdir(parents=True)
        source = package / "Proof.lean"
        source.write_bytes(b"original source")
        config = package / "lakefile.toml"
        config.write_bytes(b"original config")
        for name in (".git", ".lake"):
            (package / name).mkdir()
            (package / name / "ignored").write_bytes(b"original")
        digest = context_digest(trusted, {"kernel": tool})
        for path in (source, config):
            path.write_bytes(b"dirty source without commit changes")
            self.assertNotEqual(digest, context_digest(trusted, {"kernel": tool}))
            path.write_bytes(b"original source" if path == source else b"original config")
        for name in (".git", ".lake"):
            (package / name / "ignored").write_bytes(b"changed")
            (package / name / "extra").write_bytes(b"build output")
        self.assertEqual(digest, context_digest(trusted, {"kernel": tool}))
        # Only top-level package metadata/build directories are excluded.
        nested = package / "nested" / ".lake"
        nested.mkdir(parents=True)
        self.assertNotEqual(digest, context_digest(trusted, {"kernel": tool}))
        nested_digest = context_digest(trusted, {"kernel": tool})
        (nested / "bound").write_bytes(b"included")
        self.assertNotEqual(nested_digest, context_digest(trusted, {"kernel": tool}))

    def test_context_rejects_package_symlinks_hardlinks_and_special_files(self):
        trusted, tool = self.context_fixture()
        packages = trusted / ".lake" / "packages"
        packages.mkdir(parents=True)
        package = packages / "dependency"
        package.symlink_to(trusted / "SigGolf", target_is_directory=True)
        with self.assertRaises(ValueError):
            context_digest(trusted, {"kernel": tool})
        package.unlink()
        package.mkdir()
        source = package / "Proof.lean"
        source.write_bytes(b"source")
        alias = package / "alias"
        alias.symlink_to(trusted / "SigGolf.lean")
        with self.assertRaises((ValueError, OSError)):
            context_digest(trusted, {"kernel": tool})
        alias.unlink()
        os.link(source, alias)
        with self.assertRaises(ValueError):
            context_digest(trusted, {"kernel": tool})
        alias.unlink()
        os.mkfifo(alias)
        with self.assertRaises(ValueError):
            context_digest(trusted, {"kernel": tool})
        alias.unlink()
        packages.rename(packages.with_name("real-packages"))
        packages.symlink_to("real-packages", target_is_directory=True)
        with self.assertRaises(OSError):
            context_digest(trusted, {"kernel": tool})

    def test_package_internal_file_links_bind_text_and_target_contents(self):
        trusted, tool = self.context_fixture()
        package = trusted / ".lake" / "packages" / "dependency"
        package.mkdir(parents=True)
        target = package / "AGENTS.md"
        target.write_bytes(b"instructions")
        middle = package / "Documentation.md"
        middle.symlink_to("AGENTS.md")
        link = package / "CLAUDE.md"
        link.symlink_to("Documentation.md")
        digest = context_digest(trusted, {"kernel": tool})
        target.write_bytes(b"changed instructions")
        self.assertNotEqual(digest, context_digest(trusted, {"kernel": tool}))
        target.write_bytes(b"instructions")
        self.assertEqual(digest, context_digest(trusted, {"kernel": tool}))
        link.unlink()
        link.symlink_to("./Documentation.md")
        self.assertNotEqual(digest, context_digest(trusted, {"kernel": tool}))
        # Candidate trees retain the strict policy, even for internal file links.
        with self.assertRaises(ValueError):
            tree_digest(package)

    def test_package_links_reject_broken_cycles_directories_and_excluded_targets(self):
        trusted, tool = self.context_fixture()
        package = trusted / ".lake" / "packages" / "dependency"
        package.mkdir(parents=True)
        (package / "Proof.lean").write_bytes(b"proof")
        for name in (".git", ".lake", "ordinary"):
            (package / name).mkdir()
            (package / name / "target").write_bytes(b"not a permitted link target")
        link = package / "alias"
        for target in ("missing", "alias", ".", ".git/target", ".lake/target",
                       ".git/../Proof.lean", "../dependency/Proof.lean"):
            link.symlink_to(target)
            with self.assertRaises((ValueError, OSError), msg=target):
                context_digest(trusted, {"kernel": tool})
            link.unlink()
        directory_link = package / "directory-link"
        directory_link.symlink_to("ordinary", target_is_directory=True)
        link.symlink_to("directory-link/target")
        with self.assertRaises(ValueError):
            context_digest(trusted, {"kernel": tool})

    def test_key_canonical_and_binds_every_input(self):
        reordered = dict(reversed(list(self.claim.items())))
        self.assertEqual(self.key, acceptance_key("a" * 64, self.result["source_digest"],
                                                  reordered, "b" * 64, "certificate"))
        for field, value in (("context_digest", "c" * 64), ("source_digest", "c" * 64),
                             ("certificate_digest", "c" * 64), ("mode", "legacy")):
            changed = {**self.result, field: value}
            self.assertNotEqual(self.key, self.key_for(changed))
        changed = copy.deepcopy(self.result)
        changed["claim"]["C"] += 1
        self.assertNotEqual(self.key, self.key_for(changed))

    def test_legacy_none_certificate(self):
        result = {**self.result, "certificate_digest": None, "mode": "legacy"}
        key = self.key_for(result)
        self.cache.put(key, result)
        self.assertEqual(self.cache.get(key), result)

    def test_failures_incomplete_wrong_key_and_wrong_score_not_cached(self):
        for field, value in (("status", "rejected"), ("score", 801),
                             ("score", True), ("context_digest", "c" * 64)):
            with self.assertRaises(ValueError):
                self.cache.put(self.key, {**self.result, field: value})
        incomplete = self.result.copy()
        del incomplete["mode"]
        with self.assertRaises(ValueError):
            self.cache.put(self.key, incomplete)
        self.assertIsNone(self.cache.get(self.key))

    def test_corrupt_partial_forged_and_noncanonical_manifest_miss(self):
        self.cache.put(self.key, self.result)
        original = self.entry.read_bytes()
        manifest = json.loads(original)
        cases = [b"", b'{"version":1', original + b"\n", b"[]",
                 original[:-1] + b',"version":1}']
        for field, value in (("version", True), ("version", 99), ("key", "c" * 64)):
            changed = copy.deepcopy(manifest)
            changed[field] = value
            cases.append(json.dumps(changed, sort_keys=True, separators=(",", ":")).encode())
        changed = copy.deepcopy(manifest)
        changed["result"]["source_digest"] = "d" * 64
        cases.append(json.dumps(changed, sort_keys=True, separators=(",", ":")).encode())
        changed = copy.deepcopy(manifest)
        changed["result"]["score"] += 1
        cases.append(json.dumps(changed, sort_keys=True, separators=(",", ":")).encode())
        for raw in cases:
            self.entry.write_bytes(raw)
            self.assertIsNone(self.cache.get(self.key), raw)

    def test_cache_file_symlink_and_hardlink_attacks(self):
        victim = self.root / "victim"
        victim.write_bytes(b"do not touch")
        victim.chmod(0o600)
        self.entry.symlink_to(victim)
        self.assertIsNone(self.cache.get(self.key))
        with self.assertRaises(OSError):
            self.cache.put(self.key, self.result)
        self.assertEqual(victim.read_bytes(), b"do not touch")
        self.entry.unlink()
        self.cache.put(self.key, self.result)
        alias = self.root / "hardlink"
        os.link(self.entry, alias)
        self.assertIsNone(self.cache.get(self.key))
        with self.assertRaises(ValueError):
            self.cache.put(self.key, self.result)

    def test_cache_directory_symlinks_and_permissions(self):
        alias = self.root / "alias"
        alias.symlink_to(self.cache.path, target_is_directory=True)
        with self.assertRaises(OSError):
            ResultCache(alias)
        with self.assertRaises(OSError):
            ResultCache(alias / "nested")
        self.cache.path.chmod(0o755)
        with self.assertRaises(ValueError):
            ResultCache(self.cache.path)
        self.assertIsNone(self.cache.get(self.key))
        self.cache.path.chmod(0o700)
        unsafe = self.root / "unsafe"
        unsafe.mkdir(mode=0o777)
        unsafe.chmod(0o777)
        with self.assertRaises(ValueError):
            ResultCache(unsafe / "accepted")

    def test_unsafe_file_mode_special_file_and_oversized_miss(self):
        self.cache.put(self.key, self.result)
        self.entry.chmod(0o644)
        self.assertIsNone(self.cache.get(self.key))
        self.entry.unlink()
        os.mkfifo(self.entry)
        self.assertIsNone(self.cache.get(self.key))
        self.entry.unlink()
        self.entry.write_bytes(b"x" * (64 * 1024 + 1))
        self.entry.chmod(0o600)
        self.assertIsNone(self.cache.get(self.key))
        self.assertIsNone(self.cache.get("../outside"))

    def test_replaced_cache_directory_is_rechecked(self):
        self.cache.put(self.key, self.result)
        old = self.root / "old"
        self.cache.path.rename(old)
        self.cache.path.symlink_to(old, target_is_directory=True)
        self.assertIsNone(self.cache.get(self.key))
        with self.assertRaises(OSError):
            self.cache.put(self.key, self.result)

    def test_concurrent_atomic_writers(self):
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
            list(pool.map(lambda _: self.cache.put(self.key, self.result), range(16)))
        self.assertEqual(self.cache.get(self.key), self.result)
        self.assertEqual(list(self.cache.path.iterdir()), [self.entry])


if __name__ == "__main__":
    unittest.main()
