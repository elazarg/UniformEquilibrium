"""Regression checks for frozen Research artifact integrity."""

from __future__ import annotations

import hashlib
import pathlib
import tempfile
import unittest

from scripts.check_research_pending import check, checked_path


class PendingResearchTests(unittest.TestCase):
    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = pathlib.Path(self.directory.name)
        self.name = "Research/Pending/Sources/Example.lean.draft"
        self.path = self.root / self.name
        self.path.parent.mkdir(parents=True)
        self.path.write_text("theorem example : True := trivial\n", encoding="utf-8")
        self.manifest = {
            "status": "uncompiled",
            "artifacts": {
                self.name: {"sha256": hashlib.sha256(self.path.read_bytes()).hexdigest()}
            },
            "plans": [{"name": "example", "changes": [], "records": [self.name]}],
            "legacy_paths": {"/tmp/old-example.lean": self.name},
        }

    def test_valid_snapshot(self) -> None:
        self.assertEqual(check(self.root, self.manifest), [])

    def test_missing_artifact(self) -> None:
        self.path.unlink()
        self.assertIn(f"missing artifact: {self.name}", check(self.root, self.manifest))

    def test_changed_artifact(self) -> None:
        self.path.write_text("changed\n", encoding="utf-8")
        self.assertIn(f"hash mismatch: {self.name}", check(self.root, self.manifest))

    def test_unrecorded_artifact(self) -> None:
        extra = self.path.parent / "Extra.lean.draft"
        extra.write_text("extra\n", encoding="utf-8")
        self.assertTrue(any("unrecorded artifact" in error
                            for error in check(self.root, self.manifest)))

    def test_forbidden_compiled_suffix(self) -> None:
        item = self.manifest["artifacts"].pop(self.name)
        name = self.name.removesuffix(".draft")
        self.path.rename(self.root / name)
        self.manifest["artifacts"][name] = item
        self.assertTrue(any("compiled source inventory" in error
                            for error in check(self.root, self.manifest)))

    def test_unknown_plan_dependency(self) -> None:
        self.manifest["plans"][0]["depends_on"] = ["missing"]
        self.assertTrue(any("unknown plan dependency" in error
                            for error in check(self.root, self.manifest)))

    def test_unknown_source_change(self) -> None:
        self.manifest["artifacts"][self.name]["changes"] = ["missing.patch"]
        self.assertTrue(any("unrecorded source change" in error
                            for error in check(self.root, self.manifest)))

    def test_nonportable_path(self) -> None:
        for name in ("/tmp/example", "../example", "Research\\example"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                checked_path(self.root, name)

    def test_symlink_escape(self) -> None:
        with tempfile.TemporaryDirectory() as outside:
            link = self.root / "outside"
            link.symlink_to(outside, target_is_directory=True)
            with self.assertRaises(ValueError):
                checked_path(self.root, "outside/example")


if __name__ == "__main__":
    unittest.main()
