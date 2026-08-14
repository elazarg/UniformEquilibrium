#!/usr/bin/env python3
"""Safety and dry-run tests for the historical source synchronizer."""

from __future__ import annotations

import json
import pathlib
import subprocess
import tempfile
import unittest

from scripts import sync_from_source


class SynchronizerSafetyTests(unittest.TestCase):
    def test_rejects_live_root_broad_and_overlapping_targets(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source = root / "source"
            dependency = root / "dependency"
            source.mkdir()
            dependency.mkdir()
            live = root / "live"
            live.mkdir()

            with self.assertRaisesRegex(RuntimeError, "live repository target"):
                sync_from_source.validate_paths(
                    source, dependency, live, live_root=live
                )
            with self.assertRaisesRegex(RuntimeError, "filesystem root"):
                sync_from_source.validate_paths(
                    source, dependency, pathlib.Path("/"), live_root=live
                )
            with self.assertRaisesRegex(RuntimeError, "overlapping"):
                sync_from_source.validate_paths(
                    source, dependency, source / "staging", live_root=live
                )
            with self.assertRaisesRegex(RuntimeError, "live repository target"):
                sync_from_source.validate_paths(
                    source, dependency, live / "staging", live_root=live
                )
            symlink = root / "symlink"
            symlink.symlink_to(root / "elsewhere", target_is_directory=True)
            with self.assertRaisesRegex(RuntimeError, "symlink target"):
                sync_from_source.validate_paths(
                    source, dependency, symlink, live_root=live
                )
            target = root / "safe"
            target.mkdir()
            outside = root / "outside"
            outside.mkdir()
            (target / "UniformEquilibrium").symlink_to(
                outside, target_is_directory=True
            )
            with self.assertRaisesRegex(RuntimeError, "symlink"):
                sync_from_source._safe_destination(
                    target, "UniformEquilibrium/Example.lean"
                )

    def test_dry_run_manifest_is_complete_and_does_not_mutate_target(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            source = root / "source"
            dependency = root / "dependency"
            overlay = root / "overlay"
            target = root / "staging"
            live = root / "live"
            for directory in (source, dependency, overlay, target, live):
                directory.mkdir()

            self._write(
                source,
                "UniformEquilibrium.lean",
                "import UniformEquilibrium.Example\n",
            )
            self._write(
                source,
                "UniformEquilibrium/Example.lean",
                "import Math.Foo\n",
            )
            self._write(source, "Math/Foo.lean", "def foo := 1\n")
            self._write(
                source,
                "GameTheory/Concepts/Correlation/PrivateRecommendationTargetSeparator.lean",
                "def separator := True\n",
            )
            self._git_commit(source)
            self._write(dependency, "GameTheory/Basic.lean", "def basic := 1\n")
            self._write(
                overlay,
                "UniformEquilibrium/Conjecture/UniformExistenceConjecture.lean",
                "def conjecture := True\n",
            )
            self._write(
                overlay,
                "UniformEquilibrium/Quitting/Conjecture/Basic.lean",
                "def quittingConjecture := True\n",
            )
            stale_ue = target / "UniformEquilibrium/Old.lean"
            stale_math = target / "MathUE/Old.lean"
            self._write(target, "UniformEquilibrium/Old.lean", "old\n")
            self._write(target, "MathUE/Old.lean", "old\n")

            plan = sync_from_source.build_plan(
                source,
                self._head(source),
                dependency,
                target,
                overlay,
                live_root=live,
            )
            second_plan = sync_from_source.build_plan(
                source,
                self._head(source),
                dependency,
                target,
                overlay,
                live_root=live,
            )
            self.assertEqual(plan.manifest(), second_plan.manifest())
            manifest = plan.manifest()
            encoded = json.dumps(manifest, indent=2, sort_keys=True)
            self.assertIn('"action": "delete"', encoded)
            self.assertIn('"path": "UniformEquilibrium/Old.lean"', encoded)
            self.assertIn('"path": "MathUE/Old.lean"', encoded)
            self.assertIn('"action": "copy"', encoded)
            self.assertEqual(plan.unresolved, ())
            self.assertEqual(
                sum(
                    operation.path == "UniformEquilibrium.lean"
                    for operation in plan.operations
                    if operation.action == "copy"
                ),
                1,
            )
            self.assertEqual(stale_ue.read_text(encoding="utf-8"), "old\n")
            self.assertEqual(stale_math.read_text(encoding="utf-8"), "old\n")
            self.assertFalse((target / "MathUE/Foo.lean").exists())

            before = {
                path.relative_to(target).as_posix()
                for path in target.rglob("*.lean")
            }
            deletes = {
                operation.path
                for operation in plan.operations
                if operation.action == "delete"
            }
            copies = {
                operation.path
                for operation in plan.operations
                if operation.action == "copy"
            }
            sync_from_source.apply_plan(plan)
            after = {
                path.relative_to(target).as_posix()
                for path in target.rglob("*.lean")
            }
            self.assertEqual(after, (before - deletes) | copies)
            self.assertEqual(
                len(plan.operations), len(deletes) + len(copies)
            )

            snapshot = sync_from_source.GitSnapshot(source, self._head(source))
            with self.assertRaisesRegex(RuntimeError, "missing source object"):
                snapshot.read("missing.lean")
            snapshot.close()
            snapshot.close()
            self.assertIsNotNone(snapshot.process.poll())

    @staticmethod
    def _write(root: pathlib.Path, relative: str, contents: str) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents, encoding="utf-8")

    @staticmethod
    def _git_commit(root: pathlib.Path) -> None:
        subprocess.run(["git", "-C", str(root), "init", "-q"], check=True)
        subprocess.run(
            ["git", "-C", str(root), "config", "user.email", "test@example.com"],
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(root), "config", "user.name", "Test"], check=True
        )
        subprocess.run(["git", "-C", str(root), "add", "."], check=True)
        subprocess.run(
            ["git", "-C", str(root), "commit", "-qm", "snapshot"], check=True
        )

    @staticmethod
    def _head(root: pathlib.Path) -> str:
        return subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"], text=True
        ).strip()


if __name__ == "__main__":
    unittest.main()
