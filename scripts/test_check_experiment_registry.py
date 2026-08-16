#!/usr/bin/env python3
"""Regression tests for the Base experiment registry check."""

from __future__ import annotations

import pathlib
import tempfile
import unittest

from scripts.check_experiment_registry import registry_issues


class ExperimentRegistryTests(unittest.TestCase):
    def make_registry(
        self,
        root: pathlib.Path,
        modules: list[str],
        sources: dict[str, str],
    ) -> tuple[pathlib.Path, pathlib.Path]:
        base = root / "Base"
        base.mkdir()
        runner = base / "run_all.py"
        runner.write_text(f"EXPERIMENT_MODULES = {modules!r}\n", encoding="utf-8")
        for name, source in sources.items():
            (base / f"{name}.py").write_text(source, encoding="utf-8")
        return base, runner

    def test_exact_registry_passes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base, runner = self.make_registry(
                pathlib.Path(temporary),
                ["alpha", "beta"],
                {"alpha": "def run():\n    return {}\n", "beta": "def run():\n    return {}\n"},
            )
            self.assertEqual(registry_issues(base, runner), [])

    def test_unregistered_source_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base, runner = self.make_registry(
                pathlib.Path(temporary),
                ["alpha"],
                {
                    "alpha": "def run():\n    return {}\n",
                    "stray": "def run():\n    return {}\n",
                },
            )
            self.assertEqual(
                registry_issues(base, runner),
                ["unregistered Base programs: stray"],
            )

    def test_missing_source_and_run_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base, runner = self.make_registry(
                pathlib.Path(temporary),
                ["alpha", "missing"],
                {"alpha": "def helper():\n    return {}\n"},
            )
            self.assertEqual(
                registry_issues(base, runner),
                [
                    "registered modules without source: missing",
                    "alpha: missing top-level run()",
                ],
            )

    def test_duplicate_registration_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base, runner = self.make_registry(
                pathlib.Path(temporary),
                ["alpha", "alpha"],
                {"alpha": "def run():\n    return {}\n"},
            )
            self.assertEqual(
                registry_issues(base, runner),
                ["duplicate registered modules: alpha"],
            )


if __name__ == "__main__":
    unittest.main()
