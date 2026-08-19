#!/usr/bin/env python3
"""Unit tests for focused Lean target selection."""

from __future__ import annotations

import unittest
from unittest import mock

from scripts import ci_changed_lean_targets


class TargetTests(unittest.TestCase):
    def test_maps_all_project_library_roots(self) -> None:
        expected = {
            "AxiomAudit.lean": "+AxiomAudit",
            "Experiments/Base/Probe.lean": "+Experiments.Base.Probe",
            "Literature/Paper.lean": "+Literature.Paper",
            "MathUE/Tool.lean": "+MathUE.Tool",
            "Research/Probe.lean": "+Research.Probe",
            "Theorems/Result.lean": "+Theorems.Result",
            "UniformEquilibrium/Game.lean": "+UniformEquilibrium.Game",
        }
        for path, target in expected.items():
            with self.subTest(path=path):
                self.assertEqual(ci_changed_lean_targets.target(path), target)

    def test_rejects_unknown_lean_root(self) -> None:
        self.assertIsNone(ci_changed_lean_targets.target("Scratch/Probe.lean"))


class PlanTests(unittest.TestCase):
    def plan(self, entries: list[tuple[str, tuple[str, ...]]]):
        with mock.patch.object(ci_changed_lean_targets, "changed", return_value=entries):
            return ci_changed_lean_targets.plan("base", "head")

    def test_focuses_added_and_modified_modules(self) -> None:
        self.assertEqual(
            self.plan(
                [
                    ("M", ("UniformEquilibrium/A.lean",)),
                    ("A", ("Experiments/B.lean",)),
                ]
            ),
            ("focused", ("+Experiments.B", "+UniformEquilibrium.A")),
        )

    def test_non_lean_change_needs_no_build(self) -> None:
        self.assertEqual(self.plan([("M", ("README.md",))]), ("none", ()))

    def test_structural_change_requires_full_build(self) -> None:
        for path in ("lean-toolchain", "lakefile.lean", "lakefile.toml", "GameTheory"):
            with self.subTest(path=path):
                self.assertEqual(self.plan([("M", (path,))]), ("full", ()))

    def test_lean_rename_requires_full_build(self) -> None:
        self.assertEqual(
            self.plan([("R100", ("Research/Old.lean", "Research/New.lean"))]),
            ("full", ()),
        )


if __name__ == "__main__":
    unittest.main()
