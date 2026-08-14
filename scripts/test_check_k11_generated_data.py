#!/usr/bin/env python3
"""Regression tests for the K11 migrated-payload integrity checker."""

from __future__ import annotations

import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
CHECKER_PATH = ROOT / "scripts" / "check_k11_generated_data.py"
SPEC = importlib.util.spec_from_file_location("check_k11_generated_data", CHECKER_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load {CHECKER_PATH}")
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class K11GeneratedDataTests(unittest.TestCase):
    def test_repository_matches_manifest(self) -> None:
        self.assertEqual(CHECKER.check_repository(), [])

    def test_preconditioner_shape_change_is_rejected(self) -> None:
        path = (
            ROOT
            / "Research"
            / "Quitting"
            / "BlockPair"
            / "K11"
            / "Preconditioner.lean"
        )
        text = path.read_text(encoding="utf-8")
        changed = text.replace("  -7130412613540890,\n", "", 1)
        with self.assertRaisesRegex(CHECKER.PayloadError, "has 30 entries"):
            CHECKER.parse_preconditioner(changed)

    def test_jacobian_reversed_interval_is_rejected(self) -> None:
        path = (
            ROOT
            / "Research"
            / "Quitting"
            / "BlockPair"
            / "K11"
            / "JacobianCache.lean"
        )
        text = path.read_text(encoding="utf-8")
        changed = text.replace(
            "⟨(-56861261462224415),\n    (56861261462224416)⟩",
            "⟨(56861261462224417),\n    (56861261462224416)⟩",
            1,
        )
        with self.assertRaisesRegex(CHECKER.PayloadError, "is reversed"):
            CHECKER.parse_jacobian(changed)

    def test_payload_digest_ignores_unparsed_comments(self) -> None:
        path = (
            ROOT
            / "Research"
            / "Quitting"
            / "BlockPair"
            / "K11"
            / "JacobianCache.lean"
        )
        text = path.read_text(encoding="utf-8")
        original = CHECKER.logical_digest(CHECKER.parse_jacobian(text))
        changed = CHECKER.logical_digest(CHECKER.parse_jacobian("/- note -/\n" + text))
        self.assertEqual(original, changed)


if __name__ == "__main__":
    unittest.main()
