#!/usr/bin/env python3
"""Regression tests for the exhaustive production axiom-audit generator."""

from __future__ import annotations

import pathlib
import tempfile
import unittest
from unittest import mock

from scripts import generate_axiom_audit


class AxiomAuditGeneratorTests(unittest.TestCase):
    def test_only_production_libraries_are_audit_roots(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            (root / "lakefile.lean").write_text(
                "lean_lib MathUE where\n"
                "lean_lib UniformEquilibrium where\n"
                "lean_lib Literature where\n"
                "lean_lib Research where\n",
                encoding="utf-8",
            )
            audited_directories = {
                root / "MathUE",
                root / "UniformEquilibrium",
            }
            with (
                mock.patch.object(generate_axiom_audit, "ROOT", root),
                mock.patch.object(
                    generate_axiom_audit,
                    "AUDITED_DIRECTORIES",
                    audited_directories,
                ),
            ):
                self.assertEqual(
                    generate_axiom_audit.module_roots(),
                    {"MathUE", "UniformEquilibrium"},
                )


if __name__ == "__main__":
    unittest.main()
