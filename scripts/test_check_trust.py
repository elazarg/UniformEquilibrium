#!/usr/bin/env python3
"""Regression tests for the project-wide lexical trust scanner."""

from __future__ import annotations

import pathlib
import unittest

from scripts import check_trust


class TrustScannerTests(unittest.TestCase):
    def labels(self, source: str) -> list[str]:
        failures = check_trust.token_failures(pathlib.Path("Test.lean"), source)
        return [failure.split("forbidden ", 1)[1] for failure in failures]

    def test_rejects_every_forbidden_construct(self) -> None:
        source = """
axiom badAxiom : Prop
axioms badAxioms : Prop
set_option maxHeartbeats 0 in
theorem unfinished : True := by sorry
theorem unfinishedAgain : True := by admit
theorem computed : True := by native_decide
@[implemented_by replacement] def badImplementation : Nat := 0
unsafe def unsafeDefinition : Nat := 0
partial def partialDefinition : Nat := partialDefinition
"""
        labels = self.labels(source)
        self.assertEqual(labels.count("axiom declaration"), 2)
        self.assertIn("set_option command", labels)
        self.assertEqual(labels.count("proof placeholder"), 2)
        self.assertIn("axiom-backed native decision proof", labels)
        self.assertIn("implemented_by escape hatch", labels)
        self.assertIn("unsafe declaration or command", labels)
        self.assertIn("partial definition", labels)

    def test_ignores_comments_strings_and_identifier_substrings(self) -> None:
        source = '''
/- sorry admit axiom foo : Prop set_option linter.foo false -/
def explanation := "sorry admit native_decide implemented_by unsafe partial def"
def sorryAxName := 0
'''
        self.assertEqual(self.labels(source), [])


if __name__ == "__main__":
    unittest.main()
