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

    def test_detects_every_forbidden_token_after_primed_identifier(self) -> None:
        source = """
def value' : Nat := 0
axiom badAxiom : Prop
set_option maxHeartbeats 0 in
theorem unfinished : True := by sorry
theorem unfinishedAgain : True := by admit
theorem computed : True := by native_decide
@[implemented_by replacement] def badImplementation : Nat := 0
unsafe def unsafeDefinition : Nat := 0
partial def partialDefinition : Nat := partialDefinition
"""
        labels = self.labels(source)
        self.assertEqual(labels.count("axiom declaration"), 1)
        self.assertIn("set_option command", labels)
        self.assertEqual(labels.count("proof placeholder"), 2)
        self.assertIn("axiom-backed native decision proof", labels)
        self.assertIn("implemented_by escape hatch", labels)
        self.assertIn("unsafe declaration or command", labels)
        self.assertIn("partial definition", labels)

    def test_ignores_character_literals_including_escapes(self) -> None:
        source = r"""
def plain : Char := 'a'
def quote : Char := '\''
def backslash : Char := '\\'
def newline : Char := '\n'
def unicode : Char := '\u{03BB}'
example : True := by sorry
"""
        self.assertEqual(self.labels(source), ["proof placeholder"])

    def test_ignores_nested_comments_and_strings_with_apostrophes(self) -> None:
        source = r'''
-- sorry admit native_decide implemented_by unsafe partial def
/- outer comment with sorry
   /- nested comment with admit and 'apostrophe' -/
   native_decide implemented_by unsafe partial def
-/
def message := "sorry 'apostrophe' /- not a comment -/"
example : True := by sorry
'''
        self.assertEqual(self.labels(source), ["proof placeholder"])

    def test_multiple_primes_remain_identifier_text(self) -> None:
        source = """
def value''' : Nat := 0
example : True := by sorry
"""
        self.assertEqual(self.labels(source), ["proof placeholder"])

    def test_suffixes_before_primes_remain_identifier_text(self) -> None:
        for identifier in ("probe?'", "probe!'"):
            with self.subTest(identifier=identifier):
                source = f"def {identifier} : Nat := 0\nexample : True := by sorry\n"
                self.assertEqual(self.labels(source), ["proof placeholder"])

    def test_primed_unicode_identifiers_remain_identifier_text(self) -> None:
        for identifier in ("αprobe'", "проба''"):
            with self.subTest(identifier=identifier):
                source = f"def {identifier} : Nat := 0\nexample : True := by sorry\n"
                self.assertEqual(self.labels(source), ["proof placeholder"])


if __name__ == "__main__":
    unittest.main()
