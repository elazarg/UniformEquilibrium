#!/usr/bin/env python3
"""Regression tests for the project-wide lexical trust scanner."""

from __future__ import annotations

import pathlib
import tempfile
import unittest
from unittest import mock

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

    def test_prunes_math_workspace_but_discovers_untracked_project_source(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            ignored = root / "math" / "fable" / "Ignored.lean"
            ignored.parent.mkdir(parents=True)
            ignored.write_text("example : True := by sorry\n", encoding="utf-8")
            project = root / "UniformEquilibrium" / "Untracked.lean"
            project.parent.mkdir(parents=True)
            project.write_text("example : True := by sorry\n", encoding="utf-8")
            nested = root / "UniformEquilibrium" / "math" / "Nested.lean"
            nested.parent.mkdir(parents=True)
            nested.write_text("example : True := by sorry\n", encoding="utf-8")

            with mock.patch.object(check_trust, "ROOT", root):
                files = check_trust.lean_files()

            self.assertEqual(set(files), {project, nested})
            for discovered in (project, nested):
                with self.subTest(discovered=discovered):
                    relative = discovered.relative_to(root)
                    self.assertEqual(
                        check_trust.token_failures(
                            relative, discovered.read_text(encoding="utf-8")
                        ),
                        [f"{relative}:1: forbidden proof placeholder"],
                    )

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

    def test_resource_options_are_scoped_and_ratcheted(self) -> None:
        accepted = """
abbrev common := #[⟨`warningAsError, true⟩]
lean_lib MathUE where
  leanOptions := common
lean_lib UniformEquilibrium where
  leanOptions := common ++ #[⟨`synthInstance.maxSize, .ofNat 1024⟩]
lean_lib Research where
  leanOptions := common
"""
        self.assertEqual(check_trust.resource_option_failures(accepted), [])

        rejected = """
abbrev common := #[
  ⟨`maxRecDepth, .ofNat 4096⟩,
  ⟨`maxSynthPendingDepth, .ofNat 16⟩,
  ⟨`synthInstance.maxSize, .ofNat 2048⟩
]
lean_lib UniformEquilibrium where
  leanOptions := common
lean_lib Research where
  leanOptions := common ++ #[⟨`synthInstance.maxSize, .ofNat 1024⟩]
"""
        failures = check_trust.resource_option_failures(rejected)
        self.assertEqual(len(failures), 4)
        self.assertTrue(any("maxRecDepth=4096" in failure for failure in failures))
        self.assertTrue(
            any("maxSynthPendingDepth=16" in failure for failure in failures)
        )
        self.assertEqual(
            sum("synthInstance.maxSize" in failure for failure in failures),
            2,
        )


if __name__ == "__main__":
    unittest.main()
