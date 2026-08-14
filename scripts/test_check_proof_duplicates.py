import pathlib
import tempfile
import unittest

from scripts import check_proof_duplicates


LONG_PROOF = """by
  intro a b c d
  have h₁ : a = a := rfl
  have h₂ : b = b := rfl
  have h₃ : c = c := rfl
  have h₄ : d = d := rfl
  exact And.intro h₁ (And.intro h₂ (And.intro h₃ h₄))
  -- Padding makes this a maintenance-sized body, not a tiny proof idiom.
  exact And.intro h₁ (And.intro h₂ (And.intro h₃ h₄))
"""


class ProofDuplicateTests(unittest.TestCase):
    def _root(self) -> tempfile.TemporaryDirectory[str]:
        temporary = tempfile.TemporaryDirectory()
        root = pathlib.Path(temporary.name)
        (root / "MathUE").mkdir()
        (root / "UniformEquilibrium").mkdir()
        (root / "Research").mkdir()
        return temporary

    def test_long_cross_lane_body_is_rejected(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "MathUE" / "Owner.lean").write_text(
                "theorem owner (a b c d : Prop) : True := " + LONG_PROOF,
                encoding="utf-8",
            )
            (root / "Research" / "Copy.lean").write_text(
                "theorem renamed (a b c d : Prop) : True := " + LONG_PROOF,
                encoding="utf-8",
            )
            failures = check_proof_duplicates.duplicate_failures(root, 100)
            self.assertEqual(len(failures), 1)
            self.assertIn("Research theorem renamed copies", failures[0])

    def test_short_body_is_not_a_maintenance_duplicate(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            for lane in ("MathUE", "Research"):
                (root / lane / "Tiny.lean").write_text(
                    "theorem tiny : True := by trivial\n", encoding="utf-8"
                )
            self.assertEqual(check_proof_duplicates.duplicate_failures(root), [])

    def test_same_lane_body_is_not_cross_lane_drift(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            for name in ("First", "Second"):
                (root / "Research" / f"{name}.lean").write_text(
                    f"theorem {name.lower()} (a b c d : Prop) : True := "
                    + LONG_PROOF,
                    encoding="utf-8",
                )
            self.assertEqual(
                check_proof_duplicates.duplicate_failures(root, 100), []
            )

    def test_default_argument_is_not_the_body_assignment(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            source = (
                "def value (n : Nat := 1) : Nat := by\n"
                "  exact n + n + n + n + n + n + n + n + n + n\n"
            )
            path = root / "MathUE" / "Default.lean"
            path.write_text(source, encoding="utf-8")
            declarations = check_proof_duplicates.declaration_bodies(path)
            self.assertEqual(len(declarations), 1)
            self.assertTrue(declarations[0].normalized_body.startswith("by exact n"))

    def test_result_let_is_not_the_body_assignment(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            source = (
                "theorem resultLet :\n"
                "    let n := 1\n"
                "    let h : n = n := by rfl\n"
                "    n = n := by\n"
                "  rfl\n"
            )
            path = root / "MathUE" / "ResultLet.lean"
            path.write_text(source, encoding="utf-8")
            declarations = check_proof_duplicates.declaration_bodies(path)
            self.assertEqual(len(declarations), 1)
            self.assertEqual(declarations[0].normalized_body, "by rfl")

    def test_equation_style_body_is_rejected(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            body = (
                "\n  | 0 => 0\n"
                "  | n + 1 => n + n + n + n + n + n + n + n + n + n\n"
            )
            (root / "MathUE" / "Owner.lean").write_text(
                "def recurse : Nat → Nat" + body,
                encoding="utf-8",
            )
            (root / "Research" / "Copy.lean").write_text(
                "def recurse : Nat → Nat" + body,
                encoding="utf-8",
            )
            failures = check_proof_duplicates.duplicate_failures(root, 50)
            self.assertEqual(len(failures), 1)
            self.assertIn("Research def recurse copies", failures[0])

    def test_whitespace_does_not_merge_distinct_token_streams(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "MathUE" / "Owner.lean").write_text(
                "def owner (foo : Nat → Nat) (bar : Nat) : Nat := foo bar\n",
                encoding="utf-8",
            )
            (root / "Research" / "Copy.lean").write_text(
                "def copy (foobar : Nat) : Nat := foobar\n",
                encoding="utf-8",
            )
            self.assertEqual(check_proof_duplicates.duplicate_failures(root, 1), [])

    def test_literal_contents_remain_significant(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "MathUE" / "Owner.lean").write_text(
                'def owner : String := "↦"\n',
                encoding="utf-8",
            )
            (root / "Research" / "Copy.lean").write_text(
                'def copy : String := "=>"\n',
                encoding="utf-8",
            )
            self.assertEqual(check_proof_duplicates.duplicate_failures(root, 1), [])

    def test_whitespace_inside_string_literals_remains_significant(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "MathUE" / "Owner.lean").write_text(
                'def owner : String := "two  spaces"\n',
                encoding="utf-8",
            )
            (root / "Research" / "Copy.lean").write_text(
                'def copy : String := "two spaces"\n',
                encoding="utf-8",
            )
            self.assertEqual(check_proof_duplicates.duplicate_failures(root, 1), [])

    def test_comments_are_ignored_and_lambda_arrows_are_normalized(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "MathUE" / "Owner.lean").write_text(
                "def owner : Nat → Nat := fun n => /- canonical -/ n + n + n\n",
                encoding="utf-8",
            )
            (root / "Research" / "Copy.lean").write_text(
                "def copy : Nat → Nat := fun n ↦ -- Research\n  n + n + n\n",
                encoding="utf-8",
            )
            self.assertEqual(
                len(check_proof_duplicates.duplicate_failures(root, 1)), 1
            )

    def test_unicode_names_and_universe_command_boundary(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "MathUE" / "Owner.lean").write_text(
                "def Φ : Nat := 1 + 2 + 3 + 4\nuniverse u\n",
                encoding="utf-8",
            )
            (root / "Research" / "Copy.lean").write_text(
                "def τ : Nat := 1 + 2 + 3 + 4\nuniverse v\n",
                encoding="utf-8",
            )
            failures = check_proof_duplicates.duplicate_failures(root, 1)
            self.assertEqual(len(failures), 1)
            self.assertIn("Research def τ copies", failures[0])

    def test_attribute_on_preceding_line_does_not_hide_declaration(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            for lane in ("MathUE", "Research"):
                (root / lane / "Attributed.lean").write_text(
                    "@[simp]\ntheorem attributed : True := " + LONG_PROOF,
                    encoding="utf-8",
                )
            failures = check_proof_duplicates.duplicate_failures(root, 100)
            self.assertEqual(len(failures), 1)
            self.assertIn("Attributed.lean:2", failures[0])


if __name__ == "__main__":
    unittest.main()
