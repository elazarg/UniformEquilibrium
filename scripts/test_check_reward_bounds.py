import contextlib
import io
import json
import pathlib
import tempfile
import unittest

from scripts import check_reward_bounds


class RewardBoundTests(unittest.TestCase):
    def _root(self) -> tempfile.TemporaryDirectory[str]:
        temporary = tempfile.TemporaryDirectory()
        root = pathlib.Path(temporary.name)
        (root / "UniformEquilibrium").mkdir()
        return temporary

    def test_corrected_classifier_sees_later_binders(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Example.lean").write_text(
                """namespace Example
theorem Regime.exists_field_style (reward : Nat → Nat) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal : Nat, ∀ player : Nat, |reward terminal| ≤ M)
    (hvalue : |reward 0| ≤ M) : True := by trivial

theorem removable {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S, |reward S| ≤ M) : True := by trivial
end Example
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(len(declarations), 2)
            retained = next(
                d for d in declarations if d.name == "Regime.exists_field_style"
            )
            removable = next(d for d in declarations if d.name == "removable")
            self.assertEqual(retained.report_style_classification, "removable")
            self.assertEqual(retained.corrected_classification, "later-use")
            self.assertEqual(removable.corrected_classification, "removable")

    def test_nested_comments_strings_and_chars_do_not_create_candidates(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Noise.lean").write_text(
                """/- fake theorem {M : ℝ} (hM : 0 ≤ M)
   (hreward : ∀ S, |reward S| ≤ M) : True := by trivial
   /- nested fake {B : ℝ} -/
-/
def text : String := "theorem fake {C : ℝ} (hC : 0 ≤ C)"
def quote : Char := '\\''
theorem real {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S, |reward S| ≤ B) : True := by trivial
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual([declaration.name for declaration in declarations], ["real"])

    def test_term_and_equation_mode_declarations_are_scanned(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Modes.lean").write_text(
                """def term {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S, |reward S| ≤ M) : Nat := 0

def equation {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S, |reward S| ≤ M) : Nat → Nat
  | 0 => 0
  | n + 1 => n
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(
                [declaration.name for declaration in declarations],
                ["term", "equation"],
            )

    def test_explicit_and_grouped_bound_binders_are_ordered(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Binders.lean").write_text(
                """theorem explicit (M : ℝ)
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) : True := by trivial
theorem grouped {boundary M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) : True := by trivial
theorem unicodeGrouped {ε M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) : True := by trivial
theorem unicodeReal {δ M : Real}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) : True := by trivial
theorem unicodeLater {δ M : Real}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M)
    (hvalue : |value 0| ≤ M) : True := by trivial
theorem afterTypeclass [inst : SomeClass α] {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) : True := by trivial
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(
                [declaration.name for declaration in declarations],
                ["explicit", "grouped", "unicodeGrouped", "unicodeReal",
                    "unicodeLater", "afterTypeclass"],
            )
            self.assertEqual(
                [declaration.bound_variable for declaration in declarations],
                ["M", "M", "M", "M", "M", "M"],
            )
            self.assertEqual(
                declarations[-2].corrected_classification,
                "later-use",
            )

    def test_nested_quantified_triple_is_not_a_telescope_candidate(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Nested.lean").write_text(
                """theorem nested
    (h : ∀ (M : ℝ) (hM : 0 ≤ M)
      (hreward : ∀ S, |reward S| ≤ M), True) : True := by trivial
""",
                encoding="utf-8",
            )
            self.assertEqual(check_reward_bounds.inventory(root), [])

    def test_implicit_and_strict_implicit_hypothesis_binders(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Implicit.lean").write_text(
                """theorem implicit {boundary M : ℝ}
    {hM : 0 ≤ M} {hreward : ∀ S, |reward S| ≤ M} : True := by trivial
theorem strictImplicit ⦃boundary M : ℝ⦄
    ⦃hM : 0 ≤ M⦄ ⦃hreward : ∀ S, |reward S| ≤ M⦄ : True := by trivial
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(
                [declaration.name for declaration in declarations],
                ["implicit", "strictImplicit"],
            )

    def test_identifier_apostrophes_and_unicode_suffixes_are_exact(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Identifiers.lean").write_text(
                """theorem apostrophe' {M : ℝ}
    (hM' : 0 ≤ M) (hreward' : ∀ S, |reward S| ≤ M) : True := by trivial
theorem apostropheSuffix {M : ℝ}
    (hM : 0 ≤ M') (hreward : ∀ S, |reward' S| ≤ M') : True := by trivial
theorem unicodeSuffix {M : ℝ}
    (hM : 0 ≤ M₁) (hreward : ∀ S, |reward₁ S| ≤ M₁) : True := by trivial
theorem laterApostrophe {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M)
    (hvalue : value ≤ M') : True := by trivial
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(
                [declaration.name for declaration in declarations],
                ["apostrophe'", "laterApostrophe"],
            )
            self.assertEqual(
                declarations[-1].corrected_classification,
                "removable",
            )

    def test_check_mode_enforces_configurable_removable_limit(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Removable.lean").write_text(
                """theorem first {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) : True := by trivial
theorem second {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) : True := by trivial
""",
                encoding="utf-8",
            )
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                default_failure = check_reward_bounds.main(
                    ["--root", str(root), "--check"]
                )
            self.assertEqual(default_failure, 1)
            self.assertIn("--max-removable=0", stderr.getvalue())
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                failure = check_reward_bounds.main(
                    ["--root", str(root), "--check", "--max-removable", "1"]
                )
            self.assertEqual(failure, 1)
            self.assertIn("--max-removable=1", stderr.getvalue())
            self.assertIn("first", stderr.getvalue())
            self.assertIn("second", stderr.getvalue())
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                success = check_reward_bounds.main(
                    ["--root", str(root), "--check", "--max-removable", "2"]
                )
            self.assertEqual(success, 0)
            self.assertEqual(stderr.getvalue(), "")

    def test_check_mode_enforces_nonnegative_hypothesis_limit(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Nonnegative.lean").write_text(
                """theorem first {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M)
    (hvalue : |value| ≤ M) : True := by trivial
theorem second {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M)
    (hvalue : |value| ≤ M) : True := by trivial
""",
                encoding="utf-8",
            )
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                failure = check_reward_bounds.main(
                    ["--root", str(root), "--check", "--max-nonnegative", "1"]
                )
            self.assertEqual(failure, 1)
            self.assertIn("--max-nonnegative=1", stderr.getvalue())
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                success = check_reward_bounds.main(
                    ["--root", str(root), "--check", "--max-nonnegative", "2"]
                )
            self.assertEqual(success, 0)
            self.assertEqual(stderr.getvalue(), "")

    def test_interleaved_nontriple_binder_is_retained(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Interleaved.lean").write_text(
                """theorem interleaved {M : ℝ}
    (hreward : ∀ S, |reward S| ≤ M)
    (huses : M = M)
    (hM : 0 ≤ M) : True := by trivial
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(len(declarations), 1)
            self.assertEqual(
                declarations[0].corrected_classification,
                "later-use",
            )

    def test_result_classifier_keeps_colons_inside_binder_notation(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "ResultBinder.lean").write_text(
                """theorem quantitative {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) :
    (∑' offset : ℕ, M / (offset + 1)) = 0 := by trivial
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(len(declarations), 1)
            self.assertEqual(
                declarations[0].report_style_classification,
                "later-use",
            )
            self.assertEqual(
                declarations[0].corrected_classification,
                "later-use",
            )

    def test_result_classifier_keeps_result_level_lets(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "ResultLet.lean").write_text(
                """theorem quantitative {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) :
    let scale := 8 * M
    let h : scale = scale := by rfl
    scale = scale := by trivial
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(len(declarations), 1)
            self.assertEqual(
                declarations[0].corrected_classification,
                "later-use",
            )

    def test_data_definition_body_is_part_of_corrected_classification(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "Definition.lean").write_text(
                """def quantitative {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) : Nat :=
  if M = 0 then 0 else 1
def removable {M : ℝ}
    (hM : 0 ≤ M) (hreward : ∀ S, |reward S| ≤ M) : Nat := 0
""",
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(
                [declaration.corrected_classification for declaration in declarations],
                ["later-use", "removable"],
            )

    def test_json_is_deterministic_and_contains_exact_inventory(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "UniformEquilibrium" / "One.lean").write_text(
                "theorem one {M : ℝ} (hM : 0 ≤ M) "
                "(hreward : ∀ S, |reward S| ≤ M) : True := by trivial\n",
                encoding="utf-8",
            )
            first = check_reward_bounds.report(root)
            second = check_reward_bounds.report(root)
            self.assertEqual(json.dumps(first, sort_keys=True), json.dumps(second, sort_keys=True))
            self.assertEqual(first["summary"]["candidate_count"], 1)
            self.assertEqual(first["declarations"][0]["path"], "UniformEquilibrium/One.lean")

    def test_inventory_scans_only_explicit_project_library_roots(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            (root / "Research").mkdir()
            (root / "math").mkdir()
            candidate = (
                "theorem candidate {M : ℝ} (hM : 0 ≤ M) "
                "(hreward : ∀ S, |reward S| ≤ M) : True := by trivial\n"
            )
            (root / "Research" / "Untracked.lean").write_text(
                candidate.replace("candidate", "allowedDirectory"),
                encoding="utf-8",
            )
            (root / "AxiomAudit.lean").write_text(
                candidate.replace("candidate", "allowedUmbrella"),
                encoding="utf-8",
            )
            (root / "math" / "Ignored.lean").write_text(
                candidate.replace("candidate", "ignoredMath"),
                encoding="utf-8",
            )
            declarations = check_reward_bounds.inventory(root)
            self.assertEqual(
                [(item.name, item.path) for item in declarations],
                [
                    ("allowedUmbrella", "AxiomAudit.lean"),
                    ("allowedDirectory", "Research/Untracked.lean"),
                ],
            )


if __name__ == "__main__":
    unittest.main()
