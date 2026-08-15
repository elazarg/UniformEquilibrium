import contextlib
import io
import pathlib
import tempfile
import unittest

from scripts import check_redundant_order_hypotheses


class RedundantOrderHypothesisTests(unittest.TestCase):
    def _root(self) -> tempfile.TemporaryDirectory[str]:
        temporary = tempfile.TemporaryDirectory()
        root = pathlib.Path(temporary.name)
        (root / "UniformEquilibrium").mkdir()
        return temporary

    def _write(self, root: pathlib.Path, source: str) -> None:
        (root / "UniformEquilibrium" / "Example.lean").write_text(
            source,
            encoding="utf-8",
        )

    def test_detects_lower_and_upper_endpoint_pairs(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem lower (p : ℝ) (hp0 : 0 ≤ p) (hp : 0 < p) : True := by trivial
theorem upper (p : ℝ) (hp1 : p < 1) (hple : p ≤ 1) : True := by trivial
""",
            )
            pairs = check_redundant_order_hypotheses.inventory(root)
            self.assertEqual(
                [(item.name, item.weak_hypothesis) for item in pairs],
                [("lower", "hp0"), ("upper", "hple")],
            )

    def test_reorients_greater_than_spellings(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem reversed (p : ℝ) (hp : p > 0) (hp0 : p ≥ 0) : True := by trivial
""",
            )
            pair = check_redundant_order_hypotheses.inventory(root)[0]
            self.assertEqual((pair.left, pair.right), ("0", "p"))

    def test_does_not_cross_variables_or_declarations(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem different (p q : ℝ) (hp : 0 < p) (hq0 : 0 ≤ q) : True := by trivial
theorem strictOnly (p : ℝ) (hp : 0 < p) : True := by trivial
theorem weakOnly (p : ℝ) (hp0 : 0 ≤ p) : True := by trivial
""",
            )
            self.assertEqual(
                check_redundant_order_hypotheses.inventory(root),
                [],
            )

    def test_ignores_nested_comparisons_comments_and_literals(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """/- theorem fake (p : ℝ) (hp : 0 < p) (hp0 : 0 ≤ p) := True -/
def text : String := "theorem fake (p : ℝ) (hp : 0 < p) (hp0 : 0 ≤ p)"
theorem nested (p : ℝ) (h : (0 < p) ∧ 0 ≤ p) : True := by trivial
""",
            )
            self.assertEqual(
                check_redundant_order_hypotheses.inventory(root),
                [],
            )

    def test_scans_implicit_unicode_and_equation_declarations(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem unicode {δ : ℝ} {hδ : 0 < δ} {hδ0 : 0 ≤ δ} : True := by trivial
def equation {λ : ℝ} (hλ : 0 < λ) (hλ0 : 0 ≤ λ) : Nat → Nat
  | 0 => 0
  | n + 1 => n
""",
            )
            pairs = check_redundant_order_hypotheses.inventory(root)
            self.assertEqual([item.name for item in pairs], ["unicode", "equation"])

    def test_check_mode_enforces_limit(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem first (p : ℝ) (hp : 0 < p) (hp0 : 0 ≤ p) : True := by trivial
theorem second (q : ℝ) (hq : q < 1) (hq1 : q ≤ 1) : True := by trivial
""",
            )
            stderr = io.StringIO()
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(
                stderr
            ):
                failure = check_redundant_order_hypotheses.main(
                    ["--root", str(root), "--check", "--max-hypotheses", "1"]
                )
            self.assertEqual(failure, 1)
            self.assertIn("--max-hypotheses=1", stderr.getvalue())
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(
                io.StringIO()
            ):
                success = check_redundant_order_hypotheses.main(
                    ["--root", str(root), "--check", "--max-hypotheses", "2"]
                )
            self.assertEqual(success, 0)


if __name__ == "__main__":
    unittest.main()
