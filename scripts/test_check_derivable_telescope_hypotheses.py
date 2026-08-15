import contextlib
import io
import pathlib
import tempfile
import unittest

from scripts import check_derivable_telescope_hypotheses


class DerivableTelescopeHypothesisTests(unittest.TestCase):
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

    def test_detects_all_supported_schemas(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem classes [Finite ι] [Fintype ι] : True := by trivial
theorem member (S : Finset ι) (hS : S.Nonempty) (x : ι)
    (hx : x ∈ S) : True := by trivial
theorem numeral (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : a = 1) : True := by trivial
theorem transported (t u : ℝ) (ht0 : 0 ≤ t) (hu0 : 0 ≤ u)
    (h : t = u) : True := by trivial
""",
            )
            findings = check_derivable_telescope_hypotheses.inventory(root)
            self.assertEqual(
                [(item.name, item.category, item.redundant) for item in findings],
                [
                    ("classes", "fintype_supplies_finite", "[Finite ι]"),
                    ("member", "membership_supplies_nonempty", "hS"),
                    ("numeral", "equality_supplies_bound:numeral endpoint", "ha0"),
                    ("numeral", "equality_supplies_bound:numeral endpoint", "ha1"),
                    (
                        "transported",
                        "equality_supplies_bound:equality transport",
                        "hu0",
                    ),
                ],
            )

    def test_accepts_named_instances_and_reversed_numeral_equality(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem named [small : Finite α] [listed : Fintype α] : True := by trivial
theorem reversed (p : ℝ) (hp : 0 < p) (h : 1 = p) : True := by trivial
""",
            )
            findings = check_derivable_telescope_hypotheses.inventory(root)
            self.assertEqual(
                [(item.name, item.redundant) for item in findings],
                [("named", "[Finite α]"), ("reversed", "hp")],
            )

    def test_does_not_cross_declarations_or_nested_propositions(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem finiteOnly [Finite ι] : True := by trivial
theorem fintypeOnly [Fintype ι] : True := by trivial
theorem nested (S : Finset ι) (h : S.Nonempty ∧ ∃ x, x ∈ S) : True := by trivial
theorem oneBound (t u : ℝ) (ht0 : 0 ≤ t) (h : t = u) : True := by trivial
""",
            )
            self.assertEqual(
                check_derivable_telescope_hypotheses.inventory(root),
                [],
            )

    def test_requires_real_order_and_an_explicit_finset(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem overloaded {α : Type} [OfNat α 0] [OfNat α 1]
    [LE α] (a : α) (ha0 : 0 ≤ a) (h : a = 1) : True := by trivial
theorem custom (Collection : Type) (element : α)
    (hmem : element ∈ Collection) (hne : Collection.Nonempty) : True := by trivial
""",
            )
            self.assertEqual(
                check_derivable_telescope_hypotheses.inventory(root),
                [],
            )

    def test_explicit_source_scope_does_not_claim_section_binders(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """variable (a : ℝ) (ha0 : 0 ≤ a) (h : a = 1)
include ha0 h
theorem inherited : True := by trivial
""",
            )
            self.assertEqual(
                check_derivable_telescope_hypotheses.inventory(root),
                [],
            )

    def test_check_mode_enforces_zero_baseline(self) -> None:
        with self._root() as temporary:
            root = pathlib.Path(temporary)
            self._write(
                root,
                """theorem duplicate [Finite ι] [Fintype ι] : True := by trivial
""",
            )
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(
                io.StringIO()
            ):
                failure = check_derivable_telescope_hypotheses.main(
                    ["--root", str(root), "--check"]
                )
                success = check_derivable_telescope_hypotheses.main(
                    ["--root", str(root), "--check", "--max-hypotheses", "1"]
                )
            self.assertEqual((failure, success), (1, 0))


if __name__ == "__main__":
    unittest.main()
