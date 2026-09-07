import MathUE.Logic.SignFormulaMap
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Real.Basic

/-! Semialgebraic sets as finite Boolean combinations of real polynomial sign sets. -/

namespace MathUE

/-- Boolean sign formulas over actual real-coefficient multivariate polynomials. -/
abbrev RealPolynomialSignFormula (n : ℕ) :=
  Math.PolynomialSignCell.SignFormula (MvPolynomial (Fin n) ℝ)

/-- Real truth semantics for a real-polynomial sign formula. -/
def RealPolynomialSignFormula.HoldsAt {n : ℕ} (formula : RealPolynomialSignFormula n)
    (environment : Fin n → ℝ) : Prop :=
  formula.Holds (fun p => SignType.sign (MvPolynomial.eval environment p))

/-- A semialgebraic set is a finite Boolean combination of real polynomial sign sets. -/
def IsSemialgebraic {n : ℕ} (set : Set (Fin n → ℝ)) : Prop :=
  ∃ formula : RealPolynomialSignFormula n, ∀ environment,
    environment ∈ set ↔ formula.HoldsAt environment

namespace IsSemialgebraic

theorem polynomial_sign {n : ℕ} (polynomial : MvPolynomial (Fin n) ℝ) (sign : SignType) :
    IsSemialgebraic {environment | SignType.sign (MvPolynomial.eval environment polynomial) =
      sign} :=
  ⟨.atom polynomial sign, fun _ => Iff.rfl⟩

theorem polynomial_zero {n : ℕ} (polynomial : MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic {environment | MvPolynomial.eval environment polynomial = 0} := by
  simpa only [sign_eq_zero_iff] using polynomial_sign polynomial 0

theorem polynomial_pos {n : ℕ} (polynomial : MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic {environment | 0 < MvPolynomial.eval environment polynomial} := by
  simpa only [sign_eq_one_iff] using polynomial_sign polynomial 1

theorem polynomial_neg {n : ℕ} (polynomial : MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic {environment | MvPolynomial.eval environment polynomial < 0} := by
  simpa only [sign_eq_neg_one_iff] using polynomial_sign polynomial (-1)

theorem empty {n : ℕ} : IsSemialgebraic (∅ : Set (Fin n → ℝ)) :=
  ⟨.bot, fun _ => Iff.rfl⟩

theorem univ {n : ℕ} : IsSemialgebraic (Set.univ : Set (Fin n → ℝ)) :=
  ⟨.top, fun _ => Iff.rfl⟩

theorem inter {n : ℕ} {left right : Set (Fin n → ℝ)}
    (hl : IsSemialgebraic left) (hr : IsSemialgebraic right) :
    IsSemialgebraic (left ∩ right) := by
  obtain ⟨leftFormula, hl⟩ := hl
  obtain ⟨rightFormula, hr⟩ := hr
  exact ⟨.and leftFormula rightFormula,
    fun environment => and_congr (hl environment) (hr environment)⟩

theorem union {n : ℕ} {left right : Set (Fin n → ℝ)}
    (hl : IsSemialgebraic left) (hr : IsSemialgebraic right) :
    IsSemialgebraic (left ∪ right) := by
  obtain ⟨leftFormula, hl⟩ := hl
  obtain ⟨rightFormula, hr⟩ := hr
  exact ⟨.or leftFormula rightFormula,
    fun environment => or_congr (hl environment) (hr environment)⟩

theorem compl {n : ℕ} {set : Set (Fin n → ℝ)} (h : IsSemialgebraic set) :
    IsSemialgebraic setᶜ := by
  obtain ⟨formula, hformula⟩ := h
  exact ⟨.not formula, fun environment => not_congr (hformula environment)⟩

theorem polynomial_nonneg {n : ℕ} (polynomial : MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic {environment | 0 ≤ MvPolynomial.eval environment polynomial} := by
  simpa only [Set.compl_setOf, not_lt] using (polynomial_neg polynomial).compl

theorem polynomial_nonpos {n : ℕ} (polynomial : MvPolynomial (Fin n) ℝ) :
    IsSemialgebraic {environment | MvPolynomial.eval environment polynomial ≤ 0} := by
  simpa only [Set.compl_setOf, not_lt] using (polynomial_pos polynomial).compl

/-- Pulling back along any finite coordinate map preserves semialgebraicity. -/
theorem preimage_coordinates {n m : ℕ} {set : Set (Fin n → ℝ)}
    (h : IsSemialgebraic set) (indexMap : Fin n → Fin m) :
    IsSemialgebraic {environment : Fin m → ℝ | environment ∘ indexMap ∈ set} := by
  obtain ⟨formula, hformula⟩ := h
  refine ⟨formula.mapAtoms (MvPolynomial.rename indexMap), ?_⟩
  intro environment
  rw [RealPolynomialSignFormula.HoldsAt,
    Math.PolynomialSignCell.SignFormula.holds_mapAtoms]
  have heq : (fun p => SignType.sign (MvPolynomial.eval environment p)) ∘
      MvPolynomial.rename indexMap =
        fun p => SignType.sign (MvPolynomial.eval (environment ∘ indexMap) p) := by
    funext p
    exact congrArg SignType.sign (MvPolynomial.eval_rename indexMap environment p)
  rw [heq]
  exact hformula (environment ∘ indexMap)

end IsSemialgebraic

end MathUE
