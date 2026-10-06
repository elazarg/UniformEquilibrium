import MathUE.PMFProduct.CoalitionMass
import Mathlib.Tactic.FieldSimp

/-! # Exact coalition factorization by Bernoulli odds

This is algebra on arbitrary real rates. Only the displayed coalition's
denominators must be nonzero; no probability or global interior bounds occur.
-/

namespace Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coalitionMass_eq_continueMass_mul_prod_odds
    (rates : ι → ℝ) (coalition : Finset ι)
    (hdenominator : ∀ player ∈ coalition, 1 - rates player ≠ 0) :
    coalitionMass rates coalition =
      continueMass rates * ∏ player ∈ coalition, rates player / (1 - rates player) := by
  unfold coalitionMass continueMass
  rw [Finset.prod_div_distrib,
    ← Finset.prod_mul_prod_compl coalition (fun player => 1 - rates player)]
  have hnonzero : (∏ player ∈ coalition, (1 - rates player)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hdenominator
  field_simp

end Math.PMFProduct
