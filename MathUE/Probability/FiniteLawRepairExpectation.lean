import MathUE.Probability.FiniteLawRepair
import MathUE.ProbabilityMassFunction.Simplex
import MathUE.ProbabilityMassFunction.TotalVariation

/-!
# Expectations after finite-law support repair

The existing support repair preserves total mass at exact L1 cost twice the
bad mass. Converting that repaired law back to an actual PMF and using the
existing total-variation expectation bound controls the difference from any
observable constant on the chosen good set. No new repair or total-variation
construction is introduced here.
-/

noncomputable section

open scoped BigOperators

namespace Math.Probability.FiniteLawRepair

open _root_.Math.ProbabilityMassFunction GameTheory.Math.Probability

open Classical in
/-- An observable constant on a nonempty good set is within twice its absolute
bound times the actual bad probability mass of its anchored value. -/
theorem abs_expect_sub_anchor_le_two_mul_badMass {Outcome : Type} [Fintype Outcome]
    (law : PMF Outcome) (good : Finset Outcome) (anchor : Outcome)
    (hanchor : anchor ∈ good) (observable : Outcome → ℝ) (bound : ℝ)
    (hbound : ∀ outcome, |observable outcome| ≤ bound)
    (hgood : ∀ outcome ∈ good, observable outcome = observable anchor) :
    |expect law observable - observable anchor| ≤
      (2 * bound) * badMass (toVector law) good := by
  classical
  have hweights := mem_simplexWeights.mp (toVector_mem_stdSimplex law)
  obtain ⟨repaired, hnonneg, hsupported, hsum, hcost⟩ :=
    exists_supported_repair (toVector law) good hanchor hweights.1
  have hrepaired : repaired ∈ simplexWeights Outcome :=
    mem_simplexWeights.mpr ⟨hnonneg, hsum.trans hweights.2⟩
  let repairedLaw := ofVector repaired hrepaired
  have hvalue : expect repairedLaw observable = observable anchor := by
    rw [expect_eq_sum]
    simp only [repairedLaw, ofVector_toReal]
    calc
      (∑ outcome, repaired outcome * observable outcome) =
          ∑ outcome, repaired outcome * observable anchor := by
        apply Finset.sum_congr rfl
        intro outcome _
        by_cases hmem : outcome ∈ good
        · rw [hgood outcome hmem]
        · rw [hsupported outcome hmem, zero_mul, zero_mul]
      _ = (∑ outcome, repaired outcome) * observable anchor :=
        (Finset.sum_mul Finset.univ repaired (observable anchor)).symm
      _ = observable anchor := by rw [hsum, hweights.2, one_mul]
  have hvariation : pmfTV repairedLaw law = badMass (toVector law) good := by
    change pmfPositiveVariation repairedLaw law = _
    rw [pmfPositiveVariation_eq_half_sum_abs]
    simp only [repairedLaw, ofVector_toReal]
    change (1 / 2 : ℝ) * (∑ outcome, |repaired outcome - toVector law outcome|) = _
    rw [hcost]
    ring
  have hestimate := abs_expect_sub_le_two_mul_pmfTV repairedLaw law observable hbound
  rw [hvalue, hvariation] at hestimate
  simpa only [abs_sub_comm] using hestimate

end Math.Probability.FiniteLawRepair
