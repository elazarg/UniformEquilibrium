import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNonnegativeWeightChamber
import UniformEquilibrium.Quitting.Paths.GroupExclusionFiniteWordSource

/-! # The fixed nonnegative-weight chamber as an actual GE source

Normalizing the SAME table weight gives the capped-simplex certificate.
Two positive coordinates make its cap strictly below one. The expectation
bound delegates to the canonical reward-moment chamber, not a cap realization.
-/

noncomputable section
namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal row chamber, including zero-valued Never, is a special actual
group-exclusion source. Singleton rewards need not individually be nonnegative. -/
theorem exists_actualGroupExclusion_of_nonnegativeWeightChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : ι → ℝ) (first second : ι) (hne : first ≠ second)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second)
    (hsingleton : 0 ≤ quittingWeightedSingletonReward reward weight)
    (hterminal : ∀ terminal : {S : Finset ι // S.Nonempty},
      quittingWeightedTerminalOutcomeReward reward weight (some terminal) ≤
        quittingWeightedSingletonReward reward weight) :
    ∃ beta < 1, HasQuittingActualNonconcentratedGroupExclusion reward beta := by
  let : Nonempty ι := ⟨first⟩
  let total := quittingPlayerWeightTotal weight
  let largest := quittingPlayerWeightMaximum weight
  have hgap := quittingPlayerWeightOffMaximum_pos_of_two_positive
    weight first second hne hweight hfirst hsecond
  change 0 < total - largest at hgap
  have hlargest : 0 ≤ largest :=
    (hweight first).trans (quittingPlayerWeight_le_maximum weight first)
  have htotal : 0 < total := by linarith
  have hlt : largest / total < 1 := (div_lt_one htotal).mpr (by linarith)
  refine ⟨largest / total, hlt, ?_⟩
  intro profile
  refine ⟨fun who => weight who / total, ?_, ?_, ?_, ?_⟩
  · intro who
    exact div_nonneg (hweight who) htotal.le
  · rw [← Finset.sum_div]
    change total / total = 1
    exact div_self htotal.ne'
  · intro who
    exact div_le_div_of_nonneg_right
      (quittingPlayerWeight_le_maximum weight who) htotal.le
  · have hpair : quittingTerminalSemanticPair reward profile ∈
        quittingTerminalSemanticCarrier reward := subset_closure ⟨profile, rfl⟩
    have hupper := (terminalSemantic_weightedPrescribed_le_outcomeMaximum
      (reward := reward) (quittingTerminalSemanticPair reward profile) weight hpair).trans
        (weightedTerminalOutcomeMaximum_le_singleton_of_table
          (reward := reward) weight hsingleton hterminal)
    change (∑ who, weight who * quittingTerminalPayoff reward profile who) ≤
      ∑ who, weight who * reward (quittingSingletonTerminal who) who at hupper
    simp only [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    apply div_nonpos_of_nonpos_of_nonneg _ htotal.le
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_nonpos.mpr hupper

/-- The SAME normalized chamber supplies every literal finite-word GE
source by restriction of actual profiles, without a strategic oracle. -/
theorem exists_finiteWordGroupExclusion_of_nonnegativeWeightChamber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : ι → ℝ) (first second : ι) (hne : first ≠ second)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second)
    (hsingleton : 0 ≤ quittingWeightedSingletonReward reward weight)
    (hterminal : ∀ terminal : {S : Finset ι // S.Nonempty},
      quittingWeightedTerminalOutcomeReward reward weight (some terminal) ≤
        quittingWeightedSingletonReward reward weight) :
    ∃ beta < 1, HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta := by
  obtain ⟨beta, hbeta, hactual⟩ := exists_actualGroupExclusion_of_nonnegativeWeightChamber
    reward weight first second hne hweight hfirst hsecond hsingleton hterminal
  exact ⟨beta, hbeta,
    hasQuittingFiniteWordNonconcentratedGroupExclusion_of_actual reward beta hactual⟩

end GameTheory
