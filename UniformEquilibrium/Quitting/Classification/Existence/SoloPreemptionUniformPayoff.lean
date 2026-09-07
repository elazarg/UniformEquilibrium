import UniformEquilibrium.Quitting.Classification.Existence.AcyclicSoloPreemption

/-! # Fixed solo uniform payoff without a strict preemptor -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A nonnegative owner whose solo payoff weakly dominates every outsider's
singleton payoff supplies the standard vanishing-hazard uniform payoff. -/
theorem isUniformEquilibriumPayoff_soloReward_of_nonnegative_noPreemptor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hnoPreemptor : ∀ other, other ≠ owner →
      reward (quittingSingletonTerminal other) other ≤
        reward (quittingSingletonTerminal owner) other) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  letI : Nonempty ι := ⟨owner⟩
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_fixedTarget
  intro ε hε
  let premium := quittingSoloPairPremium reward owner
  let q := min (1 / 2 : ℝ) (ε / (2 * (premium + 1)))
  have hpremium : 0 ≤ premium := quittingSoloPairPremium_nonneg reward owner
  have hdenominator : 0 < 2 * (premium + 1) := by positivity
  have hq0 : 0 < q := by
    dsimp only [q]
    exact lt_min (by norm_num) (div_pos hε hdenominator)
  have hq1 : q ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hqSmall : q ≤ ε / (2 * (premium + 1)) := min_le_right _ _
  have hscaled : q * (premium + 1) ≤ ε / 2 := by
    calc
      q * (premium + 1) ≤
          (ε / (2 * (premium + 1))) * (premium + 1) := by gcongr
      _ = ε / 2 := by field_simp
  have herror : q * premium ≤ ε := by
    calc
      q * premium ≤ q * (premium + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hq0.le
      _ ≤ ε / 2 := hscaled
      _ ≤ ε := by linarith
  let hazard := quittingHazardCoin q hq0.le hq1
  let profile := quittingStationaryProfile reward
    (quittingSoloStationaryRoot owner hazard)
  refine ⟨profile, ?_, ?_⟩
  · exact (isεAsymptoticNash_soloStationary_le_pairPremium
      reward owner hq0 hq1 howner hnoPreemptor).mono herror
  · funext player
    exact quittingTerminalPayoff_soloStationary reward owner player hazard
      (by simpa only [hazard, quittingHazardCoin_true_toReal] using hq0)

end GameTheory
