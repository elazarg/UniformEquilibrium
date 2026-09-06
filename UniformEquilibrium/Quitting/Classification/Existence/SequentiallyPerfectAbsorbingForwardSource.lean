import UniformEquilibrium.Quitting.Bellman.Finite.FiniteEndpointErrorPunishmentFloor
import UniformEquilibrium.Quitting.Classification.Existence.SequentiallyPerfectAbsorbingNullTailAlternative
import MathUE.SummableChargeSurvival

/-! # Absorption charge and punishment floors of sequentially perfect sources

Literal restarted terminal payoffs satisfy the Bellman recursion. Termination
after every restart forces unbounded finite absorption charge. Under normality,
the finite burn-in theorem gives the approximate punishment floor at every
restarted date. Finite reversal retains the actual roots and terminal payoffs.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability StochasticGame QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Termination after every finite restart forces nonsummable total
one-stage absorption charge. -/
theorem not_summable_quittingRootAbsorptionMass_of_terminatesAfterEveryRestart
    (roots : ℕ → ι → PMF Bool)
    (hterminates : QuittingRootSequenceTerminatesAfterEveryRestart roots) :
    ¬ Summable (fun time ↦ quittingRootAbsorptionMass (roots time)) := by
  intro hsummable
  have htends : Tendsto (fun time ↦ quittingRootAbsorptionMass (roots time))
      atTop (nhds 0) := hsummable.tendsto_atTop_zero
  have heventually : ∀ᶠ time : ℕ in atTop,
      quittingRootAbsorptionMass (roots time) < 1 :=
    htends.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨start, hstart⟩ := (eventually_atTop.1 heventually)
  let charge : ℕ → ℝ := fun offset ↦
    quittingRootAbsorptionMass (roots (start + offset))
  have hcharge0 : ∀ offset, 0 ≤ charge offset := fun offset ↦ by
    exact quittingRootAbsorptionMass_nonneg (roots (start + offset))
  have hcharge1 : ∀ offset, charge offset < 1 := fun offset ↦ by
    exact hstart (start + offset) (Nat.le_add_right start offset)
  have hchargeSummable : Summable charge := by
    have hshift : Summable (fun offset ↦
        quittingRootAbsorptionMass (roots (offset + start))) :=
      (summable_nat_add_iff start).2 hsummable
    simpa only [charge, Nat.add_comm] using hshift
  obtain ⟨lower, hlower, hlowerBound⟩ :=
    Math.exists_pos_le_prod_one_sub_of_summable
      charge hcharge0 hcharge1 hchargeSummable
  have hsurvivalBound : ∀ horizon,
      lower ≤ quittingJointSurvivalWeight roots start horizon := by
    intro horizon
    rw [quittingJointSurvivalWeight_eq_prod]
    simpa only [charge, quittingRootAbsorptionMass, sub_sub_cancel] using
      hlowerBound horizon
  have hlimit : lower ≤ quittingJointSurvivalLimit roots start :=
    ge_of_tendsto' (tendsto_quittingJointSurvivalLimit roots start)
      hsurvivalBound
  rw [hterminates start] at hlimit
  linarith

omit [DecidableEq ι] in
/-- The literal restarted terminal payoff vectors satisfy the exact Bellman
recursion at every chronological row. -/
theorem quittingRootSequenceTailVector_policy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    quittingRootSequenceTailVector reward roots time =
      quittingRootSuccessorPayoff reward
        (quittingRootSequenceTailVector reward roots (time + 1))
        (roots time) := by
  funext who
  exact quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
    reward roots who time

omit [DecidableEq ι] in
/-- A reward bound controls every coordinate of every literal restarted
terminal payoff vector. -/
theorem abs_quittingRootSequenceTailVector_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (time : ℕ) (who : ι) :
    |quittingRootSequenceTailVector reward roots time who| ≤ bound := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg (reward (quittingSingletonTerminal who) who)).trans
      (hreward (quittingSingletonTerminal who) who)
  exact abs_quittingRootSequenceTerminalValue_le
    reward roots who time hbound hreward

/-- If one singleton reward strictly exceeds the row error, literal
row-perfectness rules out positive survival after every restart. -/
theorem quittingRootSequenceTerminatesAfterEveryRestart_of_rowPerfect_of_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {error : ℝ} (who : ι)
    (herrorSingleton : error < reward (quittingSingletonTerminal who) who)
    (hperfect : ∀ time, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (time + 1))
      (roots time) error) :
    QuittingRootSequenceTerminatesAfterEveryRestart roots := by
  intro start
  apply le_antisymm
  · by_contra hnot
    have hpositive : 0 < quittingJointSurvivalLimit roots start :=
      lt_of_not_ge hnot
    have hsingleton := quittingSingletonReward_le_error_of_positiveRestartSurvival
      reward roots error start hpositive hperfect who
    linarith
  · exact quittingJointSurvivalLimit_nonneg roots start

/-- Reverse the first `horizon` chronological roots into forward-packet
order. -/
def quittingReversedRootPrefix
    (roots : ℕ → ι → PMF Bool) (horizon time : ℕ) : ι → PMF Bool :=
  roots (horizon - 1 - time)

/-- Reverse the literal restarted terminal payoffs over a finite prefix. -/
def quittingReversedRootSequenceValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (horizon time : ℕ) : Payoff ι :=
  quittingRootSequenceTailVector reward roots (horizon - time)

omit [DecidableEq ι] in
/-- Reversal preserves the exact total absorption charge of a finite
chronological prefix. -/
theorem sum_absorptionMass_quittingReversedRootPrefix
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
      quittingRootAbsorptionMass
        (quittingReversedRootPrefix roots horizon time)) =
      ∑ time ∈ Finset.range horizon,
        quittingRootAbsorptionMass (roots time) := by
  exact Finset.sum_range_reflect
    (fun time ↦ quittingRootAbsorptionMass (roots time)) horizon

omit [DecidableEq ι] in
/-- Reversal of literal restarted payoffs satisfies the forward Bellman
orientation on every row of the finite prefix. -/
theorem quittingReversedRootSequenceValue_policy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {horizon time : ℕ} (htime : time < horizon) :
    quittingReversedRootSequenceValue reward roots horizon (time + 1) =
      quittingRootSuccessorPayoff reward
        (quittingReversedRootSequenceValue reward roots horizon time)
        (quittingReversedRootPrefix roots horizon time) := by
  have hnext : horizon - time = (horizon - 1 - time) + 1 := by omega
  have hcurrent : horizon - (time + 1) = horizon - 1 - time := by omega
  simpa only [quittingReversedRootSequenceValue, quittingReversedRootPrefix,
    hnext, hcurrent] using
      quittingRootSequenceTailVector_policy reward roots (horizon - 1 - time)

/-- All literal restarted terminal payoffs of a row-perfect source satisfy
the approximate punishment floor under all-player normality. The proof uses
one fixed finite reversed window ending at the arbitrary displayed date. -/
theorem punishmentFloor_le_quittingRootSequenceTailVector_of_rowPerfect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {rewardBound floorError rowError : ℝ}
    (hrewardBound : 0 < rewardBound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hnormal : ∀ player, IsQuittingNormalPlayer reward player)
    (hfloorError : 0 < floorError)
    (hrowError : rowError ≤
      min (floorError / 2) (floorError ^ 2 / (8 * rewardBound)))
    (hperfect : ∀ time, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (time + 1))
      (roots time) rowError) :
    ∀ time player,
      quittingPunishmentValue reward player - floorError ≤
        quittingRootSequenceTailVector reward roots time player := by
  let κ := floorError ^ 2 / (8 * rewardBound)
  have hκ : 0 < κ := by
    dsimp only [κ]
    positivity
  obtain ⟨length, hlength⟩ := exists_nat_gt ((rewardBound + rewardBound) / κ)
  have hburn : rewardBound + rewardBound < (length : ℝ) * κ :=
    (div_lt_iff₀ hκ).mp hlength
  intro start player
  let value : ℕ → Payoff ι := fun offset ↦
    quittingRootSequenceTailVector reward roots (start + length - offset)
  let reversedRoots : ℕ → ι → PMF Bool := fun offset ↦
    roots (start + length - 1 - offset)
  have hstart : ∀ who, -rewardBound ≤ value 0 who := by
    intro who
    have hbound := abs_quittingRootSequenceTailVector_le
      reward roots hreward (start + length) who
    dsimp only [value]
    simpa only [Nat.sub_zero] using neg_le_of_abs_le hbound
  have hquit : ∀ offset, offset < length → ∀ who,
      quittingRootQuitPayoff reward (value offset) (reversedRoots offset) who ≤
        value (offset + 1) who + rowError := by
    intro offset hoffset who
    let index := start + length - 1 - offset
    have hcurrent : start + length - offset = index + 1 := by
      dsimp only [index]
      omega
    have hnext : start + length - (offset + 1) = index := by
      dsimp only [index]
      omega
    have hrow := (hperfect index who).1
    rw [← quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector]
      at hrow
    change quittingRootQuitPayoff reward
      (quittingRootSequenceTailVector reward roots (index + 1))
      (roots index) who ≤
        quittingRootSequenceTailVector reward roots index who + rowError at hrow
    simpa only [value, reversedRoots, hcurrent, hnext, index] using hrow
  have hcontinue : ∀ offset, offset < length → ∀ who,
      quittingRootContinuePayoff reward
          (value offset) (reversedRoots offset) who ≤
        value (offset + 1) who + rowError := by
    intro offset hoffset who
    let index := start + length - 1 - offset
    have hcurrent : start + length - offset = index + 1 := by
      dsimp only [index]
      omega
    have hnext : start + length - (offset + 1) = index := by
      dsimp only [index]
      omega
    have hrow := (hperfect index who).2.1
    rw [← quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector]
      at hrow
    change quittingRootContinuePayoff reward
      (quittingRootSequenceTailVector reward roots (index + 1))
      (roots index) who ≤
        quittingRootSequenceTailVector reward roots index who + rowError at hrow
    simpa only [value, reversedRoots, hcurrent, hnext, index] using hrow
  have hfloor := quittingPunishmentFloor_le_of_finite_endpointErrors_after_burnIn
    reward value reversedRoots hrewardBound hreward hnormal hfloorError
    hrowError (by simpa only [κ] using hburn) hstart hquit hcontinue
    length le_rfl le_rfl player
  simpa only [value, Nat.add_sub_cancel_right] using hfloor

omit [DecidableEq ι] in
/-- A nonsummable nonnegative absorption clock reaches every finite charge
target in some finite prefix. -/
theorem exists_horizon_chargeTarget_le_sum_absorptionMass
    (roots : ℕ → ι → PMF Bool)
    (hdiverges : ¬ Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (chargeTarget : ℝ) :
    ∃ horizon, chargeTarget ≤ ∑ time ∈ Finset.range horizon,
      quittingRootAbsorptionMass (roots time) := by
  have htends : Tendsto (fun horizon ↦
      ∑ time ∈ Finset.range horizon,
        quittingRootAbsorptionMass (roots time)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun time ↦ quittingRootAbsorptionMass_nonneg (roots time))).1 hdiverges
  exact (htends.eventually (eventually_ge_atTop chargeTarget)).exists

end GameTheory

