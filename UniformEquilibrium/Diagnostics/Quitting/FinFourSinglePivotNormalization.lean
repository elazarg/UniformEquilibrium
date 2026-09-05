import UniformEquilibrium.Diagnostics.Quitting.FinFourSinglePivotActualSource
import UniformEquilibrium.Quitting.Terminal.SinglePivotCanonicalConsequences

/-! # Same-table Fin4 normalization with explicit source and scalar conclusions -/

noncomputable section

namespace GameTheory

/-- The original residual and one fixed pivot determine the normalized table.
All semantic fields concern that literal table; no minimum or packet ancestry
is asserted. -/
structure FinFourSinglePivotNormalization
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (bound : ℝ) where
  residual : FinFourQuantitativeFullSupportHardResidual reward bound
  pivot : Fin 4
  pivot_pos : 0 < quittingSoloReward reward pivot pivot
  canonical : IsSinglePivotSingletonTable (quittingSinglePivotNormalizedReward reward pivot) pivot
  reward_bound : ∀ terminal who,
    |quittingSinglePivotNormalizedReward reward pivot terminal who| ≤
      2 * bound / quittingSoloReward reward pivot pivot
  punishment : ∀ who,
    quittingPunishmentValue (quittingSinglePivotNormalizedReward reward pivot) who =
      (quittingPunishmentValue reward who - quittingSinglePivotOffset reward pivot who) /
        quittingSoloReward reward pivot pivot
  normal : ∀ who,
    quittingPunishmentValue (quittingSinglePivotNormalizedReward reward pivot) who ≤
      quittingSoloReward (quittingSinglePivotNormalizedReward reward pivot) who who
  no_uniformPayoff : ¬ ∃ payoff : Payoff (Fin 4),
    (quittingGame (quittingSinglePivotNormalizedReward reward pivot)).IsUniformEquilibriumPayoff
      none payoff
  profile_floor : ∀ profile,
    residual.witness.terminalGap ^ 2 / (16 * bound ^ 2) ≤
      quittingTerminalExploitability (quittingSinglePivotNormalizedReward reward pivot) profile
  actual_gap : HasTerminalExploitabilityGap (quittingSinglePivotNormalizedReward reward pivot)
    (residual.witness.terminalGap ^ 2 / (32 * bound ^ 2))
  every_exact_scalar_floor :
    ∀ deadline (mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction deadline)),
      IsQuittingFiniteDeadlineNash
        (quittingSinglePivotNormalizedReward reward pivot) deadline 0 mixed →
      residual.witness.terminalGap ^ 2 / (16 * bound ^ 2) ≤
        quittingFiniteDeadlineNeverPayoff
            (quittingSinglePivotNormalizedReward reward pivot) deadline mixed pivot +
          quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
          quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward pivot)
            (quittingFiniteDeadlineTimingProfile
              (quittingSinglePivotNormalizedReward reward pivot) deadline mixed) pivot ∧
        residual.witness.terminalGap ^ 2 / (16 * bound ^ 2) ≤
          quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot
  every_deadline_nash : ∀ deadline,
    ∃ mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (quittingFiniteDeadlineTimingGame
        (quittingSinglePivotNormalizedReward reward pivot) deadline).mixedExtension.IsNash mixed ∧
      IsQuittingFiniteDeadlineNash
        (quittingSinglePivotNormalizedReward reward pivot) deadline 0 mixed

/-- Bare original no-UE data produce every field of the normalization record.
The record is an output certificate, not an additional source premise. -/
theorem nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    Nonempty (FinFourSinglePivotNormalization reward bound) := by
  obtain ⟨residual, pivot, hpivot, hnormal, hcanonical, hfloor, hactual, _⟩ :=
    exists_finFourHardResidual_positivePivot_and_everyDeadlineNash reward hreward hnot
  have hbound : 0 < bound := hpivot.trans_le
    (le_of_abs_le (hreward (quittingSingletonTerminal pivot) pivot))
  have hgap : 0 < residual.witness.terminalGap ^ 2 / (16 * bound ^ 2) := by
    have := residual.witness.terminalGap_pos
    positivity
  refine ⟨{
    residual := residual
    pivot := pivot
    pivot_pos := hpivot
    canonical := hcanonical
    reward_bound := abs_quittingSinglePivotNormalizedReward_le reward pivot hreward hpivot
    punishment := fun who ↦
      quittingPunishmentValue_singlePivotNormalized reward pivot who hpivot (hnormal who)
    normal := singlePivotSingletonTable_punishment_le_solo _ pivot hcanonical
    no_uniformPayoff := ?_
    profile_floor := hfloor
    actual_gap := hactual
    every_exact_scalar_floor := singlePivot_exactMenuNash_scalar_and_deletedNever_ge
      _ pivot hcanonical hgap hfloor
    every_deadline_nash := fun deadline ↦ exists_exactFiniteDeadlineTimingNash _ deadline
  }⟩
  apply quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    _ (gap := residual.witness.terminalGap ^ 2 / (32 * bound ^ 2)) _ hactual
  have := residual.witness.terminalGap_pos
  positivity

/-- Restricting Fin4 counterexamples to one fixed positive singleton loses
no counterexample; the reverse direction simply forgets the canonical shape. -/
theorem exists_finFour_no_uniformPayoff_iff_exists_singlePivot
    : (∃ reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
        ¬ ∃ payoff : Payoff (Fin 4),
          (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ∃ reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
        ∃ pivot : Fin 4, IsSinglePivotSingletonTable reward pivot ∧
          ¬ ∃ payoff : Payoff (Fin 4),
            (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  constructor
  · rintro ⟨reward, hnot⟩
    obtain ⟨source⟩ := nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff
      reward (abs_reward_le_quittingRewardBound reward) hnot
    exact ⟨quittingSinglePivotNormalizedReward reward source.pivot,
      source.pivot, source.canonical, source.no_uniformPayoff⟩
  · rintro ⟨reward, _, _, hnot⟩
    exact ⟨reward, hnot⟩

end GameTheory
