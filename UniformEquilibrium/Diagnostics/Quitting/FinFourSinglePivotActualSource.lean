import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuSource
import UniformEquilibrium.Quitting.Root.SinglePivotNormalization
import UniformEquilibrium.Quitting.Punishment.SinglePivotTerminalGap

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- A same-table Fin4 hard residual contains a positive singleton pivot.  The
residual already carries punishment normality for every player; the pivot is
selected only after the one residual has been fixed. -/
theorem exists_finFourHardResidual_and_positiveSingletonPivot_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ S who, |reward S who| ≤ bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ _residual : FinFourQuantitativeFullSupportHardResidual reward bound,
      ∃ pivot : Fin 4,
        0 < reward (quittingSingletonTerminal pivot) pivot ∧
          ∀ who, IsQuittingNormalPlayer reward who := by
  let residual := Classical.choice
    (nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
      reward hreward hnot)
  have hpositive : ∃ pivot : Fin 4,
      0 < reward (quittingSingletonTerminal pivot) pivot := by
    by_contra hnone
    push Not at hnone
    let profile := quittingAlwaysContinueProfile reward
    have hzero (who : Fin 4) : quittingTerminalPayoff reward profile who = 0 := by
      exact quittingTerminalPayoff_quittingAlwaysContinue reward who
    have hcap (who : Fin 4) :
        quittingContinuationBestResponseValue reward profile who = 0 := by
      dsimp [profile]
      rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
      exact max_eq_left (hnone who)
    obtain ⟨who, deviation, hgain⟩ := residual.witness.terminalExploitability profile
    have hresponse := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who deviation
    rw [hcap who] at hresponse
    rw [hzero who] at hgain
    linarith [residual.witness.terminalGap_pos]
  obtain ⟨pivot, hpivot⟩ := hpositive
  exact ⟨residual, pivot, hpivot, residual.all_punishmentNormal⟩

/-- Once the same-table residual and its positive pivot have been selected,
every deadline gets a freshly selected exact mixed timing Nash law for the
literal normalized table. -/
theorem exists_finFourHardResidual_positivePivot_and_everyDeadlineNash
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ S who, |reward S who| ≤ bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ residual : FinFourQuantitativeFullSupportHardResidual reward bound,
      ∃ pivot : Fin 4,
        0 < reward (quittingSingletonTerminal pivot) pivot ∧
          (∀ who, IsQuittingNormalPlayer reward who) ∧
          IsSinglePivotSingletonTable
            (quittingSinglePivotNormalizedReward reward pivot) pivot ∧
          (∀ profile, residual.witness.terminalGap ^ 2 / (16 * bound ^ 2) ≤
            quittingTerminalExploitability
              (quittingSinglePivotNormalizedReward reward pivot) profile) ∧
          HasTerminalExploitabilityGap
            (quittingSinglePivotNormalizedReward reward pivot)
            (residual.witness.terminalGap ^ 2 / (32 * bound ^ 2)) ∧
          ∀ deadline, ∃ mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction deadline),
            (quittingFiniteDeadlineTimingGame
                (quittingSinglePivotNormalizedReward reward pivot) deadline).mixedExtension.IsNash
              mixed ∧
            IsQuittingFiniteDeadlineNash
              (quittingSinglePivotNormalizedReward reward pivot) deadline 0 mixed ∧
            (∀ who ≠ pivot, quittingTerminalDeviationDebt
              (quittingSinglePivotNormalizedReward reward pivot)
              (quittingFiniteDeadlineTimingProfile
                (quittingSinglePivotNormalizedReward reward pivot) deadline mixed) who = 0) ∧
            quittingTerminalDeviationDebt
                (quittingSinglePivotNormalizedReward reward pivot)
                (quittingFiniteDeadlineTimingProfile
                  (quittingSinglePivotNormalizedReward reward pivot) deadline mixed) pivot =
              max 0 (quittingFiniteDeadlineNeverPayoff
                  (quittingSinglePivotNormalizedReward reward pivot) deadline mixed pivot +
                quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
                quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward pivot)
                  (quittingFiniteDeadlineTimingProfile
                    (quittingSinglePivotNormalizedReward reward pivot) deadline mixed) pivot) ∧
            quittingTerminalDeviationDebt
                (quittingSinglePivotNormalizedReward reward pivot)
                (quittingFiniteDeadlineTimingProfile
                  (quittingSinglePivotNormalizedReward reward pivot) deadline mixed) pivot ≤
              quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot ∧
            residual.witness.terminalGap ^ 2 / (16 * bound ^ 2) ≤
              quittingTerminalExploitability
                (quittingSinglePivotNormalizedReward reward pivot)
                (quittingFiniteDeadlineTimingProfile
                  (quittingSinglePivotNormalizedReward reward pivot) deadline mixed) ∧
            residual.witness.terminalGap ^ 2 / (16 * bound ^ 2) ≤
              quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot := by
  obtain ⟨residual, pivot, hpivot, hnormal⟩ :=
    exists_finFourHardResidual_and_positiveSingletonPivot_of_no_uniformPayoff
      reward hreward hnot
  have hnormal' : ∀ who,
      quittingPunishmentValue reward who ≤ quittingSoloReward reward who who := hnormal
  have hglobal : ∀ profile,
      residual.witness.terminalGap ≤ quittingTerminalExploitability reward profile :=
    fun profile ↦ (terminalExploitabilityGap_le_quittingTerminalExploitabilityInf
      reward residual.witness.terminalExploitability).trans
        (quittingTerminalExploitabilityInf_le reward profile)
  have hfloor : ∀ profile, residual.witness.terminalGap ^ 2 / (16 * bound ^ 2) ≤
      quittingTerminalExploitability
        (quittingSinglePivotNormalizedReward reward pivot) profile := by
    intro profile
    exact singlePivot_terminalExploitability_ge_gap_sq_div reward pivot profile
      hreward hpivot hnormal' residual.witness.terminalGap_pos hglobal
  have hactual : HasTerminalExploitabilityGap
      (quittingSinglePivotNormalizedReward reward pivot)
      (residual.witness.terminalGap ^ 2 / (32 * bound ^ 2)) :=
    hasTerminalExploitabilityGap_singlePivotNormalized reward pivot hreward hpivot hnormal'
      residual.witness.terminalGap_pos hglobal
  refine ⟨residual, pivot, hpivot, hnormal,
    singlePivotNormalized_isSinglePivotSingletonTable reward pivot hpivot,
    hfloor, hactual, ?_⟩
  intro deadline
  obtain ⟨mixed, hnash, hmenuNash⟩ := exists_exactFiniteDeadlineTimingNash
    (quittingSinglePivotNormalizedReward reward pivot) deadline
  let normalized := quittingSinglePivotNormalizedReward reward pivot
  have hcanonical : IsSinglePivotSingletonTable normalized pivot :=
    singlePivotNormalized_isSinglePivotSingletonTable reward pivot hpivot
  have hnonpivot : ∀ who ≠ pivot, quittingTerminalDeviationDebt normalized
      (quittingFiniteDeadlineTimingProfile normalized deadline mixed) who = 0 := by
    intro who hne
    exact singlePivot_exactMenuNash_nonpivot_debt_eq_zero
      normalized pivot hcanonical deadline mixed hmenuNash hne
  have hpivotDebt := singlePivot_exactMenuNash_pivot_debt_eq_posPart_scalar
      normalized pivot hcanonical deadline mixed hmenuNash
  have hpivotLe := singlePivot_exactMenuNash_pivot_debt_le_deletedNever
      normalized pivot hcanonical deadline mixed hmenuNash
  have hexploitLe : quittingTerminalExploitability normalized
      (quittingFiniteDeadlineTimingProfile normalized deadline mixed) ≤
        quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot := by
    rw [quittingTerminalExploitability_eq_max_debt]
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    by_cases hwho : who = pivot
    · subst who
      exact hpivotLe
    · rw [hnonpivot who hwho]
      unfold quittingFiniteDeadlineOpponentNeverProduct quittingOpponentNeverProduct
      exact Finset.prod_nonneg fun player _ ↦
        Math.Probability.CompactStoppingLaw.realMass_nonneg _ _
  refine ⟨mixed, hnash, hmenuNash, hnonpivot, hpivotDebt, hpivotLe,
    hfloor _, ?_⟩
  exact (hfloor _).trans hexploitLe

end GameTheory
