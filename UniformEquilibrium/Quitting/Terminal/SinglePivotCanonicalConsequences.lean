import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuSource
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Quitting.Punishment.SinglePivotPunishment

/-! # Canonical-table normality and universal finite-menu scalar floors -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- No restrictions on the other entries of a canonical table are needed
for punishment normality. -/
theorem singlePivotSingletonTable_punishment_le_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) (who : ι) :
    quittingPunishmentValue reward who ≤ quittingSoloReward reward who who := by
  have h := quittingPunishmentValue_le reward who (quittingAlwaysContinueProfile reward)
  change quittingPunishmentValue reward who ≤
    quittingContinuationBestResponseValue reward (quittingAlwaysContinueProfile reward) who at h
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile] at h
  change quittingPunishmentValue reward who ≤ max 0 (quittingSoloReward reward who who) at h
  have hsolo : 0 ≤ quittingSoloReward reward who who := by
    change 0 ≤ reward (quittingSingletonTerminal who) who
    rw [hcanonical who]
    split_ifs <;> norm_num
  simpa only [max_eq_right hsolo] using h

/-- A positive full-profile floor forces both displayed scalars at every
exact menu equilibrium, not merely at one selected equilibrium. -/
theorem singlePivot_exactMenuNash_scalar_and_deletedNever_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) {gap : ℝ}
    (hgap : 0 < gap) :
    letI : Nonempty ι := ⟨pivot⟩
    (∀ profile, gap ≤ quittingTerminalExploitability reward profile) →
    ∀ deadline (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)),
      IsQuittingFiniteDeadlineNash reward deadline 0 mixed →
      gap ≤ quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
          quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
          quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot ∧
        gap ≤ quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot := by
  letI : Nonempty ι := ⟨pivot⟩
  intro hfloor deadline mixed hnash
  let profile := quittingFiniteDeadlineTimingProfile reward deadline mixed
  have hdebt : gap ≤ quittingTerminalDeviationDebt reward profile pivot := by
    apply (hfloor profile).trans
    rw [quittingTerminalExploitability_eq_max_debt]
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    by_cases hwho : who = pivot
    · subst who
      exact le_rfl
    · rw [singlePivot_exactMenuNash_nonpivot_debt_eq_zero
        reward pivot hcanonical deadline mixed hnash hwho]
      exact quittingTerminalDeviationDebt_nonneg reward profile pivot
  have hscalar := hdebt
  rw [singlePivot_exactMenuNash_pivot_debt_eq_posPart_scalar
    reward pivot hcanonical deadline mixed hnash] at hscalar
  have hscalar' : gap ≤ quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
      quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
      quittingTerminalPayoff reward profile pivot := by
    rcases le_max_iff.mp hscalar with hzero | hscalar
    · exact (not_le_of_gt hgap hzero).elim
    · exact hscalar
  exact ⟨hscalar', hdebt.trans (singlePivot_exactMenuNash_pivot_debt_le_deletedNever
    reward pivot hcanonical deadline mixed hnash)⟩

end GameTheory
