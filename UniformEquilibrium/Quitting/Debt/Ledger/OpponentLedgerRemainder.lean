import UniformEquilibrium.Quitting.Stationary.MinMax

/-! # Sharp signed remainder of the deleted-player payoff ledger -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Only finite opponent absorption between the two dates pays a signed
increment of the deleted-player ledger. -/
theorem abs_quittingLiveLedgerAccum_sub_le_survival_drop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff length : ℕ) {bound : ℝ}
    (hreward : ∀ terminal, |reward terminal who| ≤ bound) :
    |quittingLiveLedgerAccum reward roots who 0 (cutoff + length) -
      quittingLiveLedgerAccum reward roots who 0 cutoff| ≤
      bound * (quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalWeight roots who 0 (cutoff + length)) := by
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  induction length with
  | zero => simp
  | succ length ih =>
    rw [Nat.add_succ, quittingLiveLedgerAccum_zero_succ]
    have htri := abs_add_le
      (quittingLiveLedgerAccum reward roots who 0 (cutoff + length) -
        quittingLiveLedgerAccum reward roots who 0 cutoff)
      (quittingOpponentSurvivalWeight roots who 0 (cutoff + length) *
        quittingFixedOpponentsContinueReward reward roots who (cutoff + length))
    have hpay := abs_quittingFixedOpponentsContinueReward_le_hazard
      reward roots who (cutoff + length) bound hbound hreward
    have hsurv := quittingOpponentSurvivalWeight_nonneg roots who 0 (cutoff + length)
    rw [abs_mul, abs_of_nonneg hsurv] at htri
    have hscaled := mul_le_mul_of_nonneg_left hpay hsurv
    rw [quittingOpponentSurvivalWeight_zero_succ]
    have hrewrite : quittingLiveLedgerAccum reward roots who 0 (cutoff + length) +
        quittingOpponentSurvivalWeight roots who 0 (cutoff + length) *
          quittingFixedOpponentsContinueReward reward roots who (cutoff + length) -
        quittingLiveLedgerAccum reward roots who 0 cutoff =
      (quittingLiveLedgerAccum reward roots who 0 (cutoff + length) -
        quittingLiveLedgerAccum reward roots who 0 cutoff) +
        quittingOpponentSurvivalWeight roots who 0 (cutoff + length) *
          quittingFixedOpponentsContinueReward reward roots who (cutoff + length) := by ring
    rw [hrewrite]
    nlinarith

/-- The uncollected Never payoff is controlled by late finite opponent
absorption, not by their residual Never cylinder. The limit may be zero or one. -/
theorem abs_quittingNeverValue_sub_ledger_le_survival_remainder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) {bound survival : ℝ}
    (hreward : ∀ terminal, |reward terminal who| ≤ bound)
    (hlimit : Tendsto (quittingOpponentSurvivalWeight roots who 0)
      atTop (nhds survival)) :
    |quittingRootSequencePureTimeTerminalValue reward roots who none 0 -
      quittingLiveLedgerAccum reward roots who 0 cutoff| ≤
      bound * (quittingOpponentSurvivalWeight roots who 0 cutoff - survival) := by
  have hledger := (tendsto_quittingLiveLedgerAccum reward roots who).comp
    (tendsto_add_atTop_nat cutoff)
  have hsurvival := hlimit.comp (tendsto_add_atTop_nat cutoff)
  apply le_of_tendsto_of_tendsto
    ((hledger.sub tendsto_const_nhds).abs)
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub hsurvival))
  exact Eventually.of_forall fun length ↦ by
    simpa only [Function.comp_apply, Nat.add_comm length cutoff] using
      abs_quittingLiveLedgerAccum_sub_le_survival_drop reward roots who cutoff length hreward

end GameTheory
