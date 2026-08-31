import UniformEquilibrium.Diagnostics.Quitting.PureTimeMinimumDescent
import UniformEquilibrium.Diagnostics.Quitting.PositiveMinimumSeedSeamBarrier
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement

/-!
# Off-minimum paid port from a canonical pure-time minimum

After finite deadline descent reaches a strict semantic-debt target, one
coordinate carries at least its average debt.  Canonical opponents admit an
exact pure-time or `Never` cap attainer, and the resulting positive edge has
the checked literal first-disagreement row.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A canonical pure-time positive global minimum has a literal replacement
descendant above the minimum and, on that target, an exact pure-time cap
response carrying more than the original average debt together with its
paid first-disagreement row. -/
theorem pureTimeMinimum_exists_offMinimumPaidPort
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumDebt : ℝ)
    (hlower : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < minimumDebt)
    (times : QuittingPureTimeProfile ι)
    (hminimum :
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward times)) = minimumDebt) :
    ∃ target : QuittingPureTimeProfile ι,
      IsQuittingPureTimeReplacementAncestry times target ∧
      ∃ (who : ι) (response : Option ℕ),
        minimumDebt < quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward target)) ∧
        quittingTerminalPayoff reward
            (quittingPureTimeProfileBehavior reward
              (Function.update target who response)) who =
          quittingContinuationBestResponseValue reward
            (quittingPureTimeProfileBehavior reward target) who ∧
        quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingPureTimeProfileBehavior reward target)) /
              Fintype.card ι ≤
            quittingTerminalPayoff reward
                (quittingPureTimeProfileBehavior reward
                  (Function.update target who response)) who -
              quittingTerminalPayoff reward
                (quittingPureTimeProfileBehavior reward target) who ∧
        minimumDebt / Fintype.card ι <
            quittingTerminalPayoff reward
                (quittingPureTimeProfileBehavior reward
                  (Function.update target who response)) who -
              quittingTerminalPayoff reward
                (quittingPureTimeProfileBehavior reward target) who ∧
        ∃ row : QuittingPaidFirstDisagreementRow reward
            (quittingPureTimeProfileBehavior reward target) who
              (minimumDebt / Fintype.card ι),
          row.sourceWitness = target who ∧
            row.receivingWitness = response := by
  obtain ⟨target, hancestry, hoff⟩ := pureTimeMinimum_exists_offMinimum
    reward minimumDebt hlower hpositive times hminimum
  let profile := quittingPureTimeProfileBehavior reward target
  let pair := quittingTerminalSemanticPair reward profile
  have htargetPositive : 0 < quittingTerminalSemanticDebtSum pair := by
    exact hpositive.trans (by simpa only [pair, profile,
      quittingPureTimeTerminalSemanticDebtSum] using hoff)
  obtain ⟨who, haverage⟩ :=
    exists_quittingTerminalSemanticDebt_ge_average pair htargetPositive
  obtain ⟨response, hresponse⟩ :=
    exists_quittingPureTime_capAttainer reward target who
  have hsourcePayoff :
      quittingPureTimeDeviationPayoff reward profile who (target who) =
        quittingTerminalPayoff reward profile who := by
    unfold quittingPureTimeDeviationPayoff
    rw [← quittingPureTimeProfileBehavior_update]
    have hself : Function.update target who (target who) = target :=
      Function.update_eq_self who target
    rw [hself]
  have hresponsePayoff :
      quittingPureTimeDeviationPayoff reward profile who response =
        quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update target who response)) who := by
    unfold quittingPureTimeDeviationPayoff
    rw [← quittingPureTimeProfileBehavior_update]
  have hedge :
      quittingTerminalPayoff reward
            (quittingPureTimeProfileBehavior reward
              (Function.update target who response)) who -
          quittingTerminalPayoff reward profile who =
        quittingTerminalSemanticDebt pair who := by
    unfold quittingTerminalSemanticDebt
    dsimp only [pair, quittingTerminalSemanticPair]
    rw [hresponse]
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hstrictAverage : minimumDebt / Fintype.card ι <
      quittingTerminalSemanticDebtSum pair / Fintype.card ι := by
    exact div_lt_div_of_pos_right (by simpa only [pair, profile,
      quittingPureTimeTerminalSemanticDebtSum] using hoff) hcard
  have hpaid : minimumDebt / Fintype.card ι <
      quittingTerminalPayoff reward
            (quittingPureTimeProfileBehavior reward
              (Function.update target who response)) who -
          quittingTerminalPayoff reward profile who := by
    rw [hedge]
    exact hstrictAverage.trans_le haverage
  have hgainPositive : 0 < minimumDebt / Fintype.card ι :=
    div_pos hpositive hcard
  obtain ⟨row, hsource, hreceiving⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
      reward profile who (target who) response
        (minimumDebt / Fintype.card ι) hgainPositive (by
          rw [hresponsePayoff, hsourcePayoff]
          exact hpaid.le)
  refine ⟨target, hancestry, who, response, hoff, hresponse, ?_, hpaid,
    row, hsource, hreceiving⟩
  rw [hedge]
  exact haverage

end GameTheory
