/-
Support counterfactual extraction at a positive-debt coordinate.

Against fixed opponents on the unique live history, a player's own behavioral
strategy induces a stopping law on `Option ℕ`, and the player's terminal payoff
is exactly the average of the pure quit-time and `Never` deviation payoffs
under that law.  Deadline boundedness makes the player's behavioral cap
attainable by one literal pure plan.  Averaging then forces one plan of
strictly positive law mass whose pure-time payoff is no larger than the average,
so the cap attainer beats it by at least the coordinate's terminal semantic
debt.

That ordered pair of pure witnesses is exactly the entrance of the production
paid first-disagreement decoder, so the extracted counterfactual carries a
literal first-disagreement row on the very same actual profile.  Composing with
the purification-descent capstone shape turns a deadline-bounded strictly
positive global debt minimum into an off-minimum profile carrying such a row
whose gain floor is that profile's average debt.

The source witness is a positive-mass component of the prescribed stopping law.
It is not identified with the prescribed strategy, and nothing here claims that
the prescribed strategy is pure, that the exhibited profile is a minimum, or
that any equilibrium is selected.
-/
import FablePurificationDescent
import MathUE.ProbabilityMassFunction.BoundedSupportAverage
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## G1: the support counterfactual at a positive-debt coordinate -/

/-- **G1.**  At a deadline-bounded profile, an observer carrying strictly
positive terminal semantic debt has a cap-attaining pure plan and a pure plan
of strictly positive own stopping-law mass whose pure-time deviation payoffs
differ by at least that debt. -/
theorem fable_positiveDebt_support_counterfactual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline) (observer : ι)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) observer) :
    ∃ capWitness sourceWitness : Option ℕ,
      quittingPureTimeDeviationPayoff reward profile observer capWitness =
          quittingContinuationBestResponseValue reward profile observer ∧
        sourceWitness ∈
          (quittingBehaviorStoppingLaw reward (profile observer)).support ∧
        0 < quittingBehaviorStoppingLaw reward (profile observer)
          sourceWitness ∧
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer ≤
          quittingPureTimeDeviationPayoff reward profile observer capWitness -
            quittingPureTimeDeviationPayoff reward profile observer
              sourceWitness ∧
        0 < quittingPureTimeDeviationPayoff reward profile observer capWitness -
          quittingPureTimeDeviationPayoff reward profile observer
            sourceWitness := by
  obtain ⟨capWitness, hcap, -⟩ := fable_exists_deadlineBounded_pureTime_eq_cap
    reward profile observer hbound
  have habs : ∀ point : Option ℕ,
      |quittingPureTimeDeviationPayoff reward profile observer point| ≤
        quittingRewardBound reward := fun point =>
    abs_quittingTerminalPayoff_le reward _ observer
      (abs_reward_le_quittingRewardBound reward)
  have hmixture : quittingTerminalPayoff reward profile observer =
      expect (quittingBehaviorStoppingLaw reward (profile observer))
        (quittingPureTimeDeviationPayoff reward profile observer) := by
    have hlaw := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile observer (profile observer)
    rw [Function.update_eq_self] at hlaw
    exact hlaw
  obtain ⟨sourceWitness, hsupport, hle⟩ :=
    Math.ProbabilityMassFunction.exists_mem_support_le_expect
      (quittingBehaviorStoppingLaw reward (profile observer))
      (quittingPureTimeDeviationPayoff reward profile observer) habs
  have hgap : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer ≤
      quittingPureTimeDeviationPayoff reward profile observer capWitness -
        quittingPureTimeDeviationPayoff reward profile observer
          sourceWitness := by
    rw [fable_semanticDebt_profile_eq, hcap, hmixture]
    linarith
  exact ⟨capWitness, sourceWitness, hcap, hsupport,
    pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp hsupport), hgap,
    lt_of_lt_of_le hdebt hgap⟩

/-! ## G2: composing with the paid first-disagreement decoder -/

/-- **G2.**  The G1 counterfactual pair is an entrance of the production paid
first-disagreement decoder, so the same actual profile carries a literal
first-disagreement row for the ordered pair, at the observer's debt as its
gain floor. -/
theorem fable_positiveDebt_support_counterfactual_paidRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline) (observer : ι)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) observer) :
    ∃ capWitness sourceWitness : Option ℕ,
      quittingPureTimeDeviationPayoff reward profile observer capWitness =
          quittingContinuationBestResponseValue reward profile observer ∧
        0 < quittingBehaviorStoppingLaw reward (profile observer)
          sourceWitness ∧
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer ≤
          quittingPureTimeDeviationPayoff reward profile observer capWitness -
            quittingPureTimeDeviationPayoff reward profile observer
              sourceWitness ∧
        ∃ row : QuittingPaidFirstDisagreementRow reward profile observer
            (quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer),
          row.sourceWitness = sourceWitness ∧
            row.receivingWitness = capWitness := by
  obtain ⟨capWitness, sourceWitness, hcap, -, hmass, hgap, -⟩ :=
    fable_positiveDebt_support_counterfactual reward profile hbound observer
      hdebt
  exact ⟨capWitness, sourceWitness, hcap, hmass, hgap,
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward profile
      observer sourceWitness capWitness _ hdebt hgap⟩

/-! ## G3: the off-minimum capstone composition -/

omit [DecidableEq ι] in
/-- Every canonical pure-time date vector over a finite player type is
deadline bounded somewhere. -/
private theorem fable_exists_deadlineBounded_canonicalProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tau : ι → Option ℕ) :
    ∃ deadline : ℕ,
      FableDeadlineBounded reward (fableCanonicalProfile reward tau)
        deadline := by
  classical
  refine ⟨∑ player, (tau player).getD 0,
    fableDeadlineBounded_canonicalProfile reward tau ?_⟩
  intro who date hdate
  have hle : (tau who).getD 0 ≤ ∑ player, (tau player).getD 0 :=
    Finset.single_le_sum (f := fun player => (tau player).getD 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ who)
  rw [hdate] at hle
  simpa using hle

/-- A pure-time gain at a profile never exceeds the mover's terminal semantic
debt there. -/
private theorem fable_pureTimeGain_le_semanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward profile observer choice -
        quittingTerminalPayoff reward profile observer ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer := by
  have hle := le_csSup
    (bddAbove_range_quittingPureTimeDeviationPayoff reward profile observer)
    (Set.mem_range_self choice)
  rw [← quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
    at hle
  rw [fable_semanticDebt_profile_eq]
  linarith

/-- A strictly positive total debt forces a nonempty player type. -/
private theorem fable_card_pos_of_positive_debtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    0 < Fintype.card ι := by
  classical
  by_contra hcontra
  have hempty : (Finset.univ : Finset ι) = ∅ :=
    Finset.card_eq_zero.mp (by rw [Finset.card_univ]; omega)
  have hsumEq : ∑ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := rfl
  rw [← hsumEq, hempty, Finset.sum_empty] at hpositive
  exact absurd hpositive (lt_irrefl 0)

/-- **G3.**  A deadline-bounded profile whose terminal-semantic pair is a
strictly positive global minimum of total debt exhibits a deadline-bounded
profile strictly above that minimum, a responder there, a cap-attaining pure
plan, and a pure plan of strictly positive responder stopping-law mass, whose
pure-time deviation payoffs differ by at least the exhibited profile's average
debt, together with the literal paid first-disagreement row of that ordered
pair. -/
theorem fable_deadlineBounded_minimum_offMinimum_supportCounterfactualRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    ∃ (sigma : (quittingGame reward).BehaviorProfile) (bound : ℕ)
      (responder : ι) (capWitness sourceWitness : Option ℕ),
      FableDeadlineBounded reward sigma bound ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) <
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward sigma) ∧
        quittingPureTimeDeviationPayoff reward sigma responder capWitness =
          quittingContinuationBestResponseValue reward sigma responder ∧
        0 < quittingBehaviorStoppingLaw reward (sigma responder)
          sourceWitness ∧
        quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward sigma) /
            (Fintype.card ι : ℝ) ≤
          quittingPureTimeDeviationPayoff reward sigma responder capWitness -
            quittingPureTimeDeviationPayoff reward sigma responder
              sourceWitness ∧
        ∃ row : QuittingPaidFirstDisagreementRow reward sigma responder
            (quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward sigma) /
              (Fintype.card ι : ℝ)),
          row.sourceWitness = sourceWitness ∧
            row.receivingWitness = capWitness := by
  classical
  obtain ⟨sigma, bound, hsigmaBound, hlt, responder, choice, hport⟩ :
      ∃ (sigma : (quittingGame reward).BehaviorProfile) (bound : ℕ),
        FableDeadlineBounded reward sigma bound ∧
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward profile) <
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward sigma) ∧
          ∃ (responder : ι) (choice : Option ℕ),
            quittingTerminalSemanticDebtSum
                  (quittingTerminalSemanticPair reward sigma) /
                (Fintype.card ι : ℝ) ≤
              quittingPureTimeDeviationPayoff reward sigma responder choice -
                quittingTerminalPayoff reward sigma responder := by
    rcases fable_deadlineBounded_minimum_offMinimum_paidPort_shape reward
      profile hbound hminimum hpositive with ⟨tau, htau, hport⟩ | hright
    · obtain ⟨canonicalBound, hcanonicalBound⟩ :=
        fable_exists_deadlineBounded_canonicalProfile reward tau
      exact ⟨fableCanonicalProfile reward tau, canonicalBound, hcanonicalBound,
        htau, hport⟩
    · exact hright
  have hcardPos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast fable_card_pos_of_positive_debtSum reward profile hpositive
  have hfloorPos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward sigma) / (Fintype.card ι : ℝ) :=
    div_pos (lt_trans hpositive hlt) hcardPos
  have hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward sigma) responder :=
    lt_of_lt_of_le hfloorPos
      (le_trans hport
        (fable_pureTimeGain_le_semanticDebt reward sigma responder choice))
  obtain ⟨capWitness, sourceWitness, hcap, -, hmass, hgap, -⟩ :=
    fable_positiveDebt_support_counterfactual reward sigma hsigmaBound
      responder hdebt
  have hfloor : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward sigma) / (Fintype.card ι : ℝ) ≤
      quittingPureTimeDeviationPayoff reward sigma responder capWitness -
        quittingPureTimeDeviationPayoff reward sigma responder sourceWitness :=
    le_trans (le_trans hport
      (fable_pureTimeGain_le_semanticDebt reward sigma responder choice)) hgap
  exact ⟨sigma, bound, responder, capWitness, sourceWitness, hsigmaBound, hlt,
    hcap, hmass, hfloor,
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward sigma
      responder sourceWitness capWitness _ hfloorPos hfloor⟩

end GameTheory
