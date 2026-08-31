import UniformEquilibrium.Diagnostics.Quitting.PureTimeCapAttainment
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-!
# Finite semantic range of canonical pure clocks

This finite quotient records only the prescribed terminal outcome and one
cap-attaining terminal outcome per player.  It avoids any convergence of
pure-clock strategies or absolute deadlines.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite data determining the terminal semantic pair of a canonical
pure-clock profile. -/
structure QuittingPureClockSemanticCode (ι : Type) where
  prescribedOutcome : QuittingTerminalOutcome ι
  capOutcome : ι → QuittingTerminalOutcome ι

instance : Fintype (QuittingPureClockSemanticCode ι) :=
  Fintype.ofEquiv
    (QuittingTerminalOutcome ι × (ι → QuittingTerminalOutcome ι))
    { toFun := fun data => ⟨data.1, data.2⟩
      invFun := fun code => (code.prescribedOutcome, code.capOutcome)
      left_inv := fun data => by cases data; rfl
      right_inv := fun code => by cases code; rfl }

/-- Evaluation of the finite pure-clock semantic code. -/
def QuittingPureClockSemanticCode.evaluate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (code : QuittingPureClockSemanticCode ι) :
    QuittingTerminalSemanticPair ι :=
  (quittingTerminalOutcomeReward reward code.prescribedOutcome,
    fun who => quittingTerminalOutcomeReward reward (code.capOutcome who) who)

/-- The prescribed payoff of a canonical pure-clock profile is the reward of
one terminal outcome, including `Never`. -/
theorem exists_quittingPureTimeProfile_terminalOutcomeReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) :
    ∃ outcome : QuittingTerminalOutcome ι,
      quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward times) =
        quittingTerminalOutcomeReward reward outcome := by
  classical
  by_cases hsupport : (quittingPureTimeDeadlineSupport times).Nonempty
  · obtain ⟨deadline, hnonempty, hbefore⟩ :=
      exists_quittingPureTime_firstDeadline times hsupport
    refine ⟨some ⟨quittingPureTimeCoalitionAt times deadline, hnonempty⟩, ?_⟩
    simpa [quittingTerminalOutcomeReward] using
      quittingTerminalPayoff_pureTimeProfileBehavior_eq
        reward times deadline hbefore hnonempty
  · have hallNever : ∀ who, times who = none := by
      intro who
      cases hchoice : times who with
      | none => rfl
      | some deadline =>
          exfalso
          exact hsupport ⟨deadline,
            (mem_quittingPureTimeDeadlineSupport_iff times deadline).2
              ⟨who, hchoice⟩⟩
    have hprofile : quittingPureTimeProfileBehavior reward times =
        quittingAlwaysContinueProfile reward := by
      funext who
      rw [quittingPureTimeProfileBehavior_apply, hallNever who,
        quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
      rfl
    refine ⟨none, ?_⟩
    rw [hprofile]
    funext who
    rw [quittingTerminalPayoff_quittingAlwaysContinue]
    rfl

/-- Every canonical pure-clock semantic pair is the evaluation of finite
outcome data. -/
theorem exists_quittingPureClockSemanticCode
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) :
    ∃ code : QuittingPureClockSemanticCode ι,
      quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward times) =
        code.evaluate reward := by
  classical
  obtain ⟨prescribedOutcome, hprescribed⟩ :=
    exists_quittingPureTimeProfile_terminalOutcomeReward reward times
  have hcapOutcome : ∀ who : ι, ∃ outcome : QuittingTerminalOutcome ι,
      quittingContinuationBestResponseValue reward
          (quittingPureTimeProfileBehavior reward times) who =
        quittingTerminalOutcomeReward reward outcome who := by
    intro who
    obtain ⟨response, hresponse⟩ :=
      exists_quittingPureTime_capAttainer reward times who
    obtain ⟨outcome, houtcome⟩ :=
      exists_quittingPureTimeProfile_terminalOutcomeReward reward
        (Function.update times who response)
    refine ⟨outcome, ?_⟩
    rw [← hresponse]
    exact congrFun houtcome who
  let code : QuittingPureClockSemanticCode ι :=
    { prescribedOutcome := prescribedOutcome
      capOutcome := fun who => Classical.choose (hcapOutcome who) }
  refine ⟨code, ?_⟩
  ext who <;> simp only [quittingTerminalSemanticPair,
    QuittingPureClockSemanticCode.evaluate, code]
  · exact congrFun hprescribed who
  · exact Classical.choose_spec (hcapOutcome who)

/-- Canonical pure-clock terminal semantic pairs form a finite set, even
though their absolute deadlines are unbounded. -/
theorem finite_range_quittingTerminalSemanticPair_pureTimeProfileBehavior
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (Set.range fun times : QuittingPureTimeProfile ι =>
      quittingTerminalSemanticPair reward
        (quittingPureTimeProfileBehavior reward times)).Finite := by
  classical
  apply (Set.finite_range fun code : QuittingPureClockSemanticCode ι =>
    code.evaluate reward).subset
  rintro pair ⟨times, rfl⟩
  obtain ⟨code, hcode⟩ := exists_quittingPureClockSemanticCode reward times
  exact ⟨code, hcode.symm⟩

end GameTheory
