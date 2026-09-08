import UniformEquilibrium.Diagnostics.Quitting.OneDateProductRootCaps
import MathUE.PMFProduct.PureUpdateExpectation

/-!
# Actual terminal debt from screened membership gaps

A sure opponent at date zero screens every complete behavioral response.
The identities retain the original reward table, unpadded root-then-Never
profile, and individual product draws for a subsequent supported-vertex argument.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The directed reward difference obtained by toggling only the selected
player toward its preferred root action. Own root action is overwritten. -/
def quittingDirectedMembershipGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (preferred : Bool) (action : ι → Bool) : ℝ :=
  quittingRootPayoff reward 0 (Function.update action who preferred) who -
    quittingRootPayoff reward 0 (Function.update action who (!preferred)) who

@[simp]
theorem quittingDirectedMembershipGap_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (preferred choice : Bool) (action : ι → Bool) :
    quittingDirectedMembershipGap reward who preferred (Function.update action who choice) =
      quittingDirectedMembershipGap reward who preferred action := by
  simp only [quittingDirectedMembershipGap, Function.update_idem]

/-- Expected directed gaps are precisely the preferred-minus-opposite root
endpoint differences, without any assumption on action support. -/
theorem expect_quittingDirectedMembershipGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool) :
    expect (pmfPi root) (quittingDirectedMembershipGap reward who preferred) =
      if preferred then
        oneDateProductQuitEndpoint reward root who -
          oneDateProductContinueEndpoint reward root who
      else
        oneDateProductContinueEndpoint reward root who -
          oneDateProductQuitEndpoint reward root who := by
  unfold quittingDirectedMembershipGap
  rw [expect_sub, ← Math.PMFProduct.expect_pmfPi_update_pure root who preferred
    (fun action => quittingRootPayoff reward 0 action who),
    ← Math.PMFProduct.expect_pmfPi_update_pure root who (!preferred)
      (fun action => quittingRootPayoff reward 0 action who)]
  cases preferred <;> rfl

/-- Pointwise nonnegative directed gaps on supported product draws make the
preferred action weakly best after averaging. Values off support are irrelevant. -/
theorem expect_quittingDirectedMembershipGap_nonneg_of_supported
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool)
    (hcoherent : ∀ action ∈ (pmfPi root).support,
      0 ≤ quittingDirectedMembershipGap reward who preferred action) :
    0 ≤ expect (pmfPi root) (quittingDirectedMembershipGap reward who preferred) := by
  simpa only [expect_const] using
    Math.ProbabilityMassFunction.expect_mono_on_support (pmfPi root) (fun _ => 0)
      (quittingDirectedMembershipGap reward who preferred) hcoherent

/-- Independence factors the expected losing-action gap into the losing
action's probability and the expected opponent gap. -/
theorem expect_losingMembershipGap_eq_losingMass_mul_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool) :
    expect (pmfPi root) (fun action =>
      if action who = preferred then 0
      else quittingDirectedMembershipGap reward who preferred action) =
      (root who (!preferred)).toReal *
        expect (pmfPi root) (quittingDirectedMembershipGap reward who preferred) := by
  have hpinned (choice : Bool) :
      expect (pmfPi (Function.update root who (PMF.pure choice))) (fun action =>
        if action who = preferred then 0
        else quittingDirectedMembershipGap reward who preferred action) =
      if choice = preferred then 0
      else expect (pmfPi root) (quittingDirectedMembershipGap reward who preferred) := by
    rw [Math.PMFProduct.expect_pmfPi_update_pure]
    simp only [Function.update_self, quittingDirectedMembershipGap_update]
    by_cases hchoice : choice = preferred
    · simp [hchoice]
    · simp [hchoice]
  have hdecompose : pmfPi root = (root who).bind
      (fun choice => pmfPi (Function.update root who (PMF.pure choice))) := by
    simpa using pmfPi_update_bind root who (root who)
  calc
    _ = expect (root who) (fun choice =>
        expect (pmfPi (Function.update root who (PMF.pure choice))) (fun action =>
          if action who = preferred then 0
          else quittingDirectedMembershipGap reward who preferred action)) := by
      rw [hdecompose, expect_bind]
    _ = expect (root who) (fun choice =>
        if choice = preferred then 0
        else expect (pmfPi root) (quittingDirectedMembershipGap reward who preferred)) := by
      congr 1
      funext choice
      exact hpinned choice
    _ = _ := by
      rw [expect_eq_sum, Fintype.sum_bool]
      cases preferred <;> simp

/-- With a sure opponent and an averaged-best action, the complete behavioral
debt of the unpadded root is exactly losing probability times expected gap. -/
theorem quittingTerminalDeviationDebt_oneDateThenNever_eq_losingMass_mul_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool)
    {quitter : ι} (hne : quitter ≠ who)
    (hsure : (root quitter true).toReal = 1)
    (hbest : 0 ≤ expect (pmfPi root)
      (quittingDirectedMembershipGap reward who preferred)) :
    quittingTerminalDeviationDebt reward (quittingOneDateThenNeverProfile reward root) who =
      (root who (!preferred)).toReal *
        expect (pmfPi root) (quittingDirectedMembershipGap reward who preferred) := by
  have hpayoff : quittingTerminalPayoff reward
      (quittingOneDateThenNeverProfile reward root) who =
        quittingRootSuccessorPayoff reward 0 root who := by
    unfold quittingOneDateThenNeverProfile
    rw [quittingTerminalPayoff_rootThenContinuation_eq,
      oneDateProductTerminalPayoff_alwaysContinueProfile]
    rfl
  rw [quittingTerminalDeviationDebt,
    oneDateProductQuittingContinuationBestResponseValue_oneDateThenNever_sureQuitter
      reward root who hne hsure, hpayoff,
    quittingRootSuccessorPayoff_eq_endpointMix, expect_quittingDirectedMembershipGap]
  rw [expect_quittingDirectedMembershipGap] at hbest
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  cases preferred with
  | false =>
      change 0 ≤ oneDateProductContinueEndpoint reward root who -
        oneDateProductQuitEndpoint reward root who at hbest
      rw [max_eq_right (sub_nonneg.mp hbest)]
      simp only [Bool.not_false, Bool.false_eq_true, ite_false]
      unfold oneDateProductContinueEndpoint oneDateProductQuitEndpoint at *
      rw [show (root who false).toReal = 1 - (root who true).toReal by linarith]
      ring
  | true =>
      change 0 ≤ oneDateProductQuitEndpoint reward root who -
        oneDateProductContinueEndpoint reward root who at hbest
      rw [max_eq_left (sub_nonneg.mp hbest)]
      simp only [Bool.not_true, ite_true]
      unfold oneDateProductContinueEndpoint oneDateProductQuitEndpoint at *
      rw [show (root who true).toReal = 1 - (root who false).toReal by linarith]
      ring

/-- The same actual full debt is the expected losing-action gap on the
original product draws; no lottery over replacement profiles is constructed. -/
theorem quittingTerminalDeviationDebt_oneDateThenNever_eq_expect_losingMembershipGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool)
    {quitter : ι} (hne : quitter ≠ who)
    (hsure : (root quitter true).toReal = 1)
    (hbest : 0 ≤ expect (pmfPi root)
      (quittingDirectedMembershipGap reward who preferred)) :
    quittingTerminalDeviationDebt reward (quittingOneDateThenNeverProfile reward root) who =
      expect (pmfPi root) (fun action =>
        if action who = preferred then 0
        else quittingDirectedMembershipGap reward who preferred action) := by
  rw [expect_losingMembershipGap_eq_losingMass_mul_gap]
  exact quittingTerminalDeviationDebt_oneDateThenNever_eq_losingMass_mul_gap
    reward root who preferred hne hsure hbest

/-- Supported pointwise coherence supplies the averaged-best premise of the
complete unpadded debt identity. No root-Nash or attainment premise is needed. -/
theorem quittingTerminalDeviationDebt_oneDateThenNever_eq_expect_of_supported_coherent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool)
    {quitter : ι} (hne : quitter ≠ who)
    (hsure : (root quitter true).toReal = 1)
    (hcoherent : ∀ action ∈ (pmfPi root).support,
      0 ≤ quittingDirectedMembershipGap reward who preferred action) :
    quittingTerminalDeviationDebt reward (quittingOneDateThenNeverProfile reward root) who =
      expect (pmfPi root) (fun action =>
        if action who = preferred then 0
        else quittingDirectedMembershipGap reward who preferred action) :=
  quittingTerminalDeviationDebt_oneDateThenNever_eq_expect_losingMembershipGap
    reward root who preferred hne hsure
      (expect_quittingDirectedMembershipGap_nonneg_of_supported
        reward root who preferred hcoherent)

end GameTheory
