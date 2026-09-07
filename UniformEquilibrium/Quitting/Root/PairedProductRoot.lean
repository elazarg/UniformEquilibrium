import MathUE.PairedAffineIntervalEstimates
import MathUE.PMFProduct.Bool
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import UniformEquilibrium.Quitting.Root.TerminalOpponentAdvantage

/-! # Literal independent product roots with two active coordinates -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def root (first second : ι) (firstLaw secondLaw : PMF Bool) : ι → PMF Bool :=
  Function.update (Function.update (fun _ => PMF.pure false) first firstLaw) second secondLaw

def action (first second : ι) (firstAction secondAction : Bool) : ι → Bool :=
  Function.update (Function.update (fun _ => false) first firstAction) second secondAction

omit [Fintype ι] in
@[simp] theorem root_first {first second : ι} (hne : first ≠ second)
    (firstLaw secondLaw : PMF Bool) : root first second firstLaw secondLaw first = firstLaw := by
  simp [root, hne]

omit [Fintype ι] in
@[simp] theorem root_second (first second : ι) (firstLaw secondLaw : PMF Bool) :
    root first second firstLaw secondLaw second = secondLaw := by
  simp [root]

omit [Fintype ι] in
theorem root_outside {first second who : ι} (hfirst : who ≠ first) (hsecond : who ≠ second)
    (firstLaw secondLaw : PMF Bool) :
    root first second firstLaw secondLaw who = PMF.pure false := by
  simp [root, hfirst, hsecond]

theorem expect_root (first second : ι) (firstLaw secondLaw : PMF Bool)
    (f : (ι → Bool) → ℝ) :
    expect (pmfPi (root first second firstLaw secondLaw)) f =
      (1 - (firstLaw true).toReal) * (1 - (secondLaw true).toReal) *
          f (action first second false false) +
        (firstLaw true).toReal * (1 - (secondLaw true).toReal) *
          f (action first second true false) +
        (1 - (firstLaw true).toReal) * (secondLaw true).toReal *
          f (action first second false true) +
        (firstLaw true).toReal * (secondLaw true).toReal *
          f (action first second true true) := by
  unfold root
  rw [pmfPi_update_bind, expect_bind]
  simp_rw [← pmfPi_bind_update_pure, expect_bind, pmfPi_update_pure_family,
    expect_bind, expect_pure]
  simp only [expect_eq_sum, Fintype.sum_bool, pmfBool_false_toReal]
  unfold action
  ring

theorem quitters_action {first second : ι} (hne : first ≠ second)
    (a b : Bool) :
    quittingQuitters (action first second a b) =
      (if a then {first} else ∅) ∪ (if b then {second} else ∅) := by
  ext who
  by_cases hf : who = first
  · subst who
    cases a <;> cases b <;> simp [quittingQuitters, action, hne]
  by_cases hs : who = second
  · subst who
    cases a <;> cases b <;> simp [quittingQuitters, action, hne.symm]
  · cases a <;> cases b <;> simp [quittingQuitters, action, hf, hs]

theorem payoff_action (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {first second : ι} (hne : first ≠ second)
    (a b : Bool) (who : ι) :
    quittingRootPayoff reward tail (action first second a b) who =
      if a then
        if b then reward ⟨{first, second}, by simp⟩ who
        else reward (quittingSingletonTerminal first) who
      else if b then reward (quittingSingletonTerminal second) who else tail who := by
  unfold quittingRootPayoff
  rw [quitters_action hne]
  cases a <;> cases b <;> simp [quittingSingletonTerminal]

theorem rootSuccessor_eq_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail (root first second firstLaw secondLaw) who =
      Math.PairedAffine.bellman
        (reward (quittingSingletonTerminal first) who)
        (reward (quittingSingletonTerminal second) who)
        (reward ⟨{first, second}, by simp⟩ who)
        (firstLaw true).toReal (secondLaw true).toReal (tail who) := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  rw [expect_root]
  simp only [payoff_action reward tail hne, Bool.false_eq_true, if_false, if_true]
  unfold Math.PairedAffine.bellman Math.PairedAffine.contribution
  ring

omit [Fintype ι] in
theorem root_update_first (first second : ι) (firstLaw secondLaw law : PMF Bool)
    (hne : first ≠ second) :
    Function.update (root first second firstLaw secondLaw) first law =
      root first second law secondLaw := by
  unfold root
  rw [Function.update_comm hne.symm, Function.update_idem]

omit [Fintype ι] in
theorem root_update_second (first second : ι) (firstLaw secondLaw law : PMF Bool) :
    Function.update (root first second firstLaw secondLaw) second law =
      root first second firstLaw law := by
  simp [root]

theorem rootQuit_first (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {first second : ι} (hne : first ≠ second)
    (firstLaw secondLaw : PMF Bool) :
    quittingRootQuitPayoff reward tail (root first second firstLaw secondLaw) first =
      Math.PairedAffine.activeValue (reward (quittingSingletonTerminal first) first)
        (reward ⟨{first, second}, by simp⟩ first) (secondLaw true).toReal := by
  change quittingRootSuccessorPayoff reward tail
    (Function.update (root first second firstLaw secondLaw) first (PMF.pure true)) first = _
  rw [root_update_first _ _ _ _ _ hne, rootSuccessor_eq_bellman reward tail hne]
  simp [Math.PairedAffine.bellman, Math.PairedAffine.contribution,
    Math.PairedAffine.activeValue]
  ring

theorem rootContinue_first (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {first second : ι} (hne : first ≠ second)
    (firstLaw secondLaw : PMF Bool) :
    quittingRootContinuePayoff reward tail (root first second firstLaw secondLaw) first =
      (secondLaw true).toReal * reward (quittingSingletonTerminal second) first +
        (1 - (secondLaw true).toReal) * tail first := by
  change quittingRootSuccessorPayoff reward tail
    (Function.update (root first second firstLaw secondLaw) first (PMF.pure false)) first = _
  rw [root_update_first _ _ _ _ _ hne, rootSuccessor_eq_bellman reward tail hne]
  simp [Math.PairedAffine.bellman, Math.PairedAffine.contribution]

omit [Fintype ι] in
theorem root_swap {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool) :
    root first second firstLaw secondLaw = root second first secondLaw firstLaw := by
  exact Function.update_comm (f := fun _ : ι => PMF.pure false) hne firstLaw secondLaw

theorem rootQuit_second (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {first second : ι} (hne : first ≠ second)
    (firstLaw secondLaw : PMF Bool) :
    quittingRootQuitPayoff reward tail (root first second firstLaw secondLaw) second =
      Math.PairedAffine.activeValue (reward (quittingSingletonTerminal second) second)
        (reward ⟨{first, second}, by simp⟩ second) (firstLaw true).toReal := by
  rw [root_swap hne, rootQuit_first reward tail hne.symm]
  simp only [Finset.pair_comm second first]

theorem rootContinue_second (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {first second : ι} (hne : first ≠ second)
    (firstLaw secondLaw : PMF Bool) :
    quittingRootContinuePayoff reward tail (root first second firstLaw secondLaw) second =
      (firstLaw true).toReal * reward (quittingSingletonTerminal first) second +
        (1 - (firstLaw true).toReal) * tail second := by
  rw [root_swap hne, rootContinue_first reward tail hne.symm]

theorem rootContinue_outside (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {first second who : ι} (hne : first ≠ second)
    (hfirst : who ≠ first) (hsecond : who ≠ second) (firstLaw secondLaw : PMF Bool) :
    quittingRootContinuePayoff reward tail (root first second firstLaw secondLaw) who =
      Math.PairedAffine.bellman
        (reward (quittingSingletonTerminal first) who)
        (reward (quittingSingletonTerminal second) who)
        (reward ⟨{first, second}, by simp⟩ who)
        (firstLaw true).toReal (secondLaw true).toReal (tail who) := by
  have hupdate : Function.update (root first second firstLaw secondLaw) who (PMF.pure false) =
      root first second firstLaw secondLaw := by
    apply Function.update_eq_self_iff.mpr
    simp [root, hfirst, hsecond]
  change quittingRootSuccessorPayoff reward tail
    (Function.update (root first second firstLaw secondLaw) who (PMF.pure false)) who = _
  rw [hupdate, rootSuccessor_eq_bellman reward tail hne]

theorem payoff_action_quit (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {first second : ι} (hne : first ≠ second)
    (a b : Bool) (who : ι) :
    quittingRootPayoff reward tail (Function.update (action first second a b) who true) who =
      if a then
        if b then reward ⟨{who, first, second}, by simp⟩ who
        else reward ⟨{who, first}, by simp⟩ who
      else if b then reward ⟨{who, second}, by simp⟩ who
        else reward (quittingSingletonTerminal who) who := by
  unfold quittingRootPayoff
  rw [quittingQuitters_update_true_of_apply_false, quitters_action hne]
  cases a <;> cases b <;> simp [quittingSingletonTerminal]

/-- The pure-Quit endpoint of any recipient, with all joining rewards retained. -/
theorem rootQuit_eq_bellman (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {first second : ι} (hne : first ≠ second)
    (firstLaw secondLaw : PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward tail (root first second firstLaw secondLaw) who =
      Math.PairedAffine.bellman
        (reward ⟨{who, first}, by simp⟩ who)
        (reward ⟨{who, second}, by simp⟩ who)
        (reward ⟨{who, first, second}, by simp⟩ who)
        (firstLaw true).toReal (secondLaw true).toReal
        (reward (quittingSingletonTerminal who) who) := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [← pmfPi_bind_update_pure, expect_bind]
  simp only [expect_pure]
  rw [expect_root]
  simp only [payoff_action_quit reward tail hne, Bool.false_eq_true, if_false, if_true]
  unfold Math.PairedAffine.bellman Math.PairedAffine.contribution
  ring

theorem rootContinue_sub_quit_ge_of_quiet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second who : ι} (hne : first ≠ second) (hfirst : who ≠ first)
    (hsecond : who ≠ second) (firstLaw secondLaw : PMF Bool)
    (hs : reward (quittingSingletonTerminal who) who ≤ 11 / 10)
    (hpassive : Math.PairedAffine.PassiveBounds
      (reward (quittingSingletonTerminal first) who)
      (reward (quittingSingletonTerminal second) who) (reward ⟨{first, second}, by simp⟩ who))
    (hjoinFirst : reward ⟨{who, first}, by simp⟩ who ≤
      reward (quittingSingletonTerminal who) who + 1 / 50)
    (hjoinSecond : reward ⟨{who, second}, by simp⟩ who ≤
      reward (quittingSingletonTerminal who) who + 1 / 50)
    (hjoinBoth : reward ⟨{who, first, second}, by simp⟩ who ≤
      reward (quittingSingletonTerminal who) who + 1 / 50)
    (hfirstLaw : (firstLaw true).toReal ≤ 1 / 2)
    (hsecondLaw : (secondLaw true).toReal ≤ 1 / 2)
    (htail : reward (quittingSingletonTerminal who) who ≤ tail who) :
    17 / 150 * Math.PairedAffine.absorption (firstLaw true).toReal (secondLaw true).toReal ≤
      quittingRootContinuePayoff reward tail (root first second firstLaw secondLaw) who -
        quittingRootQuitPayoff reward tail (root first second firstLaw secondLaw) who := by
  rw [rootContinue_outside reward tail hne hfirst hsecond, rootQuit_eq_bellman reward tail hne]
  exact Math.PairedAffine.quiet_gap_ge hs hpassive hjoinFirst hjoinSecond hjoinBoth
    ⟨ENNReal.toReal_nonneg, hfirstLaw⟩ ⟨ENNReal.toReal_nonneg, hsecondLaw⟩ htail

theorem continueMass_root {first second : ι} (hne : first ≠ second)
    (firstLaw secondLaw : PMF Bool) :
    quittingStationaryContinueMass (root first second firstLaw secondLaw) =
      (1 - (firstLaw true).toReal) * (1 - (secondLaw true).toReal) := by
  have h := rootSuccessor_eq_bellman (fun _ => (0 : Payoff ι)) (fun _ => 1)
    hne firstLaw secondLaw first
  change quittingRootExpectedPayoff _ _ _ _ = _ at h
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add] at h
  have hz : quittingRootAbsorbingContribution (fun _ => (0 : Payoff ι))
      (root first second firstLaw secondLaw) first = 0 := by
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff quittingRootPayoff
    simp
  simpa [hz, Math.PairedAffine.bellman, Math.PairedAffine.contribution] using h

theorem absorptionMass_root {first second : ι} (hne : first ≠ second)
    (firstLaw secondLaw : PMF Bool) :
    quittingRootAbsorptionMass (root first second firstLaw secondLaw) =
      Math.PairedAffine.absorption (firstLaw true).toReal (secondLaw true).toReal := by
  rw [quittingRootAbsorptionMass, continueMass_root hne,
    Math.PairedAffine.absorption_eq_one_sub]

end GameTheory.PairedCycle
