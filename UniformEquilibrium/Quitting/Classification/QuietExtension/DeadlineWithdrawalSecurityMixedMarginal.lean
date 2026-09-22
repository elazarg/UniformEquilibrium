import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedBehavioral
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalProductLaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockExpectationDomination

/-! # Independent product marginal of the actual security mixture -/

noncomputable section

namespace GameTheory

open _root_.Math Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- Mixing the deadline independently and then changing only the selected
child clock has exactly the legal private replacement product marginal. -/
theorem deadlineSecurityMixedPrivateReplacement_childProduct
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    (pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => Function.update times i newClock) =
      pmfPi (Function.update childLaws i
        (deadlineSecurityMixedPrivateReplacementLaw
          (deadlineSecurityEvaluatedRestartFamily reward i) (childLaws i) outsideLaw
          advanceWeight withdrawalWeight hadvance hwithdrawal)) := by
  let kernel : Option ℕ → PMF (Option ℕ) := fun source =>
    outsideLaw.bind fun deadline =>
      deadlineSecurityMixedPrivateClockLaw
        (deadlineSecurityEvaluatedRestartFamily reward i) source deadline advanceWeight
        withdrawalWeight hadvance hwithdrawal
  have hkernel := pmfPi_bind_privateClockKernel childLaws i kernel
  change (pmfPi childLaws).bind (fun times =>
      outsideLaw.bind fun deadline =>
        (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
          advanceWeight withdrawalWeight hadvance hwithdrawal).map
            fun newClock => Function.update times i newClock) =
    pmfPi (Function.update childLaws i ((childLaws i).bind kernel))
  calc
    _ = (pmfPi childLaws).bind (fun times =>
          (kernel (times i)).map fun newClock =>
            Function.update times i newClock) := by
        apply congrArg (PMF.bind (pmfPi childLaws))
        funext times
        exact (PMF.map_bind (p := outsideLaw)
          (fun deadline => deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal)
          (fun newClock => Function.update times i newClock)).symm
    _ = _ := hkernel

omit [Nonempty ι] in
/-- The independently mixed private response, embedded in the quiet parent,
has precisely the stopping-law product of the legal one-child replacement. -/
theorem deadlineSecurityMixedPrivateReplacement_parentProduct
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    ((pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => Function.update times i newClock)).map
        quietParentClocks =
      pmfPi (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) := by
  rw [deadlineSecurityMixedPrivateReplacement_childProduct,
    map_pmfPi_child_quiet]
  congr 1
  funext player
  cases player with
  | none => rfl
  | some j =>
      by_cases h : j = i
      · subst j
        simp [deadlineSecurityMixedChildParentStoppingLaws,
          quietParentStoppingLaws]
      · simp [deadlineSecurityMixedChildParentStoppingLaws,
          quietParentStoppingLaws, h]

omit [Nonempty ι] in
/-- The mixed private response applied to the original independent sample
has precisely the legal quiet-parent replacement marginal. -/
theorem deadlineSecurityMixedPrivateReplacement_parentMarginal
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    (cappedClockIndependentSample childLaws outsideLaw).bind
        (fun sample =>
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (sample.1 i) sample.2
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => deadlinePrivateChildClocks sample.1 i newClock) =
      pmfPi (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) := by
  calc
    _ = ((pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => Function.update times i newClock)).map
          quietParentClocks := by
        unfold cappedClockIndependentSample
        rw [PMF.map_bind, PMF.bind_bind]
        apply congrArg (PMF.bind (pmfPi childLaws))
        funext times
        rw [PMF.bind_map, PMF.map_bind]
        apply congrArg (PMF.bind outsideLaw)
        funext deadline
        have hmaps : (fun newClock =>
            deadlinePrivateChildClocks times i newClock) =
            quietParentClocks ∘ (fun newClock =>
              Function.update times i newClock) := by
          funext newClock player
          cases player with
          | none => rfl
          | some j =>
              by_cases h : j = i <;>
                simp [deadlinePrivateChildClocks,
                  quietParentClocks, Function.update, h]
        simpa only [PMF.map_comp, Function.comp_apply] using congrArg
          (fun f : Option ℕ → (Option ι → Option ℕ) =>
            (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (times i) deadline
              advanceWeight withdrawalWeight hadvance hwithdrawal).map f)
          hmaps
    _ = _ := deadlineSecurityMixedPrivateReplacement_parentProduct reward childLaws
      outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal

/-- The actual coupled private response has the evaluated payoff of the
one-child stopping-law product, before comparison with a behavioral cap. -/
theorem deadlineSecurityMixedPrivateReplacement_evaluatedPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    _root_.Math.Probability.expect
      ((cappedClockIndependentSample childLaws outsideLaw).bind
        (fun sample =>
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (sample.1 i) sample.2
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => deadlinePrivateChildClocks sample.1 i newClock))
        (fun clocks => quittingPureClockEvaluatedPayoff reward evaluation
          clocks (some i)) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
          advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) := by
  rw [deadlineSecurityMixedPrivateReplacement_parentMarginal]
  rfl

/-- Bounded Fubini identifies the conditional private-coin payoff with the
actual evaluated stopping-law payoff of the independent replacement. -/
theorem expect_deadlineSecurityMixedPrivateClockLaw_payoff_eq_stoppingLaw
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    _root_.Math.Probability.expect
        (cappedClockIndependentSample childLaws outsideLaw)
        (fun sample => _root_.Math.Probability.expect
          (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (sample.1 i) sample.2
            advanceWeight withdrawalWeight hadvance hwithdrawal)
          (fun newClock => quittingPureClockEvaluatedPayoff reward evaluation
            (deadlinePrivateChildClocks sample.1 i newClock) (some i))) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (deadlineSecurityMixedChildParentStoppingLaws reward childLaws outsideLaw i
          advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) := by
  let source := cappedClockIndependentSample childLaws outsideLaw
  let kernel (sample : (ι → Option ℕ) × Option ℕ) :=
    (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (sample.1 i) sample.2
      advanceWeight withdrawalWeight hadvance hwithdrawal).map
        fun newClock => deadlinePrivateChildClocks sample.1 i newClock
  let payoff (clocks : Option ι → Option ℕ) :=
    quittingPureClockEvaluatedPayoff reward evaluation clocks (some i)
  have hbound (clocks : Option ι → Option ℕ) :
      |payoff clocks| ≤ evaluation 0 * quittingRewardBound reward :=
    abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone clocks (some i)
  rw [← deadlineSecurityMixedPrivateReplacement_evaluatedPayoff reward evaluation
    childLaws outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal]
  change _root_.Math.Probability.expect source (fun sample =>
    _root_.Math.Probability.expect
      (deadlineSecurityMixedPrivateClockLaw
            (deadlineSecurityEvaluatedRestartFamily reward i) (sample.1 i) sample.2
        advanceWeight withdrawalWeight hadvance hwithdrawal)
      (fun newClock => payoff
        (deadlinePrivateChildClocks sample.1 i newClock))) =
    _root_.Math.Probability.expect (source.bind kernel) payoff
  rw [_root_.Math.Probability.expect_bind_of_bounded source kernel payoff hbound]
  apply congrArg (_root_.Math.Probability.expect source)
  funext sample
  rw [_root_.Math.Probability.expect_map]

end GameTheory
