import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedLaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalProductLaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockExpectationDomination
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedActualPayoffAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedMarginal

/-!
# A shared private mixed-restart payoff core

The restart family is arbitrary in this internal semantic interface. The
evaluated and terminal security producers choose their own actual laws from
raw rewards and delegate product marginals, gain identities, and full-cap
comparison to this common implementation.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Actual averaged gain from withdrawing just the deadline atom into the
reward-table security plan. -/
def deadlineSecurityActualEvaluatedChildGainWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ℕ → PMF (Option ℕ))
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) : ℝ :=
  expect (deadlineSecurityAtomRestartLaw restart
      (times i) deadline)
    (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
      (deadlinePrivateChildClocks times i clock) (some i)) -
    quittingPureClockEvaluatedPayoff reward evaluation (quietParentClocks times) (some i)

/-- The exact max-weight identity applied to the actual evaluated quitting
payoff; the restart term is averaged over the fresh private plan. -/
theorem deadlineSecurityMixedPrivateClockLaw_evaluatedGain_identityWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ℕ → PMF (Option ℕ))
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι)
    (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    max advanceWeight withdrawalWeight *
        (expect (deadlineSecurityMixedPrivateClockLaw
            restart (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal)
          (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
            (deadlinePrivateChildClocks times i clock) (some i)) -
          quittingPureClockEvaluatedPayoff reward evaluation (quietParentClocks times) (some i)) =
      advanceWeight * cappedClockActualEvaluatedChildGain reward evaluation times deadline i +
        withdrawalWeight * deadlineSecurityActualEvaluatedChildGainWithRestart
          reward restart evaluation times deadline i := by
  have hbase : deadlinePrivateChildClocks times i (times i) = quietParentClocks times := by
    funext player
    cases player with
    | none => rfl
    | some j => by_cases h : j = i <;> simp [deadlinePrivateChildClocks, quietParentClocks, h]
  have hcap : deadlinePrivateChildClocks times i (cappedStoppingClock (times i) deadline) =
      cappedChildParentClocks times deadline i := by
    funext player
    cases player with
    | none => rfl
    | some j => by_cases h : j = i <;>
        simp [deadlinePrivateChildClocks, cappedChildParentClocks, h]
  simpa only [hbase, hcap, cappedClockActualEvaluatedChildGain,
    deadlineSecurityActualEvaluatedChildGainWithRestart] using
    deadlineSecurityMixedPrivateClockLaw_gain_identity
      restart (times i) deadline
      advanceWeight withdrawalWeight hadvance hwithdrawal
      (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
        (deadlinePrivateChildClocks times i clock) (some i))
      (fun clock => abs_quittingPureClockEvaluatedPayoff_le
        reward evaluation hnonneg hantitone _ _)

/-- Quiet independent laws with one child replaced by its actual
reward-table-selected security mixture. -/
def deadlineSecurityMixedChildParentStoppingLawsWithRestart
    (restart : ℕ → PMF (Option ℕ))
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    Option ι → PMF (Option ℕ) :=
  Function.update (quietParentStoppingLaws childLaws) (some i)
    (deadlineSecurityMixedPrivateReplacementLaw
      restart (childLaws i) outsideLaw
      advanceWeight withdrawalWeight hadvance hwithdrawal)

/-- The actual private mixture is a legal complete behavioral replacement,
so its evaluated payoff is below the unrestricted behavioral cap. -/
theorem deadlineSecurityMixedChild_payoff_le_behaviorDeviationCapWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ℕ → PMF (Option ℕ))
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    quittingStoppingLawEvaluatedPayoff reward evaluation
        (deadlineSecurityMixedChildParentStoppingLawsWithRestart restart childLaws
          outsideLaw i
          advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) ≤
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) := by
  rw [← quittingBehaviorEvaluatedPayoff_stoppingLawProfile]
  let quietProfile := quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)
  let deviation := quittingStoppingLawBehaviorStrategy reward (some i)
    (deadlineSecurityMixedPrivateReplacementLaw
      restart (childLaws i) outsideLaw
      advanceWeight withdrawalWeight hadvance hwithdrawal)
  have hprofile : quittingStoppingLawProfile reward
      (deadlineSecurityMixedChildParentStoppingLawsWithRestart restart childLaws outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) =
      Function.update quietProfile (some i) deviation := by
    funext player
    by_cases hp : player = some i
    · subst player
      simp [deadlineSecurityMixedChildParentStoppingLawsWithRestart, quietProfile, deviation,
        quittingStoppingLawProfile]
    · simp [deadlineSecurityMixedChildParentStoppingLawsWithRestart, quietProfile, deviation,
        quittingStoppingLawProfile, hp]
  rw [hprofile]
  unfold quittingBehaviorEvaluatedDeviationPayoffCap
  apply le_csSup
    (bddAbove_range_quittingBehaviorEvaluatedPayoff_update reward evaluation
      hnonneg hantitone quietProfile (some i))
  exact ⟨deviation, rfl⟩

end GameTheory

noncomputable section

namespace GameTheory

open _root_.Math Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- Mixing the deadline independently and then changing only the selected
child clock has exactly the legal private replacement product marginal. -/
theorem deadlineSecurityMixedPrivateReplacement_childProductWithRestart
    (restart : ℕ → PMF (Option ℕ))
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    (pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineSecurityMixedPrivateClockLaw
            restart (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => Function.update times i newClock) =
      pmfPi (Function.update childLaws i
        (deadlineSecurityMixedPrivateReplacementLaw
          restart (childLaws i) outsideLaw
          advanceWeight withdrawalWeight hadvance hwithdrawal)) := by
  let kernel : Option ℕ → PMF (Option ℕ) := fun source =>
    outsideLaw.bind fun deadline =>
      deadlineSecurityMixedPrivateClockLaw
        restart source deadline advanceWeight
        withdrawalWeight hadvance hwithdrawal
  have hkernel := pmfPi_bind_privateClockKernel childLaws i kernel
  change (pmfPi childLaws).bind (fun times =>
      outsideLaw.bind fun deadline =>
        (deadlineSecurityMixedPrivateClockLaw
            restart (times i) deadline
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
            restart (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal)
          (fun newClock => Function.update times i newClock)).symm
    _ = _ := hkernel

omit [Nonempty ι] in
/-- The independently mixed private response, embedded in the quiet parent,
has precisely the stopping-law product of the legal one-child replacement. -/
theorem deadlineSecurityMixedPrivateReplacement_parentProductWithRestart
    (restart : ℕ → PMF (Option ℕ))
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    ((pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineSecurityMixedPrivateClockLaw
            restart (times i) deadline
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => Function.update times i newClock)).map
        quietParentClocks =
      pmfPi (deadlineSecurityMixedChildParentStoppingLawsWithRestart restart childLaws
        outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) := by
  rw [deadlineSecurityMixedPrivateReplacement_childProductWithRestart,
    map_pmfPi_child_quiet]
  congr 1
  funext player
  cases player with
  | none => rfl
  | some j =>
      by_cases h : j = i
      · subst j
        simp [deadlineSecurityMixedChildParentStoppingLawsWithRestart,
          quietParentStoppingLaws]
      · simp [deadlineSecurityMixedChildParentStoppingLawsWithRestart,
          quietParentStoppingLaws, h]

omit [Nonempty ι] in
/-- The mixed private response applied to the original independent sample
has precisely the legal quiet-parent replacement marginal. -/
theorem deadlineSecurityMixedPrivateReplacement_parentMarginalWithRestart
    (restart : ℕ → PMF (Option ℕ))
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    (cappedClockIndependentSample childLaws outsideLaw).bind
        (fun sample =>
          (deadlineSecurityMixedPrivateClockLaw
            restart (sample.1 i) sample.2
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => deadlinePrivateChildClocks sample.1 i newClock) =
      pmfPi (deadlineSecurityMixedChildParentStoppingLawsWithRestart restart childLaws
        outsideLaw i
        advanceWeight withdrawalWeight hadvance hwithdrawal) := by
  calc
    _ = ((pmfPi childLaws).bind (fun times =>
        outsideLaw.bind fun deadline =>
          (deadlineSecurityMixedPrivateClockLaw
            restart (times i) deadline
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
            restart (times i) deadline
              advanceWeight withdrawalWeight hadvance hwithdrawal).map f)
          hmaps
    _ = _ := deadlineSecurityMixedPrivateReplacement_parentProductWithRestart restart
      childLaws
      outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal

/-- The actual coupled private response has the evaluated payoff of the
one-child stopping-law product, before comparison with a behavioral cap. -/
theorem deadlineSecurityMixedPrivateReplacement_evaluatedPayoffWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ℕ → PMF (Option ℕ))
    (evaluation : WithTop ℕ → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    _root_.Math.Probability.expect
      ((cappedClockIndependentSample childLaws outsideLaw).bind
        (fun sample =>
          (deadlineSecurityMixedPrivateClockLaw
            restart (sample.1 i) sample.2
            advanceWeight withdrawalWeight hadvance hwithdrawal).map
              fun newClock => deadlinePrivateChildClocks sample.1 i newClock))
        (fun clocks => quittingPureClockEvaluatedPayoff reward evaluation
          clocks (some i)) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (deadlineSecurityMixedChildParentStoppingLawsWithRestart restart childLaws
          outsideLaw i
          advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) := by
  rw [deadlineSecurityMixedPrivateReplacement_parentMarginalWithRestart]
  rfl

/-- Bounded Fubini identifies the conditional private-coin payoff with the
actual evaluated stopping-law payoff of the independent replacement. -/
theorem expect_deadlineSecurityMixedPrivateClockLaw_payoff_eq_stoppingLawWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ℕ → PMF (Option ℕ))
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
            restart (sample.1 i) sample.2
            advanceWeight withdrawalWeight hadvance hwithdrawal)
          (fun newClock => quittingPureClockEvaluatedPayoff reward evaluation
            (deadlinePrivateChildClocks sample.1 i newClock) (some i))) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (deadlineSecurityMixedChildParentStoppingLawsWithRestart restart childLaws
          outsideLaw i
          advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) := by
  let source := cappedClockIndependentSample childLaws outsideLaw
  let kernel (sample : (ι → Option ℕ) × Option ℕ) :=
    (deadlineSecurityMixedPrivateClockLaw
            restart (sample.1 i) sample.2
      advanceWeight withdrawalWeight hadvance hwithdrawal).map
        fun newClock => deadlinePrivateChildClocks sample.1 i newClock
  let payoff (clocks : Option ι → Option ℕ) :=
    quittingPureClockEvaluatedPayoff reward evaluation clocks (some i)
  have hbound (clocks : Option ι → Option ℕ) :
      |payoff clocks| ≤ evaluation 0 * quittingRewardBound reward :=
    abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone clocks (some i)
  rw [← deadlineSecurityMixedPrivateReplacement_evaluatedPayoffWithRestart reward restart evaluation
    childLaws outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal]
  change _root_.Math.Probability.expect source (fun sample =>
    _root_.Math.Probability.expect
      (deadlineSecurityMixedPrivateClockLaw
            restart (sample.1 i) sample.2
        advanceWeight withdrawalWeight hadvance hwithdrawal)
      (fun newClock => payoff
        (deadlinePrivateChildClocks sample.1 i newClock))) =
    _root_.Math.Probability.expect (source.bind kernel) payoff
  rw [_root_.Math.Probability.expect_bind_of_bounded source kernel payoff hbound]
  apply congrArg (_root_.Math.Probability.expect source)
  funext sample
  rw [_root_.Math.Probability.expect_map]

end GameTheory

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem expect_sub_of_abs_bounds {Ω : Type*} (law : PMF Ω)
    (f g : Ω → ℝ) {C D : ℝ}
    (hf : ∀ sample, |f sample| ≤ C)
    (hg : ∀ sample, |g sample| ≤ D) :
    expect law (fun sample => f sample - g sample) =
      expect law f - expect law g := by
  change expect law (fun sample => f sample + -g sample) = _
  rw [expect_add_of_summable]
  · rw [expect_neg]
    ring
  · exact expect_summable_of_bounded law f hf
  · simpa [mul_neg] using (expect_summable_of_bounded law g hg).neg

/-- One legal private mixed response realizes the expectation of the
weighted advance and withdrawal gains, with coefficient `max(a,b)`. -/
theorem deadlineSecurityMixedPrivateReplacement_integratedGainWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ℕ → PMF (Option ℕ))
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (i : ι) (advanceWeight withdrawalWeight : ℝ)
    (hadvance : 0 ≤ advanceWeight) (hwithdrawal : 0 ≤ withdrawalWeight) :
    max advanceWeight withdrawalWeight *
      (quittingStoppingLawEvaluatedPayoff reward evaluation
          (deadlineSecurityMixedChildParentStoppingLawsWithRestart restart childLaws
            outsideLaw i
            advanceWeight withdrawalWeight hadvance hwithdrawal) (some i) -
        quittingStoppingLawEvaluatedPayoff reward evaluation
          (quietParentStoppingLaws childLaws) (some i)) =
      expect (cappedClockIndependentSample childLaws outsideLaw)
        (fun sample => advanceWeight *
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i +
          withdrawalWeight *
            deadlineSecurityActualEvaluatedChildGainWithRestart reward restart evaluation
              sample.1 sample.2 i) := by
  let law := cappedClockIndependentSample childLaws outsideLaw
  let coin (sample : (ι → Option ℕ) × Option ℕ) :=
    deadlineSecurityMixedPrivateClockLaw
      restart (sample.1 i) sample.2
      advanceWeight withdrawalWeight hadvance hwithdrawal
  let mixed (sample : (ι → Option ℕ) × Option ℕ) :=
    expect (coin sample) (fun newClock =>
      quittingPureClockEvaluatedPayoff reward evaluation
        (deadlinePrivateChildClocks sample.1 i newClock) (some i))
  let base (sample : (ι → Option ℕ) × Option ℕ) :=
    quittingPureClockEvaluatedPayoff reward evaluation
      (quietParentClocks sample.1) (some i)
  let bound := evaluation 0 * quittingRewardBound reward
  have hmixedBound (sample : (ι → Option ℕ) × Option ℕ) :
      |mixed sample| ≤ bound := by
    exact abs_expect_le_of_abs_le (coin sample) _ fun newClock =>
      abs_quittingPureClockEvaluatedPayoff_le reward evaluation
        evaluation_nonneg evaluation_antitone
        (deadlinePrivateChildClocks sample.1 i newClock) (some i)
  have hbaseBound (sample : (ι → Option ℕ) × Option ℕ) :
      |base sample| ≤ bound :=
    abs_quittingPureClockEvaluatedPayoff_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (quietParentClocks sample.1) (some i)
  have hpoint : expect law (fun sample =>
      max advanceWeight withdrawalWeight * (mixed sample - base sample)) =
    expect law (fun sample => advanceWeight *
        cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i +
      withdrawalWeight *
        deadlineSecurityActualEvaluatedChildGainWithRestart reward restart evaluation
          sample.1 sample.2 i) := by
    apply congrArg (expect law)
    funext sample
    exact deadlineSecurityMixedPrivateClockLaw_evaluatedGain_identityWithRestart
      reward restart evaluation evaluation_nonneg evaluation_antitone
      sample.1 sample.2 i advanceWeight withdrawalWeight
      hadvance hwithdrawal
  have hlinear : expect law (fun sample =>
      max advanceWeight withdrawalWeight * (mixed sample - base sample)) =
    max advanceWeight withdrawalWeight *
      (expect law mixed - expect law base) := by
    rw [expect_const_mul, expect_sub_of_abs_bounds law mixed base
      hmixedBound hbaseBound]
  calc
    _ = max advanceWeight withdrawalWeight *
        (expect law mixed - expect law base) := by
      rw [expect_deadlineSecurityMixedPrivateClockLaw_payoff_eq_stoppingLawWithRestart
        reward restart evaluation evaluation_nonneg evaluation_antitone childLaws
        outsideLaw i advanceWeight withdrawalWeight hadvance hwithdrawal]
      rw [expect_cappedClockIndependentSample_quiet_eq_stoppingLaw
        reward evaluation childLaws outsideLaw (some i)]
    _ = expect law (fun sample =>
          max advanceWeight withdrawalWeight *
            (mixed sample - base sample)) := hlinear.symm
    _ = _ := hpoint

end GameTheory
