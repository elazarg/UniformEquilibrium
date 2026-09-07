import MathUE.Probability.DiscreteHazardQuitZeroInstallation
import UniformEquilibrium.Diagnostics.Quitting.CapResponseSegmentCollar
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization
import UniformEquilibrium.Quitting.Stationary.Root

/-! # Literal stationary Quit-now segments retain their original suffix -/

noncomputable section

namespace GameTheory

open Math.Probability Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Change only the owner's first marginal by privately mixing in Quit0. -/
def quittingStationaryQuitNowSegmentRoot
    (root : ι → PMF Bool) (owner : ι) (parameter : Set.Icc (0 : ℝ) 1) : ι → PMF Bool :=
  Function.update root owner
    (BooleanHazard.installQuitZero (fun _ => root owner)
      parameter.val parameter.property.1 parameter.property.2 0)

/-- An actual realizer of the stationary Quit0 installation segment which
retains the original stationary suffix even at null continuation histories. -/
def quittingStationaryQuitNowSegment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (parameter : Set.Icc (0 : ℝ) 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (quittingStationaryQuitNowSegmentRoot root owner parameter)
    (quittingStationaryProfile reward root)

theorem quittingStationaryQuitNowSegment_opponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {owner who : ι} (hne : who ≠ owner)
    (parameter : Set.Icc (0 : ℝ) 1) :
    quittingStationaryQuitNowSegment reward root owner parameter who =
      quittingStationaryProfile reward root who := by
  funext time history
  cases time with
  | zero => exact Function.update_of_ne hne _ _
  | succ time => rfl

/-- The moved coordinate has exactly the complete stopping law of the
canonical private law mixture, without a positive-survival assumption. -/
theorem quittingStationaryQuitNowSegment_ownerStoppingLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (parameter : Set.Icc (0 : ℝ) 1) :
    quittingBehaviorStoppingLaw reward
        (quittingStationaryQuitNowSegment reward root owner parameter owner) =
      quittingBehaviorStoppingLaw reward
        (quittingCapResponseSegment reward (quittingStationaryProfile reward root) owner
          (quittingPureTimeBehaviorStrategy reward owner (some 0)) parameter owner) := by
  have hinstalled : quittingBehaviorLiveHazard reward
      (quittingStationaryQuitNowSegment reward root owner parameter owner) =
        BooleanHazard.installQuitZero (fun _ => root owner)
          parameter.val parameter.property.1 parameter.property.2 := by
    funext time
    cases time with
    | zero => exact Function.update_self _ _ _
    | succ time => rfl
  unfold quittingBehaviorStoppingLaw quittingHazardStoppingLaw
  rw [hinstalled]
  simp only [quittingCapResponseSegment, Function.update_self,
    quittingBehaviorLiveHazard_stoppingLawMixture]
  change _ = (BooleanHazard.convexMix (fun _ => root owner)
    (quittingBehaviorLiveHazard reward
      (quittingPureTimeBehaviorStrategy reward owner (some 0)))
    parameter.val parameter.property.1 parameter.property.2).toScalar.stoppingLaw
  exact BooleanHazard.installQuitZero_stoppingLaw_eq_convexMix
    _ _ _ _ _ rfl

/-- Full payoff/cap semantics agree with the canonical cap-response segment;
the literal realization is chosen to preserve the stationary tail. -/
theorem quittingStationaryQuitNowSegment_semanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (parameter : Set.Icc (0 : ℝ) 1) :
    quittingTerminalSemanticPair reward
        (quittingStationaryQuitNowSegment reward root owner parameter) =
      quittingTerminalSemanticPair reward
        (quittingCapResponseSegment reward (quittingStationaryProfile reward root) owner
          (quittingPureTimeBehaviorStrategy reward owner (some 0)) parameter) := by
  rw [quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile reward
      (quittingStationaryQuitNowSegment reward root owner parameter),
    quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile reward
      (quittingCapResponseSegment reward (quittingStationaryProfile reward root) owner
        (quittingPureTimeBehaviorStrategy reward owner (some 0)) parameter)]
  congr 2
  funext who
  apply congrArg Math.Probability.CompactStoppingLaw.ofPMF
  by_cases hwho : who = owner
  · subst who
    exact quittingStationaryQuitNowSegment_ownerStoppingLaw reward root owner parameter
  · rw [quittingStationaryQuitNowSegment_opponents reward root hwho parameter]
    simp only [quittingCapResponseSegment, Function.update_of_ne hwho]

/-- The complete surviving suffix is the original stationary profile,
including at a sure-Quit boundary and at full cap installation. -/
theorem quittingStationaryQuitNowSegment_suffix_one_eq_source
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (parameter : Set.Icc (0 : ℝ) 1) :
    quittingAllContinueProfileSpine reward
        (quittingStationaryQuitNowSegment reward root owner parameter) 1 =
      quittingStationaryProfile reward root := by
  unfold quittingAllContinueProfileSpine quittingProfileAllContinueContinuation
    quittingStationaryQuitNowSegment
  exact shiftProfile_quittingRootThenContinuationProfile reward _ _ _

/-- One additional exact or arbitrary root puts the original stationary
source at the literal exit cut two. No survival premise is needed for identity. -/
theorem prefixed_quittingStationaryQuitNowSegment_suffix_two_eq_source
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root openingRoot : ι → PMF Bool) (owner : ι) (parameter : Set.Icc (0 : ℝ) 1) :
    quittingAllContinueProfileSpine reward
        (quittingRootThenContinuationProfile reward openingRoot
          (quittingStationaryQuitNowSegment reward root owner parameter)) 2 =
      quittingStationaryProfile reward root := by
  change quittingProfileAllContinueContinuation reward
    (quittingProfileAllContinueContinuation reward
      (quittingRootThenContinuationProfile reward openingRoot
        (quittingStationaryQuitNowSegment reward root owner parameter))) = _
  unfold quittingProfileAllContinueContinuation
  rw [shiftProfile_quittingRootThenContinuationProfile]
  exact quittingStationaryQuitNowSegment_suffix_one_eq_source reward root owner parameter

/-- The literal first-row realizer preserves the original owner's complete cap. -/
theorem quittingStationaryQuitNowSegment_ownerCap_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (parameter : Set.Icc (0 : ℝ) 1) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryQuitNowSegment reward root owner parameter) owner =
      quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward root) owner := by
  have hpair := quittingStationaryQuitNowSegment_semanticPair reward root owner parameter
  exact (congrArg (fun pair => pair.2 owner) hpair).trans
    (capResponseSegment_ownerCap_eq reward _ owner _ parameter)

/-- When Quit0 attains the original complete cap, its literal installation
has exactly the same affine owner-debt identity as the stopping-law segment. -/
theorem quittingStationaryQuitNowSegment_ownerDebt_eq_oneSub_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hattains : quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) owner
          (quittingPureTimeBehaviorStrategy reward owner (some 0))) owner =
      quittingContinuationBestResponseValue reward (quittingStationaryProfile reward root) owner)
    (parameter : Set.Icc (0 : ℝ) 1) :
    quittingTerminalDeviationDebt reward
        (quittingStationaryQuitNowSegment reward root owner parameter) owner =
      (1 - parameter.val) * quittingTerminalDeviationDebt reward
        (quittingStationaryProfile reward root) owner := by
  have hpair := quittingStationaryQuitNowSegment_semanticPair reward root owner parameter
  exact (congrArg (fun pair => quittingTerminalSemanticDebt pair owner) hpair).trans
    (capResponseSegment_ownerDebt_eq_oneSub_mul reward _ owner _ hattains parameter)

/-- The segment's first row has at least its installation parameter in total
marginal Quit hazard; this is not a root-Nash assertion. -/
theorem quittingStationaryQuitNowSegmentRoot_hazard_ge
    (root : ι → PMF Bool) (owner : ι) (parameter : Set.Icc (0 : ℝ) 1) :
    parameter.val ≤ ∑ who,
      (quittingStationaryQuitNowSegmentRoot root owner parameter who true).toReal := by
  have howner : parameter.val ≤
      (quittingStationaryQuitNowSegmentRoot root owner parameter owner true).toReal := by
    simp only [quittingStationaryQuitNowSegmentRoot, Function.update_self,
      BooleanHazard.installQuitZero, booleanCoin_true_toReal]
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr parameter.property.2) (stop_nonneg _ _))
  exact howner.trans (Finset.single_le_sum
    (f := fun who =>
      (quittingStationaryQuitNowSegmentRoot root owner parameter who true).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ owner))

end GameTheory
