import UniformEquilibrium.Quitting.Terminal.TerminalAffineReward
import UniformEquilibrium.Quitting.Paths.ProfileNeverMass
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPositiveSingletonQuietExtension

/-! # Terminal-only omitted-Never correction

Only the outsider's nonempty terminal reward row is translated. Never remains
zero. Actual behavioral strategies are retained; this is not strategic
equivalence of arbitrary profiles. The correction is the actual joint-Never
mass, and positive singleton charging below is terminal-only.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Subtract an amount only from the outsider's nonempty terminal rewards. -/
def withdrawalOutsideTerminalShift
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ :=
  quittingPlayerwiseAffineReward reward (fun _ => 1)
    (fun who => match who with | none => -excess | some _ => 0)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem withdrawalOutsideTerminalShift_none
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (A : {A : Finset (Option ι) // A.Nonempty}) :
    withdrawalOutsideTerminalShift reward excess A none = reward A none - excess := by
  simp only [withdrawalOutsideTerminalShift, quittingPlayerwiseAffineReward,
    one_mul, sub_eq_add_neg]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem withdrawalOutsideTerminalShift_some
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (A : {A : Finset (Option ι) // A.Nonempty}) (who : ι) :
    withdrawalOutsideTerminalShift reward excess A (some who) = reward A (some who) := by
  simp only [withdrawalOutsideTerminalShift, quittingPlayerwiseAffineReward,
    one_mul, add_zero]

omit [DecidableEq ι] in
/-- Exact absorption correction for the same actual behavioral profile. -/
theorem quittingTerminalPayoff_withdrawalOutsideTerminalShift_none
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff (withdrawalOutsideTerminalShift reward excess) profile none =
      quittingTerminalPayoff reward profile none -
        excess * (1 - quittingLiveMassLimit reward profile) := by
  have h := quittingTerminalPayoff_playerwiseAffine reward (fun _ => 1)
    (fun who => match who with | none => -excess | some _ => 0) profile none
  simpa only [withdrawalOutsideTerminalShift, one_mul, neg_mul,
    sub_eq_add_neg] using h

omit [DecidableEq ι] in
/-- Every child's payoff is literally unchanged, including under deviations. -/
theorem quittingTerminalPayoff_withdrawalOutsideTerminalShift_some
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff (withdrawalOutsideTerminalShift reward excess) profile (some who) =
      quittingTerminalPayoff reward profile (some who) := by
  have h := quittingTerminalPayoff_playerwiseAffine reward (fun _ => 1)
    (fun who => match who with | none => -excess | some _ => 0) profile (some who)
  simpa only [withdrawalOutsideTerminalShift, one_mul, zero_mul, add_zero] using h

/-- The complete behavioral cap of every child is unchanged. -/
theorem quittingBehaviorDeviationPayoffCap_withdrawalOutsideTerminalShift_some
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingBehaviorDeviationPayoffCap (withdrawalOutsideTerminalShift reward excess)
        profile (some who) = quittingBehaviorDeviationPayoffCap reward profile (some who) := by
  unfold quittingBehaviorDeviationPayoffCap
  congr 1
  ext value
  simp only [Set.mem_range]
  constructor <;> rintro ⟨deviation, rfl⟩ <;> refine ⟨deviation, ?_⟩
  · exact (quittingTerminalPayoff_withdrawalOutsideTerminalShift_some
      reward excess _ who).symm
  · exact quittingTerminalPayoff_withdrawalOutsideTerminalShift_some reward excess _ who

/-- Row translation costs at most excess times the baseline Never mass,
not excess times a preemption probability. No response cap is assumed. -/
theorem withdrawalOutsideTerminalDebt_le_shiftedDebt_add_neverMass
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (hexcess : 0 ≤ excess)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward profile none -
        quittingTerminalPayoff reward profile none ≤
      quittingBehaviorDeviationPayoffCap (withdrawalOutsideTerminalShift reward excess)
          profile none -
        quittingTerminalPayoff (withdrawalOutsideTerminalShift reward excess) profile none +
      excess * quittingLiveMassLimit reward profile := by
  have hcap : quittingBehaviorDeviationPayoffCap reward profile none ≤
      quittingBehaviorDeviationPayoffCap (withdrawalOutsideTerminalShift reward excess)
        profile none + excess := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply quittingBestReplyValue_le
    intro deviation
    have h := le_quittingBestReplyValue (withdrawalOutsideTerminalShift reward excess)
      profile none deviation
    rw [← quittingBehaviorDeviationPayoffCap_eq_bestReplyValue
      (withdrawalOutsideTerminalShift reward excess) profile none] at h
    change quittingTerminalPayoff (withdrawalOutsideTerminalShift reward excess)
      (Function.update profile none deviation) none ≤
        quittingBehaviorDeviationPayoffCap (withdrawalOutsideTerminalShift reward excess)
          profile none at h
    have hshift := quittingTerminalPayoff_withdrawalOutsideTerminalShift_none
      reward excess (Function.update profile none deviation)
    have hbound := hshift.symm.trans_le h
    have hmass := mul_nonneg hexcess
      (quittingLiveMassLimit_nonneg reward (Function.update profile none deviation))
    nlinarith [hbound]
  rw [quittingTerminalPayoff_withdrawalOutsideTerminalShift_none]
  linarith

/-- The actual Never mass of a quiet lift is the child product's joint Never. -/
theorem quittingLiveMassLimit_quietLift_eq_childJointNever
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    quittingLiveMassLimit reward
        (quittingLiftDeletedProfile reward (· = none) childProfile) =
      ∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal := by
  let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
  have h := quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none lifted
  change quittingLiveMassLimit reward lifted =
    ∏ who, (quittingBehaviorStoppingLaws reward lifted who none).toReal at h
  rw [quittingBehaviorStoppingLaws_liftDeletedProfile_eq_quiet,
    Fintype.prod_option] at h
  simpa only [quietParentStoppingLaws, PMF.pure_apply_self, ENNReal.toReal_one,
    one_mul] using h

omit [Fintype ι] [DecidableEq ι] in
/-- The child reward table itself is unchanged, not merely its value. -/
theorem quittingDeleteReward_withdrawalOutsideTerminalShift
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) :
    quittingDeleteReward (withdrawalOutsideTerminalShift reward excess) (· = none) =
      quittingDeleteReward reward (· = none) := by
  funext A who
  change withdrawalOutsideTerminalShift reward excess _ who.1 = reward _ who.1
  rcases who with ⟨who, hwho⟩
  cases who with
  | none => exact False.elim (hwho rfl)
  | some i => exact withdrawalOutsideTerminalShift_some reward excess _ i

omit [DecidableEq ι] in
/-- The literal quiet policy is unchanged. Only its outsider terminal rewards
were changed, so no replacement behavioral strategy is chosen. -/
theorem quittingLiftDeletedProfile_withdrawalOutsideTerminalShift
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    quittingLiftDeletedProfile (withdrawalOutsideTerminalShift reward excess)
        (· = none) childProfile = quittingLiftDeletedProfile reward (· = none) childProfile := by
  unfold quittingLiftDeletedProfile quittingInfinitePathProfile
  rw [quittingDeleteReward_withdrawalOutsideTerminalShift]
  exact QuittingLCPClassification.quittingRootSequenceProfile_congr_reward _ _ _ _

/-- A nonnegative residual can be charged to any strictly positive child
singleton using the actual joint-Never debt inequality. -/
theorem withdrawalNeverResidual_le_pivotDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (pivot : ι) (excess : ℝ) (hexcess : 0 ≤ excess)
    (hpivot : 0 < reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩
      (some pivot)) :
    excess * (∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal) ≤
      (excess / reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)) *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some pivot, Option.some_ne_none pivot⟩ -
          quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
            ⟨some pivot, Option.some_ne_none pivot⟩) := by
  let singleton := reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)
  calc
    _ = (excess / singleton) *
        ((∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal) * singleton) := by
      field_simp [singleton, ne_of_gt hpivot]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (quietOutsiderChildJointNever_mul_singleton_le_childDebt reward childProfile pivot)
      (div_nonneg hexcess hpivot.le)

end GameTheory
