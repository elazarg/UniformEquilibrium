import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockChildDeletionAdapter
import UniformEquilibrium.Quitting.Terminal.SingletonJointNeverDebt
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalNashLift

/-! # Terminal capped-clock extension from a positive child singleton -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The future and join rows of a capped-clock certificate, without its
joint-Never row. -/
structure CappedClockParentFutureJoinCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) where
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  future_row : ∀ A (hA : A.Nonempty),
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, weight i *
        (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i))
  join_row : ∀ A (hA : A.Nonempty),
    reward ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, weight i *
        (reward ⟨cappedClockChildCoalition (insert i A),
            cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i))

/-- The nonnegative amount by which the omitted joint-Never row can fail. -/
def cappedClockNeverExcess
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentFutureJoinCertificate reward) : ℝ :=
  max (reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
    ∑ i, certificate.weight i *
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)) 0

omit [Nonempty ι] in
theorem cappedClockNeverExcess_nonneg
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentFutureJoinCertificate reward) :
    0 ≤ cappedClockNeverExcess reward certificate := by
  exact le_max_right _ _

/-- Package F/J and the exact positive-part residual into the shared slack
certificate consumed by the pointwise, expectation, and full-cap owners. -/
def CappedClockParentFutureJoinCertificate.toSlack
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : CappedClockParentFutureJoinCertificate reward) :
    CappedClockParentRewardSlackCertificate reward where
  weight := certificate.weight
  weight_nonneg := certificate.weight_nonneg
  neverSlack := cappedClockNeverExcess reward certificate
  neverSlack_nonneg := cappedClockNeverExcess_nonneg reward certificate
  never_row := by
    unfold cappedClockNeverExcess
    have h := le_max_left
      (reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        ∑ i, certificate.weight i *
          reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)) 0
    linarith
  future_row := certificate.future_row
  join_row := certificate.join_row

/-- The shared actual quiet-lift slack theorem specialized to the precise
positive-part residual of an F/J certificate. -/
theorem quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_neverExcess
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentFutureJoinCertificate reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      (∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩)) +
      cappedClockNeverExcess reward certificate *
        ∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal := by
  simpa [CappedClockParentFutureJoinCertificate.toSlack] using
    quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack
      reward certificate.toSlack childProfile

omit [Nonempty ι] in
/-- A child singleton charges the actual child joint-Never mass to that
child's unrestricted terminal deviation debt. -/
theorem quietOutsiderChildJointNever_mul_singleton_le_childDebt
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (pivot : ι) :
    (∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal) *
        reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot) ≤
      quittingBehaviorDeviationPayoffCap
          (quittingDeleteReward reward (· = none)) childProfile
            ⟨some pivot, Option.some_ne_none pivot⟩ -
        quittingTerminalPayoff
          (quittingDeleteReward reward (· = none)) childProfile
            ⟨some pivot, Option.some_ne_none pivot⟩ := by
  let childLaws := quietOutsiderChildLaws reward childProfile
  let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
  have hlaws : quittingBehaviorStoppingLaws reward lifted =
      quietParentStoppingLaws childLaws := by
    exact quittingBehaviorStoppingLaws_liftDeletedProfile_eq_quiet
      reward childProfile
  have hproduct :
      (∏ player, (quietParentStoppingLaws childLaws player none).toReal) =
        ∏ i, (childLaws i none).toReal := by
    rw [Fintype.prod_option]
    simp [quietParentStoppingLaws]
  have hpivot := prod_stoppingLaw_none_mul_singleton_le_terminalDebt
    reward lifted (some pivot)
  change (∏ player,
      (quittingBehaviorStoppingLaws reward lifted player none).toReal) *
        reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot) ≤
      quittingTerminalDeviationDebt reward lifted (some pivot) at hpivot
  rw [hlaws, hproduct] at hpivot
  have hpivot' :
      (∏ i, (childLaws i none).toReal) *
          reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot) ≤
        quittingBehaviorDeviationPayoffCap reward lifted (some pivot) -
          quittingTerminalPayoff reward lifted (some pivot) := by
    simpa [quittingTerminalDeviationDebt,
      quittingContinuationBestResponseValue,
      quittingBehaviorDeviationPayoffCap] using hpivot
  rw [quittingBehaviorDeviationDebt_liftDeletedProfile reward
    (· = none) childProfile ⟨some pivot, Option.some_ne_none pivot⟩] at hpivot'
  exact hpivot'

/-- A positive child singleton converts the joint-Never correction into one
additional multiple of the pivot child's actual debt. -/
theorem quietLift_outsideDebt_le_of_positiveSingleton
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentFutureJoinCertificate reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (pivot : ι)
    (hpivot : 0 <
      reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      (∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩)) +
      (cappedClockNeverExcess reward certificate /
          reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)) *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some pivot, Option.some_ne_none pivot⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some pivot, Option.some_ne_none pivot⟩) := by
  dsimp only
  let jointNever :=
    ∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal
  let singleton :=
    reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)
  let pivotDebt :=
    quittingBehaviorDeviationPayoffCap
        (quittingDeleteReward reward (· = none)) childProfile
          ⟨some pivot, Option.some_ne_none pivot⟩ -
      quittingTerminalPayoff
        (quittingDeleteReward reward (· = none)) childProfile
          ⟨some pivot, Option.some_ne_none pivot⟩
  have hrelaxed :=
    quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_neverExcess
      reward certificate childProfile
  have hcharge : jointNever * singleton ≤ pivotDebt := by
    exact quietOutsiderChildJointNever_mul_singleton_le_childDebt
      reward childProfile pivot
  have hcoefficient :
      0 ≤ cappedClockNeverExcess reward certificate / singleton :=
    div_nonneg (cappedClockNeverExcess_nonneg reward certificate) hpivot.le
  have hcorrection : cappedClockNeverExcess reward certificate * jointNever ≤
      (cappedClockNeverExcess reward certificate / singleton) * pivotDebt := by
    calc
      cappedClockNeverExcess reward certificate * jointNever =
          (cappedClockNeverExcess reward certificate / singleton) *
            (jointNever * singleton) := by
        field_simp [singleton, ne_of_gt hpivot]
      _ ≤ (cappedClockNeverExcess reward certificate / singleton) * pivotDebt :=
        mul_le_mul_of_nonneg_left hcharge hcoefficient
  exact hrelaxed.trans (by
    simpa only [add_comm] using add_le_add_right hcorrection
      (∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩)))

/-- The positive-singleton F/J criterion lifts every child terminal
approximate equilibrium with a fixed reward-table multiplier. -/
theorem isεAsymptoticNash_quietLift_of_cappedClockPositiveSingleton
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentFutureJoinCertificate reward)
    (pivot : ι)
    (hpivot : 0 <
      reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot))
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (hnash : (quittingGame
      (quittingDeleteReward reward (· = none))).IsεAsymptoticNash
        (quittingTerminalPayoff (quittingDeleteReward reward (· = none)))
        error profile) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (max 1 ((∑ i, certificate.weight i) +
        cappedClockNeverExcess reward certificate /
          reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)) *
        error)
      (quittingLiftDeletedProfile reward (· = none) profile) := by
  let lifted := quittingLiftDeletedProfile reward (· = none) profile
  let singleton :=
    reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)
  let correctionWeight := cappedClockNeverExcess reward certificate / singleton
  let totalWeight := (∑ i, certificate.weight i) + correctionWeight
  have hcorrectionWeight : 0 ≤ correctionWeight :=
    div_nonneg (cappedClockNeverExcess_nonneg reward certificate) hpivot.le
  have hchildDebt (i : ι) :
      quittingBehaviorDeviationPayoffCap
          (quittingDeleteReward reward (· = none)) profile
            ⟨some i, Option.some_ne_none i⟩ -
        quittingTerminalPayoff
          (quittingDeleteReward reward (· = none)) profile
            ⟨some i, Option.some_ne_none i⟩ ≤ error := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply sub_le_iff_le_add.mpr
    apply quittingBestReplyValue_le
    intro deviation
    have h := hnash ⟨some i, Option.some_ne_none i⟩ deviation
    linarith
  have houtsideDebt :
      quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
          max 1 totalWeight * error := by
    calc
      quittingBehaviorDeviationPayoffCap reward lifted none -
          quittingTerminalPayoff reward lifted none ≤
        (∑ i, certificate.weight i *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward (· = none)) profile
                ⟨some i, Option.some_ne_none i⟩ -
            quittingTerminalPayoff
              (quittingDeleteReward reward (· = none)) profile
                ⟨some i, Option.some_ne_none i⟩)) +
          correctionWeight *
            (quittingBehaviorDeviationPayoffCap
                (quittingDeleteReward reward (· = none)) profile
                  ⟨some pivot, Option.some_ne_none pivot⟩ -
              quittingTerminalPayoff
                (quittingDeleteReward reward (· = none)) profile
                  ⟨some pivot, Option.some_ne_none pivot⟩) :=
        quietLift_outsideDebt_le_of_positiveSingleton
          reward certificate profile pivot hpivot
      _ ≤ (∑ i, certificate.weight i * error) +
          correctionWeight * error := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (hchildDebt i) (certificate.weight_nonneg i)
        · exact mul_le_mul_of_nonneg_left
            (hchildDebt pivot) hcorrectionWeight
      _ = totalWeight * error := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ max 1 totalWeight * error :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) herror
  intro who deviation
  have hdeviation := le_quittingBestReplyValue reward lifted who deviation
  change quittingTerminalPayoff reward lifted who +
      max 1 totalWeight * error ≥ _
  cases who with
  | none =>
      rw [← quittingBehaviorDeviationPayoffCap_eq_bestReplyValue] at hdeviation
      linarith
  | some i =>
      have hsurvivor :
          quittingBehaviorDeviationPayoffCap reward lifted (some i) -
            quittingTerminalPayoff reward lifted (some i) ≤ error := by
        simpa only [lifted] using
          (quittingBehaviorDeviationDebt_liftDeletedProfile reward
            (· = none) profile ⟨some i, Option.some_ne_none i⟩).trans_le
              (hchildDebt i)
      rw [← quittingBehaviorDeviationPayoffCap_eq_bestReplyValue] at hdeviation
      have herr : error ≤ max 1 totalWeight * error := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left 1 totalWeight) herror
      linarith

/-- Every specified child uniform-equilibrium target extends under the raw
terminal F/J criterion and one positive child own singleton. -/
theorem exists_uniformEquilibriumPayoff_eq_some_of_cappedClockPositiveSingleton
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentFutureJoinCertificate reward)
    (pivot : ι)
    (hpivot : 0 <
      reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot))
    (target : Payoff {who : Option ι // who ≠ none})
    (htarget : (quittingGame
      (quittingDeleteReward reward (· = none))).IsUniformEquilibriumPayoff
        none target) :
    ∃ payoff : Payoff (Option ι),
      (∀ i, payoff (some i) = target ⟨some i, Option.some_ne_none i⟩) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, hsurvivor, huniform⟩ :=
    exists_uniformEquilibriumPayoff_eq_on_image_of_terminalNash_lift
      reward (quittingDeleteReward reward (· = none))
      (fun who => who.1)
      (quittingLiftDeletedProfile reward (· = none))
      (max 1 ((∑ i, certificate.weight i) +
        cappedClockNeverExcess reward certificate /
          reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)))
      (fun profile who =>
        quittingTerminalPayoff_liftDeletedProfile reward (· = none) profile who)
      (fun herror profile hnash =>
        isεAsymptoticNash_quietLift_of_cappedClockPositiveSingleton
          reward certificate pivot hpivot herror profile hnash)
      target htarget
  exact ⟨payoff, fun i => hsurvivor ⟨some i, Option.some_ne_none i⟩, huniform⟩

end GameTheory
