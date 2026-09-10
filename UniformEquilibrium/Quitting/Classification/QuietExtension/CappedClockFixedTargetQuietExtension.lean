import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalNashLift
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockChildDeletionAdapter

/-! # Fixed-target quiet extension from a capped-clock certificate -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A capped-clock certificate lifts every child terminal approximate equilibrium,
with the common error factor given by the larger of one and the total weight. -/
theorem isεAsymptoticNash_quietLift_of_cappedClockCertificate
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentRewardCertificate reward)
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (hnash : (quittingGame
      (quittingDeleteReward reward (· = none))).IsεAsymptoticNash
        (quittingTerminalPayoff (quittingDeleteReward reward (· = none)))
        error profile) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (max 1 (∑ i, certificate.weight i) * error)
      (quittingLiftDeletedProfile reward (· = none) profile) := by
  let lifted := quittingLiftDeletedProfile reward (· = none) profile
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
          max 1 (∑ i, certificate.weight i) * error := by
    calc
      quittingBehaviorDeviationPayoffCap reward lifted none -
          quittingTerminalPayoff reward lifted none ≤
        ∑ i, certificate.weight i *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward (· = none)) profile
                ⟨some i, Option.some_ne_none i⟩ -
            quittingTerminalPayoff
              (quittingDeleteReward reward (· = none)) profile
                ⟨some i, Option.some_ne_none i⟩) :=
        quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt
          reward certificate profile
      _ ≤ ∑ i, certificate.weight i * error := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hchildDebt i) (certificate.weight_nonneg i)
      _ ≤ max 1 (∑ i, certificate.weight i) * error := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) herror
  intro who deviation
  have hdeviation := le_quittingBestReplyValue reward lifted who deviation
  change quittingTerminalPayoff reward lifted who +
      max 1 (∑ i, certificate.weight i) * error ≥ _
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
      have herr : error ≤ max 1 (∑ i, certificate.weight i) * error := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left 1 (∑ i, certificate.weight i)) herror
      linarith

/-- Every specified uniform-equilibrium payoff of the child game extends to
the parent under the capped-clock raw reward certificate, agreeing at every child. -/
theorem exists_uniformEquilibriumPayoff_eq_some_of_cappedClockCertificate
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentRewardCertificate reward)
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
      (max 1 (∑ i, certificate.weight i))
      (fun profile who =>
        quittingTerminalPayoff_liftDeletedProfile reward (· = none) profile who)
      (fun herror profile hnash =>
        isεAsymptoticNash_quietLift_of_cappedClockCertificate
          reward certificate herror profile hnash)
      target htarget
  exact ⟨payoff, fun i => hsurvivor ⟨some i, Option.some_ne_none i⟩, huniform⟩

end GameTheory
