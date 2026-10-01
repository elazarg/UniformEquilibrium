import UniformEquilibrium.Quitting.Examples.PatientWithdrawalDiscountedBoundary
import UniformEquilibrium.Quitting.Paths.DiscountedBehavioralCap

/-! # The patient boundary example for actual normalized discounted stage payoffs

The same literal reward table, child profile and canonical quiet lift have
strictly larger outsider discounted regret than the patient weighted child
regret for every 0<d<1. Every cap covers complete behavioral replacements.
The patient terminal certificate is unchanged; this is not a terminal
protection failure, a no-UE theorem, or an all-evaluation guarantee.
-/

noncomputable section

namespace GameTheory.PatientWithdrawalDiscountedStageBoundary

open scoped BigOperators
open PatientWithdrawalFiniteHorizonBoundary

private local instance : Nonempty Survivor := ⟨⟨some 0, by simp⟩⟩

/-- Exact full behavioral discounted caps of the same actual quiet lifted profile. -/
theorem discounted_stage_caps (discount : ℝ) (hdiscount : 0 < discount)
    (hdiscountOne : discount < 1) :
    quittingDiscountedDeviationPayoffCap reward discount liftedProfile (some 0) =
        max discount (2 * discount ^ 2) ∧
      quittingDiscountedDeviationPayoffCap reward discount liftedProfile none = discount := by
  simp_rw [quittingDiscountedDeviationPayoffCap_eq_behaviorEvaluatedCap
    reward discount hdiscount.le hdiscountOne]
  exact PatientWithdrawalDiscountedBoundary.discounted_caps discount hdiscount hdiscountOne

/-- Exact canonical stochastic discounted values: child zero d² and outsider zero. -/
theorem discounted_stage_payoffs (discount : ℝ) (hdiscount : 0 ≤ discount)
    (hdiscountOne : discount < 1) :
    (quittingGame reward).discountedPayoff discount liftedProfile none (some 0) = discount ^ 2 ∧
      (quittingGame reward).discountedPayoff discount liftedProfile none none = 0 := by
  simp_rw [quittingDiscountedPayoff_eq_behaviorEvaluatedPayoff
    reward discount hdiscount hdiscountOne]
  exact PatientWithdrawalDiscountedBoundary.discounted_payoffs discount

/-- The actual deleted-child discounted debt is the printed maximum. -/
theorem child_discounted_stage_debt (discount : ℝ) (hdiscount : 0 < discount)
    (hdiscountOne : discount < 1) :
    quittingDiscountedDeviationPayoffCap (quittingDeleteReward reward (· = none))
        discount childProfile ⟨some 0, by simp⟩ -
      (quittingGame (quittingDeleteReward reward (· = none))).discountedPayoff
        discount childProfile none ⟨some 0, by simp⟩ =
      max (discount - discount ^ 2) (discount ^ 2) := by
  rw [quittingDiscountedDeviationDebt_eq_behaviorEvaluatedDebt
    (quittingDeleteReward reward (· = none)) discount hdiscount.le hdiscountOne]
  exact PatientWithdrawalDiscountedBoundary.child_discounted_debt
    discount hdiscount hdiscountOne

/-- Literal normalized discounted stage-series failure, not merely a clock surrogate. -/
theorem patient_discounted_stage_bound_fails
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscountOne : discount < 1) :
    (∑ i : Child, (certificate.advanceWeight i + certificate.withdrawalWeight i) *
      (quittingDiscountedDeviationPayoffCap (quittingDeleteReward reward (· = none))
          discount childProfile ⟨some i, Option.some_ne_none i⟩ -
        (quittingGame (quittingDeleteReward reward (· = none))).discountedPayoff
          discount childProfile none ⟨some i, Option.some_ne_none i⟩)) <
      quittingDiscountedDeviationPayoffCap reward discount liftedProfile none -
        (quittingGame reward).discountedPayoff discount liftedProfile none none := by
  simp_rw [quittingDiscountedDeviationDebt_eq_behaviorEvaluatedDebt
    (quittingDeleteReward reward (· = none)) discount hdiscount.le hdiscountOne,
    quittingDiscountedDeviationDebt_eq_behaviorEvaluatedDebt
      reward discount hdiscount.le hdiscountOne]
  exact PatientWithdrawalDiscountedBoundary.patient_discounted_bound_fails
    discount hdiscount hdiscountOne

end GameTheory.PatientWithdrawalDiscountedStageBoundary
