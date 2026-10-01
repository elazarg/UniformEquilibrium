import UniformEquilibrium.Quitting.Paths.DiscountedStoppingLawPayoff

/-! # Full behavioral normalized discounted response caps

The supremum is over every complete behavioral strategy, not stationary,
pure-time or menu-only replies. The actual normalized stage payoff and its
complete debt equal their absorption-law counterparts for 0<=d<1.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual normalized discounted payoff envelope over complete behavioral replacements. -/
def quittingDiscountedDeviationPayoffCap
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι) (discount : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  sSup (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who =>
    (quittingGame reward).discountedPayoff discount
      (Function.update profile who deviation) none who)

/-- Pointwise actual history payoff identification, with Never and signed rewards retained. -/
theorem quittingDiscountedPayoff_eq_behaviorEvaluatedPayoff
    [Nonempty ι] (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingGame reward).discountedPayoff discount profile none who =
      quittingBehaviorEvaluatedPayoff reward (quittingDiscountedEvaluation discount) profile who :=
  quittingDiscountedPayoff_eq_stoppingLawEvaluatedPayoff
    reward discount hdiscount hdiscountOne profile who

/-- The actual full discounted cap equals the exact complete-law evaluated cap. -/
theorem quittingDiscountedDeviationPayoffCap_eq_behaviorEvaluatedCap
    [Nonempty ι] (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingDiscountedDeviationPayoffCap reward discount profile who =
      quittingBehaviorEvaluatedDeviationPayoffCap reward
        (quittingDiscountedEvaluation discount) profile who := by
  unfold quittingDiscountedDeviationPayoffCap quittingBehaviorEvaluatedDeviationPayoffCap
  apply congrArg sSup
  apply congrArg Set.range
  funext deviation
  exact quittingDiscountedPayoff_update_eq_behaviorEvaluatedPayoff
    reward discount hdiscount hdiscountOne profile who deviation

/-- The unrestricted normalized discounted debt, not only its pure-time restriction. -/
theorem quittingDiscountedDeviationDebt_eq_behaviorEvaluatedDebt
    [Nonempty ι] (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingDiscountedDeviationPayoffCap reward discount profile who -
        (quittingGame reward).discountedPayoff discount profile none who =
      quittingBehaviorEvaluatedDeviationPayoffCap reward
          (quittingDiscountedEvaluation discount) profile who -
        quittingBehaviorEvaluatedPayoff reward
          (quittingDiscountedEvaluation discount) profile who := by
  rw [quittingDiscountedDeviationPayoffCap_eq_behaviorEvaluatedCap
    reward discount hdiscount hdiscountOne profile who,
    quittingDiscountedPayoff_eq_behaviorEvaluatedPayoff
      reward discount hdiscount hdiscountOne profile who]

end GameTheory
