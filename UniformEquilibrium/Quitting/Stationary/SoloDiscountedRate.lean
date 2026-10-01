import UniformEquilibrium.Quitting.Paths.AlwaysContinueEvaluatedReplies
import UniformEquilibrium.Quitting.Paths.DiscountedBehavioralCap
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Stationary.DiscountedRate

/-! # The positive sole owner's one-M discounted regret bound

The SAME stationary solo profile is used throughout. Its owner has no
contracting deleted-opponent clock, so the general two-M all-reply comparison
does not apply to that coordinate. Instead its nonnegative singleton bounds
every complete discounted reply, and delivery uses the actual JOINT hazard.
Outsiders remain covered by the existing contracting-opponent theorem.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem soloProfile_owner_update_eq_alwaysContinue_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (deviation : (quittingGame reward).BehaviorStrategy owner) :
    Function.update (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard))
        owner deviation =
      Function.update (quittingAlwaysContinueProfile reward) owner deviation := by
  rw [← quittingSoloStationaryProfile_update_owner_never reward owner hazard,
    Function.update_idem]

/-- Every complete normalized-discounted owner response is capped by the
actual nonnegative singleton, without any owner-opponent contraction premise. -/
theorem quittingDiscountedDeviationPayoffCap_solo_owner_le_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1) :
    quittingDiscountedDeviationPayoffCap reward discount
      (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)) owner ≤
        reward (quittingSingletonTerminal owner) owner := by
  let : Nonempty ι := ⟨owner⟩
  rw [quittingDiscountedDeviationPayoffCap_eq_behaviorEvaluatedCap
    reward discount hdiscount hdiscountOne]
  have hcap : quittingBehaviorEvaluatedDeviationPayoffCap reward
      (quittingDiscountedEvaluation discount)
      (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)) owner =
      quittingBehaviorEvaluatedDeviationPayoffCap reward
        (quittingDiscountedEvaluation discount) (quittingAlwaysContinueProfile reward) owner := by
    unfold quittingBehaviorEvaluatedDeviationPayoffCap
    apply congrArg sSup
    apply congrArg Set.range
    funext deviation
    rw [soloProfile_owner_update_eq_alwaysContinue_update]
  rw [hcap]
  exact quittingBehaviorEvaluatedDeviationPayoffCap_alwaysContinue_le_singleton reward
    (quittingDiscountedEvaluation discount)
    (quittingDiscountedEvaluation_nonneg discount hdiscount)
    (quittingDiscountedEvaluation_le_one discount hdiscount hdiscountOne.le) owner howner

/-- The bound is for EACH unrestricted complete strategy, not just the
stationary, pure-time, or finite-date replies used to compute the envelope. -/
theorem discountedPayoff_update_solo_owner_le_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (deviation : (quittingGame reward).BehaviorStrategy owner) :
    (quittingGame reward).discountedPayoff discount
        (Function.update
          (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard))
          owner deviation) none owner ≤ reward (quittingSingletonTerminal owner) owner := by
  let : Nonempty ι := ⟨owner⟩
  rw [quittingDiscountedPayoff_update_eq_behaviorEvaluatedPayoff
    reward discount hdiscount hdiscountOne]
  have hbounded := bddAbove_range_quittingBehaviorEvaluatedPayoff_update reward
    (quittingDiscountedEvaluation discount)
    (quittingDiscountedEvaluation_nonneg discount hdiscount)
    (quittingDiscountedEvaluation_antitone discount hdiscount hdiscountOne.le)
    (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)) owner
  have hle : quittingBehaviorEvaluatedPayoff reward (quittingDiscountedEvaluation discount)
      (Function.update
        (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard))
        owner deviation) owner ≤
      quittingBehaviorEvaluatedDeviationPayoffCap reward (quittingDiscountedEvaluation discount)
        (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)) owner :=
    le_csSup hbounded ⟨deviation, rfl⟩
  have hcap := quittingDiscountedDeviationPayoffCap_solo_owner_le_singleton
    reward owner hazard howner discount hdiscount hdiscountOne
  rw [quittingDiscountedDeviationPayoffCap_eq_behaviorEvaluatedCap
    reward discount hdiscount hdiscountOne] at hcap
  exact hle.trans hcap

/-- Prescribed delivery uses the actual JOINT hazard, not the owner's
noncontracting deleted clock. Singleton signs are unnecessary for delivery. -/
theorem abs_discountedPayoff_solo_owner_sub_singleton_le_jointHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) (hpositive : 0 < (hazard true).toReal)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal owner| ≤ bound) :
    |(quittingGame reward).discountedPayoff discount
        (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)) none owner -
      reward (quittingSingletonTerminal owner) owner| ≤
        bound * (1 - discount) / (hazard true).toReal := by
  have hdelivery := abs_discountedPayoff_stationary_sub_terminal_le_jointGap reward
    (quittingSoloStationaryRoot owner hazard) owner discount hdiscount hdiscountOne bound hreward
    (quittingStationaryContinueMass_soloStationaryRoot_lt_one owner hazard hpositive)
  have hgap : 1 - quittingStationaryContinueMass (quittingSoloStationaryRoot owner hazard) =
      (hazard true).toReal := quittingRootAbsorptionMass_soloStationaryRoot owner hazard
  rw [quittingTerminalPayoff_soloStationary reward owner owner hazard hpositive,
    quittingSoloReward_self, hgap] at hdelivery
  exact hdelivery

/-- Literal nonnegative delivery shortfall of the SAME prescribed profile. -/
theorem discountedPayoff_solo_owner_shortfall_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) (hpositive : 0 < (hazard true).toReal)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal owner| ≤ bound) :
    let profile := quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)
    0 ≤ reward (quittingSingletonTerminal owner) owner -
        (quittingGame reward).discountedPayoff discount profile none owner ∧
      reward (quittingSingletonTerminal owner) owner -
        (quittingGame reward).discountedPayoff discount profile none owner ≤
          bound * (1 - discount) / (hazard true).toReal := by
  dsimp only
  have hself := discountedPayoff_update_solo_owner_le_singleton
    reward owner hazard howner discount hdiscount hdiscountOne
    ((quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)) owner)
  simp only [Function.update_eq_self] at hself
  have hdelivery := abs_discountedPayoff_solo_owner_sub_singleton_le_jointHazard
    reward owner hazard hpositive discount hdiscount hdiscountOne bound hreward
  exact ⟨sub_nonneg.mpr hself, by linarith [(abs_le.mp hdelivery).1]⟩

/-- The SAME positive-hazard profile has the packet's one-M owner regret
constant for every d in [0,1), including zero patience. -/
theorem discountedPayoff_update_solo_owner_le_add_one_bound_error
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) (hpositive : 0 < (hazard true).toReal)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal owner| ≤ bound)
    (deviation : (quittingGame reward).BehaviorStrategy owner) :
    (quittingGame reward).discountedPayoff discount
        (Function.update
          (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard))
          owner deviation) none owner ≤
      (quittingGame reward).discountedPayoff discount
          (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)) none owner +
        bound * (1 - discount) / (hazard true).toReal := by
  have hreply := discountedPayoff_update_solo_owner_le_singleton
    reward owner hazard howner discount hdiscount hdiscountOne deviation
  have hdelivery := abs_discountedPayoff_solo_owner_sub_singleton_le_jointHazard
    reward owner hazard hpositive discount hdiscount hdiscountOne bound hreward
  linarith [(abs_le.mp hdelivery).1]

/-- The corresponding COMPLETE discounted debt has the identical one-M bound. -/
theorem quittingDiscountedDeviationDebt_solo_owner_le_one_bound_error
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) (hpositive : 0 < (hazard true).toReal)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal owner| ≤ bound) :
    quittingDiscountedDeviationPayoffCap reward discount
        (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)) owner -
      (quittingGame reward).discountedPayoff discount
        (quittingStationaryProfile reward (quittingSoloStationaryRoot owner hazard)) none owner ≤
      bound * (1 - discount) / (hazard true).toReal := by
  have hcap := quittingDiscountedDeviationPayoffCap_solo_owner_le_singleton
    reward owner hazard howner discount hdiscount hdiscountOne
  have hdelivery := abs_discountedPayoff_solo_owner_sub_singleton_le_jointHazard
    reward owner hazard hpositive discount hdiscount hdiscountOne bound hreward
  linarith [(abs_le.mp hdelivery).1]

end GameTheory
