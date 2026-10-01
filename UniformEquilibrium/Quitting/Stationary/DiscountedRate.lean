import UniformEquilibrium.Quitting.Paths.DiscountedLiveTailRate
import UniformEquilibrium.Quitting.Stationary.LiveMass
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Geometric discounted rates with unchanged stationary opponents

The canonical discounted payoff has actual exit weight d^(t+1). Every complete
behavioral reply is compared two-sided to its own terminal payoff. Prescribed
delivery can instead use the joint clock, including a positive sole owner:
no contraction of that owner's deleted-opponent clock is then required.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι]

/-- The normalized actual joint live clock has its exact geometric denominator,
without a joint contraction assumption: d<1 already makes the series summable. -/
theorem quittingDiscountedLiveTail_stationary_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1) :
    quittingDiscountedLiveTail reward (quittingStationaryProfile reward root) discount =
      (1 - discount) / (1 - discount * quittingStationaryContinueMass root) := by
  have hproduct0 : 0 ≤ discount * quittingStationaryContinueMass root :=
    mul_nonneg hdiscount (quittingStationaryContinueMass_nonneg root)
  have hproduct1 : discount * quittingStationaryContinueMass root < 1 := by
    calc
      discount * quittingStationaryContinueMass root ≤ discount * 1 :=
        mul_le_mul_of_nonneg_left (quittingStationaryContinueMass_le_one root) hdiscount
      _ = discount := mul_one _
      _ < 1 := hdiscountOne
  unfold quittingDiscountedLiveTail
  simp_rw [quittingLiveMass_stationary_eq_pow, ← mul_pow]
  rw [tsum_geometric_of_lt_one hproduct0 hproduct1, div_eq_mul_inv]

/-- Contraction weakens the exact denominator to the packet's literal joint gap. -/
theorem quittingDiscountedLiveTail_stationary_le_jointGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (hcontracts : quittingStationaryContinueMass root < 1) :
    quittingDiscountedLiveTail reward (quittingStationaryProfile reward root) discount ≤
      (1 - discount) / (1 - quittingStationaryContinueMass root) := by
  rw [quittingDiscountedLiveTail_stationary_eq reward root discount hdiscount hdiscountOne]
  apply div_le_div_of_nonneg_left (sub_nonneg.mpr hdiscountOne.le)
    (sub_pos.mpr hcontracts)
  have hproduct : discount * quittingStationaryContinueMass root ≤
      quittingStationaryContinueMass root := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdiscountOne.le
      (quittingStationaryContinueMass_nonneg root)
  exact sub_le_sub_left hproduct 1

/-- Delivery uses only actual JOINT contraction, not every player's opponent contraction. -/
theorem abs_discountedPayoff_stationary_sub_terminal_le_jointGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) (who : ι)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal who| ≤ bound)
    (hcontracts : quittingStationaryContinueMass root < 1) :
    |(quittingGame reward).discountedPayoff discount
        (quittingStationaryProfile reward root) none who -
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
      bound * (1 - discount) / (1 - quittingStationaryContinueMass root) := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have hclock := mul_le_mul_of_nonneg_left
    (quittingDiscountedLiveTail_stationary_le_jointGap reward root discount
      hdiscount hdiscountOne hcontracts) hbound
  exact (abs_discountedPayoff_sub_terminal_le_liveTail reward
    (quittingStationaryProfile reward root) who discount hdiscount hdiscountOne bound hreward).trans
      (by simpa only [mul_div_assoc] using hclock)

variable [DecidableEq ι]

/-- Actual stationary opponents have exactly their deleted-coordinate geometric clock. -/
theorem quittingDiscountedLiveTail_stationary_opponents_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) (who : ι)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1) :
    quittingDiscountedLiveTail reward
        (quittingOpponentOnlyProfile reward (quittingStationaryProfile reward root) who)
          discount =
      (1 - discount) /
        (1 - discount * quittingStationaryFixedOpponentsContinueMass root who) := by
  unfold quittingOpponentOnlyProfile
  rw [update_quittingStationaryProfile_alwaysContinue,
    quittingDiscountedLiveTail_stationary_eq reward _ discount hdiscount hdiscountOne]
  rfl

/-- Every complete behavioral reply against the SAME original stationary opponents
has the packet's two-sided geometric error M(1-d)/(1-alpha_i), including d=0. -/
theorem abs_discountedPayoff_update_stationary_sub_terminal_le_opponentGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal who| ≤ bound)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1) :
    |(quittingGame reward).discountedPayoff discount
        (Function.update (quittingStationaryProfile reward root) who deviation) none who -
      quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) who deviation) who| ≤
      bound * (1 - discount) / (1 - quittingStationaryFixedOpponentsContinueMass root who) := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have hforced : quittingStationaryContinueMass
      (Function.update root who (PMF.pure false)) < 1 := hcontracts
  have hclock := mul_le_mul_of_nonneg_left
    (quittingDiscountedLiveTail_stationary_le_jointGap reward
      (Function.update root who (PMF.pure false)) discount
      hdiscount hdiscountOne hforced) hbound
  have hscaled : bound * quittingDiscountedLiveTail reward
      (quittingOpponentOnlyProfile reward (quittingStationaryProfile reward root) who) discount ≤
        bound * (1 - discount) /
          (1 - quittingStationaryFixedOpponentsContinueMass root who) := by
    unfold quittingOpponentOnlyProfile
    rw [update_quittingStationaryProfile_alwaysContinue]
    change bound * quittingDiscountedLiveTail reward
        (quittingStationaryProfile reward (Function.update root who (PMF.pure false))) discount ≤
      bound * (1 - discount) /
        (1 - quittingStationaryContinueMass (Function.update root who (PMF.pure false)))
    simpa only [mul_div_assoc] using hclock
  exact (abs_discountedPayoff_update_sub_terminal_le_opponentLiveTail reward
    (quittingStationaryProfile reward root) who deviation discount
      hdiscount hdiscountOne bound hreward).trans hscaled

/-- Terminal Nash combines prescribed delivery and all-reply error into playerwise
discounted regret. No global gap or minimum over the player set is supplied. -/
theorem discountedPayoff_update_stationary_le_add_playerwise_error
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (bound : ℝ) (hreward : ∀ terminal, |reward terminal who| ≤ bound)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root)) :
    (quittingGame reward).discountedPayoff discount
        (Function.update (quittingStationaryProfile reward root) who deviation) none who ≤
      (quittingGame reward).discountedPayoff discount
          (quittingStationaryProfile reward root) none who +
        2 * bound * (1 - discount) /
          (1 - quittingStationaryFixedOpponentsContinueMass root who) := by
  have hdelivery := abs_discountedPayoff_update_stationary_sub_terminal_le_opponentGap reward
    root who ((quittingStationaryProfile reward root) who) discount
      hdiscount hdiscountOne bound hreward hcontracts
  simp only [Function.update_eq_self] at hdelivery
  have hreply := abs_discountedPayoff_update_stationary_sub_terminal_le_opponentGap reward
    root who deviation discount hdiscount hdiscountOne bound hreward hcontracts
  have hterminal := hnash who deviation
  simp only [add_zero] at hterminal
  have hdouble :
      bound * (1 - discount) / (1 - quittingStationaryFixedOpponentsContinueMass root who) +
        bound * (1 - discount) / (1 - quittingStationaryFixedOpponentsContinueMass root who) =
      2 * bound * (1 - discount) /
        (1 - quittingStationaryFixedOpponentsContinueMass root who) := by ring
  linarith [(abs_le.mp hdelivery).1, (abs_le.mp hreply).2]

end GameTheory
