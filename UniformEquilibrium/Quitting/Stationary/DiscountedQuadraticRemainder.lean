import UniformEquilibrium.Quitting.Stationary.DiscountedR0Localization
import UniformEquilibrium.Quitting.Root.BernoulliExpectation
import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound

/-!
# A source-derived quadratic discounted remainder

The bound uses the same actual reward table and root as the displacement. Its
constant is four times a uniform reward-box bound. The discount is nonnegative;
no upper discount bound, small-hazard, fixed-point or equilibrium hypothesis is
needed for the remainder estimate.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Uniform quadratic bound at every actual product root and nonnegative discount. -/
theorem abs_quittingDiscountedSingletonRemainder_hazardOfRoot_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discount M : ℝ} (hdiscount0 : 0 ≤ discount)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (root : ι → PMF Bool) (who : ι) :
    |quittingDiscountedSingletonRemainder reward discount (hazardOfRoot root) who| ≤
      4 * M * (discount + ∑ player, hazardOfRoot root player) ^ 2 := by
  let deleted := Function.update root who (PMF.pure false)
  let x := hazardOfRoot deleted
  let t := ∑ player, x player
  let c := continueMass x
  let a := reward ⟨{who}, Finset.singleton_nonempty who⟩ who
  let q := quittingRootQuitPayoff reward 0 root who
  let r := quittingRootExpectedPayoff reward 0 deleted who
  let l := 1 - (1 - discount) * c
  have hM : 0 ≤ M := (abs_nonneg a).trans (hreward _ who)
  have hx0 : ∀ player, 0 ≤ x player := hazardOfRoot_nonneg deleted
  have hx1 : ∀ player, x player ≤ 1 := hazardOfRoot_le_one deleted
  have ht : 0 ≤ t := Finset.sum_nonneg fun player _ => hx0 player
  have hc0 : 0 ≤ c := continueMass_nonneg hx1
  have hc1 : c ≤ 1 := continueMass_le_one hx0 hx1
  have hfirst := continueMass_firstOrder_bounds x hx0 hx1
  change 0 ≤ c - (1 - t) ∧ c - (1 - t) ≤ t ^ 2 / 2 at hfirst
  have hmass : quittingStationaryContinueMass deleted = c := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    unfold c continueMass x hazardOfRoot
    exact Finset.prod_congr rfl fun player _ => pmfBool_false_toReal (deleted player)
  have hself : x who = 0 := by simp [x, hazardOfRoot, deleted]
  have hother (player : ι) (hne : player ≠ who) :
      x player = hazardOfRoot root player := by
    simp [x, hazardOfRoot, deleted, hne]
  have hcleq : c = continueMassExcl (hazardOfRoot root) who := by
    unfold c continueMass
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ who), hself]
    simp only [sub_zero, one_mul]
    unfold continueMassExcl
    exact Finset.prod_congr rfl fun player hplayer => by
      rw [hother player (Finset.ne_of_mem_erase hplayer)]
  have hq : |q - a| ≤ 2 * M * t := by
    have h := abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward 0 root who M hreward
    change |q - a| ≤ 2 * M * (1 - quittingStationaryContinueMass deleted) at h
    rw [hmass] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith [hfirst.1])
      (by positivity))
  have hr : |r - ∑ player, x player *
      reward ⟨{player}, Finset.singleton_nonempty player⟩ who| ≤ 3 * M / 2 * t ^ 2 := by
    have h := abs_quittingRootExpectedPayoff_sub_singletonExpansion_le
      reward 0 deleted who (K := 0) (by simp)
      (fun terminal => hreward terminal who)
    simpa [r, x, t] using h
  have hl0 : 0 ≤ l := by dsimp [l]; nlinarith
  have hll : l ≤ discount + t := by
    dsimp [l]
    nlinarith [mul_nonneg hdiscount0 (sub_nonneg.mpr hc1), hfirst.1]
  have hlerr : |l - discount - t| ≤ t ^ 2 / 2 + discount * t := by
    apply abs_le.mpr
    dsimp [l]
    constructor
    · nlinarith [mul_nonneg hdiscount0 (sub_nonneg.mpr hfirst.1), hfirst.2]
    · nlinarith [mul_nonneg hdiscount0 (sub_nonneg.mpr hc1), hfirst.1]
  have hlinear : (∑ player, hazardOfRoot root player *
      quittingSingletonMatrix reward who player) =
      (∑ player, x player * reward ⟨{player}, Finset.singleton_nonempty player⟩ who) -
        t * a := by
    have hsum : (∑ player, hazardOfRoot root player *
        quittingSingletonMatrix reward who player) =
        ∑ player, x player * quittingSingletonMatrix reward who player := by
      apply Finset.sum_congr rfl
      intro player _
      by_cases heq : player = who
      · subst player
        simp [quittingSingletonMatrix]
      · rw [hother player heq]
    rw [hsum]
    simp only [quittingSingletonMatrix, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rfl
  have hd : quittingDiscountedDisplacement reward discount (hazardOfRoot root) who =
      l * q - r := by
    have hQ := quittingRootQuitPayoff_eq_sigmaValue reward 0 root who
    have hR := quittingRootContinuePayoff_eq_gammaValue reward 0 root who
    change r = _ at hR
    simp only [gammaValue, Pi.zero_apply, mul_zero, add_zero] at hR
    rw [quittingDiscountedDisplacement, ← hcleq, ← hQ, ← hR]
  have he : quittingDiscountedSingletonRemainder reward discount (hazardOfRoot root) who =
      l * (q - a) + (l - discount - t) * a -
        (r - ∑ player, x player * reward ⟨{player}, Finset.singleton_nonempty player⟩ who) := by
    rw [quittingDiscountedSingletonRemainder, hd, hlinear]
    dsimp only [a]
    ring
  have he_bound :
      |quittingDiscountedSingletonRemainder reward discount (hazardOfRoot root) who| ≤
        (discount + t) * (2 * M * t) + (t ^ 2 / 2 + discount * t) * M +
          3 * M / 2 * t ^ 2 := by
    rw [he]
    refine (abs_sub _ _).trans ((add_le_add
      (abs_add_le (l * (q - a)) ((l - discount - t) * a)) (le_refl _)).trans ?_)
    apply add_le_add _ hr
    apply add_le_add
    · rw [abs_mul, abs_of_nonneg hl0]
      exact mul_le_mul hll hq (abs_nonneg _) (add_nonneg hdiscount0 ht)
    · rw [abs_mul]
      exact mul_le_mul hlerr (hreward _ who) (abs_nonneg _) (by positivity)
  have htle : t ≤ ∑ player, hazardOfRoot root player := by
    apply Finset.sum_le_sum
    intro player _
    by_cases heq : player = who
    · subst player
      rw [hself]
      exact hazardOfRoot_nonneg root who
    · exact (hother player heq).le
  have hsq : (discount + t) ^ 2 ≤
      (discount + ∑ player, hazardOfRoot root player) ^ 2 :=
    sq_le_sq₀ (add_nonneg hdiscount0 ht)
      (add_nonneg hdiscount0 (Finset.sum_nonneg fun player _ => hazardOfRoot_nonneg root player))
      |>.mpr (add_le_add (le_refl discount) htle)
  have hfinal := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * M by positivity)
  nlinarith [mul_nonneg hM (sq_nonneg discount),
    mul_nonneg hM (mul_nonneg hdiscount0 ht)]

/-- Real hazard coordinates retain their literal input through the root decoder. -/
theorem abs_quittingDiscountedSingletonRemainder_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discount M : ℝ} (hdiscount0 : 0 ≤ discount)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hazard : ι → ℝ) (hzero : ∀ player, 0 ≤ hazard player)
    (hone : ∀ player, hazard player ≤ 1) (who : ι) :
    |quittingDiscountedSingletonRemainder reward discount hazard who| ≤
      4 * M * (discount + ∑ player, hazard player) ^ 2 := by
  simpa only [hazardOfRoot_rootOfHazard] using
    abs_quittingDiscountedSingletonRemainder_hazardOfRoot_le reward hdiscount0
      hreward (rootOfHazard hazard hzero hone) who

/-- Source-derived localization: no remainder certificate is supplied. -/
theorem sum_hazard_le_discount_of_quittingDiscountedFixedPoint_reward_bound [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hR0 : Math.LinearProgramming.IsR0Matrix (quittingSingletonMatrix reward))
    {discount M : ℝ} (hdiscount : 0 ≤ discount)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hazard : ι → ℝ) (hzero : ∀ player, 0 ≤ hazard player)
    (hupper : ∀ player, hazard player < 1)
    (hfixed : quittingDiscountedClippedMap reward discount hazard = hazard)
    (hsmall : quittingSingletonLocalizationFactor reward * (4 * M) *
      (discount + ∑ player, hazard player) ≤ 1 / 2) :
    (∑ player, hazard player) ≤
      (2 * quittingSingletonLocalizationFactor reward * M + 1) * discount := by
  exact sum_hazard_le_discount_of_quittingDiscountedFixedPoint reward hR0 hazard hdiscount
    (fun player => hreward _ player)
    (abs_quittingDiscountedSingletonRemainder_le reward hdiscount hreward hazard hzero
      (fun player => (hupper player).le)) hzero hupper hfixed hsmall

/-- The same literal fixed point satisfies the coordinatewise scaled bound. -/
theorem hazard_div_discount_le_of_quittingDiscountedFixedPoint_reward_bound [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hR0 : Math.LinearProgramming.IsR0Matrix (quittingSingletonMatrix reward))
    {discount M : ℝ} (hdiscount : 0 < discount)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hazard : ι → ℝ) (hzero : ∀ player, 0 ≤ hazard player)
    (hupper : ∀ player, hazard player < 1)
    (hfixed : quittingDiscountedClippedMap reward discount hazard = hazard)
    (hsmall : quittingSingletonLocalizationFactor reward * (4 * M) *
      (discount + ∑ player, hazard player) ≤ 1 / 2) (who : ι) :
    hazard who / discount ≤ 2 * quittingSingletonLocalizationFactor reward * M + 1 := by
  exact hazard_div_discount_le_of_quittingDiscountedFixedPoint reward hR0 hazard hdiscount
    (fun player => hreward _ player)
    (abs_quittingDiscountedSingletonRemainder_le reward hdiscount.le hreward hazard hzero
      (fun player => (hupper player).le)) hzero hupper hfixed hsmall who

end GameTheory
