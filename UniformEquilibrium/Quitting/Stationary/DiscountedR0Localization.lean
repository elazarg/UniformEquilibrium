import UniformEquilibrium.Quitting.Stationary.DiscountedDisplacement
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import MathUE.LinearProgramming.R0Margin

/-!
# Quantitative localization from the actual discounted displacement

The remainder is the literal difference between the existing displacement and
its singleton linear part, for the same reward table, discount and hazard.
An actual fixed point away from the upper faces solves an exact standard LCP
with this remainder in its right-hand side. The existing positive R₀ margin
then absorbs a supplied quadratic estimate and bounds hazard divided by discount.

This module does not prove the quadratic remainder estimate or produce the R₀
property from absence of equilibrium. Both remain explicit source obligations.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal remainder after subtracting the singleton linear displacement. -/
def quittingDiscountedSingletonRemainder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discount : ℝ) (hazard : ι → ℝ) (who : ι) : ℝ :=
  quittingDiscountedDisplacement reward discount hazard who -
    discount * reward ⟨{who}, Finset.singleton_nonempty who⟩ who +
      ∑ player, hazard player * quittingSingletonMatrix reward who player

/-- Exact linear part, with the comparison matrix in its standard LCP orientation. -/
theorem quittingDiscountedDisplacement_eq_singletonLinear_add_remainder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discount : ℝ) (hazard : ι → ℝ) (who : ι) :
    quittingDiscountedDisplacement reward discount hazard who =
      discount * reward ⟨{who}, Finset.singleton_nonempty who⟩ who -
        (∑ player, hazard player * quittingSingletonMatrix reward who player) +
          quittingDiscountedSingletonRemainder reward discount hazard who := by
  unfold quittingDiscountedSingletonRemainder
  ring

/-- The perturbed LCP slack is exactly minus the actual displacement. -/
theorem lcpResidual_quittingDiscountedSingletonRemainder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discount : ℝ) (hazard : ι → ℝ) (who : ι) :
    lcpResidual (quittingSingletonMatrix reward)
        (fun player => -discount * reward ⟨{player}, Finset.singleton_nonempty player⟩ player -
          quittingDiscountedSingletonRemainder reward discount hazard player) hazard who =
      -quittingDiscountedDisplacement reward discount hazard who := by
  unfold lcpResidual quittingDiscountedSingletonRemainder
  ring

/-- Every actual clipped fixed point below the upper faces solves this exact LCP. -/
theorem isStandardLCPSolution_of_quittingDiscountedFixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discount : ℝ) (hazard : ι → ℝ)
    (hzero : ∀ player, 0 ≤ hazard player) (hupper : ∀ player, hazard player < 1)
    (hfixed : quittingDiscountedClippedMap reward discount hazard = hazard) :
    IsStandardLCPSolution (quittingSingletonMatrix reward)
      (fun player => -discount * reward ⟨{player}, Finset.singleton_nonempty player⟩ player -
        quittingDiscountedSingletonRemainder reward discount hazard player) hazard := by
  have hface := (quittingDiscountedClippedMap_eq_self_iff reward discount hazard hzero
    (fun player => (hupper player).le)).mp hfixed
  refine ⟨hzero, ?_, ?_⟩
  · intro player
    rw [lcpResidual_quittingDiscountedSingletonRemainder]
    rcases eq_or_lt_of_le (hzero player) with h | h
    · exact neg_nonneg.mpr ((hface player).1 h.symm)
    · rw [(hface player).2.1 h (hupper player)]
      exact neg_nonneg.mpr (le_refl (0 : ℝ))
  · intro player
    rw [lcpResidual_quittingDiscountedSingletonRemainder]
    rcases eq_or_lt_of_le (hzero player) with h | h
    · rw [← h, zero_mul]
    · rw [(hface player).2.1 h (hupper player), neg_zero, mul_zero]

/-- The explicit margin multiplier for the same reward table's singleton matrix. -/
def quittingSingletonLocalizationFactor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  ((Fintype.card ι : ℝ) + 1) / r0Margin (quittingSingletonMatrix reward)

omit [DecidableEq ι] in
theorem quittingSingletonLocalizationFactor_pos [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward)) :
    0 < quittingSingletonLocalizationFactor reward := by
  unfold quittingSingletonLocalizationFactor
  exact div_pos (by positivity) ((r0Margin_pos_iff_isR0Matrix _).mpr hR0)

/-- The R₀ estimate retains the literal remainder bound. -/
theorem sum_hazard_le_of_quittingDiscountedFixedPoint_remainder_bound [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward))
    {discount A B : ℝ} (hazard : ι → ℝ) (hdiscount : 0 ≤ discount)
    (hsingleton : ∀ player, |reward ⟨{player}, Finset.singleton_nonempty player⟩ player| ≤ A)
    (hremainder : ∀ player,
      |quittingDiscountedSingletonRemainder reward discount hazard player| ≤ B)
    (hzero : ∀ player, 0 ≤ hazard player) (hupper : ∀ player, hazard player < 1)
    (hfixed : quittingDiscountedClippedMap reward discount hazard = hazard) :
    (∑ player, hazard player) ≤
      quittingSingletonLocalizationFactor reward * (discount * A + B) := by
  have hbound := sum_le_of_isStandardLCPSolution (quittingSingletonMatrix reward)
    ((r0Margin_pos_iff_isR0Matrix _).mpr hR0)
    (fun player => -discount * reward ⟨{player}, Finset.singleton_nonempty player⟩ player -
      quittingDiscountedSingletonRemainder reward discount hazard player) hazard
    (B := discount * A + B) (fun player => ?_)
    (isStandardLCPSolution_of_quittingDiscountedFixedPoint reward discount hazard
      hzero hupper hfixed)
  · convert hbound using 1
    unfold quittingSingletonLocalizationFactor
    ring
  · calc
      _ ≤ |-discount * reward ⟨{player}, Finset.singleton_nonempty player⟩ player| +
          |quittingDiscountedSingletonRemainder reward discount hazard player| := abs_sub _ _
      _ ≤ discount * A + B := by
        rw [abs_mul, abs_neg, abs_of_nonneg hdiscount]
        exact add_le_add (mul_le_mul_of_nonneg_left (hsingleton player) hdiscount)
          (hremainder player)

/-- A quadratic estimate on the actual remainder yields linear localization once
the total scale is small relative to the same matrix's positive R₀ margin. -/
theorem sum_hazard_le_discount_of_quittingDiscountedFixedPoint [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward))
    {discount A K : ℝ} (hazard : ι → ℝ) (hdiscount : 0 ≤ discount)
    (hsingleton : ∀ player, |reward ⟨{player}, Finset.singleton_nonempty player⟩ player| ≤ A)
    (hremainder : ∀ player,
      |quittingDiscountedSingletonRemainder reward discount hazard player| ≤
        K * (discount + ∑ other, hazard other) ^ 2)
    (hzero : ∀ player, 0 ≤ hazard player) (hupper : ∀ player, hazard player < 1)
    (hfixed : quittingDiscountedClippedMap reward discount hazard = hazard)
    (hsmall : quittingSingletonLocalizationFactor reward * K *
      (discount + ∑ player, hazard player) ≤ 1 / 2) :
    (∑ player, hazard player) ≤
      (2 * quittingSingletonLocalizationFactor reward * A + 1) * discount := by
  have hbound := sum_hazard_le_of_quittingDiscountedFixedPoint_remainder_bound
    reward hR0 hazard hdiscount hsingleton hremainder hzero hupper hfixed
  have hscale : 0 ≤ discount + ∑ player, hazard player :=
    add_nonneg hdiscount (Finset.sum_nonneg fun player _ => hzero player)
  have habsorb := mul_le_mul_of_nonneg_right hsmall hscale
  nlinarith [hbound, habsorb]

/-- Coordinatewise ratio bound for every supplied positive-discount fixed point. -/
theorem hazard_div_discount_le_of_quittingDiscountedFixedPoint [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward))
    {discount A K : ℝ} (hazard : ι → ℝ) (hdiscount : 0 < discount)
    (hsingleton : ∀ player, |reward ⟨{player}, Finset.singleton_nonempty player⟩ player| ≤ A)
    (hremainder : ∀ player,
      |quittingDiscountedSingletonRemainder reward discount hazard player| ≤
        K * (discount + ∑ other, hazard other) ^ 2)
    (hzero : ∀ player, 0 ≤ hazard player) (hupper : ∀ player, hazard player < 1)
    (hfixed : quittingDiscountedClippedMap reward discount hazard = hazard)
    (hsmall : quittingSingletonLocalizationFactor reward * K *
      (discount + ∑ player, hazard player) ≤ 1 / 2) (who : ι) :
    hazard who / discount ≤ 2 * quittingSingletonLocalizationFactor reward * A + 1 := by
  apply (div_le_iff₀ hdiscount).mpr
  exact (Finset.single_le_sum (fun player _ => hzero player)
    (Finset.mem_univ who)).trans
      (sum_hazard_le_discount_of_quittingDiscountedFixedPoint reward hR0 hazard
        hdiscount.le hsingleton hremainder hzero hupper hfixed hsmall)

end GameTheory
