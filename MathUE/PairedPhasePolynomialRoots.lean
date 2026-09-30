import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Admissible roots of two paired polynomial equations

Scalar intermediate-value constructions produce an ordered interior zero of
a pair of polynomial residuals for every parameter in `[1,2]`. The rational
substitution is used only where its denominator is positive. The final zero is
not asserted to be unique.
-/

noncomputable section

namespace Math.PairedPhasePolynomialRoots

def affineEndpoint (c x : ℝ) : ℝ := c - (c - 1) * x

def primaryResidual (c a b : ℝ) : ℝ :=
  affineEndpoint c b * (1 - a * b ^ 2) - b * (1 - a) * (1 + 3 * b)

def secondaryResidual (c a b : ℝ) : ℝ :=
  affineEndpoint c a * (1 - a ^ 2 * b) - 4 * a ^ 2 * (1 - b)

def startingPolynomial (c a : ℝ) : ℝ := 4 * a ^ 2 - affineEndpoint c a

def orderingPolynomial (c a : ℝ) : ℝ :=
  (c - 1) * a ^ 3 + 3 * a ^ 2 - a - c

def secondaryRate (c a : ℝ) : ℝ :=
  startingPolynomial c a / (a ^ 2 * (4 - affineEndpoint c a))

def primaryJoin (c a b : ℝ) : ℝ := c * (a + b) + (1 - 2 * c) * a * b

def secondaryJoin (c a b : ℝ) : ℝ :=
  1 + (c - 1) * (a + b - 2 * a * b)

theorem affineEndpoint_bounds {c x : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : affineEndpoint c x ∈ Set.Icc (1 : ℝ) 2 := by
  dsimp [affineEndpoint]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hc.1) (sub_nonneg.mpr hx.2)]
  · nlinarith [hc.2, mul_nonneg (sub_nonneg.mpr hc.1) hx.1]

theorem denominator_pos {c a : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) : 0 < a ^ 2 * (4 - affineEndpoint c a) := by
  have hbounds := affineEndpoint_bounds hc ⟨ha.1.le, ha.2⟩
  exact mul_pos (sq_pos_of_pos ha.1) (by linarith [hbounds.2])

theorem startingPolynomial_strictMonoOn {c : ℝ} (hc : 1 ≤ c) :
    StrictMonoOn (startingPolynomial c) (Set.Ici ((1 : ℝ) / 2)) := by
  intro x hx y hy hxy
  change (1 : ℝ) / 2 ≤ x at hx
  change (1 : ℝ) / 2 ≤ y at hy
  have hfactor : 0 < 4 * (x + y) + (c - 1) := by
    linarith
  have hpositive := mul_pos (sub_pos.mpr hxy) hfactor
  dsimp [startingPolynomial, affineEndpoint]
  nlinarith

theorem orderingPolynomial_strictMonoOn {c : ℝ} (hc : 1 ≤ c) :
    StrictMonoOn (orderingPolynomial c) (Set.Ici ((1 : ℝ) / 2)) := by
  intro x hx y hy hxy
  change (1 : ℝ) / 2 ≤ x at hx
  change (1 : ℝ) / 2 ≤ y at hy
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hsum : 0 ≤ y ^ 2 + y * x + x ^ 2 := by positivity
  have hterm := mul_nonneg (sub_nonneg.mpr hc) hsum
  have hfactor : 0 < (c - 1) * (y ^ 2 + y * x + x ^ 2) + 3 * (x + y) - 1 := by
    linarith
  have hpositive := mul_pos (sub_pos.mpr hxy) hfactor
  have hidentity : orderingPolynomial c y - orderingPolynomial c x =
      (y - x) * ((c - 1) * (y ^ 2 + y * x + x ^ 2) + 3 * (x + y) - 1) := by
    unfold orderingPolynomial
    ring
  linarith

theorem orderingPolynomial_identity (c a : ℝ) :
    orderingPolynomial c a =
      4 * a ^ 2 - affineEndpoint c a * (1 + a + a ^ 2) := by
  unfold orderingPolynomial affineEndpoint
  ring

theorem secondaryResidual_at_secondaryRate {c a : ℝ} (ha : a ≠ 0)
    (hendpoint : 4 - affineEndpoint c a ≠ 0) :
    secondaryResidual c a (secondaryRate c a) = 0 := by
  unfold secondaryResidual secondaryRate startingPolynomial
  field_simp [ha, hendpoint]
  ring

theorem secondaryRate_sub_self {c a : ℝ} (ha : a ≠ 0)
    (hendpoint : 4 - affineEndpoint c a ≠ 0) :
    secondaryRate c a - a =
      (1 - a) * orderingPolynomial c a / (a ^ 2 * (4 - affineEndpoint c a)) := by
  rw [orderingPolynomial_identity]
  unfold secondaryRate startingPolynomial
  field_simp [ha, hendpoint]
  ring_nf

theorem primaryResidual_diagonal_sub_secondaryResidual (c a : ℝ) :
    primaryResidual c a a - secondaryResidual c a a = -a * (1 - a) ^ 2 := by
  unfold primaryResidual secondaryResidual
  ring

theorem exists_starting_root {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    ∃ a₀ ∈ Set.Ico ((1 : ℝ) / 2) (2 / 3), startingPolynomial c a₀ = 0 := by
  have hleft : startingPolynomial c (1 / 2) ≤ 0 := by
    dsimp [startingPolynomial, affineEndpoint]
    nlinarith [hc.1]
  have hright : 0 < startingPolynomial c (2 / 3) := by
    dsimp [startingPolynomial, affineEndpoint]
    nlinarith [hc.2]
  exact intermediate_value_Ico (by norm_num)
    (by unfold startingPolynomial affineEndpoint; fun_prop) ⟨hleft, hright⟩

theorem exists_ordering_root {c a₀ : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (ha₀ : a₀ ∈ Set.Ico ((1 : ℝ) / 2) (2 / 3))
    (hstarting : startingPolynomial c a₀ = 0) :
    ∃ a₁ ∈ Set.Ioo a₀ ((9 : ℝ) / 10), orderingPolynomial c a₁ = 0 := by
  have ha₀0 : 0 < a₀ := by linarith [ha₀.1]
  have ha₀1 : a₀ ≤ 1 := by linarith [ha₀.2]
  have hbounds := affineEndpoint_bounds hc ⟨ha₀0.le, ha₀1⟩
  have hleft : orderingPolynomial c a₀ < 0 := by
    rw [orderingPolynomial_identity]
    have hpositive : 0 < affineEndpoint c a₀ * (a₀ + a₀ ^ 2) := by
      apply mul_pos (by linarith [hbounds.1])
      positivity
    dsimp [startingPolynomial] at hstarting
    nlinarith
  have hright : 0 < orderingPolynomial c (9 / 10) := by
    dsimp [orderingPolynomial]
    nlinarith [hc.2]
  exact intermediate_value_Ioo (by linarith [ha₀.2])
    (by unfold orderingPolynomial; fun_prop) ⟨hleft, hright⟩

theorem secondaryRate_pos_of_starting_root {c a₀ a : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) (ha₀ : (1 : ℝ) / 2 ≤ a₀)
    (hstarting : startingPolynomial c a₀ = 0) (ha : a₀ < a) (ha1 : a ≤ 1) :
    0 < secondaryRate c a := by
  have ha0 : 0 < a := by linarith
  apply div_pos _ (denominator_pos hc ⟨ha0, ha1⟩)
  have hmono := startingPolynomial_strictMonoOn hc.1
    (Set.mem_Ici.mpr ha₀) (Set.mem_Ici.mpr (by linarith)) ha
  simpa only [hstarting] using hmono

theorem secondaryRate_lt_self_of_ordering_root {c a a₁ : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) (ha : (1 : ℝ) / 2 ≤ a)
    (haa₁ : a < a₁) (ha₁ : a₁ < 1) (hordering : orderingPolynomial c a₁ = 0) :
    secondaryRate c a < a := by
  have ha0 : 0 < a := by linarith
  have ha1 : a < 1 := lt_trans haa₁ ha₁
  have hden := denominator_pos hc ⟨ha0, ha1.le⟩
  have hendpoint : 4 - affineEndpoint c a ≠ 0 := by
    have hbounds := affineEndpoint_bounds hc ⟨ha0.le, ha1.le⟩
    linarith [hbounds.2]
  have hmono := orderingPolynomial_strictMonoOn hc.1
    (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (by linarith)) haa₁
  have hnegative : orderingPolynomial c a < 0 := by simpa [hordering] using hmono
  have hquotient := div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (sub_pos.mpr ha1) hnegative) hden
  rw [← secondaryRate_sub_self (ne_of_gt ha0) hendpoint] at hquotient
  linarith

theorem quarter_lt_of_primaryResidual_zero {c a b : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hroot : primaryResidual c a b = 0) :
    (1 : ℝ) / 4 < b := by
  have hbounds := affineEndpoint_bounds hc hb
  have hsquare : 0 ≤ b ^ 2 := sq_nonneg b
  have hsquare_le : b ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2), hb.2]
  have hfactor : 0 ≤ 1 - a * b ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) hsquare]
  have hterm := mul_nonneg (sub_nonneg.mpr hbounds.1) hfactor
  have hpositive : 0 ≤ a * (b * (1 + 3 * b)) :=
    mul_nonneg ha.1 (mul_nonneg hb.1 (by linarith [hb.1]))
  have hbound : 1 ≤ b + 4 * b ^ 2 := by
    dsimp [primaryResidual] at hroot
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) hsquare]
  by_contra hnot
  have hbquarter : b ≤ (1 : ℝ) / 4 := le_of_not_gt hnot
  have hsmall := mul_nonneg (sub_nonneg.mpr hbquarter)
    (by linarith [hb.1] : 0 ≤ 1 / 4 + b)
  nlinarith

/-- The rates are produced from the parameter alone, with both elimination
boundaries excluded before any continuation-value division. -/
theorem exists_admissible_rates {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    ∃ a b : ℝ, (1 : ℝ) / 4 < b ∧ b < a ∧ a < 9 / 10 ∧ 1 / 2 < a ∧
      primaryResidual c a b = 0 ∧ secondaryResidual c a b = 0 := by
  obtain ⟨a₀, ha₀, hstarting⟩ := exists_starting_root hc
  obtain ⟨a₁, ha₁, hordering⟩ := exists_ordering_root hc ha₀ hstarting
  have ha₀0 : 0 < a₀ := by linarith [ha₀.1]
  have ha₁0 : 0 < a₁ := by linarith [ha₀.1, ha₁.1]
  have ha₁1 : a₁ < 1 := by linarith [ha₁.2]
  have hden : ∀ a ∈ Set.Icc a₀ a₁, a ^ 2 * (4 - affineEndpoint c a) ≠ 0 := by
    intro a ha
    exact ne_of_gt (denominator_pos hc ⟨lt_of_lt_of_le ha₀0 ha.1,
      le_trans ha.2 ha₁1.le⟩)
  have hcontinuous : ContinuousOn (fun a => primaryResidual c a (secondaryRate c a))
      (Set.Icc a₀ a₁) := by
    have hrate : ContinuousOn (secondaryRate c) (Set.Icc a₀ a₁) := by
      unfold secondaryRate startingPolynomial affineEndpoint
      exact ContinuousOn.div (by fun_prop) (by fun_prop) hden
    unfold primaryResidual affineEndpoint
    fun_prop
  have hleft : 0 < primaryResidual c a₀ (secondaryRate c a₀) := by
    have hrate : secondaryRate c a₀ = 0 := by
      simp [secondaryRate, hstarting]
    simp only [hrate]
    simpa [primaryResidual, affineEndpoint] using (by linarith [hc.1] : 0 < c)
  have ha₁endpoint : 4 - affineEndpoint c a₁ ≠ 0 := by
    have hbounds := affineEndpoint_bounds hc ⟨ha₁0.le, ha₁1.le⟩
    linarith [hbounds.2]
  have hrate₁ : secondaryRate c a₁ = a₁ := by
    have hidentity := secondaryRate_sub_self (ne_of_gt ha₁0) ha₁endpoint
    rw [hordering] at hidentity
    simp only [mul_zero, zero_div] at hidentity
    linarith
  have hright : primaryResidual c a₁ (secondaryRate c a₁) < 0 := by
    have hsecondary := secondaryResidual_at_secondaryRate (ne_of_gt ha₁0) ha₁endpoint
    rw [hrate₁] at hsecondary ⊢
    have hidentity := primaryResidual_diagonal_sub_secondaryResidual c a₁
    have hpositive := mul_pos ha₁0 (sq_pos_of_pos (sub_pos.mpr ha₁1))
    linarith
  obtain ⟨a, ha, hprimary⟩ := intermediate_value_Ioo' ha₁.1.le hcontinuous ⟨hright, hleft⟩
  have ha0 : 0 < a := lt_trans ha₀0 ha.1
  have ha1 : a < 1 := lt_trans ha.2 ha₁1
  have hendpoint : 4 - affineEndpoint c a ≠ 0 := by
    have hbounds := affineEndpoint_bounds hc ⟨ha0.le, ha1.le⟩
    linarith [hbounds.2]
  have hb0 := secondaryRate_pos_of_starting_root hc ha₀.1 hstarting ha.1 ha1.le
  have hba := secondaryRate_lt_self_of_ordering_root hc
    (by linarith [ha₀.1, ha.1]) ha.2 ha₁1 hordering
  have hb1 : secondaryRate c a < 1 := lt_trans hba ha1
  refine ⟨a, secondaryRate c a, ?_, hba, lt_trans ha.2 ha₁.2,
    lt_of_le_of_lt ha₀.1 ha.1, hprimary,
    secondaryResidual_at_secondaryRate (ne_of_gt ha0) hendpoint⟩
  exact quarter_lt_of_primaryResidual_zero hc ⟨ha0.le, ha1.le⟩ ⟨hb0.le, hb1.le⟩ hprimary

theorem secondaryRate_eq_of_secondaryResidual_zero {c a b : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (hroot : secondaryResidual c a b = 0) : b = secondaryRate c a := by
  apply (eq_div_iff (ne_of_gt (denominator_pos hc ha))).mpr
  dsimp [startingPolynomial, secondaryResidual] at *
  nlinarith [hroot]

theorem secondary_slack_identity {c a : ℝ} (ha : a ≠ 0)
    (hendpoint : 4 - affineEndpoint c a ≠ 0) :
    affineEndpoint c a / a - secondaryJoin c a (secondaryRate c a) =
      -(1 - a) * affineEndpoint c a * ((c - 1) * (a ^ 2 + 2 * a - 1) - 3 * a) /
        (a ^ 2 * (4 - affineEndpoint c a)) := by
  unfold secondaryJoin secondaryRate startingPolynomial
  field_simp [ha, hendpoint]
  unfold affineEndpoint
  ring_nf

theorem slack_difference_identity {c a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (affineEndpoint c b / b - primaryJoin c a b) -
      (affineEndpoint c a / a - secondaryJoin c a b) =
      c * (a - b) / (a * b) + (1 - a) * (1 - b) := by
  unfold affineEndpoint primaryJoin secondaryJoin
  field_simp [ha, hb]
  ring

theorem secondary_slack_pos {c a b : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hroot : secondaryResidual c a b = 0) :
    secondaryJoin c a b < affineEndpoint c a / a := by
  have hbounds := affineEndpoint_bounds hc ⟨ha.1.le, ha.2.le⟩
  have hendpoint : 4 - affineEndpoint c a ≠ 0 := by linarith [hbounds.2]
  have hnegative : (c - 1) * (a ^ 2 + 2 * a - 1) - 3 * a < 0 := by
    by_cases hsign : a ^ 2 + 2 * a - 1 ≤ 0
    · have hproduct := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc.1) hsign
      linarith [ha.1]
    · have hproduct := mul_nonneg (by linarith [hc.2] : 0 ≤ 2 - c)
        (le_of_not_ge hsign)
      have hsquare : a ^ 2 < a := by
        nlinarith [mul_pos ha.1 (sub_pos.mpr ha.2)]
      nlinarith
  rw [secondaryRate_eq_of_secondaryResidual_zero hc ⟨ha.1, ha.2.le⟩ hroot]
  have hidentity := secondary_slack_identity (ne_of_gt ha.1) hendpoint
  have hpositive : 0 < -(1 - a) * affineEndpoint c a *
      ((c - 1) * (a ^ 2 + 2 * a - 1) - 3 * a) := by
    apply mul_pos_of_neg_of_neg _ hnegative
    apply mul_neg_of_neg_of_pos
    · linarith [ha.2]
    · linarith [hbounds.1]
  have hquotient := div_pos hpositive (denominator_pos hc ⟨ha.1, ha.2.le⟩)
  linarith

theorem primary_slack_pos {c a b : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : 0 < b) (hba : b < a)
    (hroot : secondaryResidual c a b = 0) :
    primaryJoin c a b < affineEndpoint c b / b := by
  have hsecondary := secondary_slack_pos hc ha hroot
  have hidentity := slack_difference_identity (c := c)
    (ne_of_gt ha.1) (ne_of_gt hb)
  have hquotient : 0 < c * (a - b) / (a * b) := by
    exact div_pos (mul_pos (by linarith [hc.1]) (sub_pos.mpr hba)) (mul_pos ha.1 hb)
  have hproduct : 0 < (1 - a) * (1 - b) := by
    exact mul_pos (sub_pos.mpr ha.2) (by linarith [ha.2])
  linarith

end Math.PairedPhasePolynomialRoots
