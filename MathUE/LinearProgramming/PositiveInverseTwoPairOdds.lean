import MathUE.LinearProgramming.CrossedMatchingPositiveOdds
import MathUE.Topology.PositiveCoordinateRadialFixedPoint

/-! # Two-pair odds with a constant strictly positive inverse

The singleton matrix need not have the crossed-matching sign pattern.
Nonnegative participant increments and nonpositive passive increments make
the variable matrix literally constant. No Q implication is asserted.
-/

noncomputable section

namespace Math.CrossedMatching

open Set LinearProgramming
open scoped Matrix

theorem variableMatrix_eq_of_premium_nonnegative_passive_nonpositive
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (premium passive point : Fin 4 → ℝ)
    (hpremium : ∀ i, 0 ≤ premium i) (hpassive : ∀ i, passive i ≤ 0) :
    variableMatrix matrix premium passive point = matrix := by
  funext i j
  simp only [variableMatrix, max_eq_right (neg_nonpos.mpr (hpremium i)),
    max_eq_right (hpassive i), zero_mul, ite_self, add_zero]

theorem exists_constant_positive_inverse_bounds
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hinverse : HasStrictlyPositiveInverse matrix) :
    ∃ lower upper : ℝ, 0 < lower ∧
      ∀ i j, lower ≤ matrix⁻¹ i j ∧ matrix⁻¹ i j ≤ upper := by
  obtain ⟨lower, upper, hlower, hbounds⟩ :=
    exists_uniform_positive_inverse_entry_bounds_on_compact
      (fun _ : Unit => matrix) Set.univ isCompact_univ continuous_const.continuousOn
      (fun _ _ => hinverse)
  exact ⟨lower, upper, hlower, hbounds () (Set.mem_univ _)⟩

theorem positiveNumerator_ray_cubic_lower
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (premium passive direction : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    {kappa radius : ℝ} (hkappa : 0 ≤ kappa) (hradius : 0 ≤ radius)
    (hdirection : ∀ i, kappa ≤ direction i) (i : Fin 4) :
    (premium i - matrix i (scheduled i)) * kappa ^ 3 * radius ^ 3 ≤
      positiveNumerator matrix premium passive (radius • direction) i := by
  let c := premium i - matrix i (scheduled i)
  have hc : 0 ≤ c := (sub_pos.mpr (hpremium i)).le
  have hcoordinate : ∀ j, 0 ≤ radius * direction j := fun j =>
    mul_nonneg hradius (hkappa.trans (hdirection j))
  have hbound : ∀ j, radius * kappa ≤ radius * direction j := fun j =>
    mul_le_mul_of_nonneg_left (hdirection j) hradius
  have hfirst := mul_le_mul (hbound (scheduled i)) (hbound (favorite i))
    (mul_nonneg hradius hkappa) (hcoordinate _)
  have htriple := mul_le_mul hfirst (hbound (other i))
    (mul_nonneg hradius hkappa) (mul_nonneg (hcoordinate _) (hcoordinate _))
  have hscaled := mul_le_mul_of_nonneg_left htriple hc
  have hquadratic : 0 ≤ c * (radius * direction (scheduled i)) *
      (radius * direction (favorite i)) :=
    mul_nonneg (mul_nonneg hc (hcoordinate _)) (hcoordinate _)
  have hlower := positiveNumerator_lower matrix premium passive (radius • direction)
    hpremium (fun j => hcoordinate j) i
  simp only [Pi.smul_apply, smul_eq_mul] at hlower
  dsimp [c] at hscaled hquadratic
  nlinarith

theorem exists_positive_odds_of_positive_inverse
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hdiagonal : ∀ i, matrix i i = 0)
    (hinverse : HasStrictlyPositiveInverse matrix) (premium passive : Fin 4 → ℝ)
    (hscheduled : ∀ i, matrix i (scheduled i) < 0)
    (hpremium : ∀ i, 0 ≤ premium i) (hpassive : ∀ i, passive i ≤ 0) :
    ∃ point : Fin 4 → ℝ, (∀ i, 0 < point i) ∧
      oddsMap matrix premium passive point = point ∧
      ∀ i, passiveEquation matrix premium passive point i = 0 := by
  have hgap : ∀ i, matrix i (scheduled i) < premium i := fun i =>
    (hscheduled i).trans_le (hpremium i)
  let field := oddsMap matrix premium passive
  let weight : (Fin 4 → ℝ) → ℝ := fun point =>
    ∑ i, positiveNumerator matrix premium passive point i
  obtain ⟨lower, upper, hlower, hentries⟩ :=
    exists_constant_positive_inverse_bounds matrix hinverse
  have hlowerUpper : lower ≤ upper := (hentries 0 0).1.trans (hentries 0 0).2
  have hupper : 0 < upper := hlower.trans_le hlowerUpper
  let kappa := lower / (4 * upper)
  have hkappa : 0 < kappa := div_pos hlower (by positivity)
  let c := premium 0 - matrix 0 (scheduled 0)
  have hc : 0 < c := sub_pos.mpr (hgap 0)
  let expansion := lower * c * kappa ^ 3
  have hexpansion : 0 < expansion := by positivity
  let outer := 1 + 1 / expansion
  have houter : 0 < outer := by positivity
  have houterOne : 1 < outer := by
    dsimp [outer]
    linarith [one_div_pos.mpr hexpansion]
  have hproduct : expansion * outer = expansion + 1 := by
    dsimp [outer]
    field_simp
  have houterSquare : 1 < expansion * outer ^ 2 := by
    have hpositive : 0 < expansion * outer := mul_pos hexpansion houter
    have hstrict := mul_lt_mul_of_pos_left houterOne hpositive
    nlinarith
  have hconstant : ∀ point, variableMatrix matrix premium passive point = matrix := fun point =>
    variableMatrix_eq_of_premium_nonnegative_passive_nonpositive
      matrix premium passive point hpremium hpassive
  have hnonnegative : ∀ point : Fin 4 → ℝ, (∀ i, 0 ≤ point i) →
      ∀ i, 0 ≤ positiveNumerator matrix premium passive point i := fun point hpoint =>
    positiveNumerator_nonnegative matrix premium passive point hgap hpoint
  have hfieldBounds : ∀ point : Fin 4 → ℝ, (∀ i, 0 ≤ point i) → ∀ i,
      lower * weight point ≤ field point i ∧ field point i ≤ upper * weight point := by
    intro point hpoint i
    dsimp only [field, weight, oddsMap]
    rw [hconstant]
    exact mulVec_entry_bounds matrix⁻¹ _ (hnonnegative point hpoint) hentries i
  have hfieldContinuous : ContinuousOn field (Set.Icc 0 (fun _ => outer)) :=
    (continuousOn_oddsMap_nonnegative_of_det_ne_zero matrix premium passive
      (fun point _ => by rw [hconstant]; exact hinverse.1)).mono
      (fun _ hpoint => hpoint.1)
  let coefficient : Fin 4 → ℝ := fun i =>
    (premium i - matrix i (scheduled i)) * (2 + outer) +
      max (premium i) 0 + max (-passive i) 0
  have hquadratic : ∀ direction : Fin 4 → ℝ,
      (∀ i, 0 ≤ direction i ∧ direction i ≤ 1) → ∀ radius : ℝ,
      0 < radius → radius ≤ outer →
        weight (radius • direction) ≤ (∑ i, coefficient i) * radius ^ 2 := by
    intro direction hdirection radius hradius hcap
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin 4) _ =>
      positiveNumerator_ray_upper matrix premium passive direction hgap hdirection
        hradius.le hcap i)
    simpa only [weight, coefficient, Finset.sum_mul] using hsum
  have hexcluded : ∀ point : Fin 4 → ℝ,
      (∀ i, 0 < point i ∧ lower / ((Fintype.card (Fin 4) : ℝ) * upper) * outer ≤ point i) →
      (∑ i, point i) = outer → ∀ scale : ℝ,
        0 < scale → scale ≤ 1 → field point ≠ scale • point := by
    intro point hpoint hsum scale hscale hscaleLe heigen
    have hpointNonnegative : ∀ i, 0 ≤ point i := fun i => (hpoint i).1.le
    let direction : Fin 4 → ℝ := fun i => point i / outer
    have hdirection : ∀ i, kappa ≤ direction i := by
      intro i
      apply (le_div_iff₀ houter).mpr
      simpa only [Fintype.card_fin, Nat.cast_ofNat, kappa] using (hpoint i).2
    have hray : outer • direction = point := by
      funext i
      change outer * (point i / outer) = point i
      field_simp [houter.ne']
    have hcubic := positiveNumerator_ray_cubic_lower matrix premium passive direction hgap
      hkappa.le houter.le hdirection 0
    rw [hray] at hcubic
    have hweightLower : positiveNumerator matrix premium passive point 0 ≤ weight point :=
      Finset.single_le_sum (fun i _ => hnonnegative point hpointNonnegative i)
        (Finset.mem_univ 0)
    have hfieldNonnegative : ∀ i, 0 ≤ field point i := fun i =>
      (mul_nonneg hlower.le (Finset.sum_nonneg
        (fun j _ => hnonnegative point hpointNonnegative j))).trans
        (hfieldBounds point hpointNonnegative i).1
    have hsingle : field point 0 ≤ ∑ i, field point i :=
      Finset.single_le_sum (fun i _ => hfieldNonnegative i) (Finset.mem_univ 0)
    have hmassBound : expansion * outer ^ 3 ≤ ∑ i, field point i := by
      have hscaled := mul_le_mul_of_nonneg_left hcubic hlower.le
      have hweightScaled := mul_le_mul_of_nonneg_left hweightLower hlower.le
      have hzero := (hfieldBounds point hpointNonnegative 0).1
      dsimp [expansion, c] at *
      nlinarith
    have hmass : (∑ i, field point i) ≤ outer := by
      rw [heigen]
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hsum]
      nlinarith
    nlinarith [mul_lt_mul_of_pos_right houterSquare houter]
  obtain ⟨point, hpoint, hfixed⟩ :=
    Math.exists_positive_fixedPoint_of_coordinate_radial_bounds field weight hlower houter
      hfieldContinuous
      (fun point hpoint => Finset.sum_pos (fun i _ => positiveNumerator_pos
        matrix premium passive point hgap (fun j => (hpoint j).1) i) Finset.univ_nonempty)
      (fun point hpoint => hfieldBounds point (fun i => (hpoint i).1)) hquadratic hexcluded
  have hcancel : variableMatrix matrix premium passive point *ᵥ point =
      positiveNumerator matrix premium passive point := by
    have hback : variableMatrix matrix premium passive point *ᵥ field point =
        positiveNumerator matrix premium passive point := by
      change variableMatrix matrix premium passive point *ᵥ oddsMap matrix premium passive point = _
      rw [oddsMap, hconstant, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hinverse.1), Matrix.one_mulVec]
    simpa only [hfixed] using hback
  refine ⟨point, hpoint, hfixed, ?_⟩
  intro i
  rw [passiveEquation_eq_numerator_sub_mulVec matrix hdiagonal premium passive point
    (fun j => (hpoint j).le) i, hcancel, sub_self]

end Math.CrossedMatching
