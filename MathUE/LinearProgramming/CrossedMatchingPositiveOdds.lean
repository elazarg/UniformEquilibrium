import MathUE.LinearProgramming.CrossedMatchingOdds
import MathUE.Topology.PositiveCoordinateRadialFixedPoint
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.Convex.Basic

noncomputable section
namespace Math.CrossedMatching
open Set LinearProgramming
open scoped Matrix


theorem positiveNumerator_pos
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (premium passive point : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    (hpoint : ∀ i, 0 < point i) (i : Fin 4) :
    0 < positiveNumerator matrix premium passive point i := by
  have hbase : 0 < (premium i - matrix i (scheduled i)) *
      point (scheduled i) * point (favorite i) * (1 + point (other i)) :=
    mul_pos (mul_pos (mul_pos (sub_pos.mpr (hpremium i)) (hpoint _))
      (hpoint _)) (by linarith [hpoint (other i)])
  exact hbase.trans_le
    (positiveNumerator_lower matrix premium passive point hpremium
      (fun j => (hpoint j).le) i)

theorem positiveNumerator_nonnegative
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (premium passive point : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    (hpoint : ∀ i, 0 ≤ point i) (i : Fin 4) :
    0 ≤ positiveNumerator matrix premium passive point i := by
  have hbase : 0 ≤ (premium i - matrix i (scheduled i)) * point (scheduled i) *
      point (favorite i) * (1 + point (other i)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sub_pos.mpr (hpremium i)).le (hpoint _))
      (hpoint _)) (by linarith [hpoint (other i)])
  exact hbase.trans (positiveNumerator_lower matrix premium passive point hpremium hpoint i)

theorem scaledEigenpointBound_pos
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (premium passive : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i) :
    0 < scaledEigenpointBound matrix premium passive := by
  unfold scaledEigenpointBound
  apply Finset.sum_pos
  · intro i _
    exact div_pos ((hsigns.favorite_pos i).trans_le (le_max_left _ _))
      (sub_pos.mpr (hpremium i))
  · exact Finset.univ_nonempty

theorem positiveNumerator_ray_upper
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (premium passive direction : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    (hdirection : ∀ i, 0 ≤ direction i ∧ direction i ≤ 1)
    {radius outer : ℝ} (hradius : 0 ≤ radius) (houter : radius ≤ outer)
    (i : Fin 4) :
    positiveNumerator matrix premium passive (radius • direction) i ≤
      ((premium i - matrix i (scheduled i)) * (2 + outer) +
        max (premium i) 0 + max (-passive i) 0) * radius ^ 2 := by
  let c := premium i - matrix i (scheduled i)
  let a := radius * direction (scheduled i)
  let f := radius * direction (favorite i)
  let o := radius * direction (other i)
  have hc : 0 ≤ c := (sub_pos.mpr (hpremium i)).le
  have ha : 0 ≤ a ∧ a ≤ radius := by
    exact ⟨mul_nonneg hradius (hdirection _).1,
      (mul_le_mul_of_nonneg_left (hdirection _).2 hradius).trans_eq (mul_one _)⟩
  have hf : 0 ≤ f ∧ f ≤ radius := by
    exact ⟨mul_nonneg hradius (hdirection _).1,
      (mul_le_mul_of_nonneg_left (hdirection _).2 hradius).trans_eq (mul_one _)⟩
  have ho : 0 ≤ o ∧ o ≤ radius := by
    exact ⟨mul_nonneg hradius (hdirection _).1,
      (mul_le_mul_of_nonneg_left (hdirection _).2 hradius).trans_eq (mul_one _)⟩
  have hfo : f * o ≤ radius ^ 2 := by nlinarith
  have haf : a * f ≤ radius ^ 2 := by nlinarith
  have hao : a * o ≤ radius ^ 2 := by nlinarith
  have hafo : a * (f * o) ≤ outer * radius ^ 2 :=
    (mul_le_mul_of_nonneg_left hfo ha.1).trans
      (mul_le_mul_of_nonneg_right (ha.2.trans houter) (sq_nonneg _))
  have hfirst : c * a * (f + o + f * o) ≤ c * (2 + outer) * radius ^ 2 := by
    have hsum : a * (f + o + f * o) ≤ (2 + outer) * radius ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsum hc]
  have hdivision : max (premium i) 0 * a ^ 2 / (1 + a) ≤
      max (premium i) 0 * radius ^ 2 := by
    apply (div_le_iff₀ (by linarith [ha.1])).mpr
    have hsquare : a ^ 2 ≤ radius ^ 2 := by nlinarith
    have hbase := mul_le_mul_of_nonneg_left hsquare (le_max_right (premium i) 0)
    have hnonnegative : 0 ≤ max (premium i) 0 * radius ^ 2 :=
      mul_nonneg (le_max_right _ _) (sq_nonneg _)
    nlinarith
  have hlast := mul_le_mul_of_nonneg_left hfo (le_max_right (-passive i) 0)
  change c * a * (f + o + f * o) +
      max (premium i) 0 * a ^ 2 / (1 + a) + max (-passive i) 0 * f * o ≤ _
  nlinarith

theorem passiveEquation_eq_numerator_sub_mulVec
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hdiagonal : ∀ i, matrix i i = 0)
    (premium passive point : Fin 4 → ℝ) (hpoint : ∀ i, 0 ≤ point i)
    (i : Fin 4) :
    passiveEquation matrix premium passive point i =
      positiveNumerator matrix premium passive point i -
        (variableMatrix matrix premium passive point *ᵥ point) i := by
  have hdenom : 1 + point (scheduled i) ≠ 0 := by
    linarith [hpoint (scheduled i)]
  have hp : max (premium i) 0 - max (-premium i) 0 = premium i :=
    posPart_sub_negPart (premium i)
  have hk : max (passive i) 0 - max (-passive i) 0 = passive i :=
    posPart_sub_negPart (passive i)
  have hrow : (matrix *ᵥ point) i =
      matrix i (favorite i) * point (favorite i) +
      matrix i (scheduled i) * point (scheduled i) +
      matrix i (other i) * point (other i) := by
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, favorite, scheduled,
        other, hdiagonal] <;> ring
  have hvariable : (variableMatrix matrix premium passive point *ᵥ point) i =
      (matrix *ᵥ point) i +
      max (-premium i) 0 * point (scheduled i) ^ 2 / (1 + point (scheduled i)) +
      max (passive i) 0 * point (other i) * point (favorite i) := by
    fin_cases i <;>
      simp [variableMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        favorite, scheduled, other] <;> ring
  rw [hvariable, hrow]
  unfold passiveEquation positiveNumerator
  field_simp [hdenom]
  linear_combination -(point (scheduled i)) ^ 2 * hp +
    point (favorite i) * point (other i) * (1 + point (scheduled i)) * hk

theorem passiveEquation_eq_zero_of_oddsMap_fixedPoint
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (hQ : IsStandardQ matrix) (premium passive point : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i)
    (hpoint : ∀ i, 0 ≤ point i)
    (hfixed : oddsMap matrix premium passive point = point) :
    ∀ i, passiveEquation matrix premium passive point i = 0 := by
  have hinverse := hasStrictlyPositiveInverse_variableMatrix_of_standardQ
    matrix hsigns hQ premium passive point hpremium hpoint
  have hcancel : variableMatrix matrix premium passive point *ᵥ point =
      positiveNumerator matrix premium passive point := by
    have hback : variableMatrix matrix premium passive point *ᵥ
        oddsMap matrix premium passive point =
          positiveNumerator matrix premium passive point := by
      rw [oddsMap, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hinverse.1), Matrix.one_mulVec]
    simpa only [hfixed] using hback
  intro i
  rw [passiveEquation_eq_numerator_sub_mulVec matrix hsigns.diagonal premium passive
    point hpoint i, hcancel, sub_self]

theorem mulVec_entry_bounds
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (vector : Fin 4 → ℝ)
    {lower upper : ℝ} (hvector : ∀ i, 0 ≤ vector i)
    (hbounds : ∀ i j, lower ≤ matrix i j ∧ matrix i j ≤ upper) (i : Fin 4) :
    lower * (∑ j, vector j) ≤ (matrix *ᵥ vector) i ∧
      (matrix *ᵥ vector) i ≤ upper * (∑ j, vector j) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (hbounds i j).1 (hvector j))
  · exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (hbounds i j).2 (hvector j))

theorem continuousOn_oddsMap_nonnegative_of_det_ne_zero
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (premium passive : Fin 4 → ℝ)
    (hdet : ∀ point ∈ Ici (0 : Fin 4 → ℝ),
      (variableMatrix matrix premium passive point).det ≠ 0) :
    ContinuousOn (oddsMap matrix premium passive) (Ici 0) := by
  have hmatrix := continuousOn_variableMatrix_nonnegative matrix premium passive
  have hinverse := continuousOn_matrix_inverse_of_det_ne_zero
    (variableMatrix matrix premium passive) (Ici 0) hmatrix
    hdet
  have hnumerator : ContinuousOn (positiveNumerator matrix premium passive) (Ici 0) := by
    apply continuousOn_pi.mpr
    intro i
    have hdenom : ∀ point ∈ Ici (0 : Fin 4 → ℝ),
        1 + point (scheduled i) ≠ 0 := by
      intro point hpoint
      have hnonnegative : 0 ≤ point (scheduled i) := hpoint (scheduled i)
      linarith
    unfold positiveNumerator
    exact
      (((continuous_const.mul (continuous_apply (scheduled i))).mul
        (((continuous_apply (favorite i)).add (continuous_apply (other i))).add
          ((continuous_apply (favorite i)).mul
            (continuous_apply (other i))))).continuousOn.add
        (((continuous_const.mul ((continuous_apply (scheduled i)).pow 2)).continuousOn).div
          (continuous_const.add (continuous_apply (scheduled i))).continuousOn hdenom)).add
        (((continuous_const.mul (continuous_apply (favorite i))).mul
          (continuous_apply (other i))).continuousOn)
  apply continuousOn_pi.mpr
  intro i
  change ContinuousOn (fun point => ∑ j,
    (variableMatrix matrix premium passive point)⁻¹ i j *
      positiveNumerator matrix premium passive point j) (Ici 0)
  apply continuousOn_finsetSum
  intro j _
  exact ((continuous_apply j).comp_continuousOn
    ((continuous_apply i).comp_continuousOn hinverse)).mul
    ((continuous_apply j).comp_continuousOn hnumerator)

private theorem continuousOn_oddsMap_nonnegative
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (hQ : IsStandardQ matrix) (premium passive : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i) :
    ContinuousOn (oddsMap matrix premium passive) (Ici 0) :=
  continuousOn_oddsMap_nonnegative_of_det_ne_zero matrix premium passive
    (fun point hpoint => (hasStrictlyPositiveInverse_variableMatrix_of_standardQ
      matrix hsigns hQ premium passive point hpremium hpoint).1)

/-- The selected odds are strictly positive in every coordinate and solve the
original signed passive equations, not merely a supplied eigenpoint problem. -/
theorem exists_positive_odds_of_matching_standardQ
    (matrix : Matrix (Fin 4) (Fin 4) ℝ) (hsigns : HasStrictMatchingSigns matrix)
    (hQ : IsStandardQ matrix) (premium passive : Fin 4 → ℝ)
    (hpremium : ∀ i, matrix i (scheduled i) < premium i) :
    ∃ point : Fin 4 → ℝ, (∀ i, 0 < point i) ∧
      oddsMap matrix premium passive point = point ∧
      ∀ i, passiveEquation matrix premium passive point i = 0 := by
  let field := oddsMap matrix premium passive
  let weight : (Fin 4 → ℝ) → ℝ := fun point =>
    ∑ i, positiveNumerator matrix premium passive point i
  let outer := scaledEigenpointBound matrix premium passive + 1
  have houter : 0 < outer := by
    have := scaledEigenpointBound_pos matrix hsigns premium passive hpremium
    dsimp [outer]
    linarith
  obtain ⟨lower, upper, hlower, hbounds⟩ :=
    exists_variableMatrix_inverse_bounds_on_cube
      matrix hsigns hQ premium passive hpremium outer
  have hfieldContinuous : ContinuousOn field (Icc 0 (fun _ => outer)) :=
    (continuousOn_oddsMap_nonnegative matrix hsigns hQ premium passive hpremium).mono
      (fun _ hpoint => hpoint.1)
  have hweightPositive : ∀ point : Fin 4 → ℝ,
      (∀ i, 0 < point i ∧ point i ≤ outer) → 0 < weight point := by
    intro point hpoint
    exact Finset.sum_pos (fun i _ => positiveNumerator_pos matrix premium passive point
      hpremium (fun j => (hpoint j).1) i) Finset.univ_nonempty
  have hfieldBounds : ∀ point : Fin 4 → ℝ,
      (∀ i, 0 ≤ point i ∧ point i ≤ outer) → ∀ i,
      lower * weight point ≤ field point i ∧ field point i ≤ upper * weight point := by
    intro point hpoint i
    exact mulVec_entry_bounds _ _
      (positiveNumerator_nonnegative matrix premium passive point hpremium
        (fun j => (hpoint j).1)) (hbounds point hpoint) i
  let coefficient : Fin 4 → ℝ := fun i =>
    (premium i - matrix i (scheduled i)) * (2 + outer) +
      max (premium i) 0 + max (-passive i) 0
  have hquadratic : ∀ direction : Fin 4 → ℝ,
      (∀ i, 0 ≤ direction i ∧ direction i ≤ 1) → ∀ radius : ℝ,
      0 < radius → radius ≤ outer →
        weight (radius • direction) ≤ (∑ i, coefficient i) * radius ^ 2 := by
    intro direction hdirection radius hradius hcap
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin 4) _ =>
      positiveNumerator_ray_upper matrix premium passive direction hpremium hdirection
        hradius.le hcap i)
    simpa only [weight, coefficient, Finset.sum_mul] using hsum
  have hexcluded : ∀ point : Fin 4 → ℝ,
      (∀ i, 0 < point i ∧ lower / ((Fintype.card (Fin 4) : ℝ) * upper) * outer ≤ point i) →
      (∑ i, point i) = outer → ∀ scale : ℝ,
        0 < scale → scale ≤ 1 → field point ≠ scale • point := by
    intro point hpoint hsum scale hscale hscaleLe heigen
    have hbound := scaled_eigenpoint_sum_lt_bound matrix hsigns hQ premium passive point
      hpremium (fun i => (hpoint i).1) hscale hscaleLe heigen
    rw [hsum] at hbound
    dsimp [outer] at hbound
    linarith
  obtain ⟨point, hpoint, hfixed⟩ :=
    Math.exists_positive_fixedPoint_of_coordinate_radial_bounds field weight hlower houter
      hfieldContinuous hweightPositive hfieldBounds hquadratic hexcluded
  exact ⟨point, hpoint, hfixed,
    passiveEquation_eq_zero_of_oddsMap_fixedPoint matrix hsigns hQ premium passive point
      hpremium (fun i => (hpoint i).le) hfixed⟩
end Math.CrossedMatching
