import MathUE.Topology.NormalizedRadialFixedPoint
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Positive finite-coordinate radial fixed points

Uniform coordinate bounds give an invariant normalized cone. A quadratic
weight estimate fixes the inner radius; scaled-eigenpoint exclusion fixes the
outer radius. This conditional generic helper contains no game source data.
-/

noncomputable section

namespace Math

open Set

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem exists_positive_fixedPoint_of_coordinate_radial_bounds
    (field : (ι → ℝ) → ι → ℝ) (weight : (ι → ℝ) → ℝ)
    {lower upper outer coefficient : ℝ}
    (hlower : 0 < lower) (houter : 0 < outer)
    (hcontinuous : ContinuousOn field (Icc 0 (fun _ => outer)))
    (hweight : ∀ point : ι → ℝ, (∀ i, 0 < point i ∧ point i ≤ outer) → 0 < weight point)
    (hbounds : ∀ point : ι → ℝ, (∀ i, 0 ≤ point i ∧ point i ≤ outer) → ∀ i,
      lower * weight point ≤ field point i ∧ field point i ≤ upper * weight point)
    (hquadratic : ∀ direction : ι → ℝ, (∀ i, 0 ≤ direction i ∧ direction i ≤ 1) →
      ∀ radius : ℝ, 0 < radius → radius ≤ outer →
        weight (radius • direction) ≤ coefficient * radius ^ 2)
    (hexcluded : ∀ point : ι → ℝ,
      (∀ i, 0 < point i ∧ lower / ((Fintype.card ι : ℝ) * upper) * outer ≤ point i) →
      (∑ i, point i) = outer →
      ∀ scale : ℝ, 0 < scale → scale ≤ 1 → field point ≠ scale • point) :
    ∃ point : ι → ℝ, (∀ i, 0 < point i) ∧ field point = point := by
  let test : ι → ℝ := fun _ => outer / 2
  have htest : ∀ i, 0 < test i ∧ test i ≤ outer := fun _ =>
    ⟨half_pos houter, by dsimp [test]; linarith⟩
  have htestWeight := hweight test htest
  have htestBounds := hbounds test (fun i => ⟨(htest i).1.le, (htest i).2⟩)
    (Classical.arbitrary ι)
  have hlowerUpper : lower ≤ upper := by
    by_contra hnot
    have hstrict := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) htestWeight
    linarith [htestBounds.1, htestBounds.2]
  have htestQuadratic := hquadratic (fun _ => 1) (fun _ => ⟨by norm_num, le_rfl⟩)
    (outer / 2) (half_pos houter) (by linarith)
  have htestRay : (outer / 2) • (fun _ : ι => (1 : ℝ)) = test := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, test]
  rw [htestRay] at htestQuadratic
  have hcoefficient : 0 < coefficient := by
    by_contra hnot
    have hnonpositive := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot)
      (sq_nonneg (outer / 2))
    linarith
  let count : ℝ := Fintype.card ι
  have hcount : 0 < count := by
    change 0 < (Fintype.card ι : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hupper : 0 < upper := hlower.trans_le hlowerUpper
  let mass : (ι → ℝ) → ℝ := fun point => ∑ i, point i
  let kappa := lower / (count * upper)
  have hkappa : 0 < kappa := div_pos hlower (mul_pos hcount hupper)
  have hkappaLe : kappa ≤ 1 / count := by
    apply (div_le_div_iff₀ (mul_pos hcount hupper) hcount).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlowerUpper hcount.le]
  let directions : Set (ι → ℝ) :=
    {point | (∀ i, kappa ≤ point i) ∧ mass point = 1}
  have hcoordinates : ∀ point ∈ directions, ∀ i, 0 ≤ point i ∧ point i ≤ 1 := by
    intro point hpoint i
    have hnonnegative : ∀ j, 0 ≤ point j := fun j => hkappa.le.trans (hpoint.1 j)
    refine ⟨hnonnegative i, ?_⟩
    have hsum := Finset.single_le_sum (fun j _ => hnonnegative j) (Finset.mem_univ i)
    exact hsum.trans_eq hpoint.2
  have hmass : Continuous mass := continuous_finsetSum _ (fun i _ => continuous_apply i)
  have hconvex : Convex ℝ directions := by
    intro x hx y hy a b ha hb hab
    constructor
    · intro i
      change kappa ≤ a * x i + b * y i
      have hxbound := mul_le_mul_of_nonneg_left (hx.1 i) ha
      have hybound := mul_le_mul_of_nonneg_left (hy.1 i) hb
      nlinarith
    · change (∑ i, (a * x i + b * y i)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      change a * mass x + b * mass y = 1
      rw [hx.2, hy.2, mul_one, mul_one, hab]
  have hclosed : IsClosed directions := by
    have hcoordinatesClosed : IsClosed {point : ι → ℝ | ∀ i, kappa ≤ point i} := by
      have hset : {point : ι → ℝ | ∀ i, kappa ≤ point i} =
          ⋂ i : ι, {point | kappa ≤ point i} := by ext point; simp
      rw [hset]
      exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
    exact hcoordinatesClosed.inter (isClosed_eq hmass continuous_const)
  have hcompact : IsCompact directions := isCompact_Icc.of_isClosed_subset hclosed (by
    intro point hpoint
    exact ⟨fun i => hpoint.1 i, fun i => (hcoordinates point hpoint i).2⟩)
  have hnonempty : directions.Nonempty := by
    refine ⟨fun _ => 1 / count, fun _ => hkappaLe, ?_⟩
    change (∑ _ : ι, 1 / count) = 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change count * (1 / count) = 1
    exact mul_one_div_cancel hcount.ne'
  let inner := min (outer / 2) (1 / (2 * count * upper * coefficient))
  have hinner : 0 < inner := lt_min (half_pos houter) (by positivity)
  have hradii : inner < outer := (min_le_left _ _).trans_lt (by linarith)
  have hray : ∀ point ∈ directions, ∀ radius ∈ Icc inner outer,
      ∀ i, 0 < (radius • point) i ∧ (radius • point) i ≤ outer := by
    intro point hpoint radius hradius i
    have hcoord := hcoordinates point hpoint i
    change 0 < radius * point i ∧ radius * point i ≤ outer
    exact ⟨mul_pos (hinner.trans_le hradius.1) (hkappa.trans_le (hpoint.1 i)),
      (mul_le_mul_of_nonneg_left hcoord.2 (hinner.trans_le hradius.1).le).trans
        (by simpa only [mul_one] using hradius.2)⟩
  have hfieldBounds : ∀ point ∈ directions, ∀ radius ∈ Icc inner outer, ∀ i,
      lower * weight (radius • point) ≤ field (radius • point) i ∧
        field (radius • point) i ≤ upper * weight (radius • point) := by
    intro point hpoint radius hradius i
    exact hbounds _ (fun j => ⟨(hray point hpoint radius hradius j).1.le,
      (hray point hpoint radius hradius j).2⟩) i
  have hfieldPositive : ∀ point ∈ directions, ∀ radius ∈ Icc inner outer, ∀ i,
      0 < field (radius • point) i := by
    intro point hpoint radius hradius i
    exact (mul_pos hlower (hweight _ (hray point hpoint radius hradius))).trans_le
      (hfieldBounds point hpoint radius hradius i).1
  have hmassPositive : ∀ point ∈ directions, ∀ radius ∈ Icc inner outer,
      0 < mass (field (radius • point)) := by
    intro point hpoint radius hradius
    exact Finset.sum_pos (fun i _ => hfieldPositive point hpoint radius hradius i)
      Finset.univ_nonempty
  have hmassUpper : ∀ point ∈ directions, ∀ radius ∈ Icc inner outer,
      mass (field (radius • point)) ≤ count * upper * weight (radius • point) := by
    intro point hpoint radius hradius
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (i : ι) _ =>
      (hfieldBounds point hpoint radius hradius i).2)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    change (∑ i, field (radius • point) i) ≤
      count * upper * weight (radius • point)
    change (∑ i, field (radius • point) i) ≤
      count * (upper * weight (radius • point)) at hsum
    nlinarith [hsum]
  have hdirection : ∀ point ∈ directions, ∀ radius ∈ Icc inner outer,
      (mass (field (radius • point)))⁻¹ • field (radius • point) ∈ directions := by
    intro point hpoint radius hradius
    have hpositive := hmassPositive point hpoint radius hradius
    constructor
    · intro i
      change lower / (count * upper) ≤
        (mass (field (radius • point)))⁻¹ * field (radius • point) i
      rw [← div_eq_inv_mul]
      apply (div_le_div_iff₀ (mul_pos hcount hupper) hpositive).mpr
      have hlowerAt := (hfieldBounds point hpoint radius hradius i).1
      have hupperAt := hmassUpper point hpoint radius hradius
      have hfirst := mul_le_mul_of_nonneg_left hupperAt hlower.le
      have hsecond := mul_le_mul_of_nonneg_left hlowerAt (mul_pos hcount hupper).le
      nlinarith
    · change (∑ i, (mass (field (radius • point)))⁻¹ * field (radius • point) i) = 1
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hpositive.ne'
  have hsmall : ∀ point ∈ directions, mass (field (inner • point)) / inner < 1 := by
    intro point hpoint
    have hquadraticAt := hquadratic point (hcoordinates point hpoint) inner hinner hradii.le
    have hup := hmassUpper point hpoint inner ⟨le_rfl, hradii.le⟩
    have hinnerBound : inner ≤ 1 / (2 * count * upper * coefficient) := min_le_right _ _
    have hlinear : inner * (2 * count * upper * coefficient) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 2 * count * upper * coefficient)).mp hinnerBound
    have hmassBound : mass (field (inner • point)) ≤
        count * upper * coefficient * inner ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hquadraticAt (mul_pos hcount hupper).le]
    apply (div_lt_iff₀ hinner).mpr
    nlinarith
  have hfieldContinuous : ContinuousOn (fun pair : (ι → ℝ) × ℝ =>
      field (pair.2 • pair.1)) (directions ×ˢ Icc inner outer) :=
    hcontinuous.comp (continuous_snd.smul continuous_fst).continuousOn (by
      intro pair hpair
      exact ⟨fun i => (hray pair.1 hpair.1 pair.2 hpair.2 i).1.le,
        fun i => (hray pair.1 hpair.1 pair.2 hpair.2 i).2⟩)
  have houterExcluded : ∀ point ∈ directions, ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
      field (outer • point) ≠ scale • (outer • point) := by
    intro point hpoint scale hscale hscaleLe
    have hpositive : ∀ i, 0 < (outer • point) i ∧
        lower / ((Fintype.card ι : ℝ) * upper) * outer ≤ (outer • point) i := by
      intro i
      refine ⟨(hray point hpoint outer ⟨hradii.le, le_rfl⟩ i).1, ?_⟩
      change kappa * outer ≤ outer * point i
      nlinarith [mul_le_mul_of_nonneg_left (hpoint.1 i) houter.le]
    apply hexcluded _ hpositive
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      change outer * mass point = outer
      rw [hpoint.2, mul_one]
    · exact hscale
    · exact hscaleLe
  obtain ⟨direction, hdirectionMem, radius, hradius, hfixed⟩ :=
    exists_fixedPoint_of_normalized_radial_map field mass hmass directions hconvex hcompact
      hnonempty hinner hradii hfieldContinuous hmassPositive hdirection hsmall houterExcluded
  exact ⟨radius • direction, fun i =>
    (hray direction hdirectionMem radius ⟨hradius.1.le, hradius.2.le⟩ i).1, hfixed⟩

end Math
