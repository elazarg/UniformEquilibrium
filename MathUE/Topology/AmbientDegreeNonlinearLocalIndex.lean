import MathUE.Topology.AmbientDegreeHomotopyNormalization
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Nonlinear local degree from the actual derivative

Local continuity and differentiability at a zero, with nonsingular derivative,
produce an isolating root-centered region and its determinant-sign degree.
The anti-Lipschitz bound and the zero-free linear comparison are derived, not
supplied. No continuous derivative or positive dimension is assumed.
-/

noncomputable section

namespace Math.Topology

open Set Filter _root_.Topology

variable {n : ℕ}

/-- A nonlinear zero has its actual derivative's determinant-sign degree on
a sufficiently small displayed region. Its closure contains no other zero.
Continuity is required only on a neighborhood of the displayed root. -/
theorem exists_ambientDegree_eq_sign_det_of_hasFDerivAt_on_nhds
    (field : (Fin n → ℝ) → Fin n → ℝ) (root : Fin n → ℝ)
    (derivative : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (neighborhood : Set (Fin n → ℝ)) (hneighborhood : neighborhood ∈ 𝓝 root)
    (hcontinuous : ContinuousOn field neighborhood) (hzero : field root = 0)
    (hdiff : HasFDerivAt field derivative root)
    (hdet : (LinearMap.toMatrix' derivative.toLinearMap).det ≠ 0) :
    ∃ radius : ℝ, 0 < radius ∧
      closure (Math.affineRootRegion root radius) ⊆ neighborhood ∧
      (∀ point ∈ closure (Math.affineRootRegion root radius),
        field point = 0 ↔ point = root) ∧
      ∃ hlocal : ContinuousOn field (closure (Math.affineRootRegion root radius)),
      ∃ hfrontier : ∀ point ∈ frontier (Math.affineRootRegion root radius), field point ≠ 0,
        ambientDegree field (Math.affineRootRegion root radius) 0
          (isOpen_affineRootRegion root radius) (isBounded_affineRootRegion root radius)
          hlocal hfrontier =
            (SignType.sign (LinearMap.toMatrix' derivative.toLinearMap).det : ℤ) := by
  let matrix := LinearMap.toMatrix' derivative.toLinearMap
  have hinjectiveMatrix : Function.Injective matrix.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det matrix).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hinjective : Function.Injective derivative.toLinearMap := by
    intro first last heq
    apply hinjectiveMatrix
    simpa only [matrix, LinearMap.toMatrix'_mulVec] using heq
  obtain ⟨K, hK, hanti⟩ := derivative.toLinearMap.exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hinjective)
  have hKReal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hcoercive : ∀ displacement, ‖displacement‖ ≤ (K : ℝ) * ‖derivative displacement‖ := by
    intro displacement
    have hbound := hanti.le_mul_dist displacement 0
    change dist displacement 0 ≤ (K : ℝ) *
      dist (derivative displacement) (derivative 0) at hbound
    simpa only [dist_zero_right, map_zero] using hbound
  let eta : ℝ := 1 / (2 * (K : ℝ))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hTaylor := hdiff.isLittleO.bound heta
  obtain ⟨taylorRadius, htaylorRadius, hTaylorBound⟩ := Metric.eventually_nhds_iff.mp hTaylor
  obtain ⟨neighborhoodRadius, hneighborhoodRadius, hNeighborhoodBound⟩ :=
    Metric.eventually_nhds_iff.mp hneighborhood
  let radius := min taylorRadius neighborhoodRadius / 2
  have hradius : 0 < radius := by dsimp [radius]; positivity
  let region := Math.affineRootRegion root radius
  have hsmall : ∀ point ∈ closure region,
      ‖point - root‖ < taylorRadius ∧ point ∈ neighborhood := by
    intro point hpoint
    have hcoordinates := closure_affineRootRegion_subset root hradius hpoint
    have hnorm : ‖point - root‖ ≤ radius := by
      apply (pi_norm_le_iff_of_nonneg hradius.le).mpr
      intro who
      change |point who - root who| ≤ radius
      exact abs_le.mpr ⟨by linarith [(hcoordinates who).1],
        by linarith [(hcoordinates who).2]⟩
    have hsmallTaylor : radius < taylorRadius := by
      have hmin := min_le_left taylorRadius neighborhoodRadius
      dsimp [radius]
      linarith
    have hsmallNeighborhood : radius < neighborhoodRadius := by
      have hmin := min_le_right taylorRadius neighborhoodRadius
      dsimp [radius]
      linarith
    refine ⟨hnorm.trans_lt hsmallTaylor, ?_⟩
    apply hNeighborhoodBound
    rw [dist_eq_norm]
    exact hnorm.trans_lt hsmallNeighborhood
  have hclosure : closure region ⊆ neighborhood := fun point hpoint => (hsmall point hpoint).2
  have hlocal : ContinuousOn field (closure region) := hcontinuous.mono hclosure
  have herror : ∀ point ∈ closure region,
      ‖field point - derivative (point - root)‖ ≤ eta * ‖point - root‖ := by
    intro point hpoint
    have hbound := hTaylorBound (show dist point root < taylorRadius from by
      rw [dist_eq_norm]
      exact (hsmall point hpoint).1)
    simpa only [hzero, sub_zero] using hbound
  let homotopy : (ℝ × (Fin n → ℝ)) → Fin n → ℝ := fun data =>
    (1 - data.1) • derivative (data.2 - root) + data.1 • field data.2
  have hhomotopyFormula : ∀ parameter point,
      homotopy (parameter, point) = derivative (point - root) +
        parameter • (field point - derivative (point - root)) := by
    intro parameter point
    ext who
    simp only [homotopy, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hhomotopyZero : ∀ parameter : Icc (0 : ℝ) 1, ∀ point ∈ closure region,
      homotopy ((parameter : ℝ), point) = 0 → point = root := by
    intro parameter point hpoint hvanish
    rw [hhomotopyFormula] at hvanish
    have heq := eq_neg_of_add_eq_zero_left hvanish
    have hlinearBound : ‖derivative (point - root)‖ ≤ eta * ‖point - root‖ := by
      calc
        _ = ‖(parameter : ℝ) • (field point - derivative (point - root))‖ := by
          exact (congrArg norm heq).trans (norm_neg _)
        _ = (parameter : ℝ) * ‖field point - derivative (point - root)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg parameter.property.1]
        _ ≤ 1 * ‖field point - derivative (point - root)‖ :=
          mul_le_mul_of_nonneg_right parameter.property.2 (norm_nonneg _)
        _ ≤ eta * ‖point - root‖ := by simpa only [one_mul] using herror point hpoint
    have hcoefficient : (K : ℝ) * eta = 1 / 2 := by
      dsimp [eta]
      field_simp [ne_of_gt hKReal]
    have hbound := (hcoercive (point - root)).trans
      (mul_le_mul_of_nonneg_left hlinearBound hKReal.le)
    rw [← mul_assoc, hcoefficient] at hbound
    have hnormZero : ‖point - root‖ = 0 := by
      linarith [norm_nonneg (point - root)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormZero)
  have hrootRegion : root ∈ region := by
    intro who
    constructor <;> linarith
  have hfrontier : ∀ parameter : Icc (0 : ℝ) 1, ∀ point ∈ frontier region,
      homotopy ((parameter : ℝ), point) ≠ 0 := by
    intro parameter point hpoint hvanish
    have heq := hhomotopyZero parameter point (frontier_subset_closure hpoint) hvanish
    subst point
    apply hpoint.2
    rw [(isOpen_affineRootRegion root radius).interior_eq]
    exact hrootRegion
  have hhomotopyContinuous : ContinuousOn homotopy (Icc (0 : ℝ) 1 ×ˢ closure region) := by
    have hlinear : Continuous (fun data : ℝ × (Fin n → ℝ) => derivative (data.2 - root)) :=
      derivative.continuous.comp (continuous_snd.sub continuous_const)
    exact ((continuous_const.sub continuous_fst).smul hlinear).continuousOn.add
      (continuous_fst.continuousOn.smul
        (hcontinuous.comp continuous_snd.continuousOn (fun _ hdata => hclosure hdata.2)))
  have hfirst : (fun point => homotopy (0, point)) = Math.affineRootField matrix root := by
    funext point
    simp [homotopy, Math.affineRootField, matrix, LinearMap.toMatrix'_mulVec]
  have hlast : (fun point => homotopy (1, point)) = field := by
    funext point
    simp [homotopy]
  have hfieldFrontier : ∀ point ∈ frontier region, field point ≠ 0 := by
    intro point hpoint hvanish
    apply hfrontier 1 point hpoint
    change homotopy ((1 : ℝ), point) = 0
    exact (congrFun hlast point).trans hvanish
  have hunique : ∀ point ∈ closure region, field point = 0 ↔ point = root := by
    intro point hpoint
    constructor
    · intro hvanish
      apply hhomotopyZero 1 point hpoint
      change homotopy ((1 : ℝ), point) = 0
      exact (congrFun hlast point).trans hvanish
    · rintro rfl
      exact hzero
  have hcomparison := ambientDegree_homotopy homotopy region 0
    (isOpen_affineRootRegion root radius) (isBounded_affineRootRegion root radius)
    hhomotopyContinuous hfrontier
  have hdegree : ambientDegree field region 0
      (isOpen_affineRootRegion root radius) (isBounded_affineRootRegion root radius)
      hlocal hfieldFrontier = (SignType.sign matrix.det : ℤ) := by
    have heq : ambientDegree (Math.affineRootField matrix root) region 0
        (isOpen_affineRootRegion root radius) (isBounded_affineRootRegion root radius)
        (Math.continuous_affineRootField matrix root).continuousOn
        (affineRootField_ne_zero_on_frontier matrix hdet root radius hradius) =
        ambientDegree field region 0
          (isOpen_affineRootRegion root radius) (isBounded_affineRootRegion root radius)
          hlocal hfieldFrontier := by
      simpa only [hfirst, hlast] using hcomparison
    exact heq.symm.trans
      (ambientDegree_affineRootField_eq_sign_det matrix hdet root radius hradius)
  exact ⟨radius, hradius, hclosure, hunique, hlocal, hfieldFrontier, hdegree⟩

/-- Global continuity is a convenient thin instance; the canonical local
theorem does not require continuity away from the root neighborhood. -/
theorem exists_ambientDegree_eq_sign_det_of_hasFDerivAt
    (field : (Fin n → ℝ) → Fin n → ℝ) (root : Fin n → ℝ)
    (derivative : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hcontinuous : Continuous field) (hzero : field root = 0)
    (hdiff : HasFDerivAt field derivative root)
    (hdet : (LinearMap.toMatrix' derivative.toLinearMap).det ≠ 0) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ point ∈ closure (Math.affineRootRegion root radius),
        field point = 0 ↔ point = root) ∧
      ∃ hlocal : ContinuousOn field (closure (Math.affineRootRegion root radius)),
      ∃ hfrontier : ∀ point ∈ frontier (Math.affineRootRegion root radius), field point ≠ 0,
        ambientDegree field (Math.affineRootRegion root radius) 0
          (isOpen_affineRootRegion root radius) (isBounded_affineRootRegion root radius)
          hlocal hfrontier =
            (SignType.sign (LinearMap.toMatrix' derivative.toLinearMap).det : ℤ) := by
  obtain ⟨radius, hradius, _hclosure, hunique, hlocal, hfrontier, hdegree⟩ :=
    exists_ambientDegree_eq_sign_det_of_hasFDerivAt_on_nhds field root derivative univ
      Filter.univ_mem hcontinuous.continuousOn hzero hdiff hdet
  exact ⟨radius, hradius, hunique, hlocal, hfrontier, hdegree⟩

end Math.Topology
