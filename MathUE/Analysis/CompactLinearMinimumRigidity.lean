import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-! # Rigidity of compact linear minima

A compact nonempty coefficient set defines a concave Lipschitz infimum of
linear forms. At every differentiability point all minimizing coefficient
vectors coincide. Such a point exists in every nonempty open set by the
existing finite-dimensional Rademacher theorem. No index inhabitation or
uniqueness of points in a carrier mapped to these coefficients is required.
-/

noncomputable section

namespace Math.CompactLinearMinimum

open Set MeasureTheory
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- The actual linear form associated with one finite coefficient vector. -/
def pairing (coefficient : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight (coefficient i)

@[simp] theorem pairing_apply (coefficient weights : ι → ℝ) :
    pairing coefficient weights = ∑ i, weights i * coefficient i := by
  simp only [pairing, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The infimum is over one fixed coefficient set, for every real weight vector. -/
def value (coefficients : Set (ι → ℝ)) (weights : ι → ℝ) : ℝ :=
  sInf ((fun coefficient => pairing coefficient weights) '' coefficients)

private theorem continuous_coefficient_evaluation (weights : ι → ℝ) :
    Continuous (fun coefficient : ι → ℝ => pairing coefficient weights) := by
  simpa only [pairing_apply, Pi.mul_apply] using
    (continuous_finsetSum (s := (Finset.univ : Finset ι)) fun i _ =>
      continuous_const.mul (continuous_apply i))

theorem value_eq_of_isMinOn (coefficients : Set (ι → ℝ)) (weights coefficient : ι → ℝ)
    (hcoefficient : coefficient ∈ coefficients)
    (hminimum : IsMinOn (fun candidate => pairing candidate weights) coefficients coefficient) :
    value coefficients weights = pairing coefficient weights := by
  have hleast : IsLeast ((fun candidate => pairing candidate weights) '' coefficients)
      (pairing coefficient weights) := by
    refine ⟨⟨coefficient, hcoefficient, rfl⟩, ?_⟩
    rintro _ ⟨candidate, hcandidate, rfl⟩
    exact hminimum hcandidate
  exact hleast.csInf_eq

/-- Every weight has an actual minimizing coefficient in the compact set. -/
theorem exists_minimizer {coefficients : Set (ι → ℝ)}
    (hcompact : IsCompact coefficients) (hnonempty : coefficients.Nonempty)
    (weights : ι → ℝ) :
    ∃ coefficient ∈ coefficients,
      pairing coefficient weights = value coefficients weights ∧
      IsMinOn (fun candidate => pairing candidate weights) coefficients coefficient := by
  obtain ⟨coefficient, hcoefficient, hminimum⟩ :=
    hcompact.exists_isMinOn hnonempty (continuous_coefficient_evaluation weights).continuousOn
  exact ⟨coefficient, hcoefficient,
    (value_eq_of_isMinOn coefficients weights coefficient hcoefficient hminimum).symm, hminimum⟩

theorem value_le {coefficients : Set (ι → ℝ)}
    (hcompact : IsCompact coefficients)
    (weights : ι → ℝ) {coefficient : ι → ℝ} (hcoefficient : coefficient ∈ coefficients) :
    value coefficients weights ≤ pairing coefficient weights := by
  obtain ⟨old, _, heq, hminimum⟩ :=
    exists_minimizer hcompact ⟨coefficient, hcoefficient⟩ weights
  rw [← heq]
  exact hminimum hcoefficient

/-- The infimum is concave without convexifying its coefficient set. -/
theorem concaveOn_value {coefficients : Set (ι → ℝ)}
    (hcompact : IsCompact coefficients) (hnonempty : coefficients.Nonempty) :
    ConcaveOn ℝ univ (value coefficients) := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ a b ha hb _
  obtain ⟨coefficient, hcoefficient, heq, _⟩ :=
    exists_minimizer hcompact hnonempty (a • first + b • second)
  rw [← heq, map_add, map_smul, map_smul]
  exact add_le_add
    (smul_le_smul_of_nonneg_left (value_le hcompact first hcoefficient) ha)
    (smul_le_smul_of_nonneg_left (value_le hcompact second hcoefficient) hb)

private theorem abs_pairing_sub_le (coefficient first second : ι → ℝ)
    {bound : ℝ} (hcoefficient : ∀ i, |coefficient i| ≤ bound) :
    |pairing coefficient first - pairing coefficient second| ≤
      (Fintype.card ι : ℝ) * bound * dist first second := by
  rw [pairing_apply, pairing_apply, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (first i * coefficient i - second i * coefficient i)| ≤
        ∑ i, |first i * coefficient i - second i * coefficient i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |first i - second i| * |coefficient i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← sub_mul, abs_mul]
    _ ≤ ∑ _i : ι, dist first second * bound := by
      apply Finset.sum_le_sum
      intro i _
      have hcoordinate : |first i - second i| ≤ dist first second := by
        rw [← Real.dist_eq]
        exact dist_le_pi_dist first second i
      exact mul_le_mul hcoordinate (hcoefficient i) (abs_nonneg _) dist_nonneg
    _ = (Fintype.card ι : ℝ) * bound * dist first second := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Compactness supplies the global Lipschitz bound; callers supply no bound oracle. -/
theorem exists_lipschitzWith_value {coefficients : Set (ι → ℝ)}
    (hcompact : IsCompact coefficients) (hnonempty : coefficients.Nonempty) :
    ∃ constant : NNReal, LipschitzWith constant (value coefficients) := by
  obtain ⟨bound, hbound, hnorm⟩ := hcompact.isBounded.exists_pos_norm_le
  let constant : NNReal := ⟨(Fintype.card ι : ℝ) * bound, by positivity⟩
  refine ⟨constant, LipschitzWith.of_dist_le_mul ?_⟩
  intro first second
  obtain ⟨left, hleft, hleftValue, _⟩ := exists_minimizer hcompact hnonempty first
  obtain ⟨right, hright, hrightValue, _⟩ := exists_minimizer hcompact hnonempty second
  have hcoefficient (coefficient : ι → ℝ) (hmem : coefficient ∈ coefficients) (i : ι) :
      |coefficient i| ≤ bound := by
    have hcoordinate : |coefficient i| ≤ ‖coefficient‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm coefficient i
    exact hcoordinate.trans (hnorm coefficient hmem)
  have hupper := value_le hcompact first hright
  have hlower := value_le hcompact second hleft
  have hrightError := abs_pairing_sub_le right first second (hcoefficient right hright)
  have hleftError := abs_pairing_sub_le left first second (hcoefficient left hleft)
  rw [Real.dist_eq]
  change |value coefficients first - value coefficients second| ≤
    ((Fintype.card ι : ℝ) * bound) * dist first second
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hrightError).2, (abs_le.mp hleftError).1]

/-- Every minimizing linear form has the derivative of the infimum at a differentiability point. -/
theorem pairing_eq_fderiv_of_minimizer {coefficients : Set (ι → ℝ)}
    (hcompact : IsCompact coefficients)
    (weights coefficient : ι → ℝ) (hcoefficient : coefficient ∈ coefficients)
    (hminimum : IsMinOn (fun candidate => pairing candidate weights) coefficients coefficient)
    (hdifferentiable : DifferentiableAt ℝ (value coefficients) weights) :
    pairing coefficient = fderiv ℝ (value coefficients) weights := by
  have heq := value_eq_of_isMinOn coefficients weights coefficient hcoefficient hminimum
  have hglobal : IsMinOn (fun point => pairing coefficient point - value coefficients point)
      univ weights := by
    intro point _
    change pairing coefficient weights - value coefficients weights ≤
      pairing coefficient point - value coefficients point
    rw [heq, sub_self]
    exact sub_nonneg.mpr (value_le hcompact point hcoefficient)
  have hzero := (hglobal.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero
    ((pairing coefficient).hasFDerivAt.sub hdifferentiable.hasFDerivAt)
  exact sub_eq_zero.mp hzero

/-- Differentiability makes all minimizing coefficient vectors equal, not all underlying pairs. -/
theorem minimizers_eq_of_differentiableAt {coefficients : Set (ι → ℝ)}
    (hcompact : IsCompact coefficients)
    (weights first second : ι → ℝ) (hfirst : first ∈ coefficients)
    (hsecond : second ∈ coefficients)
    (hfirstMin : IsMinOn (fun candidate => pairing candidate weights) coefficients first)
    (hsecondMin : IsMinOn (fun candidate => pairing candidate weights) coefficients second)
    (hdifferentiable : DifferentiableAt ℝ (value coefficients) weights) : first = second := by
  classical
  have heq := (pairing_eq_fderiv_of_minimizer hcompact weights first hfirst
    hfirstMin hdifferentiable).trans
    (pairing_eq_fderiv_of_minimizer hcompact weights second hsecond
      hsecondMin hdifferentiable).symm
  funext i
  have hcoordinate := DFunLike.congr_fun heq (Pi.single i 1)
  simpa only [pairing_apply, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hcoordinate

/-- One weight in every nonempty open region has one coefficient vector for every minimum. -/
theorem exists_mem_open_all_minimizers_eq {coefficients : Set (ι → ℝ)}
    (hcompact : IsCompact coefficients) (hnonempty : coefficients.Nonempty)
    {region : Set (ι → ℝ)} (hopen : IsOpen region) (hregion : region.Nonempty) :
    ∃ weights ∈ region, ∃ coefficient ∈ coefficients,
      IsMinOn (fun candidate => pairing candidate weights) coefficients coefficient ∧
      ∀ candidate ∈ coefficients,
        IsMinOn (fun other => pairing other weights) coefficients candidate →
          candidate = coefficient := by
  obtain ⟨constant, hlipschitz⟩ := exists_lipschitzWith_value hcompact hnonempty
  have hae : ∀ᵐ weights ∂(volume : Measure (ι → ℝ)),
      DifferentiableAt ℝ (value coefficients) weights := hlipschitz.ae_differentiableAt
  obtain ⟨weights, hdifferentiable, hweights⟩ :=
    (MeasureTheory.Measure.dense_of_ae hae).exists_mem_open hopen hregion
  obtain ⟨coefficient, hcoefficient, _, hminimum⟩ := exists_minimizer hcompact hnonempty weights
  refine ⟨weights, hweights, coefficient, hcoefficient, hminimum, ?_⟩
  intro candidate hcandidate hcandidateMin
  exact minimizers_eq_of_differentiableAt hcompact weights candidate coefficient
    hcandidate hcoefficient hcandidateMin hminimum hdifferentiable

end Math.CompactLinearMinimum
