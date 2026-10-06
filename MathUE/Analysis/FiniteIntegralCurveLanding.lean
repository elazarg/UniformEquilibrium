module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.ProjIcc

/-! # Landing from finite integral control of actual displacement

The finite-length landing step of Milnor §15 uses absolute continuity of the
integral and completeness. This owner separates those generic facts: integral
control gives uniform continuity without completeness, then the actual curve
extends to the closed interval in a complete metric target. No boundedness or
finite coordinate limit is assumed. A sphere-valued application may land at
its chart pole.

Source: Milnor, *Dynamics in One Complex Variable*, §15,
https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf
-/

public section

noncomputable section

namespace Math.FiniteIntegralCurve

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X]

/-- Absolute continuity of an actual finite integral controls all short chords.
No measurability premise is needed for this ENNReal-only conclusion. -/
theorem uniformContinuous_of_edist_le_lintegral
    {a b : ℝ} {curve : Ioo a b → X} {speed : ℝ → ℝ≥0∞}
    {μ : Measure ℝ} (hmeasure : μ ≤ volume)
    (hfinite : (∫⁻ t, speed t ∂μ) ≠ ∞)
    (hchord : ∀ s t, edist (curve s) (curve t) ≤
      ∫⁻ r in uIoc (s : ℝ) (t : ℝ), speed r ∂μ) :
    UniformContinuous curve := by
  apply EMetric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_setLIntegral_lt_of_measure_lt hfinite hε.ne'
  refine ⟨δ, hδ, fun {s t} hst => (hchord s t).trans_lt (hsmall _ ?_)⟩
  calc
    μ (uIoc (s : ℝ) (t : ℝ)) ≤ volume (uIoc (s : ℝ) (t : ℝ)) := hmeasure _
    _ = edist s t := by
      rw [Real.volume_uIoc, Subtype.edist_eq, edist_dist, Real.dist_eq]
      rw [abs_sub_comm]
    _ < δ := hst

/-- Dense uniform extension supplies actual values at both missing endpoints. -/
theorem exists_uniformContinuous_extension [CompleteSpace X]
    {a b : ℝ} (hab : a < b) {curve : Ioo a b → X}
    (hcurve : UniformContinuous curve) :
    ∃ extension : Icc a b → X, UniformContinuous extension ∧
      ∀ t : Ioo a b, extension ⟨t, t.property.1.le, t.property.2.le⟩ = curve t := by
  let inclusion : Ioo a b → Icc a b := Set.inclusion Ioo_subset_Icc_self
  have hisometry : Isometry inclusion := fun _ _ => rfl
  have hdense : DenseRange inclusion := by
    apply (denseRange_inclusion_iff Ioo_subset_Icc_self).mpr
    rw [closure_Ioo hab.ne]
  let extension := hisometry.isUniformInducing.isDenseInducing hdense |>.extend curve
  refine ⟨extension,
    uniformContinuous_uniformly_extend hisometry.isUniformInducing hdense hcurve, ?_⟩
  intro t
  exact uniformly_extend_of_ind hisometry.isUniformInducing hdense hcurve t

theorem exists_landing_of_edist_le_lintegral [CompleteSpace X]
    {a b : ℝ} (hab : a < b) {curve : Ioo a b → X} {speed : ℝ → ℝ≥0∞}
    {μ : Measure ℝ} (hmeasure : μ ≤ volume)
    (hfinite : (∫⁻ t, speed t ∂μ) ≠ ∞)
    (hchord : ∀ s t, edist (curve s) (curve t) ≤
      ∫⁻ r in uIoc (s : ℝ) (t : ℝ), speed r ∂μ) :
    ∃ extension : Icc a b → X, UniformContinuous extension ∧
      ∀ t : Ioo a b, extension ⟨t, t.property.1.le, t.property.2.le⟩ = curve t :=
  exists_uniformContinuous_extension hab
    (uniformContinuous_of_edist_le_lintegral hmeasure hfinite hchord)

/-- An actual closed-interval extension gives the literal one-sided limits of
the original curve, regardless of its assigned values outside the interval. -/
theorem endpoint_limits_of_extension
    {a b : ℝ} (hab : a < b) {curve : ℝ → X} {extension : Icc a b → X}
    (hcontinuous : Continuous extension)
    (hagrees : ∀ t : Ioo a b,
      extension ⟨t, t.property.1.le, t.property.2.le⟩ = curve t) :
    Tendsto curve (𝓝[>] a) (𝓝 (extension ⟨a, le_rfl, hab.le⟩)) ∧
      Tendsto curve (𝓝[<] b) (𝓝 (extension ⟨b, hab.le, le_rfl⟩)) := by
  have hglobal : Continuous (fun t => extension (projIcc a b hab.le t)) :=
    hcontinuous.comp continuous_projIcc
  have hagreesAt (x : ℝ) :
      (fun t => extension (projIcc a b hab.le t)) =ᶠ[𝓝[Ioo a b] x] curve := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [projIcc_of_mem _ ⟨ht.1.le, ht.2.le⟩]
    exact hagrees ⟨t, ht⟩
  constructor
  · have h := hglobal.continuousAt.continuousWithinAt
      (s := Ioo a b) (x := a)
    have hlimit := Filter.Tendsto.congr' (hagreesAt a) h
    simpa only [nhdsWithin_Ioo_eq_nhdsGT hab, projIcc_left] using hlimit
  · have h := hglobal.continuousAt.continuousWithinAt
      (s := Ioo a b) (x := b)
    have hlimit := Filter.Tendsto.congr' (hagreesAt b) h
    simpa only [nhdsWithin_Ioo_eq_nhdsLT hab, projIcc_right] using hlimit

end Math.FiniteIntegralCurve
