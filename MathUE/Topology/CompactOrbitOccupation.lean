/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Balanced occupation laws of compact forward paths

The empirical laws of consecutive edges of a path in a compact metrizable
Borel space have a weakly convergent subsequence.  Every such limit has equal
source and target marginals.  If the actual path lies in a closed edge
relation, the limiting law is supported on that relation.

This is a compact-dynamics theorem.  It does not realize an invariant law as
a stationary strategy or lift normalized state to an underlying game state.
-/

noncomputable section

namespace Math
namespace Topology

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {Point : Type*} [TopologicalSpace Point] [MeasurableSpace Point]
  [BorelSpace Point] [SecondCountableTopology Point]

/-- The uniform law of the first `horizon + 1` consecutive edges of a
forward path. -/
def empiricalEdgeLaw (path : ℕ → Point) (horizon : ℕ) :
    ProbabilityMeasure (Point × Point) :=
  let law := PMF.map
    (fun time : Fin (horizon + 1) ↦
      (path time, path (time + 1)))
    (PMF.uniformOfFintype (Fin (horizon + 1)))
  ⟨law.toMeasure, PMF.toMeasure.isProbabilityMeasure law⟩

/-- The uniform law of the first `horizon + 1` states of a forward path. -/
def empiricalStateLaw (path : ℕ → Point) (horizon : ℕ) :
    ProbabilityMeasure Point :=
  let law := PMF.map (fun time : Fin (horizon + 1) ↦ path time)
    (PMF.uniformOfFintype (Fin (horizon + 1)))
  ⟨law.toMeasure, PMF.toMeasure.isProbabilityMeasure law⟩

/-- A subsequential weak occupation limit of the actual empirical edge
laws.  The selected horizons remain explicit. -/
structure CompactForwardOccupation (path : ℕ → Point) where
  law : ProbabilityMeasure (Point × Point)
  horizons : ℕ → ℕ
  horizons_strictMono : StrictMono horizons
  empirical_tendsto :
    Tendsto (fun rank ↦ empiricalEdgeLaw path (horizons rank))
      atTop (nhds law)

namespace CompactForwardOccupation

variable {path : ℕ → Point}

theorem horizons_tendsto_atTop (occupation : CompactForwardOccupation path) :
    Tendsto occupation.horizons atTop atTop :=
  occupation.horizons_strictMono.tendsto_atTop

/-- The exact finite-horizon integral formula for empirical edge laws. -/
theorem integral_empiricalEdgeLaw_eq_average
    (path : ℕ → Point) (horizon : ℕ)
    (observable : BoundedContinuousFunction (Point × Point) ℝ) :
    ∫ edge, observable edge ∂(empiricalEdgeLaw path horizon :
        ProbabilityMeasure (Point × Point)) =
      (∑ time : Fin (horizon + 1),
        observable (path time, path (time + 1))) / (horizon + 1 : ℝ) := by
  let indexLaw := PMF.uniformOfFintype (Fin (horizon + 1))
  let edgeAt : Fin (horizon + 1) → Point × Point := fun time ↦
    (path time, path (time + 1))
  change ∫ edge, observable edge ∂(PMF.map edgeAt indexLaw).toMeasure = _
  rw [← PMF.toMeasure_map edgeAt indexLaw (measurable_of_finite _)]
  rw [integral_map (measurable_of_finite _).aemeasurable
    observable.continuous.aestronglyMeasurable]
  rw [PMF.integral_eq_sum]
  simp only [indexLaw, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.card_fin, smul_eq_mul]
  simp_rw [edgeAt]
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, Nat.cast_add, Nat.cast_one, mul_comm]

/-- The finite source-target discrepancy is exactly one endpoint term. -/
theorem integral_fst_sub_snd_empiricalEdgeLaw
    (path : ℕ → Point) (horizon : ℕ)
    (observable : BoundedContinuousFunction Point ℝ) :
    (∫ edge : Point × Point, observable edge.1
        ∂(empiricalEdgeLaw path horizon : Measure (Point × Point))) -
      ∫ edge : Point × Point, observable edge.2
        ∂(empiricalEdgeLaw path horizon : Measure (Point × Point)) =
      (observable (path 0) - observable (path (horizon + 1))) /
        (horizon + 1 : ℝ) := by
  let first : BoundedContinuousFunction (Point × Point) ℝ :=
    observable.compContinuous ⟨Prod.fst, continuous_fst⟩
  let second : BoundedContinuousFunction (Point × Point) ℝ :=
    observable.compContinuous ⟨Prod.snd, continuous_snd⟩
  rw [show (fun edge : Point × Point ↦ observable edge.1) = first from rfl]
  rw [show (fun edge : Point × Point ↦ observable edge.2) = second from rfl]
  rw [integral_empiricalEdgeLaw_eq_average path horizon first]
  rw [integral_empiricalEdgeLaw_eq_average path horizon second]
  simp only [first, second, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk]
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      ring

/-- Every bounded continuous observable has equal source and target averages
under the limiting edge law. -/
theorem integral_fst_eq_integral_snd
    (occupation : CompactForwardOccupation path)
    (observable : BoundedContinuousFunction Point ℝ) :
    (∫ edge : Point × Point, observable edge.1
        ∂(occupation.law : Measure (Point × Point))) =
      ∫ edge : Point × Point, observable edge.2
        ∂(occupation.law : Measure (Point × Point)) := by
  let first : BoundedContinuousFunction (Point × Point) ℝ :=
    observable.compContinuous ⟨Prod.fst, continuous_fst⟩
  let second : BoundedContinuousFunction (Point × Point) ℝ :=
    observable.compContinuous ⟨Prod.snd, continuous_snd⟩
  have hfirst :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      occupation.empirical_tendsto) first
  have hsecond :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      occupation.empirical_tendsto) second
  have hdenominator : Tendsto
      (fun rank ↦ (occupation.horizons rank + 1 : ℕ)) atTop atTop :=
    tendsto_add_atTop_nat 1 |>.comp occupation.horizons_tendsto_atTop
  have hlower : ∀ᶠ rank in atTop,
      -(2 * ‖observable‖) ≤
        observable (path 0) -
          observable (path (occupation.horizons rank + 1)) :=
    Eventually.of_forall fun rank ↦ by
      have hzero := observable.norm_coe_le_norm (path 0)
      have hrank := observable.norm_coe_le_norm
        (path (occupation.horizons rank + 1))
      rw [Real.norm_eq_abs] at hzero hrank
      linarith [(abs_le.mp hzero).1, (abs_le.mp hrank).2]
  have hupper : ∀ᶠ rank in atTop,
      observable (path 0) -
          observable (path (occupation.horizons rank + 1)) ≤
        2 * ‖observable‖ :=
    Eventually.of_forall fun rank ↦ by
      have hzero := observable.norm_coe_le_norm (path 0)
      have hrank := observable.norm_coe_le_norm
        (path (occupation.horizons rank + 1))
      rw [Real.norm_eq_abs] at hzero hrank
      linarith [(abs_le.mp hzero).2, (abs_le.mp hrank).1]
  have hdenominatorReal : Tendsto
      (fun rank ↦ ((occupation.horizons rank + 1 : ℕ) : ℝ))
        atTop atTop := by
    have hcast : Tendsto (fun value : ℕ ↦ (value : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    change Tendsto ((fun value : ℕ ↦ (value : ℝ)) ∘
      (fun rank ↦ occupation.horizons rank + 1)) atTop atTop
    exact hcast.comp hdenominator
  have hendpoint : Tendsto (fun rank ↦
      (observable (path 0) -
        observable (path (occupation.horizons rank + 1))) /
          ((occupation.horizons rank + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (f := fun rank : ℕ ↦ observable (path 0) -
        observable (path (occupation.horizons rank + 1)))
      (g := fun rank : ℕ ↦ ((occupation.horizons rank + 1 : ℕ) : ℝ))
      hlower hupper hdenominatorReal
  have hdifference : Tendsto (fun rank ↦
      (∫ edge : Point × Point, observable edge.1
          ∂(empiricalEdgeLaw path (occupation.horizons rank) :
            Measure (Point × Point))) -
        ∫ edge : Point × Point, observable edge.2
          ∂(empiricalEdgeLaw path (occupation.horizons rank) :
            Measure (Point × Point))) atTop (nhds 0) := by
    simpa only [integral_fst_sub_snd_empiricalEdgeLaw, Nat.cast_add,
      Nat.cast_one] using hendpoint
  have hlimit := hfirst.sub hsecond
  have heq := tendsto_nhds_unique hlimit hdifference
  simpa only [first, second,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    sub_eq_zero] using heq

variable [TopologicalSpace.PseudoMetrizableSpace Point]

/-- The source and target marginals of the occupation law are equal. -/
theorem marginals_eq
    (occupation : CompactForwardOccupation path) :
    occupation.law.map continuous_fst.measurable.aemeasurable =
      occupation.law.map continuous_snd.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro observable
  simpa only [ProbabilityMeasure.toMeasure_map,
    integral_map continuous_fst.measurable.aemeasurable
      observable.continuous.aestronglyMeasurable,
    integral_map continuous_snd.measurable.aemeasurable
      observable.continuous.aestronglyMeasurable] using
    occupation.integral_fst_eq_integral_snd observable

omit [TopologicalSpace Point] [BorelSpace Point]
  [SecondCountableTopology Point]
  [TopologicalSpace.PseudoMetrizableSpace Point] in
/-- Every empirical edge law gives full mass to a relation satisfied by all
actual source edges. -/
theorem empiricalEdgeLaw_apply_edgeGraph
    (path : ℕ → Point) (edge : Point → Point → Prop)
    (hedge : ∀ time, edge (path time) (path (time + 1)))
    (horizon : ℕ)
    (hmeasurable : MeasurableSet {pair : Point × Point |
      edge pair.1 pair.2}) :
    (empiricalEdgeLaw path horizon : Measure (Point × Point))
        {pair | edge pair.1 pair.2} = 1 := by
  let indexLaw := PMF.uniformOfFintype (Fin (horizon + 1))
  let edgeAt : Fin (horizon + 1) → Point × Point := fun time ↦
    (path time, path (time + 1))
  change (PMF.map edgeAt indexLaw).toMeasure
    {pair | edge pair.1 pair.2} = 1
  rw [← PMF.toMeasure_map edgeAt indexLaw (measurable_of_finite _)]
  rw [Measure.map_apply (measurable_of_finite _) hmeasurable]
  have hpreimage : edgeAt ⁻¹' {pair : Point × Point |
      edge pair.1 pair.2} = Set.univ := by
    ext time
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true,
      edgeAt]
    exact hedge time
  rw [hpreimage, measure_univ]

variable [T2Space Point] [CompactSpace Point]

/-- Compactness of probability laws supplies an actual subsequential weak
occupation limit. -/
theorem nonempty_compactForwardOccupation (path : ℕ → Point) :
    Nonempty (CompactForwardOccupation path) := by
  obtain ⟨law, horizons, hstrict, htendsto⟩ :=
    CompactSpace.tendsto_subseq (fun horizon ↦ empiricalEdgeLaw path horizon)
  exact ⟨{
    law := law
    horizons := horizons
    horizons_strictMono := hstrict
    empirical_tendsto := htendsto
  }⟩

omit [T2Space Point] [CompactSpace Point] in
/-- A closed relation satisfied by every source edge supports the entire
limiting occupation law. -/
theorem support_subset_edgeGraph
    (occupation : CompactForwardOccupation path)
    (edge : Point → Point → Prop)
    (hclosed : IsClosed {pair : Point × Point | edge pair.1 pair.2})
    (hedge : ∀ time, edge (path time) (path (time + 1))) :
    (occupation.law : Measure (Point × Point)).support ⊆
      {pair | edge pair.1 pair.2} := by
  have hlimsup :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
      occupation.empirical_tendsto hclosed
  have hfull : (occupation.law : Measure (Point × Point))
      {pair | edge pair.1 pair.2} = 1 := by
    have hone : atTop.limsup (fun rank ↦
        (empiricalEdgeLaw path (occupation.horizons rank) :
          Measure (Point × Point)) {pair | edge pair.1 pair.2}) = 1 := by
      simp only [empiricalEdgeLaw_apply_edgeGraph path edge hedge _
        hclosed.measurableSet, limsup_const]
    have hge : (1 : ENNReal) ≤ (occupation.law : Measure (Point × Point))
        {pair | edge pair.1 pair.2} := by
      rw [← hone]
      exact hlimsup
    exact le_antisymm (by
      calc
        (occupation.law : Measure (Point × Point))
              {pair | edge pair.1 pair.2} ≤
            (occupation.law : Measure (Point × Point)) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ) hge
  apply Measure.support_subset_of_isClosed hclosed
  rw [mem_ae_iff, measure_compl hclosed.measurableSet]
  · simp only [measure_univ, hfull, tsub_self]
  · simp

end CompactForwardOccupation

end Topology
end Math
