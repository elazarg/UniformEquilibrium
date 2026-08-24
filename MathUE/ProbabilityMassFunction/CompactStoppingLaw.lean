/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.EMetricSpace.Weak
import MathUE.Probability.StoppingLawReconstruction

/-!
# Compact stopping laws

The stopping-time space `Nat union {infinity}` is realized as `WithTop Nat`
with its compact one-point topology.  Probability measures on this space are
compact in the topology of weak convergence and are exactly the project's
discrete stopping laws on `Option Nat`.

This file also supplies finite barycentres.  They are ordinary mixtures of
probability measures, are continuous in the simplex weights, and become the
corresponding mixtures of probability mass functions under the discrete-law
bridge.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

namespace Math
namespace Probability

open MeasureTheory Set

/-- The compact one-point stopping-time space.  Finite times are coerced from
`Nat`; `top` is Never.  Definitionally this is the same underlying type as
`Option Nat`, but it carries the one-point compact topology. -/
abbrev CompactStoppingTime := WithTop Nat

noncomputable instance : MeasurableSpace CompactStoppingTime :=
  borel CompactStoppingTime

instance : BorelSpace CompactStoppingTime := ⟨rfl⟩

/-- Probability laws on the one-point compactification of finite stopping
times. -/
abbrev CompactStoppingLaw := ProbabilityMeasure CompactStoppingTime

/-- Read a compact stopping law as the project's discrete stopping law. -/
def CompactStoppingLaw.toPMF (law : CompactStoppingLaw) :
    PMF CompactStoppingTime :=
  law.toMeasure.toPMF

/-- Give a discrete stopping law its canonical weakly compact realization. -/
def CompactStoppingLaw.ofPMF (law : PMF CompactStoppingTime) :
    CompactStoppingLaw :=
  ⟨law.toMeasure, PMF.toMeasure.isProbabilityMeasure law⟩

@[simp] theorem CompactStoppingLaw.toPMF_ofPMF
    (law : PMF CompactStoppingTime) :
    (CompactStoppingLaw.ofPMF law).toPMF = law := by
  exact PMF.toMeasure_toPMF law

@[simp] theorem CompactStoppingLaw.ofPMF_toPMF (law : CompactStoppingLaw) :
    CompactStoppingLaw.ofPMF law.toPMF = law := by
  apply ProbabilityMeasure.toMeasure_injective
  exact MeasureTheory.Measure.toPMF_toMeasure law.toMeasure

/-- Compact stopping laws and discrete stopping laws contain exactly the same
probability data. -/
def compactStoppingLawEquivPMF :
    CompactStoppingLaw ≃ PMF CompactStoppingTime where
  toFun := CompactStoppingLaw.toPMF
  invFun := CompactStoppingLaw.ofPMF
  left_inv := CompactStoppingLaw.ofPMF_toPMF
  right_inv := CompactStoppingLaw.toPMF_ofPMF

/-- The compact-law mass of an arbitrary set, as a real number. -/
def CompactStoppingLaw.realMass (law : CompactStoppingLaw)
    (event : Set CompactStoppingTime) : Real :=
  (law.toMeasure event).toReal

theorem CompactStoppingLaw.realMass_nonneg (law : CompactStoppingLaw)
    (event : Set CompactStoppingTime) :
    0 <= law.realMass event :=
  ENNReal.toReal_nonneg

theorem CompactStoppingLaw.realMass_le_one (law : CompactStoppingLaw)
    (event : Set CompactStoppingTime) :
    law.realMass event <= 1 := by
  rw [CompactStoppingLaw.realMass]
  calc
    (law.toMeasure event).toReal <= (law.toMeasure Set.univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (subset_univ event))
    _ = 1 := by simp

/-- A finite barycentre of compact stopping laws. -/
def compactStoppingLawBarycenter (n : Nat)
    (weights : stdSimplex Real (Fin (n + 1)))
    (points : Fin (n + 1) -> CompactStoppingLaw) : CompactStoppingLaw := by
  let measure : Measure CompactStoppingTime :=
    ∑ index : Fin (n + 1),
      ENNReal.ofReal (weights index) • (points index : Measure CompactStoppingTime)
  refine ⟨measure, ?_⟩
  rw [MeasureTheory.isProbabilityMeasure_iff]
  simp only [measure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have hsum := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun index : Fin (n + 1) => weights index)
    (fun index _ => weights.property.1 index)
  have hweights : (∑ index, weights index) = 1 := weights.property.2
  rw [hweights] at hsum
  simpa using hsum.symm

@[simp] theorem compactStoppingLawBarycenter_toMeasure (n : Nat)
    (weights : stdSimplex Real (Fin (n + 1)))
    (points : Fin (n + 1) -> CompactStoppingLaw) :
    (compactStoppingLawBarycenter n weights points :
      Measure CompactStoppingTime) =
      ∑ index, ENNReal.ofReal (weights index) •
        (points index : Measure CompactStoppingTime) :=
  rfl

theorem CompactStoppingLaw.realMass_barycenter (n : Nat)
    (weights : stdSimplex Real (Fin (n + 1)))
    (points : Fin (n + 1) -> CompactStoppingLaw)
    (event : Set CompactStoppingTime) (_hevent : MeasurableSet event) :
    (compactStoppingLawBarycenter n weights points).realMass event =
      ∑ index, weights index * (points index).realMass event := by
  unfold CompactStoppingLaw.realMass compactStoppingLawBarycenter
  change ((∑ index, ENNReal.ofReal (weights index) •
      (points index : Measure CompactStoppingTime)) event).toReal = _
  rw [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro index _
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
    congr 1
    exact ENNReal.toReal_ofReal (weights.property.1 index)
  · intro index _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

/-- Finite barycentres depend continuously on their simplex weights. -/
theorem continuous_compactStoppingLawBarycenter (n : Nat)
    (points : Fin (n + 1) -> CompactStoppingLaw) :
    Continuous fun weights : stdSimplex Real (Fin (n + 1)) =>
      compactStoppingLawBarycenter n weights points := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro observable
  have hintegrable : forall index,
      Integrable (fun choice => observable choice)
        (points index : Measure CompactStoppingTime) :=
    fun index => BoundedContinuousFunction.integrable
      (points index : Measure CompactStoppingTime) observable
  have hintegral (weights : stdSimplex Real (Fin (n + 1))) :
      (∫ choice, observable choice ∂
          (compactStoppingLawBarycenter n weights points :
            Measure CompactStoppingTime)) =
        ∑ index, weights index *
          ∫ choice, observable choice ∂
            (points index : Measure CompactStoppingTime) := by
    rw [compactStoppingLawBarycenter_toMeasure]
    rw [integral_finsetSum_measure (fun index _ =>
      (hintegrable index).smul_measure ENNReal.ofReal_ne_top)]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal,
      stdSimplex.zero_le, smul_eq_mul]
  simp_rw [hintegral]
  exact continuous_finsetSum _ fun index _ => by
    exact ((continuous_apply index).comp continuous_subtype_val).mul
      continuous_const

theorem CompactStoppingLaw.toPMF_apply_toReal
    (law : CompactStoppingLaw) (choice : CompactStoppingTime) :
    (law.toPMF choice).toReal = law.realMass {choice} := by
  unfold CompactStoppingLaw.toPMF CompactStoppingLaw.realMass
  rw [MeasureTheory.Measure.toPMF_apply]

/-- Barycentring compact laws is exactly barycentring their discrete laws. -/
theorem CompactStoppingLaw.toPMF_barycenter_apply_toReal (n : Nat)
    (weights : stdSimplex Real (Fin (n + 1)))
    (points : Fin (n + 1) -> CompactStoppingLaw)
    (choice : CompactStoppingTime) :
    ((compactStoppingLawBarycenter n weights points).toPMF choice).toReal =
      ∑ index, weights index * ((points index).toPMF choice).toReal := by
  let event : Set CompactStoppingTime := {choice}
  have hevent : MeasurableSet event := MeasurableSet.singleton choice
  have hmass := CompactStoppingLaw.realMass_barycenter n weights points event hevent
  simpa [event, CompactStoppingLaw.toPMF_apply_toReal] using hmass

end Probability
end Math
