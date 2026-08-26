/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.EMetricSpace.Weak
import MathUE.ProbabilityMassFunction
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

open Filter MeasureTheory Set

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

/-- Event mass agrees across the compact-measure and discrete-PMF views. -/
theorem CompactStoppingLaw.realMass_eq_pmfMass_toReal
    (law : CompactStoppingLaw) {event : Set CompactStoppingTime}
    (hevent : MeasurableSet event) :
    law.realMass event =
      (_root_.Math.ProbabilityMassFunction.pmfMass
        (law.toPMF) fun choice => choice ∈ event).toReal := by
  unfold CompactStoppingLaw.realMass CompactStoppingLaw.toPMF
  rw [_root_.Math.ProbabilityMassFunction.pmfMass_eq_toOuterMeasure]
  change (law.toMeasure event).toReal =
    ((law.toMeasure.toPMF).toOuterMeasure event).toReal
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hevent]
  rw [MeasureTheory.Measure.toPMF_toMeasure]

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

/-! ## Clopen finite and tail coordinates -/

/-- A finite stopping date is a clopen point of the one-point compactification. -/
theorem compactStoppingTime_finiteSingleton_isClopen (time : Nat) :
    IsClopen ({(time : CompactStoppingTime)} : Set CompactStoppingTime) := by
  constructor
  · exact isClosed_singleton
  · rw [← Set.image_singleton]
    exact WithTop.isOpenEmbedding_coe.isOpenMap {time} (isOpen_discrete {time})

/-- The late-or-Never tail after `horizon` is the corresponding closed upper
interval. -/
theorem compactStoppingTime_tail_eq_Ici (horizon : Nat) :
    {choice : CompactStoppingTime |
        WithTop.some horizon < choice} =
      Set.Ici (WithTop.some (horizon + 1)) := by
  ext choice
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  induction choice using WithTop.recTopCoe with
  | top => simp
  | coe time =>
      simp only [WithTop.coe_lt_coe, WithTop.coe_le_coe]
      omega

/-- Every fixed late-or-Never tail is clopen. -/
theorem compactStoppingTime_tail_isClopen (horizon : Nat) :
    IsClopen {choice : CompactStoppingTime |
      WithTop.some horizon < choice} := by
  constructor
  · rw [compactStoppingTime_tail_eq_Ici]
    exact isClosed_Ici
  · exact isOpen_Ioi

/-- Weak convergence of compact stopping laws passes the real mass of any
clopen event. -/
theorem ProbabilityMeasure.tendsto_measure_toReal_of_isClopen
    {Omega : Type*} [TopologicalSpace Omega] [MeasurableSpace Omega]
    [BorelSpace Omega] {lawSeq : Nat → ProbabilityMeasure Omega}
    {law : ProbabilityMeasure Omega}
    (hlaw : Tendsto lawSeq atTop (nhds law))
    {event : Set Omega} (hevent : IsClopen event) :
    Tendsto (fun n => ((lawSeq n : Measure Omega) event).toReal) atTop
      (nhds (((law : ProbabilityMeasure Omega) : Measure Omega) event).toReal) := by
  let observable : BoundedContinuousFunction Omega Real :=
    BoundedContinuousFunction.indicator event hevent
  have hintegral :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      observable).continuousAt.tendsto.comp hlaw
  have hobservable (mu : ProbabilityMeasure Omega) :
      (∫ x, observable x ∂(mu : Measure Omega)) =
        (mu : Measure Omega).real event := by
    simp [observable, BoundedContinuousFunction.indicator_apply,
      integral_indicator_one hevent.2.measurableSet]
  change Tendsto (fun n => (lawSeq n : Measure Omega).real event) atTop
    (nhds ((law : Measure Omega).real event))
  simpa only [Function.comp_def, hobservable] using hintegral

/-- Weak convergence of compact stopping laws passes the real mass of any
clopen event. -/
theorem CompactStoppingLaw.tendsto_realMass_of_isClopen
    {lawSeq : Nat -> CompactStoppingLaw} {law : CompactStoppingLaw}
    (hlaw : Tendsto lawSeq atTop (nhds law))
    {event : Set CompactStoppingTime} (hevent : IsClopen event) :
    Tendsto (fun n => (lawSeq n).realMass event) atTop
      (nhds (law.realMass event)) := by
  let observable : BoundedContinuousFunction CompactStoppingTime Real :=
    BoundedContinuousFunction.indicator event hevent
  have hintegral :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      observable).continuousAt.tendsto.comp hlaw
  have hreal (mu : CompactStoppingLaw) :
      mu.realMass event = (mu event : Real) := by
    simpa [CompactStoppingLaw.realMass, Measure.real] using
      ProbabilityMeasure.measureReal_eq_coe_coeFn mu event
  simp_rw [hreal]
  change Tendsto (fun n => ((lawSeq n) event : Real)) atTop
    (nhds ((law event : NNReal) : Real))
  have hmass : Tendsto
      ((fun mu : CompactStoppingLaw => (mu event : Real)) ∘ lawSeq)
      atTop (nhds ((law event : NNReal) : Real)) := by
    simpa [observable, BoundedContinuousFunction.indicator_apply,
      integral_indicator_one hevent.2.measurableSet] using hintegral
  exact hmass

/-- Late-or-Never tail masses converge to the Never atom.  This is continuity
from above, not weak convergence of a varying event. -/
theorem CompactStoppingLaw.tendsto_tail_realMass_top
    (law : CompactStoppingLaw) :
    Tendsto (fun horizon => law.realMass
        {choice | WithTop.some horizon < choice}) atTop
      (nhds (law.realMass {⊤})) := by
  let tail := fun horizon : Nat =>
    {choice : CompactStoppingTime | WithTop.some horizon < choice}
  have hanti : Antitone tail := by
    intro first second hle choice hchoice
    exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hle) hchoice
  have hinter : ⋂ horizon, tail horizon = ({⊤} : Set CompactStoppingTime) := by
    ext choice
    constructor
    · intro hchoice
      have hall : ∀ horizon, WithTop.some horizon < choice := by
        intro horizon
        exact Set.mem_iInter.mp hchoice horizon
      induction choice using WithTop.recTopCoe with
      | top => rfl
      | coe time => exact (lt_irrefl (WithTop.some time) (hall time)).elim
    · intro hchoice
      have : choice = ⊤ := Set.mem_singleton_iff.mp hchoice
      subst choice
      exact Set.mem_iInter.mpr fun horizon => by simp [tail]
  have hmeasure := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := law.toMeasure) (s := tail)
    (fun horizon =>
      (compactStoppingTime_tail_isClopen horizon).1.measurableSet.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at hmeasure
  exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hmeasure

end Probability
end Math
