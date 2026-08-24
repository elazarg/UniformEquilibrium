/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.HarmonicRecurrentCoreBound
import MathUE.Probability.HittingTimePotential

/-!
# Coupled transient variation for a static harmonic observable

For a unit-interval harmonic function `value`, sum the absolute-distance potentials
`|value state - value owner|` over all transient owners.  At a transient source, the summand
centred at that source pays the entire one-step absolute variation.  Every other summand has
nonnegative drift by Jensen's inequality.  At recurrent sources the variation is zero, while
the same Jensen drift remains nonnegative.

The resulting single global potential telescopes and proves the sharp transient-cardinality
bound for static harmonic observables.  This does not yet prove Simon's time-indexed lemma:
for a backward orbit, the centres `value owner time` move with time, and their transport is the
remaining coupled issue.
-/

namespace Math.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]

/-- States outside the union of all recurrent closed communication classes. -/
def finiteTransientStates (kernel : Omega → PMF Omega) : Finset Omega :=
  Finset.univ \ finiteRecurrentCore kernel

theorem mem_finiteTransientStates_iff
    (kernel : Omega → PMF Omega) (state : Omega) :
    state ∈ finiteTransientStates kernel ↔ state ∉ finiteRecurrentCore kernel := by
  simp [finiteTransientStates]

/-- One scalar potential coupling all transient state labels. -/
def finiteTransientAbsoluteDistancePotential
    (kernel : Omega → PMF Omega) (value : Omega → ℝ) (state : Omega) : ℝ :=
  ∑ owner ∈ finiteTransientStates kernel, |value state - value owner|

theorem finiteTransientAbsoluteDistancePotential_nonneg
    (kernel : Omega → PMF Omega) (value : Omega → ℝ) (state : Omega) :
    0 ≤ finiteTransientAbsoluteDistancePotential kernel value state :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem finiteTransientAbsoluteDistancePotential_le_card
    (kernel : Omega → PMF Omega) (value : Omega → ℝ)
    (bounded : ∀ state, value state ∈ Set.Icc (0 : ℝ) 1) (state : Omega) :
    finiteTransientAbsoluteDistancePotential kernel value state ≤
      (finiteTransientStates kernel).card := by
  calc
    finiteTransientAbsoluteDistancePotential kernel value state ≤
        ∑ _ ∈ finiteTransientStates kernel, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro owner _
      rw [abs_le]
      constructor <;> linarith [(bounded state).1, (bounded state).2,
        (bounded owner).1, (bounded owner).2]
    _ = (finiteTransientStates kernel).card := by simp

omit [DecidableEq Omega] in
theorem abs_sub_const_expect_le_expect_abs_sub_const
    (law : PMF Omega) (value : Omega → ℝ) (center : ℝ) :
    |expect law value - center| ≤
      expect law (fun state ↦ |value state - center|) := by
  calc
    |expect law value - center| =
        |expect law (fun state ↦ value state - center)| := by
      rw [expect_sub, expect_const]
    _ ≤ expect law (fun state ↦ |value state - center|) :=
      abs_expect_le_expect_abs law (fun state ↦ value state - center)

theorem expect_finiteTransientAbsoluteDistancePotential
    (law : PMF Omega) (kernel : Omega → PMF Omega) (value : Omega → ℝ) :
    expect law (finiteTransientAbsoluteDistancePotential kernel value) =
      ∑ owner ∈ finiteTransientStates kernel,
        expect law (fun state ↦ |value state - value owner|) := by
  unfold finiteTransientAbsoluteDistancePotential
  rw [expect_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro owner _
  rw [expect_eq_sum]

omit [DecidableEq Omega] in
/-- Every fixed-centre absolute-distance potential has nonnegative drift under a harmonic
observable. -/
theorem absoluteDistance_expect_sub_nonneg
    (kernel : Omega → PMF Omega) (value : Omega → ℝ)
    (harmonic : ∀ state, value state = expect (kernel state) value)
    (source owner : Omega) :
    0 ≤ expect (kernel source) (fun successor ↦ |value successor - value owner|) -
      |value source - value owner| := by
  have h := abs_sub_const_expect_le_expect_abs_sub_const
    (kernel source) value (value owner)
  rw [← harmonic source] at h
  linarith

/-- At a transient source, the centre indexed by that same state is exactly the local absolute
variation; all other transient centres add nonnegative Jensen drift. -/
theorem conditionalVariation_le_transientPotentialDrift_of_mem
    (kernel : Omega → PMF Omega) (value : Omega → ℝ)
    (harmonic : ∀ state, value state = expect (kernel state) value)
    {source : Omega} (source_transient : source ∈ finiteTransientStates kernel) :
    expect (kernel source) (fun successor ↦ |value successor - value source|) ≤
      expect (kernel source)
          (finiteTransientAbsoluteDistancePotential kernel value) -
        finiteTransientAbsoluteDistancePotential kernel value source := by
  rw [expect_finiteTransientAbsoluteDistancePotential,
    finiteTransientAbsoluteDistancePotential, ← Finset.sum_sub_distrib]
  have hsourceTerm :
      expect (kernel source) (fun successor ↦ |value successor - value source|) -
          |value source - value source| ≤
        ∑ owner ∈ finiteTransientStates kernel,
          (expect (kernel source) (fun successor ↦ |value successor - value owner|) -
            |value source - value owner|) := by
    exact Finset.single_le_sum
      (fun owner _ ↦ absoluteDistance_expect_sub_nonneg
        kernel value harmonic source owner) source_transient
  simpa using hsourceTerm

/-- Static unit-interval harmonic observables have zero local variation on the recurrent core. -/
theorem staticConditionalVariation_eq_zero_of_mem_finiteRecurrentCore
    (kernel : Omega → PMF Omega) (value : Omega → ℝ)
    (bounded : ∀ state, value state ∈ Set.Icc (0 : ℝ) 1)
    (harmonic : ∀ state, value state = expect (kernel state) value)
    {source : Omega} (source_recurrent : source ∈ finiteRecurrentCore kernel) :
    expect (kernel source) (fun successor ↦ |value successor - value source|) = 0 := by
  let orbit : Omega → ℕ → ℝ := fun state _ ↦ value state
  have orbitHarmonic : IsUnitIntervalBackwardMarkovHarmonic kernel orbit := by
    constructor
    · exact fun state _ ↦ bounded state
    · exact fun state _ ↦ harmonic state
  simpa [orbit] using expect_abs_increment_eq_zero_of_mem_finiteRecurrentCore
    kernel orbit orbitHarmonic source_recurrent 0

/-- The whole one-step conditional variation is paid by the drift of one coupled transient
absolute-distance potential. -/
theorem staticConditionalVariation_le_transientPotentialDrift
    (kernel : Omega → PMF Omega) (value : Omega → ℝ)
    (bounded : ∀ state, value state ∈ Set.Icc (0 : ℝ) 1)
    (harmonic : ∀ state, value state = expect (kernel state) value)
    (source : Omega) :
    expect (kernel source) (fun successor ↦ |value successor - value source|) ≤
      expect (kernel source)
          (finiteTransientAbsoluteDistancePotential kernel value) -
        finiteTransientAbsoluteDistancePotential kernel value source := by
  by_cases source_recurrent : source ∈ finiteRecurrentCore kernel
  · rw [staticConditionalVariation_eq_zero_of_mem_finiteRecurrentCore
      kernel value bounded harmonic source_recurrent]
    rw [sub_nonneg]
    rw [expect_finiteTransientAbsoluteDistancePotential]
    unfold finiteTransientAbsoluteDistancePotential
    apply Finset.sum_le_sum
    intro owner _
    exact sub_nonneg.mp (absoluteDistance_expect_sub_nonneg
      kernel value harmonic source owner)
  · exact conditionalVariation_le_transientPotentialDrift_of_mem
      kernel value harmonic ((mem_finiteTransientStates_iff kernel source).mpr source_recurrent)

/-- Sharp coupled transient-cardinality bound for a static harmonic observable. -/
theorem finiteExpectedSpaceTimeMarkovVariation_const_le_transientCard
    (initial : Omega) (kernel : Omega → PMF Omega) (value : Omega → ℝ)
    (bounded : ∀ state, value state ∈ Set.Icc (0 : ℝ) 1)
    (harmonic : ∀ state, value state = expect (kernel state) value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel (fun state _ ↦ value state)
        horizon ≤ (finiteTransientStates kernel).card := by
  let potential := finiteTransientAbsoluteDistancePotential kernel value
  have hstep (time : ℕ) :
      expect (Math.PMFIter.iter kernel time initial) (fun source ↦
          expect (kernel source) potential - potential source) =
        expect (Math.PMFIter.iter kernel (time + 1) initial) potential -
          expect (Math.PMFIter.iter kernel time initial) potential := by
    rw [expect_sub, ← expect_bind, Math.PMFIter.iter_succ']
  rw [finiteExpectedSpaceTimeMarkovVariation_eq_sum_iter_conditional]
  calc
    (∑ time ∈ Finset.range horizon,
        expect (Math.PMFIter.iter kernel time initial) (fun source ↦
          expect (kernel source) (fun successor ↦ |value successor - value source|))) ≤
        ∑ time ∈ Finset.range horizon,
          expect (Math.PMFIter.iter kernel time initial) (fun source ↦
            expect (kernel source) potential - potential source) := by
      apply Finset.sum_le_sum
      intro time _
      apply expect_mono
      exact staticConditionalVariation_le_transientPotentialDrift
        kernel value bounded harmonic
    _ = expect (Math.PMFIter.iter kernel horizon initial) potential - potential initial := by
      simp_rw [hstep]
      have htel := Finset.sum_range_sub'
        (fun time ↦ expect (Math.PMFIter.iter kernel time initial) potential) horizon
      have hneg :
          (∑ time ∈ Finset.range horizon,
              (expect (Math.PMFIter.iter kernel (time + 1) initial) potential -
                expect (Math.PMFIter.iter kernel time initial) potential)) =
            -∑ time ∈ Finset.range horizon,
              (expect (Math.PMFIter.iter kernel time initial) potential -
                expect (Math.PMFIter.iter kernel (time + 1) initial) potential) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro time _
        ring
      rw [hneg, htel]
      simp [Math.PMFIter.iter_zero]
    _ ≤ (finiteTransientStates kernel).card := by
      have hterminal : expect (Math.PMFIter.iter kernel horizon initial) potential ≤
          (finiteTransientStates kernel).card := by
        calc
          expect (Math.PMFIter.iter kernel horizon initial) potential ≤
              expect (Math.PMFIter.iter kernel horizon initial)
                (fun _ ↦ ((finiteTransientStates kernel).card : ℝ)) := by
            apply expect_mono
            exact finiteTransientAbsoluteDistancePotential_le_card
              kernel value bounded
          _ = (finiteTransientStates kernel).card := expect_const _ _
      have hinitial := finiteTransientAbsoluteDistancePotential_nonneg kernel value initial
      linarith

/-- Reader-facing form with Simon's coarser total-state cardinality on the right. -/
theorem finiteExpectedSpaceTimeMarkovVariation_const_le_card
    (initial : Omega) (kernel : Omega → PMF Omega) (value : Omega → ℝ)
    (bounded : ∀ state, value state ∈ Set.Icc (0 : ℝ) 1)
    (harmonic : ∀ state, value state = expect (kernel state) value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel (fun state _ ↦ value state)
        horizon ≤ Fintype.card Omega := by
  exact (finiteExpectedSpaceTimeMarkovVariation_const_le_transientCard
    initial kernel value bounded harmonic horizon).trans (by
      exact_mod_cast Finset.card_le_card (Finset.subset_univ (finiteTransientStates kernel)))

end

end Math.Probability
