/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import MathUE.Topology.ThreeFourFifthsRotation
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonResidualHard

/-!
# An aperiodic selected chain in the ballistic normalized relation

This exact rational regression uses the checked paired-singleton solo matrix
and an explicit rational collision matrix.  The normalized relation has a
uniformly full-support aperiodic selected orbit with renewal ratio `1/2`, and
also has a stationary fixed point.

The construction is matrix-level only.  It is not an actual strict quitting
ray, does not carry a producer-atlas source, and does not lift its normalized
states to literal roots, payoffs, endpoint Nash, or Bellman closure.  It
therefore refutes only the inference that a selected normalized chain must
itself become stationary or periodic.
-/

noncomputable section

namespace GameTheory
namespace BallisticNormalizedSelectedChainRegression

open Math Math.Topology Set
open FourPlayerPairedSingleton

abbrev Player := Fin 4

/-- Rational collision matrix paired with the checked singleton matrix. -/
def collisionMatrix : Player → Player → ℝ := fun who owner =>
  ![![0, -42 / 13, -4 / 13, 20 / 13],
    ![-42 / 13, 0, 20 / 13, -4 / 13],
    ![20 / 13, -4 / 13, 0, -42 / 13],
    ![-4 / 13, 20 / 13, -42 / 13, 0]] who owner

/-- Current normalized hazard direction at a complex phase. -/
def currentVector (phase : ℂ) : Player → ℝ :=
  ![1 / 4 + phase.re / 8,
    1 / 4 - phase.re / 8,
    1 / 4 + phase.im / 8,
    1 / 4 - phase.im / 8]

/-- Exact geometric tail barycenter at a complex phase. -/
def tailVector (phase : ℂ) : Player → ℝ :=
  ![1 / 4 + (7 * phase.re - 4 * phase.im) / 104,
    1 / 4 - (7 * phase.re - 4 * phase.im) / 104,
    1 / 4 + (4 * phase.re + 7 * phase.im) / 104,
    1 / 4 - (4 * phase.re + 7 * phase.im) / 104]

theorem currentVector_sum (phase : ℂ) :
    ∑ who, currentVector phase who = 1 := by
  simp [currentVector, Fin.sum_univ_succ]
  ring

theorem tailVector_sum (phase : ℂ) :
    ∑ who, tailVector phase who = 1 := by
  simp [tailVector, Fin.sum_univ_succ]
  ring

theorem currentVector_nonneg {phase : ℂ} (hnorm : ‖phase‖ = 1)
    (who : Player) :
    0 ≤ currentVector phase who := by
  have hre := Complex.abs_re_le_norm phase
  have him := Complex.abs_im_le_norm phase
  rw [hnorm] at hre him
  fin_cases who <;> simp [currentVector] <;>
    nlinarith [neg_abs_le phase.re, le_abs_self phase.re,
      neg_abs_le phase.im, le_abs_self phase.im]

theorem currentVector_ge_one_eighth {phase : ℂ} (hnorm : ‖phase‖ = 1)
    (who : Player) :
    1 / 8 ≤ currentVector phase who := by
  have hre := Complex.abs_re_le_norm phase
  have him := Complex.abs_im_le_norm phase
  rw [hnorm] at hre him
  fin_cases who <;> simp [currentVector] <;>
    nlinarith [neg_abs_le phase.re, le_abs_self phase.re,
      neg_abs_le phase.im, le_abs_self phase.im]

theorem tailVector_nonneg {phase : ℂ} (hnorm : ‖phase‖ = 1)
    (who : Player) :
    0 ≤ tailVector phase who := by
  have hre := Complex.abs_re_le_norm phase
  have him := Complex.abs_im_le_norm phase
  rw [hnorm] at hre him
  fin_cases who <;> simp [tailVector] <;>
    nlinarith [neg_abs_le phase.re, le_abs_self phase.re,
      neg_abs_le phase.im, le_abs_self phase.im]

def currentSimplex (phase : ℂ) (hnorm : ‖phase‖ = 1) :
    stdSimplex ℝ Player :=
  ⟨currentVector phase, currentVector_nonneg hnorm, currentVector_sum phase⟩

def tailSimplex (phase : ℂ) (hnorm : ‖phase‖ = 1) :
    stdSimplex ℝ Player :=
  ⟨tailVector phase, tailVector_nonneg hnorm, tailVector_sum phase⟩

/-- Standalone normalized state space for the regression. -/
abbrev State :=
  stdSimplex ℝ Player × stdSimplex ℝ Player × Set.Icc (1 / 2 : ℝ) 1

/-- Normalized singleton-plus-collision work. -/
def work (state : State) (who : Player) : ℝ :=
  (∑ owner, pairedSingletonMatrix who owner * state.2.1.val owner) +
    (state.2.2 : ℝ) *
      ∑ owner, collisionMatrix who owner * state.1.val owner

/-- The exact standalone ballistic relation used by the diagnostic. -/
def IsEdge (current next : State) : Prop :=
  (∀ who, current.2.1.val who =
    (current.2.2 : ℝ) * current.1.val who +
      (1 - (current.2.2 : ℝ)) * next.2.1.val who) ∧
  (∀ who, work current who ≤ 0) ∧
    ∀ who, current.1.val who * work current who = 0

/-- Rotation phase at an actual selected-chain index. -/
def phaseAt (time : ℕ) : ℂ :=
  threeFourFifthsMultiplier ^ time

@[simp] theorem phaseAt_norm (time : ℕ) : ‖phaseAt time‖ = 1 := by
  simp [phaseAt, norm_pow]

theorem phaseAt_ne_zero (time : ℕ) : phaseAt time ≠ 0 := by
  rw [← norm_ne_zero_iff]
  simp

/-- Exact selected normalized state. -/
def stateAt (time : ℕ) : State :=
  (currentSimplex (phaseAt time) (phaseAt_norm time),
    tailSimplex (phaseAt time) (phaseAt_norm time),
    ⟨1 / 2, by norm_num⟩)

@[simp] theorem stateAt_current (time : ℕ) (who : Player) :
    (stateAt time).1.val who = currentVector (phaseAt time) who := rfl

@[simp] theorem stateAt_tail (time : ℕ) (who : Player) :
    (stateAt time).2.1.val who = tailVector (phaseAt time) who := rfl

@[simp] theorem stateAt_ratio (time : ℕ) :
    ((stateAt time).2.2 : ℝ) = 1 / 2 := rfl

theorem tailVector_renewal (phase : ℂ) (who : Player) :
    tailVector phase who =
      (1 / 2 : ℝ) * currentVector phase who +
        (1 - (1 / 2 : ℝ)) *
          tailVector (threeFourFifthsMultiplier * phase) who := by
  fin_cases who <;>
    simp [tailVector, currentVector] <;>
    ring

theorem work_phase_eq_zero (phase : ℂ) (hnorm : ‖phase‖ = 1)
    (who : Player) :
    work (currentSimplex phase hnorm, tailSimplex phase hnorm,
      ⟨1 / 2, by norm_num⟩) who = 0 := by
  fin_cases who <;>
    simp [work, currentSimplex, tailSimplex, currentVector, tailVector,
      pairedSingletonMatrix, collisionMatrix, Fin.sum_univ_succ] <;>
    ring

theorem stateAt_edge (time : ℕ) : IsEdge (stateAt time) (stateAt (time + 1)) := by
  have hphase : phaseAt (time + 1) =
      threeFourFifthsMultiplier * phaseAt time := by
    simp [phaseAt, pow_succ, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro who
    simpa only [stateAt_tail, stateAt_current, stateAt_ratio, hphase] using
      tailVector_renewal (phaseAt time) who
  · intro who
    rw [show work (stateAt time) who = 0 by
      exact work_phase_eq_zero (phaseAt time) (phaseAt_norm time) who]
  · intro who
    rw [show work (stateAt time) who = 0 by
      exact work_phase_eq_zero (phaseAt time) (phaseAt_norm time) who]
    simp

theorem stateAt_current_ge_one_eighth (time : ℕ) (who : Player) :
    1 / 8 ≤ (stateAt time).1.val who :=
  currentVector_ge_one_eighth (phaseAt_norm time) who

theorem currentVector_injective_on_unit
    {first second : ℂ} (_hfirst : ‖first‖ = 1)
    (_hsecond : ‖second‖ = 1)
    (heq : currentVector first = currentVector second) :
    first = second := by
  apply Complex.ext
  · have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    simp [currentVector] at h0 h1
    linarith
  · have h2 := congrFun heq 2
    have h3 := congrFun heq 3
    simp [currentVector] at h2 h3
    linarith

/-- The selected normalized chain has no positive period at any start. -/
theorem stateAt_not_periodic (start period : ℕ) (hperiod : 0 < period) :
    stateAt (start + period) ≠ stateAt start := by
  intro hstate
  have hcurrent : currentVector (phaseAt (start + period)) =
      currentVector (phaseAt start) := by
    exact congrArg (fun state : State ↦ state.1.val) hstate
  have hphase : phaseAt (start + period) = phaseAt start :=
    currentVector_injective_on_unit (phaseAt_norm (start + period))
      (phaseAt_norm start) hcurrent
  have hfactor : phaseAt (start + period) =
      threeFourFifthsMultiplier ^ period * phaseAt start := by
    simp [phaseAt, pow_add, mul_comm]
  rw [hfactor] at hphase
  exact threeFourFifthsMultiplier_pow_mul_ne hperiod
    (phaseAt_ne_zero start) hphase

/-- Uniform barycenter used by the stationary state in the same relation. -/
def uniformSimplex : stdSimplex ℝ Player :=
  ⟨fun _ ↦ 1 / 4, by
    constructor
    · intro who
      positivity
    · norm_num [Fin.sum_univ_succ]⟩

/-- The ambient normalized relation also has an explicit fixed state. -/
def fixedState : State :=
  (uniformSimplex, uniformSimplex, ⟨1 / 2, by norm_num⟩)

theorem fixedState_work_eq_zero (who : Player) :
    work fixedState who = 0 := by
  fin_cases who <;>
    norm_num [work, fixedState, uniformSimplex, pairedSingletonMatrix,
      collisionMatrix, Fin.sum_univ_succ]

theorem fixedState_edge : IsEdge fixedState fixedState := by
  refine ⟨?_, ?_, ?_⟩
  · intro who
    norm_num [fixedState, uniformSimplex]
  · intro who
    rw [fixedState_work_eq_zero]
  · intro who
    rw [fixedState_work_eq_zero, mul_zero]

/-- The solo matrix in the regression has the checked full normal core. -/
theorem soloMatrix_normalCore_eq_univ :
    QuittingLCPClassification.normalCore pairedSingletonMatrix = Finset.univ :=
  pairedSingletonMatrix_normalCore_eq_univ

/-- The solo matrix has no homogeneous simplex solution. -/
theorem soloMatrix_noHomogeneous :
    ¬QuittingLCPClassification.HasHomogeneousSimplexSolution
      pairedSingletonMatrix :=
  pairedSingletonMatrix_noHomogeneous

/-- The solo matrix is standard-Q. -/
theorem soloMatrix_standardQ :
    QuittingLCPClassification.IsStandardQMatrix pairedSingletonMatrix :=
  pairedSingletonMatrix_standardQ

/-- The solo matrix is not projective Q-bar. -/
theorem soloMatrix_not_projectiveQBar :
    ¬QuittingLCPClassification.IsProjectiveQBarMatrix
      pairedSingletonMatrix :=
  pairedSingletonMatrix_not_projectiveQBar

end BallisticNormalizedSelectedChainRegression
end GameTheory
