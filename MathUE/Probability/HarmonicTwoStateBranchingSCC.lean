/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.HarmonicFunctionalTransientClassVariation
import MathUE.Probability.DurationMarkovRenewal

/-!
# The smallest branching transient SCC

This four-state example isolates the first regime not covered by functional transient
communication classes.  States `a,b` form a transient two-state SCC.  From `a`, the chain
either moves to `b` or exits; from `b`, it splits between `a` and `b`.  A deterministic
two-cycle supplies a bounded two-phase backward-harmonic value.

The current-state Bernoulli potential fails its one-step Bellman inequality at `b`.  This is
not a counterexample to Simon's bound: the state-coupled potential `4/5` at `a` and `6/5` at
`b` pays every conditional increment exactly.  Thus the smallest branching SCC already
requires coupling across state labels, while still satisfying a bound strictly below two.
-/

namespace Math.Probability

noncomputable section

namespace TwoStateBranchingSCC

inductive State
  | a
  | b
  | recurrentZero
  | recurrentOne
  deriving DecidableEq, Fintype

def aSuccessor : Bool → State
  | false => .b
  | true => .recurrentOne

def bSuccessor : Bool → State
  | false => .a
  | true => .b

/-- The transient block is `a ↔ b`, with a self-loop at `b` and an exit from `a`. -/
def kernel : State → PMF State
  | .a => (PMF.uniformOfFintype Bool).map aSuccessor
  | .b => (PMF.uniformOfFintype Bool).map bSuccessor
  | .recurrentZero => PMF.pure .recurrentOne
  | .recurrentOne => PMF.pure .recurrentZero

def phase (time : ℕ) : ℝ := (-1 : ℝ) ^ time

theorem phase_succ (time : ℕ) : phase (time + 1) = -phase time := by
  simp [phase, pow_succ]

theorem abs_phase (time : ℕ) : |phase time| = 1 := by
  simp [phase, abs_pow]

/-- The transient values alternate as `(1/5,3/5)` and `(4/5,2/5)`. -/
def value (state : State) (time : ℕ) : ℝ :=
  match state with
  | .a => 1 / 2 - 3 * phase time / 10
  | .b => 1 / 2 + phase time / 10
  | .recurrentZero => 1 / 2 - phase time / 2
  | .recurrentOne => 1 / 2 + phase time / 2

theorem value_mem_Icc (state : State) (time : ℕ) :
    value state time ∈ Set.Icc (0 : ℝ) 1 := by
  have hphase : -1 ≤ phase time ∧ phase time ≤ 1 := by
    rw [← abs_le, abs_phase]
  cases state <;>
    simp only [value] <;>
    constructor <;> linarith

theorem value_harmonic (state : State) (time : ℕ) :
    value state time =
      expect (kernel state) (fun successor => value successor (time + 1)) := by
  cases state with
  | a =>
      rw [show kernel .a =
        (PMF.uniformOfFintype Bool).map aSuccessor by rfl]
      rw [expect_map,
        Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]
      simp [aSuccessor, value, phase_succ]
      ring
  | b =>
      rw [show kernel .b =
        (PMF.uniformOfFintype Bool).map bSuccessor by rfl]
      rw [expect_map,
        Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]
      simp [bSuccessor, value, phase_succ]
      ring
  | recurrentZero =>
      simp [kernel, value, phase_succ]
      ring
  | recurrentOne =>
      simp [kernel, value, phase_succ]
      ring

theorem value_isUnitIntervalBackwardMarkovHarmonic :
    IsUnitIntervalBackwardMarkovHarmonic kernel value :=
  ⟨value_mem_Icc, value_harmonic⟩

/-- Both directions in the two-state transient block have positive support. -/
theorem a_communicates_b : PMFCommunicates kernel .a .b := by
  constructor
  · apply Relation.ReflTransGen.single
    simp [PMFSupportStep, kernel, aSuccessor]
  · apply Relation.ReflTransGen.single
    simp [PMFSupportStep, kernel, bSuccessor]

/-- The branching row at `b` has both members of its SCC in support. -/
theorem a_mem_support_b : State.a ∈ (kernel .b).support := by
  simp [kernel, bSuccessor]

theorem b_mem_support_b : State.b ∈ (kernel .b).support := by
  simp [kernel, bSuccessor]

private def IsRecurrentLabel (state : State) : Prop :=
  state = .recurrentZero ∨ state = .recurrentOne

private theorem recurrentLabel_of_supportStep
    {source destination : State}
    (source_recurrent : IsRecurrentLabel source)
    (step : PMFSupportStep kernel source destination) :
    IsRecurrentLabel destination := by
  rcases source_recurrent with source_eq | source_eq
  · subst source
    right
    simpa [PMFSupportStep, kernel] using step
  · subst source
    left
    simpa [PMFSupportStep, kernel] using step

private theorem recurrentLabel_of_reachable
    {source destination : State}
    (source_recurrent : IsRecurrentLabel source)
    (reachable : PMFReachable kernel source destination) :
    IsRecurrentLabel destination := by
  induction reachable with
  | refl => exact source_recurrent
  | tail _ step ih => exact recurrentLabel_of_supportStep ih step

private theorem not_reachable_a_from_recurrentOne :
    ¬PMFReachable kernel .recurrentOne .a := by
  intro reachable
  rcases recurrentLabel_of_reachable (Or.inr rfl) reachable with h | h <;>
    cases h

private theorem not_mem_finiteRecurrentCore_a :
    State.a ∉ finiteRecurrentCore kernel := by
  intro a_recurrent
  have class_closed :=
    (mem_finiteRecurrentCore_iff kernel .a).mp a_recurrent
  have recurrentOne_step : PMFSupportStep kernel .a .recurrentOne := by
    simp [PMFSupportStep, kernel, aSuccessor]
  have recurrentOne_mem := class_closed
    (self_mem_pmfCommunicationClass kernel .a) recurrentOne_step
  have communicates :=
    (mem_pmfCommunicationClass_iff kernel .a .recurrentOne).mp recurrentOne_mem
  exact not_reachable_a_from_recurrentOne communicates.2

theorem a_mem_finiteTransientStates : State.a ∈ finiteTransientStates kernel :=
  (mem_finiteTransientStates_iff kernel .a).mpr not_mem_finiteRecurrentCore_a

private theorem not_mem_finiteRecurrentCore_b :
    State.b ∉ finiteRecurrentCore kernel := by
  intro b_recurrent
  apply not_mem_finiteRecurrentCore_a
  apply (mem_finiteRecurrentCore_iff kernel .a).mpr
  rw [pmfCommunicationClass_eq_of_communicates kernel a_communicates_b]
  exact (mem_finiteRecurrentCore_iff kernel .b).mp b_recurrent

theorem b_mem_finiteTransientStates : State.b ∈ finiteTransientStates kernel :=
  (mem_finiteTransientStates_iff kernel .b).mpr not_mem_finiteRecurrentCore_b

/-- This is literally the first intrinsic residual: one transient row has two supported
successors in its own nontrivial communication class. -/
theorem not_hasFunctionalTransientCommunicationClasses :
    ¬HasFunctionalTransientCommunicationClasses kernel := by
  intro functional
  have a_reaches_b : PMFReachable kernel .a .b := a_communicates_b.1
  have a_eq_b := functional b_mem_finiteTransientStates
    a_mem_support_b a_mem_finiteTransientStates a_reaches_b
    b_mem_support_b b_mem_finiteTransientStates Relation.ReflTransGen.refl
  cases a_eq_b

/-- Conditional absolute variation is exactly `1/5` at either transient state and zero on
the recurrent two-cycle. -/
theorem conditionalVariation_eq (state : State) (time : ℕ) :
    expect (kernel state) (fun successor =>
      |value successor (time + 1) - value state time|) =
        if state = .a ∨ state = .b then (1 / 5 : ℝ) else 0 := by
  cases state with
  | a =>
      rw [show kernel .a =
        (PMF.uniformOfFintype Bool).map aSuccessor by rfl]
      rw [expect_map,
        Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]
      simp only [aSuccessor, value, phase_succ]
      have hfirst :
          |(1 / 2 - phase time / 10) -
              (1 / 2 - 3 * phase time / 10)| = (1 / 5 : ℝ) := by
        rw [show (1 / 2 - phase time / 10) -
            (1 / 2 - 3 * phase time / 10) = (1 / 5) * phase time by ring]
        rw [abs_mul, abs_phase]
        norm_num
      have hsecond :
          |(1 / 2 - phase time / 2) -
              (1 / 2 - 3 * phase time / 10)| = (1 / 5 : ℝ) := by
        rw [show (1 / 2 - phase time / 2) -
            (1 / 2 - 3 * phase time / 10) = (-1 / 5) * phase time by ring]
        rw [abs_mul, abs_phase]
        norm_num
      rw [show 1 / 2 + -phase time / 10 = 1 / 2 - phase time / 10 by ring]
      rw [show 1 / 2 + -phase time / 2 = 1 / 2 - phase time / 2 by ring]
      rw [hfirst, hsecond]
      norm_num
  | b =>
      rw [show kernel .b =
        (PMF.uniformOfFintype Bool).map bSuccessor by rfl]
      rw [expect_map,
        Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]
      simp only [bSuccessor, value, phase_succ]
      have hfirst :
          |(1 / 2 + 3 * phase time / 10) -
              (1 / 2 + phase time / 10)| = (1 / 5 : ℝ) := by
        rw [show (1 / 2 + 3 * phase time / 10) -
            (1 / 2 + phase time / 10) = (1 / 5) * phase time by ring]
        rw [abs_mul, abs_phase]
        norm_num
      have hsecond :
          |(1 / 2 - phase time / 10) -
              (1 / 2 + phase time / 10)| = (1 / 5 : ℝ) := by
        rw [show (1 / 2 - phase time / 10) -
            (1 / 2 + phase time / 10) = (-1 / 5) * phase time by ring]
        rw [abs_mul, abs_phase]
        norm_num
      rw [show 1 / 2 - 3 * -phase time / 10 =
        1 / 2 + 3 * phase time / 10 by ring]
      rw [show 1 / 2 + -phase time / 10 = 1 / 2 - phase time / 10 by ring]
      rw [hfirst, hsecond]
      norm_num
  | recurrentZero =>
      simp [kernel, value, phase_succ]
      ring
  | recurrentOne =>
      simp [kernel, value, phase_succ]
      ring

/-- The uncoupled candidate installs the Bernoulli potential at both displayed transient
states and zero on the closed two-cycle. -/
def uncoupledBernoulliPotential (state : State) (time : ℕ) : ℝ :=
  if state = .a ∨ state = .b then
    bernoulliVariationPotential (value state time)
  else 0

theorem bernoulli_value_b_zero_eq_b_one :
    bernoulliVariationPotential (value .b 0) =
      bernoulliVariationPotential (value .b 1) := by
  norm_num [value, phase, bernoulliVariationPotential]

theorem bernoulli_value_a_one :
    bernoulliVariationPotential (value .a 1) = 4 / 5 := by
  have hvalue : value .a 1 = 4 / 5 := by
    norm_num [value, phase]
  rw [hvalue]
  exact DurationPeelingCounterexample.bernoulliVariationPotential_four_fifths

theorem expect_uncoupledBernoulliPotential_b_one :
    expect (kernel .b) (fun successor =>
      uncoupledBernoulliPotential successor 1) =
        (bernoulliVariationPotential (value .a 1) +
          bernoulliVariationPotential (value .b 1)) / 2 := by
  rw [show kernel .b =
    (PMF.uniformOfFintype Bool).map bSuccessor by rfl]
  rw [expect_map,
    Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]
  simp [bSuccessor, uncoupledBernoulliPotential]

/-- The current-state Bernoulli potential already fails at time zero in the smallest
branching SCC.  The strict inequality uses only that every Bernoulli potential is at most
one; no numerical approximation to a square root is involved. -/
theorem uncoupledBernoulliPotential_step_fails :
    uncoupledBernoulliPotential .b 0 <
      expect (kernel .b) (fun successor =>
        |value successor 1 - value .b 0|) +
      expect (kernel .b) (fun successor =>
        uncoupledBernoulliPotential successor 1) := by
  rw [conditionalVariation_eq .b 0]
  simp only [reduceCtorEq, or_true, if_true]
  rw [expect_uncoupledBernoulliPotential_b_one,
    bernoulli_value_a_one, ← bernoulli_value_b_zero_eq_b_one]
  have hbound := bernoulliVariationPotential_le_one_of_mem_Icc
    (value_mem_Icc .b 0)
  simp only [uncoupledBernoulliPotential, reduceCtorEq, or_true, if_true]
  linarith

/-- A state-coupled remaining-variation potential for the exact branching example. -/
def coupledPotential : State → ℝ
  | .a => 4 / 5
  | .b => 6 / 5
  | .recurrentZero => 0
  | .recurrentOne => 0

theorem coupledPotential_nonneg (state : State) : 0 ≤ coupledPotential state := by
  cases state <;> norm_num [coupledPotential]

theorem coupledPotential_le_six_fifths (state : State) :
    coupledPotential state ≤ 6 / 5 := by
  cases state <;> norm_num [coupledPotential]

/-- The coupled potential pays every one-step increment exactly. -/
theorem conditionalVariation_add_expect_coupledPotential
    (state : State) (time : ℕ) :
    expect (kernel state) (fun successor =>
        |value successor (time + 1) - value state time|) +
      expect (kernel state) coupledPotential = coupledPotential state := by
  rw [conditionalVariation_eq]
  cases state with
  | a =>
      rw [show kernel .a =
        (PMF.uniformOfFintype Bool).map aSuccessor by rfl]
      rw [expect_map,
        Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]
      norm_num [aSuccessor, coupledPotential]
  | b =>
      rw [show kernel .b =
        (PMF.uniformOfFintype Bool).map bSuccessor by rfl]
      rw [expect_map,
        Math.ProbabilityMassFunction.expect_uniformOfFintype_bool]
      norm_num [bSuccessor, coupledPotential]
  | recurrentZero => simp [kernel, coupledPotential]
  | recurrentOne => simp [kernel, coupledPotential]

/-- Despite failure of the uncoupled Bernoulli account, the exact branching SCC has total
expected variation at most `6/5`, uniformly over finite horizons and initial states. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_six_fifths
    (initial : State) (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤ 6 / 5 := by
  let potential : State → ℕ → ℝ := fun state _ => coupledPotential state
  exact (finiteExpectedSpaceTimeMarkovVariation_le_initialPotential
    initial kernel value potential
      (fun state _ => coupledPotential_nonneg state)
      (fun state time => by
        simpa [potential] using
          (conditionalVariation_add_expect_coupledPotential state time).le)
      horizon).trans (coupledPotential_le_six_fifths initial)

end TwoStateBranchingSCC

end

end Math.Probability
