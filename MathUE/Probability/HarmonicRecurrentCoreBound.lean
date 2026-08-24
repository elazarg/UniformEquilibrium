/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.FiniteKernelPeriodicMixing
import MathUE.Probability.FiniteReachableClosedClass

/-!
# Kernel-dependent harmonic variation bounds from recurrent cores

One supplied closed communicating class gives a finite expected-variation
bound whenever every state can reach that same class.  The bound is the
kernel-dependent transience constant of the hitting-time certificate, not the
sharp state-cardinality constant.

For a general finite kernel there may be several disjoint closed classes, so
no one of them need be reachable from every state.  The finite recurrent core
below is the union of all canonical communication classes which are closed.
It is itself closed and reachable from every state.  Local periodic mixing is
used class by class on this union; no common period or phase type is asserted.
-/

namespace Math.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- A supplied closed communicating class reached from every state yields one
kernel-dependent bound, uniform over the initial state, horizon, and bounded
backward-harmonic orbit. -/
theorem exists_finiteExpectedVariation_bound_of_all_reach_closedClass
    [DecidableEq Omega]
    (kernel : Omega → PMF Omega) (anchor : Omega)
    (closedClass : ReachableClosedClass kernel anchor)
    (reachable : ∀ source, ∃ target, target ∈ closedClass.states ∧
      PMFReachable kernel source target) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ initial value, IsUnitIntervalBackwardMarkovHarmonic kernel value →
        ∀ horizon,
          finiteExpectedSpaceTimeMarkovVariation
              initial kernel value horizon ≤ bound := by
  letI : Nonempty Omega := ⟨anchor⟩
  obtain ⟨package⟩ :=
    finiteClosedClassPeriodicMixingPrinciple Omega kernel anchor closedClass
  letI : DecidableEq package.Phase := package.instDecidableEqPhase
  obtain ⟨certificate⟩ := exists_closedCoreTransienceCertificate
    kernel (closedClass.states : Set Omega) package.mixing.closed reachable
  let bound : ℝ :=
    (certificate.horizon : ℝ) / certificate.minorization
  refine ⟨bound, div_nonneg (Nat.cast_nonneg _) certificate.minorization_pos.le,
    ?_⟩
  intro initial value harmonic horizon
  exact package.mixing.finiteExpectedVariation_le_transiencePotential
    certificate initial value harmonic horizon

/-- States whose canonical mutual-reachability class is support-closed.  This
is the union of all recurrent closed communicating classes of the finite
support graph. -/
def finiteRecurrentCore (kernel : Omega → PMF Omega) : Finset Omega := by
  classical
  exact Finset.univ.filter fun state =>
    IsPMFClosed kernel (pmfCommunicationClass kernel state)

theorem mem_finiteRecurrentCore_iff
    (kernel : Omega → PMF Omega) (state : Omega) :
    state ∈ finiteRecurrentCore kernel ↔
      IsPMFClosed kernel (pmfCommunicationClass kernel state) := by
  classical
  simp [finiteRecurrentCore]

/-- Communicating states have the same canonical communication class. -/
theorem pmfCommunicationClass_eq_of_communicates
    (kernel : Omega → PMF Omega) {first second : Omega}
    (communicates : PMFCommunicates kernel first second) :
    pmfCommunicationClass kernel first =
      pmfCommunicationClass kernel second := by
  ext state
  simp only [mem_pmfCommunicationClass_iff]
  constructor
  · intro hstate
    exact ⟨communicates.2.trans hstate.1,
      hstate.2.trans communicates.1⟩
  · intro hstate
    exact ⟨communicates.1.trans hstate.1,
      hstate.2.trans communicates.2⟩

/-- The union of all recurrent communication classes is support-closed. -/
theorem finiteRecurrentCore_closed (kernel : Omega → PMF Omega) :
    IsClosedCore kernel (finiteRecurrentCore kernel : Set Omega) := by
  intro source hsource destination hdestination
  have hsourceClosed :
      IsPMFClosed kernel (pmfCommunicationClass kernel source) :=
    (mem_finiteRecurrentCore_iff kernel source).mp hsource
  have hdestinationClass :
      destination ∈ pmfCommunicationClass kernel source :=
    hsourceClosed (self_mem_pmfCommunicationClass kernel source) hdestination
  have hcommunicates : PMFCommunicates kernel source destination :=
    (mem_pmfCommunicationClass_iff kernel source destination).mp
      hdestinationClass
  apply (mem_finiteRecurrentCore_iff kernel destination).mpr
  rw [← pmfCommunicationClass_eq_of_communicates kernel hcommunicates]
  exact hsourceClosed

/-- Every state reaches some state of the finite recurrent core.  The target
class may depend on the source. -/
theorem exists_reachable_finiteRecurrentCore
    [DecidableEq Omega]
    (kernel : Omega → PMF Omega) (source : Omega) :
    ∃ target, target ∈ finiteRecurrentCore kernel ∧
      PMFReachable kernel source target := by
  obtain ⟨closedClass⟩ := exists_reachableClosedClass kernel source
  refine ⟨closedClass.entry, ?_, closedClass.reachable_entry⟩
  apply (mem_finiteRecurrentCore_iff kernel closedClass.entry).mpr
  rw [← closedClass.states_eq_communicationClass]
  exact closedClass.closed

/-- A recurrent-core state supplies its own canonical reachable closed class.
This retains the source label and avoids choosing a global phase type across
different recurrent classes. -/
def reachableClosedClassOfMemFiniteRecurrentCore
    [DecidableEq Omega]
    (kernel : Omega → PMF Omega) (state : Omega)
    (hstate : state ∈ finiteRecurrentCore kernel) :
    ReachableClosedClass kernel state where
  states := pmfCommunicationClass kernel state
  states_nonempty :=
    ⟨state, self_mem_pmfCommunicationClass kernel state⟩
  closed := (mem_finiteRecurrentCore_iff kernel state).mp hstate
  communicates := communicationClass_communicates kernel state
  entry := state
  entry_mem := self_mem_pmfCommunicationClass kernel state
  reachable_entry := Relation.ReflTransGen.refl

/-- Every one-step increment sourced in the recurrent core is exactly zero.
The periodic mixing package is selected for the source's own communicating
class. -/
theorem expect_abs_increment_eq_zero_of_mem_finiteRecurrentCore
    [DecidableEq Omega]
    (kernel : Omega → PMF Omega) (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    {source : Omega} (hsource : source ∈ finiteRecurrentCore kernel)
    (time : ℕ) :
    expect (kernel source) (fun successor =>
      |value successor (time + 1) - value source time|) = 0 := by
  let closedClass :=
    reachableClosedClassOfMemFiniteRecurrentCore kernel source hsource
  obtain ⟨package⟩ :=
    finiteClosedClassPeriodicMixingPrinciple Omega kernel source closedClass
  letI : DecidableEq package.Phase := package.instDecidableEqPhase
  rw [expect_eq_sum]
  apply Finset.sum_eq_zero
  intro successor _
  by_cases hsuccessor : successor ∈ (kernel source).support
  · have hsourceClass : source ∈ closedClass.states := by
      exact self_mem_pmfCommunicationClass kernel source
    have heq := package.mixing.value_successor_eq_of_mem_core
      value harmonic.1 harmonic.2 hsourceClass hsuccessor time
    rw [heq, sub_self, abs_zero, mul_zero]
  · have hzero : kernel source successor = 0 := by
      simpa [PMF.mem_support_iff] using hsuccessor
    simp [hzero]

/-- Global variation is bounded by expected occupation outside the union of
all recurrent closed classes. -/
theorem finiteExpectedVariation_le_finiteRecurrentCoreOccupation
    [DecidableEq Omega]
    (kernel : Omega → PMF Omega) (initial : Omega)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤
      ∑ time ∈ Finset.range horizon,
        expect (Math.PMFIter.iter kernel time initial)
          (transientCharge (finiteRecurrentCore kernel : Set Omega)) := by
  rw [finiteExpectedSpaceTimeMarkovVariation_eq_sum_iter_conditional]
  apply Finset.sum_le_sum
  intro time _
  apply expect_mono
  intro source
  by_cases hsource : source ∈ finiteRecurrentCore kernel
  · rw [expect_abs_increment_eq_zero_of_mem_finiteRecurrentCore
      kernel value harmonic hsource time]
    simp [transientCharge_of_mem hsource]
  · rw [transientCharge_of_not_mem hsource]
    calc
      expect (kernel source) (fun successor =>
          |value successor (time + 1) - value source time|) ≤
          expect (kernel source) (fun _ => (1 : ℝ)) := by
        apply expect_mono
        intro successor
        rw [abs_le]
        constructor <;>
          linarith [(harmonic.1 successor (time + 1)).1,
            (harmonic.1 successor (time + 1)).2,
            (harmonic.1 source time).1,
            (harmonic.1 source time).2]
      _ = 1 := expect_const _ _

/-- Every finite kernel has a kernel-dependent finite expected-variation
bound, uniform over initial states, horizons, and unit-interval
backward-harmonic orbits.  No state-cardinality estimate is asserted. -/
theorem exists_kernelDependent_finiteExpectedVariation_bound
    [DecidableEq Omega] [Nonempty Omega]
    (kernel : Omega → PMF Omega) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ initial value, IsUnitIntervalBackwardMarkovHarmonic kernel value →
        ∀ horizon,
          finiteExpectedSpaceTimeMarkovVariation
              initial kernel value horizon ≤ bound := by
  obtain ⟨certificate⟩ := exists_closedCoreTransienceCertificate
    kernel (finiteRecurrentCore kernel : Set Omega)
      (finiteRecurrentCore_closed kernel)
      (exists_reachable_finiteRecurrentCore kernel)
  let bound : ℝ :=
    (certificate.horizon : ℝ) / certificate.minorization
  refine ⟨bound, div_nonneg (Nat.cast_nonneg _) certificate.minorization_pos.le,
    ?_⟩
  intro initial value harmonic horizon
  exact (finiteExpectedVariation_le_finiteRecurrentCoreOccupation
    kernel initial value harmonic horizon).trans
      (certificate.total_transientOccupation_le horizon initial)

end

end Math.Probability
