/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteLinearChargedCapacity
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ExhaustiveTangentAlternative

/-!
# Linear charged capacity of a flat stopping-law tangent family

This module consumes the exact finite circulation-versus-strict-Lyapunov
alternative for the signed columns of a flat stopping-law tangent family.  In
the no-circulation branch the same weight bounds the total charge of every
nonnegative mass vector whose linear endpoint remains in the nonnegative
orthant.

This is a numerical tangent-space conclusion.  Feasible linear masses are not
asserted to be semantic pairs, executable stopping laws, reset paths, or
chronological certificate data.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The charged strict-Lyapunov conclusion for the active signed tangent
columns.  The charge is the negative mover diagonal used by the stopping-law
frontier. -/
def HasQuittingStoppingLawFlatStrictLyapunovWeight
    (active : Finset ι) (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  ∃ weight : ι → ℝ,
    (∀ observer, 1 ≤ weight observer) ∧
      ∀ mover,
        Math.FiniteLinearChargedCapacity.weightedValue weight (tangent mover) ≤
          -quittingActiveDebtTangentGain active tangent mover.1

/-- Exact finite alternative for a flat stopping-law tangent family: either
its signed columns carry a normalized positive charge circulation or one
strictly positive weight decreases along every column by its mover charge. -/
theorem stoppingLawFlatTangent_chargedCirculation_xor_strictLyapunovWeight
    (active : Finset ι) (tangent : {who // who ∈ active} → ι → ℝ)
    (hflat : ∀ mover, ∑ observer, tangent mover observer = 0) :
    Xor
      (HasQuittingStoppingLawFlatChargedCirculation active tangent)
      (HasQuittingStoppingLawFlatStrictLyapunovWeight active tangent) := by
  have halt :=
    Math.FiniteLinearChargedCapacity.normalizedPositiveChargedCirculation_xor_strictWeight
      tangent (fun mover ↦
        quittingActiveDebtTangentGain active tangent mover.1) hflat
  have hcolumn :
      (fun mover : {who // who ∈ active} ↦
        quittingActiveDebtTangentExtension active tangent mover.1) =
        tangent := by
    funext mover observer
    simp [quittingActiveDebtTangentExtension, mover.2]
  unfold HasQuittingStoppingLawFlatChargedCirculation
    HasQuittingStoppingLawFlatStrictLyapunovWeight
  dsimp only
  rw [hcolumn]
  exact halt

/-- In the no-circulation branch, one strict Lyapunov weight gives a common
finite charge bound for every feasible linear plan and every initial debt. -/
theorem exists_stoppingLawFlatStrictWeight_capacityBound_of_noCirculation
    (active : Finset ι) (tangent : {who // who ∈ active} → ι → ℝ)
    (hflat : ∀ mover, ∑ observer, tangent mover observer = 0)
    (hnoCirculation :
      ¬ HasQuittingStoppingLawFlatChargedCirculation active tangent) :
    ∃ weight : ι → ℝ,
      (∀ observer, 1 ≤ weight observer) ∧
      (∀ mover,
        Math.FiniteLinearChargedCapacity.weightedValue weight (tangent mover) ≤
          -quittingActiveDebtTangentGain active tangent mover.1) ∧
      ∀ (debt : ι → ℝ) (mass : {who // who ∈ active} → ℝ),
        Math.FiniteLinearChargedCapacity.IsFeasible debt tangent mass →
          Math.FiniteLinearChargedCapacity.totalCharge
              (fun mover ↦
                quittingActiveDebtTangentGain active tangent mover.1) mass ≤
            Math.FiniteLinearChargedCapacity.weightedValue weight debt := by
  apply
    Math.FiniteLinearChargedCapacity.exists_strictWeight_capacityBound_of_noCirculation
      tangent (fun mover ↦
        quittingActiveDebtTangentGain active tangent mover.1) hflat
  have hcolumn :
      (fun mover : {who // who ∈ active} ↦
        quittingActiveDebtTangentExtension active tangent mover.1) =
        tangent := by
    funext mover observer
    simp [quittingActiveDebtTangentExtension, mover.2]
  unfold HasQuittingStoppingLawFlatChargedCirculation at hnoCirculation
  dsimp only at hnoCirculation
  rw [hcolumn] at hnoCirculation
  exact hnoCirculation

/-- The exhaustive stopping-law frontier with its final potential branch
replaced by the stronger strict-weight and universal linear-capacity
conclusion.  The no-entry tags are retained, but no semantic realizability is
added. -/
def IsQuittingStoppingLawLinearCapacityFrontierBranch
    (base : QuittingTerminalSemanticPair ι) (active : Finset ι)
    (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  (∃ mover, 0 < ∑ observer, tangent mover observer) ∨
    ((∀ mover, ∑ observer, tangent mover observer = 0) ∧
      HasQuittingStoppingLawFlatSupportEntry base active tangent) ∨
    ((∀ mover, ∑ observer, tangent mover observer = 0) ∧
      ¬ HasQuittingStoppingLawFlatSupportEntry base active tangent ∧
      HasQuittingStoppingLawFlatChargedCirculation active tangent) ∨
    ((∀ mover, ∑ observer, tangent mover observer = 0) ∧
      ¬ HasQuittingStoppingLawFlatSupportEntry base active tangent ∧
      ∃ weight : ι → ℝ,
        (∀ observer, 1 ≤ weight observer) ∧
        (∀ mover,
          Math.FiniteLinearChargedCapacity.weightedValue weight
              (tangent mover) ≤
            -quittingActiveDebtTangentGain active tangent mover.1) ∧
        ∀ (debt : ι → ℝ) (mass : {who // who ∈ active} → ℝ),
          Math.FiniteLinearChargedCapacity.IsFeasible debt tangent mass →
            Math.FiniteLinearChargedCapacity.totalCharge
                (fun mover ↦
                  quittingActiveDebtTangentGain active tangent mover.1) mass ≤
              Math.FiniteLinearChargedCapacity.weightedValue weight debt)

/-- Consume the exact linear alternative on the flat/no-entry residual of
any regime-free exhaustive stopping-law frontier witness. -/
theorem IsQuittingStoppingLawExhaustiveTangentAlternative.toLinearCapacityBranch
    {base : QuittingTerminalSemanticPair ι} {active : Finset ι}
    {tangent : {who // who ∈ active} → ι → ℝ}
    (branch : IsQuittingStoppingLawExhaustiveTangentAlternative
      base active tangent) :
    IsQuittingStoppingLawLinearCapacityFrontierBranch base active tangent := by
  rcases branch with hpositive | ⟨hflat, hentry⟩ |
      ⟨hflat, hnoEntry, hcirculation⟩ |
      ⟨hflat, hnoEntry, hnoCirculation, _hpotential⟩
  · exact Or.inl hpositive
  · exact Or.inr (Or.inl ⟨hflat, hentry⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hflat, hnoEntry, hcirculation⟩))
  · obtain ⟨weight, hpositive, hdescent, hcapacity⟩ :=
      exists_stoppingLawFlatStrictWeight_capacityBound_of_noCirculation
        active tangent hflat hnoCirculation
    exact Or.inr (Or.inr (Or.inr
      ⟨hflat, hnoEntry, weight, hpositive, hdescent, hcapacity⟩))

end GameTheory
