/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.HarmonicRankedTransientVariation

/-!
# Backward-harmonic variation on functional transient communication classes

The SCC-condensation adapter for `FunctionalTransientLayerCertificate` is canonical.  Rank a
transient state by the number of transient states strictly downstream of its communication
class.  A supported transient edge cannot increase this rank.  It preserves rank exactly
only when the edge stays inside the same communication class.

Consequently, if every transient row has at most one supported successor in its own
communication class, the Bernoulli-plus-rank theorem proves Simon's sharp transient-cardinal
variation bound.  Transient classes may be arbitrarily large and cyclic, and rows may branch
arbitrarily toward downstream classes.  The remaining graph-theoretic regime has a transient
state with two supported successors which both return to it.
-/

namespace Math.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]

/-- Transient states reachable from `source` which cannot return to `source`.  This depends
only on the communication class of `source`. -/
def strictTransientComponentFuture
    (kernel : Omega → PMF Omega) (source : Omega) : Finset Omega := by
  classical
  exact (finiteTransientStates kernel).filter fun destination =>
    PMFReachable kernel source destination ∧
      ¬PMFReachable kernel destination source

theorem mem_strictTransientComponentFuture_iff
    (kernel : Omega → PMF Omega) (source destination : Omega) :
    destination ∈ strictTransientComponentFuture kernel source ↔
      destination ∈ finiteTransientStates kernel ∧
        PMFReachable kernel source destination ∧
          ¬PMFReachable kernel destination source := by
  classical
  simp [strictTransientComponentFuture]

omit [Fintype Omega] [DecidableEq Omega] in
private theorem supportStep_of_mem_support
    (kernel : Omega → PMF Omega) {source destination : Omega}
    (support : destination ∈ (kernel source).support) :
    PMFSupportStep kernel source destination := by
  simpa [PMFSupportStep, PMF.mem_support_iff] using support

/-- A support edge makes the strict downstream component-future shrink weakly. -/
theorem strictTransientComponentFuture_subset_of_support
    (kernel : Omega → PMF Omega) {source destination : Omega}
    (destination_support : destination ∈ (kernel source).support) :
    strictTransientComponentFuture kernel destination ⊆
      strictTransientComponentFuture kernel source := by
  intro state state_future
  obtain ⟨state_transient, destination_reaches_state, state_not_reach_destination⟩ :=
    (mem_strictTransientComponentFuture_iff kernel destination state).mp state_future
  have support_step := supportStep_of_mem_support kernel destination_support
  have source_reaches_destination : PMFReachable kernel source destination :=
    Relation.ReflTransGen.single support_step
  have state_not_reach_source : ¬PMFReachable kernel state source := by
    intro state_reaches_source
    exact state_not_reach_destination
      (state_reaches_source.trans source_reaches_destination)
  apply (mem_strictTransientComponentFuture_iff kernel source state).mpr
  exact ⟨state_transient,
    Relation.ReflTransGen.head support_step destination_reaches_state,
    state_not_reach_source⟩

/-- If a supported edge does not return, its destination lies strictly downstream and the
component-future cardinality strictly decreases. -/
theorem strictTransientComponentFuture_card_lt_of_not_return
    (kernel : Omega → PMF Omega) {source destination : Omega}
    (destination_transient : destination ∈ finiteTransientStates kernel)
    (destination_support : destination ∈ (kernel source).support)
    (not_return : ¬PMFReachable kernel destination source) :
    (strictTransientComponentFuture kernel destination).card <
      (strictTransientComponentFuture kernel source).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨strictTransientComponentFuture_subset_of_support
    kernel destination_support, ?_⟩
  intro future_eq
  have support_step := supportStep_of_mem_support kernel destination_support
  have destination_mem_source_future :
      destination ∈ strictTransientComponentFuture kernel source := by
    apply (mem_strictTransientComponentFuture_iff kernel source destination).mpr
    exact ⟨destination_transient, Relation.ReflTransGen.single support_step,
      not_return⟩
  have destination_not_own_future :
      destination ∉ strictTransientComponentFuture kernel destination := by
    intro destination_future
    exact (mem_strictTransientComponentFuture_iff
      kernel destination destination).mp destination_future |>.2.2
        Relation.ReflTransGen.refl
  exact destination_not_own_future (future_eq ▸ destination_mem_source_future)

/-- Intrinsic hypothesis: inside each transient communication class, one row has at most one
supported successor.  The same row may have arbitrarily many exits to downstream classes. -/
def HasFunctionalTransientCommunicationClasses (kernel : Omega → PMF Omega) : Prop :=
  ∀ ⦃source first second⦄,
    source ∈ finiteTransientStates kernel →
    first ∈ (kernel source).support →
    first ∈ finiteTransientStates kernel →
    PMFReachable kernel first source →
    second ∈ (kernel source).support →
    second ∈ finiteTransientStates kernel →
    PMFReachable kernel second source → first = second

/-- Functional transient communication classes canonically produce the layer certificate. -/
def functionalTransientLayerCertificateOfCommunicationClasses
    (kernel : Omega → PMF Omega)
    (functionalClasses : HasFunctionalTransientCommunicationClasses kernel) :
    FunctionalTransientLayerCertificate kernel := by
  classical
  refine {
    rank := fun state => (strictTransientComponentFuture kernel state).card
    rank_lt_card := ?_
    nonincreasing := ?_
    sameLayer_unique := ?_ }
  · intro state state_transient
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro destination destination_future
      exact (mem_strictTransientComponentFuture_iff kernel state destination).mp
        destination_future |>.1
    · intro future_eq
      have state_not_future :
          state ∉ strictTransientComponentFuture kernel state := by
        intro state_future
        exact (mem_strictTransientComponentFuture_iff
          kernel state state).mp state_future |>.2.2 Relation.ReflTransGen.refl
      exact state_not_future (future_eq.symm ▸ state_transient)
  · intro source destination _source_transient destination_support
      _destination_transient
    exact Finset.card_le_card
      (strictTransientComponentFuture_subset_of_support kernel destination_support)
  · intro source first second source_transient first_support first_transient
      first_layer second_support second_transient second_layer
    have first_returns : PMFReachable kernel first source := by
      by_contra first_not_return
      have hstrict := strictTransientComponentFuture_card_lt_of_not_return
        kernel first_transient first_support first_not_return
      omega
    have second_returns : PMFReachable kernel second source := by
      by_contra second_not_return
      have hstrict := strictTransientComponentFuture_card_lt_of_not_return
        kernel second_transient second_support second_not_return
      omega
    exact functionalClasses source_transient first_support first_transient
      first_returns second_support second_transient second_returns

/-- Sharp intrinsic capstone: functional transient SCCs, with arbitrary downstream branching,
have time-dependent expected variation at most the number of transient states. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_transientCard_of_functionalClasses
    (initial : Omega) (kernel : Omega → PMF Omega)
    (functionalClasses : HasFunctionalTransientCommunicationClasses kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤
      (finiteTransientStates kernel).card := by
  exact finiteExpectedSpaceTimeMarkovVariation_le_transientCard_of_functionalLayers
    initial kernel
      (functionalTransientLayerCertificateOfCommunicationClasses
        kernel functionalClasses)
      value harmonic horizon

/-- Simon's stated total-state cardinality form for functional transient SCCs. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_card_of_functionalClasses
    (initial : Omega) (kernel : Omega → PMF Omega)
    (functionalClasses : HasFunctionalTransientCommunicationClasses kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤
      Fintype.card Omega := by
  exact (finiteExpectedSpaceTimeMarkovVariation_le_transientCard_of_functionalClasses
    initial kernel functionalClasses value harmonic horizon).trans (by
      exact_mod_cast Finset.card_le_card
        (Finset.subset_univ (finiteTransientStates kernel)))

end

end Math.Probability
