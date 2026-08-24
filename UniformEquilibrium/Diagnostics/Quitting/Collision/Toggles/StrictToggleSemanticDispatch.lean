/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.EmptyBaseCompactSeparation
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseConcreteGap
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StrictToggleCycleFaces
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.SupportStatusCells

/-!
# Aggregate semantic dispatch for a reachable strict-toggle cycle

This module packages the three genuine face shapes without erasing their
different residual data.  Successful branches produce an actual fixed
uniform payoff.  The other branches retain the concrete large-base `G` gap,
the punishment-priced singleton `G` gap, or the exact empty-base no-solution
system together with every compact-interior `W` gap.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

variable {witness : QuittingTerminalExploitabilityWitness reward}
variable {seed : Finset ι}

/-- The four honest outputs of the strict-toggle semantic dispatch. -/
def HasQuittingStrictToggleSemanticDispatch
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) : Prop :=
  (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    (2 ≤ cycle.persistentBase.card ∧
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward
            cycle.persistentBase cycle.freePlayers,
          gamma ≤ quittingPersistentLargeBaseExcess reward
            cycle.persistentBase cycle.freePlayers point) ∨
    (∃ owner : ι, cycle.persistentBase = {owner} ∧
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward
            {owner} cycle.freePlayers,
          gamma ≤ quittingSingletonBaseExcess reward owner
            cycle.freePlayers point) ∨
    (cycle.persistentBase = ∅ ∧
      (¬ ∃ root : QuittingRootSimplex ι,
        IsQuittingEmptyBaseSimplexInteriorSolution reward
          cycle.freePlayers root) ∧
      ∀ rho : ℝ, 0 < rho → rho < 1 / 2 →
        ∃ gamma : ℝ, 0 < gamma ∧
          ∀ root ∈ quittingEmptyBaseRhoBox cycle.freePlayers rho,
            gamma ≤ quittingEmptyBaseSimplexDefect reward
              cycle.freePlayers root)

/-- The exact three-way residual after excluding the solved uniform-payoff
output. -/
def HasQuittingStrictToggleSemanticResidual
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) : Prop :=
  (2 ≤ cycle.persistentBase.card ∧
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward
            cycle.persistentBase cycle.freePlayers,
          gamma ≤ quittingPersistentLargeBaseExcess reward
            cycle.persistentBase cycle.freePlayers point) ∨
    (∃ owner : ι, cycle.persistentBase = {owner} ∧
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ point ∈ quittingPersistentBaseNashSet reward
            {owner} cycle.freePlayers,
          gamma ≤ quittingSingletonBaseExcess reward owner
            cycle.freePlayers point) ∨
    (cycle.persistentBase = ∅ ∧
      (¬ ∃ root : QuittingRootSimplex ι,
        IsQuittingEmptyBaseSimplexInteriorSolution reward
          cycle.freePlayers root) ∧
      ∀ rho : ℝ, 0 < rho → rho < 1 / 2 →
        ∃ gamma : ℝ, 0 < gamma ∧
          ∀ root ∈ quittingEmptyBaseRhoBox cycle.freePlayers rho,
            gamma ≤ quittingEmptyBaseSimplexDefect reward
              cycle.freePlayers root)

/-- **Aggregate cycle-to-semantic alternative.**  Every actual reachable
strict-toggle cycle lands in one all-behavior compiler or one of the three
concrete residual chambers, with no supplied compiler certificate. -/
theorem hasQuittingStrictToggleSemanticDispatch
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    cycle.HasQuittingStrictToggleSemanticDispatch := by
  rcases cycle.persistentBase_shape with hempty | hsingleton | hlarge
  · rcases exists_uniformPayoff_or_emptyBase_noSolution_with_rhoGaps
      reward cycle.freePlayers cycle.two_le_card_freePlayers with
      huniform | hresidual
    · exact Or.inl huniform
    · exact Or.inr (Or.inr (Or.inr ⟨hempty, hresidual⟩))
  · obtain ⟨owner, hownerBase⟩ := hsingleton
    have hownerFree : owner ∉ cycle.freePlayers := by
      intro hfree
      exact Finset.disjoint_left.mp cycle.disjoint_persistentBase_freePlayers
        (by simp [hownerBase]) hfree
    rcases exists_uniformPayoff_or_singletonBase_pos_gap
      reward owner cycle.freePlayers hownerFree with huniform | hgap
    · exact Or.inl huniform
    · exact Or.inr (Or.inr (Or.inl ⟨owner, hownerBase, hgap⟩))
  · rcases exists_uniformPayoff_or_persistentLargeBase_pos_gap
      reward cycle.persistentBase cycle.freePlayers
      cycle.disjoint_persistentBase_freePlayers hlarge with
      huniform | hgap
    · exact Or.inl huniform
    · exact Or.inr (Or.inl ⟨hlarge, hgap⟩)

/-- In a putative counterexample, the accepted branch is impossible, so an
actual reachable cycle lands in one of the three concrete residual chambers. -/
theorem hasQuittingStrictToggleSemanticResidual_of_no_uniformPayoff
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hnoUniform : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    cycle.HasQuittingStrictToggleSemanticResidual := by
  exact (cycle.hasQuittingStrictToggleSemanticDispatch.resolve_left hnoUniform)

omit [Nonempty ι] in
/-- Instance-free formulation for an arbitrary four-element player type. -/
def HasQuittingStrictToggleSemanticDispatchOfCardFour
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hfour : Fintype.card ι = 4) : Prop :=
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  cycle.HasQuittingStrictToggleSemanticDispatch

omit [Nonempty ι] in
/-- The aggregate dispatch is genuinely invariant under replacing `Fin 4`
by any finite player type of cardinality four. -/
theorem hasQuittingStrictToggleSemanticDispatch_of_card_four
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hfour : Fintype.card ι = 4) :
    cycle.HasQuittingStrictToggleSemanticDispatchOfCardFour hfour := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  change cycle.HasQuittingStrictToggleSemanticDispatch
  exact cycle.hasQuittingStrictToggleSemanticDispatch

end QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

end GameTheory
