/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawTangentExtraction

/-!
# Disjoint branches of a finite stopping-law tangent family

This module refines the stopping-law tangent pipeline into a disjointly tagged
partition.  Positive slope is separated from the flat case; within the flat
case, support entry is separated from its absence, and positive charged
circulation from the residual separating-potential co-decrease.

The partition is finite tangent data.  It assumes no terminal exploitability witness,
selected tangent family, or asymptotic chronology.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Entry of one flat normalized reset column into a coordinate which has
zero debt at the semantic base. -/
def HasQuittingStoppingLawFlatSupportEntry
    (base : QuittingTerminalSemanticPair ι) (active : Finset ι)
    (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  let column := quittingActiveDebtTangentExtension active tangent
  ∃ mover ∈ active, ∃ recipient,
    quittingTerminalSemanticDebt base recipient = 0 ∧
      0 < column mover recipient

/-- Positive charged balance of the full signed flat reset columns. -/
def HasQuittingStoppingLawFlatChargedCirculation
    (active : Finset ι) (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  let column := quittingActiveDebtTangentExtension active tangent
  let gain := quittingActiveDebtTangentGain active tangent
  HasNormalizedPositiveChargedCirculation
    (fun mover : {who // who ∈ active} ↦ column mover.1)
    (fun mover : {who // who ∈ active} ↦ gain mover.1)

/-- The separating-potential residual of a flat reset family, retaining the
same-column decrease of a second active debtor. -/
def HasQuittingStoppingLawFlatPotentialCoDecrease
    (active : Finset ι) (tangent : {who // who ∈ active} → ι → ℝ) : Prop :=
  let column := quittingActiveDebtTangentExtension active tangent
  let gain := quittingActiveDebtTangentGain active tangent
  ∃ potential : ι → ℝ, ∃ mover ∈ active, ∃ other ∈ active.erase mover,
    (∀ who, 0 ≤ potential who) ∧
    (∀ source ∈ active,
      gain source ≤ ∑ who, potential who * column source who) ∧
    (∀ source ∈ active, potential source ≤ potential mover) ∧
    column mover mover = -gain mover ∧
    column mover other < 0

/-- A disjointly tagged form of the finite stopping-law tangent alternative.

The last three branches explicitly record flatness.  Successive negations
make this a partition for the selected tangent family: positive slope versus
flat; then support entry versus no entry; then charged circulation versus its
separating-potential alternative. -/
def IsQuittingStoppingLawExhaustiveTangentAlternative
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
      ¬ HasQuittingStoppingLawFlatChargedCirculation active tangent ∧
      HasQuittingStoppingLawFlatPotentialCoDecrease active tangent)

/-- Forgetting the partition tags recovers the existing stopping-law
pipeline alternative. -/
theorem IsQuittingStoppingLawExhaustiveTangentAlternative.toTangentAlternative
    {base : QuittingTerminalSemanticPair ι} {active : Finset ι}
    {tangent : {who // who ∈ active} → ι → ℝ}
    (branch : IsQuittingStoppingLawExhaustiveTangentAlternative
      base active tangent) :
    IsQuittingStoppingLawTangentAlternative base active tangent := by
  rcases branch with hpositive | ⟨_hflat, hentry⟩ |
      ⟨_hflat, _hnoEntry, hcirculation⟩ |
      ⟨_hflat, _hnoEntry, _hnoCirculation, hpotential⟩
  · exact Or.inl hpositive
  · exact Or.inr (Or.inl hentry)
  · exact Or.inr (Or.inr (Or.inl hcirculation))
  · exact Or.inr (Or.inr (Or.inr hpotential))

end GameTheory
