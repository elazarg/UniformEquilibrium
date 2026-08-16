/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.VanishingDebtAtomAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion

/-!
# Static strategic orientations of a stopping-law terminal atom

A positive terminal payoff-difference atom determines a strict signed-mass
polarity.  When its terminal label is a singleton, the reusable game-facing
strategic output is an atomic coalition-toggle handoff, positive punishment,
or exact player deletion at the supplied exploitability gap.

These static predicates assume no counterexample regime, selected frontier,
or asymptotic rectangle packet.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A positive absorbing terminal-payoff atom has exactly the expected signed
mass polarity.  This is the complete static information present in an atom:
positive reward pairs with increased first-profile mass, and negative reward
pairs with decreased first-profile mass. -/
theorem positive_quittingTerminalPayoffDifferenceAtom_iff_signedMassPolarity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty}) :
    0 < quittingTerminalPayoffDifferenceAtom reward first second observer
        (some terminal) ↔
      (0 < reward terminal observer ∧
          quittingTerminalOutcomeMass reward second (some terminal) <
            quittingTerminalOutcomeMass reward first (some terminal)) ∨
        (reward terminal observer < 0 ∧
          quittingTerminalOutcomeMass reward first (some terminal) <
            quittingTerminalOutcomeMass reward second (some terminal)) := by
  unfold quittingTerminalPayoffDifferenceAtom
  simp only [quittingTerminalOutcomeReward]
  rw [mul_pos_iff]
  constructor
  · rintro (⟨hmass, hreward⟩ | ⟨hmass, hreward⟩)
    · exact Or.inl ⟨hreward, sub_pos.mp hmass⟩
    · exact Or.inr ⟨hreward, sub_neg.mp hmass⟩
  · rintro (⟨hreward, hmass⟩ | ⟨hreward, hmass⟩)
    · exact Or.inl ⟨sub_pos.mpr hmass, hreward⟩
    · exact Or.inr ⟨sub_neg.mpr hmass, hreward⟩

/-- A strict coalition insertion toggle together with the literal unstable
pure atomic row supplied by the positive terminal exploitability floor. -/
def HasQuittingStaticAtomicToggleHandoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty),
    owner ∉ quitters ∧
      reward ⟨quitters, hquitters⟩ owner <
        reward
          ⟨insert owner quitters,
            Finset.insert_nonempty owner quitters⟩ owner ∧
      ∃ who, who ≠ owner ∧ ∃ deviation : PMF Bool,
        quittingRootExpectedPayoff reward 0
            (Function.update
              (QuittingSureSetOwnerRepair.quittingPureSetRoot
                (insert owner quitters)) who deviation) who >
          quittingRootExpectedPayoff reward 0
            (QuittingSureSetOwnerRepair.quittingPureSetRoot
              (insert owner quitters)) who

/-- Exact descent of the same terminal exploitability floor after deleting
one player. -/
def HasQuittingExactPlayerDeletionAtGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (gap : ℝ) : Prop :=
  Nonempty (QuittingDeletedPlayer owner) ∧
    HasTerminalExploitabilityGap
      (quittingDeletePlayerReward reward owner) gap

/-- The game-facing output attached to an observer singleton. -/
def HasQuittingSingletonStaticStrategicDispatch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (gap : ℝ) : Prop :=
  HasQuittingStaticAtomicToggleHandoff reward ∨
    0 < quittingPunishmentValue reward owner ∨
    HasQuittingExactPlayerDeletionAtGap reward owner gap

end GameTheory
