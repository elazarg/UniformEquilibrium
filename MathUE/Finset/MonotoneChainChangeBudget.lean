/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Change budget for monotone finite-set chains

A strict step in a monotone chain of finite sets increases cardinality. Hence
the number of changes before a cutoff is bounded by the final cardinality
minus the initial cardinality.
-/

namespace Math.Finset.MonotoneChainChangeBudget

variable {α : Type*} [DecidableEq α]

/-- Indices below `cutoff` at which a finite-set sequence changes. -/
def changeTimes (support : ℕ → Finset α) (cutoff : ℕ) : Finset ℕ :=
  (Finset.range cutoff).filter fun phase => support phase ≠ support (phase + 1)

/-- Each change in a monotone finite-set chain consumes at least one unit of
the final cardinality. -/
theorem initialCard_add_changeTimes_card_le_finalCard
    (support : ℕ → Finset α)
    (cutoff : ℕ)
    (hmono : ∀ phase < cutoff, support phase ⊆ support (phase + 1)) :
    (support 0).card + (changeTimes support cutoff).card ≤
      (support cutoff).card := by
  induction cutoff with
  | zero => simp [changeTimes]
  | succ cutoff ih =>
      have hmonoPrefix :
          ∀ phase < cutoff, support phase ⊆ support (phase + 1) := by
        intro phase hphase
        exact hmono phase (hphase.trans (Nat.lt_succ_self cutoff))
      have ihPrefix := ih hmonoPrefix
      by_cases heq : support cutoff = support (cutoff + 1)
      · have hchanges : changeTimes support (cutoff + 1) =
            changeTimes support cutoff := by
          ext phase
          by_cases hphase : phase = cutoff
          · subst phase
            simp [changeTimes, heq]
          · simp only [changeTimes, Finset.mem_filter, Finset.mem_range]
            constructor
            · rintro ⟨hphaseLt, hchange⟩
              exact ⟨by omega, hchange⟩
            · rintro ⟨hphaseLt, hchange⟩
              exact ⟨by omega, hchange⟩
        rw [hchanges, ← heq]
        exact ihPrefix
      · have hstrict : (support cutoff).card < (support (cutoff + 1)).card := by
          have hle := Finset.card_le_card (hmono cutoff (Nat.lt_succ_self cutoff))
          by_contra hnot
          have hreverse : (support (cutoff + 1)).card ≤ (support cutoff).card := by
            omega
          exact heq (Finset.eq_of_subset_of_card_le
            (hmono cutoff (Nat.lt_succ_self cutoff)) hreverse)
        have hchangesSet : changeTimes support (cutoff + 1) =
            insert cutoff (changeTimes support cutoff) := by
          ext phase
          by_cases hphase : phase = cutoff
          · subst phase
            simp [changeTimes, heq]
          · simp only [changeTimes, Finset.mem_filter, Finset.mem_range,
              Finset.mem_insert]
            constructor
            · rintro ⟨hphaseLt, hchange⟩
              exact Or.inr ⟨by omega, hchange⟩
            · rintro (hphaseEq | ⟨hphaseLt, hchange⟩)
              · exact False.elim (hphase hphaseEq)
              · exact ⟨by omega, hchange⟩
        have hnotmem : cutoff ∉ changeTimes support cutoff := by
          simp [changeTimes]
        rw [hchangesSet, Finset.card_insert_of_notMem hnotmem]
        omega

end Math.Finset.MonotoneChainChangeBudget
