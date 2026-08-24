/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Promotion of a strict join to a sure-exit candidate

A strict outsider join produces a larger coalition.  That coalition is
either a sure exit set, or its failure is witnessed by a strict leave of an
old member or a strict join of another outsider.  The entering player cannot
be the leaving witness because its anchored inequality has the opposite
strict direction.

This is a finite table-level alternative.  It does not turn the displayed
toggle into a quitting chronology.
-/

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [DecidableEq ι]

/-- A strict outsider join either creates a sure exit set or exposes a
further strict toggle not undoing the anchored join. -/
theorem isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) {entrant : ι} (hentrant : entrant ∉ S)
    (hjoin : quittingSetReward reward S entrant <
      quittingSetReward reward (insert entrant S) entrant) :
    IsQuittingSureExitSet reward (insert entrant S) ∨
      (∃ member ∈ S,
        quittingSetReward reward (insert entrant S) member <
          quittingSetReward reward ((insert entrant S).erase member) member) ∨
      ∃ outsider ∉ insert entrant S,
        quittingSetReward reward (insert entrant S) outsider <
          quittingSetReward reward
            (insert outsider (insert entrant S)) outsider := by
  classical
  by_cases hsure : IsQuittingSureExitSet reward (insert entrant S)
  · exact Or.inl hsure
  · right
    by_cases hmembers : ∀ member ∈ insert entrant S,
        quittingSetReward reward ((insert entrant S).erase member) member ≤
          quittingSetReward reward (insert entrant S) member
    · have houtsiders : ¬∀ outsider ∉ insert entrant S,
          quittingSetReward reward
              (insert outsider (insert entrant S)) outsider ≤
            quittingSetReward reward (insert entrant S) outsider := by
        intro houtsiders
        exact hsure ⟨hmembers, houtsiders⟩
      push Not at houtsiders
      exact Or.inr houtsiders
    · push Not at hmembers
      obtain ⟨member, hmember, hgain⟩ := hmembers
      have hmemberOld : member ∈ S := by
        rcases Finset.mem_insert.mp hmember with heq | hmem
        · subst member
          rw [Finset.erase_insert hentrant] at hgain
          exact absurd hgain (not_lt_of_ge hjoin.le)
        · exact hmem
      exact Or.inl ⟨member, hmemberOld, hgain⟩

end GameTheory
