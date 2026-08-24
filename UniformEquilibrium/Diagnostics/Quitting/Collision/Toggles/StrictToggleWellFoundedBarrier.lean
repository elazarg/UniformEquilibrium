/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StrictOrbit

/-!
# No global well-founded descent from strict-toggle orientation alone

In terminal-counterexample semantics every coalition has a strict profitable
membership toggle.  Consequently no natural-valued rank on coalitions can
decrease along every strict toggle.  A well-founded paid-chain iteration must
therefore supply a source-dependent restriction selecting an acyclic subset
of toggles, or attach the toggle to an executable semantic compiler; the
orientation inequality alone cannot be its descent invariant.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal strict improvement when one player flips coalition membership. -/
def IsQuittingStrictMembershipToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (coalition : Finset ι) (who : ι) : Prop :=
  quittingSetReward reward coalition who <
    quittingSetReward reward (quittingToggleCoalition coalition who) who

/-- A terminal exploitability witness rules out every coalition ranking that
decreases along all literal strict membership toggles.  This includes
coalition cardinality and every other coalition-only natural invariant. -/
theorem QuittingTerminalExploitabilityWitness.not_exists_globalStrictToggleRank
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ¬ ∃ rank : Finset ι → ℕ,
      ∀ coalition who,
        IsQuittingStrictMembershipToggle reward coalition who →
          rank (quittingToggleCoalition coalition who) < rank coalition := by
  rintro ⟨rank, decreases⟩
  have impossible : ∀ bound coalition, rank coalition = bound → False := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
        intro coalition hrank
        let who := witness.strictTogglePlayer coalition
        have hstrict : IsQuittingStrictMembershipToggle reward coalition who := by
          exact witness.strictToggleSuccessor_strictGain coalition
        have hlower := decreases coalition who hstrict
        have hsuccessor : quittingToggleCoalition coalition who =
            witness.strictToggleSuccessor coalition := rfl
        rw [hsuccessor, hrank] at hlower
        exact ih (rank (witness.strictToggleSuccessor coalition)) hlower
          (witness.strictToggleSuccessor coalition) rfl
  exact impossible (rank ∅) ∅ rfl

/-! ## Nonvacuous two-label sign regression -/

/-- A two-player reward table whose literal strict-toggle graph contains the
four-cycle `∅ → {false} → {false,true} → {true} → ∅`. -/
def strictToggleRankBarrierReward :
    {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun terminal who ↦
    if terminal.1 = {false} then
      if who = false then 1 else 0
    else if terminal.1 = {false, true} then
      if who = false then 0 else 1
    else if who = false then 1 else -1

theorem strictToggleRankBarrierReward_cycle :
    IsQuittingStrictMembershipToggle strictToggleRankBarrierReward ∅ false ∧
    IsQuittingStrictMembershipToggle strictToggleRankBarrierReward
        ({false} : Finset Bool) true ∧
    IsQuittingStrictMembershipToggle strictToggleRankBarrierReward
        ({false, true} : Finset Bool) false ∧
    IsQuittingStrictMembershipToggle strictToggleRankBarrierReward
        ({true} : Finset Bool) true := by
  have hpair : ({true, false} : Finset Bool) = {false, true} := by decide
  have hpairNeSingleton : ({false, true} : Finset Bool) ≠ {false} := by decide
  have htrueNePair : ({true} : Finset Bool) ≠ {false, true} := by decide
  norm_num [IsQuittingStrictMembershipToggle, quittingToggleCoalition,
    quittingSetReward, strictToggleRankBarrierReward, hpair,
    hpairNeSingleton, htrueNePair]

/-- The explicit sign table admits no natural rank decreasing along its four
displayed strict toggles. -/
theorem strictToggleRankBarrierReward_not_exists_cycleRank :
    ¬ ∃ rank : Finset Bool → ℕ,
      rank ({false} : Finset Bool) < rank ∅ ∧
      rank ({false, true} : Finset Bool) < rank {false} ∧
      rank ({true} : Finset Bool) < rank {false, true} ∧
      rank ∅ < rank {true} := by
  rintro ⟨rank, h01, h12, h23, h30⟩
  omega

end GameTheory
