/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Membership-toggle instability under a quitting terminal exploitability witness

Fix a finite quitting game with reward table `r`, extended by `r(∅) = 0` for
nonabsorption, and a terminal exploitability witness: a positive terminal gap by which
every behavioral profile admits a unilateral terminal improvement.  This
module records the quantitative instability that the gap forces on the
finitely many pure sure-exit profiles and on all stationary profiles.

For every coalition `S`, the profile in which exactly the members of `S`
quit at every live history pays `r(S)`, and every unilateral behavior
deviation is worth at most the better of the deviator's two membership
toggles — joining the exit set or leaving it.  Applying the regime's gap to
this profile therefore produces, at every `S`, a player who gains at least
the gap by toggling its own membership.  Splitting on membership gives the
leave-or-join form: some member gains at least the gap by staying behind, or
some outsider gains at least the gap by joining.  In particular no sure exit
set exists, at any coalition including the empty and the grand one.

Reading the toggle at distinguished coalitions yields concrete finite
rejection tests.  At `S = ∅` the only nontrivial toggle is a solo exit, so
some player's solo reward is at least the gap.  At a singleton `S = {owner}`
whose owner's solo reward exceeds `-gap`, the owner's own toggles are ruled
out and some distinct opponent gains at least the gap by colliding with the
owner's exit; combining the two coalitions shows the game has at least two
players.  At `S = univ` there is no outsider, so some player gains at least
the gap by letting the others leave without it.  Finally, since every
unilateral deviation from a stationary profile is capped by the deviator's
selected stationary cap, every stationary root has a player whose cap
exceeds its realized payoff by at least the gap.

All statements are finite, table-level inequalities, intended as search-facing
rejection tests: a candidate reward table on which any one of them fails
cannot carry a terminal exploitability witness.

## Reference and lineage

Quitting games and their uniform equilibria are those of Solan and Vieille,
*Quitting games*, Math. Oper. Res. **26**(2) (2001), 265--285.

The mechanism is not new.  Rejecting a candidate profile by the first-period
unilateral toggles of its exit set is the standard first-stage Nash failure
analysis of the quitting-game literature.  At `S = ∅` it is the solo-exit
test, and at a singleton it is the collision test; the arguments proving
Lemma 2.6 and Lemma 2.7 of Solan and Solan, *Quitting games and linear
complementarity problems*, Math. Oper. Res. **45**(2) (2020), are of exactly
this kind, run against one perturbed stationary row at a time.

What is sharper here is the quantification.  Every inequality below is priced
against one common terminal gap that depends neither on the coalition nor on
the candidate profile, and the toggle statements hold simultaneously at every
coalition, including the empty and the grand one.  That is what turns them
from tests on a candidate into finite rejection tests on the reward table.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness

/-- **No profile is Nash below the gap.**  Under a terminal exploitability witness, no
behavioral profile whatsoever is a terminal `ε`-equilibrium for any tolerance
`ε` smaller than the regime's terminal gap. -/
theorem not_isεAsymptoticNash_of_lt_terminalGap
    (witness : QuittingTerminalExploitabilityWitness reward)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε : ℝ} (hε : ε < witness.terminalGap) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  intro hnash
  obtain ⟨who, dev, hgain⟩ := witness.terminalExploitability profile
  have hupper := hnash who dev
  linarith

/-- **The uniform toggle instability.**  At every coalition `S`, some player
gains at least the terminal gap over `r(S)` by toggling its own membership
in `S`: the better of joining and leaving beats the on-path reward by the
gap. -/
theorem exists_toggle_gain
    (witness : QuittingTerminalExploitabilityWitness reward) (S : Finset ι) :
    ∃ who, quittingSetReward reward S who + witness.terminalGap ≤
      max (quittingSetReward reward (insert who S) who)
        (quittingSetReward reward (S.erase who) who) := by
  obtain ⟨who, dev, hgain⟩ := witness.terminalExploitability
    (quittingStationaryProfile reward (quittingPureSetRoot S))
  refine ⟨who, ?_⟩
  rw [quittingTerminalPayoff_pureSetRoot] at hgain
  exact hgain.trans
    (quittingTerminalPayoff_update_pureSetRoot_le reward S who dev)

/-- **The leave-or-join dichotomy.**  At every coalition `S`, either some
member gains at least the terminal gap by staying behind while the rest of
`S` exits, or some outsider gains at least the terminal gap by joining the
exit.  The trivial toggle at each player is eliminated by positivity of the
gap. -/
theorem exists_leave_or_join_gain
    (witness : QuittingTerminalExploitabilityWitness reward) (S : Finset ι) :
    (∃ member ∈ S,
        quittingSetReward reward S member + witness.terminalGap ≤
          quittingSetReward reward (S.erase member) member) ∨
      ∃ outsider ∉ S,
        quittingSetReward reward S outsider + witness.terminalGap ≤
          quittingSetReward reward (insert outsider S) outsider := by
  obtain ⟨who, hwho⟩ := witness.exists_toggle_gain S
  by_cases hmem : who ∈ S
  · refine Or.inl ⟨who, hmem, ?_⟩
    rw [Finset.insert_eq_self.mpr hmem] at hwho
    rcases le_max_iff.mp hwho with hstay | hleave
    · linarith [witness.terminalGap_pos]
    · exact hleave
  · refine Or.inr ⟨who, hmem, ?_⟩
    rw [Finset.erase_eq_of_notMem hmem] at hwho
    rcases le_max_iff.mp hwho with hjoin | hstay
    · exact hjoin
    · linarith [witness.terminalGap_pos]

/-- **No sure exit set survives.**  Under a terminal exploitability witness, no
coalition — empty, proper, or grand — passes the sure-exit-set test. -/
theorem not_isQuittingSureExitSet
    (witness : QuittingTerminalExploitabilityWitness reward) (S : Finset ι) :
    ¬ IsQuittingSureExitSet reward S := by
  intro h
  obtain ⟨who, hwho⟩ := witness.exists_toggle_gain S
  have hmax := (isQuittingSureExitSet_iff_forall_max reward S).mp h who
  linarith [witness.terminalGap_pos]

/-- **A profitable solo exit exists.**  Reading the toggle at the empty
coalition: some player's solo reward is at least the terminal gap. -/
theorem exists_terminalGap_le_soloReward
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ who, witness.terminalGap ≤ quittingSoloReward reward who who := by
  obtain ⟨who, hwho⟩ := witness.exists_toggle_gain (∅ : Finset ι)
  rw [Finset.insert_empty, Finset.erase_empty, quittingSetReward_empty,
    zero_add, quittingSetReward_singleton_eq_soloReward] at hwho
  rcases le_max_iff.mp hwho with hgain | hzero
  · exact ⟨who, hgain⟩
  · exact absurd hzero (not_le.mpr witness.terminalGap_pos)

/-- **A collision gain at every viable singleton.**  If an owner's solo
reward exceeds the negated terminal gap — in particular whenever it is
nonnegative — then the owner's own toggles at `{owner}` are ruled out, and
some distinct opponent gains at least the gap by joining the owner's exit. -/
theorem exists_collision_gain
    (witness : QuittingTerminalExploitabilityWitness reward) {owner : ι}
    (howner : -witness.terminalGap < quittingSoloReward reward owner owner) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other + witness.terminalGap ≤
        quittingSingletonCollisionReward reward owner other := by
  obtain ⟨who, hwho⟩ := witness.exists_toggle_gain ({owner} : Finset ι)
  by_cases hne : who = owner
  · exfalso
    rw [hne, Finset.insert_eq_self.mpr (Finset.mem_singleton_self owner),
      Finset.erase_singleton, quittingSetReward_empty,
      quittingSetReward_singleton_eq_soloReward] at hwho
    rcases le_max_iff.mp hwho with hstay | hleave
    · linarith [witness.terminalGap_pos]
    · linarith
  · refine ⟨who, hne, ?_⟩
    rw [Finset.erase_eq_of_notMem
        (show who ∉ ({owner} : Finset ι) by simpa using hne),
      quittingSetReward_insert_singleton,
      quittingSetReward_singleton_eq_soloReward] at hwho
    rcases le_max_iff.mp hwho with hjoin | hstay
    · exact hjoin
    · linarith [witness.terminalGap_pos]

/-- Every singleton row has a complete refusal-or-collision alternative.  The
owner either gains the terminal gap by continuing forever, or a distinct
player gains it by joining the owner's singleton exit. -/
theorem singleton_refusal_or_exists_collision_gain
    (witness : QuittingTerminalExploitabilityWitness reward) (owner : ι) :
    witness.terminalGap ≤ -quittingSoloReward reward owner owner ∨
      ∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other + witness.terminalGap ≤
          quittingSingletonCollisionReward reward owner other := by
  rcases witness.exists_leave_or_join_gain ({owner} : Finset ι) with hleave | hjoin
  · obtain ⟨member, hmember, hgain⟩ := hleave
    obtain rfl : member = owner := Finset.mem_singleton.mp hmember
    left
    rw [quittingSetReward_singleton_eq_soloReward, Finset.erase_singleton,
      quittingSetReward_empty] at hgain
    linarith
  · obtain ⟨other, hother, hgain⟩ := hjoin
    right
    refine ⟨other, ?_, ?_⟩
    · simpa using hother
    · rw [quittingSetReward_insert_singleton,
        quittingSetReward_singleton_eq_soloReward] at hgain
      exact hgain

/-- **At least two players.**  The empty-coalition toggle produces an owner
with a profitable solo exit, whose singleton coalition then produces a
distinct colliding opponent. -/
theorem one_lt_card
    (witness : QuittingTerminalExploitabilityWitness reward) :
    1 < Fintype.card ι := by
  obtain ⟨owner, howner⟩ := witness.exists_terminalGap_le_soloReward
  have howner' : -witness.terminalGap <
      quittingSoloReward reward owner owner := by
    linarith [witness.terminalGap_pos]
  obtain ⟨other, hne, -⟩ := witness.exists_collision_gain howner'
  exact Fintype.one_lt_card_iff.mpr ⟨other, owner, hne⟩

/-- **The grand exit leaks.**  At the grand coalition there is no outsider,
so some player gains at least the terminal gap by staying behind while all
the others exit. -/
theorem exists_grandExit_leave_gain
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ who, quittingSetReward reward (Finset.univ : Finset ι) who +
        witness.terminalGap ≤
      quittingSetReward reward (Finset.univ.erase who) who := by
  obtain ⟨who, hwho⟩ := witness.exists_toggle_gain (Finset.univ : Finset ι)
  refine ⟨who, ?_⟩
  rw [Finset.insert_eq_self.mpr (Finset.mem_univ who)] at hwho
  rcases le_max_iff.mp hwho with hstay | hleave
  · linarith [witness.terminalGap_pos]
  · exact hleave

/-- **Every stationary profile is cap-exploitable.**  At every stationary
root, some player's selected stationary cap exceeds that player's realized
terminal payoff by at least the terminal gap.  This is the toggle instability
extended from pure sure-exit roots to arbitrary stationary rows. -/
theorem exists_stationaryCap_gain
    (witness : QuittingTerminalExploitabilityWitness reward) (root : ι → PMF Bool) :
    ∃ who, quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who + witness.terminalGap ≤
      quittingStationaryUnilateralCap reward root who := by
  obtain ⟨who, dev, hgain⟩ := witness.terminalExploitability
    (quittingStationaryProfile reward root)
  exact ⟨who, hgain.trans
    (quittingTerminalPayoff_update_stationary_le_cap reward root who dev)⟩

end QuittingTerminalExploitabilityWitness

end GameTheory
