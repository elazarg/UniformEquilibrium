/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.Additive.CirculationDecomposition
import MathUE.FiniteSerialRelation
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StrictOrbit

/-!
# Reachable simple cycles in the strict coalition-toggle graph

Restrict the chosen strict-toggle successor to coalitions reachable from a
specified seed.  Finite recurrence gives a nonempty closed walk in this
functional graph, and the generic additive-transport reduction extracts a
simple directed cycle.  Every membership toggle flips coalition-cardinality
parity, while a strict improvement cannot be immediately reversed.  On four
players the cycle therefore has even length between four and sixteen.

This is a static reward-table cycle.  Its vertices are already terminal
coalitions; it is not a quitting chronology, Bellman path, hazard schedule,
or equilibrium certificate.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingTerminalExploitabilityWitness

omit [Fintype iota] in
private theorem eq_of_toggle_toggle_eq
    (S : Finset iota) (first second : iota)
    (hreturn : quittingToggleCoalition
      (quittingToggleCoalition S first) second = S) :
    second = first := by
  by_contra hne
  let middle := quittingToggleCoalition S first
  have hpreserve : first ∈ quittingToggleCoalition middle second ↔
      first ∈ middle := by
    by_cases hsecond : second ∈ middle
    · rw [quittingToggleCoalition_of_mem hsecond]
      simp [Ne.symm hne]
    · rw [quittingToggleCoalition_of_notMem hsecond]
      simp [Ne.symm hne]
  have hflip : first ∈ middle ↔ first ∉ S := by
    dsimp only [middle]
    by_cases hfirst : first ∈ S
    · rw [quittingToggleCoalition_of_mem hfirst]
      simp [hfirst]
    · rw [quittingToggleCoalition_of_notMem hfirst]
      simp [hfirst]
  have hsame : first ∈ quittingToggleCoalition middle second ↔ first ∈ S := by
    rw [show quittingToggleCoalition middle second = S by exact hreturn]
  rw [hpreserve, hflip] at hsame
  tauto

/-- Two selected strict membership toggles cannot return immediately to the
same coalition. -/
theorem strictToggleSuccessor_twice_ne
    (witness : QuittingTerminalExploitabilityWitness reward)
    (S : Finset iota) :
    witness.strictToggleSuccessor
        (witness.strictToggleSuccessor S) ≠ S := by
  intro hreturn
  have hplayers :
      witness.strictTogglePlayer (witness.strictToggleSuccessor S) =
        witness.strictTogglePlayer S := by
    apply eq_of_toggle_toggle_eq S
    simpa only [strictToggleSuccessor] using hreturn
  have hfirst := witness.strictToggleSuccessor_gain S
  have hsecond :=
    witness.strictToggleSuccessor_gain (witness.strictToggleSuccessor S)
  rw [hplayers, hreturn] at hsecond
  linarith [witness.terminalGap_pos]

/-- Every selected membership toggle flips coalition-cardinality parity. -/
theorem strictToggleSuccessor_card_mod_two
    (witness : QuittingTerminalExploitabilityWitness reward)
    (S : Finset iota) :
    (witness.strictToggleSuccessor S).card % 2 = (S.card + 1) % 2 := by
  rw [strictToggleSuccessor]
  by_cases hmem : witness.strictTogglePlayer S ∈ S
  · rw [quittingToggleCoalition_of_mem hmem,
      Finset.card_erase_of_mem hmem]
    have hcard : 0 < S.card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  · rw [quittingToggleCoalition_of_notMem hmem,
      Finset.card_insert_of_notMem hmem]

/-- Coalitions reachable from a fixed seed under the selected strict-toggle
successor. -/
def StrictToggleReachableCoalition
    (witness : QuittingTerminalExploitabilityWitness reward)
    (seed : Finset iota) :=
  {S : Finset iota // ∃ time,
    (witness.strictToggleSuccessor^[time]) seed = S}

/-- The selected successor preserves reachability from the seed. -/
def strictToggleReachableNext
    (witness : QuittingTerminalExploitabilityWitness reward)
    (seed : Finset iota)
    (state : witness.StrictToggleReachableCoalition seed) :
    witness.StrictToggleReachableCoalition seed :=
  ⟨witness.strictToggleSuccessor state.1, by
    obtain ⟨time, htime⟩ := state.2
    refine ⟨time + 1, ?_⟩
    rw [show time + 1 = time.succ by omega,
      Function.iterate_succ_apply', htime]⟩

/-- Functional edge graph of selected strict toggles on the reachable
coalition subtype.  An edge identity is its source vertex. -/
def strictToggleReachableGraph
    (witness : QuittingTerminalExploitabilityWitness reward)
    (seed : Finset iota) :
    Math.EdgeGraph
      (witness.StrictToggleReachableCoalition seed)
      (witness.StrictToggleReachableCoalition seed) where
  source := id
  target := witness.strictToggleReachableNext seed

private def periodicCycleWalk
    (witness : QuittingTerminalExploitabilityWitness reward)
    (seed : Finset iota)
    {R : witness.StrictToggleReachableCoalition seed →
      witness.StrictToggleReachableCoalition seed → Prop}
    (hR : ∀ source target,
      R source target ↔ witness.strictToggleReachableNext seed source = target)
    (periodic : Math.FiniteSerialRelation.PeriodicCycle R) :
    ∀ time,
      (witness.strictToggleReachableGraph seed).Walk
        (periodic.vertex 0) (periodic.vertex time)
  | 0 => .nil
  | time + 1 =>
      ((periodicCycleWalk witness seed hR periodic time).concat
        (periodic.vertex time) rfl).castFinish
          ((hR _ _).mp (periodic.edge time))

@[simp] private theorem periodicCycleWalk_length
    (witness : QuittingTerminalExploitabilityWitness reward)
    (seed : Finset iota)
    {R : witness.StrictToggleReachableCoalition seed →
      witness.StrictToggleReachableCoalition seed → Prop}
    (hR : ∀ source target,
      R source target ↔ witness.strictToggleReachableNext seed source = target)
    (periodic : Math.FiniteSerialRelation.PeriodicCycle R) (time : ℕ) :
    (periodicCycleWalk witness seed hR periodic time).length = time := by
  induction time with
  | zero => rfl
  | succ time ih => simp [periodicCycleWalk, ih]

private theorem strictToggleReachableWalk_card_mod_two
    (witness : QuittingTerminalExploitabilityWitness reward)
    (seed : Finset iota)
    {start finish : witness.StrictToggleReachableCoalition seed}
    (walk : (witness.strictToggleReachableGraph seed).Walk start finish) :
    finish.1.card % 2 = (start.1.card + walk.length) % 2 := by
  induction walk with
  | nil => simp
  | @concat middle walk edge legal ih =>
      have hedge := witness.strictToggleSuccessor_card_mod_two edge.1
      change edge = middle at legal
      subst edge
      change
        (witness.strictToggleSuccessor middle.1).card % 2 =
          (start.1.card + (walk.length + 1)) % 2
      omega

private theorem strictToggleReachableGraph_no_length_two
    (witness : QuittingTerminalExploitabilityWitness reward)
    (seed : Finset iota)
    {base : witness.StrictToggleReachableCoalition seed}
    (cycle : (witness.strictToggleReachableGraph seed).Walk base base) :
    cycle.length ≠ 2 := by
  intro hlength
  have hedgesLength : cycle.edges.length = 2 := by
    simpa using hlength
  obtain ⟨first, second, hedges⟩ := List.length_eq_two.mp hedgesLength
  have hsource := cycle.source_head (by rw [hedges]; simp)
  have htarget := cycle.target_getLast (by rw [hedges]; simp)
  have hchain := cycle.edges_isChain
  have hsource' :
      (witness.strictToggleReachableGraph seed).source first = base := by
    simpa [hedges] using hsource
  have htarget' :
      (witness.strictToggleReachableGraph seed).target second = base := by
    simpa [hedges] using htarget
  have hchain' :
      (witness.strictToggleReachableGraph seed).target first =
        (witness.strictToggleReachableGraph seed).source second := by
    simpa [hedges] using hchain
  change first = base at hsource'
  change witness.strictToggleReachableNext seed second = base at htarget'
  change witness.strictToggleReachableNext seed first = second at hchain'
  subst first
  subst second
  exact witness.strictToggleSuccessor_twice_ne base.1
    (congrArg Subtype.val htarget')

/-- A simple selected-toggle cycle whose base is reachable from the supplied
seed.  The graph type records every edge as the chosen strict successor. -/
structure ReachableStrictToggleSimpleCycle
    (witness : QuittingTerminalExploitabilityWitness reward)
    (seed : Finset iota) where
  base : witness.StrictToggleReachableCoalition seed
  cycle : (witness.strictToggleReachableGraph seed).Walk base base
  simple : Math.AdditiveTransport.IsSimpleCycle cycle
  length_even : Even cycle.length
  four_le_length : 4 ≤ cycle.length
  length_le_sixteen : cycle.length ≤ 16

/-- **Reachable simple strict-toggle cycle on four players.**

From every seed, the selected strict-toggle orbit reaches a simple directed
coalition cycle.  Its length is even and lies between four and sixteen. -/
theorem exists_reachableStrictToggleSimpleCycle
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcardPlayers : Fintype.card iota = 4)
    (seed : Finset iota) :
    Nonempty (witness.ReachableStrictToggleSimpleCycle seed) := by
  classical
  let Reachable := witness.StrictToggleReachableCoalition seed
  let next : Reachable → Reachable := witness.strictToggleReachableNext seed
  let R : Reachable → Reachable → Prop := fun source target => next source = target
  letI : Finite Reachable :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype Reachable := Fintype.ofFinite Reachable
  letI : Nonempty Reachable :=
    ⟨⟨seed, ⟨0, rfl⟩⟩⟩
  obtain ⟨periodic⟩ :=
    Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial R
      (fun state => ⟨next state, rfl⟩)
  have hR : ∀ source target, R source target ↔
      witness.strictToggleReachableNext seed source = target := by
    intro source target
    rfl
  let closed :=
    (periodicCycleWalk witness seed hR periodic periodic.period).castFinish
      (by simpa using periodic.vertex_periodic 0)
  have hclosedPos : 0 < closed.length := by
    simpa [closed] using periodic.period_pos
  obtain ⟨base, cycle, hsimple, _hmean⟩ :=
    Math.AdditiveTransport.exists_simpleCycle_cycleMeanDominates
      (G := witness.strictToggleReachableGraph seed)
      (fun _ => (0 : ℝ)) closed hclosedPos
  have hlengthLeCard : cycle.length ≤ Fintype.card Reachable :=
    hsimple.length_le_card
  have hcard : Fintype.card Reachable ≤ 16 := by
    calc
      Fintype.card Reachable ≤ Fintype.card (Finset iota) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = 16 := by simp [Fintype.card_finset, hcardPlayers]
  have hlengthLe : cycle.length ≤ 16 := hlengthLeCard.trans hcard
  have hparity :=
    strictToggleReachableWalk_card_mod_two witness seed cycle
  have hevenMod : cycle.length % 2 = 0 := by omega
  have heven : Even cycle.length := Nat.even_iff.mpr hevenMod
  have hnotTwo :=
    strictToggleReachableGraph_no_length_two witness seed cycle
  have hfour : 4 ≤ cycle.length := by
    have hpos := hsimple.1
    rcases heven with ⟨half, hhalf⟩
    omega
  exact ⟨⟨base, cycle, hsimple, Nat.even_iff.mpr hevenMod,
    hfour, hlengthLe⟩⟩

end QuittingTerminalExploitabilityWitness

end GameTheory
