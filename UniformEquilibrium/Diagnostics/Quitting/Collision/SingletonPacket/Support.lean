/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.Surplus
import UniformEquilibrium.Diagnostics.Quitting.Collision.PreemptionCycle
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityToggles
import UniformEquilibrium.Quitting.Classification.SingletonPacketSupport

/-!
# Counterexample consequences of singleton-packet support

The generic support graph and strict-lasso record live in production. A
terminal exploitability witness supplies the strict entrance edge and places its
terminal margin in both the packet target and one supported singleton atom.
-/

noncomputable section

namespace GameTheory

open Finset
open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness

/-- Strict conditional refusal contains one literal strict supported edge. -/
theorem exists_strictSupportedPreferenceEdge
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ owner other,
      0 < packet.mass owner ∧
      0 < packet.mass other ∧
      owner ≠ other ∧
      packet.target owner <
        quittingSingletonMixture reward packet.mass owner ∧
      quittingSingletonMixture reward packet.mass owner <
        quittingSingletonRefusalValue reward packet.mass owner owner ∧
      quittingSingletonRefusalValue reward packet.mass owner owner ≤
        reward (quittingSingletonTerminal other) owner := by
  letI : Nonempty ι := witness.nonempty_players
  obtain ⟨owner, hownerMass, hownerLt, htarget, hrefusal⟩ :=
    witness.exists_active_strictSingletonRefusal packet
  have howner : owner ∈ packet.support :=
    (packet.mem_support_iff owner).2 hownerMass
  obtain ⟨other, hother, hne, hreward⟩ :=
    packet.exists_supported_refusal_le_singletonReward howner hownerLt
  exact ⟨owner, other, hownerMass,
    (packet.mem_support_iff other).1 hother, hne.symm,
    htarget, hrefusal, hreward⟩

/-- Every counterexample packet has a strict supported entrance edge feeding
a finite recurrent weak-preference support class. -/
theorem nonempty_strictSupportedPreferenceLasso
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    Nonempty (QuittingStrictSupportedPreferenceLasso packet) := by
  obtain ⟨entrance, first, hentranceMass, hfirstMass, hne,
      htarget, hrefusal, hfirst⟩ :=
    witness.exists_strictSupportedPreferenceEdge packet
  have hentrance : entrance ∈ packet.support :=
    (packet.mem_support_iff entrance).2 hentranceMass
  have hfirstMem : first ∈ packet.support :=
    (packet.mem_support_iff first).2 hfirstMass
  have hsupport : packet.support.Nontrivial :=
    ⟨entrance, hentrance, first, hfirstMem, hne⟩
  obtain ⟨cycleStart, cycleStop, hcycle, hclosed, hweak⟩ :=
    packet.exists_weakPreferenceClosedOrbit_from hsupport first hfirstMem
  exact ⟨{
    entrance := entrance
    first := first
    entrance_mem := hentrance
    first_mem := hfirstMem
    first_ne := hne.symm
    target_lt_mixture := htarget
    mixture_lt_refusal := hrefusal
    refusal_le_first := hfirst
    support_nontrivial := hsupport
    cycleStart := cycleStart
    cycleStop := cycleStop
    cycleStart_lt_cycleStop := hcycle
    recurrent_closed := hclosed
    recurrent_weak := hweak }⟩

/-! ## The exact two-support residual -/

/-- **Crossed-spectator residual for a two-owner counterexample packet.**
If a counterexample packet is supported on exactly two owners, neither
supported singleton row can be safe for every outsider: the aligned case is
solved by the no-harm singleton compiler.  Packet feasibility then forces two
distinct outsiders with opposite strict inequalities.  The first outsider is
harmed by `first` and helped by `second`; the second outsider is harmed by
`second` and helped by `first`.

Consequently a counterexample packet with two-point support requires at least
four players.  The theorem does not control either outsider's collision payoff
from joining a supported exit; those are the remaining semantic inequalities
for a support-two repair. -/
theorem exists_crossedSpectators_of_support_eq_pair
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {first second : ι} (hne : first ≠ second)
    (hsupport : packet.support = {first, second}) :
    ∃ left right,
      left ∉ packet.support ∧ right ∉ packet.support ∧ left ≠ right ∧
        reward (quittingSingletonTerminal first) left <
          reward (quittingSingletonTerminal left) left ∧
        reward (quittingSingletonTerminal left) left <
          reward (quittingSingletonTerminal second) left ∧
        reward (quittingSingletonTerminal second) right <
          reward (quittingSingletonTerminal right) right ∧
        reward (quittingSingletonTerminal right) right <
          reward (quittingSingletonTerminal first) right := by
  have hbadFirst : ∃ who, who ∉ packet.support ∧
      reward (quittingSingletonTerminal first) who <
        reward (quittingSingletonTerminal who) who := by
    by_contra hno
    push Not at hno
    have houtside : ∀ who, who ∉ packet.support →
        reward (quittingSingletonTerminal who) who ≤
          reward (quittingSingletonTerminal first) who := by
      intro who hwho
      exact hno who hwho
    exact witness.not_exists_uniformEquilibriumPayoff
      (packet.exists_uniformEquilibriumPayoff_of_support_eq_pair_of_first_noHarm
        hne hsupport houtside)
  have hsupportSwap : packet.support = {second, first} := by
    rw [Finset.pair_comm]
    exact hsupport
  have hbadSecond : ∃ who, who ∉ packet.support ∧
      reward (quittingSingletonTerminal second) who <
        reward (quittingSingletonTerminal who) who := by
    by_contra hno
    push Not at hno
    have houtside : ∀ who, who ∉ packet.support →
        reward (quittingSingletonTerminal who) who ≤
          reward (quittingSingletonTerminal second) who := by
      intro who hwho
      exact hno who hwho
    exact witness.not_exists_uniformEquilibriumPayoff
      (packet.exists_uniformEquilibriumPayoff_of_support_eq_pair_of_first_noHarm
        hne.symm hsupportSwap houtside)
  obtain ⟨left, hleftOutside, hleftBad⟩ := hbadFirst
  obtain ⟨right, hrightOutside, hrightBad⟩ := hbadSecond
  have hleftHelped :=
    packet.soloReward_lt_other_of_support_eq_pair_of_lt_solo
      hne hsupport left hleftBad
  have hrightHelped :=
    packet.soloReward_lt_other_of_support_eq_pair_of_lt_solo
      hne.symm hsupportSwap right hrightBad
  have hlr : left ≠ right := by
    intro heq
    subst right
    linarith
  exact ⟨left, right, hleftOutside, hrightOutside, hlr, hleftBad,
    hleftHelped, hrightBad, hrightHelped⟩

/-- **Exact `Fin 4` support-two chamber.**  In a four-player counterexample,
the crossed witnesses above are exactly the two players outside the packet
support. -/
theorem exists_crossedSpectators_of_finFour_support_eq_pair
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {first second : Fin 4} (hne : first ≠ second)
    (hsupport : packet.support = {first, second}) :
    ∃ left right,
      packet.supportᶜ = {left, right} ∧ left ≠ right ∧
        reward (quittingSingletonTerminal first) left <
          reward (quittingSingletonTerminal left) left ∧
        reward (quittingSingletonTerminal left) left <
          reward (quittingSingletonTerminal second) left ∧
        reward (quittingSingletonTerminal second) right <
          reward (quittingSingletonTerminal right) right ∧
        reward (quittingSingletonTerminal right) right <
          reward (quittingSingletonTerminal first) right := by
  obtain ⟨left, right, hleft, hright, hlr, hleftBad, hleftHelped,
      hrightBad, hrightHelped⟩ :=
    witness.exists_crossedSpectators_of_support_eq_pair packet hne hsupport
  have hpairSubset : ({left, right} : Finset (Fin 4)) ⊆ packet.supportᶜ := by
    intro who hwho
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
    rcases hwho with rfl | rfl
    · simpa only [Finset.mem_compl] using hleft
    · simpa only [Finset.mem_compl] using hright
  have hcomplCard : packet.supportᶜ.card = 2 := by
    rw [Finset.card_compl, hsupport, Finset.card_pair hne]
    norm_num
  have hpairCard : ({left, right} : Finset (Fin 4)).card = 2 :=
    Finset.card_pair hlr
  have houtside : ({left, right} : Finset (Fin 4)) = packet.supportᶜ := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    rw [hpairCard, hcomplCard]
  exact ⟨left, right, houtside.symm, hlr, hleftBad, hleftHelped,
    hrightBad, hrightHelped⟩

/-- **Unique full-gap preemptor in the crossed support-two chamber.**
Suppose `owner` and `partner` are exactly the packet owners, while `remaining`
and `sheltered` are exactly the outsiders.  If `sheltered` strictly benefits
from `owner`'s singleton exit, then a viable `owner` can only be preempted by
`remaining`: packet feasibility excludes `partner`, and the strict benefit
excludes `sheltered`.  Without viability, the owner's own singleton payoff is
at most the negative terminal gap.

This conclusion still uses only singleton rows.  It supplies no collision or
larger-coalition payoff inequality. -/
theorem terminalGap_le_negSolo_or_remaining_preempts_of_support_eq_pair
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner partner remaining sheltered : ι} (hne : owner ≠ partner)
    (hsupport : packet.support = {owner, partner})
    (houtside : packet.supportᶜ = {remaining, sheltered})
    (hsheltered : quittingSoloReward reward sheltered sheltered <
      quittingSoloReward reward owner sheltered) :
    witness.terminalGap ≤ -quittingSoloReward reward owner owner ∨
      QuittingSoloPreempts reward witness.terminalGap owner remaining := by
  by_cases hnegative : witness.terminalGap ≤
      -quittingSoloReward reward owner owner
  · exact Or.inl hnegative
  · right
    have hviable : -witness.terminalGap <
        quittingSoloReward reward owner owner := by
      linarith
    obtain ⟨other, hpreempts⟩ := witness.exists_soloPreemptor hviable
    have hpartnerReward : quittingSoloReward reward partner partner ≤
        quittingSoloReward reward owner partner :=
      (packet.soloReward_le_other_of_support_eq_pair hne hsupport).2
    have hotherPartner : other ≠ partner := by
      intro heq
      subst other
      linarith [hpreempts.2, witness.terminalGap_pos]
    have hotherOutside : other ∈ packet.supportᶜ := by
      rw [Finset.mem_compl, hsupport]
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
        ⟨hpreempts.1, hotherPartner⟩
    rw [houtside] at hotherOutside
    simp only [Finset.mem_insert, Finset.mem_singleton] at hotherOutside
    rcases hotherOutside with hremaining | hshelteredOther
    · simpa only [hremaining] using hpreempts
    · subst other
      linarith [hpreempts.2, witness.terminalGap_pos]

/-- In the exact four-player crossed chamber, both supported owners obey the
same two-way alternative: their own singleton payoff is at most the negative
terminal gap, or the spectator harmed by their singleton row preempts them by
the full terminal gap. -/
theorem supportOwners_negative_or_crossedSpectators_preempt
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {first second left right : Fin 4} (hne : first ≠ second)
    (hsupport : packet.support = {first, second})
    (houtside : packet.supportᶜ = {left, right})
    (hleftHelped : quittingSoloReward reward left left <
      quittingSoloReward reward second left)
    (hrightHelped : quittingSoloReward reward right right <
      quittingSoloReward reward first right) :
    (witness.terminalGap ≤ -quittingSoloReward reward first first ∨
        QuittingSoloPreempts reward witness.terminalGap first left) ∧
      (witness.terminalGap ≤ -quittingSoloReward reward second second ∨
        QuittingSoloPreempts reward witness.terminalGap second right) := by
  have hsupportSwap : packet.support = {second, first} := by
    simpa only [Finset.pair_comm] using hsupport
  have houtsideSwap : packet.supportᶜ = {right, left} := by
    simpa only [Finset.pair_comm] using houtside
  exact ⟨
    witness.terminalGap_le_negSolo_or_remaining_preempts_of_support_eq_pair
      packet hne hsupport houtside hrightHelped,
    witness.terminalGap_le_negSolo_or_remaining_preempts_of_support_eq_pair
      packet hne.symm hsupportSwap houtsideSwap hleftHelped⟩

end QuittingTerminalExploitabilityWitness

namespace QuittingNormalizedSingletonSourcePacket

/-- **Two-coordinate projective-Q screen for the crossed chamber.**
On a two-owner packet, the owner pair has a nonnegative normalized singleton
column.  Each crossed helped inequality gives the same pure-column witness for
one owner--spectator pair.  These three principal matrices are therefore
projective Q, so no nonprojective principal matrix can equal any of them.

For an exact `Fin 4` crossed chamber, a two-element nonprojective principal
set is consequently restricted to the two harmed owner--spectator pairs or
the spectator pair.  The theorem does not assert that the residual LCP
principal supplied elsewhere has cardinality two. -/
theorem nonprojectivePrincipal_ne_safePairs_of_support_eq_pair
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {first second left right : ι} (hne : first ≠ second)
    (hsupport : packet.support = {first, second})
    (hleftHelped : quittingSoloReward reward left left <
      quittingSoloReward reward second left)
    (hrightHelped : quittingSoloReward reward right right <
      quittingSoloReward reward first right)
    {players : Finset ι}
    (hnot : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) players)) :
    players ≠ {first, second} ∧ players ≠ {first, right} ∧
      players ≠ {second, left} := by
  have pairProjective (owner sheltered : ι)
      (hharm : quittingSoloReward reward sheltered sheltered ≤
        quittingSoloReward reward owner sheltered) :
      IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward) {owner, sheltered}) := by
    apply (isProjectiveQMatrix_iff_standard_or_homogeneous _).2
    right
    apply Math.LinearProgramming.singletonLCPFeasible_of_diag_eq_zero
      ⟨owner, by simp⟩
    · change normalizedSoloMatrix reward owner owner = 0
      exact normalizedSoloMatrix_diagonal reward owner
    · intro who
      change 0 ≤ normalizedSoloMatrix reward who.1 owner
      rw [normalizedSoloMatrix_eq_soloReward_sub]
      have hwho : who.1 = owner ∨ who.1 = sheltered := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using who.2
      rcases hwho with howner | hsheltered
      · rw [howner, sub_self]
      · rw [hsheltered]
        linarith
  have hownerPair : IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) {first, second}) :=
    pairProjective first second
      (packet.soloReward_le_other_of_support_eq_pair hne hsupport).2
  have hfirstRight : IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) {first, right}) :=
    pairProjective first right hrightHelped.le
  have hsecondLeft : IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) {second, left}) :=
    pairProjective second left hleftHelped.le
  exact ⟨fun heq ↦ hnot (heq ▸ hownerPair),
    fun heq ↦ hnot (heq ▸ hfirstRight),
    fun heq ↦ hnot (heq ▸ hsecondLeft)⟩

end QuittingNormalizedSingletonSourcePacket

namespace QuittingTerminalExploitabilityWitness

/-- The terminal margin is visible in a coordinate of every forced packet's
target. -/
theorem exists_terminalGap_le_packetTarget
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ who, witness.terminalGap ≤ packet.target who := by
  obtain ⟨who, hgap⟩ := witness.exists_terminalGap_le_soloReward
  exact ⟨who, hgap.trans (packet.solo_le_target who)⟩

/-- A positive-mass singleton atom of every forced packet pays some player at
least the counterexample's terminal margin. -/
theorem exists_supportedSingleton_terminalGap
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ who owner, 0 < packet.mass owner ∧
      witness.terminalGap ≤
        reward (quittingSingletonTerminal owner) who := by
  obtain ⟨who, hgap⟩ := witness.exists_terminalGap_le_packetTarget packet
  have hweighted :
      ∑ owner ∈ packet.support,
          packet.mass owner * witness.terminalGap ≤
        ∑ owner ∈ packet.support,
          packet.mass owner *
            reward (quittingSingletonTerminal owner) who := by
    rw [← Finset.sum_mul, packet.sum_support_mass,
      packet.sum_support_mul_singletonReward]
    simpa using hgap.trans (packet.mix_ge_target who)
  obtain ⟨owner, howner, hle⟩ :=
    Finset.exists_le_of_sum_le packet.support_nonempty hweighted
  have hmass : 0 < packet.mass owner :=
    (packet.mem_support_iff owner).mp howner
  refine ⟨who, owner, hmass, ?_⟩
  exact le_of_mul_le_mul_left hle hmass

end QuittingTerminalExploitabilityWitness

end GameTheory
