/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Packet.Surplus
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
