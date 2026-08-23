/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Packet.Defect
import UniformEquilibrium.Quitting.Classification.SingletonPacketEnergy

/-!
# Packet energy restrictions in a terminal exploitability witness

The generic refusal-energy identities and defect comparison live in
`Quitting.Classification.SingletonPacketEnergy`. This adapter rules out
full-mass atoms and specializes the generic identities to counterexample
packets. In particular, every such packet has a positive reciprocal-synergy
pair in its positive support.

These restrictions do not realize that pair as a charged Bellman path.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness

/-- No normalized singleton packet of a terminal exploitability witness has a full-mass
atom. A strict-surplus atom supplies positive mass away from every putative
full atom. -/
theorem normalizedSingletonPacket_mass_lt_one
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) (owner : ι) :
    packet.mass owner < 1 := by
  obtain ⟨selected, hselected, hselectedLt, -, -⟩ :=
    witness.exists_active_strictSingletonRefusal packet
  by_cases heq : owner = selected
  · simpa [heq] using hselectedLt
  · have hmem : owner ∈ (Finset.univ.erase selected : Finset ι) := by
      exact Finset.mem_erase.mpr ⟨heq, Finset.mem_univ owner⟩
    have hownerLe : packet.mass owner ≤
        ∑ other ∈ (Finset.univ.erase selected : Finset ι),
          packet.mass other :=
      Finset.single_le_sum
        (fun other _ => packet.mass_nonneg other) hmem
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset ι)) (f := packet.mass)
      (a := selected) (Finset.mem_univ selected)
    rw [packet.mass_sum] at hsplit
    linarith

/-- In a terminal exploitability witness the aggregate weighted refusal identity is
automatic: strict packet surplus rules out every full-mass denominator. -/
theorem packetWeightedRefusal_eq_quadraticForm
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    quittingPacketWeightedRefusalSurplus packet =
      quittingSingletonPacketQuadraticEnergy reward packet.mass :=
  quittingPacketWeightedRefusal_eq_quadraticForm packet
    (witness.normalizedSingletonPacket_mass_lt_one packet)

/-- **Positive reciprocal pair restriction.** Every normalized singleton
packet of a terminal exploitability witness contains two distinct positive-mass owners
whose reciprocal solo effects have positive sum. -/
theorem exists_supported_pair_pos_reciprocalSoloEffect
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ who owner,
      0 < packet.mass who ∧ 0 < packet.mass owner ∧ who ≠ owner ∧
        0 < quittingSingletonSoloEffect reward who owner +
          quittingSingletonSoloEffect reward owner who := by
  letI : Nonempty ι := witness.nonempty_players
  exact exists_supported_pair_pos_reciprocalSoloEffect_of_packetDefect_pos
    packet
    (quittingNormalizedSingletonPacketDefect_pos witness
      (packet.mass, packet.target) packet.data_mem)

end QuittingTerminalExploitabilityWitness

end GameTheory
