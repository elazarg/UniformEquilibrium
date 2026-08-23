/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.Surplus
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityToggles

/-!
# Strict singleton-refusal source witness

This module records the finite singleton-source consequence of terminal
exploitability.  It is independent of the positive-debt dynamic tail: no
compatibility relation between the two extracted witnesses is asserted.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The finite singleton-source consequence of terminal exploitability. -/
structure QuittingStrictSingletonRefusalSourceWitness
    (witness : QuittingTerminalExploitabilityWitness reward) where
  packet : QuittingNormalizedSingletonSourcePacket reward
  packetOwner : ι
  packetOwnerMass_pos : 0 < packet.mass packetOwner
  packetOwnerMass_lt_one : packet.mass packetOwner < 1
  packetTarget_lt_delivery :
    packet.target packetOwner <
      quittingSingletonMixture reward packet.mass packetOwner
  packetDelivery_lt_refusal :
    quittingSingletonMixture reward packet.mass packetOwner <
      quittingSingletonRefusalValue reward packet.mass packetOwner packetOwner

namespace QuittingTerminalExploitabilityWitness

/-- Every terminal exploitability witness has a finite strict-refusal source
packet. -/
theorem nonempty_strictSingletonRefusalSourceWitness
    (witness : QuittingTerminalExploitabilityWitness reward) :
    Nonempty (QuittingStrictSingletonRefusalSourceWitness witness) := by
  letI : Nonempty ι := witness.nonempty_players
  obtain ⟨packet⟩ := witness.nonempty_normalizedSingletonSourcePacket
  obtain ⟨packetOwner, hpacketPos, hpacketLtOne, htargetLt, hrefusal⟩ :=
    witness.exists_active_strictSingletonRefusal packet
  exact ⟨{
    packet := packet
    packetOwner := packetOwner
    packetOwnerMass_pos := hpacketPos
    packetOwnerMass_lt_one := hpacketLtOne
    packetTarget_lt_delivery := htargetLt
    packetDelivery_lt_refusal := hrefusal }⟩

end QuittingTerminalExploitabilityWitness

end GameTheory
