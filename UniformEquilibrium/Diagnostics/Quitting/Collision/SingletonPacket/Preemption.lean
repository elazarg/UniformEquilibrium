/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.Energy
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary
import UniformEquilibrium.Quitting.Classification.SingletonPacketSupport

/-!
# Singleton-packet support versus strict preemption

Packet energy forces a positive reciprocal-synergy pair in every normalized
packet of a terminal exploitability witness.  The normalized-matrix dictionary
shows that this pair cannot be a two-way strict preemption pair at the positive
terminal margin.

This is a table-level restriction.  It does not place the selected packet pair
on the independently forced preemption cycle.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The packet solo-effect matrix is literally the normalized singleton matrix
used by the LCP gate. -/
theorem normalizedSoloMatrix_eq_quittingSingletonSoloEffect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) :
    normalizedSoloMatrix reward who owner =
      quittingSingletonSoloEffect reward who owner := by
  have hsolo (quitter receiver : ι) :
      quittingSoloReward reward quitter receiver =
        reward (quittingSingletonTerminal quitter) receiver := by
    unfold quittingSoloReward quittingSingletonTerminal
    apply congrArg (fun terminal ↦ reward terminal receiver)
    apply Subtype.ext
    rfl
  rw [normalizedSoloMatrix_eq_soloReward_sub, hsolo, hsolo]
  rfl

namespace QuittingTerminalExploitabilityWitness

/-- Every counterexample packet contains two positive punishment-normal atoms
with positive reciprocal normalized-matrix sum.  At the positive terminal
margin, the selected pair cannot be a strict preemption two-cycle. -/
theorem exists_normal_packetPair_not_mutuallyPreempting
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∃ first second,
      0 < packet.mass first ∧
      0 < packet.mass second ∧
      first ≠ second ∧
      IsQuittingNormalPlayer reward first ∧
      IsQuittingNormalPlayer reward second ∧
      0 < normalizedSoloMatrix reward first second +
        normalizedSoloMatrix reward second first ∧
      ¬(QuittingSoloPreempts reward witness.terminalGap first second ∧
        QuittingSoloPreempts reward witness.terminalGap second first) := by
  obtain ⟨first, second, hfirst, hsecond, hne, hpositive⟩ :=
    witness.exists_supported_pair_pos_reciprocalSoloEffect packet
  refine ⟨first, second, hfirst, hsecond, hne,
    packet.isQuittingNormalPlayer_of_mass_pos first hfirst,
    packet.isQuittingNormalPlayer_of_mass_pos second hsecond, ?_, ?_⟩
  · simpa only [normalizedSoloMatrix_eq_quittingSingletonSoloEffect] using
      hpositive
  · rintro ⟨hforward, hbackward⟩
    have hforwardMatrix :=
      ((quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg
        reward witness.terminalGap first second).1 hforward).2
    have hbackwardMatrix :=
      ((quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg
        reward witness.terminalGap second first).1 hbackward).2
    have hgap := witness.terminalGap_pos
    have hmatrix :
        0 < normalizedSoloMatrix reward first second +
          normalizedSoloMatrix reward second first := by
      simpa only [normalizedSoloMatrix_eq_quittingSingletonSoloEffect] using
        hpositive
    linarith

end QuittingTerminalExploitabilityWitness

end GameTheory
