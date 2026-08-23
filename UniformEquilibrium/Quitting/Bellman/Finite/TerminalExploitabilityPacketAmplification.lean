/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ChargedPacketAmplification
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness

/-!
# Source-matched packet producers versus canonical capacity

This is the honest game-facing consumer of the generic packet-amplification
theorem.  It accepts a supplied producer of exact reachable predecessor paths;
it does not manufacture such packets from a stopping-law tangent or identify
their charges with a residual gain.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget
open Math.ChargedPathBudget.ChargedRelation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A source-matched exact packet producer is incompatible with a finite
prefix capacity under a terminal exploitability witness.  The producer may be state-dependent,
but must provide a genuine exact reachable relation path at every packet. -/
theorem QuittingTerminalExploitabilityWitness.false_of_uniform_reachable_packet_producer
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {h c : ℝ} (hh : 0 < h) (hc : 0 < c)
    (producer : ∀ state,
      (quittingPunishmentFloorReachableChargedRelation reward).Reaches
        (⟨quittingPunishmentFloorBoxAnchor reward,
          isQuittingPunishmentFloorReachable_anchor⟩ :
          QuittingPunishmentFloorReachableState reward) state →
      ∃ target : QuittingPunishmentFloorReachableState reward,
        Nonempty (TubePacket
        (quittingPunishmentFloorReachableChargedRelation reward)
        Set.univ (fun _ => (0 : ℝ)) h 0 c
        (source := state) (target := target))) :
    False := by
  let start : QuittingPunishmentFloorReachableState reward :=
    ⟨quittingPunishmentFloorBoxAnchor reward,
      isQuittingPunishmentFloorReachable_anchor⟩
  let R := quittingPunishmentFloorReachableChargedRelation reward
  have hcapacity : ∀ {source target : QuittingPunishmentFloorReachableState reward}
      (path : R.Path source target),
      path.chargeSum ≤ quittingPunishmentFloorPrefixChargeBound reward := by
    intro source target path
    exact witness.reachablePath_chargeSum_le_prefixChargeBound path
  apply not_finite_path_capacity_of_uniform_tube_packet R Set.univ
    (fun _ => 0) start (omega := 0) (C := quittingPunishmentFloorPrefixChargeBound reward)
    (hstart := by simp) hh (by norm_num) hc
  · intro state hreach hstate
    obtain ⟨target, packet⟩ := producer state hreach
    exact ⟨target, packet⟩
  · intro source target path
    exact hcapacity path

end GameTheory
