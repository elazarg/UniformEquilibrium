/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ConcentratedSingleton.StrategicDispatch

/-!
# Collision residuals from nonsingleton concentrated packets

The raw concentrated compiler first tests whether the routed terminal is a
singleton.  For a supplied nonsingleton terminal this branch is impossible,
so the compiler directly returns its collision minimum-fiber residual.  This
bridge deliberately needs no terminal-exploitability witness or strategic
opponent label.
-/

noncomputable section

namespace GameTheory

open Filter

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingReprojectionConcentratedPacket

/-- A concentrated packet with a nonsingleton terminal enters the collision
minimum-fiber residual directly. -/
theorem nonempty_collisionMinimumResidual_of_terminal_card_ne_one
    {minimum : QuittingTerminalSemanticPair iota}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (hcard : terminal.val.card ≠ 1)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hscale : ∀ index, 0 < scale index)
    (hscaleTendsto : Tendsto scale atTop (nhds 0)) :
    Nonempty (QuittingConcentratedCollisionMinimumResidual reward minimum
      owner terminal packet) := by
  rcases exists_concentrated_singleton_or_tailEscape_or_otherDefect
      (reward := reward) minimum packet hminimumCarrier hminimum
        hminimumPositive hscale hscaleTendsto with hsingleton | hcollision
  · exact False.elim (hcard hsingleton)
  · obtain ⟨cluster, subseq, hcluster, hsubseq, htail, howner,
      hresidual⟩ := hcollision
    exact ⟨{
      cluster := cluster
      subseq := subseq
      cluster_mem := hcluster
      subseq_strictMono := hsubseq
      tail_tendsto := htail
      ownerDefect_tendsto := howner
      escape_or_otherDefect := hresidual
    }⟩

end QuittingReprojectionConcentratedPacket

end GameTheory
