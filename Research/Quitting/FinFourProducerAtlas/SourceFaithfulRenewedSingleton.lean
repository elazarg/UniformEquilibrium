/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.StrongConcentratedPacket
import Research.Quitting.FinFourPureNonsingletonCollisionScreening
import Research.Quitting.SourceFaithfulRetainedResolution

/-!
# Source-faithful renewed singleton packets

A source-faithful minimum causalization whose retained terminal is
nonsingleton may be screened after its exact cap--Nash word.  Every requested
positive resolution weakly below the causalization's incoming marked-mass
floor is eventually present at the shifted marked date.  Fin4 pure
nonsingleton screening then reaches a literal singleton through at most three
strict paid edges and one final no-loss pair-to-singleton route.

The resulting packet keeps the supplied suffix profiles, marked dates, exact
root words, and one cofinal tail of their chronology.  Its singleton target
has the requested absolute mass floor and the same complete post-date
behavioral spine as the corresponding prefixed source.  No forced-pair
selection, return, recursive source, or uniform-equilibrium conclusion is
asserted here.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

namespace FinFourSourceFaithfulRenewedSingletonPacket

variable {point : QuittingTerminalSemanticLawPoint (Fin 4)}
variable {terminal : {S : Finset (Fin 4) // S.Nonempty}}
variable {profiles : ℕ → (quittingGame reward).BehaviorProfile}
variable {mark : ℕ → ℕ} {lambda : ℝ}

/-- The original nonsingleton terminal as a screening state. -/
def sourceCoalition (hterminal : 1 < terminal.val.card) :
    QuittingNonsingletonCoalition (Fin 4) :=
  ⟨terminal.val, hterminal⟩

/-- Reindex one cofinal tail of the supplied causalization. -/
def sourceRank (cutoff rank : ℕ) : ℕ := cutoff + rank

/-- The literal exact cap--Nash prefix profile at one retained source rank. -/
def sourceProfile
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda)
    (cutoff rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (causal.roots (sourceRank cutoff rank))
    (profiles (sourceRank cutoff rank))

/-- The original marked date shifted behind the exact prefix word. -/
def sourceMark
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda)
    (cutoff rank : ℕ) : ℕ :=
  sourceRank cutoff rank + 1 + mark (sourceRank cutoff rank)

end FinFourSourceFaithfulRenewedSingletonPacket

/-- A cofinal source-faithful sequence of screened singleton endpoints at one
requested absolute resolution. -/
structure FinFourSourceFaithfulRenewedSingletonPacket
    {point : QuittingTerminalSemanticLawPoint (Fin 4)}
    {terminal : {S : Finset (Fin 4) // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda)
    (terminalNonsingleton : 1 < terminal.val.card)
    (resolution : ℝ) where
  resolution_pos : 0 < resolution
  resolution_le_parent : resolution ≤ lambda
  cutoff : ℕ
  endpoint : ∀ rank,
    FinFourPureNonsingletonScreenedEndpoint reward point.1
      (FinFourSourceFaithfulRenewedSingletonPacket.sourceProfile
        causal cutoff rank)
      (FinFourSourceFaithfulRenewedSingletonPacket.sourceMark
        causal cutoff rank)
      (FinFourSourceFaithfulRenewedSingletonPacket.sourceCoalition
        terminalNonsingleton)
      resolution

namespace FinFourSourceFaithfulRenewedSingletonPacket

variable {point : QuittingTerminalSemanticLawPoint (Fin 4)}
variable {terminal : {S : Finset (Fin 4) // S.Nonempty}}
variable {profiles : ℕ → (quittingGame reward).BehaviorProfile}
variable {mark : ℕ → ℕ} {lambda resolution : ℝ}
variable {causal : QuittingSourceFaithfulMinimumCausalization
  point terminal profiles mark lambda}
variable {terminalNonsingleton : 1 < terminal.val.card}

/-- The selected causalization ranks are strictly increasing. -/
theorem sourceRank_strictMono
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) :
    StrictMono (sourceRank packet.cutoff) := by
  intro first second hlt
  dsimp only [sourceRank]
  omega

/-- The selected causalization ranks are cofinal. -/
theorem sourceRank_tendsto_atTop
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) :
    Tendsto (sourceRank packet.cutoff) atTop atTop :=
  packet.sourceRank_strictMono.tendsto_atTop

/-- Every retained source word has the exact causal length `sourceRank + 1`. -/
theorem sourceRoots_length
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    (causal.roots (sourceRank packet.cutoff rank)).length =
      sourceRank packet.cutoff rank + 1 :=
  causal.roots_length (sourceRank packet.cutoff rank)

/-- Every retained source word remains cap--Nash over its literal supplied
suffix. -/
theorem sourceRoots_nash
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    IsQuittingCapNashRootStack reward
      (causal.roots (sourceRank packet.cutoff rank))
      (profiles (sourceRank packet.cutoff rank)) :=
  causal.roots_nash (sourceRank packet.cutoff rank)

/-- The selected literal prefixed-source debts still converge to the global
minimum value. -/
theorem sourceDebt_tendsto_minimum
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) :
    Tendsto (fun rank ↦ quittingTerminalDebtSum reward
      (sourceProfile causal packet.cutoff rank)) atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
  simpa only [sourceProfile, Function.comp_def] using
    causal.prefix_debt_tendsto.comp packet.sourceRank_tendsto_atTop

/-- Pure screening uses at most three strict profitable edges at every
retained rank. -/
theorem edge_count_le_three
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    (packet.endpoint rank).orbit.terminal_time.val ≤ 3 :=
  (packet.endpoint rank).edge_count_le_three

/-- The requested absolute resolution reaches every singleton target without
loss. -/
theorem resolution_le_singletonStageMass
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    resolution ≤ quittingStageCoalitionMass reward
      (packet.endpoint rank).targetProfile
      (sourceMark causal packet.cutoff rank)
      (packet.endpoint rank).singleton :=
  (packet.endpoint rank).lambda_le_targetStageMass

/-- Every target terminal is literally a singleton. -/
theorem singleton_card
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    (packet.endpoint rank).singleton.val.card = 1 :=
  (packet.endpoint rank).singleton_card

/-- Screening changes no complete behavior after the shifted marked date. -/
theorem endpoint_postDateSpine_eq_source
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    quittingAllContinueProfileSpine reward
        (packet.endpoint rank).targetProfile
        (sourceMark causal packet.cutoff rank + 1) =
      quittingAllContinueProfileSpine reward
        (sourceProfile causal packet.cutoff rank)
        (sourceMark causal packet.cutoff rank + 1) := by
  apply quittingAllContinueProfileSpine_eq_of_eq_from
  intro who time history htime
  exact (packet.endpoint rank).targetProfile_eq_of_time_ne who time history
    (by omega)

/-- Every renewed singleton endpoint produces the generic strong packet at
exactly the same requested resolution. -/
theorem nonempty_strongConcentratedPacket
    (packet : FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) (rank : ℕ) :
    Nonempty (FinFourSingletonStageStrongConcentratedPacket reward
      (packet.endpoint rank).targetProfile
      (packet.endpoint rank).singleton
      (sourceMark causal packet.cutoff rank) resolution) :=
  FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass
    (packet.endpoint rank).targetProfile
    (packet.endpoint rank).singleton
    (sourceMark causal packet.cutoff rank) resolution
    (packet.singleton_card rank) packet.resolution_pos
    (packet.resolution_le_singletonStageMass rank)

end FinFourSourceFaithfulRenewedSingletonPacket

/-- Every positive resolution weakly below the incoming source-faithful
marked-mass floor produces a cofinal renewed singleton packet. -/
theorem nonempty_finFourSourceFaithfulRenewedSingletonPacket
    {point : QuittingTerminalSemanticLawPoint (Fin 4)}
    {terminal : {S : Finset (Fin 4) // S.Nonempty}}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {mark : ℕ → ℕ} {lambda resolution : ℝ}
    (causal : QuittingSourceFaithfulMinimumCausalization
      point terminal profiles mark lambda)
    (terminalNonsingleton : 1 < terminal.val.card)
    (hresolutionPos : 0 < resolution)
    (hresolutionLe : resolution ≤ lambda) :
    Nonempty (FinFourSourceFaithfulRenewedSingletonPacket
      causal terminalNonsingleton resolution) := by
  have hminimumPos : 0 < quittingTerminalSemanticDebtSum point.1 := by
    rw [causal.debt_eq_inf]
    exact causal.inf_pos
  have heventually :=
    causal.eventually_requestedResolution_le_shiftedMarkMass hresolutionLe
  rw [eventually_atTop] at heventually
  obtain ⟨cutoff, hcutoff⟩ := heventually
  let endpoint : ∀ rank,
      FinFourPureNonsingletonScreenedEndpoint reward point.1
        (FinFourSourceFaithfulRenewedSingletonPacket.sourceProfile
          causal cutoff rank)
        (FinFourSourceFaithfulRenewedSingletonPacket.sourceMark
          causal cutoff rank)
        (FinFourSourceFaithfulRenewedSingletonPacket.sourceCoalition
          terminalNonsingleton)
        resolution := fun rank ↦ Classical.choice
      (quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint
        reward point.1
        (FinFourSourceFaithfulRenewedSingletonPacket.sourceProfile
          causal cutoff rank)
        (FinFourSourceFaithfulRenewedSingletonPacket.sourceMark
          causal cutoff rank)
        (FinFourSourceFaithfulRenewedSingletonPacket.sourceCoalition
          terminalNonsingleton)
        resolution causal.minimum hminimumPos hresolutionPos (by
          simpa only [FinFourSourceFaithfulRenewedSingletonPacket.sourceProfile,
            FinFourSourceFaithfulRenewedSingletonPacket.sourceMark,
            FinFourSourceFaithfulRenewedSingletonPacket.sourceRank,
            FinFourSourceFaithfulRenewedSingletonPacket.sourceCoalition,
            quittingTerminalOfNonsingletonCoalition] using
              hcutoff (cutoff + rank) (by omega)))
  exact ⟨{
    resolution_pos := hresolutionPos
    resolution_le_parent := hresolutionLe
    cutoff := cutoff
    endpoint := endpoint
  }⟩

end GameTheory
