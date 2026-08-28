/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.MinimumReturnForcedPair
import Research.Quitting.FinFourProducerAtlas.MonodromyImpossible
import Research.Quitting.FinFourPureNonsingletonCollisionScreening

/-!
# Source-preserving cofinal singleton frames for the Fin4 atlas

Every monodromy-free producer residual supplies literal singleton endpoints at
strictly increasing ranks of one retained minimum-law chronology.  The
minimum-singleton constructor uses one owner-compression chronology.  The
other constructors reuse exactly the selected rows stored by their entrance.

Frames are indexed by their entrance, so neither the owner-clock chronology
nor the selected-row family can vary across the public packet.  This narrow
prerequisite stops at the cofinal singleton-frame stream; the forced-pair and
completion-mode layers import it without creating a dependency cycle.
-/

noncomputable section

namespace GameTheory

open Filter
open QuittingNonsingletonMinimumLawTransfer

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}

/-! ## Exact entrances -/

/-- The three nonsingleton residual origins.  Its `rows` accessor is the
literal selected-row family already stored by that origin. -/
inductive FinFourSourcePreservingSelectedEntrance
    (source : FinFourMinimumAtomProducer reward bound) : Type
  | purifiedSingleton (producer : FinFourPurifiedSingletonProducer source)
  | terminalSingleton (producer : FinFourTerminalSingletonProducer source)
  | tailEscape
      (producer : TailEscapeSubsequence reward source.point source.atom)

namespace FinFourSourcePreservingSelectedEntrance

/-- The original selected rows, without another chronology selection. -/
def rows (entrance : FinFourSourcePreservingSelectedEntrance source) :
    SelectedRows reward source.point source.atom :=
  match entrance with
  | .purifiedSingleton producer => producer.low.rows
  | .terminalSingleton producer => producer.purification.low.rows
  | .tailEscape producer => producer.rows

end FinFourSourcePreservingSelectedEntrance

/-- The exact monodromy-free entrance.  The singleton constructor stores the
one owner-clock producer used at every later rank. -/
inductive FinFourSourcePreservingSingletonEntrance
    (source : FinFourMinimumAtomProducer reward bound) : Type
  | minimumSingleton
      (terminalCard : source.atom.terminal.val.card = 1)
      (producer : FinFourOwnerCompressedSingletonProducer source)
  | selected
      (entrance : FinFourSourcePreservingSelectedEntrance source)

namespace FinFourSourcePreservingSingletonEntrance

/-- Recover the exact original monodromy-free residual witness. -/
def toResidual
    (entrance : FinFourSourcePreservingSingletonEntrance source) :
    FinFourProducerResidualWithoutMonodromy reward bound :=
  match entrance with
  | .minimumSingleton terminalCard _ =>
      .minimumSingleton source terminalCard
  | .selected (.purifiedSingleton producer) =>
      .purifiedSingleton source producer
  | .selected (.terminalSingleton producer) =>
      .terminalSingleton source producer
  | .selected (.tailEscape producer) =>
      .tailEscape source producer

end FinFourSourcePreservingSingletonEntrance

/-! ## Entrance-indexed frames -/

/-- One literal singleton frame.  The dependent entrance index forces every
frame to use the packet's one producer or one stored selected-row family. -/
inductive FinFourSourcePreservingSingletonFrame
    {source : FinFourMinimumAtomProducer reward bound} :
    FinFourSourcePreservingSingletonEntrance source → Type
  | ownerClock
      {terminalCard : source.atom.terminal.val.card = 1}
      {producer : FinFourOwnerCompressedSingletonProducer source}
      (depth : ℕ)
      (endpoint : FinFourOwnerCompressedSingletonEndpoint source
        producer.chronology producer.owner
          source.minimumSingletonClockResolution depth) :
      FinFourSourcePreservingSingletonFrame
        (.minimumSingleton terminalCard producer)
  | selectedScreening
      (entrance : FinFourSourcePreservingSelectedEntrance source)
      (rank : ℕ)
      (endpoint : FinFourPureNonsingletonScreenedEndpoint reward
        source.point.1
        (prefixedProfile reward entrance.rows.profiles entrance.rows.roots rank)
        (shiftedStage entrance.rows.roots entrance.rows.mark rank)
        ⟨source.atom.terminal.val, entrance.rows.collision⟩
        source.minimumSingletonClockResolution) :
      FinFourSourcePreservingSingletonFrame (.selected entrance)

namespace FinFourSourcePreservingSingletonFrame

variable {entrance : FinFourSourcePreservingSingletonEntrance source}

/-- The exact rank of the retained minimum-law source chronology. -/
def sourceRank (frame : FinFourSourcePreservingSingletonFrame entrance) : ℕ :=
  match frame with
  | .ownerClock _ endpoint => endpoint.rank
  | .selectedScreening _ rank _ => rank

/-- The unmodified suffix profile under the retained cap-root word. -/
def suffixProfile (frame : FinFourSourcePreservingSingletonFrame entrance) :
    (quittingGame reward).BehaviorProfile :=
  match frame with
  | .ownerClock _ endpoint => endpoint.suffixProfile
  | .selectedScreening selected rank _ => selected.rows.profiles rank

/-- The exact retained cap-root word. -/
def rootStack (frame : FinFourSourcePreservingSingletonFrame entrance) :
    List (Fin 4 → PMF Bool) :=
  match frame with
  | .ownerClock _ endpoint => endpoint.rootStack
  | .selectedScreening selected rank _ => selected.rows.roots rank

/-- The literal prefixed source profile at `sourceRank`. -/
def referenceProfile (frame : FinFourSourcePreservingSingletonFrame entrance) :
    (quittingGame reward).BehaviorProfile :=
  match frame with
  | .ownerClock _ endpoint => endpoint.referenceProfile
  | .selectedScreening selected rank _ =>
      prefixedProfile reward selected.rows.profiles selected.rows.roots rank

/-- The actual one-date singleton target. -/
def targetProfile (frame : FinFourSourcePreservingSingletonFrame entrance) :
    (quittingGame reward).BehaviorProfile :=
  match frame with
  | .ownerClock _ endpoint => endpoint.targetProfile
  | .selectedScreening _ _ endpoint => endpoint.targetProfile

/-- The literal marked date in the retained source profile. -/
def stage (frame : FinFourSourcePreservingSingletonFrame entrance) : ℕ :=
  match frame with
  | .ownerClock _ endpoint => endpoint.stage
  | .selectedScreening selected rank _ =>
      shiftedStage selected.rows.roots selected.rows.mark rank

/-- The actual singleton coalition reached at the marked date. -/
def singleton (frame : FinFourSourcePreservingSingletonFrame entrance) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  match frame with
  | .ownerClock _ _ => source.atom.terminal
  | .selectedScreening _ _ endpoint => endpoint.singleton

/-- The source profile is definitionally the retained literal prefix. -/
theorem referenceProfile_eq_literalRootStack
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    frame.referenceProfile =
      quittingLiteralRootStackProfile reward frame.rootStack
        frame.suffixProfile := by
  cases frame <;> rfl

/-- The retained source word has the exact causal length `rank + 1`. -/
theorem rootStack_length
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    frame.rootStack.length = frame.sourceRank + 1 := by
  cases frame with
  | ownerClock depth endpoint => exact endpoint.rootStack_length
  | selectedScreening selected rank endpoint =>
      exact selected.rows.roots_length rank

/-- The retained word remains cap--Nash over its unmodified suffix. -/
theorem rootStack_nash
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    IsQuittingCapNashRootStack reward frame.rootStack frame.suffixProfile := by
  cases frame with
  | ownerClock depth endpoint => exact endpoint.rootStack_nash
  | selectedScreening selected rank endpoint =>
      exact selected.rows.roots_nash rank

/-- Every target coalition is literally a singleton. -/
theorem singleton_card
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    frame.singleton.val.card = 1 := by
  cases frame with
  | ownerClock depth endpoint =>
      rw [singleton, endpoint.terminal_eq_singleton]
      simp
  | selectedScreening selected rank endpoint => exact endpoint.singleton_card

/-- Every target carries the common canonical stage-mass floor. -/
theorem resolution_le_stageMass
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    source.minimumSingletonClockResolution ≤
      quittingStageCoalitionMass reward frame.targetProfile frame.stage
        frame.singleton := by
  cases frame with
  | ownerClock depth endpoint => exact endpoint.target_stageMass_gt.le
  | selectedScreening selected rank endpoint =>
      exact endpoint.lambda_le_targetStageMass

/-- The target differs from its source profile only at the displayed date,
for every player and every finite history. -/
theorem targetProfile_eq_of_time_ne
    (frame : FinFourSourcePreservingSingletonFrame entrance)
    (player : Fin 4) (time : ℕ)
    (history : (quittingGame reward).Hist time)
    (htime : time ≠ frame.stage) :
    frame.targetProfile player time history =
      frame.referenceProfile player time history := by
  cases frame with
  | @ownerClock terminalCard producer depth endpoint =>
      by_cases hplayer : player = producer.owner
      · subst player
        exact congrFun (endpoint.targetProfile_owner_of_ne time htime) history
      · exact congrFun
          (congrFun (endpoint.targetProfile_other_eq player hplayer) time)
          history
  | selectedScreening selected rank endpoint =>
      exact endpoint.targetProfile_eq_of_time_ne player time history htime

/-- Complete post-date behavioral-spine equality. -/
theorem postDateSpine_eq_reference
    (frame : FinFourSourcePreservingSingletonFrame entrance) :
    quittingAllContinueProfileSpine reward frame.targetProfile
        (frame.stage + 1) =
      quittingAllContinueProfileSpine reward frame.referenceProfile
        (frame.stage + 1) := by
  apply quittingAllContinueProfileSpine_eq_of_eq_from
  intro player time history htime
  exact frame.targetProfile_eq_of_time_ne player time history (by omega)

end FinFourSourcePreservingSingletonFrame

/-! ## Cofinal packets -/

/-- One source-preserving cofinal sequence of actual singleton frames. -/
structure FinFourSourcePreservingCofinalSingletonPacket
    {source : FinFourMinimumAtomProducer reward bound}
    (entrance : FinFourSourcePreservingSingletonEntrance source) where
  frame : ℕ → FinFourSourcePreservingSingletonFrame entrance
  sourceRank_strictMono : StrictMono (fun rank => (frame rank).sourceRank)
  suffixLaw_tendsto : Tendsto (fun rank =>
    (quittingTerminalSemanticPair reward (frame rank).suffixProfile,
      quittingTerminalOutcomeMass reward (frame rank).suffixProfile)) atTop
      (nhds source.point)
  referenceDebt_tendsto : Tendsto (fun rank =>
    quittingTerminalDebtSum reward (frame rank).referenceProfile) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1))

namespace FinFourSourcePreservingCofinalSingletonPacket

variable {entrance : FinFourSourcePreservingSingletonEntrance source}

/-- The exact monodromy-free residual retained by the packet. -/
def residual
    (_packet : FinFourSourcePreservingCofinalSingletonPacket entrance) :
    FinFourProducerResidualWithoutMonodromy reward bound :=
  entrance.toResidual

/-- The source rank used by one stream frame. -/
def sourceRank
    (packet : FinFourSourcePreservingCofinalSingletonPacket entrance)
    (rank : ℕ) : ℕ :=
  (packet.frame rank).sourceRank

/-- Stream source ranks are strictly increasing. -/
theorem sourceRank_strictMono'
    (packet : FinFourSourcePreservingCofinalSingletonPacket entrance) :
    StrictMono packet.sourceRank :=
  packet.sourceRank_strictMono

/-- Stream source ranks are cofinal in the retained chronology. -/
theorem sourceRank_tendsto_atTop
    (packet : FinFourSourcePreservingCofinalSingletonPacket entrance) :
    Tendsto packet.sourceRank atTop atTop :=
  packet.sourceRank_strictMono'.tendsto_atTop

/-- Every frame retains the exact cap-root word at its source rank. -/
theorem rootStack_length
    (packet : FinFourSourcePreservingCofinalSingletonPacket entrance)
    (rank : ℕ) :
    (packet.frame rank).rootStack.length = packet.sourceRank rank + 1 :=
  (packet.frame rank).rootStack_length

/-- Every retained source word remains cap--Nash over its suffix. -/
theorem rootStack_nash
    (packet : FinFourSourcePreservingCofinalSingletonPacket entrance)
    (rank : ℕ) :
    IsQuittingCapNashRootStack reward (packet.frame rank).rootStack
      (packet.frame rank).suffixProfile :=
  (packet.frame rank).rootStack_nash

/-- The actual endpoint at every stream rank is a singleton. -/
theorem singleton_card
    (packet : FinFourSourcePreservingCofinalSingletonPacket entrance)
    (rank : ℕ) :
    (packet.frame rank).singleton.val.card = 1 :=
  (packet.frame rank).singleton_card

/-- The canonical scale is carried at every stream rank. -/
theorem resolution_le_stageMass
    (packet : FinFourSourcePreservingCofinalSingletonPacket entrance)
    (rank : ℕ) :
    source.minimumSingletonClockResolution ≤
      quittingStageCoalitionMass reward (packet.frame rank).targetProfile
        (packet.frame rank).stage (packet.frame rank).singleton :=
  (packet.frame rank).resolution_le_stageMass

/-- Full off-date equality at every frame. -/
theorem targetProfile_eq_of_time_ne
    (packet : FinFourSourcePreservingCofinalSingletonPacket entrance)
    (rank : ℕ) (player : Fin 4) (time : ℕ)
    (history : (quittingGame reward).Hist time)
    (htime : time ≠ (packet.frame rank).stage) :
    (packet.frame rank).targetProfile player time history =
      (packet.frame rank).referenceProfile player time history :=
  (packet.frame rank).targetProfile_eq_of_time_ne player time history htime

/-- Full post-date behavioral-spine equality at every frame. -/
theorem postDateSpine_eq_reference
    (packet : FinFourSourcePreservingCofinalSingletonPacket entrance)
    (rank : ℕ) :
    quittingAllContinueProfileSpine reward
        (packet.frame rank).targetProfile ((packet.frame rank).stage + 1) =
      quittingAllContinueProfileSpine reward
        (packet.frame rank).referenceProfile
          ((packet.frame rank).stage + 1) :=
  (packet.frame rank).postDateSpine_eq_reference

end FinFourSourcePreservingCofinalSingletonPacket

/-! ## Constructors -/

private noncomputable def screenedEndpoint
    (selected : FinFourSourcePreservingSelectedEntrance source) (rank : ℕ)
    (hmass : source.minimumSingletonClockResolution <
      selectedStageMass selected.rows rank) :
    FinFourPureNonsingletonScreenedEndpoint reward source.point.1
      (prefixedProfile reward selected.rows.profiles selected.rows.roots rank)
      (shiftedStage selected.rows.roots selected.rows.mark rank)
      ⟨source.atom.terminal.val, selected.rows.collision⟩
      source.minimumSingletonClockResolution :=
  Classical.choice
    (quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint
      reward source.point.1
      (prefixedProfile reward selected.rows.profiles selected.rows.roots rank)
      (shiftedStage selected.rows.roots selected.rows.mark rank)
      ⟨source.atom.terminal.val, selected.rows.collision⟩
      source.minimumSingletonClockResolution source.minimum
      source.minimumDebt_pos source.minimumSingletonClockResolution_pos
      (by simpa only [FinFourMinimumAtomProducer.minimumSingletonClockResolution,
          selectedStageMass, quittingTerminalOfNonsingletonCoalition]
        using hmass.le))

private theorem nonempty_cofinalSingletonPacket_of_selectedEntrance
    (selected : FinFourSourcePreservingSelectedEntrance source) :
    Nonempty (FinFourSourcePreservingCofinalSingletonPacket
      (.selected selected)) := by
  have hevent :=
    selected.rows.eventually_stageMass_gt_square_div_eight source.point_mem
  rw [eventually_atTop] at hevent
  obtain ⟨cutoff, hcutoff⟩ := hevent
  let frame : ℕ →
      FinFourSourcePreservingSingletonFrame (.selected selected) :=
    fun rank => .selectedScreening selected (cutoff + rank)
      (screenedEndpoint selected (cutoff + rank) (by
        simpa only [FinFourMinimumAtomProducer.minimumSingletonClockResolution]
          using hcutoff (cutoff + rank) (by omega)))
  have hindex : StrictMono (fun rank => cutoff + rank) := by
    intro first second hlt
    exact Nat.add_lt_add_left hlt cutoff
  have hrank : StrictMono (fun rank => (frame rank).sourceRank) := by
    simpa only [frame, FinFourSourcePreservingSingletonFrame.sourceRank] using
      hindex
  have hsuffixLaw := selected.rows.profiles_tendsto.comp hindex.tendsto_atTop
  have hdebt := selected.rows.prefix_debt_tendsto.comp hindex.tendsto_atTop
  rw [← source.debt_eq_inf] at hdebt
  exact ⟨{
    frame := frame
    sourceRank_strictMono := hrank
    suffixLaw_tendsto := by
      simpa only [Function.comp_def, frame,
        FinFourSourcePreservingSingletonFrame.suffixProfile] using hsuffixLaw
    referenceDebt_tendsto := by
      simpa only [Function.comp_def, frame,
        FinFourSourcePreservingSingletonFrame.referenceProfile] using hdebt
  }⟩

namespace FinFourMinimumAtomProducer

/-- A singleton minimum atom yields a cofinal packet on exactly one retained
owner-compression chronology. -/
theorem nonempty_sourcePreservingCofinalSingletonPacket_of_singleton
    (source : FinFourMinimumAtomProducer reward bound)
    (terminalCard : source.atom.terminal.val.card = 1) :
    ∃ producer : FinFourOwnerCompressedSingletonProducer source,
      Nonempty (FinFourSourcePreservingCofinalSingletonPacket
        (.minimumSingleton terminalCard producer)) := by
  obtain ⟨producer⟩ :=
    source.nonempty_ownerCompressedSingletonProducer terminalCard
  let endpoint := fun rank =>
    finFourOwnerCompressedCofinalEndpointAt producer
      source.minimumSingletonClockResolution
      source.minimumSingletonClockResolution_pos
      source.minimumSingletonClockResolution_lt_terminalMass rank
  let frame : ℕ → FinFourSourcePreservingSingletonFrame
      (.minimumSingleton terminalCard producer) :=
    fun rank => .ownerClock
      (finFourOwnerCompressedCofinalEndpoint producer
        source.minimumSingletonClockResolution
        source.minimumSingletonClockResolution_pos
        source.minimumSingletonClockResolution_lt_terminalMass rank).1
      (endpoint rank)
  have hindex : StrictMono (fun rank => (endpoint rank).rank) := by
    simpa only [endpoint] using
      strictMono_finFourOwnerCompressedCofinalEndpoint_rank producer
        source.minimumSingletonClockResolution
        source.minimumSingletonClockResolution_pos
        source.minimumSingletonClockResolution_lt_terminalMass
  have hrank : StrictMono (fun rank => (frame rank).sourceRank) := by
    simpa only [frame, endpoint,
      FinFourSourcePreservingSingletonFrame.sourceRank] using hindex
  have hsuffixLaw := producer.chronology.profiles_tendsto.comp
    hindex.tendsto_atTop
  have hdebt := producer.chronology.prefix_debt_tendsto.comp
    hindex.tendsto_atTop
  rw [← source.debt_eq_inf] at hdebt
  exact ⟨producer, ⟨{
    frame := frame
    sourceRank_strictMono := hrank
    suffixLaw_tendsto := by
      simpa only [Function.comp_def, frame, endpoint,
        FinFourSourcePreservingSingletonFrame.suffixProfile,
        FinFourOwnerCompressedSingletonEndpoint.suffixProfile] using hsuffixLaw
    referenceDebt_tendsto := by
      simpa only [Function.comp_def, frame, endpoint,
        FinFourSourcePreservingSingletonFrame.referenceProfile,
        FinFourOwnerCompressedSingletonEndpoint.referenceProfile] using hdebt
  }⟩⟩

end FinFourMinimumAtomProducer

/-- Every monodromy-free entrance produces a cofinal packet whose public
residual projection is definitionally the supplied entrance witness. -/
theorem FinFourProducerResidualWithoutMonodromy.exists_cofinalSingletonPacket
    (residual : FinFourProducerResidualWithoutMonodromy reward bound) :
    ∃ (source : FinFourMinimumAtomProducer reward bound)
        (entrance : FinFourSourcePreservingSingletonEntrance source)
        (packet : FinFourSourcePreservingCofinalSingletonPacket entrance),
      packet.residual = residual := by
  cases residual with
  | minimumSingleton source terminalCard =>
      obtain ⟨producer, ⟨packet⟩⟩ :=
        source.nonempty_sourcePreservingCofinalSingletonPacket_of_singleton
          terminalCard
      exact ⟨source, .minimumSingleton terminalCard producer, packet, rfl⟩
  | purifiedSingleton source producer =>
      obtain ⟨packet⟩ :=
        nonempty_cofinalSingletonPacket_of_selectedEntrance
          (.purifiedSingleton producer)
      exact ⟨source, .selected (.purifiedSingleton producer), packet, rfl⟩
  | terminalSingleton source producer =>
      obtain ⟨packet⟩ :=
        nonempty_cofinalSingletonPacket_of_selectedEntrance
          (.terminalSingleton producer)
      exact ⟨source, .selected (.terminalSingleton producer), packet, rfl⟩
  | tailEscape source producer =>
      obtain ⟨packet⟩ :=
        nonempty_cofinalSingletonPacket_of_selectedEntrance
          (.tailEscape producer)
      exact ⟨source, .selected (.tailEscape producer), packet, rfl⟩

/-- Forgetful nonempty form of the source-preserving constructor. -/
theorem FinFourProducerResidualWithoutMonodromy.nonempty_cofinalSingletonPacket
    (residual : FinFourProducerResidualWithoutMonodromy reward bound) :
    ∃ (source : FinFourMinimumAtomProducer reward bound)
        (entrance : FinFourSourcePreservingSingletonEntrance source),
      Nonempty (FinFourSourcePreservingCofinalSingletonPacket entrance) := by
  obtain ⟨source, entrance, packet, _⟩ :=
    residual.exists_cofinalSingletonPacket
  exact ⟨source, entrance, ⟨packet⟩⟩

/-- Bounded Fin4 data either already has a uniform-equilibrium payoff or
retains the exact entrance residual, its source, and a cofinal packet. -/
theorem uniformPayoff_or_exists_sourcePreservingCofinalSingletonPacket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ (residual : FinFourProducerResidualWithoutMonodromy reward bound)
        (source : FinFourMinimumAtomProducer reward bound)
        (entrance : FinFourSourcePreservingSingletonEntrance source)
        (packet : FinFourSourcePreservingCofinalSingletonPacket entrance),
          packet.residual = residual := by
  rcases uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy
      reward hreward with hpayoff | hresidual
  · exact Or.inl hpayoff
  · obtain ⟨residual⟩ := hresidual
    obtain ⟨source, entrance, packet, heq⟩ :=
      residual.exists_cofinalSingletonPacket
    exact Or.inr ⟨residual, source, entrance, packet, heq⟩

end GameTheory
