/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.StrongConcentratedPacketConsumer
import Research.Quitting.FinFourPureNonsingletonCollisionScreening

/-!
# Source-indexed Fin4 pure nonsingleton collision screening

Every nonsingleton minimum-law atom has a selected actual row above the
canonical quadratic scale.  Pure collision screening sends that row through
at most three certified strict edges to a literal singleton, which supplies
the existing strong concentrated-packet adapter and its exact
strategic-versus-collision-minimum consumer.

This is the minimal nonsingleton atlas entrance: it uses neither the
high-tail/low-tail split nor a near-minimum selected row.  It does not assert
that the initial pure overwrite or final pair route is profitable, preserve a
marked cap--Nash root, consume the collision-minimum residual, or prove a
uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter
open MathUE.FiniteBooleanEndpointOrbit
open QuittingNonsingletonMinimumLawTransfer

/-! ## One selected source row -/

/-- One retained selected row whose original atom mass exceeds the canonical
`mu^2 / 8` screening resolution. -/
structure FinFourPureNonsingletonSelectedRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  terminal_card : 1 < source.atom.terminal.val.card
  rows : SelectedRows reward source.point source.atom
  rank : ℕ
  stage_mass_floor :
    source.minimumSingletonClockResolution < selectedStageMass rows rank

namespace FinFourPureNonsingletonSelectedRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The actual prefixed source profile at the retained selected rank. -/
def profile (row : FinFourPureNonsingletonSelectedRow source) :
    (quittingGame reward).BehaviorProfile :=
  prefixedProfile reward row.rows.profiles row.rows.roots row.rank

/-- The actual marked date at the retained selected rank. -/
def stage (row : FinFourPureNonsingletonSelectedRow source) : ℕ :=
  shiftedStage row.rows.roots row.rows.mark row.rank

/-- The canonical `mu^2 / 8` screening and concentrated-packet scale. -/
def lambda (_row : FinFourPureNonsingletonSelectedRow source) : ℝ :=
  source.minimumSingletonClockResolution

/-- The original nonsingleton minimum-law atom as the screening start. -/
def coalition (row : FinFourPureNonsingletonSelectedRow source) :
    QuittingNonsingletonCoalition (Fin 4) :=
  ⟨source.atom.terminal.val, row.terminal_card⟩

/-- The canonical screening scale is positive. -/
theorem lambda_pos (row : FinFourPureNonsingletonSelectedRow source) :
    0 < row.lambda :=
  source.minimumSingletonClockResolution_pos

/-- The original selected atom carries the screening scale. -/
theorem lambda_le_sourceStageMass
    (row : FinFourPureNonsingletonSelectedRow source) :
    row.lambda ≤ quittingStageCoalitionMass reward row.profile row.stage
      (quittingTerminalOfNonsingletonCoalition row.coalition) := by
  simpa only [lambda, profile, stage, coalition,
    quittingTerminalOfNonsingletonCoalition, selectedStageMass] using
      row.stage_mass_floor.le

/-- The exact selected cap-root stack remains retained as source provenance;
no claim is made that the simultaneous pure sibling is cap--Nash. -/
theorem roots_nash (row : FinFourPureNonsingletonSelectedRow source) :
    IsQuittingCapNashRootStack reward (row.rows.roots row.rank)
      (row.rows.profiles row.rank) :=
  row.rows.roots_nash row.rank

/-- The retained stack has its original causal depth. -/
theorem roots_length (row : FinFourPureNonsingletonSelectedRow source) :
    (row.rows.roots row.rank).length = row.rank + 1 :=
  row.rows.roots_length row.rank

/-- Pure screening of this exact selected row reaches a literal singleton
without any tail-excess or near-minimality hypothesis. -/
theorem nonempty_screenedEndpoint
    (row : FinFourPureNonsingletonSelectedRow source) :
    Nonempty (FinFourPureNonsingletonScreenedEndpoint reward source.point.1
      row.profile row.stage row.coalition row.lambda) :=
  quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint
    reward source.point.1 row.profile row.stage row.coalition row.lambda
      source.minimum source.minimumDebt_pos row.lambda_pos
        row.lambda_le_sourceStageMass

end FinFourPureNonsingletonSelectedRow

namespace FinFourMinimumAtomProducer

/-- A nonsingleton source supplies one selected row above the canonical
quadratic resolution, retaining one selected-row family and rank. -/
theorem nonempty_pureNonsingletonSelectedRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hcollision : 1 < source.atom.terminal.val.card) :
    Nonempty (FinFourPureNonsingletonSelectedRow source) := by
  obtain ⟨rows⟩ := QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows
    reward source.point source.atom source.point_mem source.minimum
      source.minimumDebt_pos hcollision
  obtain ⟨rank, hmass⟩ :=
    (rows.eventually_stageMass_gt_square_div_eight source.point_mem).exists
  exact ⟨{
    terminal_card := hcollision
    rows := rows
    rank := rank
    stage_mass_floor := by
      simpa only [minimumSingletonClockResolution] using hmass
  }⟩

end FinFourMinimumAtomProducer

/-! ## Strong packet and existing consumer -/

/-- The selected source row, complete certified screening orbit, literal
singleton endpoint, and strong concentrated packet at the same resolution. -/
structure FinFourPureNonsingletonStrongConcentratedPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  row : FinFourPureNonsingletonSelectedRow source
  endpoint : FinFourPureNonsingletonScreenedEndpoint reward source.point.1
    row.profile row.stage row.coalition row.lambda
  strong : FinFourSingletonStageStrongConcentratedPacket reward
    endpoint.targetProfile endpoint.singleton row.stage row.lambda

namespace FinFourPureNonsingletonStrongConcentratedPacket

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The retained screening orbit has at most three strict profitable edges. -/
theorem edge_count_le_three
    (produced : FinFourPureNonsingletonStrongConcentratedPacket source) :
    produced.endpoint.orbit.terminal_time.val ≤ 3 :=
  produced.endpoint.edge_count_le_three

/-- Every strict edge on the retained source orbit has the literal canonical
paid floor `mu^2 * D_* / 32`. -/
theorem canonical_edge_gain_floor
    (produced : FinFourPureNonsingletonStrongConcentratedPacket source)
    (time : ℕ) (htime : time < produced.endpoint.orbit.terminal_time) :
    let screened := produced.endpoint.screenedEdge time htime
    source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 32 ≤
      quittingSameStageCoalitionGain reward produced.row.profile
        produced.row.stage (produced.endpoint.orbit.orbit time)
          screened.edge.who screened.edge.action := by
  dsimp only
  calc
    source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 32 =
        produced.row.lambda *
          quittingTerminalSemanticDebtSum source.point.1 / 4 := by
      dsimp only [FinFourPureNonsingletonSelectedRow.lambda,
        FinFourMinimumAtomProducer.minimumSingletonClockResolution]
      ring
    _ ≤ quittingSameStageCoalitionGain reward produced.row.profile
          produced.row.stage (produced.endpoint.orbit.orbit time)
          (produced.endpoint.screenedEdge time htime).edge.who
          (produced.endpoint.screenedEdge time htime).edge.action :=
      produced.endpoint.edge_gain_floor source.minimumDebt_pos.le time htime

/-- The strong packet has exactly the canonical selected-source resolution. -/
theorem packet_resolution_eq
    (produced : FinFourPureNonsingletonStrongConcentratedPacket source) :
    produced.strong.adapter.packet.resolution =
      source.minimumSingletonClockResolution := rfl

/-- The singleton target receives at least the exact packet resolution. -/
theorem resolution_le_singletonStageMass
    (produced : FinFourPureNonsingletonStrongConcentratedPacket source) :
    source.minimumSingletonClockResolution ≤
      quittingStageCoalitionMass reward produced.endpoint.targetProfile
        produced.row.stage produced.endpoint.singleton :=
  produced.endpoint.lambda_le_targetStageMass

end FinFourPureNonsingletonStrongConcentratedPacket

/-- A source-attached screened packet together with the existing consumer's
exact result on that same literal packet. -/
structure FinFourPureNonsingletonStrongConcentratedPacketConsumption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  produced : FinFourPureNonsingletonStrongConcentratedPacket source
  result : FinFourStrongConcentratedPacketConsumerResult source produced.strong

namespace FinFourPureNonsingletonStrongConcentratedPacketConsumption

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The checked consumer split preserves the original minimum source and the
exact strong packet produced by the retained screening orbit. -/
theorem strategic_or_collisionMinimumResidual
    (consumption :
      FinFourPureNonsingletonStrongConcentratedPacketConsumption source) :
    FinFourStrongConcentratedPacketStrategicArm source
        consumption.produced.strong ∨
      Nonempty (QuittingConcentratedCollisionMinimumResidual reward
        source.point.1 consumption.produced.strong.packetOwner
          consumption.produced.strong.adapter.routedTerminal
          consumption.produced.strong.adapter.packet) :=
  consumption.result

end FinFourPureNonsingletonStrongConcentratedPacketConsumption

namespace FinFourMinimumAtomProducer

/-- Every nonsingleton minimum-law atom produces a source-attached strong
concentrated packet through the no-tail pure screening route. -/
theorem nonempty_strongConcentratedPacket_of_nonsingleton
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hcollision : 1 < source.atom.terminal.val.card) :
    Nonempty (FinFourPureNonsingletonStrongConcentratedPacket source) := by
  obtain ⟨row⟩ := source.nonempty_pureNonsingletonSelectedRow hcollision
  obtain ⟨endpoint⟩ := row.nonempty_screenedEndpoint
  obtain ⟨strong⟩ :=
    FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass
      endpoint.targetProfile endpoint.singleton row.stage row.lambda
      endpoint.singleton_card row.lambda_pos endpoint.lambda_le_targetStageMass
  exact ⟨{
    row := row
    endpoint := endpoint
    strong := strong
  }⟩

/-- Every nonsingleton minimum-law atom reaches the existing exact
strategic-versus-collision-minimum consumer, without a tail split or copied
self-tail profile. -/
theorem nonempty_strongConcentratedPacketConsumption_of_nonsingleton
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hcollision : 1 < source.atom.terminal.val.card) :
    Nonempty
      (FinFourPureNonsingletonStrongConcentratedPacketConsumption source) := by
  obtain ⟨produced⟩ :=
    source.nonempty_strongConcentratedPacket_of_nonsingleton hcollision
  exact ⟨{
    produced := produced
    result := produced.strong.consumerResult
  }⟩

end FinFourMinimumAtomProducer

end GameTheory
