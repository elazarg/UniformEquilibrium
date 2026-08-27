/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.ActualLowTail
import Research.Quitting.FinFourProducerAtlas.MonodromyImpossible
import Research.Quitting.FinFourProducerAtlas.StrongConcentratedPacketConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSelfTailClosure

/-!
# Self-tail contraction of the nonsingleton Fin4 minimum-law source

The selected minimum-law rows simultaneously have the canonical quadratic
stage-mass floor and terminal debt arbitrarily close to the fixed minimum.
Copying one sufficiently late row through its marked date and restarting that
complete selected profile gives an actual low-tail passport for the raw
same-stage dispatch.  Its closed-segment arm is impossible, and the remaining
singleton endpoint enters the maintained strong concentrated-packet consumer.

Only the restarted continuation is near-minimal.  No target-side cap--Nash,
near-minimality, return, regeneration, or uniform-payoff conclusion is made.
-/

noncomputable section

namespace GameTheory

open Filter
open QuittingNonsingletonMinimumLawTransfer

/-! ## Simultaneous selected-row passports -/

/-- At one rank of one retained selected-row family, the marked source atom
has the canonical mass floor and the complete prefixed profile has sufficiently
small excess terminal debt over the same minimum point. -/
structure FinFourSelectedSelfTailPassport
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (rows : SelectedRows reward source.point source.atom) (rank : ℕ) : Prop where
  stage_mass_floor :
    source.minimumSingletonClockResolution < selectedStageMass rows rank
  prefix_debt_excess_lt :
    quittingTerminalDebtSum reward
          (prefixedProfile reward rows.profiles rows.roots rank) -
        quittingTerminalSemanticDebtSum source.point.1 <
      source.minimumSingletonClockResolution *
        quittingTerminalSemanticDebtSum source.point.1 / 2

namespace QuittingNonsingletonMinimumLawTransfer.SelectedRows

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Every sufficiently late selected row simultaneously has the exact mass
and debt bounds needed by its self-tail closure. -/
theorem eventually_finFourSelectedSelfTailPassport
    (rows : SelectedRows reward source.point source.atom) :
    ∀ᶠ rank in atTop, FinFourSelectedSelfTailPassport source rows rank := by
  have hmass := rows.eventually_stageMass_gt_square_div_eight source.point_mem
  have hdebtTendsto : Tendsto (fun rank ↦
      quittingTerminalDebtSum reward
          (prefixedProfile reward rows.profiles rows.roots rank) -
        quittingTerminalSemanticDebtSum source.point.1)
      atTop (nhds 0) := by
    have hprefix := rows.prefix_debt_tendsto
    rw [← source.debt_eq_inf] at hprefix
    have hsub := hprefix.sub_const
      (quittingTerminalSemanticDebtSum source.point.1)
    simpa only [sub_self] using hsub
  have hthresholdPos : 0 < source.minimumSingletonClockResolution *
      quittingTerminalSemanticDebtSum source.point.1 / 2 :=
    div_pos
      (mul_pos source.minimumSingletonClockResolution_pos source.minimumDebt_pos)
      (by norm_num)
  have hdebt := hdebtTendsto.eventually_lt_const hthresholdPos
  filter_upwards [hmass, hdebt] with rank hmassRank hdebtRank
  exact {
    stage_mass_floor := by
      simpa only [FinFourMinimumAtomProducer.minimumSingletonClockResolution]
        using hmassRank
    prefix_debt_excess_lt := hdebtRank
  }

/-- Explicit cutoff form of the eventual selected self-tail passport. -/
theorem exists_cutoff_finFourSelectedSelfTailPassport
    (rows : SelectedRows reward source.point source.atom) :
    ∃ cutoff, ∀ rank, cutoff ≤ rank →
      FinFourSelectedSelfTailPassport source rows rank := by
  simpa only [eventually_atTop] using
    (rows.eventually_finFourSelectedSelfTailPassport (source := source))

end QuittingNonsingletonMinimumLawTransfer.SelectedRows

/-- One actual selected family and rank carrying the simultaneous passport.
The self-tail closure and raw low-row record are added below without placing
the repaired profile back inside `SelectedRows`. -/
structure FinFourSelectedSelfTailRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  rows : SelectedRows reward source.point source.atom
  rank : ℕ
  passport : FinFourSelectedSelfTailPassport source rows rank

namespace FinFourMinimumAtomProducer

/-- Every nonsingleton minimum-law source supplies one simultaneous selected
self-tail passport without selecting a second minimum point or chronology. -/
theorem nonempty_selectedSelfTailRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hcollision : 1 < source.atom.terminal.val.card) :
    Nonempty (FinFourSelectedSelfTailRow source) := by
  obtain ⟨rows⟩ := QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows
    reward source.point source.atom source.point_mem source.minimum
      source.minimumDebt_pos hcollision
  obtain ⟨rank, hpassport⟩ :=
    (rows.eventually_finFourSelectedSelfTailPassport (source := source)).exists
  exact ⟨{
    rows := rows
    rank := rank
    passport := hpassport
  }⟩

end FinFourMinimumAtomProducer

/-! ## Literal self-tail low rows -/

/-- One selected passport together with its literal self-tail closure.  The
dependent source index retains the original hard residual, minimum semantic
point, causal atom, selected-row family, and rank. -/
structure FinFourSelfTailLowRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  selected : FinFourSelectedSelfTailRow source

namespace FinFourSelfTailLowRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The complete selected prefixed profile before self-tail closure. -/
def selectedProfile (row : FinFourSelfTailLowRow source) :
    (quittingGame reward).BehaviorProfile :=
  prefixedProfile reward row.selected.rows.profiles row.selected.rows.roots
    row.selected.rank

/-- The marked date in the selected prefixed profile. -/
def stage (row : FinFourSelfTailLowRow source) : ℕ :=
  shiftedStage row.selected.rows.roots row.selected.rows.mark row.selected.rank

/-- The literal self-tail closure through the selected marked date. -/
def profile (row : FinFourSelfTailLowRow source) :
    (quittingGame reward).BehaviorProfile :=
  quittingSelfTailClosure reward row.selectedProfile row.stage

/-- The canonical scale `mu^2 / 8` used in both minimum-atom branches. -/
def lambda (_row : FinFourSelfTailLowRow source) : ℝ :=
  source.minimumSingletonClockResolution

/-- The original nonsingleton causal atom remains the initial coalition. -/
def coalition (row : FinFourSelfTailLowRow source) :
    QuittingNonsingletonCoalition (Fin 4) :=
  ⟨source.atom.terminal.val, row.selected.rows.collision⟩

/-- The self-tail closure preserves the selected source atom's unconditional
stage mass exactly. -/
theorem stageMass_eq_selectedStageMass (row : FinFourSelfTailLowRow source) :
    quittingStageCoalitionMass reward row.profile row.stage
        source.atom.terminal =
      selectedStageMass row.selected.rows row.selected.rank := by
  rw [profile, quittingStageCoalitionMass_selfTailClosure]
  rfl

/-- The selected atom in the self-tail closure has stage mass strictly above
the canonical scale `mu^2 / 8`. -/
theorem lambda_lt_stageMass (row : FinFourSelfTailLowRow source) :
    row.lambda < quittingStageCoalitionMass reward row.profile row.stage
      source.atom.terminal := by
  rw [row.stageMass_eq_selectedStageMass]
  exact row.selected.passport.stage_mass_floor

/-- The self-tail closure preserves the selected marked atom exactly. -/
theorem lambda_le_stageMass (row : FinFourSelfTailLowRow source) :
    row.lambda ≤ quittingStageCoalitionMass reward row.profile row.stage
      source.atom.terminal :=
  row.lambda_lt_stageMass.le

/-- The exact restarted-continuation identity turns selected total-debt
closeness into the low-tail inequality consumed by raw dispatch. -/
theorem lowTail (row : FinFourSelfTailLowRow source) :
    quittingSpineDebtExcess reward row.profile
        (quittingTerminalSemanticDebtSum source.point.1) (row.stage + 1) <
      row.lambda * quittingTerminalSemanticDebtSum source.point.1 / 2 := by
  rw [profile, quittingSpineDebtExcess_selfTailClosure]
  exact row.selected.passport.prefix_debt_excess_lt

/-- The self-tail row as the minimal actual passport consumed by raw Fin4
same-stage dispatch. -/
def actualRow (row : FinFourSelfTailLowRow source) :
    FinFourActualLowTailRow source where
  profile := row.profile
  stage := row.stage
  lambda := row.lambda
  coalition := row.coalition
  lambda_pos := source.minimumSingletonClockResolution_pos
  lambda_le_stageMass := row.lambda_le_stageMass
  lowTail := row.lowTail

/-- Full behavioral-profile provenance of the restarted continuation. -/
theorem fullSpine_eq_selectedProfile (row : FinFourSelfTailLowRow source) :
    quittingAllContinueProfileSpine reward row.profile (row.stage + 1) =
      row.selectedProfile := by
  exact quittingAllContinueProfileSpine_selfTailClosure
    reward row.selectedProfile row.stage

end FinFourSelfTailLowRow

namespace FinFourMinimumAtomProducer

/-- Every nonsingleton source supplies one actual self-tail low row without
reselecting its minimum point, causal atom, or selected family. -/
theorem nonempty_selfTailLowRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hcollision : 1 < source.atom.terminal.val.card) :
    Nonempty (FinFourSelfTailLowRow source) := by
  obtain ⟨selected⟩ := source.nonempty_selectedSelfTailRow hcollision
  exact ⟨⟨selected⟩⟩

end FinFourMinimumAtomProducer

/-! ## Singleton extraction and strong-packet consumption -/

/-- The unique surviving raw-dispatch arm, indexed by the exact self-tail low
row from which it was produced. -/
structure FinFourSelfTailSingletonEndpoint
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (row : FinFourSelfTailLowRow source) where
  endpoint : FinFourActualLowTailSingletonEndpoint row.actualRow

namespace FinFourSelfTailSingletonEndpoint

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {row : FinFourSelfTailLowRow source}

/-- The endpoint's complete post-date behavioral profile is exactly the
original selected prefixed profile.  This is stronger than live-root or
terminal-semantic equality and follows because every dispatch mutation occurs
at the one marked date. -/
theorem postDateSpine_eq_selectedProfile
    (singleton : FinFourSelfTailSingletonEndpoint row) :
    quittingAllContinueProfileSpine reward singleton.endpoint.targetProfile
        (row.stage + 1) =
      row.selectedProfile := by
  have hendpoint := singleton.endpoint.postDateSpine_eq
  have hrow := row.fullSpine_eq_selectedProfile
  simpa only [FinFourSelfTailLowRow.actualRow] using hendpoint.trans hrow

/-- Terminal-semantic projection of the exact post-date spine identity. -/
theorem postDateTail_eq_selectedProfile
    (singleton : FinFourSelfTailSingletonEndpoint row) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          singleton.endpoint.targetProfile (row.stage + 1)) =
      quittingTerminalSemanticPair reward row.selectedProfile :=
  congrArg (quittingTerminalSemanticPair reward)
    singleton.postDateSpine_eq_selectedProfile

end FinFourSelfTailSingletonEndpoint

namespace FinFourSelfTailLowRow

/-- Raw same-stage dispatch yields a singleton endpoint: the alternative
closed segment is ruled out by the source-independent Fin4 obstruction. -/
theorem nonempty_singletonEndpoint
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (row : FinFourSelfTailLowRow source) :
    Nonempty (FinFourSelfTailSingletonEndpoint row) := by
  rcases row.actualRow.nonempty_singletonEndpoint_or_closedSegment with
    endpoint | closed
  · obtain ⟨endpoint⟩ := endpoint
    exact ⟨⟨endpoint⟩⟩
  · obtain ⟨closed⟩ := closed
    exact False.elim
      (not_nonempty_finFourSameStageEndpointClosedSegment ⟨closed.trace⟩)

end FinFourSelfTailLowRow

/-- A strong concentrated packet retaining its exact self-tail row and raw
singleton endpoint. -/
structure FinFourSelfTailStrongConcentratedPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (row : FinFourSelfTailLowRow source) where
  singletonEndpoint : FinFourSelfTailSingletonEndpoint row
  strong : FinFourSingletonStageStrongConcentratedPacket reward
    singletonEndpoint.endpoint.targetProfile
    singletonEndpoint.endpoint.singleton row.stage row.lambda

/-- A produced self-tail packet together with the existing consumer's exact
strategic-versus-collision-minimum output on that same packet. -/
structure FinFourSelfTailStrongConcentratedPacketConsumption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (row : FinFourSelfTailLowRow source) where
  produced : FinFourSelfTailStrongConcentratedPacket row
  result : FinFourStrongConcentratedPacketConsumerResult source produced.strong

namespace FinFourSelfTailLowRow

/-- Construct and consume the strong concentrated packet reached from this
exact self-tail row. -/
theorem nonempty_strongConcentratedPacketConsumption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (row : FinFourSelfTailLowRow source) :
    Nonempty (FinFourSelfTailStrongConcentratedPacketConsumption row) := by
  obtain ⟨singletonEndpoint⟩ := row.nonempty_singletonEndpoint
  obtain ⟨strong⟩ :=
    FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass
      singletonEndpoint.endpoint.targetProfile
      singletonEndpoint.endpoint.singleton row.stage row.lambda
      singletonEndpoint.endpoint.singleton_card row.actualRow.lambda_pos
      singletonEndpoint.endpoint.lambda_le_stageMass
  exact ⟨{
    produced := {
      singletonEndpoint := singletonEndpoint
      strong := strong
    }
    result := strong.consumerResult
  }⟩

end FinFourSelfTailLowRow

/-- Source-level nonsingleton provenance for the self-tail consumer chain. -/
structure FinFourNonsingletonSelfTailConsumption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  terminal_card : 1 < source.atom.terminal.val.card
  row : FinFourSelfTailLowRow source
  consumption : FinFourSelfTailStrongConcentratedPacketConsumption row

namespace FinFourMinimumAtomProducer

/-- Every nonsingleton minimum atom reaches and consumes one exact strong
self-tail packet. -/
theorem nonempty_nonsingletonSelfTailConsumption
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hcollision : 1 < source.atom.terminal.val.card) :
    Nonempty (FinFourNonsingletonSelfTailConsumption source) := by
  obtain ⟨row⟩ := source.nonempty_selfTailLowRow hcollision
  obtain ⟨consumption⟩ := row.nonempty_strongConcentratedPacketConsumption
  exact ⟨{
    terminal_card := hcollision
    row := row
    consumption := consumption
  }⟩

end FinFourMinimumAtomProducer

/-! ## Common minimum-atom contraction -/

/-- The two exhaustive minimum-atom routes, each retaining its literal strong
packet and exact consumer result.  This is a contraction to an existing
strategic-versus-collision residual, not a resolution of that residual. -/
inductive FinFourMinimumAtomContractedConsumer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) : Type
  | singletonClock
      (terminal_card : source.atom.terminal.val.card = 1)
      (producer : FinFourOwnerCompressedSingletonProducer source)
      (consumption : FinFourOwnerCompressedStrongConcentratedPacketConsumption
        producer source.minimumSingletonClockResolution 0)
  | nonsingletonSelfTail
      (consumption : FinFourNonsingletonSelfTailConsumption source)

/-- A forgetful existential projection retaining the minimum source, one
strong packet, and its exact consumer result.  It does not retain which source
route produced that packet or the route's dependent origin data. -/
def FinFourMinimumAtomContractedConsumerResult
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) : Prop :=
  ∃ (sourceProfile : (quittingGame reward).BehaviorProfile)
      (sourceTerminal : {S : Finset (Fin 4) // S.Nonempty})
      (stage : ℕ) (resolution : ℝ)
      (strong : FinFourSingletonStageStrongConcentratedPacket reward
        sourceProfile sourceTerminal stage resolution),
    FinFourStrongConcentratedPacketConsumerResult source strong

namespace FinFourMinimumAtomContractedConsumer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Forget the route and its dependent origin while retaining an actual strong
packet and its exact consumer output on the same minimum source. -/
theorem consumerResult (consumer : FinFourMinimumAtomContractedConsumer source) :
    FinFourMinimumAtomContractedConsumerResult source := by
  cases consumer with
  | singletonClock _ _ consumption =>
      exact ⟨_, _, _, _, consumption.produced.strong, consumption.result⟩
  | nonsingletonSelfTail consumption =>
      exact ⟨_, _, _, _, consumption.consumption.produced.strong,
        consumption.consumption.result⟩

end FinFourMinimumAtomContractedConsumer

namespace FinFourMinimumAtomProducer

/-- Every minimum atom enters one of the two exact strong-packet consumer
routes, split only by its retained terminal's cardinality. -/
theorem nonempty_contractedConsumer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    Nonempty (FinFourMinimumAtomContractedConsumer source) := by
  by_cases hsingleton : source.atom.terminal.val.card = 1
  · obtain ⟨producer⟩ :=
      source.nonempty_ownerCompressedSingletonProducer hsingleton
    obtain ⟨consumption⟩ := producer.nonempty_strongConcentratedPacketConsumption
      source.minimumSingletonClockResolution
      source.minimumSingletonClockResolution_pos
      source.minimumSingletonClockResolution_lt_terminalMass 0
    exact ⟨.singletonClock hsingleton producer consumption⟩
  · have hcollision : 1 < source.atom.terminal.val.card := by
      have hpositive : 0 < source.atom.terminal.val.card :=
        Finset.card_pos.mpr source.atom.terminal.property
      omega
    obtain ⟨consumption⟩ :=
      source.nonempty_nonsingletonSelfTailConsumption hcollision
    exact ⟨.nonsingletonSelfTail consumption⟩

/-- Every minimum-atom source therefore supplies the consumer's exact
strategic-versus-collision-minimum output. -/
theorem contractedConsumerResult
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    FinFourMinimumAtomContractedConsumerResult source := by
  obtain ⟨consumer⟩ := source.nonempty_contractedConsumer
  exact consumer.consumerResult

end FinFourMinimumAtomProducer

/-! ## Hard-residual and bounded-data adapters -/

/-- A supplied hard residual reaches one common source-indexed contracted
consumer, with literal equality between the source's retained residual and
the supplied residual. -/
theorem exists_finFourMinimumAtomContractedConsumer_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    ∃ source : FinFourMinimumAtomProducer reward bound,
      source.residual = residual ∧
        Nonempty (FinFourMinimumAtomContractedConsumer source) := by
  obtain ⟨source, source_residual_eq⟩ :=
    FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual
      reward bound residual
  exact ⟨source, source_residual_eq, source.nonempty_contractedConsumer⟩

/-- Projection of the hard-residual adapter to an actual strong packet and
its exact consumer result. -/
theorem exists_finFourMinimumAtomContractedConsumerResult_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    ∃ source : FinFourMinimumAtomProducer reward bound,
      source.residual = residual ∧
        FinFourMinimumAtomContractedConsumerResult source := by
  obtain ⟨source, source_residual_eq, consumer⟩ :=
    exists_finFourMinimumAtomContractedConsumer_of_hardResidual
      reward bound residual
  obtain ⟨consumer⟩ := consumer
  exact ⟨source, source_residual_eq, consumer.consumerResult⟩

/-- Global bounded Fin4 data either has a uniform-equilibrium payoff or
retains an actual hard residual together with the exact source constructed
from it and that source's contracted consumer. -/
theorem
    uniformPayoff_or_exists_finFourMinimumAtomContractedConsumer_withResidualProvenance
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ residual : FinFourQuantitativeFullSupportHardResidual reward bound,
        ∃ source : FinFourMinimumAtomProducer reward bound,
          source.residual = residual ∧
            Nonempty (FinFourMinimumAtomContractedConsumer source) := by
  rcases uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual
      reward hreward with hpayoff | hresidual
  · exact Or.inl hpayoff
  · obtain ⟨residual⟩ := hresidual
    obtain ⟨source, source_residual_eq, consumer⟩ :=
      exists_finFourMinimumAtomContractedConsumer_of_hardResidual
        reward bound residual
    exact Or.inr ⟨residual, source, source_residual_eq, consumer⟩

/-- Global bounded Fin4 data either already has a uniform-equilibrium payoff
or reaches one of the two source-preserving strong-packet consumer routes.
This forgetful projection omits the hard-residual equality; the second arm
still contains an unresolved collision-minimum residual. -/
theorem uniformPayoff_or_exists_finFourMinimumAtomContractedConsumer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ source : FinFourMinimumAtomProducer reward bound,
        Nonempty (FinFourMinimumAtomContractedConsumer source) := by
  rcases
      uniformPayoff_or_exists_finFourMinimumAtomContractedConsumer_withResidualProvenance
        reward hreward with hpayoff | hresidual
  · exact Or.inl hpayoff
  · obtain ⟨_residual, source, _source_residual_eq, consumer⟩ := hresidual
    exact Or.inr ⟨source, consumer⟩

/-- Provenance-rich global projection to the exact consumer result. -/
theorem
    uniformPayoff_or_exists_finFourMinimumAtomContractedConsumerResult_withResidualProvenance
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ residual : FinFourQuantitativeFullSupportHardResidual reward bound,
        ∃ source : FinFourMinimumAtomProducer reward bound,
          source.residual = residual ∧
            FinFourMinimumAtomContractedConsumerResult source := by
  rcases
      uniformPayoff_or_exists_finFourMinimumAtomContractedConsumer_withResidualProvenance
        reward hreward with hpayoff | hconsumer
  · exact Or.inl hpayoff
  · obtain ⟨residual, source, source_residual_eq, consumer⟩ := hconsumer
    obtain ⟨consumer⟩ := consumer
    exact Or.inr
      ⟨residual, source, source_residual_eq, consumer.consumerResult⟩

/-- Forgetful global projection to the exact consumer output, with the
existing uniform-payoff arm preserved unchanged. -/
theorem uniformPayoff_or_exists_finFourMinimumAtomContractedConsumerResult
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ source : FinFourMinimumAtomProducer reward bound,
        FinFourMinimumAtomContractedConsumerResult source := by
  rcases
      uniformPayoff_or_exists_finFourMinimumAtomContractedConsumerResult_withResidualProvenance
        reward hreward with hpayoff | hconsumer
  · exact Or.inl hpayoff
  · obtain ⟨_residual, source, _source_residual_eq, result⟩ := hconsumer
    exact Or.inr ⟨source, result⟩

end GameTheory
