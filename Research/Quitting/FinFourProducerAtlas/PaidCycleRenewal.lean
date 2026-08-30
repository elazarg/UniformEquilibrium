/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.Topology.FiniteLabelSubsequence
import Research.Quitting.FinFourProducerAtlas.ExplicitResolutionForcedPair
import Research.Quitting.FinFourProducerAtlas.PaidNonsingletonCycle

/-!
# Exact-resolution renewal of a minimum paid cycle

The equality arm of a paid nonsingleton cycle regenerates a minimum source at
its actual target law.  The source-faithful causalization is eventually a
literal all-Continue word, so it retains the full incoming resolution.
Pure-nonsingleton screening returns that retained atom to a singleton without
mass loss, and the explicit-resolution compiler reconstructs a full forced
pair and paid payer endpoint at every cofinal rank.

A simultaneous finite-label extraction fixes the singleton owner, forced
owner, payer, and payer action.  Thus a minimum-cycle equality branch really
renews the complete concentrated packet geometry on the fresh minimum source,
at exactly the same positive resolution and with the same hard residual.  No
well-founded orientation or uniform-equilibrium consumer is asserted here.
-/

noncomputable section

namespace GameTheory

open Filter

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource :
  FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}
variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}
variable {cycle : FinFourForcedPairPaidNonsingletonCycle packet}
variable {endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle}

namespace FinFourForcedPairPaidNonsingletonCycle

/-- The fixed target terminal of a closed nonsingleton cycle remains
nonsingleton. -/
theorem targetTerminal_nonsingleton
    (cycle : FinFourForcedPairPaidNonsingletonCycle packet) :
    1 < cycle.targetTerminal.val.card := by
  exact cycle.targetCoalition.2

end FinFourForcedPairPaidNonsingletonCycle

/-- The equality-arm regenerated source together with a complete cofinal
forced-pair family at the unchanged resolution. -/
structure FinFourPaidCycleRenewal
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint)
    where
  singleton : FinFourSourceFaithfulRenewedSingletonPacket
    regeneration.causalization cycle.targetTerminal_nonsingleton lambda
  forced : ∀ rank,
    FinFourExplicitResolutionForcedPairPacket
      (singleton.toExplicitResolutionFrame
        (source := regeneration.next) rank)

namespace FinFourPaidCycleRenewal

variable {regeneration :
  FinFourPaidCycleMinimumRegeneration packet cycle endpoint}

/-- The finite label stabilized below. -/
abbrev Label := Fin 4 × Fin 4 × Fin 4 × Bool

/-- Singleton owner, forced owner, payer, and payer endpoint action. -/
def label (renewal : FinFourPaidCycleRenewal regeneration) (rank : ℕ) :
    Label :=
  ((renewal.forced rank).singletonOwner,
    (renewal.forced rank).forcedOwner,
    (renewal.forced rank).payer,
    (renewal.forced rank).payerAdapter.action)

/-- The renewed row viewed through the neutral singleton-frame compiler. -/
def commonForcedPair
    (renewal : FinFourPaidCycleRenewal regeneration) (rank : ℕ) :
    FinFourSingletonFrameForcedPairPacket
      (renewal.singleton.toSingletonFrame
        (source := regeneration.next) rank) :=
  (renewal.forced rank).toSingletonFrameForcedPairPacket

/-- The fresh minimum source retains the incoming hard residual. -/
theorem next_residual_eq
    (_renewal : FinFourPaidCycleRenewal regeneration) :
    regeneration.next.residual = source.residual :=
  regeneration.next_residual_eq

/-- The renewed singleton ranks remain cofinal in the fresh source-faithful
chronology. -/
theorem sourceRank_tendsto_atTop
    (renewal : FinFourPaidCycleRenewal regeneration) :
    Tendsto (FinFourSourceFaithfulRenewedSingletonPacket.sourceRank
      renewal.singleton.cutoff) atTop atTop :=
  renewal.singleton.sourceRank_tendsto_atTop

/-- Every renewed payer has the same fixed quantitative gain floor. -/
theorem payerGain_floor
    (renewal : FinFourPaidCycleRenewal regeneration) (rank : ℕ) :
    lambda * quittingTerminalSemanticDebtSum regeneration.next.point.1 / 3 ≤
      (renewal.forced rank).payerGain :=
  (renewal.commonForcedPair rank).payerGain_floor

/-- Every renewed payer loses exactly its actual gain in its own unrestricted
debt coordinate. -/
theorem payerDebt_eq_sub_gain
    (renewal : FinFourPaidCycleRenewal regeneration) (rank : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (renewal.forced rank).payerAdapter.targetProfile)
        (renewal.forced rank).payer =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (renewal.forced rank).forcedAdapter.targetProfile)
          (renewal.forced rank).payer -
        (renewal.forced rank).payerGain :=
  (renewal.commonForcedPair rank).payerTargetDebt_eq_sourceDebt_sub_gain

/-- The renewed paid target keeps the complete literal post-date source
spine. -/
theorem payerTarget_postDateSpine_eq_reference
    (renewal : FinFourPaidCycleRenewal regeneration) (rank : ℕ) :
    quittingAllContinueProfileSpine reward
        (renewal.forced rank).payerAdapter.targetProfile
        ((renewal.singleton.toExplicitResolutionFrame
          (source := regeneration.next) rank).stage + 1) =
      quittingAllContinueProfileSpine reward
        (renewal.singleton.toExplicitResolutionFrame
          (source := regeneration.next) rank).referenceProfile
        ((renewal.singleton.toExplicitResolutionFrame
          (source := regeneration.next) rank).stage + 1) :=
  (renewal.forced rank).payerTarget_postDateSpine_eq_reference

end FinFourPaidCycleRenewal

/-- One exact-resolution renewal with all four discrete forced-pair labels
fixed on a cofinal strict subsequence. -/
structure FinFourStabilizedPaidCycleRenewal
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint)
    where
  renewal : FinFourPaidCycleRenewal regeneration
  embedding : ℕ → ℕ
  embedding_strictMono : StrictMono embedding
  fixedLabel : FinFourPaidCycleRenewal.Label
  label_eq_fixed : ∀ rank,
    renewal.label (embedding rank) = fixedLabel

namespace FinFourStabilizedPaidCycleRenewal

variable {regeneration :
  FinFourPaidCycleMinimumRegeneration packet cycle endpoint}

/-- The selected explicit frame. -/
def frame (renewal : FinFourStabilizedPaidCycleRenewal regeneration)
    (rank : ℕ) : FinFourExplicitResolutionSingletonFrame regeneration.next :=
  renewal.renewal.singleton.toExplicitResolutionFrame
    (source := regeneration.next) (renewal.embedding rank)

/-- The selected full forced-pair packet. -/
def row (renewal : FinFourStabilizedPaidCycleRenewal regeneration)
    (rank : ℕ) : FinFourExplicitResolutionForcedPairPacket
      (renewal.frame rank) :=
  renewal.renewal.forced (renewal.embedding rank)

/-- Fixed singleton owner. -/
def singletonOwner
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) : Fin 4 :=
  renewal.fixedLabel.1

/-- Fixed forced owner. -/
def forcedOwner
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) : Fin 4 :=
  renewal.fixedLabel.2.1

/-- Fixed payer. -/
def payer
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) : Fin 4 :=
  renewal.fixedLabel.2.2.1

/-- Fixed payer endpoint action. -/
def payerAction
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) : Bool :=
  renewal.fixedLabel.2.2.2

theorem row_singletonOwner
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) (rank : ℕ) :
    (renewal.row rank).singletonOwner = renewal.singletonOwner :=
  congrArg Prod.fst (renewal.label_eq_fixed rank)

theorem row_forcedOwner
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) (rank : ℕ) :
    (renewal.row rank).forcedOwner = renewal.forcedOwner :=
  congrArg (fun label ↦ label.2.1) (renewal.label_eq_fixed rank)

theorem row_payer
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) (rank : ℕ) :
    (renewal.row rank).payer = renewal.payer :=
  congrArg (fun label ↦ label.2.2.1) (renewal.label_eq_fixed rank)

theorem row_payerAction
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) (rank : ℕ) :
    (renewal.row rank).payerAdapter.action = renewal.payerAction :=
  congrArg (fun label ↦ label.2.2.2) (renewal.label_eq_fixed rank)

/-- The selected fresh-source ranks remain cofinal after label
stabilization. -/
theorem sourceRank_tendsto_atTop
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) :
    Tendsto (fun rank ↦
      FinFourSourceFaithfulRenewedSingletonPacket.sourceRank
        renewal.renewal.singleton.cutoff (renewal.embedding rank))
      atTop atTop :=
  renewal.renewal.singleton.sourceRank_tendsto_atTop.comp
    renewal.embedding_strictMono.tendsto_atTop

/-- Fixed positive payer gain at every stabilized row. -/
theorem payerGain_floor
    (renewal : FinFourStabilizedPaidCycleRenewal regeneration) (rank : ℕ) :
    lambda * quittingTerminalSemanticDebtSum regeneration.next.point.1 / 3 ≤
      (renewal.row rank).payerGain :=
  renewal.renewal.payerGain_floor (renewal.embedding rank)

end FinFourStabilizedPaidCycleRenewal

namespace FinFourPaidCycleMinimumRegeneration

/-- A minimum-cycle equality branch renews the full fixed-label packet at the
same resolution on its fresh source. -/
theorem nonempty_stabilizedRenewal
    (regeneration : FinFourPaidCycleMinimumRegeneration packet cycle endpoint) :
    Nonempty (FinFourStabilizedPaidCycleRenewal regeneration) := by
  obtain ⟨singleton⟩ :=
    nonempty_finFourSourceFaithfulRenewedSingletonPacket
      regeneration.causalization cycle.targetTerminal_nonsingleton
        packet.lambda_pos le_rfl
  let forced : ∀ rank,
      FinFourExplicitResolutionForcedPairPacket
        (singleton.toExplicitResolutionFrame
          (source := regeneration.next) rank) := fun rank ↦
    Classical.choice
      (singleton.nonempty_forcedPairPacket
        (source := regeneration.next) rank)
  let renewal : FinFourPaidCycleRenewal regeneration := {
    singleton := singleton
    forced := forced
  }
  obtain ⟨fixed, embedding, hmono, hfixed⟩ :=
    Math.exists_fixed_label_on_strictMono_subsequence renewal.label
  exact ⟨{
    renewal := renewal
    embedding := embedding
    embedding_strictMono := hmono
    fixedLabel := fixed
    label_eq_fixed := hfixed
  }⟩

end FinFourPaidCycleMinimumRegeneration

/-! ## Source-facing exhaustive outcome -/

/-- The paid-cycle producer outcome with its equality arm strengthened to a
source-faithful, fixed-label renewal at the unchanged positive resolution.

The renewed rows are literal siblings in the regenerated source chronology.
This wrapper does not place the old paid edge in that chronology and supplies
no return orientation, rank descent, terminal approximation, or uniform
equilibrium. -/
inductive FinFourSourceFaithfulPaidCycleOutcome
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : Type
  | paidSingleton : FinFourForcedPairPaidSingletonEndpoint packet →
      FinFourSourceFaithfulPaidCycleOutcome packet
  | offMinimumEndpoint :
      (cycle : FinFourForcedPairPaidNonsingletonCycle packet) →
      (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle) →
      quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum endpoint.targetPoint.1 →
      FinFourSourceFaithfulPaidCycleOutcome packet
  | stabilizedMinimumRenewal :
      (cycle : FinFourForcedPairPaidNonsingletonCycle packet) →
      (endpoint : FinFourPaidNonsingletonCycleEndpointLaw packet cycle) →
      (regeneration : FinFourPaidCycleMinimumRegeneration
        packet cycle endpoint) →
      FinFourStabilizedPaidCycleRenewal regeneration →
      FinFourSourceFaithfulPaidCycleOutcome packet

/-- Source-facing exhaustive paid-cycle outcome with the equality arm carrying
the complete fixed-label renewal rather than a bare regeneration. -/
theorem nonempty_sourceFaithfulPaidCycleOutcome
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (FinFourSourceFaithfulPaidCycleOutcome packet) := by
  obtain ⟨outcome⟩ := nonempty_paidNonsingletonCycleOutcome packet
  cases outcome with
  | paidSingleton singleton =>
      exact ⟨FinFourSourceFaithfulPaidCycleOutcome.paidSingleton singleton⟩
  | offMinimumEndpoint cycle endpoint hstrict =>
      exact ⟨FinFourSourceFaithfulPaidCycleOutcome.offMinimumEndpoint
        cycle endpoint hstrict⟩
  | minimumRegeneration cycle endpoint regeneration =>
      obtain ⟨renewal⟩ := regeneration.nonempty_stabilizedRenewal
      exact ⟨FinFourSourceFaithfulPaidCycleOutcome.stabilizedMinimumRenewal
        cycle endpoint regeneration renewal⟩

end GameTheory
