/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.MinimumReturnForcedPair
import Research.Quitting.FinFourProducerAtlas.ThreeRoleRegeneration

/-!
# Normalized return from the actual Fin4 forced-pair source

One fixed minimum-return forced-pair packet supplies actual comparison and
target profiles, a fixed pair terminal, a fixed marked owner, positive mass
and payoff-gain floors, zero marked-owner defect, and literal reference tails.
This file compactifies those full decorations and derives the generic
normalized passport rather than accepting it as supplied data.

The resulting enlarged-slice minimizer either returns to the displayed
minimum and reaches an actual endpoint-law limit, or remains strictly off
minimum with only all Continue as an exact cap--Nash root.  The endpoint law
then gives strict target-debt ascent or exact same-law minimum-source
regeneration.  No canonical maximal-ray, rank decrease, chronological return,
or recursive completion claim is made here.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- The actual comparison profiles immediately before the fixed outsider's
best-endpoint update. -/
def normalizedSourceProfiles
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    ℕ → (quittingGame reward).BehaviorProfile :=
  fun index ↦ packet.base.pureSingletonProfile (packet.subsequence index)

/-- The actual forced-pair rows, with no compactness or convergence data
supplied as fields. -/
def normalizedDecoratedFamily
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    QuittingMarkedPairDecoratedFamily reward where
  sourceProfile := packet.normalizedSourceProfiles
  profile := packet.movingProfiles
  mark := packet.movingMark
  terminal := packet.movingTerminal
  markedOwner := returnSource.forcedOwner
  gainMover := returnSource.forcedOwner
  markedMass_pos := by
    intro index
    rw [show packet.movingTerminal =
        (packet.base.forcedAdapter
          (packet.subsequence index)).routedTerminal by
      exact (packet.forcedTerminal_eq_movingTerminal index).symm]
    simpa only [movingProfiles, movingMark] using
      packet.lambda_pos.trans (packet.lambda_lt_forcedPairStageMass index)
  actualGain_pos := by
    intro index
    have hfloor := packet.lambda_mul_terminalGap_le_forcedOwnerGain index
    have hpositive :
        0 < lambda * source.residual.witness.terminalGap :=
      mul_pos packet.lambda_pos source.residual.witness.terminalGap_pos
    change 0 < packet.base.forcedOwnerGain (packet.subsequence index)
    exact hpositive.trans_le hfloor
  markedOwnerDefect_eq_zero := by
    intro index
    simpa only [movingProfiles, movingMark,
      QuittingStageAtomConcentratedPacketAdapter.targetTail] using
        packet.forcedOwnerDefect_eq_zero index

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- A compactly selected subsequence of the actual full forced-pair
decorations.  The reindexed family and its `ConvergentPassport` are derived
below; neither is stored as a hypothesis. -/
structure FinFourNormalizedReturnSelection
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  limit : QuittingMarkedPairDecoration (Fin 4)
  limit_mem_ambient :
    limit ∈ packet.normalizedDecoratedFamily.prefixOrbitAmbient
  decorations_tendsto : Tendsto
    (packet.normalizedDecoratedFamily.baseDecoration ∘ subsequence)
    atTop (nhds limit)

namespace FinFourNormalizedReturnSelection

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

/-- The source family restricted to the compactly convergent subsequence. -/
def family (selection : FinFourNormalizedReturnSelection packet) :
    QuittingMarkedPairDecoratedFamily reward where
  sourceProfile :=
    packet.normalizedDecoratedFamily.sourceProfile ∘ selection.subsequence
  profile := packet.normalizedDecoratedFamily.profile ∘ selection.subsequence
  mark := packet.normalizedDecoratedFamily.mark ∘ selection.subsequence
  terminal := packet.normalizedDecoratedFamily.terminal
  markedOwner := packet.normalizedDecoratedFamily.markedOwner
  gainMover := packet.normalizedDecoratedFamily.gainMover
  markedMass_pos := fun rank ↦
    packet.normalizedDecoratedFamily.markedMass_pos
      (selection.subsequence rank)
  actualGain_pos := fun rank ↦
    packet.normalizedDecoratedFamily.actualGain_pos
      (selection.subsequence rank)
  markedOwnerDefect_eq_zero := fun rank ↦
    packet.normalizedDecoratedFamily.markedOwnerDefect_eq_zero
      (selection.subsequence rank)

/-- The actual indices in the fixed packet. -/
def packetIndex (selection : FinFourNormalizedReturnSelection packet)
    (rank : ℕ) : ℕ :=
  selection.subsequence rank

/-- The actual ranks in the one fixed owner chronology. -/
def sourceRank (selection : FinFourNormalizedReturnSelection packet)
    (rank : ℕ) : ℕ :=
  packet.selectedRank (selection.packetIndex rank)

/-- Compact selection preserves strict increase of the actual source ranks. -/
theorem sourceRank_strictMono
    (selection : FinFourNormalizedReturnSelection packet) :
    StrictMono selection.sourceRank := by
  exact packet.selectedRank_strictMono.comp selection.subsequence_strictMono

/-- Every selected comparison profile is the actual pure singleton row at
the displayed original packet index. -/
theorem sourceProfile_eq
    (selection : FinFourNormalizedReturnSelection packet) (rank : ℕ) :
    selection.family.sourceProfile rank =
      packet.base.pureSingletonProfile
        (packet.subsequence (selection.packetIndex rank)) := rfl

/-- Every selected target is the actual one-date best endpoint of that
comparison row. -/
theorem profile_eq
    (selection : FinFourNormalizedReturnSelection packet) (rank : ℕ) :
    selection.family.profile rank =
      (packet.base.forcedAdapter
        (packet.subsequence (selection.packetIndex rank))).targetProfile := rfl

/-- Every selected marked date is the actual endpoint date at the retained
source rank. -/
theorem mark_eq
    (selection : FinFourNormalizedReturnSelection packet) (rank : ℕ) :
    selection.family.mark rank =
      (packet.base.endpoint
        (packet.subsequence (selection.packetIndex rank))).stage := rfl

/-- The selected family carries the fixed literal pair. -/
theorem terminal_eq
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.family.terminal = packet.movingTerminal := rfl

/-- Literal value of the fixed pair terminal. -/
theorem terminal_val
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.family.terminal.val =
      {returnSource.producer.owner, returnSource.forcedOwner} := by
  rw [selection.terminal_eq]
  rfl

/-- The fixed terminal is genuinely a pair. -/
theorem terminal_card
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.family.terminal.val.card = 2 := by
  rw [selection.terminal_eq]
  exact packet.movingTerminal_card

/-- The marked owner is literally the fixed forced owner. -/
theorem markedOwner_eq
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.family.markedOwner = returnSource.forcedOwner := rfl

/-- The actual-gain mover is literally the same fixed forced owner. -/
theorem gainMover_eq
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.family.gainMover = returnSource.forcedOwner := rfl

/-- The selected family uses the fixed forced owner both as marked owner and
as the mover whose actual source-to-target gain is retained. -/
theorem markedOwner_eq_gainMover
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.family.markedOwner = selection.family.gainMover := rfl

/-- The original resolution is strictly below every selected marked mass. -/
theorem lambda_lt_markedMass
    (selection : FinFourNormalizedReturnSelection packet) (rank : ℕ) :
    lambda < quittingStageCoalitionMass reward
      (selection.family.profile rank) (selection.family.mark rank)
        selection.family.terminal := by
  rw [selection.profile_eq rank, selection.mark_eq rank,
    selection.terminal_eq]
  rw [show packet.movingTerminal =
      (packet.base.forcedAdapter
        (packet.subsequence (selection.packetIndex rank))).routedTerminal by
    exact (packet.forcedTerminal_eq_movingTerminal
      (selection.packetIndex rank)).symm]
  exact packet.lambda_lt_forcedPairStageMass (selection.packetIndex rank)

/-- Every selected actual payoff gain retains the fixed table-gap floor. -/
theorem lambda_mul_terminalGap_le_actualGain
    (selection : FinFourNormalizedReturnSelection packet) (rank : ℕ) :
    lambda * source.residual.witness.terminalGap ≤
      quittingTerminalPayoff reward (selection.family.profile rank)
          selection.family.gainMover -
        quittingTerminalPayoff reward (selection.family.sourceProfile rank)
          selection.family.gainMover := by
  change lambda * source.residual.witness.terminalGap ≤
    packet.base.forcedOwnerGain
      (packet.subsequence (selection.packetIndex rank))
  exact packet.lambda_mul_terminalGap_le_forcedOwnerGain
    (selection.packetIndex rank)

/-- The displayed gain floor is itself positive and is attained as a lower
bound by the same actual source/target pair. -/
theorem terminalGapGain_pos_and_le_actualGain
    (selection : FinFourNormalizedReturnSelection packet) (rank : ℕ) :
    0 < lambda * source.residual.witness.terminalGap ∧
      lambda * source.residual.witness.terminalGap ≤
        quittingTerminalPayoff reward (selection.family.profile rank)
            selection.family.gainMover -
          quittingTerminalPayoff reward (selection.family.sourceProfile rank)
            selection.family.gainMover :=
  ⟨mul_pos packet.lambda_pos source.residual.witness.terminalGap_pos,
    selection.lambda_mul_terminalGap_le_actualGain rank⟩

/-- The selected marked owner has exactly zero local defect at every actual
source row. -/
theorem markedOwnerDefect_eq_zero
    (selection : FinFourNormalizedReturnSelection packet) (rank : ℕ) :
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (selection.family.profile rank) (selection.family.mark rank + 1))).1
      (quittingProfileLiveRoot reward (selection.family.profile rank)
        (selection.family.mark rank)) selection.family.markedOwner = 0 :=
  selection.family.markedOwnerDefect_eq_zero rank

/-- The complete post-date behavioral spine is the actual selected
near-minimum reference profile. -/
theorem postDateSpine_eq_reference
    (selection : FinFourNormalizedReturnSelection packet) (rank : ℕ) :
    quittingAllContinueProfileSpine reward
        (selection.family.profile rank) (selection.family.mark rank + 1) =
      packet.base.referenceProfile
        (packet.subsequence (selection.packetIndex rank)) := by
  simpa only [selection.profile_eq rank, selection.mark_eq rank] using
    packet.forcedPair_postDateSpine_eq_reference (selection.packetIndex rank)

/-- The reindexed family has the compactly selected full decoration limit. -/
theorem family_baseDecoration_tendsto
    (selection : FinFourNormalizedReturnSelection packet) :
    Tendsto selection.family.baseDecoration atTop (nhds selection.limit) := by
  change Tendsto
    (packet.normalizedDecoratedFamily.baseDecoration ∘ selection.subsequence)
      atTop (nhds selection.limit)
  exact selection.decorations_tendsto

/-- The selected limit has positive whole debt by global minimality. -/
theorem limit_wholeDebt_pos
    (selection : FinFourNormalizedReturnSelection packet) :
    0 < selection.limit.wholeDebt := by
  have hcarrier :=
    QuittingMarkedPairDecoratedFamily.semantic_mem_carrier_of_law_mem_carrier
      selection.limit.whole selection.limit_mem_ambient.1.1
  exact source.minimumDebt_pos.trans_le
    (source.minimum selection.limit.whole.1 hcarrier)

/-- The fixed positive mass floor survives compactification. -/
theorem limit_markedMass_pos
    (selection : FinFourNormalizedReturnSelection packet) :
    0 < selection.limit.markedMass := by
  have hlimit : Tendsto (fun rank ↦
      (selection.family.baseDecoration rank).markedMass) atTop
      (nhds selection.limit.markedMass) :=
    ((continuous_fst.comp continuous_snd).tendsto selection.limit).comp
      selection.family_baseDecoration_tendsto
  have hlower : lambda ≤ selection.limit.markedMass :=
    ge_of_tendsto' hlimit fun rank ↦
      (selection.lambda_lt_markedMass rank).le
  exact packet.lambda_pos.trans_le hlower

/-- The fixed positive actual-gain floor survives compactification. -/
theorem limit_actualGain_pos
    (selection : FinFourNormalizedReturnSelection packet) :
    0 < selection.limit.actualGain := by
  have hlimit : Tendsto (fun rank ↦
      (selection.family.baseDecoration rank).actualGain) atTop
      (nhds selection.limit.actualGain) :=
    ((continuous_snd.comp continuous_snd).tendsto selection.limit).comp
      selection.family_baseDecoration_tendsto
  have hlower : lambda * source.residual.witness.terminalGap ≤
      selection.limit.actualGain :=
    ge_of_tendsto' hlimit fun rank ↦
      selection.lambda_mul_terminalGap_le_actualGain rank
  exact (mul_pos packet.lambda_pos
    source.residual.witness.terminalGap_pos).trans_le hlower

/-- The selected limit's tail lies on the original minimum-debt fibre. -/
theorem limit_tailDebt_eq_minimum
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.limit.tailDebt =
      quittingTerminalSemanticDebtSum source.point.1 := by
  have hlimit : Tendsto (fun rank ↦
      (selection.family.baseDecoration rank).tailDebt) atTop
      (nhds selection.limit.tailDebt) :=
    (QuittingMarkedPairDecoration.continuous_tailDebt.tendsto
      selection.limit).comp selection.family_baseDecoration_tendsto
  have hminimum := packet.movingTailDebt_tendsto_minimum.comp
    selection.subsequence_strictMono.tendsto_atTop
  have hminimum' : Tendsto (fun rank ↦
      (selection.family.baseDecoration rank).tailDebt) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
    change Tendsto ((fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (packet.movingProfiles rank) (packet.movingMark rank + 1)))) ∘
            selection.subsequence) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1))
    simpa only [
      FinFourOwnerCompressedMinimumReturnForcedPairPacket.movingPacket,
      id_eq] using hminimum
  exact tendsto_nhds_unique hlimit hminimum'

/-- The generic convergent passport is derived from the actual compact
selection and its forced-pair quantitative facts. -/
def passport (selection : FinFourNormalizedReturnSelection packet) :
    QuittingMarkedPairDecoratedFamily.ConvergentPassport
      selection.family source.point.1 where
  limit := selection.limit
  tendsto_base := selection.family_baseDecoration_tendsto
  tailDebt_eq := selection.limit_tailDebt_eq_minimum
  wholeDebt_pos := selection.limit_wholeDebt_pos
  markedMass_pos := selection.limit_markedMass_pos
  actualGain_pos := selection.limit_actualGain_pos

/-- Canonical positive marked-mass density at the selected full limit. -/
def massDensity (selection : FinFourNormalizedReturnSelection packet) : ℝ :=
  selection.limit.markedMass / (2 * selection.limit.wholeDebt)

/-- Canonical positive actual-gain density at the selected full limit. -/
def gainDensity (selection : FinFourNormalizedReturnSelection packet) : ℝ :=
  selection.limit.actualGain / (2 * selection.limit.wholeDebt)

theorem massDensity_pos
    (selection : FinFourNormalizedReturnSelection packet) :
    0 < selection.massDensity :=
  div_pos selection.limit_markedMass_pos
    (mul_pos (by norm_num) selection.limit_wholeDebt_pos)

theorem gainDensity_pos
    (selection : FinFourNormalizedReturnSelection packet) :
    0 < selection.gainDensity :=
  div_pos selection.limit_actualGain_pos
    (mul_pos (by norm_num) selection.limit_wholeDebt_pos)

theorem massDensity_mul_wholeDebt_lt
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.massDensity * selection.limit.wholeDebt <
      selection.limit.markedMass := by
  rw [massDensity]
  calc
    selection.limit.markedMass / (2 * selection.limit.wholeDebt) *
          selection.limit.wholeDebt = selection.limit.markedMass / 2 := by
      field_simp [ne_of_gt selection.limit_wholeDebt_pos]
    _ < selection.limit.markedMass := by
      linarith [selection.limit_markedMass_pos]

theorem gainDensity_mul_wholeDebt_lt
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.gainDensity * selection.limit.wholeDebt <
      selection.limit.actualGain := by
  rw [gainDensity]
  calc
    selection.limit.actualGain / (2 * selection.limit.wholeDebt) *
          selection.limit.wholeDebt = selection.limit.actualGain / 2 := by
      field_simp [ne_of_gt selection.limit_wholeDebt_pos]
    _ < selection.limit.actualGain := by
      linarith [selection.limit_actualGain_pos]

end FinFourNormalizedReturnSelection

namespace QuittingMarkedPairMinimumReturnActualizer

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {selection : FinFourNormalizedReturnSelection packet}
  {point : QuittingMarkedPairDecoration (Fin 4)}

/-- The original fixed-packet index behind one actualized raw-prefix row. -/
def finFourOriginPacketIndex
    (actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
      source.point.1 selection.massDensity selection.gainDensity point)
    (rank : ℕ) : ℕ :=
  selection.packetIndex (actualizer.originRank rank)

/-- The original source-chronology rank behind one actualized raw-prefix
row. -/
def finFourOriginSourceRank
    (actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
      source.point.1 selection.massDensity selection.gainDensity point)
    (rank : ℕ) : ℕ :=
  selection.sourceRank (actualizer.originRank rank)

/-- The literal finite product-root word used by one actualized row. -/
def finFourOriginRoots
    (actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
      source.point.1 selection.massDensity selection.gainDensity point)
    (rank : ℕ) : List (Fin 4 → PMF Bool) :=
  actualizer.originRoots rank

/-- The actualized target is exactly the displayed root word prefixed to the
selected forced-pair target. -/
theorem finFour_profile_eq_literalRootStack
    (actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
      source.point.1 selection.massDensity selection.gainDensity point)
    (rank : ℕ) :
    actualizer.profiles rank =
      quittingLiteralRootStackProfile reward
        (actualizer.finFourOriginRoots rank)
        (packet.base.forcedAdapter
          (packet.subsequence
            (actualizer.finFourOriginPacketIndex rank))).targetProfile := by
  rfl

/-- The comparison profile uses the same literal root word on the selected
pure singleton source. -/
theorem finFour_sourceProfile_eq_literalRootStack
    (actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
      source.point.1 selection.massDensity selection.gainDensity point)
    (rank : ℕ) :
    actualizer.sourceProfiles rank =
      quittingLiteralRootStackProfile reward
        (actualizer.finFourOriginRoots rank)
        (packet.base.pureSingletonProfile
          (packet.subsequence
            (actualizer.finFourOriginPacketIndex rank))) := by
  rfl

/-- Arbitrary-prefix actualization preserves the complete behavioral tail of
the exact selected near-minimum reference profile.  The finite prefix word is
literally `actualizer.originRoots rank`. -/
theorem finFour_postDateSpine_eq_reference
    (actualizer : QuittingMarkedPairMinimumReturnActualizer selection.family
      source.point.1 selection.massDensity selection.gainDensity point)
    (rank : ℕ) :
    quittingAllContinueProfileSpine reward (actualizer.profiles rank)
        (actualizer.mark rank + 1) =
      packet.base.referenceProfile
        (packet.subsequence (actualizer.finFourOriginPacketIndex rank)) := by
  calc
    quittingAllContinueProfileSpine reward (actualizer.profiles rank)
          (actualizer.mark rank + 1) =
        quittingAllContinueProfileSpine reward
          (selection.family.profile (actualizer.originRank rank))
          (selection.family.mark (actualizer.originRank rank) + 1) := by
      exact selection.family.descendant_postMarkSpine_eq
        (actualizer.originRank rank) (actualizer.originRoots rank)
    _ = packet.base.referenceProfile
          (packet.subsequence (actualizer.finFourOriginPacketIndex rank)) := by
      exact selection.postDateSpine_eq_reference (actualizer.originRank rank)

end QuittingMarkedPairMinimumReturnActualizer

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- Compactness produces the full decorated subsequence used by the source
adapter; it is not supplied by the caller. -/
theorem nonempty_normalizedReturnSelection
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (FinFourNormalizedReturnSelection packet) := by
  let family := packet.normalizedDecoratedFamily
  have hmem : ∀ rank, family.baseDecoration rank ∈
      family.prefixOrbitAmbient := by
    intro rank
    simpa only [QuittingMarkedPairDecoratedFamily.rawDecoration_nil] using
      family.rawDecoration_mem_ambient rank []
  obtain ⟨limit, hlimit, subsequence, hsubsequence, htendsto⟩ :=
    family.prefixOrbitAmbient_isCompact.tendsto_subseq hmem
  exact ⟨{
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    limit := limit
    limit_mem_ambient := hlimit
    decorations_tendsto := htendsto
  }⟩

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- The actual normalized-return result attached to one fixed source packet.
The equality arm contains an actual raw-prefix actualizer and the checked
endpoint-law regeneration-or-ascent result.  The strict arm contains only the
enlarged-slice inert point and its exact cap--Nash correspondence. -/
structure FinFourNormalizedReturnThreeRoleOrStrictInert
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  selection : FinFourNormalizedReturnSelection packet
  point : QuittingMarkedPairDecoration (Fin 4)
  point_mem : point ∈ selection.family.normalizedPassportSlice source.point.1
    selection.massDensity selection.gainDensity
  point_minimal : ∀ candidate ∈
      selection.family.normalizedPassportSlice source.point.1
        selection.massDensity selection.gainDensity,
    point.wholeDebt ≤ candidate.wholeDebt
  minimum_le_point :
    quittingTerminalSemanticDebtSum source.point.1 ≤ point.wholeDebt
  outcome :
    (∃ actualizer : QuittingMarkedPairMinimumReturnActualizer
        selection.family source.point.1 selection.massDensity
          selection.gainDensity point,
      point.wholeDebt = quittingTerminalSemanticDebtSum source.point.1 ∧
        Nonempty (FinFourThreeRoleRegenerationOrAscent source
          actualizer.packet)) ∨
    (quittingTerminalSemanticDebtSum source.point.1 < point.wholeDebt ∧
      ∀ root : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward point.whole.1.2 0 root ↔
          root = (quittingAllContinueRoot : Fin 4 → PMF Bool))

namespace FinFourNormalizedReturnThreeRoleOrStrictInert

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

/-- The terminal-gap witness retained from the same hard residual. -/
def witness
    (_capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    QuittingTerminalExploitabilityWitness reward :=
  source.residual.witness

@[simp] theorem witness_eq_source
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    capstone.witness = source.residual.witness := rfl

/-- The original singleton owner is the fixed other member of the pair. -/
def other
    (_capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    Fin 4 :=
  returnSource.producer.owner

@[simp] theorem other_eq_owner
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    capstone.other = returnSource.producer.owner := rfl

/-- The retained other player differs from the marked gain mover. -/
theorem other_ne_gainMover
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    capstone.other ≠ capstone.selection.family.gainMover := by
  exact returnSource.forcedOwner_ne_owner.symm

/-- The retained other player belongs to the fixed pair terminal. -/
theorem other_mem_terminal
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    capstone.other ∈ capstone.selection.family.terminal.val := by
  simp [other, FinFourNormalizedReturnSelection.family,
    FinFourOwnerCompressedMinimumReturnForcedPairPacket.normalizedDecoratedFamily,
    FinFourOwnerCompressedMinimumReturnForcedPairPacket.movingTerminal]

/-- Forgetting the endpoint law and regenerated source recovers the previous
public equality-arm chord versus strict-inert surface. -/
theorem threeRole_or_strictInert
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    (∃ actualizer : QuittingMarkedPairMinimumReturnActualizer
        capstone.selection.family source.point.1
          capstone.selection.massDensity capstone.selection.gainDensity
            capstone.point,
      ∃ mover recipient,
        capstone.point.wholeDebt =
            quittingTerminalSemanticDebtSum source.point.1 ∧
          Nonempty (ConcentratedCollisionFourRole.ThreeRoleLimitChord reward
            source.point.1 capstone.selection.family.markedOwner mover
              recipient actualizer.resolution)) ∨
    (quittingTerminalSemanticDebtSum source.point.1 <
        capstone.point.wholeDebt ∧
      ∀ root : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward capstone.point.whole.1.2 0 root ↔
          root = (quittingAllContinueRoot : Fin 4 → PMF Bool)) := by
  rcases capstone.outcome with hequality | hinert
  · left
    obtain ⟨actualizer, hreturn, ⟨result⟩⟩ := hequality
    exact ⟨actualizer, result.mover, result.recipient, hreturn,
      ⟨result.toThreeRoleLimitChord⟩⟩
  · exact Or.inr hinert

end FinFourNormalizedReturnThreeRoleOrStrictInert

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- Actual Fin4 source adapter and consumer.  It derives a full convergent
passport from one fixed forced-pair packet and returns either endpoint-law
regeneration/ascent or the strict enlarged-slice inert point. -/
theorem nonempty_normalizedReturnThreeRole_or_strictInert
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (FinFourNormalizedReturnThreeRoleOrStrictInert packet) := by
  obtain ⟨selection⟩ := packet.nonempty_normalizedReturnSelection
  obtain ⟨point, hpoint, hminimal, hlower, hbranch⟩ :=
    selection.family.exists_minimum_normalizedPassportSlice_eq_or_strict_inert
      source.point.1 source.minimum source.minimumDebt_pos selection.passport
        selection.massDensity selection.gainDensity
          selection.massDensity_mul_wholeDebt_lt
          selection.gainDensity_mul_wholeDebt_lt
  refine ⟨{
    selection := selection
    point := point
    point_mem := hpoint
    point_minimal := hminimal
    minimum_le_point := hlower
    outcome := ?_
  }⟩
  rcases hbranch with hreturn | hinert
  · left
    obtain ⟨actualizer⟩ := nonempty_quittingMarkedPairMinimumReturnActualizer
      selection.family source.point.1 selection.massDensity
        selection.gainDensity point selection.massDensity_pos
          selection.gainDensity_pos source.minimumDebt_pos hpoint hreturn
    obtain ⟨mover, recipient, ⟨endpoint⟩⟩ :=
      actualizer.nonempty_threeRoleEndpointLaw_of_minimumReturn
        source.semantic_mem source.minimum source.minimumDebt_pos (by
          rw [show selection.family.terminal = packet.movingTerminal from rfl,
            packet.movingTerminal_card]
          norm_num) hreturn hpoint.2.1
    exact ⟨actualizer, hreturn,
      endpoint.nonempty_finFourRegenerationOrAscent⟩
  · exact Or.inr hinert

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- Source-level capstone retaining the actual packet selected at the fixed
resolution before normalized compactification. -/
structure FinFourNormalizedReturnSourceCapstone
    (returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source)
    (lambda : ℝ) where
  packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda
  normalized : FinFourNormalizedReturnThreeRoleOrStrictInert packet

namespace FinFourOwnerCompressedMinimumReturnForcedPairSource

/-- Construct the normalized return/inert capstone from one fixed source and
one admissible resolution.  The packet, compact subsequence, passport, and
minimizer are all selected internally. -/
theorem nonempty_normalizedReturnThreeRole_or_strictInert
    (returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda < source.point.2 (some source.atom.terminal)) :
    Nonempty (FinFourNormalizedReturnSourceCapstone returnSource lambda) := by
  obtain ⟨packet⟩ :=
    returnSource.nonempty_packet lambda hlambda_pos hlambda_lt
  obtain ⟨normalized⟩ :=
    packet.nonempty_normalizedReturnThreeRole_or_strictInert
  exact ⟨{ packet := packet, normalized := normalized }⟩

end FinFourOwnerCompressedMinimumReturnForcedPairSource

namespace FinFourNormalizedReturnSourceCapstone

/-- Source-level strongest outcome.  The equality arm stores an actual
endpoint law and its strict-ascent-or-same-law-regeneration result; the other
arm is the unconsumed strict normalized inert point. -/
theorem regenerationOrAscent_or_strictInert
    (capstone : FinFourNormalizedReturnSourceCapstone returnSource lambda) :
    (∃ actualizer : QuittingMarkedPairMinimumReturnActualizer
        capstone.normalized.selection.family source.point.1
          capstone.normalized.selection.massDensity
            capstone.normalized.selection.gainDensity
              capstone.normalized.point,
      capstone.normalized.point.wholeDebt =
          quittingTerminalSemanticDebtSum source.point.1 ∧
        Nonempty (FinFourThreeRoleRegenerationOrAscent source
          actualizer.packet)) ∨
    (quittingTerminalSemanticDebtSum source.point.1 <
        capstone.normalized.point.wholeDebt ∧
      ∀ root : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward capstone.normalized.point.whole.1.2 0 root ↔
          root = (quittingAllContinueRoot : Fin 4 → PMF Bool)) :=
  capstone.normalized.outcome

end FinFourNormalizedReturnSourceCapstone

namespace FinFourMinimumAtomProducer

/-- A singleton minimum atom fixes one chronology and outsider before every
later admissible resolution; each resolution then produces its own actual
normalized return/inert capstone. -/
theorem exists_normalizedReturnSource_for_all_resolutions
    (source : FinFourMinimumAtomProducer reward bound)
    (terminal_card : source.atom.terminal.val.card = 1) :
    ∃ returnSource :
        FinFourOwnerCompressedMinimumReturnForcedPairSource source,
      ∀ lambda, 0 < lambda →
        lambda < source.point.2 (some source.atom.terminal) →
          Nonempty
            (FinFourNormalizedReturnSourceCapstone returnSource lambda) := by
  obtain ⟨returnSource⟩ :=
    source.nonempty_minimumReturnForcedPairSource terminal_card
  exact ⟨returnSource, fun lambda hlambda_pos hlambda_lt ↦
    returnSource.nonempty_normalizedReturnThreeRole_or_strictInert
      lambda hlambda_pos hlambda_lt⟩

end FinFourMinimumAtomProducer

end GameTheory
