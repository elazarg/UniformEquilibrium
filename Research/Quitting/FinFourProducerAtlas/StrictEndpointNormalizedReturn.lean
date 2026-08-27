/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.CanonicalPairMinimumEndpointSupportRankHandoff
import Research.Quitting.FinFourProducerAtlas.NormalizedReturn

/-!
# Normalizing the strict paid endpoint of the canonical Fin4 pair ray

The canonical maximal-prefix ray and the earlier normalized forced-pair
family have different endpoint origins.  This module keeps that distinction
literal.  It freezes the paid endpoint action on a strict subsequence of the
canonical ray, compactifies those exact source/target pairs, and applies the
generic normalized-passport minimizer to that family.

The minimum-return normalized arm exposes the existing strategic-singleton or
same-packet collision-minimum consumer before invoking any stronger endpoint-
law result.  The strict normalized arm retains only the unique-all-Continue
inert point.  No exactness is transported across the horizontal paid update.
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

variable
  (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda)

/-- The canonical paid endpoint retains the original near-minimum behavioral
tail after its copied maximal-prefix word and its one horizontal update. -/
theorem rayPaidTarget_postMarkSpine_eq_tail (index : ℕ) :
    quittingAllContinueProfileSpine reward (packet.rayPaidTargetProfile index)
        (index + 1) =
      packet.rayTail index := by
  unfold rayPaidTargetProfile
  rw [quittingAllContinueProfileSpine_add]
  rw [quittingAllContinueProfileSpine_maximalCapSemanticPrefixProfile]
  calc
    quittingAllContinueProfileSpine reward
          (packet.rayPaidAdapter index).targetProfile 1 =
        quittingAllContinueProfileSpine reward
          (packet.rayBaseProfile index) 1 := by
      apply quittingAllContinueProfileSpine_eq_of_eq_from
      intro who time history htime
      have hne : time ≠ 0 := by omega
      exact congrFun
        ((packet.rayPaidAdapter index).targetProfile_at_of_ne time hne who)
        history
    _ = packet.rayTail index :=
      packet.rayBaseProfile_postMarkSpine_eq_tail index

/-- At the shifted marked date, the paid target sees exactly the date-zero
best-endpoint root from which it was constructed. -/
theorem rayPaidTarget_markedRoot_eq (index : ℕ) :
    quittingProfileLiveRoot reward (packet.rayPaidTargetProfile index) index =
      quittingProfileLiveRoot reward
        (packet.rayPaidAdapter index).targetProfile 0 := by
  rw [← congrFun (quittingProfileSpineRoot_eq_profileLiveRoot reward
    (packet.rayPaidTargetProfile index)) index]
  rw [← congrFun (quittingProfileSpineRoot_eq_profileLiveRoot reward
    (packet.rayPaidAdapter index).targetProfile) 0]
  unfold quittingProfileSpineRoot
  unfold rayPaidTargetProfile
  rw [quittingAllContinueProfileSpine_maximalCapSemanticPrefixProfile]
  rfl

/-- The horizontal best-endpoint update kills the canonical payer's marked
root defect exactly, after the unchanged outer word. -/
theorem rayPaidTarget_markedDefect_eq_zero (index : ℕ) :
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (packet.rayPaidTargetProfile index) (index + 1))).1
      (quittingProfileLiveRoot reward (packet.rayPaidTargetProfile index)
        index) packet.payer = 0 := by
  rw [packet.rayPaidTarget_postMarkSpine_eq_tail index,
    packet.rayPaidTarget_markedRoot_eq index]
  rw [← packet.rayPaidAdapter_sourceTail_eq_reference index]
  rw [(packet.rayPaidAdapter index).target_markedRoot_eq]
  exact quittingRootCoordinateNashDefect_update_bestEndpoint_eq_zero
    reward (packet.rayPaidAdapter index).sourceTail.1
      (packet.rayPaidAdapter index).sourceRoot packet.payer

/-- The canonical source and target at one depth differ by the retained
positive copied-prefix payer gain. -/
theorem rayPaidGain_pos (index : ℕ) : 0 < packet.rayPaidGain index := by
  have hfloor := packet.rayResolution_mul_minimumDebt_div_three_le_rayPaidGain
    index
  exact (div_pos (mul_pos packet.rayResolution_pos source.minimumDebt_pos)
    (by norm_num)).trans_le hfloor

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

private theorem exists_fixed_bool_strictMono_subsequence (label : ℕ → Bool) :
    ∃ fixed : Bool, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧ ∀ index, label (subsequence index) = fixed := by
  have hfrequent : ∃ fixed : Bool, ∃ᶠ index in atTop,
      label index = fixed := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ᶠ index in atTop, ∀ fixed : Bool,
        label index ≠ fixed := by
      rw [eventually_all]
      exact hnot
    obtain ⟨index, hindex⟩ := hall.exists
    exact hindex (label index) rfl
  obtain ⟨fixed, hfixed⟩ := hfrequent
  obtain ⟨subsequence, hsubsequence, hlabel⟩ :=
    extraction_of_frequently_atTop hfixed
  exact ⟨fixed, subsequence, hsubsequence, hlabel⟩

/-- Fixed-action canonical paid-endpoint rows.  The depth map is cofinal and
the target at every depth is the literal paid endpoint of that same canonical
ray source. -/
structure FinFourCanonicalPaidEndpointRows
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  action : Bool
  depth : ℕ → ℕ
  depth_strictMono : StrictMono depth
  action_eq : ∀ rank, (packet.rayPaidAdapter (depth rank)).action = action
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  routedTerminal_eq : ∀ rank,
    (packet.rayPaidAdapter (depth rank)).routedTerminal = terminal

namespace FinFourCanonicalPaidEndpointRows

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

/-- The forced owner is a fixed routed member distinct from the paid owner in
both endpoint modes. -/
theorem other_mem_terminal
    (rows : FinFourCanonicalPaidEndpointRows packet) :
    returnSource.forcedOwner ∈ rows.terminal.val := by
  rw [← rows.routedTerminal_eq 0]
  change returnSource.forcedOwner ∈
    quittingPureEndpointRoutedCoalition packet.rayTerminal.val packet.payer
      (packet.rayPaidAdapter (rows.depth 0)).action
  rw [rows.action_eq 0]
  cases rows.action
  · simp [quittingPureEndpointRoutedCoalition,
      FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayTerminal,
      FinFourOwnerCompressedMinimumReturnForcedPairPacket.movingTerminal,
      packet.payer_ne_forcedOwner.symm]
  · simp [quittingPureEndpointRoutedCoalition,
      FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayTerminal,
      FinFourOwnerCompressedMinimumReturnForcedPairPacket.movingTerminal]

/-- The exact canonical paid source/target pairs as a generic decorated
family. -/
def family (rows : FinFourCanonicalPaidEndpointRows packet) :
    QuittingMarkedPairDecoratedFamily reward where
  sourceProfile := fun rank ↦ packet.rayFamily.rayProfiles (rows.depth rank)
  profile := fun rank ↦ packet.rayPaidTargetProfile (rows.depth rank)
  mark := rows.depth
  terminal := rows.terminal
  markedOwner := packet.payer
  gainMover := packet.payer
  markedMass_pos := by
    intro rank
    rw [show rows.terminal =
        (packet.rayPaidAdapter (rows.depth rank)).routedTerminal by
      exact (rows.routedTerminal_eq rank).symm]
    change 0 < quittingStageCoalitionMass reward
      (quittingMaximalCapSemanticPrefixProfile reward packet.raySource
        (packet.rayPaidAdapter (rows.depth rank)).targetProfile
        (rows.depth rank))
      (rows.depth rank + 0)
      (packet.rayPaidAdapter (rows.depth rank)).routedTerminal
    rw [quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add]
    have hsurvival :=
      quittingMaximalCapSemanticPrefixSurvival_pos_of_positiveMinimum reward
        source.point.1 packet.raySource source.minimum source.minimumDebt_pos
          packet.raySource_mem (rows.depth rank)
    exact mul_pos hsurvival
      (packet.rayPaidAdapter (rows.depth rank)).targetStageMass_pos
  actualGain_pos := fun rank ↦ packet.rayPaidGain_pos (rows.depth rank)
  markedOwnerDefect_eq_zero := fun rank ↦
    packet.rayPaidTarget_markedDefect_eq_zero (rows.depth rank)

@[simp] theorem family_sourceProfile
    (rows : FinFourCanonicalPaidEndpointRows packet) (rank : ℕ) :
    rows.family.sourceProfile rank =
      packet.rayFamily.rayProfiles (rows.depth rank) := rfl

@[simp] theorem family_profile
    (rows : FinFourCanonicalPaidEndpointRows packet) (rank : ℕ) :
    rows.family.profile rank = packet.rayPaidTargetProfile (rows.depth rank) :=
  rfl

@[simp] theorem family_mark
    (rows : FinFourCanonicalPaidEndpointRows packet) (rank : ℕ) :
    rows.family.mark rank = rows.depth rank := rfl

@[simp] theorem family_terminal
    (rows : FinFourCanonicalPaidEndpointRows packet) :
    rows.family.terminal = rows.terminal := rfl

@[simp] theorem family_markedOwner
    (rows : FinFourCanonicalPaidEndpointRows packet) :
    rows.family.markedOwner = packet.payer := rfl

@[simp] theorem family_gainMover
    (rows : FinFourCanonicalPaidEndpointRows packet) :
    rows.family.gainMover = packet.payer := rfl

theorem sourceDebt_tendsto_minimum
    (rows : FinFourCanonicalPaidEndpointRows packet)
    (rayReturn :
      FinFourOwnerCompressedMinimumReturnForcedPairPacket.MaximalPrefixRayMinimumReturn
        packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (rows.family.sourceProfile rank)))
      atTop (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
  have h := packet.rayProfiles_wholeDebt_tendsto.comp
    rows.depth_strictMono.tendsto_atTop
  change Tendsto
    ((fun index ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (packet.rayFamily.rayProfiles index))) ∘
        rows.depth) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1))
  simpa only [rayReturn.limit_eq] using h

theorem postMarkSpine_eq_tail
    (rows : FinFourCanonicalPaidEndpointRows packet) (rank : ℕ) :
    quittingAllContinueProfileSpine reward (rows.family.profile rank)
        (rows.family.mark rank + 1) =
      packet.rayTail (rows.depth rank) :=
  packet.rayPaidTarget_postMarkSpine_eq_tail (rows.depth rank)

theorem tailDebt_tendsto_minimum
    (rows : FinFourCanonicalPaidEndpointRows packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (rows.family.profile rank)
          (rows.family.mark rank + 1)))) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
  have h := packet.referenceDebt_tendsto.comp
    rows.depth_strictMono.tendsto_atTop
  convert h using 1
  funext rank
  rw [rows.postMarkSpine_eq_tail rank]
  rfl

end FinFourCanonicalPaidEndpointRows

namespace FinFourCanonicalPaidEndpointRows

/-- Reindex fixed-action paid rows by a further cofinal subsequence. -/
def reindex
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (rows : FinFourCanonicalPaidEndpointRows packet)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence) :
    FinFourCanonicalPaidEndpointRows packet where
  action := rows.action
  depth := rows.depth ∘ subsequence
  depth_strictMono := rows.depth_strictMono.comp hsubsequence
  action_eq := fun rank ↦ rows.action_eq (subsequence rank)
  terminal := rows.terminal
  routedTerminal_eq := fun rank ↦ rows.routedTerminal_eq (subsequence rank)

@[simp] theorem reindex_family_baseDecoration
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (rows : FinFourCanonicalPaidEndpointRows packet)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (rank : ℕ) :
    (rows.reindex subsequence hsubsequence).family.baseDecoration rank =
      rows.family.baseDecoration (subsequence rank) := by
  apply Prod.ext
  · apply Prod.ext <;> rfl
  · apply Prod.ext <;> rfl

end FinFourCanonicalPaidEndpointRows

/-- One compact joint-law origin for the literal paid endpoints of the
minimum-return canonical ray. -/
structure FinFourCanonicalPaidEndpointOrigin
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  rayReturn :
    FinFourOwnerCompressedMinimumReturnForcedPairPacket.MaximalPrefixRayMinimumReturn
      packet
  rows : FinFourCanonicalPaidEndpointRows packet
  limit : QuittingMarkedPairDecoration (Fin 4)
  limit_mem_ambient : limit ∈ rows.family.prefixOrbitAmbient
  decorations_tendsto : Tendsto rows.family.baseDecoration atTop (nhds limit)

namespace FinFourCanonicalPaidEndpointRows

/-- Compactify any supplied fixed-action endpoint rows on a further strict
subsequence, retaining the exact refinement of their depth map. -/
theorem exists_origin_refining
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (rows : FinFourCanonicalPaidEndpointRows packet)
    (rayReturn : packet.MaximalPrefixRayMinimumReturn) :
    ∃ origin : FinFourCanonicalPaidEndpointOrigin packet,
      ∃ refinement : ℕ → ℕ, StrictMono refinement ∧
        origin.rows.depth = rows.depth ∘ refinement := by
  have hmem : ∀ rank, rows.family.baseDecoration rank ∈
      rows.family.prefixOrbitAmbient := by
    intro rank
    simpa only [QuittingMarkedPairDecoratedFamily.rawDecoration_nil] using
      rows.family.rawDecoration_mem_ambient rank []
  obtain ⟨limit, hlimit, refinement, hrefinement, htendsto⟩ :=
    rows.family.prefixOrbitAmbient_isCompact.tendsto_subseq hmem
  let refinedRows := rows.reindex refinement hrefinement
  refine ⟨{
    rayReturn := rayReturn
    rows := refinedRows
    limit := limit
    limit_mem_ambient := hlimit
    decorations_tendsto := ?_
  }, refinement, hrefinement, rfl⟩
  change Tendsto
    (rows.reindex refinement hrefinement).family.baseDecoration atTop
      (nhds limit)
  convert htendsto using 1
  funext rank
  exact rows.reindex_family_baseDecoration refinement hrefinement rank

end FinFourCanonicalPaidEndpointRows

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- The canonical ray's paid endpoints admit one fixed-action compact joint
origin.  No endpoint minimum/strict decision is made here. -/
theorem nonempty_canonicalPaidEndpointOrigin
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (rayReturn : packet.MaximalPrefixRayMinimumReturn) :
    Nonempty (FinFourCanonicalPaidEndpointOrigin packet) := by
  obtain ⟨action, firstSubseq, hfirst, haction⟩ :=
    exists_fixed_bool_strictMono_subsequence
      (fun index ↦ (packet.rayPaidAdapter index).action)
  let firstRows : FinFourCanonicalPaidEndpointRows packet := {
    action := action
    depth := firstSubseq
    depth_strictMono := hfirst
    action_eq := haction
    terminal := (packet.rayPaidAdapter (firstSubseq 0)).routedTerminal
    routedTerminal_eq := by
      intro rank
      apply Subtype.ext
      change quittingPureEndpointRoutedCoalition packet.rayTerminal.val packet.payer
            (packet.rayPaidAdapter (firstSubseq rank)).action =
          quittingPureEndpointRoutedCoalition packet.rayTerminal.val packet.payer
            (packet.rayPaidAdapter (firstSubseq 0)).action
      rw [haction rank, haction 0]
  }
  obtain ⟨origin, _⟩ := firstRows.exists_origin_refining rayReturn
  exact ⟨origin⟩

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

namespace FinFourCanonicalPaidEndpointOrigin

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

/-- The semantic whole-profile coordinates of the stored rows converge to
the semantic coordinate of this very decorated origin. -/
theorem wholeSemantic_tendsto
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (origin.rows.family.profile rank)) atTop
      (nhds origin.limit.whole.1) := by
  have hprojection : Continuous
      (fun point : QuittingMarkedPairDecoration (Fin 4) ↦ point.1.1.1) := by
    fun_prop
  have hlimit := (hprojection.tendsto origin.limit).comp
    origin.decorations_tendsto
  simpa only [Function.comp_def,
    QuittingMarkedPairDecoratedFamily.baseDecoration,
    QuittingMarkedPairDecoration.whole] using hlimit

theorem limit_tailDebt_eq_minimum
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    origin.limit.tailDebt =
      quittingTerminalSemanticDebtSum source.point.1 := by
  have hlimit : Tendsto (fun rank ↦
      (origin.rows.family.baseDecoration rank).tailDebt) atTop
      (nhds origin.limit.tailDebt) :=
    (QuittingMarkedPairDecoration.continuous_tailDebt.tendsto origin.limit).comp
      origin.decorations_tendsto
  have hminimum := origin.rows.tailDebt_tendsto_minimum
  have hminimum' : Tendsto (fun rank ↦
      (origin.rows.family.baseDecoration rank).tailDebt) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
    simpa only [QuittingMarkedPairDecoration.tailDebt,
      QuittingMarkedPairDecoratedFamily.baseDecoration,
      QuittingMarkedPairDecoration.tail,
      FinFourCanonicalPaidEndpointRows.family_profile,
      FinFourCanonicalPaidEndpointRows.family_mark] using hminimum
  exact tendsto_nhds_unique hlimit hminimum'

theorem limit_wholeDebt_pos
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    0 < origin.limit.wholeDebt := by
  have hcarrier :=
    QuittingMarkedPairDecoratedFamily.semantic_mem_carrier_of_law_mem_carrier
      origin.limit.whole origin.limit_mem_ambient.1.1
  exact source.minimumDebt_pos.trans_le
    (source.minimum origin.limit.whole.1 hcarrier)

theorem limit_markedMass_pos
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    0 < origin.limit.markedMass := by
  have hlimit : Tendsto (fun rank ↦
      (origin.rows.family.baseDecoration rank).markedMass) atTop
      (nhds origin.limit.markedMass) :=
    ((continuous_fst.comp continuous_snd).tendsto origin.limit).comp
      origin.decorations_tendsto
  let floor := packet.rayResolution ^ 2
  have hfloorPos : 0 < floor := sq_pos_of_pos packet.rayResolution_pos
  have hlower : ∀ rank, floor ≤
      (origin.rows.family.baseDecoration rank).markedMass := by
    intro rank
    change floor ≤ quittingStageCoalitionMass reward
      (packet.rayPaidTargetProfile (origin.rows.depth rank))
        (origin.rows.depth rank) origin.rows.terminal
    rw [show origin.rows.terminal =
        (packet.rayPaidAdapter (origin.rows.depth rank)).routedTerminal by
      exact (origin.rows.routedTerminal_eq rank).symm]
    change floor ≤ quittingStageCoalitionMass reward
      (quittingMaximalCapSemanticPrefixProfile reward packet.raySource
        (packet.rayPaidAdapter (origin.rows.depth rank)).targetProfile
        (origin.rows.depth rank))
      (origin.rows.depth rank + 0)
      (packet.rayPaidAdapter (origin.rows.depth rank)).routedTerminal
    rw [quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add]
    have hsurvival :=
      minimumDebt_div_sourceDebt_le_maximalCapSemanticPrefixSurvival reward
        source.point.1 packet.raySource source.minimum source.minimumDebt_pos
          packet.raySource_mem (origin.rows.depth rank)
    have hresolution : packet.rayResolution ≤
        quittingMaximalCapSemanticPrefixSurvival reward packet.raySource
          (origin.rows.depth rank) := by
      simpa only [FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayResolution]
        using hsurvival
    have hstage :=
      (packet.rayPaidAdapter (origin.rows.depth rank)).resolution_le_targetStageMass
    dsimp only [floor]
    rw [pow_two]
    exact mul_le_mul hresolution hstage packet.rayResolution_pos.le
      (quittingMaximalCapSemanticPrefixSurvival_nonneg reward packet.raySource
        (origin.rows.depth rank))
  exact hfloorPos.trans_le (ge_of_tendsto' hlimit hlower)

theorem limit_actualGain_pos
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    0 < origin.limit.actualGain := by
  have hlimit : Tendsto (fun rank ↦
      (origin.rows.family.baseDecoration rank).actualGain) atTop
      (nhds origin.limit.actualGain) :=
    ((continuous_snd.comp continuous_snd).tendsto origin.limit).comp
      origin.decorations_tendsto
  let floor := packet.rayResolution *
    quittingTerminalSemanticDebtSum source.point.1 / 3
  have hfloorPos : 0 < floor :=
    div_pos (mul_pos packet.rayResolution_pos source.minimumDebt_pos)
      (by norm_num)
  have hlower : ∀ rank, floor ≤
      (origin.rows.family.baseDecoration rank).actualGain := by
    intro rank
    exact packet.rayResolution_mul_minimumDebt_div_three_le_rayPaidGain
      (origin.rows.depth rank)
  exact hfloorPos.trans_le (ge_of_tendsto' hlimit hlower)

def passport (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    QuittingMarkedPairDecoratedFamily.ConvergentPassport origin.rows.family
      source.point.1 where
  limit := origin.limit
  tendsto_base := origin.decorations_tendsto
  tailDebt_eq := origin.limit_tailDebt_eq_minimum
  wholeDebt_pos := origin.limit_wholeDebt_pos
  markedMass_pos := origin.limit_markedMass_pos
  actualGain_pos := origin.limit_actualGain_pos

def massDensity (origin : FinFourCanonicalPaidEndpointOrigin packet) : ℝ :=
  origin.limit.markedMass / (2 * origin.limit.wholeDebt)

def gainDensity (origin : FinFourCanonicalPaidEndpointOrigin packet) : ℝ :=
  origin.limit.actualGain / (2 * origin.limit.wholeDebt)

theorem massDensity_pos
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    0 < origin.massDensity :=
  div_pos origin.limit_markedMass_pos
    (mul_pos (by norm_num) origin.limit_wholeDebt_pos)

theorem gainDensity_pos
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    0 < origin.gainDensity :=
  div_pos origin.limit_actualGain_pos
    (mul_pos (by norm_num) origin.limit_wholeDebt_pos)

theorem massDensity_mul_wholeDebt_lt
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    origin.massDensity * origin.limit.wholeDebt < origin.limit.markedMass := by
  rw [massDensity]
  field_simp [ne_of_gt origin.limit_wholeDebt_pos]
  linarith [origin.limit_markedMass_pos]

theorem gainDensity_mul_wholeDebt_lt
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    origin.gainDensity * origin.limit.wholeDebt < origin.limit.actualGain := by
  rw [gainDensity]
  field_simp [ne_of_gt origin.limit_wholeDebt_pos]
  linarith [origin.limit_actualGain_pos]

end FinFourCanonicalPaidEndpointOrigin

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket
namespace CanonicalPairMinimumEndpointDebtAscent

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

/-- Direct fixed-action rows from the concentrated packet already aligned
with the generic strict endpoint cluster. -/
def endpointRows (ascent : CanonicalPairMinimumEndpointDebtAscent packet) :
    FinFourCanonicalPaidEndpointRows packet where
  action := ascent.endpointPacket.action
  depth := ascent.endpointPacket.subsequence
  depth_strictMono := ascent.endpointPacket.subsequence_strictMono
  action_eq := ascent.endpointPacket.action_eq
  terminal := ascent.endpointPacket.terminal
  routedTerminal_eq := ascent.endpointPacket.terminal_eq

@[simp] theorem endpointRows_depth
    (ascent : CanonicalPairMinimumEndpointDebtAscent packet) :
    ascent.endpointRows.depth = ascent.endpointPacket.subsequence := rfl

@[simp] theorem endpointRows_family_profile
    (ascent : CanonicalPairMinimumEndpointDebtAscent packet) (rank : ℕ) :
    ascent.endpointRows.family.profile rank =
      packet.rayPaidTargetProfile (ascent.endpointPacket.subsequence rank) :=
  rfl

end CanonicalPairMinimumEndpointDebtAscent
end FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- The canonical endpoint excursion is strictly above the positive global
minimum.  The exact canonical endpoint origin is retained, not reconstructed
from the unrelated first forced-owner endpoint family. -/
structure FinFourCanonicalStrictEndpointOrigin
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  origin : FinFourCanonicalPaidEndpointOrigin packet
  strict : quittingTerminalSemanticDebtSum source.point.1 <
    origin.limit.wholeDebt

/-- A strict endpoint origin built on a further refinement of the exact
subsequence already stored by the canonical debt-ascent branch. -/
structure FinFourCanonicalDebtAscentStrictEndpointOrigin
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (ascent :
      FinFourOwnerCompressedMinimumReturnForcedPairPacket.CanonicalPairMinimumEndpointDebtAscent
        packet) where
  strictOrigin : FinFourCanonicalStrictEndpointOrigin packet
  endpointRefinement : ℕ → ℕ
  endpointRefinement_strictMono : StrictMono endpointRefinement
  rows_depth_eq : strictOrigin.origin.rows.depth =
    ascent.endpointPacket.subsequence ∘ endpointRefinement
  limit_whole_eq_endpointCluster : strictOrigin.origin.limit.whole.1 =
    ascent.debtAscent.endpointCluster

namespace FinFourCanonicalDebtAscentStrictEndpointOrigin

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {ascent :
    FinFourOwnerCompressedMinimumReturnForcedPairPacket.CanonicalPairMinimumEndpointDebtAscent
      packet}

/-- Every direct decorated row is the literal canonical paid endpoint on the
recorded further refinement of the debt-ascent packet. -/
theorem rows_profile_eq
    (strict : FinFourCanonicalDebtAscentStrictEndpointOrigin ascent)
    (rank : ℕ) :
    strict.strictOrigin.origin.rows.family.profile rank =
      packet.rayPaidTargetProfile
        (ascent.endpointPacket.subsequence
          (strict.endpointRefinement rank)) := by
  change packet.rayPaidTargetProfile
      (strict.strictOrigin.origin.rows.depth rank) = _
  rw [strict.rows_depth_eq]
  rfl

/-- The whole-debt limit of the decorated strict origin is the exact total
debt of the generic debt-ascent endpoint cluster. -/
theorem limit_wholeDebt_eq_endpointCluster
    (strict : FinFourCanonicalDebtAscentStrictEndpointOrigin ascent) :
    strict.strictOrigin.origin.limit.wholeDebt =
      quittingTerminalSemanticDebtSum ascent.debtAscent.endpointCluster := by
  unfold QuittingMarkedPairDecoration.wholeDebt
  rw [strict.limit_whole_eq_endpointCluster]

end FinFourCanonicalDebtAscentStrictEndpointOrigin

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket
namespace CanonicalPairMinimumEndpointDebtAscent

/-- Compactifying the debt-ascent packet on a further subsequence yields a
strict decorated origin at that very generic endpoint cluster. -/
theorem nonempty_strictEndpointOrigin
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (ascent : CanonicalPairMinimumEndpointDebtAscent packet) :
    Nonempty (FinFourCanonicalDebtAscentStrictEndpointOrigin ascent) := by
  obtain ⟨origin, endpointRefinement, hrefinement, hdepth⟩ :=
    ascent.endpointRows.exists_origin_refining ascent.rayReturn
  have horigin := origin.wholeSemantic_tendsto
  have hendpoint := ascent.endpointPacket_endpoint_tendsto.comp
    hrefinement.tendsto_atTop
  have hfunctions : (fun rank ↦ quittingTerminalSemanticPair reward
      (origin.rows.family.profile rank)) = fun rank ↦
        quittingTerminalSemanticPair reward
          (packet.rayPaidTargetProfile
            (ascent.endpointPacket.subsequence
              (endpointRefinement rank))) := by
    funext rank
    change quittingTerminalSemanticPair reward
        (packet.rayPaidTargetProfile (origin.rows.depth rank)) = _
    rw [hdepth]
    rfl
  rw [hfunctions] at horigin
  have hlimitEq : origin.limit.whole.1 =
      ascent.debtAscent.endpointCluster :=
    tendsto_nhds_unique horigin hendpoint
  have hstrict : quittingTerminalSemanticDebtSum source.point.1 <
      origin.limit.wholeDebt := by
    unfold QuittingMarkedPairDecoration.wholeDebt
    rw [hlimitEq]
    exact ascent.endpointCluster_debtSum_gt_minimum
  exact ⟨{
    strictOrigin := { origin := origin, strict := hstrict }
    endpointRefinement := endpointRefinement
    endpointRefinement_strictMono := hrefinement
    rows_depth_eq := hdepth
    limit_whole_eq_endpointCluster := hlimitEq
  }⟩

end CanonicalPairMinimumEndpointDebtAscent
end FinFourOwnerCompressedMinimumReturnForcedPairPacket

namespace FinFourCanonicalPaidEndpointOrigin

/-- Every canonical paid-endpoint origin is either already on the minimum
fibre or gives the named strict endpoint origin. -/
theorem minimum_or_nonempty_strict
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (origin : FinFourCanonicalPaidEndpointOrigin packet) :
    origin.limit.wholeDebt = quittingTerminalSemanticDebtSum source.point.1 ∨
      Nonempty (FinFourCanonicalStrictEndpointOrigin packet) := by
  have hlower : quittingTerminalSemanticDebtSum source.point.1 ≤
      origin.limit.wholeDebt := by
    have hcarrier :=
      QuittingMarkedPairDecoratedFamily.semantic_mem_carrier_of_law_mem_carrier
        origin.limit.whole origin.limit_mem_ambient.1.1
    exact source.minimum origin.limit.whole.1 hcarrier
  rcases hlower.eq_or_lt with heq | hlt
  · exact Or.inl heq.symm
  · exact Or.inr ⟨{ origin := origin, strict := hlt }⟩

end FinFourCanonicalPaidEndpointOrigin

namespace FinFourCanonicalStrictEndpointOrigin

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}

def family (strict : FinFourCanonicalStrictEndpointOrigin packet) :=
  strict.origin.rows.family

def terminal (strict : FinFourCanonicalStrictEndpointOrigin packet) :=
  strict.origin.rows.terminal

def markedOwner (_strict : FinFourCanonicalStrictEndpointOrigin packet) :=
  packet.payer

def other (_strict : FinFourCanonicalStrictEndpointOrigin packet) :=
  returnSource.forcedOwner

def witness (_strict : FinFourCanonicalStrictEndpointOrigin packet) :=
  source.residual.witness

@[simp] theorem family_eq
    (strict : FinFourCanonicalStrictEndpointOrigin packet) :
    strict.family = strict.origin.rows.family := rfl

@[simp] theorem markedOwner_eq
    (strict : FinFourCanonicalStrictEndpointOrigin packet) :
    strict.markedOwner = packet.payer := rfl

@[simp] theorem other_eq
    (strict : FinFourCanonicalStrictEndpointOrigin packet) :
    strict.other = returnSource.forcedOwner := rfl

theorem other_ne_markedOwner
    (strict : FinFourCanonicalStrictEndpointOrigin packet) :
    strict.other ≠ strict.markedOwner :=
  packet.payer_ne_forcedOwner.symm

theorem other_mem_terminal
    (strict : FinFourCanonicalStrictEndpointOrigin packet) :
    strict.other ∈ strict.terminal.val :=
  strict.origin.rows.other_mem_terminal

end FinFourCanonicalStrictEndpointOrigin

namespace QuittingMarkedPairMinimumReturnActualizer

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {strict : FinFourCanonicalStrictEndpointOrigin packet}
  {point : QuittingMarkedPairDecoration (Fin 4)}

/-- The canonical maximal-ray depth behind one actualized strict endpoint. -/
def strictEndpointDepth
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (rank : ℕ) : ℕ :=
  strict.origin.rows.depth (actualizer.originRank rank)

/-- The literal root word prefixed by the normalized actualizer. -/
def strictEndpointRoots
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (rank : ℕ) : List (Fin 4 → PMF Bool) :=
  actualizer.originRoots rank

/-- Every normalized target profile is the displayed literal root word on the
canonical paid endpoint at its retained maximal-ray depth. -/
theorem strictEndpoint_profile_eq_literalRootStack
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (rank : ℕ) :
    actualizer.profiles rank =
      quittingLiteralRootStackProfile reward
        (actualizer.strictEndpointRoots rank)
        (packet.rayPaidTargetProfile (actualizer.strictEndpointDepth rank)) := by
  rfl

/-- The comparison profile uses the same word on the literal pre-endpoint
canonical ray source; it is gain provenance, not a transported Nash claim. -/
theorem strictEndpoint_sourceProfile_eq_literalRootStack
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (rank : ℕ) :
    actualizer.sourceProfiles rank =
      quittingLiteralRootStackProfile reward
        (actualizer.strictEndpointRoots rank)
        (packet.rayFamily.rayProfiles
          (actualizer.strictEndpointDepth rank)) := by
  rfl

/-- The actual marked date is the word length plus the retained canonical
maximal-ray depth. -/
theorem strictEndpoint_mark_eq
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (rank : ℕ) :
    actualizer.mark rank =
      (actualizer.strictEndpointRoots rank).length +
        actualizer.strictEndpointDepth rank := by
  rfl

/-- Arbitrary-prefix actualization preserves the full near-minimum behavioral
tail of the canonical ray row. -/
theorem strictEndpoint_postMarkSpine_eq_rayTail
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (rank : ℕ) :
    quittingAllContinueProfileSpine reward (actualizer.profiles rank)
        (actualizer.mark rank + 1) =
      packet.rayTail (actualizer.strictEndpointDepth rank) := by
  calc
    quittingAllContinueProfileSpine reward (actualizer.profiles rank)
          (actualizer.mark rank + 1) =
        quittingAllContinueProfileSpine reward
          (strict.family.profile (actualizer.originRank rank))
          (strict.family.mark (actualizer.originRank rank) + 1) := by
      exact strict.family.descendant_postMarkSpine_eq
        (actualizer.originRank rank) (actualizer.originRoots rank)
    _ = packet.rayTail (actualizer.strictEndpointDepth rank) :=
      strict.origin.rows.postMarkSpine_eq_tail (actualizer.originRank rank)

/-- The normalized packet's positive historical gain is the literal payoff
difference between its target and comparison profiles. -/
theorem strictEndpoint_gainFloor_le_actualPayoffGain
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (rank : ℕ) :
    actualizer.gainFloor ≤
      quittingTerminalPayoff reward (actualizer.profiles rank) packet.payer -
        quittingTerminalPayoff reward (actualizer.sourceProfiles rank)
          packet.payer := by
  simpa only [FinFourCanonicalStrictEndpointOrigin.family,
    FinFourCanonicalPaidEndpointRows.family_gainMover] using
      actualizer.gainFloor_le_actualPayoffGain rank

/-- Whole debts of the actual strict-endpoint descendants converge to the
original global minimum in the normalized-return arm. -/
theorem strictEndpoint_wholeDebt_tendsto_minimum
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (hreturn : point.wholeDebt =
      quittingTerminalSemanticDebtSum source.point.1) :
    Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (actualizer.profiles rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1)) :=
  actualizer.wholeDebt_tendsto_minimum hreturn

/-- Post-mark tail debts of those same actual descendants converge to the
original global minimum. -/
theorem strictEndpoint_tailDebt_tendsto_minimum
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (htail : point.tailDebt =
      quittingTerminalSemanticDebtSum source.point.1) :
    Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (actualizer.profiles rank)
          (actualizer.mark rank + 1)))) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1)) :=
  actualizer.tailDebt_tendsto_minimum htail

end QuittingMarkedPairMinimumReturnActualizer

/-- Literal output of the existing concentrated consumer on one canonical
strict-endpoint minimum-return actualizer. -/
def FinFourStrictEndpointConsumerOutput
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (strict : FinFourCanonicalStrictEndpointOrigin packet)
    {point : QuittingMarkedPairDecoration (Fin 4)}
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point) :
    Prop :=
  HasQuittingConcentratedSingletonStrategicDispatch strict.witness
      actualizer.packet strict.other ∨
    Nonempty (QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 strict.markedOwner strict.terminal actualizer.packet)

namespace FinFourCanonicalStrictEndpointOrigin

variable
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda}
  {point : QuittingMarkedPairDecoration (Fin 4)}

/-- The exact intermediate packet consumer requested by the strict-endpoint
reduction.  Witness, other member, minimum, owner, terminal, profiles, and
packet are all the fields of this one canonical actualizer. -/
theorem consumerOutput
    (strict : FinFourCanonicalStrictEndpointOrigin packet)
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point) :
    FinFourStrictEndpointConsumerOutput strict actualizer := by
  exact source.residual.witness
    |>.concentratedPacket_singletonStrategic_or_collisionMinimumResidual
      source.point.1 actualizer.packet strict.other
        strict.other_ne_markedOwner strict.other_mem_terminal
        source.semantic_mem source.minimum source.minimumDebt_pos
        actualizer.scale_pos actualizer.scale_tendsto_zero

/-- Every collision residual selected from this actualizer has tail-cluster
debt exactly equal to the original minimum. -/
theorem collisionResidual_clusterDebt_eq_minimum
    (strict : FinFourCanonicalStrictEndpointOrigin packet)
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (htail : point.tailDebt =
      quittingTerminalSemanticDebtSum source.point.1)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 strict.markedOwner strict.terminal actualizer.packet) :
    quittingTerminalSemanticDebtSum residual.cluster =
      quittingTerminalSemanticDebtSum source.point.1 := by
  have hcluster : Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (actualizer.profiles (actualizer.packet.subseq
            (residual.subseq rank)))
          (actualizer.packet.mark (residual.subseq rank) + 1)))) atTop
      (nhds (quittingTerminalSemanticDebtSum residual.cluster)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      residual.tail_tendsto
  have hminimum := (actualizer.tailDebt_tendsto_minimum htail).comp
    residual.subseq_strictMono.tendsto_atTop
  simpa only [id_eq] using tendsto_nhds_unique hcluster hminimum

/-- The collision residual's exhaustive split is therefore literally in its
minimum-tail other-defect arm. -/
theorem collisionResidual_minimumTail
    (strict : FinFourCanonicalStrictEndpointOrigin packet)
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (htail : point.tailDebt =
      quittingTerminalSemanticDebtSum source.point.1)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 strict.markedOwner strict.terminal actualizer.packet) :
    quittingTerminalSemanticDebtSum residual.cluster =
        quittingTerminalSemanticDebtSum source.point.1 ∧
      ∀ᶠ rank in atTop,
        actualizer.packet.resolution *
              quittingTerminalSemanticDebtSum source.point.1 / 2 ≤
          ∑ other ∈ Finset.univ.erase strict.markedOwner,
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward
                  (actualizer.profiles
                    (actualizer.packet.subseq (residual.subseq rank)))
                  (actualizer.packet.mark (residual.subseq rank) + 1))).1
              (quittingProfileLiveRoot reward
                (actualizer.profiles
                  (actualizer.packet.subseq (residual.subseq rank)))
                (actualizer.packet.mark (residual.subseq rank))) other := by
  have heq := strict.collisionResidual_clusterDebt_eq_minimum
    actualizer htail residual
  rcases residual.escape_or_otherDefect with hescape | hminimum
  · rw [heq] at hescape
    exact (lt_irrefl _ hescape).elim
  · exact ⟨heq, hminimum.2⟩

/-- In the nonsingleton routed-terminal case, the same actualizer reaches the
actual endpoint-law consumer and hence strict target-debt ascent or exact
minimum-source regeneration.  This does not consume either result further. -/
theorem nonempty_threeRoleRegenerationOrAscent
    (strict : FinFourCanonicalStrictEndpointOrigin packet)
    (actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
      source.point.1 strict.origin.massDensity strict.origin.gainDensity point)
    (hreturn : point.wholeDebt =
      quittingTerminalSemanticDebtSum source.point.1)
    (htail : point.tailDebt =
      quittingTerminalSemanticDebtSum source.point.1)
    (hterminal : 1 < strict.terminal.val.card) :
    Nonempty (FinFourThreeRoleRegenerationOrAscent source actualizer.packet) := by
  obtain ⟨mover, recipient, ⟨endpoint⟩⟩ :=
    actualizer.nonempty_threeRoleEndpointLaw_of_minimumReturn
      source.semantic_mem source.minimum source.minimumDebt_pos hterminal
        hreturn htail
  exact endpoint.nonempty_finFourRegenerationOrAscent

end FinFourCanonicalStrictEndpointOrigin

/-- The normalized minimizer's exact branch proposition. -/
def FinFourStrictEndpointNormalizedOutcome
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (strict : FinFourCanonicalStrictEndpointOrigin packet)
    (point : QuittingMarkedPairDecoration (Fin 4)) : Prop :=
  (∃ actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
        source.point.1 strict.origin.massDensity strict.origin.gainDensity point,
      point.wholeDebt = quittingTerminalSemanticDebtSum source.point.1 ∧
        FinFourStrictEndpointConsumerOutput strict actualizer) ∨
    (quittingTerminalSemanticDebtSum source.point.1 < point.wholeDebt ∧
      ∀ root : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward point.whole.1.2 0 root ↔
          root = (quittingAllContinueRoot : Fin 4 → PMF Bool))

/-- One strict canonical paid-endpoint origin, its normalized-slice minimizer,
and the literal minimum-return packet output or strict inert alternative. -/
structure FinFourStrictEndpointNormalizedReturnOrInert
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (strict : FinFourCanonicalStrictEndpointOrigin packet) where
  point : QuittingMarkedPairDecoration (Fin 4)
  point_mem : point ∈ strict.family.normalizedPassportSlice source.point.1
    strict.origin.massDensity strict.origin.gainDensity
  point_minimal : ∀ candidate ∈
      strict.family.normalizedPassportSlice source.point.1
        strict.origin.massDensity strict.origin.gainDensity,
    point.wholeDebt ≤ candidate.wholeDebt
  minimum_le_point :
    quittingTerminalSemanticDebtSum source.point.1 ≤ point.wholeDebt
  outcome : FinFourStrictEndpointNormalizedOutcome strict point

/-- The normalized result of one generic debt-ascent branch, retaining the
same source-attached ascent and its cluster-coherent strict endpoint origin. -/
structure FinFourCanonicalDebtAscentNormalizedReturnOrInert
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (ascent :
      FinFourOwnerCompressedMinimumReturnForcedPairPacket.CanonicalPairMinimumEndpointDebtAscent
        packet) where
  strictSource : FinFourCanonicalDebtAscentStrictEndpointOrigin ascent
  normalized : FinFourStrictEndpointNormalizedReturnOrInert
    strictSource.strictOrigin

/-- Stronger one-way consumer view of a normalized strict endpoint.  In the
minimum-return arm it keeps the actualizer and reaches the actual three-role
endpoint-law classifier; in the other arm it keeps the same inert point. -/
def FinFourStrictEndpointThreeRoleOrInert
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (strict : FinFourCanonicalStrictEndpointOrigin packet)
    (result : FinFourStrictEndpointNormalizedReturnOrInert strict) : Prop :=
  (∃ actualizer : QuittingMarkedPairMinimumReturnActualizer strict.family
        source.point.1 strict.origin.massDensity strict.origin.gainDensity
          result.point,
      result.point.wholeDebt =
          quittingTerminalSemanticDebtSum source.point.1 ∧
        Nonempty (FinFourThreeRoleRegenerationOrAscent source
          actualizer.packet)) ∨
    (quittingTerminalSemanticDebtSum source.point.1 < result.point.wholeDebt ∧
      ∀ root : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward result.point.whole.1.2 0 root ↔
          root = (quittingAllContinueRoot : Fin 4 → PMF Bool))

namespace FinFourStrictEndpointNormalizedReturnOrInert

/-- A nonsingleton routed terminal upgrades the normalized equality arm to
the actual endpoint-law regeneration/ascent classifier, while leaving the
strict inert arm unchanged. -/
theorem threeRoleRegenerationOrAscent_or_inert
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    {strict : FinFourCanonicalStrictEndpointOrigin packet}
    (result : FinFourStrictEndpointNormalizedReturnOrInert strict)
    (hterminal : 1 < strict.terminal.val.card) :
    FinFourStrictEndpointThreeRoleOrInert strict result := by
  rcases result.outcome with hreturn | hinert
  · left
    obtain ⟨actualizer, hwhole, _consumer⟩ := hreturn
    exact ⟨actualizer, hwhole,
      strict.nonempty_threeRoleRegenerationOrAscent actualizer hwhole
        result.point_mem.2.1 hterminal⟩
  · exact Or.inr hinert

end FinFourStrictEndpointNormalizedReturnOrInert

namespace FinFourCanonicalStrictEndpointOrigin

/-- Normalize the exact strict canonical endpoint family.  The equality arm
first stores the strategic/collision output on the same literal packet; the
stronger endpoint-law consumers remain available independently. -/
theorem nonempty_normalizedReturn_or_inert
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (strict : FinFourCanonicalStrictEndpointOrigin packet) :
    Nonempty (FinFourStrictEndpointNormalizedReturnOrInert strict) := by
  obtain ⟨point, hpoint, hminimal, hlower, hbranch⟩ :=
    strict.family.exists_minimum_normalizedPassportSlice_eq_or_strict_inert
      source.point.1 source.minimum source.minimumDebt_pos
        strict.origin.passport strict.origin.massDensity
          strict.origin.gainDensity
          strict.origin.massDensity_mul_wholeDebt_lt
          strict.origin.gainDensity_mul_wholeDebt_lt
  refine ⟨{
    point := point
    point_mem := hpoint
    point_minimal := hminimal
    minimum_le_point := hlower
    outcome := ?_
  }⟩
  rcases hbranch with hreturn | hinert
  · obtain ⟨actualizer⟩ := nonempty_quittingMarkedPairMinimumReturnActualizer
      strict.family source.point.1 strict.origin.massDensity
        strict.origin.gainDensity point strict.origin.massDensity_pos
          strict.origin.gainDensity_pos source.minimumDebt_pos hpoint hreturn
    exact Or.inl ⟨actualizer, hreturn, strict.consumerOutput actualizer⟩
  · exact Or.inr hinert

end FinFourCanonicalStrictEndpointOrigin

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket
namespace CanonicalPairMinimumEndpointDebtAscent

/-- Normalize the strict endpoint origin selected on a further subsequence of
this exact debt-ascent branch. -/
theorem nonempty_strictNormalizedReturnOrInert
    {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda}
    (ascent : CanonicalPairMinimumEndpointDebtAscent packet) :
    Nonempty (FinFourCanonicalDebtAscentNormalizedReturnOrInert ascent) := by
  obtain ⟨strictSource⟩ := ascent.nonempty_strictEndpointOrigin
  obtain ⟨normalized⟩ :=
    strictSource.strictOrigin.nonempty_normalizedReturn_or_inert
  exact ⟨{ strictSource := strictSource, normalized := normalized }⟩

end CanonicalPairMinimumEndpointDebtAscent
end FinFourOwnerCompressedMinimumReturnForcedPairPacket

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- Source-facing canonical endpoint split.  The same committed maximal ray
produces either a compact paid-endpoint limit already on the minimum fibre, or
the normalized strict-endpoint return/inert result.  The first arm deliberately
does not identify itself with any support-rank handoff object. -/
theorem canonicalPaidEndpointMinimum_or_nonempty_strictNormalizedReturnOrInert
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (rayReturn : packet.MaximalPrefixRayMinimumReturn) :
    (∃ origin : FinFourCanonicalPaidEndpointOrigin packet,
      origin.limit.wholeDebt =
        quittingTerminalSemanticDebtSum source.point.1) ∨
      ∃ strict : FinFourCanonicalStrictEndpointOrigin packet,
        Nonempty (FinFourStrictEndpointNormalizedReturnOrInert strict) := by
  obtain ⟨origin⟩ := packet.nonempty_canonicalPaidEndpointOrigin rayReturn
  rcases origin.minimum_or_nonempty_strict with hminimum | hstrict
  · exact Or.inl ⟨origin, hminimum⟩
  · obtain ⟨strict⟩ := hstrict
    exact Or.inr ⟨strict, strict.nonempty_normalizedReturn_or_inert⟩

/-- Source-facing composition of the canonical support handoff, the
cluster-coherent strict normalized endpoint result, and the unchanged strict
scalar-ray stall. -/
theorem nonempty_canonicalPairSupportHandoff_or_strictNormalized_or_rayStall
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (CanonicalPairMinimumEndpointSupportRankHandoff packet) ∨
      (∃ ascent : CanonicalPairMinimumEndpointDebtAscent packet,
        Nonempty (FinFourCanonicalDebtAscentNormalizedReturnOrInert ascent)) ∨
      Nonempty (MaximalPrefixRayStall packet) := by
  rcases packet
      |>.nonempty_canonicalPairMinimumEndpointSupportRankHandoff_or_debtAscent_or_rayStall
    with hhandoff | hascent | hstall
  · exact Or.inl hhandoff
  · obtain ⟨ascent⟩ := hascent
    exact Or.inr (Or.inl
      ⟨ascent, ascent.nonempty_strictNormalizedReturnOrInert⟩)
  · exact Or.inr (Or.inr hstall)

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
