/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ConcentratedCollisionFourRoleMonodromy
import Research.Quitting.NormalizedPassportMinimizer

/-!
# Actualizing the minimum-return arm of a normalized passport

When a normalized-slice minimizer has whole debt equal to the global minimum,
raw arbitrary-prefix descendants approaching it can be shifted far enough to
retain uniform mass and actual-gain floors.  This file records those actual
profiles and compiles their zero marked-owner defect into the existing
concentrated packet interface.

The construction is conditional on supplied fixed-label decorated-family data.
It does not produce that family from a Fin4 atlas source, and it does not claim
that the closed minimizer itself is behaviorally attained.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Raw actual descendants approaching a minimum-return decorated point, with
uniform quantitative floors retained after one sequence shift. -/
structure QuittingMarkedPairMinimumReturnActualizer
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair ι)
    (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι) where
  originRank : ℕ → ℕ
  originRoots : ℕ → List (ι → PMF Bool)
  decorations_tendsto : Tendsto (fun rank =>
    family.rawDecoration (originRank rank) (originRoots rank)) atTop (nhds point)
  resolution : ℝ
  resolution_eq : resolution =
    massDensity * quittingTerminalSemanticDebtSum minimum / 2
  resolution_pos : 0 < resolution
  gainFloor : ℝ
  gainFloor_eq : gainFloor =
    gainDensity * quittingTerminalSemanticDebtSum minimum / 2
  gainFloor_pos : 0 < gainFloor
  stageMass_floor : ∀ rank, resolution ≤
    (family.rawDecoration (originRank rank) (originRoots rank)).markedMass
  actualGain_floor : ∀ rank, gainFloor ≤
    (family.rawDecoration (originRank rank) (originRoots rank)).actualGain

/-- A positive normalized-slice point whose whole debt dominates the reference
debt produces actual raw descendants with half of the reference-based density
floors.  The equality-arm constructor below is the minimum-return
specialization. -/
theorem nonempty_quittingMarkedPairMinimumReturnActualizer_of_debt_le
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair ι)
    (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι)
    (hmassDensity : 0 < massDensity) (hgainDensity : 0 < gainDensity)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hpoint : point ∈
      family.normalizedPassportSlice minimum massDensity gainDensity)
    (hlower : quittingTerminalSemanticDebtSum minimum ≤ point.wholeDebt) :
    Nonempty (QuittingMarkedPairMinimumReturnActualizer
      family minimum massDensity gainDensity point) := by
  have hcarrier := hpoint.1
  rw [QuittingMarkedPairDecoratedFamily.prefixOrbitCarrier,
    mem_closure_iff_seq_limit] at hcarrier
  obtain ⟨rows, hrows, hrowsTendsto⟩ := hcarrier
  choose originRank originRoots horigin using hrows
  let resolution :=
    massDensity * quittingTerminalSemanticDebtSum minimum / 2
  let gainFloor :=
    gainDensity * quittingTerminalSemanticDebtSum minimum / 2
  have hresolutionPos : 0 < resolution := by
    exact div_pos (mul_pos hmassDensity hminimum_pos) (by norm_num)
  have hgainFloorPos : 0 < gainFloor := by
    exact div_pos (mul_pos hgainDensity hminimum_pos) (by norm_num)
  have hresolutionLt : resolution < point.markedMass := by
    have hlower : massDensity * quittingTerminalSemanticDebtSum minimum ≤
        point.markedMass :=
      (mul_le_mul_of_nonneg_left hlower hmassDensity.le).trans hpoint.2.2.1
    dsimp only [resolution]
    nlinarith [mul_pos hmassDensity hminimum_pos]
  have hgainFloorLt : gainFloor < point.actualGain := by
    have hlower : gainDensity * quittingTerminalSemanticDebtSum minimum ≤
        point.actualGain :=
      (mul_le_mul_of_nonneg_left hlower hgainDensity.le).trans hpoint.2.2.2
    dsimp only [gainFloor]
    nlinarith [mul_pos hgainDensity hminimum_pos]
  have hmassTendsto : Tendsto (fun rank => (rows rank).markedMass) atTop
      (nhds point.markedMass) := by
    exact ((continuous_fst.comp continuous_snd).tendsto point).comp hrowsTendsto
  have hgainTendsto : Tendsto (fun rank => (rows rank).actualGain) atTop
      (nhds point.actualGain) := by
    exact ((continuous_snd.comp continuous_snd).tendsto point).comp hrowsTendsto
  have heventually : ∀ᶠ rank in atTop,
      resolution < (rows rank).markedMass ∧
        gainFloor < (rows rank).actualGain := by
    filter_upwards [hmassTendsto.eventually_const_lt hresolutionLt,
      hgainTendsto.eventually_const_lt hgainFloorLt] with rank hmass hgain
    exact ⟨hmass, hgain⟩
  obtain ⟨start, hstart⟩ := eventually_atTop.1 heventually
  let shiftedRank : ℕ → ℕ := fun rank => originRank (rank + start)
  let shiftedRoots : ℕ → List (ι → PMF Bool) :=
    fun rank => originRoots (rank + start)
  have hshiftTendsto : Tendsto (fun rank => rows (rank + start)) atTop
      (nhds point) := (tendsto_add_atTop_iff_nat start).2 hrowsTendsto
  refine ⟨{
    originRank := shiftedRank
    originRoots := shiftedRoots
    decorations_tendsto := ?_
    resolution := resolution
    resolution_eq := rfl
    resolution_pos := hresolutionPos
    gainFloor := gainFloor
    gainFloor_eq := rfl
    gainFloor_pos := hgainFloorPos
    stageMass_floor := ?_
    actualGain_floor := ?_
  }⟩
  · apply hshiftTendsto.congr'
    filter_upwards [] with rank
    exact horigin (rank + start) |>.symm
  · intro rank
    have hrow := hstart (rank + start) (by omega)
    simpa only [shiftedRank, shiftedRoots, horigin] using hrow.1.le
  · intro rank
    have hrow := hstart (rank + start) (by omega)
    simpa only [shiftedRank, shiftedRoots, horigin] using hrow.2.le

/-- A minimum-return point in a positive normalized slice produces actual raw
descendants with the canonical half-density mass and gain floors. -/
theorem nonempty_quittingMarkedPairMinimumReturnActualizer
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair ι)
    (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι)
    (hmassDensity : 0 < massDensity) (hgainDensity : 0 < gainDensity)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hpoint : point ∈
      family.normalizedPassportSlice minimum massDensity gainDensity)
    (hreturn : point.wholeDebt =
      quittingTerminalSemanticDebtSum minimum) :
    Nonempty (QuittingMarkedPairMinimumReturnActualizer
      family minimum massDensity gainDensity point) :=
  nonempty_quittingMarkedPairMinimumReturnActualizer_of_debt_le
    family minimum massDensity gainDensity point hmassDensity hgainDensity
      hminimum_pos hpoint hreturn.ge

namespace QuittingMarkedPairMinimumReturnActualizer

variable
  {family : QuittingMarkedPairDecoratedFamily reward}
  {minimum : QuittingTerminalSemanticPair ι}
  {massDensity gainDensity : ℝ}
  {point : QuittingMarkedPairDecoration ι}

variable (actualizer : QuittingMarkedPairMinimumReturnActualizer
  family minimum massDensity gainDensity point)

/-- Actual endpoint profiles selected from the raw arbitrary-prefix orbit. -/
def profiles : ℕ → (quittingGame reward).BehaviorProfile := fun rank =>
  family.descendantProfile (actualizer.originRank rank)
    (actualizer.originRoots rank)

/-- Actual commonly-prefixed comparison profiles that witness the gain. -/
def sourceProfiles : ℕ → (quittingGame reward).BehaviorProfile := fun rank =>
  family.descendantSourceProfile (actualizer.originRank rank)
    (actualizer.originRoots rank)

/-- Shifted actual marked dates. -/
def mark : ℕ → ℕ := fun rank =>
  family.descendantMark (actualizer.originRank rank)
    (actualizer.originRoots rank)

/-- Literal source-rank/root-word provenance for every actualized row. -/
theorem profile_eq_descendant (rank : ℕ) :
    actualizer.profiles rank =
      family.descendantProfile (actualizer.originRank rank)
        (actualizer.originRoots rank) := rfl

/-- Literal comparison-profile provenance for every actualized row. -/
theorem sourceProfile_eq_descendant (rank : ℕ) :
    actualizer.sourceProfiles rank =
      family.descendantSourceProfile (actualizer.originRank rank)
        (actualizer.originRoots rank) := rfl

/-- Uniform unconditional marked-mass floor on the actual profiles. -/
theorem resolution_le_stageMass (rank : ℕ) :
    actualizer.resolution ≤ quittingStageCoalitionMass reward
      (actualizer.profiles rank) (actualizer.mark rank) family.terminal := by
  calc
    actualizer.resolution ≤
        (family.rawDecoration (actualizer.originRank rank)
          (actualizer.originRoots rank)).markedMass :=
      actualizer.stageMass_floor rank
    _ = quittingStageCoalitionMass reward (actualizer.profiles rank)
          (actualizer.mark rank) family.terminal := by
      simpa only [profiles, mark] using family.rawDecoration_markedMass_eq
        (actualizer.originRank rank) (actualizer.originRoots rank)

/-- Uniform actual payoff-gain floor, with both behavioral profiles exposed. -/
theorem gainFloor_le_actualPayoffGain (rank : ℕ) :
    actualizer.gainFloor ≤
      quittingTerminalPayoff reward (actualizer.profiles rank) family.gainMover -
        quittingTerminalPayoff reward (actualizer.sourceProfiles rank)
          family.gainMover := by
  calc
    actualizer.gainFloor ≤
        (family.rawDecoration (actualizer.originRank rank)
          (actualizer.originRoots rank)).actualGain :=
      actualizer.actualGain_floor rank
    _ = quittingTerminalPayoff reward (actualizer.profiles rank)
          family.gainMover -
        quittingTerminalPayoff reward (actualizer.sourceProfiles rank)
          family.gainMover := by
      simpa only [profiles, sourceProfiles] using
        family.rawDecoration_actualGain_eq (actualizer.originRank rank)
          (actualizer.originRoots rank)

/-- The marked owner's local root defect is exactly zero on every actualized
row, before any normalization by a vanishing scale. -/
theorem markedOwnerDefect_eq_zero (rank : ℕ) :
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (actualizer.profiles rank)
          (actualizer.mark rank + 1))).1
      (quittingProfileLiveRoot reward (actualizer.profiles rank)
        (actualizer.mark rank)) family.markedOwner = 0 := by
  exact family.descendant_markedOwnerDefect_eq_zero
    (actualizer.originRank rank) (actualizer.originRoots rank)

/-- Whole semantic debts of the actual profiles converge to the minimizer's
whole debt. -/
theorem wholeDebt_tendsto : Tendsto (fun rank =>
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (actualizer.profiles rank))) atTop
      (nhds point.wholeDebt) := by
  have hmap := QuittingMarkedPairDecoration.continuous_wholeDebt.tendsto point
    |>.comp actualizer.decorations_tendsto
  refine hmap.congr' ?_
  filter_upwards [] with rank
  simp only [Function.comp_apply, QuittingMarkedPairDecoration.wholeDebt,
    profiles]
  rw [family.rawDecoration_whole_eq]

/-- Marked post-date tail debts converge to the minimizer's tail debt. -/
theorem tailDebt_tendsto : Tendsto (fun rank =>
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (actualizer.profiles rank)
          (actualizer.mark rank + 1)))) atTop (nhds point.tailDebt) := by
  have hmap := QuittingMarkedPairDecoration.continuous_tailDebt.tendsto point
    |>.comp actualizer.decorations_tendsto
  refine hmap.congr' ?_
  filter_upwards [] with rank
  simp only [Function.comp_apply, QuittingMarkedPairDecoration.tailDebt,
    profiles, mark]
  rw [family.rawDecoration_tail_eq,
    family.descendant_postMarkSpine_eq]

/-- Canonical positive scale used by the existing concentrated-packet
consumer. -/
def scale (_actualizer : QuittingMarkedPairMinimumReturnActualizer
    family minimum massDensity gainDensity point) : ℕ → ℝ :=
  fun rank => 1 / ((rank : ℝ) + 1)

theorem scale_pos (rank : ℕ) : 0 < actualizer.scale rank := by
  simp only [scale]
  positivity

theorem scale_tendsto_zero : Tendsto actualizer.scale atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Cut off immediately after the actual marked date. -/
def cutoff : ℕ → ℕ := fun rank => actualizer.mark rank + 1

/-- The minimum-return actual rows form an actual concentrated packet. -/
def packet : QuittingReprojectionConcentratedPacket reward actualizer.profiles
    family.markedOwner family.terminal actualizer.cutoff actualizer.scale where
  resolution := actualizer.resolution
  resolution_pos := actualizer.resolution_pos
  subseq := id
  subseq_strictMono := strictMono_id
  mark := actualizer.mark
  mark_lt := by intro rank; simp [cutoff]
  stageMass := by
    intro rank
    simpa using actualizer.resolution_le_stageMass rank
  semanticPrefix := by
    intro rank
    exact positive_stageCoalitionMass_has_semanticPrefixIncidence reward
      (actualizer.profiles rank) (actualizer.mark rank) family.terminal
        (actualizer.resolution_pos.trans_le
          (actualizer.resolution_le_stageMass rank))
  defect_tendsto := by
    have hzero : (fun rank =>
        (quittingLiveMass reward (actualizer.profiles rank)
            (actualizer.mark rank) *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward
                (actualizer.profiles rank) (actualizer.mark rank + 1))).1
            (quittingProfileLiveRoot reward (actualizer.profiles rank)
              (actualizer.mark rank)) family.markedOwner) /
          actualizer.scale rank) = fun _ => 0 := by
      funext rank
      rw [actualizer.markedOwnerDefect_eq_zero rank, mul_zero, zero_div]
    simp only [id_eq]
    rw [hzero]
    exact tendsto_const_nhds

/-- Whole source debt tends to the global minimum in the equality arm. -/
theorem wholeDebt_tendsto_minimum
    (hreturn : point.wholeDebt = quittingTerminalSemanticDebtSum minimum) :
    Tendsto (fun rank => quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (actualizer.profiles rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum)) := by
  simpa only [hreturn] using actualizer.wholeDebt_tendsto

/-- Marked tail debt also tends to the same global minimum in the equality
arm. -/
theorem tailDebt_tendsto_minimum
    (htail : point.tailDebt = quittingTerminalSemanticDebtSum minimum) :
    Tendsto (fun rank => quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (actualizer.profiles rank)
          (actualizer.mark rank + 1)))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum)) := by
  simpa only [htail] using actualizer.tailDebt_tendsto

/-- The equality-arm packet reaches the existing three-role limit-chord
consumer.  Tail escape is impossible because the marked tail debt converges
to the same positive minimum while the packet resolution is fixed positive. -/
theorem nonempty_threeRoleLimitChord_of_minimumReturn
    [Nonempty ι]
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < family.terminal.val.card)
    (hreturn : point.wholeDebt = quittingTerminalSemanticDebtSum minimum)
    (htail : point.tailDebt = quittingTerminalSemanticDebtSum minimum) :
    ∃ mover recipient,
      Nonempty (ConcentratedCollisionFourRole.ThreeRoleLimitChord reward minimum
        family.markedOwner mover recipient actualizer.resolution) := by
  have hsourceDebt : Tendsto (fun rank =>
      quittingTerminalSemanticDebtSum
        (ConcentratedCollisionFourRole.source reward
          (ConcentratedCollisionFourRole.packetProfile actualizer.packet rank)))
      atTop (nhds (quittingTerminalSemanticDebtSum minimum)) := by
    simpa [ConcentratedCollisionFourRole.packetProfile,
      ConcentratedCollisionFourRole.source, packet] using
      actualizer.wholeDebt_tendsto_minimum hreturn
  have hdispatch :=
    ConcentratedCollisionFourRole.packet_tailEscapeFrequently_or_threeRoleLimitChord
      minimum actualizer.packet hminimumCarrier hminimum hminimum_pos hcollision
        actualizer.scale_pos actualizer.scale_tendsto_zero hsourceDebt
  rcases hdispatch with hescape | hchord
  · have htailDebt := actualizer.tailDebt_tendsto_minimum htail
    have hdiff : Tendsto (fun rank =>
        quittingTerminalSemanticDebtSum
            (ConcentratedCollisionFourRole.tail reward
              (ConcentratedCollisionFourRole.packetProfile actualizer.packet rank)
              (actualizer.packet.mark rank)) -
          quittingTerminalSemanticDebtSum minimum) atTop (nhds 0) := by
      have hsub := htailDebt.sub_const
        (quittingTerminalSemanticDebtSum minimum)
      simpa [ConcentratedCollisionFourRole.packetProfile,
        ConcentratedCollisionFourRole.tail, packet] using hsub
    have hthreshold : 0 <
        actualizer.resolution * quittingTerminalSemanticDebtSum minimum / 2 :=
      div_pos (mul_pos actualizer.resolution_pos hminimum_pos) (by norm_num)
    have hsmall : ∀ᶠ rank in atTop,
        ¬ ConcentratedCollisionFourRole.packetEscape minimum actualizer.packet
          rank := by
      filter_upwards [hdiff.eventually_lt_const hthreshold] with rank hlt
      exact not_le_of_gt hlt
    exact (not_frequently.mpr hsmall hescape).elim
  · exact hchord

end QuittingMarkedPairMinimumReturnActualizer

/-- Direct equality-arm compiler from supplied fixed-label decorated-family
data.  It constructs the actualizer and its concentrated packet internally,
then returns the existing three-role limit-chord consumer. -/
theorem exists_minimumReturnActualizer_and_threeRoleLimitChord
    [Nonempty ι]
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair ι)
    (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι)
    (hmassDensity : 0 < massDensity) (hgainDensity : 0 < gainDensity)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hpoint : point ∈
      family.normalizedPassportSlice minimum massDensity gainDensity)
    (hreturn : point.wholeDebt = quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < family.terminal.val.card) :
    ∃ actualizer : QuittingMarkedPairMinimumReturnActualizer
        family minimum massDensity gainDensity point,
      ∃ mover recipient,
        Nonempty (ConcentratedCollisionFourRole.ThreeRoleLimitChord reward
          minimum family.markedOwner mover recipient actualizer.resolution) := by
  obtain ⟨actualizer⟩ := nonempty_quittingMarkedPairMinimumReturnActualizer
    family minimum massDensity gainDensity point hmassDensity hgainDensity
      hminimum_pos hpoint hreturn
  refine ⟨actualizer, ?_⟩
  exact actualizer.nonempty_threeRoleLimitChord_of_minimumReturn
    hminimumCarrier hminimum hminimum_pos hcollision hreturn hpoint.2.1

end GameTheory
