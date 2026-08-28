/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.NormalizedReturn
import Research.Quitting.NormalizedPassportSingleDensityToll

/-!
# The actual Fin4 normalized-inert passport has one density

For the fixed singleton owner and fixed forced outsider, the actual
source-to-pair gain is exactly marked pair mass times one literal table gap.
The identity survives the common arbitrary prefixes and closed carrier, so
the normalized minimizer carries the generic single-density tent toll.

The strict-inert wrapper below retains the original packet, compact selection,
minimizer, and exact-root statement.  It does not consume the strict arm or
construct a terminal approximation or uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability
open QuittingSureSetOwnerRepair

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {producer : FinFourOwnerCompressedSingletonProducer source}
  {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairBase

/-- The exact table difference paid when the fixed outsider joins the fixed
singleton owner. -/
def forcedPairGap
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda) :
    ℝ :=
  quittingSetReward reward {producer.owner, base.forcedOwner} base.forcedOwner -
    quittingSetReward reward {producer.owner} base.forcedOwner

/-- The hard-residual terminal gap is a lower bound for the literal pair gap. -/
theorem terminalGap_le_forcedPairGap
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda) :
    source.residual.witness.terminalGap ≤ base.forcedPairGap := by
  unfold forcedPairGap
  linarith [base.terminalGap_join]

/-- The literal pair gap is positive. -/
theorem forcedPairGap_pos
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda) :
    0 < base.forcedPairGap :=
  source.residual.witness.terminalGap_pos.trans_le
    base.terminalGap_le_forcedPairGap

/-- At the pure singleton row, the forced outsider's coordinate defect is
exactly the literal singleton-to-pair table gap. -/
theorem forcedOwnerDefect_eq_forcedPairGap
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    quittingRootCoordinateNashDefect reward
        (base.forcedAdapter index).sourceTail.1
        (base.forcedAdapter index).sourceRoot base.forcedOwner =
      base.forcedPairGap := by
  let adapter := base.forcedAdapter index
  have hsourceRoot : adapter.sourceRoot =
      quittingPureSetRoot ({producer.owner} : Finset (Fin 4)) := by
    funext who
    simp only [QuittingStageAtomConcentratedPacketAdapter.sourceRoot,
      pureSingletonProfile,
      quittingProfileLiveRoot_literalPureRootProfile_self,
      producer.terminal_eq]
    simp [quittingPureSetRoot, quittingSetAction, quittingCoalitionAction]
  have herase :
      (({producer.owner} : Finset (Fin 4)).erase
        base.forcedOwner).Nonempty := by
    simp [base.forcedOwner_ne_owner]
  have hcontinue : quittingRootContinuePayoff reward adapter.sourceTail.1
        adapter.sourceRoot base.forcedOwner =
      quittingSetReward reward {producer.owner} base.forcedOwner := by
    rw [hsourceRoot,
      quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
        adapter.sourceTail.1 {producer.owner} base.forcedOwner herase]
    simp [base.forcedOwner_ne_owner]
  have hquit : quittingRootQuitPayoff reward adapter.sourceTail.1
        adapter.sourceRoot base.forcedOwner =
      quittingSetReward reward {producer.owner, base.forcedOwner}
        base.forcedOwner := by
    rw [hsourceRoot, quittingRootQuitPayoff_pureSetRoot_eq_insert]
    simp [Finset.pair_comm]
  have hfalse : (adapter.sourceRoot base.forcedOwner false).toReal = 1 := by
    rw [hsourceRoot]
    simp [quittingPureSetRoot, quittingSetAction,
      base.forcedOwner_ne_owner]
  have htrue : (adapter.sourceRoot base.forcedOwner true).toReal = 0 := by
    rw [hsourceRoot]
    simp [quittingPureSetRoot, quittingSetAction,
      base.forcedOwner_ne_owner]
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    hfalse, htrue, one_mul, zero_mul, add_zero]
  simp only [quittingRootEndpointDifference, hcontinue, hquit]
  change max base.forcedPairGap 0 = base.forcedPairGap
  rw [max_eq_left base.forcedPairGap_pos.le]

/-- Exact one-row identity: actual forced-owner gain is marked pair mass
times the fixed table gap. -/
theorem forcedOwnerGain_eq_forcedPairGap_mul_stageMass
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    base.forcedOwnerGain index =
      base.forcedPairGap *
        quittingStageCoalitionMass reward
          (base.forcedAdapter index).targetProfile
          (base.endpoint index).stage
          (base.forcedAdapter index).routedTerminal := by
  rw [forcedOwnerGain,
    (base.forcedAdapter index).sourceToTargetGain_eq_liveMass_mul_defect,
    base.forcedOwnerDefect_eq_forcedPairGap index]
  rw [show quittingLiveMass reward (base.pureSingletonProfile index)
      (base.endpoint index).stage =
        quittingLiveMass reward (base.crossTailProfile index)
          (base.endpoint index).stage by
    exact quittingLiveMass_literalPureRootProfile_eq reward
      (base.crossTailProfile index) (base.endpoint index).stage
        (quittingCoalitionAction source.atom.terminal.val)]
  rw [← base.forcedPair_stageMass_eq_liveMass index]
  ring

end FinFourOwnerCompressedMinimumReturnForcedPairBase

variable {returnSource :
  FinFourOwnerCompressedMinimumReturnForcedPairSource source}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda)

/-- Every actual supplied decoration has the same gain-to-mass table ratio. -/
theorem normalizedDecoratedFamily_base_actualGain_eq_gap_mul_markedMass
    (rank : ℕ) :
    (packet.normalizedDecoratedFamily.baseDecoration rank).actualGain =
      packet.base.forcedPairGap *
        (packet.normalizedDecoratedFamily.baseDecoration rank).markedMass := by
  change packet.base.forcedOwnerGain (packet.subsequence rank) =
    packet.base.forcedPairGap *
      quittingStageCoalitionMass reward (packet.movingProfiles rank)
        (packet.movingMark rank) packet.movingTerminal
  rw [show packet.movingTerminal =
      (packet.base.forcedAdapter
        (packet.subsequence rank)).routedTerminal by
    exact (packet.forcedTerminal_eq_movingTerminal rank).symm]
  exact packet.base.forcedOwnerGain_eq_forcedPairGap_mul_stageMass
    (packet.subsequence rank)

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

namespace FinFourNormalizedReturnSelection

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- The reindexed selected family retains the exact base-row identity. -/
theorem family_base_actualGain_eq_gap_mul_markedMass
    (selection : FinFourNormalizedReturnSelection packet) (rank : ℕ) :
    (selection.family.baseDecoration rank).actualGain =
      packet.base.forcedPairGap *
        (selection.family.baseDecoration rank).markedMass := by
  exact packet.normalizedDecoratedFamily_base_actualGain_eq_gap_mul_markedMass
    (selection.subsequence rank)

/-- The exact gain-to-mass identity on the full closed selected carrier. -/
theorem carrier_actualGain_eq_gap_mul_markedMass
    (selection : FinFourNormalizedReturnSelection packet)
    {point : QuittingMarkedPairDecoration (Fin 4)}
    (hpoint : point ∈ selection.family.prefixOrbitCarrier) :
    point.actualGain = packet.base.forcedPairGap * point.markedMass := by
  exact selection.family.actualGain_eq_gap_mul_markedMass_of_base
    packet.base.forcedPairGap selection.family_base_actualGain_eq_gap_mul_markedMass
      hpoint

/-- The compact passport limit obeys the same exact identity. -/
theorem limit_actualGain_eq_gap_mul_markedMass
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.limit.actualGain =
      packet.base.forcedPairGap * selection.limit.markedMass := by
  exact selection.carrier_actualGain_eq_gap_mul_markedMass
    selection.passport.limit_mem_prefixOrbitCarrier

/-- The two canonical densities collapse to one literal density. -/
theorem gainDensity_eq_forcedPairGap_mul_massDensity
    (selection : FinFourNormalizedReturnSelection packet) :
    selection.gainDensity =
      packet.base.forcedPairGap * selection.massDensity := by
  unfold gainDensity massDensity
  rw [selection.limit_actualGain_eq_gap_mul_markedMass]
  ring

end FinFourNormalizedReturnSelection

namespace FinFourNormalizedReturnThreeRoleOrStrictInert

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- Every actual normalized-return capstone carries the generic
single-density minimizer, independently of which outcome arm holds. -/
def singleDensityMinimizer
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    QuittingSingleDensityPassportMinimizer capstone.selection.family
      source.point.1 where
  gap := packet.base.forcedPairGap
  density := capstone.selection.massDensity
  gap_pos := packet.base.forcedPairGap_pos
  density_pos := capstone.selection.massDensity_pos
  point := capstone.point
  carrier_identity := fun candidate hcandidate ↦
    capstone.selection.carrier_actualGain_eq_gap_mul_markedMass hcandidate
  point_mem := by
    simpa only [capstone.selection.gainDensity_eq_forcedPairGap_mul_massDensity]
      using capstone.point_mem
  point_minimal := by
    intro candidate hcandidate
    apply capstone.point_minimal candidate
    simpa only [capstone.selection.gainDensity_eq_forcedPairGap_mul_massDensity]
      using hcandidate
  pointDebt_pos := source.minimumDebt_pos.trans_le capstone.minimum_le_point

@[simp] theorem singleDensityMinimizer_point
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    capstone.singleDensityMinimizer.point = capstone.point := rfl

/-- The generic arbitrary-root tent bound on the actual source-attached
normalized minimizer. -/
theorem rootDefect_ge_min_singleDensityTent
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet)
    (root : Fin 4 → PMF Bool) :
    min
        (capstone.point.wholeDebt * quittingRootAbsorptionMass root)
        (quittingStationaryContinueMass root *
            capstone.singleDensityMinimizer.slack /
          capstone.selection.massDensity) ≤
      quittingRootTotalNashDefect reward capstone.point.whole.1.2 root :=
  capstone.singleDensityMinimizer.rootDefect_ge_min_tent root

/-- Corrected actual local alternative: zero slack, or positive slack with
the linear toll on the displayed small-absorption ball. -/
theorem slack_eq_zero_or_positive_with_local_toll
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet) :
    capstone.singleDensityMinimizer.slack = 0 ∨
      (0 < capstone.singleDensityMinimizer.slack ∧
        ∀ root : Fin 4 → PMF Bool,
          quittingRootAbsorptionMass root ≤
              capstone.singleDensityMinimizer.slack /
                capstone.point.markedMass →
            capstone.point.wholeDebt * quittingRootAbsorptionMass root ≤
              quittingRootTotalNashDefect reward
                capstone.point.whole.1.2 root) :=
  capstone.singleDensityMinimizer.slack_eq_zero_or_positive_with_local_toll

/-- Canonical saturation gives the exact marked-mass, actual-gain, and debt
ratios relative to the selected forced-pair passport limit. -/
theorem saturation_ratio
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet)
    (hsaturation : capstone.singleDensityMinimizer.slack = 0) :
    capstone.point.markedMass / capstone.selection.limit.markedMass =
        capstone.point.actualGain / capstone.selection.limit.actualGain ∧
      capstone.point.actualGain / capstone.selection.limit.actualGain =
        capstone.point.wholeDebt /
          (2 * capstone.selection.limit.wholeDebt) := by
  exact capstone.singleDensityMinimizer.saturation_ratio
    capstone.selection.limit
      capstone.selection.passport.limit_mem_prefixOrbitCarrier
      capstone.selection.limit_wholeDebt_pos
      capstone.selection.limit_markedMass_pos rfl hsaturation

/-- Saturation loses at least half of the selected limit's marked mass. -/
theorem markedMass_le_half_limit_of_slack_eq_zero
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet)
    (hsaturation : capstone.singleDensityMinimizer.slack = 0) :
    capstone.point.markedMass ≤ capstone.selection.limit.markedMass / 2 := by
  have hlimitMem : capstone.selection.limit ∈
      capstone.selection.family.normalizedPassportSlice source.point.1
        capstone.selection.massDensity capstone.selection.gainDensity :=
    capstone.selection.passport.limit_mem_normalizedPassportSlice
      capstone.selection.massDensity capstone.selection.gainDensity
        capstone.selection.massDensity_mul_wholeDebt_lt
        capstone.selection.gainDensity_mul_wholeDebt_lt
  have hdebt := capstone.point_minimal capstone.selection.limit hlimitMem
  have hpointMass : capstone.point.markedMass =
      capstone.selection.massDensity * capstone.point.wholeDebt := by
    change capstone.point.markedMass -
      capstone.selection.massDensity * capstone.point.wholeDebt = 0
        at hsaturation
    linarith
  rw [hpointMass]
  calc
    capstone.selection.massDensity * capstone.point.wholeDebt ≤
        capstone.selection.massDensity * capstone.selection.limit.wholeDebt :=
      mul_le_mul_of_nonneg_left hdebt capstone.selection.massDensity_pos.le
    _ = capstone.selection.limit.markedMass / 2 := by
      unfold FinFourNormalizedReturnSelection.massDensity
      field_simp [ne_of_gt capstone.selection.limit_wholeDebt_pos]

/-- Saturation loses at least half of the selected limit's actual gain. -/
theorem actualGain_le_half_limit_of_slack_eq_zero
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet)
    (hsaturation : capstone.singleDensityMinimizer.slack = 0) :
    capstone.point.actualGain ≤ capstone.selection.limit.actualGain / 2 := by
  have hpointGain : capstone.point.actualGain =
      packet.base.forcedPairGap * capstone.point.markedMass :=
    capstone.selection.carrier_actualGain_eq_gap_mul_markedMass
      capstone.point_mem.1
  rw [hpointGain,
    capstone.selection.limit_actualGain_eq_gap_mul_markedMass,
    show packet.base.forcedPairGap * capstone.selection.limit.markedMass / 2 =
        packet.base.forcedPairGap *
          (capstone.selection.limit.markedMass / 2) by ring]
  exact mul_le_mul_of_nonneg_left
    (capstone.markedMass_le_half_limit_of_slack_eq_zero hsaturation)
    packet.base.forcedPairGap_pos.le

end FinFourNormalizedReturnThreeRoleOrStrictInert

/-- The actual strict normalized-inert arm together with its source-attached
single-density minimizer. -/
structure FinFourNormalizedStrictInertSingleDensityToll
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet
  minimum_lt_point :
    quittingTerminalSemanticDebtSum source.point.1 < capstone.point.wholeDebt
  exactRoot_iff_allContinue : ∀ root : Fin 4 → PMF Bool,
    IsεQuittingRootNash reward capstone.point.whole.1.2 0 root ↔
      root = (quittingAllContinueRoot : Fin 4 → PMF Bool)

namespace FinFourNormalizedStrictInertSingleDensityToll

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- The retained single-density passport minimizer. -/
def minimizer
    (strict : FinFourNormalizedStrictInertSingleDensityToll packet) :
    QuittingSingleDensityPassportMinimizer strict.capstone.selection.family
      source.point.1 :=
  strict.capstone.singleDensityMinimizer

/-- The strict arm retains the complete arbitrary-root tent bound. -/
theorem rootDefect_ge_min_tent
    (strict : FinFourNormalizedStrictInertSingleDensityToll packet)
    (root : Fin 4 → PMF Bool) :
    min
        (strict.capstone.point.wholeDebt * quittingRootAbsorptionMass root)
        (quittingStationaryContinueMass root * strict.minimizer.slack /
          strict.capstone.selection.massDensity) ≤
      quittingRootTotalNashDefect reward
        strict.capstone.point.whole.1.2 root :=
  strict.capstone.rootDefect_ge_min_singleDensityTent root

/-- The strict arm retains the corrected saturation-or-positive-toll
alternative without acquiring any terminal consumer. -/
theorem slack_eq_zero_or_positive_with_local_toll
    (strict : FinFourNormalizedStrictInertSingleDensityToll packet) :
    strict.minimizer.slack = 0 ∨
      (0 < strict.minimizer.slack ∧
        ∀ root : Fin 4 → PMF Bool,
          quittingRootAbsorptionMass root ≤
              strict.minimizer.slack /
                strict.capstone.point.markedMass →
            strict.capstone.point.wholeDebt * quittingRootAbsorptionMass root ≤
              quittingRootTotalNashDefect reward
                strict.capstone.point.whole.1.2 root) :=
  strict.capstone.slack_eq_zero_or_positive_with_local_toll

end FinFourNormalizedStrictInertSingleDensityToll

namespace FinFourNormalizedReturnThreeRoleOrStrictInert

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- Extract the stronger source-attached strict-inert object whenever the
stored normalized outcome is the strict arm. -/
theorem nonempty_strictInertSingleDensityToll_of_outcome
    (capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet)
    (hinert : quittingTerminalSemanticDebtSum source.point.1 <
        capstone.point.wholeDebt ∧
      ∀ root : Fin 4 → PMF Bool,
        IsεQuittingRootNash reward capstone.point.whole.1.2 0 root ↔
          root = (quittingAllContinueRoot : Fin 4 → PMF Bool)) :
    Nonempty (FinFourNormalizedStrictInertSingleDensityToll packet) :=
  ⟨{
    capstone := capstone
    minimum_lt_point := hinert.1
    exactRoot_iff_allContinue := hinert.2
  }⟩

end FinFourNormalizedReturnThreeRoleOrStrictInert

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- Actual source-facing refinement of the existing normalized capstone.  It
returns its minimum-debt actualizer or the strengthened strict-inert
single-density object; no extra certificate is supplied by the caller. -/
theorem nonempty_minimumReturnActualizer_or_strictInertSingleDensityToll
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    ( ∃ capstone : FinFourNormalizedReturnThreeRoleOrStrictInert packet,
        ∃ _actualizer : QuittingMarkedPairMinimumReturnActualizer
            capstone.selection.family source.point.1
              capstone.selection.massDensity capstone.selection.gainDensity
                capstone.point,
          capstone.point.wholeDebt =
            quittingTerminalSemanticDebtSum source.point.1) ∨
      Nonempty (FinFourNormalizedStrictInertSingleDensityToll packet) := by
  obtain ⟨capstone⟩ := packet.nonempty_normalizedReturnThreeRole_or_strictInert
  rcases capstone.outcome with hequality | hinert
  · left
    obtain ⟨actualizer, hdebt, _⟩ := hequality
    exact ⟨capstone, actualizer, hdebt⟩
  · exact Or.inr
      (capstone.nonempty_strictInertSingleDensityToll_of_outcome hinert)

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
