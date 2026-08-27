/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.Topology.FiniteLabelSubsequence
import Research.Quitting.ConcentratedSingleton.NonSingletonResidual
import Research.Quitting.FinFourProducerAtlas.StrongConcentratedPacketConsumer
import Research.Quitting.PureNonsingletonCollisionScreening
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PunishmentNormalAtomicCollisionHandoff
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StaticCycleChronologyBarrier
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSelfTailClosure

/-!
# Cofinal minimum-tail forced pairs on one Fin4 owner chronology

One owner-compressed chronology is fixed before the resolution and depth
quantifiers.  At cofinally increasing source ranks, its live roots through the
compressed singleton date are copied in front of the original near-minimum
reference profile.  The marked singleton is then pureified and the one
table-selected full-gap outsider is forced to Quit, producing the same literal
pair at every rank with the reference profile as its full post-date tail.

The final finite-label extraction fixes one paid endpoint player.  No target
profile is asserted near-minimal, and no cap--Nash certificate is transported
across the cross-tail restart or either horizontal one-date update.
-/

noncomputable section

namespace GameTheory

open Filter
open QuittingNonsingletonMinimumLawTransfer
open QuittingSureSetOwnerRepair

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-! ## A strictly cofinal endpoint selection -/

/-- An endpoint together with the depth at which it was requested. -/
abbrev FinFourOwnerCompressedEndpointSelection
    (producer : FinFourOwnerCompressedSingletonProducer source)
    (lambda : ℝ) :=
  Σ depth, FinFourOwnerCompressedSingletonEndpoint source
    producer.chronology producer.owner lambda depth

/-- Recursively request the next endpoint beyond the previously selected
source rank.  All choices use the producer's already fixed chronology. -/
noncomputable def finFourOwnerCompressedCofinalEndpoint
    (producer : FinFourOwnerCompressedSingletonProducer source)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda < source.point.2 (some source.atom.terminal)) :
    ℕ → FinFourOwnerCompressedEndpointSelection producer lambda
  | 0 => ⟨0, Classical.choice
      (producer.chronology.nonempty_ownerCompressedSingleton producer.owner
        producer.terminal_eq lambda hlambda_pos hlambda_lt 0)⟩
  | n + 1 =>
      let previous := finFourOwnerCompressedCofinalEndpoint producer lambda
        hlambda_pos hlambda_lt n
      let depth := previous.2.rank + 1
      ⟨depth, Classical.choice
        (producer.chronology.nonempty_ownerCompressedSingleton producer.owner
          producer.terminal_eq lambda hlambda_pos hlambda_lt depth)⟩

/-- The actual endpoint selected at one cofinal sequence index. -/
def finFourOwnerCompressedCofinalEndpointAt
    (producer : FinFourOwnerCompressedSingletonProducer source)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda < source.point.2 (some source.atom.terminal))
    (index : ℕ) :
    FinFourOwnerCompressedSingletonEndpoint source producer.chronology
      producer.owner lambda
        (finFourOwnerCompressedCofinalEndpoint producer lambda hlambda_pos
          hlambda_lt index).1 :=
  (finFourOwnerCompressedCofinalEndpoint producer lambda hlambda_pos
    hlambda_lt index).2

/-- The selected source ranks are strictly increasing, rather than merely
unbounded by their external request indices. -/
theorem strictMono_finFourOwnerCompressedCofinalEndpoint_rank
    (producer : FinFourOwnerCompressedSingletonProducer source)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda < source.point.2 (some source.atom.terminal)) :
    StrictMono (fun index ↦
      (finFourOwnerCompressedCofinalEndpointAt producer lambda hlambda_pos
        hlambda_lt index).rank) := by
  apply strictMono_nat_of_lt_succ
  intro index
  let previous := finFourOwnerCompressedCofinalEndpoint producer lambda
    hlambda_pos hlambda_lt index
  have hdepth :=
    (finFourOwnerCompressedCofinalEndpointAt producer lambda hlambda_pos
      hlambda_lt (index + 1)).requestedDepth_le_rank
  change previous.2.rank + 1 ≤
    (finFourOwnerCompressedCofinalEndpointAt producer lambda hlambda_pos
      hlambda_lt (index + 1)).rank at hdepth
  exact (Nat.lt_succ_self previous.2.rank).trans_le hdepth

/-! ## One cross-tail forced pair -/

/-- Data fixed before the cofinal endpoint and payer selections. -/
structure FinFourOwnerCompressedMinimumReturnForcedPairBase
    (producer : FinFourOwnerCompressedSingletonProducer source)
    (lambda : ℝ) where
  lambda_pos : 0 < lambda
  lambda_lt_terminalMass :
    lambda < source.point.2 (some source.atom.terminal)
  forcedOwner : Fin 4
  forcedOwner_ne_owner : forcedOwner ≠ producer.owner
  terminalGap_join :
    quittingSetReward reward {producer.owner} forcedOwner +
          source.residual.witness.terminalGap ≤
      quittingSetReward reward {producer.owner, forcedOwner} forcedOwner

namespace FinFourOwnerCompressedMinimumReturnForcedPairBase

variable
  {producer : FinFourOwnerCompressedSingletonProducer source}
  {lambda : ℝ}

/-- The cofinally selected compressed endpoint at one raw index. -/
def endpoint
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :=
  finFourOwnerCompressedCofinalEndpointAt producer lambda base.lambda_pos
    base.lambda_lt_terminalMass index

/-- The near-minimum reference profile at the endpoint's retained source
rank.  This is not the compressed target. -/
def referenceProfile
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) : (quittingGame reward).BehaviorProfile :=
  (base.endpoint index).referenceProfile

/-- Copy the compressed target's actual live roots through its marked date,
then restart the near-minimum reference profile. -/
def crossTailProfile
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingCrossTailClosure reward (base.endpoint index).targetProfile
    (base.referenceProfile index) (base.endpoint index).stage

/-- Simultaneously pureify the cross-tail marked row to the original minimum
singleton. -/
def pureSingletonProfile
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralPureRootProfile reward (base.crossTailProfile index)
    (base.endpoint index).stage
      (quittingCoalitionAction source.atom.terminal.val)

/-- The copied prefix preserves the endpoint's exact singleton atom. -/
theorem crossTail_singletonStageMass_eq
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    quittingStageCoalitionMass reward (base.crossTailProfile index)
        (base.endpoint index).stage source.atom.terminal =
      quittingStageCoalitionMass reward (base.endpoint index).targetProfile
        (base.endpoint index).stage source.atom.terminal := by
  exact quittingStageCoalitionMass_crossTailClosure reward
    (base.endpoint index).targetProfile (base.referenceProfile index)
      (base.endpoint index).stage source.atom.terminal

/-- Pureification assigns the complete reached mass to the singleton. -/
theorem pureSingleton_stageMass_eq_liveMass
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    quittingStageCoalitionMass reward (base.pureSingletonProfile index)
        (base.endpoint index).stage source.atom.terminal =
      quittingLiveMass reward (base.crossTailProfile index)
        (base.endpoint index).stage := by
  unfold pureSingletonProfile
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_literalPureRootProfile_eq,
    quittingProfileLiveRoot_literalPureRootProfile_self,
    quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]

/-- The requested arbitrary resolution survives both the cross-tail restart
and simultaneous singleton pureification. -/
theorem lambda_lt_pureSingletonStageMass
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    lambda < quittingStageCoalitionMass reward
      (base.pureSingletonProfile index) (base.endpoint index).stage
        source.atom.terminal := by
  rw [base.pureSingleton_stageMass_eq_liveMass]
  have hstage := (base.endpoint index).target_stageMass_gt
  rw [← base.crossTail_singletonStageMass_eq] at hstage
  exact hstage.trans_le
    (quittingStageCoalitionMass_le_liveMass reward
      (base.crossTailProfile index) (base.endpoint index).stage
        source.atom.terminal)

/-- The full post-date spine of the pure singleton is literally the selected
near-minimum reference profile. -/
theorem pureSingleton_postDateSpine_eq_reference
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    quittingAllContinueProfileSpine reward (base.pureSingletonProfile index)
        ((base.endpoint index).stage + 1) =
      base.referenceProfile index := by
  calc
    quittingAllContinueProfileSpine reward (base.pureSingletonProfile index)
          ((base.endpoint index).stage + 1) =
        quittingAllContinueProfileSpine reward (base.crossTailProfile index)
          ((base.endpoint index).stage + 1) := by
      apply quittingAllContinueProfileSpine_eq_of_eq_from
      intro who time history htime
      have hne : time ≠ (base.endpoint index).stage := by omega
      simp [pureSingletonProfile, quittingLiteralPureRootProfile,
        quittingLiteralOneDateOverride, hne]
    _ = base.referenceProfile index :=
      quittingAllContinueProfileSpine_crossTailClosure reward
        (base.endpoint index).targetProfile (base.referenceProfile index)
          (base.endpoint index).stage

/-- A forced-owner adapter exists at every selected raw index. -/
theorem nonempty_forcedAdapter
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    Nonempty (QuittingStageAtomConcentratedPacketAdapter reward
      (base.pureSingletonProfile index) source.atom.terminal base.forcedOwner
        (base.endpoint index).stage lambda) := by
  have hterminalNe : source.atom.terminal.val ≠ {base.forcedOwner} := by
    rw [producer.terminal_eq]
    exact fun heq ↦ base.forcedOwner_ne_owner
      (Finset.singleton_inj.mp heq).symm
  exact QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass
    (base.pureSingletonProfile index) source.atom.terminal base.forcedOwner
      (base.endpoint index).stage lambda hterminalNe base.lambda_pos
        (base.lambda_lt_pureSingletonStageMass index).le

/-- The selected forced-owner adapter. -/
theorem forcedAdapter
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    QuittingStageAtomConcentratedPacketAdapter reward
      (base.pureSingletonProfile index) source.atom.terminal base.forcedOwner
        (base.endpoint index).stage lambda :=
  Classical.choice (base.nonempty_forcedAdapter index)

/-- The forced comparison is screened by the sure singleton owner, so the
table gap makes Quit strictly optimal at every selected rank. -/
theorem forcedAction_eq_true
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    (base.forcedAdapter index).action = true := by
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
      (({producer.owner} : Finset (Fin 4)).erase base.forcedOwner).Nonempty := by
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
  have hstrict : quittingRootContinuePayoff reward adapter.sourceTail.1
        adapter.sourceRoot base.forcedOwner <
      quittingRootQuitPayoff reward adapter.sourceTail.1
        adapter.sourceRoot base.forcedOwner := by
    rw [hcontinue, hquit]
    linarith [source.residual.witness.terminalGap_pos,
      base.terminalGap_join]
  unfold QuittingStageAtomConcentratedPacketAdapter.action
    quittingRootBestEndpointAction
  simp [not_le.mpr hstrict]

/-- The routed terminal is the same literal pair at every rank. -/
theorem forcedTerminal_val
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    (base.forcedAdapter index).routedTerminal.val =
      {producer.owner, base.forcedOwner} := by
  rw [QuittingStageAtomConcentratedPacketAdapter.routedTerminal_val]
  simp only [QuittingStageAtomConcentratedPacketAdapter.routedCoalition,
    base.forcedAction_eq_true index,
    quittingPureEndpointRoutedCoalition_true, producer.terminal_eq]
  exact Finset.pair_comm _ _

/-- The forced pair is genuinely nonsingleton. -/
theorem forcedTerminal_card
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    (base.forcedAdapter index).routedTerminal.val.card = 2 := by
  rw [base.forcedTerminal_val]
  have hnot : producer.owner ∉ ({base.forcedOwner} : Finset (Fin 4)) := by
    simpa using base.forcedOwner_ne_owner.symm
  rw [Finset.card_insert_of_notMem hnot]
  simp

/-- The forced pair retains the entire reached live mass. -/
theorem forcedPair_stageMass_eq_liveMass
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    quittingStageCoalitionMass reward (base.forcedAdapter index).targetProfile
        (base.endpoint index).stage
        (base.forcedAdapter index).routedTerminal =
      quittingLiveMass reward (base.crossTailProfile index)
        (base.endpoint index).stage := by
  have hpair : (base.forcedAdapter index).targetProfile =
      quittingLiteralPureRootProfile reward (base.crossTailProfile index)
        (base.endpoint index).stage
          (quittingCoalitionAction
            (base.forcedAdapter index).routedTerminal.val) := by
    rw [QuittingStageAtomConcentratedPacketAdapter.targetProfile_eq_literalOneDateProfile]
    exact quittingLiteralPureRootProfile_update_eq_routed reward
      (base.crossTailProfile index) (base.endpoint index).stage
        source.atom.terminal.val base.forcedOwner
          (base.forcedAdapter index).action
            (base.forcedAdapter index).routedTerminal.val rfl
  rw [hpair, quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_literalPureRootProfile_eq,
    quittingProfileLiveRoot_literalPureRootProfile_self,
    quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]

/-- The fixed pair retains the requested resolution. -/
theorem lambda_lt_forcedPairStageMass
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    lambda < quittingStageCoalitionMass reward
      (base.forcedAdapter index).targetProfile (base.endpoint index).stage
        (base.forcedAdapter index).routedTerminal := by
  rw [base.forcedPair_stageMass_eq_liveMass]
  exact (base.lambda_lt_pureSingletonStageMass index).trans_eq
    (base.pureSingleton_stageMass_eq_liveMass index)

/-- The complete post-date spine of the forced pair is literally the
near-minimum reference profile. -/
theorem forcedPair_postDateSpine_eq_reference
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    quittingAllContinueProfileSpine reward
        (base.forcedAdapter index).targetProfile
        ((base.endpoint index).stage + 1) =
      base.referenceProfile index := by
  calc
    quittingAllContinueProfileSpine reward
          (base.forcedAdapter index).targetProfile
          ((base.endpoint index).stage + 1) =
        quittingAllContinueProfileSpine reward
          (base.pureSingletonProfile index)
          ((base.endpoint index).stage + 1) := by
      apply quittingAllContinueProfileSpine_eq_of_eq_from
      intro who time history htime
      have hne : time ≠ (base.endpoint index).stage := by omega
      exact congrFun
        ((base.forcedAdapter index).targetProfile_at_of_ne time hne who)
        history
    _ = base.referenceProfile index :=
      base.pureSingleton_postDateSpine_eq_reference index

/-- The forced owner's marked coordinate defect is exactly zero. -/
theorem forcedOwnerDefect_eq_zero
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    quittingRootCoordinateNashDefect reward
        (base.forcedAdapter index).targetTail.1
        (quittingProfileLiveRoot reward
          (base.forcedAdapter index).targetProfile
          (base.endpoint index).stage)
        base.forcedOwner = 0 :=
  (base.forcedAdapter index).ownerMarkedDefect_eq_zero

/-- The actual payoff gain of the table-selected forced owner. -/
def forcedOwnerGain
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) : ℝ :=
  (base.forcedAdapter index).sourceToTargetGain

/-- The source hard-residual gap lower-bounds the forced owner's defect at
the literal pure singleton row. -/
theorem terminalGap_le_forcedOwnerDefect
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    source.residual.witness.terminalGap ≤
      quittingRootCoordinateNashDefect reward
        (base.forcedAdapter index).sourceTail.1
        (base.forcedAdapter index).sourceRoot base.forcedOwner := by
  have hsourceRoot : (base.forcedAdapter index).sourceRoot =
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
  have hcontinue : quittingRootContinuePayoff reward
        (base.forcedAdapter index).sourceTail.1
        (base.forcedAdapter index).sourceRoot base.forcedOwner =
      quittingSetReward reward {producer.owner} base.forcedOwner := by
    rw [hsourceRoot,
      quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
        (base.forcedAdapter index).sourceTail.1 {producer.owner}
          base.forcedOwner herase]
    simp [base.forcedOwner_ne_owner]
  have hquit : quittingRootQuitPayoff reward
        (base.forcedAdapter index).sourceTail.1
        (base.forcedAdapter index).sourceRoot base.forcedOwner =
      quittingSetReward reward {producer.owner, base.forcedOwner}
        base.forcedOwner := by
    rw [hsourceRoot, quittingRootQuitPayoff_pureSetRoot_eq_insert]
    simp [Finset.pair_comm]
  have hfalse :
      ((base.forcedAdapter index).sourceRoot
        base.forcedOwner false).toReal = 1 := by
    rw [hsourceRoot]
    simp [quittingPureSetRoot, quittingSetAction,
      base.forcedOwner_ne_owner]
  have htrue :
      ((base.forcedAdapter index).sourceRoot
        base.forcedOwner true).toReal = 0 := by
    rw [hsourceRoot]
    simp [quittingPureSetRoot, quittingSetAction,
      base.forcedOwner_ne_owner]
  have hgapDifference : source.residual.witness.terminalGap ≤
      quittingRootEndpointDifference reward
        (base.forcedAdapter index).sourceTail.1
        (base.forcedAdapter index).sourceRoot base.forcedOwner := by
    simp only [quittingRootEndpointDifference, hcontinue, hquit]
    linarith [base.terminalGap_join]
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    hfalse, htrue, one_mul, zero_mul, add_zero,
    max_eq_left (source.residual.witness.terminalGap_pos.le.trans
      hgapDifference)]
  exact hgapDifference

/-- At every cofinal row the forced singleton-to-pair move gains at least
`lambda * terminalGap`. -/
theorem lambda_mul_terminalGap_le_forcedOwnerGain
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    lambda * source.residual.witness.terminalGap ≤
      base.forcedOwnerGain index := by
  exact (base.forcedAdapter index).sourceToTargetGain_lowerBound lambda
    source.residual.witness.terminalGap
      ((base.forcedAdapter index).resolution_le_sourceStageMass.trans
        (quittingStageCoalitionMass_le_liveMass reward
          (base.pureSingletonProfile index) (base.endpoint index).stage
            source.atom.terminal))
      source.residual.witness.terminalGap_pos.le
      (base.terminalGap_le_forcedOwnerDefect index)

/-- Reference total debts converge to the retained global minimum along the
strictly cofinal raw rank selection. -/
theorem tendsto_referenceDebt
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda) :
    Tendsto (fun index ↦ quittingTerminalDebtSum reward
      (base.referenceProfile index)) atTop
        (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
  have hraw := producer.chronology.prefix_debt_tendsto.comp
    (strictMono_finFourOwnerCompressedCofinalEndpoint_rank producer lambda
      base.lambda_pos base.lambda_lt_terminalMass).tendsto_atTop
  rw [← source.debt_eq_inf] at hraw
  change Tendsto
    ((fun rank ↦ quittingTerminalDebtSum reward
        (QuittingNonsingletonMinimumLawTransfer.prefixedProfile reward
          producer.chronology.profiles producer.chronology.roots rank)) ∘
      fun index ↦ (base.endpoint index).rank) atTop
        (nhds (quittingTerminalSemanticDebtSum source.point.1))
  exact hraw

/-- The stored post-date spine debt excess is exactly the reference debt
minus `D_*`, hence tends to zero. -/
theorem tendsto_forcedPairSpineDebtExcess_zero
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda) :
    Tendsto (fun index ↦ quittingSpineDebtExcess reward
      (base.forcedAdapter index).targetProfile
      (quittingTerminalSemanticDebtSum source.point.1)
      ((base.endpoint index).stage + 1)) atTop (nhds 0) := by
  have hconst : Tendsto
      (fun _ : ℕ ↦ quittingTerminalSemanticDebtSum source.point.1) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1)) :=
    tendsto_const_nhds
  have hdebt := base.tendsto_referenceDebt.sub hconst
  have heq :
      (fun index ↦ quittingSpineDebtExcess reward
        (base.forcedAdapter index).targetProfile
        (quittingTerminalSemanticDebtSum source.point.1)
        ((base.endpoint index).stage + 1)) =
      (fun index ↦ quittingTerminalDebtSum reward
          (base.referenceProfile index) -
        quittingTerminalSemanticDebtSum source.point.1) := by
    funext index
    unfold quittingSpineDebtExcess
    rw [base.forcedPair_postDateSpine_eq_reference]
    rw [quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
  rw [heq]
  simpa using hdebt

end FinFourOwnerCompressedMinimumReturnForcedPairBase

/-! ## A paid endpoint on every selected forced pair -/

/-- A direct positive-defect endpoint selected away from the forced owner at
one member of the cofinal forced-pair sequence. -/
structure FinFourOwnerCompressedMinimumReturnPaidRow
    {producer : FinFourOwnerCompressedSingletonProducer source}
    {lambda : ℝ}
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) where
  payer : Fin 4
  payer_ne_forcedOwner : payer ≠ base.forcedOwner
  payerAdapter : QuittingStageAtomConcentratedPacketAdapter reward
    (base.forcedAdapter index).targetProfile
    (base.forcedAdapter index).routedTerminal payer
    (base.endpoint index).stage lambda
  payerDefect_floor :
    quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      quittingRootCoordinateNashDefect reward payerAdapter.sourceTail.1
        payerAdapter.sourceRoot payer

namespace FinFourOwnerCompressedMinimumReturnForcedPairBase

variable
  {producer : FinFourOwnerCompressedSingletonProducer source}
  {lambda : ℝ}

/-- Every selected forced pair contains a coordinate away from the zero-defect
forced owner carrying at least one third of the minimum total debt. -/
theorem nonempty_paidRow
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    Nonempty (FinFourOwnerCompressedMinimumReturnPaidRow base index) := by
  have hforcedCard := base.forcedTerminal_card index
  let pairCoalition : QuittingNonsingletonCoalition (Fin 4) :=
    ⟨(base.forcedAdapter index).routedTerminal.val, by omega⟩
  have hpairProfile : (base.forcedAdapter index).targetProfile =
      quittingLiteralPureRootCoalitionProfile reward
        (base.crossTailProfile index) (base.endpoint index).stage
          pairCoalition := by
    simpa only [QuittingStageAtomConcentratedPacketAdapter.targetProfile,
      pureSingletonProfile, quittingLiteralOneDateProfile, pairCoalition,
      quittingLiteralPureRootCoalitionProfile,
      quittingPureRootOfCoalition] using
      quittingLiteralPureRootProfile_update_eq_routed reward
        (base.crossTailProfile index) (base.endpoint index).stage
          source.atom.terminal.val base.forcedOwner
            (base.forcedAdapter index).action
              (base.forcedAdapter index).routedTerminal.val rfl
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward
      (base.forcedAdapter index).targetProfile
        ((base.endpoint index).stage + 1))
  let root := quittingProfileLiveRoot reward
    (base.forcedAdapter index).targetProfile (base.endpoint index).stage
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward
      (base.forcedAdapter index).targetProfile (base.endpoint index).stage)
  have hcurrentCarrier : current ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have hminimumFloor : quittingTerminalSemanticDebtSum source.point.1 ≤
      quittingTerminalSemanticDebtSum current :=
    source.minimum current hcurrentCarrier
  have hsum : quittingTerminalSemanticDebtSum current =
      ∑ who, quittingRootCoordinateNashDefect reward tail.1 root who := by
    have hraw :=
      quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect
        reward (base.crossTailProfile index) (base.endpoint index).stage
          pairCoalition
    rw [← hpairProfile] at hraw
    simpa only [current, tail, root] using hraw
  have hforcedZero : quittingRootCoordinateNashDefect reward tail.1 root
      base.forcedOwner = 0 := by
    change quittingRootCoordinateNashDefect reward
        (base.forcedAdapter index).targetTail.1
        (quittingProfileLiveRoot reward
          (base.forcedAdapter index).targetProfile
            (base.endpoint index).stage) base.forcedOwner = 0
    exact base.forcedOwnerDefect_eq_zero index
  let others : Finset (Fin 4) := Finset.univ.erase base.forcedOwner
  have hothers : others.Nonempty := by
    exact ⟨producer.owner, Finset.mem_erase.mpr
      ⟨fun heq ↦ base.forcedOwner_ne_owner heq.symm,
        Finset.mem_univ producer.owner⟩⟩
  obtain ⟨payer, hpayerMem, haverage⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul others hothers
      (fun who ↦ quittingRootCoordinateNashDefect reward tail.1 root who)
  have hpayerNe : payer ≠ base.forcedOwner :=
    (Finset.mem_erase.mp hpayerMem).1
  have hsumOthers :
      ∑ who ∈ others,
          quittingRootCoordinateNashDefect reward tail.1 root who =
        ∑ who, quittingRootCoordinateNashDefect reward tail.1 root who := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun who ↦ quittingRootCoordinateNashDefect reward tail.1 root who)
        (Finset.mem_univ base.forcedOwner)]
    simp only [others, hforcedZero, add_zero]
  have haverage' :
      (∑ who, quittingRootCoordinateNashDefect reward tail.1 root who) ≤
        3 * quittingRootCoordinateNashDefect reward tail.1 root payer := by
    rw [← hsumOthers]
    simpa [others] using haverage
  have hpayerFloor : quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      quittingRootCoordinateNashDefect reward tail.1 root payer := by
    have htotal := hminimumFloor.trans (hsum.trans_le haverage')
    linarith
  have hpayerTerminal :
      (base.forcedAdapter index).routedTerminal.val ≠ {payer} := by
    intro heq
    have hone : (base.forcedAdapter index).routedTerminal.val.card = 1 := by
      rw [heq]
      simp
    omega
  obtain ⟨payerAdapter⟩ :=
    QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass
      (base.forcedAdapter index).targetProfile
        (base.forcedAdapter index).routedTerminal payer
          (base.endpoint index).stage lambda hpayerTerminal base.lambda_pos
            (base.lambda_lt_forcedPairStageMass index).le
  exact ⟨{
    payer := payer
    payer_ne_forcedOwner := hpayerNe
    payerAdapter := payerAdapter
    payerDefect_floor := by
      simpa only [QuittingStageAtomConcentratedPacketAdapter.sourceTail,
        QuittingStageAtomConcentratedPacketAdapter.sourceRoot, tail, root] using
        hpayerFloor
  }⟩

/-- One choice of paid row at a raw cofinal index.  The later finite-label
subsequence freezes the resulting chosen payer; no canonical choice is
asserted. -/
noncomputable def paidRow
    (base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda)
    (index : ℕ) :
    FinFourOwnerCompressedMinimumReturnPaidRow base index :=
  Classical.choice (base.nonempty_paidRow index)

end FinFourOwnerCompressedMinimumReturnForcedPairBase

namespace FinFourOwnerCompressedMinimumReturnPaidRow

variable
  {producer : FinFourOwnerCompressedSingletonProducer source}
  {lambda : ℝ}
  {base : FinFourOwnerCompressedMinimumReturnForcedPairBase producer lambda}
  {index : ℕ}

/-- The first adapter, with its original singleton owner and fixed forced
outsider, is a strong concentrated packet. -/
def strong (_row : FinFourOwnerCompressedMinimumReturnPaidRow base index) :
    FinFourSingletonStageStrongConcentratedPacket reward
      (base.pureSingletonProfile index) source.atom.terminal
        (base.endpoint index).stage lambda where
  singletonOwner := producer.owner
  sourceTerminal_eq := producer.terminal_eq
  packetOwner := base.forcedOwner
  packetOwner_ne_singletonOwner := base.forcedOwner_ne_owner
  adapter := base.forcedAdapter index

/-- The actual paid endpoint gain. -/
def payerGain
    (row : FinFourOwnerCompressedMinimumReturnPaidRow base index) : ℝ :=
  row.payerAdapter.sourceToTargetGain

/-- The actual paid endpoint has the direct `lambda * D_* / 3` floor. -/
theorem payerGain_floor
    (row : FinFourOwnerCompressedMinimumReturnPaidRow base index) :
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      row.payerGain := by
  have hlive : lambda ≤ quittingLiveMass reward
      (base.forcedAdapter index).targetProfile
        (base.endpoint index).stage :=
    row.payerAdapter.resolution_le_sourceStageMass.trans
      (quittingStageCoalitionMass_le_liveMass reward
        (base.forcedAdapter index).targetProfile
          (base.endpoint index).stage
            (base.forcedAdapter index).routedTerminal)
  have hnonneg : 0 ≤
      quittingTerminalSemanticDebtSum source.point.1 / 3 :=
    div_nonneg source.minimumDebt_pos.le (by norm_num)
  have hbound := row.payerAdapter.sourceToTargetGain_lowerBound lambda
    (quittingTerminalSemanticDebtSum source.point.1 / 3) hlive hnonneg
      row.payerDefect_floor
  simpa only [payerGain] using (show
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      row.payerAdapter.sourceToTargetGain by
        calc
          lambda * quittingTerminalSemanticDebtSum source.point.1 / 3 =
              lambda *
                (quittingTerminalSemanticDebtSum source.point.1 / 3) := by ring
          _ ≤ row.payerAdapter.sourceToTargetGain := hbound)

/-- The direct paid endpoint gain is positive at every selected row. -/
theorem payerGain_pos
    (row : FinFourOwnerCompressedMinimumReturnPaidRow base index) :
    0 < row.payerGain := by
  have hfloor : 0 <
      lambda * quittingTerminalSemanticDebtSum source.point.1 / 3 :=
    div_pos (mul_pos base.lambda_pos source.minimumDebt_pos) (by norm_num)
  exact hfloor.trans_le row.payerGain_floor

/-- The payer's unrestricted terminal debt decreases by exactly its gain. -/
theorem payerTargetDebt_eq_sourceDebt_sub_gain
    (row : FinFourOwnerCompressedMinimumReturnPaidRow base index) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward row.payerAdapter.targetProfile)
        row.payer =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (base.forcedAdapter index).targetProfile) row.payer -
        row.payerGain :=
  row.payerAdapter.targetOwnerDebt_eq_sourceOwnerDebt_sub_gain

/-- The paid target is a literal pure routed coalition over the same
cross-tail profile. -/
theorem payerTargetProfile_eq_pureRouted
    (row : FinFourOwnerCompressedMinimumReturnPaidRow base index) :
    row.payerAdapter.targetProfile =
      quittingLiteralPureRootProfile reward (base.crossTailProfile index)
        (base.endpoint index).stage
          (quittingCoalitionAction row.payerAdapter.routedTerminal.val) := by
  calc
    row.payerAdapter.targetProfile =
        quittingLiteralOneDateProfile reward
          (base.forcedAdapter index).targetProfile row.payer
            (base.endpoint index).stage row.payerAdapter.action := rfl
    _ = quittingLiteralOneDateProfile reward
          (quittingLiteralPureRootProfile reward
            (base.crossTailProfile index) (base.endpoint index).stage
              (quittingCoalitionAction
                (base.forcedAdapter index).routedTerminal.val))
          row.payer (base.endpoint index).stage
            row.payerAdapter.action := by
      apply congrArg (fun profile ↦ quittingLiteralOneDateProfile reward
        profile row.payer (base.endpoint index).stage row.payerAdapter.action)
      rw [QuittingStageAtomConcentratedPacketAdapter.targetProfile_eq_literalOneDateProfile]
      exact quittingLiteralPureRootProfile_update_eq_routed reward
        (base.crossTailProfile index) (base.endpoint index).stage
          source.atom.terminal.val base.forcedOwner
            (base.forcedAdapter index).action
              (base.forcedAdapter index).routedTerminal.val rfl
    _ = quittingLiteralPureRootProfile reward (base.crossTailProfile index)
          (base.endpoint index).stage
            (quittingCoalitionAction row.payerAdapter.routedTerminal.val) := by
      simpa only [quittingLiteralOneDateProfile] using
        quittingLiteralPureRootProfile_update_eq_routed reward
          (base.crossTailProfile index) (base.endpoint index).stage
            (base.forcedAdapter index).routedTerminal.val row.payer
              row.payerAdapter.action row.payerAdapter.routedTerminal.val rfl

/-- The paid endpoint routes exactly the complete forced-pair marked mass. -/
theorem payerRoutedStageMass_eq_forcedPairStageMass
    (row : FinFourOwnerCompressedMinimumReturnPaidRow base index) :
    quittingStageCoalitionMass reward row.payerAdapter.targetProfile
        (base.endpoint index).stage row.payerAdapter.routedTerminal =
      quittingStageCoalitionMass reward
        (base.forcedAdapter index).targetProfile
          (base.endpoint index).stage
            (base.forcedAdapter index).routedTerminal := by
  calc
    quittingStageCoalitionMass reward row.payerAdapter.targetProfile
          (base.endpoint index).stage row.payerAdapter.routedTerminal =
        quittingLiveMass reward (base.crossTailProfile index)
          (base.endpoint index).stage := by
      rw [row.payerTargetProfile_eq_pureRouted,
        quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
        quittingLiveMass_literalPureRootProfile_eq,
        quittingProfileLiveRoot_literalPureRootProfile_self,
        quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]
    _ = quittingStageCoalitionMass reward
          (base.forcedAdapter index).targetProfile
            (base.endpoint index).stage
              (base.forcedAdapter index).routedTerminal :=
      (base.forcedPair_stageMass_eq_liveMass index).symm

/-- The paid target retains the complete near-minimum post-date spine. -/
theorem payerTarget_postDateSpine_eq_reference
    (row : FinFourOwnerCompressedMinimumReturnPaidRow base index) :
    quittingAllContinueProfileSpine reward row.payerAdapter.targetProfile
        ((base.endpoint index).stage + 1) =
      base.referenceProfile index := by
  calc
    quittingAllContinueProfileSpine reward row.payerAdapter.targetProfile
          ((base.endpoint index).stage + 1) =
        quittingAllContinueProfileSpine reward
          (base.forcedAdapter index).targetProfile
            ((base.endpoint index).stage + 1) := by
      apply quittingAllContinueProfileSpine_eq_of_eq_from
      intro who time history htime
      have hne : time ≠ (base.endpoint index).stage := by omega
      exact congrFun (row.payerAdapter.targetProfile_at_of_ne time hne who)
        history
    _ = base.referenceProfile index :=
      base.forcedPair_postDateSpine_eq_reference index

/-- Since the first forced action is Quit, its existing collision consumer
produces a collision-minimum residual without an extra certificate input. -/
theorem nonempty_collisionMinimumResidual
    (row : FinFourOwnerCompressedMinimumReturnPaidRow base index) :
    Nonempty (QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 base.forcedOwner
        (base.forcedAdapter index).routedTerminal
          (base.forcedAdapter index).packet) :=
  row.strong.collisionMinimumResidual_of_action_eq_true
    (base.forcedAction_eq_true index)

end FinFourOwnerCompressedMinimumReturnPaidRow

/-! ## Freeze the table outsider, chronology, and paid player -/

/-- A chronology and table-selected full-gap outsider fixed before the
resolution parameter. -/
structure FinFourOwnerCompressedMinimumReturnForcedPairSource
    (source : FinFourMinimumAtomProducer reward bound) where
  producer : FinFourOwnerCompressedSingletonProducer source
  forcedOwner : Fin 4
  forcedOwner_ne_owner : forcedOwner ≠ producer.owner
  terminalGap_join :
    quittingSetReward reward {producer.owner} forcedOwner +
          source.residual.witness.terminalGap ≤
      quittingSetReward reward {producer.owner, forcedOwner} forcedOwner

namespace FinFourOwnerCompressedMinimumReturnForcedPairSource

variable {source : FinFourMinimumAtomProducer reward bound}

/-- Specialize the fixed source chronology and outsider at one admissible
resolution, without making another semantic or table selection. -/
def base
    (returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda < source.point.2 (some source.atom.terminal)) :
    FinFourOwnerCompressedMinimumReturnForcedPairBase
      returnSource.producer lambda where
  lambda_pos := hlambda_pos
  lambda_lt_terminalMass := hlambda_lt
  forcedOwner := returnSource.forcedOwner
  forcedOwner_ne_owner := returnSource.forcedOwner_ne_owner
  terminalGap_join := returnSource.terminalGap_join

end FinFourOwnerCompressedMinimumReturnForcedPairSource

/-- At one admissible resolution, a strict subsequence of the source's
cofinal ranks on which one payer label is fixed. -/
structure FinFourOwnerCompressedMinimumReturnForcedPairPacket
    {source : FinFourMinimumAtomProducer reward bound}
    (returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source)
    (lambda : ℝ) where
  lambda_pos : 0 < lambda
  lambda_lt_terminalMass :
    lambda < source.point.2 (some source.atom.terminal)
  payer : Fin 4
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  payer_eq : ∀ index,
    ((returnSource.base lambda lambda_pos lambda_lt_terminalMass).paidRow
      (subsequence index)).payer = payer

private theorem exists_fixed_finFour_strictMono_subsequence
    (label : ℕ → Fin 4) :
    ∃ fixed : Fin 4, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        ∀ index, label (subsequence index) = fixed := by
  have hfrequent : ∃ fixed : Fin 4, ∃ᶠ index in atTop,
      label index = fixed := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ᶠ index in atTop, ∀ fixed : Fin 4,
        label index ≠ fixed := by
      rw [eventually_all]
      exact hnot
    obtain ⟨index, hindex⟩ := hall.exists
    exact hindex (label index) rfl
  obtain ⟨fixed, hfixed⟩ := hfrequent
  obtain ⟨subsequence, hsubsequence, hlabel⟩ :=
    extraction_of_frequently_atTop hfixed
  exact ⟨fixed, subsequence, hsubsequence, hlabel⟩

namespace FinFourOwnerCompressedMinimumReturnForcedPairSource

variable {source : FinFourMinimumAtomProducer reward bound}

/-- For every resolution chosen after this source object, freeze one paid
player along a further strict subsequence. -/
theorem nonempty_packet
    (returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda < source.point.2 (some source.atom.terminal)) :
    Nonempty (FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) := by
  let base := returnSource.base lambda hlambda_pos hlambda_lt
  obtain ⟨payer, subsequence, hsubsequence, hpayer⟩ :=
    exists_fixed_finFour_strictMono_subsequence
      (fun index ↦ (base.paidRow index).payer)
  exact ⟨{
    lambda_pos := hlambda_pos
    lambda_lt_terminalMass := hlambda_lt
    payer := payer
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    payer_eq := hpayer
  }⟩

end FinFourOwnerCompressedMinimumReturnForcedPairSource

namespace FinFourMinimumAtomProducer

/-- A singleton minimum atom fixes one chronology and one table outsider
before any later resolution or depth selection. -/
theorem nonempty_minimumReturnForcedPairSource
    (source : FinFourMinimumAtomProducer reward bound)
    (terminal_card : source.atom.terminal.val.card = 1) :
    Nonempty (FinFourOwnerCompressedMinimumReturnForcedPairSource source) := by
  obtain ⟨producer⟩ :=
    source.nonempty_ownerCompressedSingletonProducer terminal_card
  obtain ⟨forcedOwner, hforcedNe, hgap⟩ :=
    source.residual.exists_terminalGap_collision_at_singleton producer.owner
  exact ⟨{
    producer := producer
    forcedOwner := forcedOwner
    forcedOwner_ne_owner := hforcedNe
    terminalGap_join := hgap
  }⟩

/-- Literal quantifier order: select the source chronology and outsider once,
then serve every admissible resolution with a fixed-payer cofinal packet. -/
theorem exists_minimumReturnForcedPairSource_for_all_resolutions
    (source : FinFourMinimumAtomProducer reward bound)
    (terminal_card : source.atom.terminal.val.card = 1) :
    ∃ returnSource :
        FinFourOwnerCompressedMinimumReturnForcedPairSource source,
      ∀ lambda, 0 < lambda →
        lambda < source.point.2 (some source.atom.terminal) →
          Nonempty (FinFourOwnerCompressedMinimumReturnForcedPairPacket
            returnSource lambda) := by
  obtain ⟨returnSource⟩ :=
    source.nonempty_minimumReturnForcedPairSource terminal_card
  exact ⟨returnSource, returnSource.nonempty_packet⟩

end FinFourMinimumAtomProducer

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable
  {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}

/-- The fixed-resolution base, definitionally using the source object's
already selected chronology and outsider. -/
def base
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    FinFourOwnerCompressedMinimumReturnForcedPairBase
      returnSource.producer lambda :=
  returnSource.base lambda packet.lambda_pos packet.lambda_lt_terminalMass

/-- The paid row at one index of the frozen-player subsequence. -/
def row
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    FinFourOwnerCompressedMinimumReturnPaidRow packet.base
      (packet.subsequence index) :=
  packet.base.paidRow (packet.subsequence index)

/-- The source rank actually used by one final packet row. -/
def selectedRank
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) : ℕ :=
  (packet.base.endpoint (packet.subsequence index)).rank

/-- Final source ranks remain strictly increasing after freezing the payer. -/
theorem selectedRank_strictMono
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    StrictMono packet.selectedRank := by
  exact (strictMono_finFourOwnerCompressedCofinalEndpoint_rank
    returnSource.producer lambda packet.lambda_pos
      packet.lambda_lt_terminalMass).comp packet.subsequence_strictMono

/-- The final sequence's near-minimum reference debts still converge to the
same original `D_*`. -/
theorem referenceDebt_tendsto
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Tendsto (fun index ↦ quittingTerminalDebtSum reward
      (packet.base.referenceProfile (packet.subsequence index))) atTop
        (nhds (quittingTerminalSemanticDebtSum source.point.1)) :=
  packet.base.tendsto_referenceDebt.comp
    packet.subsequence_strictMono.tendsto_atTop

/-- The forced pair's exact post-date spine debt excess tends to zero along
the frozen-player subsequence. -/
theorem forcedPairSpineDebtExcess_tendsto_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Tendsto (fun index ↦ quittingSpineDebtExcess reward
      (packet.base.forcedAdapter (packet.subsequence index)).targetProfile
      (quittingTerminalSemanticDebtSum source.point.1)
      ((packet.base.endpoint (packet.subsequence index)).stage + 1))
        atTop (nhds 0) :=
  packet.base.tendsto_forcedPairSpineDebtExcess_zero.comp
    packet.subsequence_strictMono.tendsto_atTop

/-- One payer label is literally fixed along the final subsequence. -/
theorem row_payer_eq
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.row index).payer = packet.payer :=
  packet.payer_eq index

/-- The fixed payer differs from the source object's fixed forced owner. -/
theorem payer_ne_forcedOwner
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    packet.payer ≠ returnSource.forcedOwner := by
  have hne := (packet.row 0).payer_ne_forcedOwner
  rw [packet.row_payer_eq 0] at hne
  simpa only [base,
    FinFourOwnerCompressedMinimumReturnForcedPairSource.base] using hne

/-- Every row has the same literal forced pair selected before `lambda`. -/
theorem forcedTerminal_val
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.base.forcedAdapter (packet.subsequence index)).routedTerminal.val =
      {returnSource.producer.owner, returnSource.forcedOwner} :=
  packet.base.forcedTerminal_val (packet.subsequence index)

/-- Every forced terminal is genuinely a pair. -/
theorem forcedTerminal_card
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.base.forcedAdapter
      (packet.subsequence index)).routedTerminal.val.card = 2 :=
  packet.base.forcedTerminal_card (packet.subsequence index)

/-- The fixed outsider's actual best endpoint is Quit at every selected row. -/
theorem forcedAction_eq_true
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.base.forcedAdapter
      (packet.subsequence index)).action = true :=
  packet.base.forcedAction_eq_true (packet.subsequence index)

/-- The forced owner's coordinate defect is zero at every selected pair. -/
theorem forcedOwnerDefect_eq_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingRootCoordinateNashDefect reward
        (packet.base.forcedAdapter
          (packet.subsequence index)).targetTail.1
        (quittingProfileLiveRoot reward
          (packet.base.forcedAdapter
            (packet.subsequence index)).targetProfile
          (packet.base.endpoint (packet.subsequence index)).stage)
        returnSource.forcedOwner = 0 :=
  packet.base.forcedOwnerDefect_eq_zero (packet.subsequence index)

/-- Every admissible resolution is strictly below one because it is below a
coordinate of the retained terminal probability law. -/
theorem lambda_lt_one
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    lambda < 1 := by
  have hsimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
    source.point source.point_mem
  have hmassLeOne : source.point.2 (some source.atom.terminal) ≤ 1 := by
    have hle : source.point.2 (some source.atom.terminal) ≤
        ∑ outcome, source.point.2 outcome :=
      Finset.single_le_sum (fun outcome _ ↦ hsimplex.1 outcome)
        (Finset.mem_univ _)
    simpa only [hsimplex.2] using hle
  exact packet.lambda_lt_terminalMass.trans_le hmassLeOne

/-- The fixed outsider's first move retains the full table-gap gain floor. -/
theorem lambda_mul_terminalGap_le_forcedOwnerGain
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    lambda * source.residual.witness.terminalGap ≤
      packet.base.forcedOwnerGain (packet.subsequence index) :=
  packet.base.lambda_mul_terminalGap_le_forcedOwnerGain
    (packet.subsequence index)

/-- The fixed payer carries the headline `D_* / 3` defect at every final
row. -/
theorem payerDefect_floor
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      quittingRootCoordinateNashDefect reward
        (packet.row index).payerAdapter.sourceTail.1
        (packet.row index).payerAdapter.sourceRoot packet.payer := by
  rw [← packet.row_payer_eq index]
  exact (packet.row index).payerDefect_floor

/-- Verbatim weaker packet floor: `lambda * D_* / 6`. -/
theorem lambda_mul_minimumDebt_div_six_le_payerDefect
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
      quittingRootCoordinateNashDefect reward
        (packet.row index).payerAdapter.sourceTail.1
        (packet.row index).payerAdapter.sourceRoot packet.payer := by
  have hlambda : lambda ≤ 1 := packet.lambda_lt_one.le
  have hdebt : 0 ≤ quittingTerminalSemanticDebtSum source.point.1 :=
    source.minimumDebt_pos.le
  have hmul : lambda * quittingTerminalSemanticDebtSum source.point.1 ≤
      quittingTerminalSemanticDebtSum source.point.1 := by
    exact mul_le_of_le_one_left hdebt hlambda
  exact (by
    calc
      lambda * quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
          quittingTerminalSemanticDebtSum source.point.1 / 3 := by linarith
      _ ≤ _ := packet.payerDefect_floor index)

/-- The fixed payer's actual gain has the headline `lambda * D_* / 3`
floor. -/
theorem payerGain_floor
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
      (packet.row index).payerGain :=
  (packet.row index).payerGain_floor

/-- Verbatim weaker gain floor `lambda * D_* / 6`. -/
theorem lambda_mul_minimumDebt_div_six_le_payerGain
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
      (packet.row index).payerGain :=
  (by linarith [packet.payerGain_floor index,
      mul_pos packet.lambda_pos source.minimumDebt_pos] :
    lambda * quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
      (packet.row index).payerGain)

/-- Verbatim weaker gain floor `lambda^2 * D_* / 6`. -/
theorem lambda_sq_mul_minimumDebt_div_six_le_payerGain
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    lambda ^ 2 * quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
      (packet.row index).payerGain := by
  have hlambda : lambda ≤ 1 := packet.lambda_lt_one.le
  have hsquare : lambda ^ 2 ≤ lambda := by
    nlinarith [mul_nonneg packet.lambda_pos.le (sub_nonneg.mpr hlambda)]
  have hdebt : 0 ≤ quittingTerminalSemanticDebtSum source.point.1 :=
    source.minimumDebt_pos.le
  have hscaled := mul_le_mul_of_nonneg_right hsquare hdebt
  calc
    lambda ^ 2 * quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
        lambda * quittingTerminalSemanticDebtSum source.point.1 / 6 := by
      linarith
    _ ≤ (packet.row index).payerGain :=
      packet.lambda_mul_minimumDebt_div_six_le_payerGain index

/-- The fixed payer's gain is positive on every final row. -/
theorem payerGain_pos
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    0 < (packet.row index).payerGain :=
  (packet.row index).payerGain_pos

/-- The fixed payer's unrestricted debt decreases by exactly its actual
gain on every row. -/
theorem payerTargetDebt_eq_sourceDebt_sub_gain
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.row index).payerAdapter.targetProfile) packet.payer =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (packet.base.forcedAdapter
              (packet.subsequence index)).targetProfile) packet.payer -
        (packet.row index).payerGain := by
  rw [← packet.row_payer_eq index]
  exact (packet.row index).payerTargetDebt_eq_sourceDebt_sub_gain

/-- The payer routes exactly the forced pair's complete marked mass. -/
theorem payerRoutedStageMass_eq_forcedPairStageMass
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingStageCoalitionMass reward
        (packet.row index).payerAdapter.targetProfile
        (packet.base.endpoint (packet.subsequence index)).stage
        (packet.row index).payerAdapter.routedTerminal =
      quittingStageCoalitionMass reward
        (packet.base.forcedAdapter
          (packet.subsequence index)).targetProfile
        (packet.base.endpoint (packet.subsequence index)).stage
        (packet.base.forcedAdapter
          (packet.subsequence index)).routedTerminal :=
  (packet.row index).payerRoutedStageMass_eq_forcedPairStageMass

/-- The forced pair has the full selected near-minimum profile as its exact
post-date spine. -/
theorem forcedPair_postDateSpine_eq_reference
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingAllContinueProfileSpine reward
        (packet.base.forcedAdapter
          (packet.subsequence index)).targetProfile
        ((packet.base.endpoint (packet.subsequence index)).stage + 1) =
      packet.base.referenceProfile (packet.subsequence index) :=
  packet.base.forcedPair_postDateSpine_eq_reference
    (packet.subsequence index)

/-- The paid endpoint retains the same complete near-minimum post-date
spine. -/
theorem payerTarget_postDateSpine_eq_reference
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingAllContinueProfileSpine reward
        (packet.row index).payerAdapter.targetProfile
        ((packet.base.endpoint (packet.subsequence index)).stage + 1) =
      packet.base.referenceProfile (packet.subsequence index) :=
  (packet.row index).payerTarget_postDateSpine_eq_reference

/-- The forced target's named semantic tail is exactly the selected reference
profile's semantic pair. -/
theorem forcedTargetTail_eq_referenceSemantic
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.base.forcedAdapter
      (packet.subsequence index)).targetTail =
      quittingTerminalSemanticPair reward
        (packet.base.referenceProfile (packet.subsequence index)) := by
  unfold QuittingStageAtomConcentratedPacketAdapter.targetTail
  exact congrArg (quittingTerminalSemanticPair reward)
    (packet.forcedPair_postDateSpine_eq_reference index)

/-- Consequently the forced target tail has exactly the selected reference
profile's total debt. -/
theorem forcedTargetTailDebtSum_eq_referenceDebt
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticDebtSum
        (packet.base.forcedAdapter
          (packet.subsequence index)).targetTail =
      quittingTerminalDebtSum reward
        (packet.base.referenceProfile (packet.subsequence index)) := by
  rw [packet.forcedTargetTail_eq_referenceSemantic,
    quittingTerminalDebtSum_eq_terminalSemanticDebtSum]

/-- The paid target has the same named semantic tail. -/
theorem payerTargetTail_eq_referenceSemantic
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.row index).payerAdapter.targetTail =
      quittingTerminalSemanticPair reward
        (packet.base.referenceProfile (packet.subsequence index)) := by
  unfold QuittingStageAtomConcentratedPacketAdapter.targetTail
  exact congrArg (quittingTerminalSemanticPair reward)
    (packet.payerTarget_postDateSpine_eq_reference index)

/-- Consequently the paid target tail has exactly the selected reference
profile's total debt. -/
theorem payerTargetTailDebtSum_eq_referenceDebt
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticDebtSum
        (packet.row index).payerAdapter.targetTail =
      quittingTerminalDebtSum reward
        (packet.base.referenceProfile (packet.subsequence index)) := by
  rw [packet.payerTargetTail_eq_referenceSemantic,
    quittingTerminalDebtSum_eq_terminalSemanticDebtSum]

/-- The original arbitrary resolution remains strictly below the forced
pair's marked mass. -/
theorem lambda_lt_forcedPairStageMass
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    lambda < quittingStageCoalitionMass reward
      (packet.base.forcedAdapter
        (packet.subsequence index)).targetProfile
      (packet.base.endpoint (packet.subsequence index)).stage
      (packet.base.forcedAdapter
        (packet.subsequence index)).routedTerminal :=
  packet.base.lambda_lt_forcedPairStageMass (packet.subsequence index)

/-- The forced pair carries exactly the complete live mass of its copied
prefix, rather than merely the requested lower bound. -/
theorem forcedPair_stageMass_eq_liveMass
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingStageCoalitionMass reward
        (packet.base.forcedAdapter
          (packet.subsequence index)).targetProfile
        (packet.base.endpoint (packet.subsequence index)).stage
        (packet.base.forcedAdapter
          (packet.subsequence index)).routedTerminal =
      quittingLiveMass reward
        (packet.base.crossTailProfile (packet.subsequence index))
        (packet.base.endpoint (packet.subsequence index)).stage :=
  packet.base.forcedPair_stageMass_eq_liveMass (packet.subsequence index)

/-- The paid routed coalition retains that same complete copied-prefix live
mass exactly. -/
theorem payerRoutedStageMass_eq_liveMass
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingStageCoalitionMass reward
        (packet.row index).payerAdapter.targetProfile
        (packet.base.endpoint (packet.subsequence index)).stage
        (packet.row index).payerAdapter.routedTerminal =
      quittingLiveMass reward
        (packet.base.crossTailProfile (packet.subsequence index))
        (packet.base.endpoint (packet.subsequence index)).stage := by
  rw [packet.payerRoutedStageMass_eq_forcedPairStageMass,
    packet.forcedPair_stageMass_eq_liveMass]

/-! ## One moving concentrated packet -/

/-- The fixed literal pair terminal selected before the resolution. -/
def movingTerminal
  (_packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨{returnSource.producer.owner, returnSource.forcedOwner}, by
    simp⟩

/-- Every row's dependently constructed routed terminal is the one fixed
terminal of the moving packet. -/
theorem forcedTerminal_eq_movingTerminal
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.base.forcedAdapter
      (packet.subsequence index)).routedTerminal = packet.movingTerminal := by
  apply Subtype.ext
  exact packet.forcedTerminal_val index

/-- The actual varying forced-pair profiles. -/
def movingProfiles
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    ℕ → (quittingGame reward).BehaviorProfile :=
  fun index ↦
    (packet.base.forcedAdapter (packet.subsequence index)).targetProfile

/-- The first cutoff immediately after each actual marked date. -/
def movingCutoff
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : ℕ → ℕ :=
  fun index ↦
    (packet.base.endpoint (packet.subsequence index)).stage + 1

/-- The actual varying marked dates. -/
def movingMark
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : ℕ → ℕ :=
  fun index ↦ (packet.base.endpoint (packet.subsequence index)).stage

/-- A positive normalization scale tending to zero. -/
def movingScale
    (_packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : ℕ → ℝ :=
  fun index ↦ 1 / ((index : ℝ) + 1)

theorem movingScale_pos
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    0 < packet.movingScale index := by
  simp only [movingScale]
  positivity

theorem movingScale_tendsto_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Tendsto packet.movingScale atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The fixed moving terminal has cardinality two. -/
theorem movingTerminal_card
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    packet.movingTerminal.val.card = 2 := by
  have hnot : returnSource.producer.owner ∉
      ({returnSource.forcedOwner} : Finset (Fin 4)) := by
    simpa using returnSource.forcedOwner_ne_owner.symm
  rw [movingTerminal, Finset.card_insert_of_notMem hnot]
  simp

/-- The single moving concentrated packet formed from all selected forced
pairs.  Its resolution, owner, terminal, chronology, outsider, and external
payer label are fixed; only its actual profile and marked date move. -/
def movingPacket
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    QuittingReprojectionConcentratedPacket reward packet.movingProfiles
      returnSource.forcedOwner packet.movingTerminal packet.movingCutoff
        packet.movingScale where
  resolution := lambda
  resolution_pos := packet.lambda_pos
  subseq := id
  subseq_strictMono := strictMono_id
  mark := packet.movingMark
  mark_lt := by
    intro index
    simp [movingMark, movingCutoff]
  stageMass := by
    intro index
    rw [show packet.movingTerminal =
        (packet.base.forcedAdapter
          (packet.subsequence index)).routedTerminal by
      exact (packet.forcedTerminal_eq_movingTerminal index).symm]
    simpa only [movingProfiles, movingMark, id_eq] using
      (packet.lambda_lt_forcedPairStageMass index).le
  semanticPrefix := by
    intro index
    have hpositive : 0 < quittingStageCoalitionMass reward
        (packet.movingProfiles index) (packet.movingMark index)
          packet.movingTerminal := by
      have hmass := packet.lambda_lt_forcedPairStageMass index
      rw [packet.forcedTerminal_eq_movingTerminal index] at hmass
      exact packet.lambda_pos.trans (by
        simpa only [movingProfiles, movingMark] using hmass)
    simpa only [id_eq] using
      positive_stageCoalitionMass_has_semanticPrefixIncidence reward
        (packet.movingProfiles index) (packet.movingMark index)
          packet.movingTerminal hpositive
  defect_tendsto := by
    have hzero : (fun index ↦
        (quittingLiveMass reward
            (packet.movingProfiles index) (packet.movingMark index) *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward
                (packet.movingProfiles index)
                  (packet.movingMark index + 1))).1
            (quittingProfileLiveRoot reward (packet.movingProfiles index)
              (packet.movingMark index)) returnSource.forcedOwner /
          packet.movingScale index)) = fun _index ↦ 0 := by
      funext index
      rw [show quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (packet.movingProfiles index)
                (packet.movingMark index + 1))).1
          (quittingProfileLiveRoot reward (packet.movingProfiles index)
          (packet.movingMark index)) returnSource.forcedOwner = 0 by
        simpa only [movingProfiles, movingMark,
          QuittingStageAtomConcentratedPacketAdapter.targetTail] using
          packet.forcedOwnerDefect_eq_zero index]
      simp
    simpa only [id_eq, hzero] using
      (tendsto_const_nhds : Tendsto (fun _index : ℕ ↦ (0 : ℝ))
        atTop (nhds 0))

/-- The moving packet keeps the originally requested fixed resolution. -/
theorem movingPacket_resolution_eq
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    packet.movingPacket.resolution = lambda := rfl

/-- Its literal post-date tail debts converge to the original minimum. -/
theorem movingTailDebt_tendsto_minimum
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Tendsto (fun index ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (packet.movingProfiles (packet.movingPacket.subseq index))
          (packet.movingPacket.mark index + 1)))) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
  convert packet.referenceDebt_tendsto using 1
  funext index
  rw [← quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
  exact congrArg (quittingTerminalSemanticDebtSum ∘
    quittingTerminalSemanticPair reward) (by
      simpa only [movingPacket, movingProfiles, movingMark, id_eq] using
        packet.forcedPair_postDateSpine_eq_reference index)

/-- The moving pair packet enters the global collision-minimum residual
without a strategic-singleton alternative. -/
theorem nonempty_movingCollisionMinimumResidual
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 returnSource.forcedOwner packet.movingTerminal
        packet.movingPacket) := by
  apply packet.movingPacket
    |>.nonempty_collisionMinimumResidual_of_terminal_card_ne_one
  · rw [packet.movingTerminal_card]
    norm_num
  · exact source.semantic_mem
  · exact source.minimum
  · exact source.minimumDebt_pos
  · exact packet.movingScale_pos
  · exact packet.movingScale_tendsto_zero

/-- Every cluster selected from the single moving packet has total debt
exactly equal to the original retained minimum `D_*`. -/
theorem movingCollisionResidual_clusterDebt_eq_minimum
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 returnSource.forcedOwner packet.movingTerminal
        packet.movingPacket) :
    quittingTerminalSemanticDebtSum residual.cluster =
      quittingTerminalSemanticDebtSum source.point.1 := by
  have hclusterDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (packet.movingProfiles
              (packet.movingPacket.subseq (residual.subseq rank)))
            (packet.movingPacket.mark (residual.subseq rank) + 1))))
      atTop (nhds (quittingTerminalSemanticDebtSum residual.cluster)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      residual.tail_tendsto
  have hreference := packet.referenceDebt_tendsto.comp
    residual.subseq_strictMono.tendsto_atTop
  have hminimumDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (packet.movingProfiles
              (packet.movingPacket.subseq (residual.subseq rank)))
            (packet.movingPacket.mark (residual.subseq rank) + 1))))
      atTop (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
    convert hreference using 1
    funext rank
    rw [← quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
    exact congrArg (quittingTerminalSemanticDebtSum ∘
      quittingTerminalSemanticPair reward) (by
        simpa only [movingPacket, movingProfiles, movingMark, id_eq] using
          packet.forcedPair_postDateSpine_eq_reference
            (residual.subseq rank))
  exact tendsto_nhds_unique hclusterDebt hminimumDebt

/-- The strict off-minimum cluster arm is impossible for every residual of
the moving packet. -/
theorem movingCollisionResidual_not_offMinimum
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 returnSource.forcedOwner packet.movingTerminal
        packet.movingPacket) :
    ¬ quittingTerminalSemanticDebtSum source.point.1 <
      quittingTerminalSemanticDebtSum residual.cluster := by
  rw [packet.movingCollisionResidual_clusterDebt_eq_minimum residual]
  exact lt_irrefl _

/-- The residual's exhaustive split therefore lands literally in its
minimum-tail other-defect arm. -/
theorem movingCollisionResidual_minimumTail
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 returnSource.forcedOwner packet.movingTerminal
        packet.movingPacket) :
    quittingTerminalSemanticDebtSum residual.cluster =
        quittingTerminalSemanticDebtSum source.point.1 ∧
      ∀ᶠ rank in atTop,
        packet.movingPacket.resolution *
              quittingTerminalSemanticDebtSum source.point.1 / 2 ≤
          ∑ other ∈ Finset.univ.erase returnSource.forcedOwner,
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward
                  (packet.movingProfiles
                    (packet.movingPacket.subseq (residual.subseq rank)))
                  (packet.movingPacket.mark (residual.subseq rank) + 1))).1
              (quittingProfileLiveRoot reward
                (packet.movingProfiles
                  (packet.movingPacket.subseq (residual.subseq rank)))
                (packet.movingPacket.mark (residual.subseq rank))) other := by
  rcases residual.escape_or_otherDefect with hescape | hminimum
  · exact False.elim
      (packet.movingCollisionResidual_not_offMinimum residual hescape)
  · exact hminimum

/-- Existential capstone: the one moving packet has an actual residual, its
cluster lies exactly on the original minimum-debt fiber, and the compiler's
strict off-minimum arm has been eliminated. -/
theorem exists_minimumTailCollisionResidual
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    ∃ residual : QuittingConcentratedCollisionMinimumResidual reward
        source.point.1 returnSource.forcedOwner packet.movingTerminal
          packet.movingPacket,
      quittingTerminalSemanticDebtSum residual.cluster =
          quittingTerminalSemanticDebtSum source.point.1 ∧
        ∀ᶠ rank in atTop,
          packet.movingPacket.resolution *
                quittingTerminalSemanticDebtSum source.point.1 / 2 ≤
            ∑ other ∈ Finset.univ.erase returnSource.forcedOwner,
              quittingRootCoordinateNashDefect reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward
                    (packet.movingProfiles
                      (packet.movingPacket.subseq (residual.subseq rank)))
                    (packet.movingPacket.mark (residual.subseq rank) + 1))).1
                (quittingProfileLiveRoot reward
                  (packet.movingProfiles
                    (packet.movingPacket.subseq (residual.subseq rank)))
                  (packet.movingPacket.mark (residual.subseq rank))) other := by
  obtain ⟨residual⟩ := packet.nonempty_movingCollisionMinimumResidual
  exact ⟨residual, packet.movingCollisionResidual_minimumTail residual⟩

/-- Consumer-facing contraction: every moving residual is minimum-tail and
the already frozen payer carries the verbatim defect and gain floors at every
outer packet index. -/
theorem movingCollisionResidual_minimumTail_fixedPayer
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (residual : QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 returnSource.forcedOwner packet.movingTerminal
        packet.movingPacket) :
    quittingTerminalSemanticDebtSum residual.cluster =
        quittingTerminalSemanticDebtSum source.point.1 ∧
      packet.payer ≠ returnSource.forcedOwner ∧
      ∀ index,
        lambda * quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
            quittingRootCoordinateNashDefect reward
              (packet.row index).payerAdapter.sourceTail.1
              (packet.row index).payerAdapter.sourceRoot packet.payer ∧
          lambda ^ 2 *
                quittingTerminalSemanticDebtSum source.point.1 / 6 ≤
            (packet.row index).payerGain := by
  exact ⟨packet.movingCollisionResidual_clusterDebt_eq_minimum residual,
    packet.payer_ne_forcedOwner, fun index ↦
      ⟨packet.lambda_mul_minimumDebt_div_six_le_payerDefect index,
        packet.lambda_sq_mul_minimumDebt_div_six_le_payerGain index⟩⟩

/-- One admissible resolution together with the single moving packet, its
minimum-tail residual, and the stronger directly selected payer bounds. -/
structure ResolutionCapstone
    (returnSource :
      FinFourOwnerCompressedMinimumReturnForcedPairSource source)
    (lambda : ℝ) where
  packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource lambda
  residual : QuittingConcentratedCollisionMinimumResidual reward
    source.point.1 returnSource.forcedOwner packet.movingTerminal
      packet.movingPacket
  clusterDebt_eq : quittingTerminalSemanticDebtSum residual.cluster =
    quittingTerminalSemanticDebtSum source.point.1
  payer_ne_forcedOwner : packet.payer ≠ returnSource.forcedOwner
  paidBounds : ∀ index,
    quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
        quittingRootCoordinateNashDefect reward
          (packet.row index).payerAdapter.sourceTail.1
          (packet.row index).payerAdapter.sourceRoot packet.payer ∧
      lambda * quittingTerminalSemanticDebtSum source.point.1 / 3 ≤
        (packet.row index).payerGain

/-- Each selected strong forced pair reaches the existing collision-minimum
consumer without any supplied certificate hypothesis. -/
theorem nonempty_collisionMinimumResidual
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    Nonempty (QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 returnSource.forcedOwner
        (packet.base.forcedAdapter
          (packet.subsequence index)).routedTerminal
        (packet.base.forcedAdapter
          (packet.subsequence index)).packet) :=
  (packet.row index).nonempty_collisionMinimumResidual

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

namespace FinFourOwnerCompressedMinimumReturnForcedPairSource

variable
  {source : FinFourMinimumAtomProducer reward bound}

/-- Construct the complete minimum-tail result at one resolution, without
reselecting this source object's chronology or table outsider. -/
theorem nonempty_resolutionCapstone
    (returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source)
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    (hlambda_lt : lambda < source.point.2 (some source.atom.terminal)) :
    Nonempty
      (FinFourOwnerCompressedMinimumReturnForcedPairPacket.ResolutionCapstone
        returnSource lambda) := by
  obtain ⟨packet⟩ := returnSource.nonempty_packet lambda hlambda_pos
    hlambda_lt
  obtain ⟨residual⟩ := packet.nonempty_movingCollisionMinimumResidual
  exact ⟨{
    packet := packet
    residual := residual
    clusterDebt_eq :=
      packet.movingCollisionResidual_clusterDebt_eq_minimum residual
    payer_ne_forcedOwner := packet.payer_ne_forcedOwner
    paidBounds := fun index ↦
      ⟨packet.payerDefect_floor index, packet.payerGain_floor index⟩
  }⟩

end FinFourOwnerCompressedMinimumReturnForcedPairSource

/-- One chronology and table outsider fixed before all resolutions, with a
complete minimum-tail resolution capstone available for every later
`0 < lambda < mu`. -/
structure FinFourOwnerCompressedMinimumReturnForcedPairFamilyCapstone
    (source : FinFourMinimumAtomProducer reward bound) where
  returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source
  resolution : ∀ lambda, 0 < lambda →
    lambda < source.point.2 (some source.atom.terminal) →
      Nonempty
        (FinFourOwnerCompressedMinimumReturnForcedPairPacket.ResolutionCapstone
          returnSource lambda)

namespace FinFourMinimumAtomProducer

/-- One-shot Part B capstone with the source/chronology/outsider choice made
outside the universal resolution quantifier. -/
theorem nonempty_minimumReturnForcedPairFamilyCapstone
    (source : FinFourMinimumAtomProducer reward bound)
    (terminal_card : source.atom.terminal.val.card = 1) :
    Nonempty
      (FinFourOwnerCompressedMinimumReturnForcedPairFamilyCapstone source) := by
  obtain ⟨returnSource⟩ :=
    source.nonempty_minimumReturnForcedPairSource terminal_card
  exact ⟨{
    returnSource := returnSource
    resolution := fun lambda hlambda_pos hlambda_lt ↦
      returnSource.nonempty_resolutionCapstone lambda hlambda_pos hlambda_lt
  }⟩

end FinFourMinimumAtomProducer

end GameTheory
