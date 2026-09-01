import Research.Quitting.ExactPrefixAtomTransport
import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairMinimumCausalization
import Research.Quitting.FinFourProducerAtlas.PairedSameResidualSourceRegeneration
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.CommonPrefixTerminalLawStability

/-!
# Common-prefix transport for a moving-pair minimum chord

The source-faithful chord causalization supplies exact cap--Nash words
against the literal chord tails.  This module copies each same word before
the chord and routed target tails.  It retains their literal unilateral
response edge, exact payoff/debt/law transport, complete target convergence,
and the shifted marked atom.

The target is causalized only after one common tail reindex.  No claim says
that its new causalization reuses the chord words.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {data : FinFourMovingMarkedPairMinimumSource source}
  {residual : FinFourMovingMarkedPairVanishingResidual data}
  {minimum : FinFourMovingMarkedPairMinimumApproach residual}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
  {compactification :
    FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1}

/-- The first source-faithful causalization, whose words are exact against
the actual chord tails. -/
structure FinFourMovingMarkedPairCommonPrefixResponse
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) where
  causalization : QuittingSourceFaithfulMinimumCausalization
    compactification.chordPoint data.labels.targetTerminal
    (fun rank ↦ data.chordProfile weight hweight0.le hweight1.le
      (compactification.select rank))
    (fun rank ↦ (data.marked (compactification.select rank)).mark)
    (weight * data.reachFloor)

namespace FinFourMovingMarkedPairCommonPrefixResponse

/-- Literal source tail on the final common selector. -/
def sourceTail
    (_common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  data.sourceProfile (compactification.select rank)

/-- Literal actual chord tail on the final common selector. -/
def chordTail
    (_common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  data.chordProfile weight hweight0.le hweight1.le
    (compactification.select rank)

/-- Literal routed target tail on the same final selector. -/
def targetTail
    (_common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  data.targetProfile (compactification.select rank)

/-- Joint survival of the exact chord word. -/
def survival
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : ℝ :=
  quittingLiteralRootStackJointSurvival (common.causalization.roots rank)

/-- Chord tail behind its selected exact cap--Nash word. -/
def chordPrefixedProfile
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (common.causalization.roots rank)
    (common.chordTail rank)

/-- Routed target tail behind the same copied word. -/
def targetPrefixedProfile
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (common.causalization.roots rank)
    (common.targetTail rank)

/-- Shifted location of the original routed marked atom. -/
def shiftedMark
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : ℕ :=
  (common.causalization.roots rank).length +
    (data.marked (compactification.select rank)).mark

/-- The copied word's joint survival tends to one. -/
theorem survival_tendsto_one
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) :
    Tendsto common.survival atTop (nhds 1) := by
  change Tendsto (fun rank ↦ quittingCapNashStackContinueProduct
    (common.causalization.roots rank)) atTop (nhds 1)
  exact common.causalization.continueProduct_tendsto_one

/-- Opponents agree in the actual chord and routed target tails. -/
theorem targetTail_eq_chordTail_of_ne
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) (other : Fin 4) (hne : other ≠ data.labels.mover) :
    common.targetTail rank other = common.chordTail rank other := by
  unfold targetTail chordTail FinFourMovingMarkedPairMinimumSource.chordProfile
    quittingResponseChordProfile
  rw [Function.update_of_ne hne]
  exact data.targetProfile_eq_sourceProfile_of_ne
    (compactification.select rank) other hne

/-- A common literal word preserves equality of complete tail strategies. -/
private theorem literalRootStackProfile_apply_eq_of_tail
    (roots : List (Fin 4 → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile) (who : Fin 4)
    (htail : first who = second who) :
    quittingLiteralRootStackProfile reward roots first who =
      quittingLiteralRootStackProfile reward roots second who := by
  induction roots with
  | nil => simpa
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons]
      funext time history
      cases time with
      | zero => rfl
      | succ time => exact congrFun (congrFun ih time) _

/-- Opponent agreement survives the copied word. -/
theorem targetPrefixedProfile_eq_chordPrefixedProfile_of_ne
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) (other : Fin 4) (hne : other ≠ data.labels.mover) :
    common.targetPrefixedProfile rank other =
      common.chordPrefixedProfile rank other := by
  exact literalRootStackProfile_apply_eq_of_tail
    (common.causalization.roots rank) (common.targetTail rank)
      (common.chordTail rank) other
      (common.targetTail_eq_chordTail_of_ne rank other hne)

/-- The copied target is the literal full-strategy response to the copied
chord. -/
theorem targetPrefixed_eq_update
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) :
    common.targetPrefixedProfile rank = Function.update
      (common.chordPrefixedProfile rank) data.labels.mover
      (common.targetPrefixedProfile rank data.labels.mover) := by
  symm
  apply update_endpoint_with_response_observer_eq_response
  intro other hother
  exact common.targetPrefixedProfile_eq_chordPrefixedProfile_of_ne
    rank other hother

/-- The target response leaves the mover's unrestricted cap unchanged. -/
theorem targetPrefixed_mover_cap_eq_chordPrefixed
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingContinuationBestResponseValue reward
        (common.targetPrefixedProfile rank) data.labels.mover =
      quittingContinuationBestResponseValue reward
        (common.chordPrefixedProfile rank) data.labels.mover := by
  rw [common.targetPrefixed_eq_update rank]
  exact quittingContinuationBestResponseValue_update_self reward
    (common.chordPrefixedProfile rank) data.labels.mover
      (common.targetPrefixedProfile rank data.labels.mover)

/-- Exact payoff transport through the copied word. -/
theorem targetPrefixed_payoff_sub_chordPrefixed_eq_survival_mul
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) (who : Fin 4) :
    quittingTerminalPayoff reward (common.targetPrefixedProfile rank) who -
        quittingTerminalPayoff reward (common.chordPrefixedProfile rank) who =
      common.survival rank *
        (quittingTerminalPayoff reward (common.targetTail rank) who -
          quittingTerminalPayoff reward (common.chordTail rank) who) := by
  exact quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul
    (reward := reward) (common.causalization.roots rank)
      (common.targetTail rank) (common.chordTail rank) who

/-- The tail chord-to-target mover gain is the complementary chord weight
times the original routed gain. -/
theorem targetTail_payoffGain_eq_complement_mul_reach_mul_rewardGap
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalPayoff reward (common.targetTail rank)
          data.labels.mover -
        quittingTerminalPayoff reward (common.chordTail rank)
          data.labels.mover =
      (1 - weight) * data.markedReach (compactification.select rank) *
        data.labels.rewardGap reward := by
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq reward
    (common.sourceTail rank) data.labels.mover data.labels.mover
      (common.sourceTail rank data.labels.mover)
      (common.targetTail rank data.labels.mover) weight
      hweight0.le hweight1.le
  have htarget : Function.update (common.sourceTail rank) data.labels.mover
      (common.targetTail rank data.labels.mover) = common.targetTail rank := by
    apply update_endpoint_with_response_observer_eq_response
    intro other hother
    exact data.targetProfile_eq_sourceProfile_of_ne
      (compactification.select rank) other hother
  rw [Function.update_eq_self, htarget] at haffine
  change quittingTerminalPayoff reward (common.chordTail rank)
      data.labels.mover =
    (1 - weight) * quittingTerminalPayoff reward (common.sourceTail rank)
        data.labels.mover +
      weight * quittingTerminalPayoff reward (common.targetTail rank)
        data.labels.mover at haffine
  have hgain := data.targetPayoff_sub_sourcePayoff_eq_markedReach_mul_rewardGap
    (compactification.select rank)
  change quittingTerminalPayoff reward (common.targetTail rank)
        data.labels.mover -
      quittingTerminalPayoff reward (common.sourceTail rank)
        data.labels.mover =
    data.markedReach (compactification.select rank) *
      data.labels.rewardGap reward at hgain
  linear_combination (1 - weight) * hgain - haffine

/-- Literal copied-prefix mover gain with every coefficient exposed. -/
theorem targetPrefixed_payoffGain_eq_survival_mul_complement_mul_reach_mul_gap
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalPayoff reward (common.targetPrefixedProfile rank)
          data.labels.mover -
        quittingTerminalPayoff reward (common.chordPrefixedProfile rank)
          data.labels.mover =
      common.survival rank * (1 - weight) *
        data.markedReach (compactification.select rank) *
          data.labels.rewardGap reward := by
  rw [common.targetPrefixed_payoff_sub_chordPrefixed_eq_survival_mul,
    common.targetTail_payoffGain_eq_complement_mul_reach_mul_rewardGap]
  ring

/-- The copied behavioral response edge has one uniform positive payoff-gain
floor eventually. -/
theorem eventually_gainFloor_le_targetPrefixed_payoffGain
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) :
    ∀ᶠ rank in atTop,
      (1 - weight) * data.reachFloor * data.labels.rewardGap reward / 2 ≤
        quittingTerminalPayoff reward (common.targetPrefixedProfile rank)
            data.labels.mover -
          quittingTerminalPayoff reward (common.chordPrefixedProfile rank)
            data.labels.mover := by
  have hhalf : ∀ᶠ rank in atTop, 1 / 2 < common.survival rank :=
    common.survival_tendsto_one.eventually (Ioi_mem_nhds (by norm_num))
  filter_upwards [hhalf] with rank hrank
  rw [common.targetPrefixed_payoffGain_eq_survival_mul_complement_mul_reach_mul_gap]
  have hreach := data.reachFloor_le (compactification.select rank)
  change data.reachFloor ≤
    data.markedReach (compactification.select rank) at hreach
  have hweight : 0 ≤ 1 - weight := (sub_pos.mpr hweight1).le
  have hgap : 0 ≤ data.labels.rewardGap reward := data.rewardGap_pos.le
  have hfloor : 0 ≤ data.reachFloor := data.reachFloor_pos.le
  have hsurvival : 0 ≤ common.survival rank :=
    quittingLiteralRootStackJointSurvival_nonneg _
  have hcoefficient : 0 ≤
      (1 - weight) * data.reachFloor * data.labels.rewardGap reward :=
    mul_nonneg (mul_nonneg hweight hfloor) hgap
  calc
    (1 - weight) * data.reachFloor * data.labels.rewardGap reward / 2 =
        (1 / 2) * (1 - weight) * data.reachFloor *
          data.labels.rewardGap reward := by ring
    _ = (1 / 2) * ((1 - weight) * data.reachFloor *
        data.labels.rewardGap reward) := by ring
    _ ≤ common.survival rank * ((1 - weight) * data.reachFloor *
        data.labels.rewardGap reward) :=
      mul_le_mul_of_nonneg_right hrank.le hcoefficient
    _ = common.survival rank * (1 - weight) * data.reachFloor *
        data.labels.rewardGap reward := by ring
    _ ≤ common.survival rank * (1 - weight) *
        data.markedReach (compactification.select rank) *
          data.labels.rewardGap reward := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hreach
          (mul_nonneg hsurvival hweight)) hgap

/-- Exact mover-debt transport through the copied word. -/
theorem targetPrefixed_moverDebt_eq_survival_mul_premarkResidual
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingTerminalDeviationDebt reward (common.targetPrefixedProfile rank)
        data.labels.mover =
      common.survival rank *
        data.premarkResidual (compactification.select rank) := by
  have hchord := quittingTerminalDeviationDebt_capNashRootStack_eq
    (reward := reward) (common.causalization.roots rank)
      (common.chordTail rank) data.labels.mover
      (common.causalization.roots_nash rank)
  change quittingTerminalDeviationDebt reward
        (common.chordPrefixedProfile rank) data.labels.mover =
      common.survival rank * quittingTerminalDeviationDebt reward
        (common.chordTail rank) data.labels.mover at hchord
  have hgain :=
    common.targetPrefixed_payoff_sub_chordPrefixed_eq_survival_mul
      rank data.labels.mover
  have hprefixCap := common.targetPrefixed_mover_cap_eq_chordPrefixed rank
  have htailCap : quittingContinuationBestResponseValue reward
      (common.targetTail rank) data.labels.mover =
      quittingContinuationBestResponseValue reward
        (common.chordTail rank) data.labels.mover := by
    have hupdate : Function.update (common.chordTail rank) data.labels.mover
        (common.targetTail rank data.labels.mover) =
      common.targetTail rank := by
      apply update_endpoint_with_response_observer_eq_response
      exact common.targetTail_eq_chordTail_of_ne rank
    rw [← hupdate]
    exact quittingContinuationBestResponseValue_update_self reward
      (common.chordTail rank) data.labels.mover
        (common.targetTail rank data.labels.mover)
  unfold quittingTerminalDeviationDebt at hchord ⊢
  rw [hprefixCap]
  have htargetDebt := data.target_mover_debt_eq_premarkResidual
    (compactification.select rank)
  change quittingContinuationBestResponseValue reward
        (common.targetTail rank) data.labels.mover -
      quittingTerminalPayoff reward (common.targetTail rank)
        data.labels.mover =
    data.premarkResidual (compactification.select rank) at htargetDebt
  linear_combination hchord - hgain - common.survival rank * htailCap +
    common.survival rank * htargetDebt

/-- Exact routed-coalition mass at the shifted original mark. -/
theorem targetPrefixed_shiftedMark_mass_eq_survival_mul_markedReach
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) :
    quittingStageCoalitionMass reward (common.targetPrefixedProfile rank)
        (common.shiftedMark rank) data.labels.targetTerminal =
      common.survival rank *
        data.markedReach (compactification.select rank) := by
  unfold targetPrefixedProfile shiftedMark survival targetTail
  rw [quittingStageCoalitionMass_literalRootStack_add_length,
    data.target_stageCoalitionMass_targetTerminal_eq_markedReach]
  rfl

/-- The copied words are nonempty. -/
theorem roots_ne_nil
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : common.causalization.roots rank ≠ [] := by
  intro hempty
  have hlength := common.causalization.roots_length rank
  rw [hempty] at hlength
  simp at hlength

/-- Head of the selected nonempty word. -/
def firstRoot
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : Fin 4 → PMF Bool :=
  (common.causalization.roots rank).head (common.roots_ne_nil rank)

/-- Tail of the selected nonempty word. -/
def remainingRoots
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) : List (Fin 4 → PMF Bool) :=
  (common.causalization.roots rank).tail

/-- Head and tail recover the selected word. -/
theorem firstRoot_cons_remainingRoots
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) :
    common.firstRoot rank :: common.remainingRoots rank =
      common.causalization.roots rank :=
  List.cons_head_tail (common.roots_ne_nil rank)

/-- Actual target tails converge jointly to the compact target. -/
theorem targetTail_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (common.targetTail rank),
        quittingTerminalOutcomeMass reward (common.targetTail rank)))
      atTop (nhds compactification.targetPoint) := by
  simpa only [targetTail,
    FinFourMovingMarkedPairMinimumChordCompactification.select,
    Function.comp_apply] using compactification.target_tendsto

/-- Actual chord tails converge jointly to the compact chord. -/
theorem chordTail_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (common.chordTail rank),
        quittingTerminalOutcomeMass reward (common.chordTail rank)))
      atTop (nhds compactification.chordPoint) := by
  exact common.causalization.profiles_tendsto

/-- Singleton cash-out is strictly below every target limiting cap. -/
theorem singletonReward_lt_targetPoint_cap
    (_common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    reward (quittingSingletonTerminal who) who <
      compactification.targetPoint.1.2 who := by
  have hsemantic : compactification.targetPoint.1 ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier compactification.targetPoint
      compactification.targetPoint_mem
  have hpositive : 0 <
      quittingTerminalSemanticDebtSum compactification.targetPoint.1 := by
    rw [(compactification.target_and_chord_debtSum_eq_source).1]
    exact source.minimumDebt_pos
  have hmargin := minimumTerminalSemantic_singletonMargin
    compactification.targetPoint.1 hsemantic
      compactification.target_globalMinimum hpositive who
  linarith [hpositive]

/-- Singleton cash-out is strictly below every chord limiting cap. -/
theorem singletonReward_lt_chordPoint_cap
    (_common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    reward (quittingSingletonTerminal who) who <
      compactification.chordPoint.1.2 who := by
  have hsemantic : compactification.chordPoint.1 ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier compactification.chordPoint
      compactification.chordPoint_mem
  have hpositive : 0 <
      quittingTerminalSemanticDebtSum compactification.chordPoint.1 := by
    rw [(compactification.target_and_chord_debtSum_eq_source).2]
    exact source.minimumDebt_pos
  have hmargin := minimumTerminalSemantic_singletonMargin
    compactification.chordPoint.1 hsemantic
      compactification.chord_globalMinimum hpositive who
  linarith [hpositive]

/-- Complete target-tail caps converge coordinatewise. -/
theorem targetTail_cap_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (common.targetTail rank) who) atTop
      (nhds (compactification.targetPoint.1.2 who)) := by
  have hpair := continuous_fst.tendsto compactification.targetPoint |>.comp
    common.targetTail_tendsto
  exact ((continuous_apply who).comp continuous_snd).tendsto
    compactification.targetPoint.1 |>.comp hpair

/-- Complete chord-tail caps converge coordinatewise. -/
theorem chordTail_cap_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (common.chordTail rank) who) atTop
      (nhds (compactification.chordPoint.1.2 who)) := by
  have hpair := continuous_fst.tendsto compactification.chordPoint |>.comp
    common.chordTail_tendsto
  exact ((continuous_apply who).comp continuous_snd).tendsto
    compactification.chordPoint.1 |>.comp hpair

/-- Complete target-prefixed caps converge coordinatewise. -/
theorem targetPrefixed_cap_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (common.targetPrefixedProfile rank) who) atTop
      (nhds (compactification.targetPoint.1.2 who)) := by
  have hsurvival : Tendsto (fun rank ↦
      quittingLiteralRootStackJointSurvival
        (common.firstRoot rank :: common.remainingRoots rank))
      atTop (nhds 1) := by
    rw [show (fun rank ↦ quittingLiteralRootStackJointSurvival
        (common.firstRoot rank :: common.remainingRoots rank)) =
      common.survival by
        funext rank
        rw [common.firstRoot_cons_remainingRoots]
        rfl]
    exact common.survival_tendsto_one
  have hcap :=
    tendsto_quittingContinuationBestResponseValue_literalRootStack_of_joint
      reward common.firstRoot common.remainingRoots common.targetTail who
      (compactification.targetPoint.1.2 who) hsurvival
      (common.targetTail_cap_tendsto who)
      (common.singletonReward_lt_targetPoint_cap who)
  simpa only [targetPrefixedProfile,
    common.firstRoot_cons_remainingRoots] using hcap

/-- Complete chord-prefixed caps converge coordinatewise. -/
theorem chordPrefixed_cap_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingContinuationBestResponseValue reward
      (common.chordPrefixedProfile rank) who) atTop
      (nhds (compactification.chordPoint.1.2 who)) := by
  have hsurvival : Tendsto (fun rank ↦
      quittingLiteralRootStackJointSurvival
        (common.firstRoot rank :: common.remainingRoots rank))
      atTop (nhds 1) := by
    rw [show (fun rank ↦ quittingLiteralRootStackJointSurvival
        (common.firstRoot rank :: common.remainingRoots rank)) =
      common.survival by
        funext rank
        rw [common.firstRoot_cons_remainingRoots]
        rfl]
    exact common.survival_tendsto_one
  have hcap :=
    tendsto_quittingContinuationBestResponseValue_literalRootStack_of_joint
      reward common.firstRoot common.remainingRoots common.chordTail who
      (compactification.chordPoint.1.2 who) hsurvival
      (common.chordTail_cap_tendsto who)
      (common.singletonReward_lt_chordPoint_cap who)
  simpa only [chordPrefixedProfile,
    common.firstRoot_cons_remainingRoots] using hcap

/-- Chord-tail debt coordinates converge. -/
theorem chordTail_debt_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalDeviationDebt reward
      (common.chordTail rank) who) atTop
      (nhds (quittingTerminalSemanticDebt
        compactification.chordPoint.1 who)) := by
  have hpair := continuous_fst.tendsto compactification.chordPoint |>.comp
    common.chordTail_tendsto
  exact (continuous_quittingTerminalSemanticDebt who).tendsto
    compactification.chordPoint.1 |>.comp hpair

/-- Exact chord-prefixed playerwise debt scaling. -/
theorem chordPrefixed_debt_eq_survival_mul
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (rank : ℕ) (who : Fin 4) :
    quittingTerminalDeviationDebt reward (common.chordPrefixedProfile rank) who =
      common.survival rank *
        quittingTerminalDeviationDebt reward (common.chordTail rank) who := by
  exact quittingTerminalDeviationDebt_capNashRootStack_eq
    (reward := reward) (common.causalization.roots rank)
      (common.chordTail rank) who (common.causalization.roots_nash rank)

/-- Chord-prefixed debt coordinates converge. -/
theorem chordPrefixed_debt_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalDeviationDebt reward
      (common.chordPrefixedProfile rank) who) atTop
      (nhds (quittingTerminalSemanticDebt
        compactification.chordPoint.1 who)) := by
  have hproduct := common.survival_tendsto_one.mul
    (common.chordTail_debt_tendsto who)
  convert hproduct using 1
  · funext rank
    exact common.chordPrefixed_debt_eq_survival_mul rank who
  · simp

/-- Chord-prefixed prescribed payoffs converge coordinatewise. -/
theorem chordPrefixed_payoff_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (common.chordPrefixedProfile rank) who) atTop
      (nhds (compactification.chordPoint.1.1 who)) := by
  have hdifference := (common.chordPrefixed_cap_tendsto who).sub
    (common.chordPrefixed_debt_tendsto who)
  unfold quittingTerminalDeviationDebt at hdifference
  simpa only [quittingTerminalSemanticDebt, sub_sub_cancel] using hdifference

/-- Target-tail prescribed payoffs converge coordinatewise. -/
theorem targetTail_payoff_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (common.targetTail rank) who) atTop
      (nhds (compactification.targetPoint.1.1 who)) := by
  have hpair := continuous_fst.tendsto compactification.targetPoint |>.comp
    common.targetTail_tendsto
  exact ((continuous_apply who).comp continuous_fst).tendsto
    compactification.targetPoint.1 |>.comp hpair

/-- Chord-tail prescribed payoffs converge coordinatewise. -/
theorem chordTail_payoff_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (common.chordTail rank) who) atTop
      (nhds (compactification.chordPoint.1.1 who)) := by
  have hpair := continuous_fst.tendsto compactification.chordPoint |>.comp
    common.chordTail_tendsto
  exact ((continuous_apply who).comp continuous_fst).tendsto
    compactification.chordPoint.1 |>.comp hpair

/-- Target-prefixed prescribed payoffs converge coordinatewise. -/
theorem targetPrefixed_payoff_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
    (who : Fin 4) :
    Tendsto (fun rank ↦ quittingTerminalPayoff reward
      (common.targetPrefixedProfile rank) who) atTop
      (nhds (compactification.targetPoint.1.1 who)) := by
  have htailDifference := (common.targetTail_payoff_tendsto who).sub
    (common.chordTail_payoff_tendsto who)
  have hscaled := common.survival_tendsto_one.mul htailDifference
  have hsum := hscaled.add (common.chordPrefixed_payoff_tendsto who)
  convert hsum using 1
  · funext rank
    have htransport :=
      common.targetPrefixed_payoff_sub_chordPrefixed_eq_survival_mul rank who
    linarith
  · congr 1
    ring

/-- The complete terminal law of the copied target converges to the compact
target law. -/
theorem targetPrefixed_law_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦ quittingTerminalOutcomeMass reward
      (common.targetPrefixedProfile rank)) atTop
      (nhds compactification.targetPoint.2) := by
  apply tendsto_quittingTerminalOutcomeMass_literalRootStack_of_joint
  · exact common.survival_tendsto_one
  · exact (continuous_snd.tendsto compactification.targetPoint).comp
      common.targetTail_tendsto

/-- The copied target profiles converge in the complete semantic/law packet
to the strict-support child. -/
theorem targetPrefixed_tendsto
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (common.targetPrefixedProfile rank),
        quittingTerminalOutcomeMass reward
          (common.targetPrefixedProfile rank)))
      atTop (nhds compactification.targetPoint) := by
  have hpayoff : Tendsto (fun rank who ↦ quittingTerminalPayoff reward
      (common.targetPrefixedProfile rank) who) atTop
      (nhds compactification.targetPoint.1.1) :=
    tendsto_pi_nhds.mpr common.targetPrefixed_payoff_tendsto
  have hcap : Tendsto (fun rank who ↦ quittingContinuationBestResponseValue
      reward (common.targetPrefixedProfile rank) who) atTop
      (nhds compactification.targetPoint.1.2) :=
    tendsto_pi_nhds.mpr common.targetPrefixed_cap_tendsto
  have hsemantic := hpayoff.prodMk hcap
  rw [nhds_prod_eq, nhds_prod_eq]
  exact hsemantic.prodMk common.targetPrefixed_law_tendsto

/-- Eventually the shifted routed atom retains at least half the original
uniform reach floor. -/
theorem eventually_half_reachFloor_le_targetPrefixed_shiftedMark_mass
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) :
    ∀ᶠ rank in atTop, data.reachFloor / 2 ≤
      quittingStageCoalitionMass reward (common.targetPrefixedProfile rank)
        (common.shiftedMark rank) data.labels.targetTerminal := by
  have hhalf : ∀ᶠ rank in atTop, 1 / 2 < common.survival rank :=
    common.survival_tendsto_one.eventually (Ioi_mem_nhds (by norm_num))
  filter_upwards [hhalf] with rank hrank
  rw [common.targetPrefixed_shiftedMark_mass_eq_survival_mul_markedReach]
  have hsurvival0 : 0 ≤ common.survival rank :=
    quittingLiteralRootStackJointSurvival_nonneg _
  have hreach := data.reachFloor_le (compactification.select rank)
  change data.reachFloor ≤
    data.markedReach (compactification.select rank) at hreach
  nlinarith [data.reachFloor_pos]

end FinFourMovingMarkedPairCommonPrefixResponse

/-- The supplied minimum-chord compactification admits a common-word
response package using its source-faithful chord causalization. -/
theorem nonempty_finFourMovingMarkedPairCommonPrefixResponse
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    Nonempty (FinFourMovingMarkedPairCommonPrefixResponse compactification) := by
  obtain ⟨causalization⟩ :=
    compactification.nonempty_sourceFaithfulMinimumCausalization
  exact ⟨⟨causalization⟩⟩

end GameTheory
