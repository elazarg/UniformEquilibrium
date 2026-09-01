import UniformEquilibrium.Diagnostics.Quitting.LiteralOneDateProfile
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapPortExactTrichotomy
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualReachPaidFirstDisagreement
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFiniteCapSeedSharpness
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSelfTailClosure
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryTailSemanticReduction

/-!
# An actual screened mark and its premark debt residual

This module records one literal behavioral profile whose marked live
root contains a sure-quitting opponent.  The mover is changed only at that
mark, from the opposite pure endpoint to a locally weakly better endpoint.
The resulting identities concern complete behavioral-profile payoffs and
unrestricted behavioral replacement caps.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual profile data for one locally selected endpoint at a root screened
by an unchanged sure-quitting opponent.  A pure pair root supplies these
fields by choosing the other member of the pair. -/
structure QuittingActualReachedScreenedEndpointMark
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  sourceProfile : (quittingGame reward).BehaviorProfile
  mover : ι
  other : ι
  mark : ℕ
  selectedAction : Bool
  other_ne_mover : other ≠ mover
  source_mover_opposite :
    quittingProfileLiveRoot reward sourceProfile mark mover =
      PMF.pure (!selectedAction)
  source_other_quits :
    quittingProfileLiveRoot reward sourceProfile mark other = PMF.pure true
  selected_endpoint_gain_nonneg :
    0 ≤ quittingRootSuccessorPayoff reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward sourceProfile (mark + 1))).1
          (Function.update
            (quittingProfileLiveRoot reward sourceProfile mark) mover
            (PMF.pure selectedAction)) mover -
        quittingRootSuccessorPayoff reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward sourceProfile (mark + 1))).1
          (quittingProfileLiveRoot reward sourceProfile mark) mover

namespace QuittingActualReachedScreenedEndpointMark

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The literal target changes only the mover's prescribed action at the
marked date. -/
def targetProfile (source : QuittingActualReachedScreenedEndpointMark reward) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward source.sourceProfile source.mover
    source.mark source.selectedAction

/-- The actual shifted semantic tail used at the marked root. -/
def tail (source : QuittingActualReachedScreenedEndpointMark reward) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward source.sourceProfile
      (source.mark + 1))

/-- The selected local endpoint gap at the actual marked root and tail. -/
def localEndpointGap
    (source : QuittingActualReachedScreenedEndpointMark reward) : ℝ :=
  quittingRootSuccessorPayoff reward source.tail.1
      (Function.update
        (quittingProfileLiveRoot reward source.sourceProfile source.mark)
        source.mover (PMF.pure source.selectedAction)) source.mover -
    quittingRootSuccessorPayoff reward source.tail.1
      (quittingProfileLiveRoot reward source.sourceProfile source.mark)
      source.mover

/-- The full-profile payoff gained by the one-date marked toggle. -/
def markedToggleGain
    (source : QuittingActualReachedScreenedEndpointMark reward) : ℝ :=
  quittingTerminalPayoff reward source.targetProfile source.mover -
    quittingTerminalPayoff reward source.sourceProfile source.mover

/-- The debt remaining after applying the selected marked endpoint.  It is a
complete behavioral-cap residual, not a local-root residual. -/
def premarkResidual
    (source : QuittingActualReachedScreenedEndpointMark reward) : ℝ :=
  quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward source.targetProfile) source.mover

/-- The marked toggle's whole-profile payoff gain is actual reach times the
local endpoint gap. -/
theorem markedToggleGain_eq_liveMass_mul_localEndpointGap
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    source.markedToggleGain =
      quittingLiveMass reward source.sourceProfile source.mark *
        source.localEndpointGap := by
  simpa only [markedToggleGain, targetProfile, localEndpointGap, tail] using
    quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect
      reward source.sourceProfile source.mover source.mark source.selectedAction

/-- The target mover's debt is literally the premark residual. -/
theorem target_mover_debt_eq_premarkResidual
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source.targetProfile) source.mover =
      source.premarkResidual := rfl

/-- The source mover's complete debt splits into the marked contribution and
the debt left on the literal target. -/
theorem source_mover_debt_eq_markedToggleGain_add_premarkResidual
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source.sourceProfile) source.mover =
      source.markedToggleGain + source.premarkResidual := by
  have hsub := quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain
    reward source.sourceProfile source.mover source.mark source.selectedAction
  dsimp only [targetProfile, markedToggleGain, premarkResidual] at hsub ⊢
  linarith

/-- Literal reached-contribution form of the source mover's debt split. -/
theorem source_mover_debt_eq_reach_mul_localEndpointGap_add_premarkResidual
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source.sourceProfile) source.mover =
      quittingLiveMass reward source.sourceProfile source.mark *
          source.localEndpointGap +
        source.premarkResidual := by
  rw [source.source_mover_debt_eq_markedToggleGain_add_premarkResidual,
    source.markedToggleGain_eq_liveMass_mul_localEndpointGap]

/-- The screened endpoint selection makes the marked contribution
nonnegative. -/
theorem markedToggleGain_nonneg
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    0 ≤ source.markedToggleGain := by
  rw [source.markedToggleGain_eq_liveMass_mul_localEndpointGap]
  exact mul_nonneg (quittingLiveMass_nonneg reward source.sourceProfile source.mark)
    source.selected_endpoint_gain_nonneg

/-- The unchanged other player still quits surely at the target marked root. -/
theorem target_other_quits
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    quittingProfileLiveRoot reward source.targetProfile source.mark source.other =
      PMF.pure true := by
  rw [targetProfile, quittingProfileLiveRoot_literalOneDateProfile]
  rw [Function.update_of_ne source.other_ne_mover]
  exact source.source_other_quits

/-- The literal target preserves every canonical live root strictly before
the marked date. -/
theorem targetProfile_liveRoot_eq_of_lt
    (source : QuittingActualReachedScreenedEndpointMark reward)
    {time : ℕ} (htime : time < source.mark) :
    quittingProfileLiveRoot reward source.targetProfile time =
      quittingProfileLiveRoot reward source.sourceProfile time := by
  unfold targetProfile quittingLiteralOneDateProfile quittingProfileLiveRoot
  funext player
  by_cases hplayer : player = source.mover
  · subst player
    rw [Function.update_self]
    exact congrFun (quittingLiteralOneDateOverride_of_ne
      (source.sourceProfile source.mover) source.mark time
      source.selectedAction (Nat.ne_of_lt htime)) (quittingLiveHist reward time)
  · rw [Function.update_of_ne hplayer]

/-- At the target mark the fixed opponents cannot all continue, because the
unchanged screening player quits surely. -/
theorem target_fixedOpponentsContinueMass_eq_zero
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    quittingFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward source.targetProfile) source.mover
        source.mark = 0 := by
  unfold quittingFixedOpponentsContinueMass
  apply quittingStationaryContinueMass_of_sureQuitter
    (quitter := source.other)
  rw [Function.update_of_ne source.other_ne_mover]
  exact source.target_other_quits

/-- Every plan which waits beyond the target mark has the screened Continue
value at that mark. -/
theorem target_relativePureTimeValue_eq_continueReward
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (later : Option ℕ) (hlater : IsQuittingStrictlyLaterDelay later) :
    quittingRootSequenceRelativePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward source.targetProfile) source.mover
        source.mark later =
      quittingFixedOpponentsContinueReward reward
        (quittingProfileLiveRoot reward source.targetProfile) source.mover
        source.mark := by
  unfold quittingRootSequenceRelativePureTimeTerminalValue
    quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  have hmass := source.target_fixedOpponentsContinueMass_eq_zero
  cases later with
  | none => simp [quittingAbsolutePureTime, hmass]
  | some delay =>
      have hne : source.mark ≠ source.mark + delay := by
        dsimp [IsQuittingStrictlyLaterDelay] at hlater
        omega
      rw [quittingAbsolutePureTime,
        quittingPureTimeHazard_some_of_ne hne]
      simp [hmass]

/-- The local-gap hypothesis is exactly optimality of the selected pure
endpoint against the two screened endpoint values. -/
theorem selected_endpoint_value_ge_opposite
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    if source.selectedAction then
      quittingFixedOpponentsContinueReward reward
          (quittingProfileLiveRoot reward source.targetProfile) source.mover
          source.mark ≤
        quittingFixedOpponentsQuitValue reward
          (quittingProfileLiveRoot reward source.targetProfile) source.mover
          source.mark
    else
      quittingFixedOpponentsQuitValue reward
          (quittingProfileLiveRoot reward source.targetProfile) source.mover
          source.mark ≤
        quittingFixedOpponentsContinueReward reward
          (quittingProfileLiveRoot reward source.targetProfile) source.mover
  source.mark := by
  have hgap : 0 ≤
      quittingRootExpectedPayoff reward source.tail.1
          (Function.update
            (quittingProfileLiveRoot reward source.sourceProfile source.mark)
            source.mover (PMF.pure source.selectedAction)) source.mover -
        quittingRootExpectedPayoff reward source.tail.1
          (quittingProfileLiveRoot reward source.sourceProfile source.mark)
          source.mover := by
    simpa only [tail, quittingRootSuccessorPayoff] using
      source.selected_endpoint_gain_nonneg
  have hsourceMass : quittingStationaryContinueMass
      (quittingProfileLiveRoot reward source.sourceProfile source.mark) = 0 :=
    quittingStationaryContinueMass_of_sureQuitter source.source_other_quits
  have hselectedMass : quittingStationaryContinueMass
      (Function.update
        (quittingProfileLiveRoot reward source.sourceProfile source.mark)
        source.mover (PMF.pure source.selectedAction)) = 0 := by
    apply quittingStationaryContinueMass_of_sureQuitter
      (quitter := source.other)
    rw [Function.update_of_ne source.other_ne_mover]
    exact source.source_other_quits
  have hsourceUpdate : Function.update
      (quittingProfileLiveRoot reward source.sourceProfile source.mark)
        source.mover (PMF.pure (!source.selectedAction)) =
      quittingProfileLiveRoot reward source.sourceProfile source.mark :=
    Function.update_eq_self_iff.mpr source.source_mover_opposite.symm
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    hselectedMass, hsourceMass] at hgap
  simp only [zero_mul, add_zero] at hgap
  have htargetRoot := quittingProfileLiveRoot_literalOneDateProfile
    reward source.sourceProfile source.mover source.mark source.selectedAction
  change quittingProfileLiveRoot reward source.targetProfile source.mark = _
    at htargetRoot
  cases haction : source.selectedAction with
  | false =>
      simp only [haction, Bool.not_false] at hsourceUpdate
      rw [← hsourceUpdate] at hgap
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp [haction, htargetRoot, quittingFixedOpponentsQuitValue,
        quittingFixedOpponentsContinueReward] at hgap ⊢
      exact hgap
  | true =>
      simp only [haction, Bool.not_true] at hsourceUpdate
      rw [← hsourceUpdate] at hgap
      simp only [eq_self, ↓reduceIte]
      simp [haction, htargetRoot, quittingFixedOpponentsQuitValue,
        quittingFixedOpponentsContinueReward] at hgap ⊢
      exact hgap

/-- A nonmover's unrestricted behavioral cap changes by at most twice the
reward bound times that nonmover's deleted reach through the marked prefix.
The controlling clock is opponent survival, not the smaller joint reach. -/
theorem abs_target_nonmoverCap_sub_source_le_deletedReach
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (observer : ι) (_hobserver : observer ≠ source.mover)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingContinuationBestResponseValue reward source.targetProfile observer -
        quittingContinuationBestResponseValue reward source.sourceProfile observer| ≤
      2 * M * quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward source.sourceProfile) observer 0
        source.mark := by
  rw [quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot,
    quittingContinuationBestResponseValue_eq_rootSequence_profileLiveRoot]
  exact abs_quittingRootSequenceBestResponseValue_sub_le_of_prefix_eq
    reward (quittingProfileLiveRoot reward source.targetProfile)
      (quittingProfileLiveRoot reward source.sourceProfile) observer source.mark
      hreward (fun time htime ↦ source.targetProfile_liveRoot_eq_of_lt htime)

/-- The actual joint reach through the marked prefix is exactly one player's
own prescribed survival times that player's deleted reach. -/
theorem source_liveMass_eq_ownSurvival_mul_deletedReach
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (observer : ι) :
    quittingLiveMass reward source.sourceProfile source.mark =
      quittingHazardSurvival
          (quittingBehaviorLiveHazard reward
            (source.sourceProfile observer)) source.mark *
        quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward source.sourceProfile) observer 0
          source.mark := by
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingJointSurvivalWeight_eq_prod]
  have hbridge := quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own
    (quittingProfileLiveRoot reward source.sourceProfile) observer source.mark
  unfold quittingSurvivalPrefix at hbridge
  simp only [Nat.zero_add] at hbridge ⊢
  rw [hbridge, quittingHazardSurvival_eq_prod]
  simp only [quittingBehaviorLiveHazard, quittingProfileLiveRoot]
  ring

/-- Opponent survival past the screened mark is zero. -/
theorem target_opponentSurvivalWeight_eq_zero_of_mark_lt
    (source : QuittingActualReachedScreenedEndpointMark reward)
    {time : ℕ} (htime : source.mark < time) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward source.targetProfile) source.mover 0
        time = 0 := by
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_eq_zero (Finset.mem_range.mpr htime)
  simpa using source.target_fixedOpponentsContinueMass_eq_zero

/-- Any positive paid row on the screened target starts no later than the
mark.  Strictness additionally uses support of the row's source clock. -/
theorem paidRow_start_le_mark
    (source : QuittingActualReachedScreenedEndpointMark reward)
    {gain : ℝ} (hgain : 0 < gain)
    (row : QuittingPaidFirstDisagreementRow reward source.targetProfile
      source.mover gain) :
    row.start ≤ source.mark := by
  by_contra hnot
  have hmark : source.mark < row.start := Nat.lt_of_not_ge hnot
  have hlive : row.liveMass = 0 := by
    rw [row.liveMass_eq]
    exact source.target_opponentSurvivalWeight_eq_zero_of_mark_lt hmark
  have hpaid := row.gain_le_paid
  rw [hlive, zero_mul] at hpaid
  linarith

/-- The target mover's actual live hazard is the selected pure endpoint at
the mark. -/
theorem target_hazard_at_mark
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    quittingBehaviorLiveHazard reward
        (source.targetProfile source.mover) source.mark =
      PMF.pure source.selectedAction := by
  change quittingProfileLiveRoot reward source.targetProfile source.mark
      source.mover = PMF.pure source.selectedAction
  rw [targetProfile, quittingProfileLiveRoot_literalOneDateProfile]
  simp

private theorem target_stoppingLaw_some_mark_not_mem_of_continue
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (haction : source.selectedAction = false) :
    some source.mark ∉
      (quittingBehaviorStoppingLaw reward
        (source.targetProfile source.mover)).support := by
  rw [PMF.mem_support_iff]
  intro hne
  have hreal :
      (quittingBehaviorStoppingLaw reward
        (source.targetProfile source.mover) (some source.mark)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hne, PMF.apply_ne_top _ _⟩
  rw [quittingBehaviorStoppingLaw_some_toReal,
    quittingHazardStopMass_eq_survival_mul_stop,
    source.target_hazard_at_mark, haction] at hreal
  simp at hreal

private theorem target_hazardSurvival_eq_zero_of_quit
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (haction : source.selectedAction = true) {time : ℕ}
    (htime : source.mark < time) :
    quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (source.targetProfile source.mover))
        time = 0 := by
  have hmark :
      quittingHazardSurvival
          (quittingBehaviorLiveHazard reward
            (source.targetProfile source.mover))
          (source.mark + 1) = 0 := by
    rw [quittingHazardSurvival_succ, source.target_hazard_at_mark, haction]
    simp
  have hanti := antitone_quittingHazardSurvival
    (quittingBehaviorLiveHazard reward (source.targetProfile source.mover))
  have hle := hanti (Nat.succ_le_iff.mpr htime)
  have hnonneg := quittingHazardSurvival_nonneg
    (quittingBehaviorLiveHazard reward (source.targetProfile source.mover)) time
  rw [hmark] at hle
  linarith

private theorem target_stoppingLaw_later_not_mem_of_quit
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (haction : source.selectedAction = true) (later : Option ℕ)
    (hlater : IsQuittingStrictlyLaterDelay later) :
    quittingAbsolutePureTime source.mark later ∉
      (quittingBehaviorStoppingLaw reward
        (source.targetProfile source.mover)).support := by
  rw [PMF.mem_support_iff]
  intro hne
  have hreal :
      (quittingBehaviorStoppingLaw reward
        (source.targetProfile source.mover)
          (quittingAbsolutePureTime source.mark later)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hne, PMF.apply_ne_top _ _⟩
  cases later with
  | none =>
      rw [quittingAbsolutePureTime,
        quittingBehaviorStoppingLaw_none_toReal] at hreal
      have hle := quittingHazardNeverMass_le_survival
        (quittingBehaviorLiveHazard reward (source.targetProfile source.mover))
        (source.mark + 1)
      have hzero := source.target_hazardSurvival_eq_zero_of_quit haction
        (show source.mark < source.mark + 1 by omega)
      have hnonneg := quittingHazardNeverMass_nonneg
        (quittingBehaviorLiveHazard reward (source.targetProfile source.mover))
      rw [hzero] at hle
      have : quittingHazardNeverMass
          (quittingBehaviorLiveHazard reward
            (source.targetProfile source.mover)) = 0 := by
        linarith
      exact hreal this
  | some delay =>
      have hdelay : 0 < delay := hlater
      rw [quittingAbsolutePureTime,
        quittingBehaviorStoppingLaw_some_toReal,
        quittingHazardStopMass_eq_survival_mul_stop,
        source.target_hazardSurvival_eq_zero_of_quit haction (by omega),
        zero_mul] at hreal
      exact hreal rfl

/-- A positive paid row whose source clock is supported by the target's
actual stopping law starts strictly before the screened mark. -/
theorem paidRow_start_lt_mark_of_sourceWitness_mem_support
    (source : QuittingActualReachedScreenedEndpointMark reward)
    {gain : ℝ} (hgain : 0 < gain)
    (row : QuittingPaidFirstDisagreementRow reward source.targetProfile
      source.mover gain)
    (hsource : row.sourceWitness ∈
      (quittingBehaviorStoppingLaw reward
        (source.targetProfile source.mover)).support) :
    row.start < source.mark := by
  have hle := source.paidRow_start_le_mark hgain row
  apply lt_of_le_of_ne hle
  intro hmark
  have hstart : row.start = source.mark := le_antisymm hle (by omega)
  have hlive0 : 0 ≤ row.liveMass := by
    rw [row.liveMass_eq]
    exact quittingOpponentSurvivalWeight_nonneg _ _ _ _
  cases hreceiving : row.receivingEarlier with
  | false =>
      have hchronology := row.chronology
      rw [hreceiving] at hchronology
      simp only [Bool.false_eq_true, ↓reduceIte] at hchronology
      rcases hchronology with ⟨hsourceWitness, hreceivingWitness⟩
      rw [hstart] at hsourceWitness
      cases haction : source.selectedAction with
      | false =>
          exact source.target_stoppingLaw_some_mark_not_mem_of_continue
            haction (hsourceWitness ▸ hsource)
      | true =>
          have hrelative := source.target_relativePureTimeValue_eq_continueReward
            row.later row.later_strict
          have hselected := source.selected_endpoint_value_ge_opposite
          rw [haction] at hselected
          simp only [eq_self, ↓reduceIte] at hselected
          have hreached := row.reachedGain_eq
          rw [hreceiving, hstart] at hreached
          simp only [Bool.false_eq_true, ↓reduceIte] at hreached
          rw [hrelative] at hreached
          have hreachedNonpos : row.reachedGain ≤ 0 := by linarith
          have hpaid : row.liveMass * row.reachedGain ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hlive0 hreachedNonpos
          linarith [row.gain_le_paid]
  | true =>
      have hchronology := row.chronology
      rw [hreceiving] at hchronology
      simp only [eq_self, ↓reduceIte] at hchronology
      rcases hchronology with ⟨hreceivingWitness, hsourceWitness⟩
      rw [hstart] at hsourceWitness
      cases haction : source.selectedAction with
      | false =>
          have hrelative := source.target_relativePureTimeValue_eq_continueReward
            row.later row.later_strict
          have hselected := source.selected_endpoint_value_ge_opposite
          rw [haction] at hselected
          simp only [Bool.false_eq_true, ↓reduceIte] at hselected
          have hreached := row.reachedGain_eq
          rw [hreceiving, hstart] at hreached
          simp only [eq_self, ↓reduceIte] at hreached
          rw [hrelative] at hreached
          have hreachedNonpos : row.reachedGain ≤ 0 := by linarith
          have hpaid : row.liveMass * row.reachedGain ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hlive0 hreachedNonpos
          linarith [row.gain_le_paid]
      | true =>
          exact source.target_stoppingLaw_later_not_mem_of_quit haction
            row.later row.later_strict (hsourceWitness ▸ hsource)

/-- A source-supported paid row localized strictly before the screened mark,
with the selector's literal own/opponent/joint reach floors. -/
structure StrictEarlierPaidRow
    (source : QuittingActualReachedScreenedEndpointMark reward) (M : ℝ) where
  row : QuittingPaidFirstDisagreementRow reward source.targetProfile
    source.mover (source.premarkResidual / 4)
  sourceWitness_mem : row.sourceWitness ∈
    (quittingBehaviorStoppingLaw reward
      (source.targetProfile source.mover)).support
  start_lt_mark : row.start < source.mark
  paidGain_floor : source.premarkResidual / 4 ≤
    quittingPureTimeDeviationPayoff reward source.targetProfile source.mover
        row.receivingWitness -
      quittingPureTimeDeviationPayoff reward source.targetProfile source.mover
        row.sourceWitness
  ownSurvival_floor : source.premarkResidual ≤
    4 * M * quittingHazardSurvival
      (quittingBehaviorLiveHazard reward
        (source.targetProfile source.mover)) row.start
  opponentReach_floor : source.premarkResidual ≤ 8 * M * row.liveMass
  jointReach_floor : source.premarkResidual * source.premarkResidual ≤
    32 * M * M * quittingSurvivalPrefix
      (quittingProfileLiveRoot reward source.targetProfile) row.start

/-- Positive premark residual debt produces an actual supported paid row
strictly before the mark, with the checked reach and gain constants. -/
theorem exists_strictEarlierPaidRow_of_premarkResidual_pos
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hresidual : 0 < source.premarkResidual) :
    Nonempty (StrictEarlierPaidRow source M) := by
  have hdebt : source.premarkResidual ≤
      quittingContinuationBestResponseValue reward source.targetProfile
          source.mover -
        quittingTerminalPayoff reward source.targetProfile source.mover := by
    rw [← source.target_mover_debt_eq_premarkResidual]
    rfl
  obtain ⟨row, hsource, hown, hopponent, hjoint⟩ :=
    positiveDebt_exists_actualJointReach_paidRow_mem_support reward
      source.targetProfile source.mover M source.premarkResidual hreward
      hresidual hdebt
  refine ⟨{
    row := row
    sourceWitness_mem := hsource
    start_lt_mark := source.paidRow_start_lt_mark_of_sourceWitness_mem_support
      (by linarith) row hsource
    paidGain_floor := ?_
    ownSurvival_floor := hown
    opponentReach_floor := hopponent
    jointReach_floor := hjoint }⟩
  rw [row.edge_identity]
  exact row.gain_le_paid

/-- The literal target either kills the mover's complete debt or exposes a
source-supported paid row strictly before the screened mark. -/
theorem premarkResidual_eq_zero_or_nonempty_strictEarlierPaidRow
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    source.premarkResidual = 0 ∨ Nonempty (StrictEarlierPaidRow source M) := by
  have hnonneg : 0 ≤ source.premarkResidual := by
    rw [← source.target_mover_debt_eq_premarkResidual]
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingTerminalSemanticPair_mem_carrier reward source.targetProfile)
      source.mover
  by_cases hzero : source.premarkResidual = 0
  · exact Or.inl hzero
  · exact Or.inr (source.exists_strictEarlierPaidRow_of_premarkResidual_pos
      M hreward (lt_of_le_of_ne hnonneg (Ne.symm hzero)))

/-- Direct cap-port attachment for the strictly earlier paid row.  The
global minimum is supplied separately; the literal marked target is not
asserted to be a minimum. -/
theorem exists_strictEarlierPaidRow_and_capPortTrichotomy
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hresidual : 0 < source.premarkResidual)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ paid : StrictEarlierPaidRow source M,
      ∃ (capSource : QuittingPaidCapLiftedSource reward)
        (port : capSource.SummablePort),
        capSource.minimum = minimum ∧
          minimum ∈ quittingTerminalSemanticCarrier reward ∧
          capSource.profile = source.targetProfile ∧
          capSource.observer = source.mover ∧
          capSource.gain = source.premarkResidual / 4 ∧
          HEq capSource.row paid.row ∧
          (capSource.ChargedNearReturn port ∨
            capSource.QuantitativeDebtDescent port ∨
            capSource.InertStall port) := by
  obtain ⟨paid⟩ := source.exists_strictEarlierPaidRow_of_premarkResidual_pos
    M hreward hresidual
  let capSource : QuittingPaidCapLiftedSource reward :=
    { minimum := minimum
      minimum_le := hminimum
      minimum_pos := hminimumPos
      profile := source.targetProfile
      observer := source.mover
      gain := source.premarkResidual / 4
      gain_pos := by linarith
      row := paid.row }
  obtain ⟨port⟩ := capSource.nonempty_summablePort
  have hrow : HEq capSource.row paid.row := by
    exact HEq.rfl
  refine ⟨paid, capSource, port, rfl, hminimumMem, rfl, rfl, rfl, hrow, ?_⟩
  exact capSource.chargedNearReturn_or_quantitativeDebtDescent_or_inertStall port

/-- Complete killed-or-paid dispatch.  The zero arm is literal mover-debt
annihilation; the positive arm retains the strict-earlier paid row and the
separately supplied attained positive global minimum used by the cap port. -/
theorem target_mover_debt_eq_zero_or_strictEarlierPaidRow_capPortTrichotomy
    (source : QuittingActualReachedScreenedEndpointMark reward)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source.targetProfile)
          source.mover = 0 ∨
      ∃ paid : StrictEarlierPaidRow source M,
        ∃ (capSource : QuittingPaidCapLiftedSource reward)
          (port : capSource.SummablePort),
          capSource.minimum = minimum ∧
            minimum ∈ quittingTerminalSemanticCarrier reward ∧
            capSource.profile = source.targetProfile ∧
            capSource.observer = source.mover ∧
            capSource.gain = source.premarkResidual / 4 ∧
            HEq capSource.row paid.row ∧
            (capSource.ChargedNearReturn port ∨
              capSource.QuantitativeDebtDescent port ∨
              capSource.InertStall port) := by
  have hnonneg : 0 ≤ source.premarkResidual := by
    rw [← source.target_mover_debt_eq_premarkResidual]
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingTerminalSemanticPair_mem_carrier reward source.targetProfile)
      source.mover
  by_cases hzero : source.premarkResidual = 0
  · left
    rw [source.target_mover_debt_eq_premarkResidual, hzero]
  · right
    have hresidual : 0 < source.premarkResidual :=
      lt_of_le_of_ne hnonneg (Ne.symm hzero)
    exact source.exists_strictEarlierPaidRow_and_capPortTrichotomy M hreward
      hresidual minimum hminimumMem hminimum hminimumPos

/-! ## Pure nonempty-host law and restricted premark envelope -/

/-- The specialization needed for the signed terminal-law statement: the
screened marked root is literally a pure nonempty coalition.  The screening
player witnesses that routing the mover leaves a nonempty coalition even
when the selected action is Continue. -/
structure PurePairData
    (source : QuittingActualReachedScreenedEndpointMark reward) where
  coalition : Finset ι
  coalition_nonempty : coalition.Nonempty
  source_root_eq :
    quittingProfileLiveRoot reward source.sourceProfile source.mark =
      quittingPureSetRoot coalition

namespace PurePairData

variable {source : QuittingActualReachedScreenedEndpointMark reward}

/-- The pure terminal coalition selected by the marked endpoint. -/
def sourceTerminal (data : PurePairData source) :
    {S : Finset ι // S.Nonempty} :=
  ⟨data.coalition, data.coalition_nonempty⟩

/-- The pure terminal coalition after the mover is routed to the selected
endpoint. -/
def targetTerminal (data : PurePairData source) :
    {S : Finset ι // S.Nonempty} :=
  ⟨quittingPureEndpointRoutedCoalition data.coalition source.mover
      source.selectedAction,
    by
      cases haction : source.selectedAction with
      | true => simp [quittingPureEndpointRoutedCoalition]
      | false =>
          have hother : source.other ∈ data.coalition := by
            have hroot := source.source_other_quits
            rw [data.source_root_eq] at hroot
            have hmass := congrArg (fun law : PMF Bool => law true) hroot
            by_contra hnot
            simp [quittingPureSetRoot, quittingSetAction, hnot] at hmass
          exact ⟨source.other, by
            simp [quittingPureEndpointRoutedCoalition,
              hother, source.other_ne_mover]⟩⟩

/-- A pure-set root assigns mass one to its displayed coalition and zero to
every other coalition. -/
theorem quittingRootCoalitionMass_pureSetRoot
    (coalition terminal : Finset ι) :
    quittingRootCoalitionMass (quittingPureSetRoot coalition) terminal =
      if terminal = coalition then 1 else 0 := by
  rw [quittingRootCoalitionMass_eq_pmfPi]
  change ((pmfPi (fun player : ι =>
    PMF.pure (quittingSetAction coalition player)))
      (quittingCoalitionAction terminal)).toReal = _
  rw [pmfPi_pure]
  by_cases heq : terminal = coalition
  · subst terminal
    have haction : quittingCoalitionAction coalition =
        quittingSetAction coalition := by
      funext player
      simp [quittingCoalitionAction, quittingSetAction]
    rw [haction]
    simp
  · have haction : quittingCoalitionAction terminal ≠
        quittingSetAction coalition := by
      intro h
      apply heq
      ext player
      simpa [quittingCoalitionAction, quittingSetAction] using
        congrFun h player
    simp [PMF.pure_apply, haction, heq]

/-- The source root at the mark absorbs surely. -/
theorem source_continueMass_at_mark_eq_zero (data : PurePairData source) :
    quittingStationaryContinueMass
        (quittingProfileLiveRoot reward source.sourceProfile source.mark) = 0 := by
  rw [data.source_root_eq]
  obtain ⟨quitter, hquitter⟩ := data.coalition_nonempty
  apply quittingStationaryContinueMass_of_sureQuitter (quitter := quitter)
  simp [quittingPureSetRoot, quittingSetAction, hquitter]

/-- The target root is the pure coalition obtained by routing the mover's
selected endpoint. -/
theorem target_root_eq_pureSetRoot_routed (data : PurePairData source) :
    quittingProfileLiveRoot reward source.targetProfile source.mark =
      quittingPureSetRoot data.targetTerminal.val := by
  rw [targetProfile, quittingProfileLiveRoot_literalOneDateProfile,
    data.source_root_eq]
  funext player
  by_cases hplayer : player = source.mover
  · subst player
    cases haction : source.selectedAction <;>
      simp [targetTerminal, quittingPureSetRoot,
        quittingPureEndpointRoutedCoalition, quittingSetAction, haction]
  · rw [Function.update_of_ne hplayer]
    cases haction : source.selectedAction <;>
      simp [targetTerminal, quittingPureSetRoot,
        quittingPureEndpointRoutedCoalition, quittingSetAction, haction,
        hplayer]

/-- The target root at the mark also absorbs surely. -/
theorem target_continueMass_at_mark_eq_zero (data : PurePairData source) :
    quittingStationaryContinueMass
        (quittingProfileLiveRoot reward source.targetProfile source.mark) = 0 := by
  rw [data.target_root_eq_pureSetRoot_routed]
  obtain ⟨quitter, hquitter⟩ := data.targetTerminal.property
  apply quittingStationaryContinueMass_of_sureQuitter (quitter := quitter)
  simp [quittingPureSetRoot, quittingSetAction, hquitter]

/-- The selected endpoint really toggles the mover's membership, so the two
terminal coalitions in the signed law are distinct. -/
theorem targetTerminal_ne_sourceTerminal (data : PurePairData source) :
    data.targetTerminal ≠ data.sourceTerminal := by
  intro heq
  have hval : data.targetTerminal.val = data.sourceTerminal.val :=
    congrArg Subtype.val heq
  cases haction : source.selectedAction with
  | false =>
      have hmem : source.mover ∈ data.coalition := by
        by_contra hnot
        have hopposite := source.source_mover_opposite
        rw [data.source_root_eq] at hopposite
        have himpossible := congrArg (fun law : PMF Bool => law true) hopposite
        simp [quittingPureSetRoot, quittingSetAction, haction, hnot] at himpossible
      have : source.mover ∉ data.targetTerminal.val := by
        simp [targetTerminal, quittingPureEndpointRoutedCoalition, haction]
      apply this
      rw [hval]
      exact hmem
  | true =>
      have hnot : source.mover ∉ data.coalition := by
        intro hmem
        have hopposite := source.source_mover_opposite
        rw [data.source_root_eq] at hopposite
        have himpossible := congrArg (fun law : PMF Bool => law true) hopposite
        simp [quittingPureSetRoot, quittingSetAction, haction, hmem] at himpossible
      have : source.mover ∈ data.targetTerminal.val := by
        simp [targetTerminal, quittingPureEndpointRoutedCoalition, haction]
      apply hnot
      change source.mover ∈ data.sourceTerminal.val
      rw [← hval]
      exact this

omit [DecidableEq ι] in
private theorem liveMass_succ_mark_eq_zero_of_sureQuitter
    (profile : (quittingGame reward).BehaviorProfile)
    (quitter : ι) (mark : ℕ)
    (hsure : quittingProfileLiveRoot reward profile mark quitter =
      PMF.pure true) :
    quittingLiveMass reward profile (mark + 1) = 0 := by
  rw [quittingLiveMass_succ, quittingJointContinueMass_eq_product]
  have hproduct : (∏ player,
      ((profile player mark (quittingLiveHist reward mark)) false).toReal) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ quitter)
    change ((quittingProfileLiveRoot reward profile mark quitter) false).toReal = 0
    rw [hsure]
    simp
  rw [hproduct, mul_zero]

private theorem stageCoalitionMass_eq_zero_after_sureQuitter
    (profile : (quittingGame reward).BehaviorProfile)
    (quitter : ι) (mark : ℕ)
    (hsure : quittingProfileLiveRoot reward profile mark quitter =
      PMF.pure true)
    (terminal : {S : Finset ι // S.Nonempty})
    (time : ℕ) (htime : mark + 1 ≤ time) :
    quittingStageCoalitionMass reward profile time terminal = 0 := by
  have hzero := liveMass_succ_mark_eq_zero_of_sureQuitter
    profile quitter mark hsure
  have hle := quittingLiveMass_antitone reward profile htime
  have hnonneg := quittingLiveMass_nonneg reward profile time
  have hlive : quittingLiveMass reward profile time = 0 := by
    rw [hzero] at hle
    linarith
  unfold quittingStageCoalitionMass
  rw [hlive, zero_mul]

/-- The literal pure-pair toggle moves exactly the marked unconditional mass
from the source coalition to the routed coalition.  The formula includes the
Never coordinate. -/
theorem target_terminalOutcomeMass_eq_add_dirac_sub_dirac
    (data : PurePairData source)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward source.targetProfile outcome =
      quittingTerminalOutcomeMass reward source.sourceProfile outcome +
        quittingLiveMass reward source.sourceProfile source.mark *
          (if outcome = some data.targetTerminal then 1 else 0) -
        quittingLiveMass reward source.sourceProfile source.mark *
          (if outcome = some data.sourceTerminal then 1 else 0) := by
  cases outcome with
  | none =>
      have hsource := quittingLiveMassLimit_eq_zero_of_live_sureQuitter
        reward source.sourceProfile source.other source.mark
        source.source_other_quits
      have htarget := quittingLiveMassLimit_eq_zero_of_live_sureQuitter
        reward source.targetProfile source.other source.mark
        source.target_other_quits
      change quittingLiveMassLimit reward source.targetProfile =
        quittingLiveMassLimit reward source.sourceProfile + _ - _
      simp [hsource, htarget]
  | some terminal =>
      have hsourceLimit :=
        quittingAbsorbedMassLimit_eq_absorbedMass_of_stage_zero_after
          reward source.sourceProfile terminal (source.mark + 1)
          (fun time htime => stageCoalitionMass_eq_zero_after_sureQuitter
            source.sourceProfile source.other source.mark
            source.source_other_quits terminal time htime)
      have htargetLimit :=
        quittingAbsorbedMassLimit_eq_absorbedMass_of_stage_zero_after
          reward source.targetProfile terminal (source.mark + 1)
          (fun time htime => stageCoalitionMass_eq_zero_after_sureQuitter
            source.targetProfile source.other source.mark
            source.target_other_quits terminal time htime)
      change quittingAbsorbedMassLimit reward source.targetProfile terminal =
        quittingAbsorbedMassLimit reward source.sourceProfile terminal + _ - _
      rw [hsourceLimit, htargetLimit,
        quittingAbsorbedMass_succ_eq_add_stageCoalitionMass,
        quittingAbsorbedMass_succ_eq_add_stageCoalitionMass]
      have habsorbed : quittingAbsorbedMass reward source.targetProfile
          source.mark terminal =
          quittingAbsorbedMass reward source.sourceProfile source.mark terminal := by
        rw [quittingAbsorbedMass_eq_sum_stageCoalitionMass,
          quittingAbsorbedMass_eq_sum_stageCoalitionMass]
        apply Finset.sum_congr rfl
        intro time htime
        apply quittingStageCoalitionMass_eq_of_liveRoot_eq_of_le
        intro earlier hearlier
        exact source.targetProfile_liveRoot_eq_of_lt
          (lt_of_le_of_lt hearlier (Finset.mem_range.mp htime))
      rw [habsorbed]
      have hlive : quittingLiveMass reward source.targetProfile source.mark =
          quittingLiveMass reward source.sourceProfile source.mark :=
        quittingLiveMass_eq_of_liveRoot_eq_of_lt reward _ _ source.mark
          (fun time htime => source.targetProfile_liveRoot_eq_of_lt htime)
      rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
        quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
        hlive, data.target_root_eq_pureSetRoot_routed, data.source_root_eq,
        quittingRootCoalitionMass_pureSetRoot,
        quittingRootCoalitionMass_pureSetRoot]
      dsimp only [targetTerminal, sourceTerminal]
      simp only [Option.some.injEq, Subtype.ext_iff]
      have hdistinct : quittingPureEndpointRoutedCoalition data.coalition
          source.mover source.selectedAction ≠ data.coalition := by
        intro heq
        apply data.targetTerminal_ne_sourceTerminal
        exact Subtype.ext heq
      by_cases htarget : terminal.val =
          quittingPureEndpointRoutedCoalition data.coalition source.mover
            source.selectedAction
      · have hsource : terminal.val ≠ data.coalition := by
          intro heq
          exact hdistinct (htarget.symm.trans heq)
        simp [htarget, hdistinct]
      · by_cases hsource : terminal.val = data.coalition
        · simp [hsource, Ne.symm hdistinct]
        · simp [htarget, hsource]

/-- A unilateral response is premark-restricted when its literal action at
every canonical live history before the mark is unchanged. -/
def AgreesOnLiveHistoryBeforeMark
    (deviation : (quittingGame reward).BehaviorStrategy source.mover) : Prop :=
  ∀ time < source.mark,
    deviation time (quittingLiveHist reward time) =
      source.sourceProfile source.mover time (quittingLiveHist reward time)

/-- A premark-restricted response has the same complete live roots as the
selected target strictly before the mark. -/
theorem update_liveRoot_eq_target_of_lt
    (deviation : (quittingGame reward).BehaviorStrategy source.mover)
    (hagrees : AgreesOnLiveHistoryBeforeMark (source := source) deviation)
    {time : ℕ} (htime : time < source.mark) :
    quittingProfileLiveRoot reward
        (Function.update source.sourceProfile source.mover deviation) time =
      quittingProfileLiveRoot reward source.targetProfile time := by
  rw [source.targetProfile_liveRoot_eq_of_lt htime]
  funext player
  by_cases hplayer : player = source.mover
  · subst player
    unfold quittingProfileLiveRoot
    rw [Function.update_self]
    simpa [quittingGame] using hagrees time htime
  · simp [quittingProfileLiveRoot, hplayer]

/-- At the marked row an arbitrary restricted response differs from the
selected target only in the mover's current marginal. -/
theorem update_liveRoot_mark_eq_update_target
    (deviation : (quittingGame reward).BehaviorStrategy source.mover) :
    quittingProfileLiveRoot reward
        (Function.update source.sourceProfile source.mover deviation)
        source.mark =
      Function.update
        (quittingProfileLiveRoot reward source.targetProfile source.mark)
        source.mover
        (deviation source.mark (quittingLiveHist reward source.mark)) := by
  rw [targetProfile, quittingProfileLiveRoot_literalOneDateProfile]
  funext player
  by_cases hplayer : player = source.mover
  · subst player
    simp [quittingProfileLiveRoot]
  · simp [quittingProfileLiveRoot, hplayer]

private theorem arbitrary_marginal_absorbingContribution_le_selected
    (marginal : PMF Bool) :
    quittingRootAbsorbingContribution reward
        (Function.update
          (quittingProfileLiveRoot reward source.targetProfile source.mark)
          source.mover marginal) source.mover ≤
      quittingRootAbsorbingContribution reward
        (quittingProfileLiveRoot reward source.targetProfile source.mark)
        source.mover := by
  let root := quittingProfileLiveRoot reward source.targetProfile source.mark
  let quitValue := quittingFixedOpponentsQuitValue reward
    (quittingProfileLiveRoot reward source.targetProfile) source.mover source.mark
  let continueValue := quittingFixedOpponentsContinueReward reward
    (quittingProfileLiveRoot reward source.targetProfile) source.mover source.mark
  have hmix := quittingRootExpectedPayoff_update_eq_endpointMix
    reward (fun _ => 0) root source.mover marginal
  have hleft : quittingRootExpectedPayoff reward (fun _ => 0)
      (Function.update root source.mover marginal) source.mover =
      quittingRootAbsorbingContribution reward
        (Function.update root source.mover marginal) source.mover := by
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
    simp
  have hbase : quittingRootExpectedPayoff reward (fun _ => 0) root source.mover =
      quittingRootAbsorbingContribution reward root source.mover := by
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
    simp
  have hquit : quittingRootQuitPayoff reward (fun _ => 0) root source.mover =
      quitValue := by
    unfold quittingRootQuitPayoff quitValue quittingFixedOpponentsQuitValue
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
    simp [root]
  have hcontinue : quittingRootContinuePayoff reward (fun _ => 0) root
      source.mover = continueValue := by
    unfold quittingRootContinuePayoff continueValue
      quittingFixedOpponentsContinueReward
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
    simp [root]
  have hsum : (marginal true).toReal + (marginal false).toReal = 1 := by
    simpa [Fintype.sum_bool] using Math.Probability.pmf_toReal_sum_one marginal
  have htrue : 0 ≤ (marginal true).toReal := ENNReal.toReal_nonneg
  have hfalse : 0 ≤ (marginal false).toReal := ENNReal.toReal_nonneg
  have hselected := source.selected_endpoint_value_ge_opposite
  change quittingRootAbsorbingContribution reward
      (Function.update root source.mover marginal) source.mover ≤
    quittingRootAbsorbingContribution reward root source.mover
  rw [← hleft]
  change quittingRootExpectedPayoff reward (fun _ => 0)
      (Function.update root source.mover marginal) source.mover ≤ _
  rw [hmix, hquit, hcontinue]
  cases haction : source.selectedAction with
  | false =>
      rw [haction] at hselected
      simp only [Bool.false_eq_true, ↓reduceIte] at hselected
      change quitValue ≤ continueValue at hselected
      have hroot : root source.mover = PMF.pure false := by
        simpa [root, quittingBehaviorLiveHazard, quittingProfileLiveRoot,
          quittingGame, haction] using
          source.target_hazard_at_mark
      rw [show quittingRootAbsorbingContribution reward root source.mover =
          continueValue by
        calc
          quittingRootAbsorbingContribution reward root source.mover =
              quittingRootExpectedPayoff reward (fun _ => 0) root source.mover :=
            hbase.symm
          _ = quittingRootExpectedPayoff reward (fun _ => 0)
                (Function.update root source.mover (PMF.pure false))
                source.mover := by
            rw [Function.update_eq_self_iff.mpr hroot.symm]
          _ = continueValue := hcontinue]
      calc
        (marginal true).toReal * quitValue +
            (marginal false).toReal * continueValue ≤
            (marginal true).toReal * continueValue +
              (marginal false).toReal * continueValue :=
          add_le_add (mul_le_mul_of_nonneg_left hselected htrue) le_rfl
        _ = continueValue := by rw [← add_mul, hsum, one_mul]
  | true =>
      rw [haction] at hselected
      simp only [eq_self, ↓reduceIte] at hselected
      change continueValue ≤ quitValue at hselected
      have hroot : root source.mover = PMF.pure true := by
        simpa [root, quittingBehaviorLiveHazard, quittingProfileLiveRoot,
          quittingGame, haction] using
          source.target_hazard_at_mark
      rw [show quittingRootAbsorbingContribution reward root source.mover =
          quitValue by
        calc
          quittingRootAbsorbingContribution reward root source.mover =
              quittingRootExpectedPayoff reward (fun _ => 0) root source.mover :=
            hbase.symm
          _ = quittingRootExpectedPayoff reward (fun _ => 0)
                (Function.update root source.mover (PMF.pure true))
                source.mover := by
            rw [Function.update_eq_self_iff.mpr hroot.symm]
          _ = quitValue := hquit]
      calc
        (marginal true).toReal * quitValue +
            (marginal false).toReal * continueValue ≤
            (marginal true).toReal * quitValue +
              (marginal false).toReal * quitValue :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hselected hfalse)
        _ = quitValue := by rw [← add_mul, hsum, one_mul]

/-- Every unilateral response which agrees with the source at all canonical
live histories before the mark is bounded by the literal selected endpoint
profile.  Together with the selected profile itself, this is the exact
restricted response envelope, without replacing the prefix by a normalized
date-zero model. -/
theorem restrictedResponse_terminalPayoff_le_target
    (deviation : (quittingGame reward).BehaviorStrategy source.mover)
    (hagrees : AgreesOnLiveHistoryBeforeMark (source := source) deviation) :
    quittingTerminalPayoff reward
        (Function.update source.sourceProfile source.mover deviation)
        source.mover ≤
      quittingTerminalPayoff reward source.targetProfile source.mover := by
  let deviated := Function.update source.sourceProfile source.mover deviation
  let x := quittingProfileLiveRoot reward source.targetProfile
  let y := quittingProfileLiveRoot reward deviated
  have hprefix : ∀ time, time < source.mark → x time = y time := by
    intro time htime
    exact (update_liveRoot_eq_target_of_lt (source := source)
      deviation hagrees htime).symm
  have hscale := quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
    reward x y source.mover source.mark hprefix
  have hyRoot : y source.mark = Function.update (x source.mark) source.mover
      (deviation source.mark (quittingLiveHist reward source.mark)) := by
    exact update_liveRoot_mark_eq_update_target (source := source) deviation
  have hxMass : quittingStationaryContinueMass (x source.mark) = 0 := by
    apply quittingStationaryContinueMass_of_sureQuitter
      (quitter := source.other)
    exact source.target_other_quits
  have hyMass : quittingStationaryContinueMass (y source.mark) = 0 := by
    rw [hyRoot]
    apply quittingStationaryContinueMass_of_sureQuitter
      (quitter := source.other)
    rw [Function.update_of_ne source.other_ne_mover]
    exact source.target_other_quits
  have htail : quittingRootSequenceTerminalValue reward x source.mover
        source.mark -
      quittingRootSequenceTerminalValue reward y source.mover source.mark ≥ 0 := by
    rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
        reward x source.mover source.mark,
      quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
        reward y source.mover source.mark,
      quittingRootSuccessorPayoff,
      quittingRootSuccessorPayoff,
      quittingRootExpectedPayoff_eq_absorbingContribution_add,
      quittingRootExpectedPayoff_eq_absorbingContribution_add,
      hxMass, hyMass, zero_mul, zero_mul, add_zero, add_zero, hyRoot]
    exact sub_nonneg.mpr
      (arbitrary_marginal_absorbingContribution_le_selected
        (source := source) _)
  have hsurvival := quittingJointSurvivalWeight_nonneg y 0 source.mark
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  change quittingRootSequenceTerminalValue reward y source.mover 0 ≤
    quittingRootSequenceTerminalValue reward x source.mover 0
  nlinarith [hscale]

/-- Exact restricted-envelope certificate.  The literal target strategy is
admissible, it pays the source value plus the positive part of the marked
gain, and it dominates every strategy satisfying the same premark live-path
restriction. -/
theorem restrictedResponse_exact_envelope
    (source : QuittingActualReachedScreenedEndpointMark reward) :
    AgreesOnLiveHistoryBeforeMark (source := source)
        (source.targetProfile source.mover) ∧
      quittingTerminalPayoff reward source.targetProfile source.mover =
        quittingTerminalPayoff reward source.sourceProfile source.mover +
          max 0 source.markedToggleGain ∧
      ∀ deviation : (quittingGame reward).BehaviorStrategy source.mover,
        AgreesOnLiveHistoryBeforeMark (source := source) deviation →
          quittingTerminalPayoff reward
              (Function.update source.sourceProfile source.mover deviation)
              source.mover ≤
            quittingTerminalPayoff reward source.targetProfile source.mover := by
  refine ⟨?_, ?_, ?_⟩
  · intro time htime
    unfold targetProfile quittingLiteralOneDateProfile
    rw [Function.update_self]
    exact congrFun (quittingLiteralOneDateOverride_of_ne
      (source.sourceProfile source.mover) source.mark time
      source.selectedAction (Nat.ne_of_lt htime))
      (quittingLiveHist reward time)
  · rw [max_eq_right source.markedToggleGain_nonneg]
    unfold markedToggleGain
    ring
  · intro deviation hagrees
    exact restrictedResponse_terminalPayoff_le_target
      (source := source) deviation hagrees

end PurePairData

end QuittingActualReachedScreenedEndpointMark

end GameTheory
