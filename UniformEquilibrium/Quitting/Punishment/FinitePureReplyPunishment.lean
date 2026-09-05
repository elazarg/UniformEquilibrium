import UniformEquilibrium.Quitting.Punishment.FinitePureReplyValue
import UniformEquilibrium.Quitting.Cycles.PeriodicFiniteReplyPrefix

/-! # Punishment with finite-date responses

Repeating actual opponent prefixes identifies the finite-date punishment
infimum, including signed rewards and nonabsorbing opponent plans.
-/

noncomputable section

namespace GameTheory

open Set Filter Math.Probability QuittingSureSetOwnerRepair
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A deleted survival limit of one forces the initial finite response to
deliver the own singleton. -/
theorem solo_le_finiteBound_of_opponentSurvival_tendsto_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {bound : ℝ}
    (hfinite : ∀ time, quittingRootSequencePureTimeTerminalValue
      reward roots who (some time) 0 ≤ bound)
    (hlimit : Tendsto (quittingOpponentSurvivalWeight roots who 0) atTop (nhds 1)) :
    quittingSoloReward reward who who ≤ bound := by
  have hfirst : 1 ≤ quittingOpponentSurvivalWeight roots who 0 1 := by
    apply le_of_tendsto hlimit
    filter_upwards [eventually_ge_atTop 1] with time htime
    exact antitone_quittingOpponentSurvivalWeight roots who 0 htime
  have hmass : quittingStationaryFixedOpponentsContinueMass (roots 0) who = 1 := by
    have h := le_antisymm (quittingOpponentSurvivalWeight_le_one roots who 0 1) hfirst
    simpa [quittingOpponentSurvivalWeight, quittingFixedOpponentsContinueMass,
      quittingStationaryFixedOpponentsContinueMass] using h
  have hroot : Function.update (roots 0) who (PMF.pure true) =
      quittingPureSetRoot ({who} : Finset ι) := by
    funext player
    by_cases hp : player = who
    · subst player
      simp [quittingPureSetRoot, quittingSetAction]
    · rw [Function.update_of_ne hp,
        eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one hmass player hp]
      simp [quittingPureSetRoot, quittingSetAction, hp]
  have h := hfinite 0
  simpa [quittingRootSequencePureTimeTerminalValue_some_eq, quittingLiveLedgerAccum,
    quittingOpponentSurvivalWeight, quittingFixedOpponentsQuitValue, hroot,
    quittingRootAbsorbingContribution_pureSetRoot,
    quittingSetReward_singleton_eq_soloReward, quittingSoloReward] using h

/-- A contracting deleted-survival limit allows signed finite-prefix repetition
to produce complete punishment profiles arbitrarily close to the finite bound. -/
theorem quittingPunishmentValue_le_of_finiteBound_and_renewalLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {bound survival : ℝ}
    (hfinite : ∀ time, quittingRootSequencePureTimeTerminalValue
      reward roots who (some time) 0 ≤ bound)
    (hlimit : Tendsto (quittingOpponentSurvivalWeight roots who 0)
      atTop (nhds survival))
    (hcontracts : survival < 1)
    (hrenewal : quittingRootSequencePureTimeTerminalValue reward roots who none 0 /
      (1 - survival) ≤ bound) :
    quittingPunishmentValue reward who ≤ bound := by
  apply le_of_forall_gt
  intro upper hupper
  have hquot := ((tendsto_quittingLiveLedgerAccum reward roots who).div
    (tendsto_const_nhds.sub hlimit) (by linarith : 1 - survival ≠ 0)).comp
      (tendsto_add_atTop_nat 1)
  have hsurvival := hlimit.comp (tendsto_add_atTop_nat 1)
  have hevent := (hsurvival.eventually (gt_mem_nhds hcontracts)).and
    (hquot.eventually (gt_mem_nhds (hrenewal.trans_lt hupper)))
  obtain ⟨window, hwindow⟩ := hevent.exists
  exact (quittingPunishmentValue_le reward who _).trans_lt
    ((quittingBestReplyValue_periodizedPrefix_le_max reward roots who window
      (fun phase ↦ hfinite phase.val) hwindow.1).trans_lt
        (max_lt hupper hwindow.2))

/-- Against complete opponents whose finite-date supremum lies below the own
singleton, finite-prefix repetition already bounds the full punishment value. -/
theorem quittingPunishmentValue_le_finitePureReplyValue_of_lt_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hsolo : quittingFinitePureReplyValue reward profile who <
      quittingSoloReward reward who who) :
    quittingPunishmentValue reward who ≤ quittingFinitePureReplyValue reward profile who := by
  let laws := quittingCompactStoppingLawsOfProfile reward profile
  let canonical := quittingCompactStoppingLawProfile reward laws
  let roots := quittingProfileLiveRoot reward canonical
  let survival := quittingOpponentNeverProduct laws who
  have hfinite : ∀ time, quittingRootSequencePureTimeTerminalValue
      reward roots who (some time) 0 ≤ quittingFinitePureReplyValue reward profile who := by
    intro time
    rw [quittingFinitePureReplyValue_eq_compactStoppingLawsOfProfile]
    simpa only [quittingTerminalPayoff_update_pureTimeBehaviorStrategy] using
      quittingTerminalPayoff_finiteTime_le_finitePureReplyValue reward canonical who time
  have hlimit : Tendsto (quittingOpponentSurvivalWeight roots who 0)
      atTop (nhds survival) :=
    quittingOpponentSurvivalWeight_compactStoppingLawProfile_tendsto reward laws who
  have hnonneg : 0 ≤ survival := ge_of_tendsto hlimit
    (Eventually.of_forall fun time ↦ quittingOpponentSurvivalWeight_nonneg roots who 0 time)
  have hle : survival ≤ 1 := le_of_tendsto hlimit
    (Eventually.of_forall fun time ↦ quittingOpponentSurvivalWeight_le_one roots who 0 time)
  have hcontracts : survival < 1 := by
    apply lt_of_le_of_ne hle
    intro heq
    have hone : Tendsto (quittingOpponentSurvivalWeight roots who 0) atTop (nhds 1) :=
      heq ▸ hlimit
    exact (not_le_of_gt hsolo)
      (solo_le_finiteBound_of_opponentSurvival_tendsto_one reward roots who hfinite hone)
  apply quittingPunishmentValue_le_of_finiteBound_and_renewalLimit
    reward roots who hfinite hlimit hcontracts
  apply (div_le_iff₀ (by linarith : 0 < 1 - survival)).mpr
  have hlate := neverPayoff_add_opponentNever_mul_solo_le_finitePureReplyValue
    reward profile who
  rw [quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy] at hlate
  change quittingRootSequencePureTimeTerminalValue reward roots who none 0 +
    survival * quittingSoloReward reward who who ≤
      quittingFinitePureReplyValue reward profile who at hlate
  nlinarith

/-- Finite-date responses have punishment value equal to the smaller of the
full behavioral punishment value and the own singleton reward. -/
theorem quittingFinitePureReplyPunishmentValue_eq_min
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingFinitePureReplyPunishmentValue reward who =
      min (quittingPunishmentValue reward who) (quittingSoloReward reward who who) := by
  apply le_antisymm
  · exact le_min (quittingFinitePureReplyPunishmentValue_le_punishmentValue reward who)
      (quittingFinitePureReplyPunishmentValue_le_solo reward who)
  · letI : Nonempty ((quittingGame reward).BehaviorProfile) :=
      ⟨quittingAlwaysContinueProfile reward⟩
    apply le_ciInf
    intro profile
    by_cases hsolo : quittingFinitePureReplyValue reward profile who <
        quittingSoloReward reward who who
    · exact (min_le_left _ _).trans
        (quittingPunishmentValue_le_finitePureReplyValue_of_lt_solo reward profile who hsolo)
    · exact (min_le_right _ _).trans (le_of_not_gt hsolo)

end GameTheory
