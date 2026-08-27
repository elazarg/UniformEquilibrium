import UniformEquilibrium.Quitting.Cycles.PeriodicRootResponseSystem
import UniformEquilibrium.Quitting.Cycles.PeriodicJointSurvival
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Cycles.SoloRootSequenceValues
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import MathUE.BonferroniProductBounds
import MathUE.FiniteCycleAggregate

/-!
# Local periodic anchor obstructions

This file records the game-facing local periodic Never barrier.  The cyclic
compiler supplies an actual behavioral profile, rather than a profile
restricted to pure deviations.  The one-stage collision estimate, deleted-
player contraction, and finite weighted-period aggregate are proved below
from the minimum-tube assumptions.

The resulting theorem is conditional on the supplied cyclic roots and their
numerical tube and absorption hypotheses, but its conclusion is against the
unrestricted behavioral deviation space.  In particular, it does not claim
best-response attainment.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {K : ℕ} [NeZero K]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The singleton payoff used as the local anchor in the periodic barrier. -/
def quittingSingletonAnchor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  reward ⟨{who}, Finset.singleton_nonempty who⟩ who

/-- Quit hazards and deleted-player survival read directly from a product root.
These are the quantities occurring in the minimum-tube packet. -/
def quittingPeriodicQuitHazard (root : ι → PMF Bool) (who : ι) : ℝ :=
  (root who true).toReal

def quittingPeriodicDeletedSurvival
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootDeletedContinueMass root who

/-- The actual terminal payoff of the compiled cyclic behavioral profile. -/
def quittingPeriodicActualPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) : ℝ :=
  quittingCyclicTerminalValue reward cycle phase who

/-- The complete Never replacement, evaluated against the cyclic roots. -/
def quittingPeriodicNeverPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) : ℝ :=
  quittingPeriodicWindowRefusalValue reward
    (quittingCyclicRootSequence cycle phase) who

/-- The unrestricted unilateral behavioral cap of the compiled profile. -/
def quittingPeriodicBehavioralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) : ℝ :=
  sSup (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who ↦
    quittingTerminalPayoff reward
      (Function.update (quittingCyclicBehaviorProfile reward cycle phase) who
        deviation) who)

omit [NeZero K] in
@[simp] theorem quittingPeriodicNeverPayoff_eq_refusal
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    quittingPeriodicNeverPayoff reward cycle phase who =
      quittingPeriodicWindowRefusalValue reward
        (quittingCyclicRootSequence cycle phase) who :=
  rfl

omit [DecidableEq ι] [NeZero K] in
@[simp] theorem quittingPeriodicActualPayoff_eq_cyclic
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    quittingPeriodicActualPayoff reward cycle phase who =
      quittingCyclicTerminalValue reward cycle phase who :=
  rfl

/-- The Never deviation is below the unrestricted cap.  This is the exact
bridge from the periodic response system to all behavioral deviations. -/
theorem quittingPeriodicNeverPayoff_le_behavioralCap
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    quittingPeriodicNeverPayoff reward cycle phase who ≤
      quittingPeriodicBehavioralCap reward cycle phase who := by
  rw [quittingPeriodicBehavioralCap,
    sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile]
  unfold quittingPeriodicNeverPayoff
  rw [quittingCyclicResponseCap, quittingPeriodicWindowBestResponseValue]
  exact le_max_left _ _

/-- The one-stage Never comparison has the sharp collision constant used by
the packet.  The endpoint identity separates the deleted-opponent survival
term from the joining (collision) term. -/
theorem quittingRootContinue_sub_quit_ge_singletonGap_mul_survival_sub_collision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) {R eta : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hgap : eta ≤ tail who - quittingSingletonAnchor reward who) :
    eta * quittingRootDeletedContinueMass root who -
          2 * R * quittingRootOpponentAbsorptionMass root who ≤
      quittingRootContinuePayoff reward tail root who -
        quittingRootQuitPayoff reward tail root who := by
  let opponent := quittingRootOpponentAbsorptionMass root who
  let survival := quittingRootDeletedContinueMass root who
  have hsurvival : survival = 1 - opponent := by
    exact quittingRootOpponentContinueMass_eq_one_sub_absorptionMass
      root who
  have hsurvival_nonneg : 0 ≤ survival := by
    exact quittingRootDeletedContinueMass_nonneg root who
  have hopen_nonneg : 0 ≤ opponent := by
    exact quittingRootOpponentAbsorptionMass_nonneg root who
  have hjoin := quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
    reward root who hreward
  have hscaled := mul_le_mul_of_nonneg_left hgap hsurvival_nonneg
  have hformula := quittingRootEndpointDifference_eq_outsiderNever
    reward tail root who
  have hendpoint :
      quittingRootEndpointDifference reward tail root who ≤
        -eta * survival + 2 * R * opponent := by
    rw [hformula, hsurvival]
    change (1 - opponent) *
        (quittingSingletonAnchor reward who - tail who) + _ ≤ _
    have hjoin' : quittingOutsiderJoiningContribution reward root who ≤
        2 * R * opponent := by
      rw [show quittingRootAbsorptionMass
          (Function.update root who (PMF.pure false)) = opponent by rfl] at hjoin
      exact hjoin
    nlinarith
  rw [quittingRootContinuePayoff_eq_deleted,
    quittingRootQuitPayoff_eq_deletedQuitValue]
  change eta * survival - 2 * R * opponent ≤
    quittingRootDeletedContinueReward reward root who + survival * tail who -
      quittingRootDeletedQuitValue reward root who
  have hdiff :
      quittingRootDeletedContinueReward reward root who + survival * tail who -
          quittingRootDeletedQuitValue reward root who =
        -(quittingRootEndpointDifference reward tail root who) := by
    dsimp [survival]
    rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_eq_deletedQuitValue,
      quittingRootContinuePayoff_eq_deleted]
    ring
  rw [hdiff]
  linarith

/-- The deleted-player collision mass is bounded by the sum of the opponent
quit hazards. -/
theorem quittingRootOpponentAbsorptionMass_le_card_mul_hazard
    (root : ι → PMF Bool) (who : ι) {m : ℝ}
    (hm : ∀ other, (root other true).toReal ≤ m) :
    quittingRootOpponentAbsorptionMass root who ≤
      ((Fintype.card ι : ℝ) - 1) * m := by
  letI : Nonempty ι := ⟨who⟩
  have hunion := Math.one_sub_prod_one_sub_le_sum
    (fun other ↦ (root other true).toReal)
    (Finset.univ.erase who)
    (fun other _ ↦ ENNReal.toReal_nonneg)
    (fun other _ ↦ by
      exact ENNReal.toReal_mono ENNReal.one_ne_top ((root other).coe_le_one true))
  rw [← quittingRootOpponentAbsorptionMass_eq_one_sub_prod root who] at hunion
  have hsum :
      (∑ other ∈ Finset.univ.erase who, (root other true).toReal) ≤
        ∑ _other ∈ Finset.univ.erase who, m := by
    apply Finset.sum_le_sum
    intro other hother
    exact hm other
  have hcard : (Finset.univ.erase who).card = Fintype.card ι - 1 := by
    simp
  calc
    quittingRootOpponentAbsorptionMass root who ≤
        ∑ other ∈ Finset.univ.erase who, (root other true).toReal := hunion
    _ ≤ ∑ _other ∈ Finset.univ.erase who, m := hsum
    _ = ((Fintype.card ι : ℝ) - 1) * m := by
      rw [Finset.sum_const, hcard]
      norm_num [nsmul_eq_mul,
        Nat.cast_sub (Fintype.card_pos_iff.mpr inferInstance)]

/-- The packet's hazard scale turns the one-stage collision estimate into a
uniform half-`eta` Continue-over-Quit gain. -/
theorem quittingRootContinue_sub_quit_ge_half_eta_of_small_hazard
    (root : ι → PMF Bool) (tail : Payoff ι) (who : ι)
    {R eta : ℝ} (R_nonneg : 0 ≤ R) (eta_pos : 0 < eta)
    (card_two_le : 2 ≤ Fintype.card ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hgap : eta ≤ tail who - quittingSingletonAnchor reward who)
    (hhazard : ∀ other, (root other true).toReal ≤
      eta / (2 * ((Fintype.card ι : ℝ) - 1) * (eta + 2 * R))) :
    eta / 2 ≤ quittingRootContinuePayoff reward tail root who -
      quittingRootQuitPayoff reward tail root who := by
  have hbase := quittingRootContinue_sub_quit_ge_singletonGap_mul_survival_sub_collision
    reward tail root who hreward hgap
  have hmass := quittingRootOpponentAbsorptionMass_le_card_mul_hazard root who
    (m := eta / (2 * ((Fintype.card ι : ℝ) - 1) * (eta + 2 * R))) hhazard
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by
    have hcard : (2 : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast card_two_le
    linarith
  have hden : 0 < eta + 2 * R := by linarith
  have hmass' : quittingRootOpponentAbsorptionMass root who ≤
      eta / (2 * (eta + 2 * R)) := by
    calc
      quittingRootOpponentAbsorptionMass root who ≤
          ((Fintype.card ι : ℝ) - 1) *
            (eta / (2 * ((Fintype.card ι : ℝ) - 1) * (eta + 2 * R))) := hmass
      _ = eta / (2 * (eta + 2 * R)) := by
        field_simp
  have hscaled := mul_le_mul_of_nonneg_left hmass'
    (by linarith : 0 ≤ eta + 2 * R)
  have hscaled_rhs :
      (eta + 2 * R) * (eta / (2 * (eta + 2 * R))) = eta / 2 := by
    field_simp
  have hnonneg := quittingRootOpponentAbsorptionMass_nonneg root who
  have hrewrite := quittingRootOpponentContinueMass_eq_one_sub_absorptionMass
    root who
  have hsurvival : quittingRootDeletedContinueMass root who =
      1 - quittingRootOpponentAbsorptionMass root who := by
    exact hrewrite
  rw [hsurvival] at hbase
  rw [hscaled_rhs] at hscaled
  nlinarith

@[simp] theorem quittingPeriodicBehavioralCap_eq_cyclicResponseCap
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    quittingPeriodicBehavioralCap reward cycle phase who =
      quittingCyclicResponseCap reward cycle phase who := by
  unfold quittingPeriodicBehavioralCap
  exact sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile
    reward cycle phase who

omit [NeZero K] in
theorem quittingRootSuccessorPayoff_deleted_eq_continue
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    quittingRootSuccessorPayoff reward
        (quittingCyclicTerminalValue reward
          (quittingCyclicDeletedCycle cycle who)
          (finRotate K phase))
        (quittingCyclicDeletedCycle cycle who phase) who =
      quittingRootContinuePayoff reward
        (quittingCyclicTerminalValue reward
          (quittingCyclicDeletedCycle cycle who)
          (finRotate K phase)) (cycle phase) who := by
  rfl

omit [NeZero K] in
theorem quittingPeriodicNeverPayoff_eq_continuePayoff
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    quittingPeriodicNeverPayoff reward cycle phase who =
      quittingRootContinuePayoff reward
        (fun player ↦ quittingPeriodicNeverPayoff reward cycle
          (finRotate K phase) player)
        (cycle phase) who := by
  rw [quittingPeriodicNeverPayoff_eq_refusal,
    quittingPeriodicWindowRefusalValue_eq_cyclicTerminalValue_deleted]
  rw [quittingRootContinuePayoff_eq_deleted]
  rw [quittingPeriodicNeverPayoff_eq_refusal,
    quittingPeriodicWindowRefusalValue_eq_cyclicTerminalValue_deleted,
    quittingCyclicTerminalValue_eq_rootSuccessorPayoff]
  have h := quittingRootSuccessorPayoff_deleted_eq_continue
    (reward := reward) cycle phase who
  rw [quittingRootContinuePayoff_eq_deleted] at h
  exact h

omit [NeZero K] in
theorem quittingPeriodicNeverGap_eq_step
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι) :
    quittingPeriodicNeverPayoff reward cycle phase who -
        quittingPeriodicActualPayoff reward cycle phase who =
      quittingRootDeletedContinueMass (cycle phase) who *
          (quittingPeriodicNeverPayoff reward cycle (finRotate K phase) who -
            quittingPeriodicActualPayoff reward cycle (finRotate K phase) who) +
        (cycle phase who true).toReal *
          (quittingRootContinuePayoff reward
              (quittingCyclicTerminalValue reward cycle
                (finRotate K phase)) (cycle phase) who -
            quittingRootQuitPayoff reward
              (quittingCyclicTerminalValue reward cycle
                (finRotate K phase)) (cycle phase) who) := by
  have hnever := quittingPeriodicNeverPayoff_eq_continuePayoff
    (reward := reward) cycle phase who
  rw [quittingRootContinuePayoff_eq_deleted] at hnever
  have hactual := quittingCyclicTerminalValue_eq_rootSuccessorPayoff
    (reward := reward) cycle phase
  have hactual' := congrFun hactual who
  rw [quittingRootSuccessorPayoff_eq_endpointMix] at hactual'
  rw [quittingRootContinuePayoff_eq_deleted,
    quittingRootQuitPayoff_eq_deletedQuitValue] at hactual'
  simp only [quittingPeriodicActualPayoff]
  rw [hnever, hactual']
  rw [quittingRootContinuePayoff_eq_deleted,
    quittingRootQuitPayoff_eq_deletedQuitValue]
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (cycle phase) who
  have hfalse : (cycle phase who false).toReal =
      1 - (cycle phase who true).toReal := by
    linarith
  rw [hfalse]
  ring

omit [NeZero K] in
theorem quittingPeriodicContinue_sub_quit_ge_half_eta
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    {R eta : ℝ} (R_nonneg : 0 ≤ R) (eta_pos : 0 < eta)
    (card_two_le : 2 ≤ Fintype.card ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hgap : eta ≤ quittingCyclicTerminalValue reward cycle
      (finRotate K phase) who - quittingSingletonAnchor reward who)
    (hhazard : ∀ other, (cycle phase other true).toReal ≤
      eta / (2 * ((Fintype.card ι : ℝ) - 1) * (eta + 2 * R))) :
    eta / 2 ≤ quittingRootContinuePayoff reward
        (quittingCyclicTerminalValue reward cycle (finRotate K phase))
        (cycle phase) who -
      quittingRootQuitPayoff reward
        (quittingCyclicTerminalValue reward cycle (finRotate K phase))
        (cycle phase) who := by
  exact quittingRootContinue_sub_quit_ge_half_eta_of_small_hazard
    (reward := reward) (cycle phase)
    (quittingCyclicTerminalValue reward cycle (finRotate K phase)) who
    R_nonneg eta_pos card_two_le hreward hgap hhazard

/-! ## The deleted-player contraction bridge -/

omit [NeZero K] in
theorem quittingCyclicRootSequence_solo_of_not_deleted_contracts
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    (hcontracts : ¬ (∏ k : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1) :
    ∀ time player, player ≠ who →
      quittingCyclicRootSequence cycle phase time player = PMF.pure false := by
  intro time player hplayer
  have hroot := quittingCyclicDeletedCycle_eq_allContinueRoot_of_not_contracts
    (cycle := cycle) (who := who) hcontracts
      (quittingCyclicOrbit phase time)
  have hplayer' := congrFun hroot player
  rw [quittingCyclicDeletedCycle, Function.update_of_ne hplayer] at hplayer'
  exact hplayer'

theorem exists_quittingCyclicTerminalValue_eq_solo_of_not_deleted_contracts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (who : ι)
    (hcontracts : ¬ (∏ k : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1)
    (hfull : (∏ k : Fin K,
      quittingStationaryContinueMass (cycle k)) < 1) :
    ∃ phase, quittingCyclicTerminalValue reward cycle phase who =
      quittingSingletonAnchor reward who := by
  obtain ⟨phase, hphase⟩ : ∃ phase : Fin K,
      quittingStationaryContinueMass (cycle phase) < 1 := by
    by_contra hnone
    push Not at hnone
    have hone : ∀ phase : Fin K,
        quittingStationaryContinueMass (cycle phase) = 1 := by
      intro phase
      exact le_antisymm
        (quittingStationaryContinueMass_le_one (cycle phase))
        (hnone phase)
    rw [Finset.prod_eq_one (fun phase _ => hone phase)] at hfull
    linarith
  let roots : ℕ → ι → PMF Bool := quittingCyclicRootSequence cycle phase
  have hperiodic : ∀ time, roots (time + K) = roots time := by
    intro time
    simp only [roots, quittingCyclicRootSequence, quittingCyclicOrbit_add,
      quittingCyclicOrbit_card]
  have hzero : quittingJointSurvivalLimit roots 0 = 0 := by
    apply quittingJointSurvivalLimit_eq_zero_of_periodic roots
      (start := 0) (period := K) (date := 0)
    · exact hperiodic
    · exact Nat.pos_of_ne_zero (NeZero.ne K)
    · simpa [roots] using hphase
  have hlive : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0 := by
    rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
    exact hzero
  have hsolo : ∀ time player, player ≠ who → roots time player = PMF.pure false :=
    quittingCyclicRootSequence_solo_of_not_deleted_contracts cycle phase who
      hcontracts
  have hvalue := quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing
    reward roots who 0 hsolo hlive who
  refine ⟨phase, ?_⟩
  simpa [roots, quittingCyclicTerminalValue, quittingSingletonAnchor,
    quittingSoloReward] using hvalue

theorem quittingCyclicTerminalValue_eq_solo_of_not_deleted_contracts_at
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    (hcontracts : ¬ (∏ k : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1)
    (hphase : quittingStationaryContinueMass (cycle phase) < 1) :
    quittingCyclicTerminalValue reward cycle phase who =
      quittingSingletonAnchor reward who := by
  let roots : ℕ → ι → PMF Bool := quittingCyclicRootSequence cycle phase
  have hperiodic : ∀ time, roots (time + K) = roots time := by
    intro time
    simp only [roots, quittingCyclicRootSequence, quittingCyclicOrbit_add,
      quittingCyclicOrbit_card]
  have hzero : quittingJointSurvivalLimit roots 0 = 0 := by
    apply quittingJointSurvivalLimit_eq_zero_of_periodic roots
      (start := 0) (period := K) (date := 0)
    · exact hperiodic
    · exact Nat.pos_of_ne_zero (NeZero.ne K)
    · simpa [roots] using hphase
  have hlive : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0 := by
    rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
    exact hzero
  have hsolo : ∀ time player, player ≠ who → roots time player = PMF.pure false :=
    quittingCyclicRootSequence_solo_of_not_deleted_contracts cycle phase who
      hcontracts
  have hvalue := quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing
    reward roots who 0 hsolo hlive who
  simpa [roots, quittingCyclicTerminalValue, quittingSingletonAnchor,
    quittingSoloReward] using hvalue

theorem quittingPeriodicDeletedProduct_lt_one_of_payoff_gap
    (cycle : Fin K → ι → PMF Bool) {eta : ℝ} (eta_pos : 0 < eta)
    (hgap : ∀ (phase : Fin K) (who : ι),
      quittingSingletonAnchor reward who + eta ≤
        quittingCyclicTerminalValue reward cycle phase who)
    (hfull : (∏ k : Fin K,
      quittingStationaryContinueMass (cycle k)) < 1) (who : ι) :
    (∏ k : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle k) who) < 1 := by
  by_contra hcontract
  obtain ⟨phase, hsolo⟩ :=
    exists_quittingCyclicTerminalValue_eq_solo_of_not_deleted_contracts
      reward cycle who hcontract hfull
  have htube := hgap phase who
  rw [hsolo] at htube
  linarith

theorem quittingPeriodicNeverGap_ge_weighted_charge_of_payoff_gap
    (cycle : Fin K → ι → PMF Bool) {R eta : ℝ}
    (R_nonneg : 0 ≤ R) (eta_pos : 0 < eta)
    (card_two_le : 2 ≤ Fintype.card ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hgap : ∀ (phase : Fin K) (who : ι),
      quittingSingletonAnchor reward who + eta ≤
        quittingCyclicTerminalValue reward cycle phase who)
    (hhazard : ∀ (phase : Fin K) (who : ι),
      quittingPeriodicQuitHazard (cycle phase) who ≤
        eta / (2 * ((Fintype.card ι : ℝ) - 1) * (eta + 2 * R)))
    (hfull : (∏ k : Fin K,
      quittingStationaryContinueMass (cycle k)) < 1)
    (phase : Fin K) (who : ι) :
    -quittingCyclicResidualCharge
        (fun k => quittingRootDeletedContinueMass (cycle k) who)
        (fun k => -(eta / 2) * (cycle k who true).toReal) phase K /
      (1 - ∏ k : Fin K,
        quittingRootDeletedContinueMass (cycle k) who) ≤
      quittingPeriodicNeverPayoff reward cycle phase who -
        quittingPeriodicActualPayoff reward cycle phase who := by
  have hcontract := quittingPeriodicDeletedProduct_lt_one_of_payoff_gap
    (reward := reward) cycle (eta_pos := eta_pos) hgap hfull who
  let coefficient : Fin K → ℝ := fun k =>
    quittingRootDeletedContinueMass (cycle k) who
  let hazard : Fin K → ℝ := fun k => (cycle k who true).toReal
  let residual : Fin K → ℝ := fun k => -(eta / 2) * hazard k
  let value : Fin K → ℝ := fun k => -(
    quittingPeriodicNeverPayoff reward cycle k who -
      quittingPeriodicActualPayoff reward cycle k who)
  have hcoefficient : ∀ k, 0 ≤ coefficient k := by
    intro k
    exact quittingRootDeletedContinueMass_nonneg (cycle k) who
  have hstep : ∀ k, value k ≤ residual k +
      coefficient k * value (finRotate K k) := by
    intro k
    have hrec := quittingPeriodicNeverGap_eq_step
      (reward := reward) cycle k who
    have hgain := quittingPeriodicContinue_sub_quit_ge_half_eta
      (reward := reward) cycle k who R_nonneg eta_pos card_two_le hreward
      (by
        have h := hgap (finRotate K k) who
        linarith) (by
        intro other
        exact hhazard k other)
    have hhazard_nonneg : 0 ≤ hazard k := by
      exact ENNReal.toReal_nonneg
    have hscaled := mul_le_mul_of_nonneg_left hgain hhazard_nonneg
    change -(
        quittingPeriodicNeverPayoff reward cycle k who -
          quittingPeriodicActualPayoff reward cycle k who) ≤ _
    dsimp [residual, coefficient, value, hazard]
    have hrec' :
        quittingPeriodicNeverPayoff reward cycle k who -
            quittingPeriodicActualPayoff reward cycle k who =
          quittingRootDeletedContinueMass (cycle k) who *
              (quittingPeriodicNeverPayoff reward cycle (finRotate K k) who -
                quittingPeriodicActualPayoff reward cycle (finRotate K k) who) +
            (cycle k who true).toReal *
              (quittingRootContinuePayoff reward
                  (quittingCyclicTerminalValue reward cycle (finRotate K k))
                  (cycle k) who -
                quittingRootQuitPayoff reward
                  (quittingCyclicTerminalValue reward cycle (finRotate K k))
                  (cycle k) who) := hrec
    have hrec'' :
        quittingPeriodicWindowRefusalValue reward
              (quittingCyclicRootSequence cycle k) who -
            quittingCyclicTerminalValue reward cycle k who =
          quittingRootDeletedContinueMass (cycle k) who *
              (quittingPeriodicWindowRefusalValue reward
                  (quittingCyclicRootSequence cycle (finRotate K k)) who -
                quittingCyclicTerminalValue reward cycle (finRotate K k) who) +
            (cycle k who true).toReal *
              (quittingRootContinuePayoff reward
                  (quittingCyclicTerminalValue reward cycle (finRotate K k))
                  (cycle k) who -
                quittingRootQuitPayoff reward
                  (quittingCyclicTerminalValue reward cycle (finRotate K k))
                  (cycle k) who) := by
      simpa [quittingPeriodicNeverPayoff, quittingPeriodicActualPayoff] using hrec'
    rw [hrec'']
    linarith
  have hbound := cyclicValue_le_residualCharge_div_one_sub_prod
    coefficient residual value hcoefficient hcontract hstep phase
  dsimp [value, coefficient, residual, hazard] at hbound ⊢
  simpa [neg_div] using (neg_le_neg hbound)

theorem exists_quittingPeriodicBehavioralGap_of_payoff_gap
    (cycle : Fin K → ι → PMF Bool) {R eta : ℝ}
    (R_nonneg : 0 ≤ R) (eta_pos : 0 < eta)
    (card_two_le : 2 ≤ Fintype.card ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hgap : ∀ (phase : Fin K) (who : ι),
      quittingSingletonAnchor reward who + eta ≤
        quittingCyclicTerminalValue reward cycle phase who)
    (hhazard : ∀ (phase : Fin K) (who : ι),
      quittingPeriodicQuitHazard (cycle phase) who ≤
        eta / (2 * ((Fintype.card ι : ℝ) - 1) * (eta + 2 * R)))
    (hfull : (∏ k : Fin K,
      quittingStationaryContinueMass (cycle k)) < 1)
    (base : Fin K) :
    ∃ who,
      quittingPeriodicActualPayoff reward cycle base who +
          eta / (2 * (Fintype.card ι : ℝ)) ≤
        quittingPeriodicBehavioralCap reward cycle base who := by
  have hcardpos : 0 < Fintype.card ι := by
    omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcardpos
  let q : Fin K → ι → ℝ := fun phase who =>
    (cycle phase who true).toReal
  let coefficient : Fin K → ι → ℝ := fun phase who =>
    quittingRootDeletedContinueMass (cycle phase) who
  let value : Fin K → ι → ℝ := fun phase who =>
    quittingPeriodicNeverPayoff reward cycle phase who -
      quittingPeriodicActualPayoff reward cycle phase who
  let beta : Fin K → ℝ := fun phase =>
    quittingStationaryContinueMass (cycle phase)
  have hq0 : ∀ phase who, 0 ≤ q phase who := by
    intro phase who
    exact ENNReal.toReal_nonneg
  have hq1 : ∀ phase who, q phase who ≤ 1 := by
    intro phase who
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      ((cycle phase who).coe_le_one true)
  have hcoef0 : ∀ phase who, 0 ≤ coefficient phase who := by
    intro phase who
    exact quittingRootDeletedContinueMass_nonneg (cycle phase) who
  have hbeta0 : ∀ phase, 0 ≤ beta phase := by
    intro phase
    exact quittingStationaryContinueMass_nonneg (cycle phase)
  have hcbeta : ∀ phase who, beta phase ≤ coefficient phase who := by
    intro phase who
    change quittingStationaryContinueMass (cycle phase) ≤
      quittingStationaryContinueMass
        (Function.update (cycle phase) who (PMF.pure false))
    exact quittingStationaryContinueMass_le_fixedOpponentsContinueMass
      (cycle phase) who
  have hbeta_eq : ∀ phase, beta phase = ∏ player : ι, (1 - q phase player) := by
    intro phase
    dsimp [beta]
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_congr rfl
    intro player _
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (cycle phase) player
    dsimp [q]
    linarith
  have hcontracts : ∀ who, ∏ phase : Fin K, coefficient phase who < 1 := by
    intro who
    change (∏ phase : Fin K,
      quittingStationaryContinueMass
        (Function.update (cycle phase) who (PMF.pure false))) < 1
    simpa [quittingRootDeletedContinueMass,
      quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass] using
      quittingPeriodicDeletedProduct_lt_one_of_payoff_gap
        (reward := reward) cycle eta_pos hgap hfull who
  have hstep : ∀ phase who, value phase who ≥ eta / 2 * q phase who +
      coefficient phase who * value (finRotate K phase) who := by
    intro phase who
    have hrec := quittingPeriodicNeverGap_eq_step
      (reward := reward) cycle phase who
    have hgain := quittingPeriodicContinue_sub_quit_ge_half_eta
      (reward := reward) cycle phase who R_nonneg eta_pos card_two_le hreward
      (by
        have h := hgap (finRotate K phase) who
        linarith) (by
        intro other
        exact hhazard phase other)
    have hq_nonneg : 0 ≤ q phase who := hq0 phase who
    have hscaled := mul_le_mul_of_nonneg_left hgain hq_nonneg
    dsimp [value, q, coefficient]
    have hrec' :
        quittingPeriodicNeverPayoff reward cycle phase who -
            quittingPeriodicActualPayoff reward cycle phase who =
          quittingRootDeletedContinueMass (cycle phase) who *
              (quittingPeriodicNeverPayoff reward cycle (finRotate K phase) who -
                quittingPeriodicActualPayoff reward cycle (finRotate K phase) who) +
            (cycle phase who true).toReal *
              (quittingRootContinuePayoff reward
                  (quittingCyclicTerminalValue reward cycle (finRotate K phase))
                  (cycle phase) who -
                quittingRootQuitPayoff reward
                  (quittingCyclicTerminalValue reward cycle (finRotate K phase))
                  (cycle phase) who) := hrec
    have hrec'' :
        quittingPeriodicWindowRefusalValue reward
              (quittingCyclicRootSequence cycle phase) who -
            quittingCyclicTerminalValue reward cycle phase who =
          quittingRootDeletedContinueMass (cycle phase) who *
              (quittingPeriodicWindowRefusalValue reward
                  (quittingCyclicRootSequence cycle (finRotate K phase)) who -
                quittingCyclicTerminalValue reward cycle (finRotate K phase) who) +
            (cycle phase who true).toReal *
              (quittingRootContinuePayoff reward
                  (quittingCyclicTerminalValue reward cycle (finRotate K phase))
                  (cycle phase) who -
                quittingRootQuitPayoff reward
                  (quittingCyclicTerminalValue reward cycle (finRotate K phase))
                  (cycle phase) who) := by
      simpa [quittingPeriodicNeverPayoff, quittingPeriodicActualPayoff] using hrec'
    rw [hrec'']
    linarith
  obtain ⟨who, hwho⟩ := Math.FiniteCycleAggregate.exists_player_base_ge_eta_div_two_card
    q coefficient value beta eta base (by linarith) hq0 hq1 hcoef0 hbeta0 hcbeta
      hbeta_eq hfull hcontracts hstep
  refine ⟨who, ?_⟩
  have hcap := quittingPeriodicNeverPayoff_le_behavioralCap
    (reward := reward) cycle base who
  dsimp [value] at hwho
  have hwho' : eta / (2 * (Fintype.card ι : ℝ)) ≤
      quittingPeriodicNeverPayoff reward cycle base who -
        quittingPeriodicActualPayoff reward cycle base who := by
    simpa [quittingPeriodicNeverPayoff, quittingPeriodicActualPayoff] using hwho
  linarith

/-- A supplied Never-gap certificate, phrased using the actual cyclic profile.
The witness may come from a weighted-period collision calculation. -/
structure QuittingPeriodicNeverGapCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (eta : ℝ) where
  player : ι
  gap : eta ≤
    quittingPeriodicNeverPayoff reward cycle phase player -
      quittingPeriodicActualPayoff reward cycle phase player

/-- The unrestricted behavioral conclusion from the Never barrier. -/
theorem exists_quittingPeriodicBehavioralGap_of_neverGap
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (eta : ℝ)
    (cert : QuittingPeriodicNeverGapCertificate reward cycle phase eta) :
    ∃ who,
      quittingPeriodicActualPayoff reward cycle phase who + eta ≤
        quittingPeriodicBehavioralCap reward cycle phase who := by
  refine ⟨cert.player, ?_⟩
  have hcap := quittingPeriodicNeverPayoff_le_behavioralCap
    (reward := reward) cycle phase cert.player
  have hgap := cert.gap
  linarith

/-- Reader-facing form: a Never gap for one player is a terminal exploitability
lower bound against every unilateral behavioral replacement. -/
theorem exists_quittingPeriodicBehavioralGap_of_neverGap'
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (eta : ℝ)
    (player : ι)
    (hgap : eta ≤
      quittingPeriodicNeverPayoff reward cycle phase player -
        quittingPeriodicActualPayoff reward cycle phase player) :
    ∃ who,
      quittingPeriodicActualPayoff reward cycle phase who + eta ≤
        sSup (Set.range fun deviation :
          (quittingGame reward).BehaviorStrategy who ↦
            quittingTerminalPayoff reward
              (Function.update (quittingCyclicBehaviorProfile reward cycle phase)
                who deviation) who) := by
  refine ⟨player, ?_⟩
  have hcap := quittingPeriodicNeverPayoff_le_behavioralCap
    (reward := reward) cycle phase player
  change quittingPeriodicActualPayoff reward cycle phase player + eta ≤
    quittingPeriodicBehavioralCap reward cycle phase player
  linarith

/-- Exact minimum-tube packet hypotheses.  The collision half, deleted-player
contraction, and weighted finite-cycle aggregate are discharged by the
theorems above. -/
structure LocalPeriodicAnchorPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) where
  R : ℝ
  eta : ℝ
  R_nonneg : 0 ≤ R
  eta_pos : 0 < eta
  card_two_le : 2 ≤ Fintype.card ι
  reward_bound : ∀ (terminal : {S : Finset ι // S.Nonempty}) (who : ι),
    |reward terminal who| ≤ R
  payoff_gap : ∀ (cyclePhase : Fin K) (who : ι),
    quittingSingletonAnchor reward who + eta ≤
      quittingCyclicTerminalValue reward cycle cyclePhase who
  max_hazard_bound : ∀ (cyclePhase : Fin K) (who : ι),
    quittingPeriodicQuitHazard (cycle cyclePhase) who ≤
      eta / (2 * ((Fintype.card ι : ℝ) - 1) * (eta + 2 * R))
  positive_absorption :
    ∏ cyclePhase : Fin K,
      quittingStationaryContinueMass (cycle cyclePhase) < 1

/-- Conditional Theorem A.  The numerical minimum-tube assumptions yield the
advertised unrestricted behavioral exploitability bound for the supplied
cyclic roots. -/
theorem localPeriodicAnchor_obstruction
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (packet : LocalPeriodicAnchorPacket reward cycle phase) :
    ∃ who,
      quittingPeriodicActualPayoff reward cycle phase who +
          packet.eta / (2 * (Fintype.card ι : ℝ)) ≤
        quittingPeriodicBehavioralCap reward cycle phase who := by
  exact exists_quittingPeriodicBehavioralGap_of_payoff_gap
    (reward := reward) cycle (R := packet.R) (eta := packet.eta)
      packet.R_nonneg packet.eta_pos
      packet.card_two_le packet.reward_bound packet.payoff_gap
      packet.max_hazard_bound packet.positive_absorption phase

/-- Named Theorem-A surface for clients that want the advertised numerical
constant without unfolding the packet structure. -/
theorem localPeriodicAnchor_theoremA
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (packet : LocalPeriodicAnchorPacket reward cycle phase) :
    ∃ who,
      quittingPeriodicActualPayoff reward cycle phase who +
          packet.eta / (2 * (Fintype.card ι : ℝ)) ≤
        quittingPeriodicBehavioralCap reward cycle phase who :=
  localPeriodicAnchor_obstruction (reward := reward) cycle phase packet

end GameTheory
