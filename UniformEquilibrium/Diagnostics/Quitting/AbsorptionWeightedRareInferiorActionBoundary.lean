import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketProducer
import UniformEquilibrium.Quitting.Root.SupportPurification
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Punishment.CoalitionLock
import UniformEquilibrium.Quitting.Punishment.ContinueFloor
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorForward

/-! # Rare inferior supported-action boundary for ordinary root regret -/

noncomputable section

namespace GameTheory.AbsorptionWeightedRareInferiorActionBoundary

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open QuittingSureSetOwnerRepair

/-- Player zero earns one exactly when player one is the sole quitter. -/
def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal player ↦ if terminal.1 = {1} ∧ player = 0 then 1 else 0

/-- Player one quits surely, player zero quits with rare probability `ε`, and
the other two players continue surely. -/
def rareRoot (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : Fin 4 → PMF Bool :=
  fun player ↦ if player = 0 then bernoulliBool ε hε0 hε1
    else if player = 1 then PMF.pure true else PMF.pure false

@[simp] theorem rareRoot_zero_true_toReal
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ((rareRoot ε hε0 hε1 0) true).toReal = ε := by
  simp [rareRoot]

@[simp] theorem rareRoot_zero_false_toReal
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ((rareRoot ε hε0 hε1 0) false).toReal = 1 - ε := by
  simp [rareRoot]

@[simp] theorem rareRoot_one_eq
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    rareRoot ε hε0 hε1 1 = PMF.pure true := by simp [rareRoot]

@[simp] theorem rareRoot_two_eq
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    rareRoot ε hε0 hε1 2 = PMF.pure false := by simp [rareRoot]

@[simp] theorem rareRoot_three_eq
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    rareRoot ε hε0 hε1 3 = PMF.pure false := by simp [rareRoot]

private theorem reward_apply (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (player : Fin 4) :
    reward terminal player = if terminal.1 = {1} ∧ player = 0 then 1 else 0 := rfl

/-- At zero continuation, player zero's Quit and Continue endpoints are zero
and one respectively. -/
theorem playerZero_endpoint_values
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    quittingRootQuitPayoff reward 0 (rareRoot ε hε0 hε1) 0 = 0 ∧
    quittingRootContinuePayoff reward 0 (rareRoot ε hε0 hε1) 0 = 1 := by
  let quitAction : Fin 4 → Bool := fun player ↦ player = 0 ∨ player = 1
  let continueAction : Fin 4 → Bool := fun player ↦ player = 1
  have hquitRoot : Function.update (rareRoot ε hε0 hε1) 0 (PMF.pure true) =
      fun player ↦ PMF.pure (quitAction player) := by
    funext player
    fin_cases player <;> simp [rareRoot, quitAction]
  have hcontinueRoot : Function.update (rareRoot ε hε0 hε1) 0 (PMF.pure false) =
      fun player ↦ PMF.pure (continueAction player) := by
    funext player
    fin_cases player <;> simp [rareRoot, continueAction]
  have hquittersQuit : quittingQuitters quitAction = {0, 1} := by
    ext player
    fin_cases player <;> simp [quittingQuitters, quitAction]
  have hquittersContinue : quittingQuitters continueAction = {1} := by
    ext player
    fin_cases player <;> simp [quittingQuitters, continueAction]
  constructor
  · unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    rw [hquitRoot, pmfPi_pure, expect_pure]
    unfold quittingRootPayoff
    rw [show quittingQuitters quitAction = {0, 1} from hquittersQuit]
    norm_num [reward]
  · unfold quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [hcontinueRoot, pmfPi_pure, expect_pure]
    unfold quittingRootPayoff
    rw [show quittingQuitters continueAction = {1} from hquittersContinue]
    norm_num [reward]

/-- The rare used Quit action has unit loss, while its ordinary mixed regret
is only its probability `ε`. -/
theorem playerZero_gap_and_ordinaryDefect
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    quittingRootEndpointDifference reward 0 (rareRoot ε hε0 hε1) 0 = -1 ∧
    quittingRootCoordinateNashDefect reward 0 (rareRoot ε hε0 hε1) 0 = ε := by
  obtain ⟨hquit, hcontinue⟩ := playerZero_endpoint_values hε0 hε1
  constructor
  · unfold quittingRootEndpointDifference
    linarith
  · rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
    rw [show quittingRootEndpointDifference reward 0 (rareRoot ε hε0 hε1) 0 = -1 by
      unfold quittingRootEndpointDifference
      linarith]
    simp

/-- The inferior Quit action is genuinely supported whenever `ε>0`, even
though its unit gap contributes only `ε` to ordinary regret. -/
theorem playerZero_supportedQuit_gap_one
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < ((rareRoot ε hε.le hε1 0) true).toReal ∧
      quittingRootContinuePayoff reward 0 (rareRoot ε hε.le hε1) 0 -
        quittingRootQuitPayoff reward 0 (rareRoot ε hε.le hε1) 0 = 1 := by
  rw [rareRoot_zero_true_toReal]
  obtain ⟨hquit, hcontinue⟩ := playerZero_endpoint_values hε.le hε1
  exact ⟨hε, by linarith⟩

/-- The displayed successor annotation of the rare row. -/
def rareSuccessorValue (ε : ℝ) : Payoff (Fin 4) :=
  fun player ↦ if player = 0 then 1 - ε else 0

private theorem rootExpected_zero_of_player_ne_zero
    (root : Fin 4 → PMF Bool) (player : Fin 4) (hplayer : player ≠ 0) :
    quittingRootExpectedPayoff reward 0 root player = 0 := by
  unfold quittingRootExpectedPayoff
  rw [show (fun action ↦ quittingRootPayoff reward 0 action player) =
      fun _ ↦ 0 by
    funext action
    by_cases hquit : (quittingQuitters action).Nonempty
    · simp [quittingRootPayoff, hquit, reward, hplayer]
    · simp [quittingRootPayoff, hquit]]
  simp

theorem successor_zero_nonneg
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (player : Fin 4) :
    0 ≤ quittingRootSuccessorPayoff reward 0 (rareRoot ε hε0 hε1) player := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  have hmono := expect_mono (pmfPi (rareRoot ε hε0 hε1))
    (fun _ : Fin 4 → Bool ↦ (0 : ℝ))
    (fun action ↦ quittingRootPayoff reward 0 action player) (fun action ↦ by
      by_cases hquit : (quittingQuitters action).Nonempty
      · simp [quittingRootPayoff, hquit, reward]
        split <;> norm_num
      · simp [quittingRootPayoff, hquit])
  simpa using hmono

@[simp] theorem rareRoot_absorptionMass
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    quittingRootAbsorptionMass (rareRoot ε hε0 hε1) = 1 := by
  unfold quittingRootAbsorptionMass
  have hc : quittingStationaryContinueMass (rareRoot ε hε0 hε1) = 0 := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_eq_zero (Finset.mem_univ 1)
    simp [rareRoot]
  rw [hc]
  norm_num

/-- The exact Bellman successor gives player zero payoff `1-ε`. -/
theorem successor_zero_playerZero
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    quittingRootSuccessorPayoff reward 0 (rareRoot ε hε0 hε1) 0 = 1 - ε := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  obtain ⟨hquit, hcontinue⟩ := playerZero_endpoint_values hε0 hε1
  rw [hquit, hcontinue, rareRoot_zero_true_toReal,
    rareRoot_zero_false_toReal]
  ring

/-- The complete Bellman successor is literally `(1-ε,0,0,0)`. -/
theorem rareRoot_successor_eq
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    quittingRootSuccessorPayoff reward 0 (rareRoot ε hε0 hε1) =
      rareSuccessorValue ε := by
  funext player
  fin_cases player
  · exact successor_zero_playerZero hε0 hε1
  all_goals
    exact rootExpected_zero_of_player_ne_zero _ _ (by decide)

/-- Every coordinate other than player zero has zero ordinary defect. -/
theorem coordinateNashDefect_eq_zero_of_ne_zero
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (player : Fin 4) (hplayer : player ≠ 0) :
    quittingRootCoordinateNashDefect reward 0 (rareRoot ε hε0 hε1) player = 0 := by
  unfold quittingRootCoordinateNashDefect quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootSuccessorPayoff
  rw [rootExpected_zero_of_player_ne_zero _ player hplayer,
    rootExpected_zero_of_player_ne_zero _ player hplayer,
    rootExpected_zero_of_player_ne_zero _ player hplayer]
  norm_num

/-- Purification deletes player zero's rare inferior Quit action. -/
def prunedRoot : Fin 4 → PMF Bool := quittingPureSetRoot {1}

/-- The sure-absorption value of the pruned row. -/
def prunedValue : Payoff (Fin 4) := fun player ↦ if player = 0 then 1 else 0

/-- At every nonnegative threshold below one, the support purifier
really deletes exactly player zero's rare inferior Quit action. -/
theorem supportPurifiedRoot_eq_prunedRoot
    {ε threshold : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hthreshold0 : 0 ≤ threshold) (hthreshold1 : threshold < 1) :
    quittingSupportPurifiedRoot reward 0 threshold
      (rareRoot ε hε.le hε1.le) = prunedRoot := by
  funext player
  by_cases hplayer : player = 0
  · subst player
    have hbad : IsQuittingRootBadQuitAt reward 0 threshold
        (rareRoot ε hε.le hε1.le) 0 := by
      dsimp only [IsQuittingRootBadQuitAt]
      obtain ⟨hquit, hcontinue⟩ := playerZero_endpoint_values hε.le hε1.le
      linarith
    rw [quittingSupportPurifiedRoot_eq_pure_false_of_badQuit _ _ _ _ _ hbad]
    simp [prunedRoot, quittingPureSetRoot, quittingSetAction]
  · have hquit : quittingRootQuitPayoff reward 0
        (rareRoot ε hε.le hε1.le) player = 0 :=
      rootExpected_zero_of_player_ne_zero _ player hplayer
    have hcontinue : quittingRootContinuePayoff reward 0
        (rareRoot ε hε.le hε1.le) player = 0 :=
      rootExpected_zero_of_player_ne_zero _ player hplayer
    have hnotQuit : ¬ IsQuittingRootBadQuitAt reward 0 threshold
        (rareRoot ε hε.le hε1.le) player := by
      simp [IsQuittingRootBadQuitAt, hquit, hcontinue, hthreshold0]
    have hnotContinue : ¬ IsQuittingRootBadContinueAt reward 0 threshold
        (rareRoot ε hε.le hε1.le) player := by
      simp [IsQuittingRootBadContinueAt, hquit, hcontinue, hthreshold0]
    rw [quittingSupportPurifiedRoot_eq_self_of_not_bad _ _ _ _ _
      hnotQuit hnotContinue]
    fin_cases player <;>
      simp_all [rareRoot, prunedRoot, quittingPureSetRoot, quittingSetAction]

@[simp] theorem prunedRoot_absorptionMass :
    quittingRootAbsorptionMass prunedRoot = 1 := by
  unfold prunedRoot quittingRootAbsorptionMass
  rw [stationaryContinueMass_pureSetRoot_of_nonempty (by simp)]
  norm_num

@[simp] theorem prunedRoot_successor (tail : Payoff (Fin 4)) :
    quittingRootSuccessorPayoff reward tail prunedRoot = prunedValue := by
  funext player
  unfold prunedRoot quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty (by simp)]
  fin_cases player <;> norm_num [quittingSetReward, reward, prunedValue]

/-- The pruned sure-absorption row is an exact support Nash row at its own
value. -/
theorem prunedRoot_isExactSupportNash :
    IsQuittingRootSupportApproxNash reward prunedValue 0 prunedRoot := by
  have hstable : IsQuittingSureExitSet reward {1} := by
    rw [isQuittingSureExitSet_iff_forall_max]
    intro player
    fin_cases player <;> norm_num [quittingSetReward, reward]
  have hnash := isZeroQuittingRootNash_pureSetRoot_setReward {1} hstable
  have hvalue : quittingSetReward reward {1} = prunedValue := by
    funext player
    fin_cases player <;> norm_num [quittingSetReward, reward, prunedValue]
  rw [← hvalue]
  exact isQuittingRootSupportApproxNash_zero_of_isZeroNash reward _ _ hnash

theorem punishmentValue_le_zero (player : Fin 4) :
    quittingPunishmentValue reward player ≤ 0 := by
  refine (quittingPunishmentValue_le_max_solo reward player).trans ?_
  fin_cases player <;> norm_num [quittingSetReward, reward]

@[simp] theorem punishmentValue_eq_zero (player : Fin 4) :
    quittingPunishmentValue reward player = 0 := by
  apply le_antisymm (punishmentValue_le_zero player)
  refine (show 0 ≤ quittingContinueFloor reward player from ?_).trans
    (quittingContinueFloor_le_quittingPunishmentValue reward player)
  unfold quittingContinueFloor quittingBlockContinueFloor
  apply Math.Finset.le_insertMin le_rfl
  intro terminal _
  simp only [reward]
  split <;> norm_num

/-- Both annotations of the rare one-row Bellman edge satisfy every
nonnegative punishment-floor tolerance. -/
theorem rareRoot_zero_and_successor_floor
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (player : Fin 4) :
    quittingPunishmentValue reward player - ε ≤ 0 ∧
      quittingPunishmentValue reward player - ε ≤
        quittingRootSuccessorPayoff reward 0 (rareRoot ε hε0 hε1) player := by
  have hp := punishmentValue_le_zero player
  have hs := successor_zero_nonneg hε0 hε1 player
  constructor <;> linarith

/-- The rare row is an actual one-step absorption-weighted packet: its
Bellman residual is zero, its ordinary mixed-root defects are bounded by
`ε` times its unit absorption, and both displayed values satisfy the floors. -/
def rareRoot_weightedPacket
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    QuittingAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox 1) ε 1 := {
  roots := fun _ ↦ rareRoot ε hε.le hε1.le
  value := fun time ↦ if time = 0 then 0 else rareSuccessorValue ε
  horizon := 1
  value_mem := by
    intro time htime player
    by_cases hzero : time = 0
    · simp [hzero]
    · have hone : time = 1 := by omega
      simp only [hone, Nat.one_ne_zero, if_false, rareSuccessorValue]
      split
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · norm_num
  bellman := by
    intro time htime player
    have hzero : time = 0 := by omega
    subst time
    change |rareSuccessorValue ε player -
      quittingRootSuccessorPayoff reward 0 (rareRoot ε hε.le hε1.le) player| ≤
        ε * quittingRootAbsorptionMass (rareRoot ε hε.le hε1.le)
    rw [rareRoot_successor_eq hε.le hε1.le, sub_self, abs_zero]
    exact mul_nonneg hε.le (quittingRootAbsorptionMass_nonneg _)
  regret := by
    intro time htime player
    have hzero : time = 0 := by omega
    subst time
    change quittingRootCoordinateNashDefect reward 0
      (rareRoot ε hε.le hε1.le) player ≤
        ε * quittingRootAbsorptionMass (rareRoot ε hε.le hε1.le)
    rw [rareRoot_absorptionMass, mul_one]
    by_cases hplayer : player = 0
    · subst player
      exact (playerZero_gap_and_ordinaryDefect hε.le hε1.le).2.le
    · rw [coordinateNashDefect_eq_zero_of_ne_zero hε.le hε1.le player hplayer]
      exact hε.le
  rational := by
    intro target time htime
    obtain ⟨hzeroFloor, hsuccessorFloor⟩ :=
      rareRoot_zero_and_successor_floor hε.le hε1.le target
    by_cases hzero : time = 0
    · simpa [hzero] using hzeroFloor
    · simp only [hzero, if_false]
      rw [← rareRoot_successor_eq hε.le hε1.le]
      exact hsuccessorFloor
  chargeTarget_le := by simp }

/-- Repeating the pruned sure-absorption row supplies exact packets of every
positive support tolerance and every requested absorption charge. -/
theorem prunedRoot_hasExactFiniteForwardPackets :
    HasExactFiniteForwardPackets reward 1 := by
  intro supportError herror chargeTarget hcharge
  obtain ⟨horizon, hhorizon⟩ := exists_nat_ge chargeTarget
  refine ⟨{
    roots := fun _ ↦ prunedRoot
    value := fun _ ↦ prunedValue
    horizon := horizon
    value_mem := ?_
    policy := ?_
    support := ?_
    rational := ?_
    chargeTarget_le := ?_ }⟩
  · intro _ _ player
    fin_cases player <;> norm_num [prunedValue]
  · intro _ _
    exact (prunedRoot_successor prunedValue).symm
  · intro _ _ player
    have hexact := prunedRoot_isExactSupportNash player
    constructor
    · intro hplayed
      linarith [hexact.1 hplayed]
    · intro hplayed
      linarith [hexact.2 hplayed]
  · intro target _ _
    have hpunish := punishmentValue_le_zero target
    have hvalue : 0 ≤ prunedValue target := by
      simp only [prunedValue]
      split <;> norm_num
    linarith
  · simpa using hhorizon

end GameTheory.AbsorptionWeightedRareInferiorActionBoundary
