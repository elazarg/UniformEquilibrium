import MathUE.LinearProgramming.ThreeCyclePathRigidity
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

/-!
# Normalized paths from actual singleton root play

The values below are actual terminal root-sequence payoffs, not supplied
Bellman annotations. Initial absorption and strictly positive finite
survival imply absorption after every starting date. Column balance then
normalizes the actual child surpluses by the existing zero-defect backward
recursion estimate. No periodicity or vertex visits are assumed.
-/

noncomputable section

namespace GameTheory

open Filter Math.LinearProgramming QuittingLCPClassification
open scoped Topology

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- Actual terminal surplus over the player's own singleton payoff. -/
def quittingRootSequenceSingletonSurplus
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) : ℝ :=
  quittingRootSequenceTerminalValue reward roots who time - quittingSoloReward reward who who

/-- Actual terminal surpluses are uniformly bounded by twice the finite
reward bound, including when absorption is not certain. -/
theorem abs_quittingRootSequenceSingletonSurplus_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) :
    |quittingRootSequenceSingletonSurplus reward roots time who| ≤
      2 * quittingRewardBound reward := by
  have hvalue := abs_quittingTerminalPayoff_le reward
    (quittingRootSequenceProfile reward roots time) who
    (abs_reward_le_quittingRewardBound reward)
  have hsolo := abs_reward_le_quittingRewardBound reward
    (quittingSingletonTerminal who) who
  have htriangle := abs_sub_le
    (quittingRootSequenceTerminalValue reward roots who time) 0
    (quittingSoloReward reward who who)
  simp only [sub_zero, zero_sub, abs_neg] at htriangle
  change |quittingRootSequenceTerminalValue reward roots who time| ≤ _ at hvalue
  change |quittingSoloReward reward who who| ≤ _ at hsolo
  dsimp only [quittingRootSequenceSingletonSurplus]
  linarith

/-- Every finite linear combination of actual singleton surpluses is bounded. -/
theorem abs_sum_mul_quittingRootSequenceSingletonSurplus_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : κ → ι) (weight : κ → ℝ) (time : ℕ) :
    |∑ i, weight i * quittingRootSequenceSingletonSurplus reward roots time (child i)| ≤
      ∑ i, |weight i| * (2 * quittingRewardBound reward) := by
  classical
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_quittingRootSequenceSingletonSurplus_le reward roots time (child i)) (abs_nonneg _)

/-- At an actual solo row, the joint Continue mass is one minus its owner's
Quit probability. -/
theorem quittingStationaryContinueMass_eq_one_sub_of_others_continue
    (root : ι → PMF Bool) (owner : ι)
    (hsolo : ∀ other, other ≠ owner → root other = PMF.pure false) :
    quittingStationaryContinueMass root = 1 - (root owner true).toReal := by
  classical
  have hsum := quittingRoot_continueProbability_add_quitProbability root owner
  conv_lhs => rw [eq_quittingSoloStationaryRoot_of_others_continue hsolo]
  rw [quittingStationaryContinueMass_solo]
  linarith

/-- Actual terminal surpluses obey the singleton comparison-matrix recurrence. -/
theorem quittingRootSequenceSingletonSurplus_solo_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι)
    (hsolo : ∀ time other, other ≠ owner time → roots time other = PMF.pure false)
    (time : ℕ) (who : ι) :
    quittingRootSequenceSingletonSurplus reward roots time who =
      (roots time (owner time) true).toReal * quittingSingletonMatrix reward who (owner time) +
        (1 - (roots time (owner time) true).toReal) *
          quittingRootSequenceSingletonSurplus reward roots (time + 1) who := by
  classical
  have hvalue := quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
    reward roots who time
  rw [eq_quittingSoloStationaryRoot_of_others_continue (hsolo time),
    quittingRootSuccessorPayoff_solo] at hvalue
  have hsum := quittingRoot_continueProbability_add_quitProbability (roots time) (owner time)
  have hcontinue : (roots time (owner time) false).toReal =
      1 - (roots time (owner time) true).toReal := by linarith
  rw [hcontinue] at hvalue
  dsimp only [quittingRootSequenceSingletonSurplus, quittingSingletonMatrix,
    quittingSoloReward] at hvalue ⊢
  linarith

/-- Finite linear combinations preserve the actual singleton recurrence. -/
theorem sum_mul_quittingRootSequenceSingletonSurplus_solo_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : κ → ι) (owner : ℕ → κ)
    (hsolo : ∀ time other, other ≠ child (owner time) →
      roots time other = PMF.pure false)
    (weight : κ → ℝ) (time : ℕ) :
    (∑ i, weight i * quittingRootSequenceSingletonSurplus reward roots time (child i)) =
      (roots time (child (owner time)) true).toReal *
        Matrix.vecMul weight ((quittingSingletonMatrix reward).submatrix child child) (owner time) +
      (1 - (roots time (child (owner time)) true).toReal) *
        (∑ i, weight i *
          quittingRootSequenceSingletonSurplus reward roots (time + 1) (child i)) := by
  classical
  simp_rw [quittingRootSequenceSingletonSurplus_solo_step reward roots
    (fun time => child (owner time)) hsolo time]
  unfold Matrix.vecMul dotProduct Matrix.submatrix
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.of_apply]
  ring

/-- Initial absorption propagates to every suffix when all finite prefixes
have positive survival. No positive lower bound uniform in time is required. -/
theorem tendsto_jointSurvival_zero_of_initial_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (hcontinue : ∀ time, 0 < quittingStationaryContinueMass (roots time))
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0) (start : ℕ) :
    Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0) := by
  have hzero : quittingJointSurvivalLimit roots 0 = 0 := by
    rwa [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit] at habsorb
  have hprefix : 0 < quittingJointSurvivalWeight roots 0 start := by
    rw [quittingJointSurvivalWeight_eq_prod]
    exact Finset.prod_pos fun offset _ => hcontinue (0 + offset)
  have hfactor := quittingJointSurvivalLimit_eq_prefix_mul_tail roots 0 start
  rw [hzero, Nat.zero_add] at hfactor
  have htail : quittingJointSurvivalLimit roots start = 0 :=
    (mul_eq_zero.mp hfactor.symm).resolve_left hprefix.ne'
  simpa only [htail] using tendsto_quittingJointSurvivalLimit roots start

/-- Column balance normalizes actual terminal surpluses on an embedded child.
Neither nonnegative surpluses nor positive weights are needed for this identity. -/
theorem quittingRootSequenceSingletonSurplus_weightedSum_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : κ ↪ ι) (owner : ℕ → κ)
    (hsolo : ∀ time other, other ≠ child (owner time) →
      roots time other = PMF.pure false)
    (hquit : ∀ time, (roots time (child (owner time)) true).toReal < 1)
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0)
    (weight : κ → ℝ)
    (hbalance : Matrix.vecMul weight
      ((quittingSingletonMatrix reward).submatrix child child) = 1)
    (start : ℕ) :
    ∑ i, weight i * quittingRootSequenceSingletonSurplus reward roots start (child i) = 1 := by
  classical
  let discount : ℕ → ℝ := fun time =>
    1 - (roots time (child (owner time)) true).toReal
  let error : ℕ → ℝ := fun time =>
    (∑ i, weight i * quittingRootSequenceSingletonSurplus reward roots time (child i)) - 1
  have hdiscount : ∀ time, quittingStationaryContinueMass (roots time) = discount time :=
    fun time => quittingStationaryContinueMass_eq_one_sub_of_others_continue
      (roots time) (child (owner time)) (hsolo time)
  have hdiscount0 : ∀ time, 0 ≤ discount time :=
    fun time => (sub_pos.mpr (hquit time)).le
  have hdiscount1 : ∀ time, discount time ≤ 1 := by
    intro time
    dsimp only [discount]
    exact sub_le_self _ ENNReal.toReal_nonneg
  have hrec : ∀ time, error time = discount time * error (time + 1) - 0 := by
    intro time
    have hcol := congrFun hbalance (owner time)
    have hsum := sum_mul_quittingRootSequenceSingletonSurplus_solo_step
      reward roots child owner hsolo weight time
    rw [hcol] at hsum
    simp only [Pi.one_apply] at hsum
    dsimp only [error, discount]
    linarith
  have hsurvival : ∀ first,
      Tendsto (Math.survivalProduct discount first) atTop (nhds 0) := by
    intro first
    have h := tendsto_jointSurvival_zero_of_initial_absorption reward roots
      (fun time => by rw [hdiscount]; exact sub_pos.mpr (hquit time)) habsorb first
    have heq : quittingJointSurvivalWeight roots first =
        Math.survivalProduct discount first := by
      funext length
      simp only [quittingJointSurvivalWeight_eq_survivalProduct, hdiscount]
    rwa [heq] at h
  have hbound : ∃ bound : ℝ, ∀ time, |error time| ≤ bound := by
    refine ⟨(∑ i, |weight i| * (2 * quittingRewardBound reward)) + 1, fun time => ?_⟩
    have hsum := abs_sum_mul_quittingRootSequenceSingletonSurplus_le
      reward roots child weight time
    have htriangle := abs_sub_le
      (∑ i, weight i * quittingRootSequenceSingletonSurplus reward roots time (child i)) 0 1
    simp only [sub_zero, zero_sub, abs_neg, abs_one] at htriangle
    dsimp only [error]
    linarith
  have hzero := Math.abs_prescribedError_le_of_suffixDiscrepancy
    error (fun _ => 0) discount 0 hdiscount0 hdiscount1 hrec
    (by intro first length; simp) hsurvival hbound start
  have heq := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  dsimp only [error] at heq
  linarith

/-- A linear relation among the child singleton comparison rows transports
to actual terminal surpluses under absorbing solo play. This applies to every
parent coordinate, not only players outside the child. -/
theorem quittingRootSequenceSingletonSurplus_eq_of_row_span
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : κ ↪ ι) (owner : ℕ → κ)
    (hsolo : ∀ time other, other ≠ child (owner time) →
      roots time other = PMF.pure false)
    (hquit : ∀ time, (roots time (child (owner time)) true).toReal < 1)
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0)
    (who : ι) (weight : κ → ℝ)
    (hrow : Matrix.vecMul weight
      ((quittingSingletonMatrix reward).submatrix child child) =
        fun j => quittingSingletonMatrix reward who (child j))
    (start : ℕ) :
    quittingRootSequenceSingletonSurplus reward roots start who =
      ∑ i, weight i * quittingRootSequenceSingletonSurplus reward roots start (child i) := by
  classical
  let discount : ℕ → ℝ := fun time =>
    1 - (roots time (child (owner time)) true).toReal
  let error : ℕ → ℝ := fun time =>
    quittingRootSequenceSingletonSurplus reward roots time who -
      ∑ i, weight i * quittingRootSequenceSingletonSurplus reward roots time (child i)
  have hrec : ∀ time, error time = discount time * error (time + 1) - 0 := by
    intro time
    have hsum := sum_mul_quittingRootSequenceSingletonSurplus_solo_step
      reward roots child owner hsolo weight time
    rw [congrFun hrow (owner time)] at hsum
    have hwho := quittingRootSequenceSingletonSurplus_solo_step
      reward roots (fun time => child (owner time)) hsolo time who
    dsimp only [error, discount]
    linarith
  have hdiscount : ∀ time, quittingStationaryContinueMass (roots time) = discount time :=
    fun time => quittingStationaryContinueMass_eq_one_sub_of_others_continue
      (roots time) (child (owner time)) (hsolo time)
  have hsurvival : ∀ first,
      Tendsto (Math.survivalProduct discount first) atTop (nhds 0) := by
    intro first
    have h := tendsto_jointSurvival_zero_of_initial_absorption reward roots
      (fun time => by rw [hdiscount]; exact sub_pos.mpr (hquit time)) habsorb first
    have heq : quittingJointSurvivalWeight roots first =
        Math.survivalProduct discount first := by
      funext length
      simp only [quittingJointSurvivalWeight_eq_survivalProduct, hdiscount]
    rwa [heq] at h
  have hbound : ∃ bound : ℝ, ∀ time, |error time| ≤ bound := by
    refine ⟨2 * quittingRewardBound reward +
      (∑ i, |weight i| * (2 * quittingRewardBound reward)), fun time => ?_⟩
    have hsum := abs_sum_mul_quittingRootSequenceSingletonSurplus_le
      reward roots child weight time
    have hwho := abs_quittingRootSequenceSingletonSurplus_le reward roots time who
    have htriangle := abs_sub_le
      (quittingRootSequenceSingletonSurplus reward roots time who) 0
      (∑ i, weight i * quittingRootSequenceSingletonSurplus reward roots time (child i))
    simp only [sub_zero, zero_sub, abs_neg] at htriangle
    dsimp only [error]
    linarith
  have hzero := Math.abs_prescribedError_le_of_suffixDiscrepancy
    error (fun _ => 0) discount 0
    (fun time => (sub_pos.mpr (hquit time)).le)
    (fun _ => sub_le_self _ ENNReal.toReal_nonneg) hrec
    (by intro first length; simp) hsurvival hbound start
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

/-- The actual inverse of the child comparison matrix gives every parent's
terminal-surplus row. No supplied continuation law, floor, or owner tie is
assumed for this identity. -/
theorem quittingRootSequenceSingletonSurplus_eq_inverseRow
    [DecidableEq κ]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : κ ↪ ι) (owner : ℕ → κ)
    (hsolo : ∀ time other, other ≠ child (owner time) →
      roots time other = PMF.pure false)
    (hquit : ∀ time, (roots time (child (owner time)) true).toReal < 1)
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0)
    (hdet : ((quittingSingletonMatrix reward).submatrix child child).det ≠ 0)
    (who : ι) (start : ℕ) :
    quittingRootSequenceSingletonSurplus reward roots start who =
      ∑ i, Matrix.vecMul (fun j => quittingSingletonMatrix reward who (child j))
          ((quittingSingletonMatrix reward).submatrix child child)⁻¹ i *
        quittingRootSequenceSingletonSurplus reward roots start (child i) := by
  apply quittingRootSequenceSingletonSurplus_eq_of_row_span
    reward roots child owner hsolo hquit habsorb who
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.vecMul_one]

/-- A source-faithful normalized path built from actual parent terminal
values. The child may be any finite embedded player set. -/
def normalizedSingletonPathOfRootSequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : κ ↪ ι) (owner : ℕ → κ)
    (hsolo : ∀ time other, other ≠ child (owner time) →
      roots time other = PMF.pure false)
    (hquit : ∀ time, (roots time (child (owner time)) true).toReal < 1)
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0)
    (weight : κ → ℝ) (hweight : ∀ i, 0 < weight i)
    (hbalance : Matrix.vecMul weight
      ((quittingSingletonMatrix reward).submatrix child child) = 1)
    (hfloor : ∀ time i, quittingSoloReward reward (child i) (child i) ≤
      quittingRootSequenceTerminalValue reward roots (child i) time)
    (htie : ∀ time, 0 < (roots time (child (owner time)) true).toReal →
      quittingRootSequenceTerminalValue reward roots (child (owner time)) time =
        quittingSoloReward reward (child (owner time)) (child (owner time))) :
    NormalizedSingletonPath ((quittingSingletonMatrix reward).submatrix child child) weight where
  owner := owner
  hazard := fun time => (roots time (child (owner time)) true).toReal
  value := fun time i => quittingRootSequenceSingletonSurplus reward roots time (child i)
  weight_pos := hweight
  hazard_nonneg := fun _ => ENNReal.toReal_nonneg
  hazard_lt_one := hquit
  value_nonneg := fun time i => sub_nonneg.mpr (hfloor time i)
  normalized := quittingRootSequenceSingletonSurplus_weightedSum_eq_one
    reward roots child owner hsolo hquit habsorb weight hbalance
  step := fun time i => quittingRootSequenceSingletonSurplus_solo_step
    reward roots (fun time => child (owner time)) hsolo time (child i)
  active_zero := fun time hpositive => sub_eq_zero.mpr (htie time hpositive)
  absorbs := fun start => by
    have hcontinue : ∀ time, quittingStationaryContinueMass (roots time) =
        1 - (roots time (child (owner time)) true).toReal :=
      fun time => quittingStationaryContinueMass_eq_one_sub_of_others_continue
        (roots time) (child (owner time)) (hsolo time)
    have h := tendsto_jointSurvival_zero_of_initial_absorption reward roots
      (fun time => by rw [hcontinue]; exact sub_pos.mpr (hquit time)) habsorb start
    have heq : quittingJointSurvivalWeight roots start =
        Math.survivalProduct
          (fun time => 1 - (roots time (child (owner time)) true).toReal) start := by
      funext length
      simp only [quittingJointSurvivalWeight_eq_survivalProduct, hcontinue]
    rwa [heq] at h

end GameTheory
