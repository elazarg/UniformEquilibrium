/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.LiveMassRecurrence
import UniformEquilibrium.Quitting.Stationary.Root

/-!
# Live mass under a stationary quitting profile

For a stationary quitting profile, the conditional probability of surviving
one more stage is a constant `q`: the mass assigned by the product root action
to the all-continue joint action.  Consequently the live mass after `time`
stages is exactly `q ^ time`.

This gives the elementary stationary regime split.  Either `q = 1`, in which
case play remains live with probability one at every finite time, or `q < 1`,
in which case live mass converges geometrically to zero.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The one-stage probability that every player continues under a stationary
product root action. -/
def quittingStationaryContinueMass (root : ι → PMF Bool) : ℝ :=
  ((pmfPi root) (quittingAllContinueAction : ι → Bool)).toReal

omit [DecidableEq ι] in
/-- The all-continue mass is the product of the displayed Continue
probabilities. -/
theorem quittingStationaryContinueMass_eq_prod_continueProbability
    (root : ι → PMF Bool) :
    quittingStationaryContinueMass root =
      ∏ player, (root player false).toReal := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  rfl

omit [DecidableEq ι] in
/-- A product root with all-continue mass one has every marginal pure
Continue. -/
theorem eq_pure_false_of_quittingStationaryContinueMass_eq_one
    {root : ι → PMF Bool}
    (hmass : quittingStationaryContinueMass root = 1) (player : ι) :
    root player = PMF.pure false := by
  classical
  have hprod : ∏ index : ι, (root index false).toReal = 1 := by
    rw [← ENNReal.toReal_prod]
    simpa [quittingStationaryContinueMass, quittingAllContinueAction]
      using hmass
  have hnonneg : ∀ index : ι, 0 ≤ (root index false).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hle : ∀ index : ι, (root index false).toReal ≤ 1 := by
    intro index
    rw [← ENNReal.toReal_one,
      ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
    exact PMF.coe_le_one _ _
  have hsplit : ∏ index : ι, (root index false).toReal =
      (root player false).toReal *
        ∏ index ∈ Finset.univ.erase player, (root index false).toReal :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ player)).symm
  have hrest : ∏ index ∈ Finset.univ.erase player,
      (root index false).toReal ≤ 1 :=
    Finset.prod_le_one (fun index _ => hnonneg index)
      (fun index _ => hle index)
  have hfalse : (root player false).toReal = 1 := by
    nlinarith [hnonneg player, hle player,
      Finset.prod_nonneg (fun index (_ : index ∈ Finset.univ.erase player) =>
        hnonneg index)]
  have htrue : (root player true).toReal = 0 := by
    have hsum := Math.ProbabilityMassFunction.sum_coe_fintype (root player)
    have hsumReal : (root player true).toReal + (root player false).toReal
        = 1 := by
      have hne : (root player true) + (root player false) ≠ ⊤ := by
        rw [Fintype.sum_bool] at hsum
        rw [hsum]
        simp
      rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
      rw [Fintype.sum_bool] at hsum
      rw [hsum]
      simp
    linarith
  have htrueZero : root player true = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff (root player true)).mp htrue with
      hzero | htop
    · exact hzero
    · exact absurd htop (PMF.apply_ne_top _ _)
  have hfalseOne : root player false = 1 := by
    have hsum := Math.ProbabilityMassFunction.sum_coe_fintype (root player)
    rw [Fintype.sum_bool, htrueZero, zero_add] at hsum
    exact hsum
  ext action
  cases action <;> simp [PMF.pure_apply, htrueZero, hfalseOne]

omit [DecidableEq ι] in
theorem quittingStationaryContinueMass_nonneg
    (root : ι → PMF Bool) :
    0 ≤ quittingStationaryContinueMass root :=
  ENNReal.toReal_nonneg

omit [DecidableEq ι] in
theorem quittingStationaryContinueMass_le_one
    (root : ι → PMF Bool) :
    quittingStationaryContinueMass root ≤ 1 := by
  unfold quittingStationaryContinueMass
  rw [← ENNReal.toReal_one,
    ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
  exact PMF.coe_le_one _ _

/-- Joint continuation factors into the continuation mass after forcing one
player to Continue and that player's displayed Continue probability. -/
theorem quittingStationaryContinueMass_eq_forcedContinue_mul_own
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass root =
      quittingStationaryContinueMass
          (Function.update root who (PMF.pure false)) *
        (root who false).toReal := by
  classical
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    ← Finset.mul_prod_erase Finset.univ
      (fun player ↦ (root player false).toReal) (Finset.mem_univ who)]
  have hforced :
      (∏ player, (Function.update root who (PMF.pure false) player false).toReal) =
        ∏ player ∈ Finset.univ.erase who, (root player false).toReal := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun player ↦
        (Function.update root who (PMF.pure false) player false).toReal)
      (Finset.mem_univ who)]
    have hown :
        (Function.update root who (PMF.pure false) who false).toReal = 1 := by
      simp
    rw [hown, one_mul]
    refine Finset.prod_congr rfl fun player hplayer ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hplayer)]
  rw [hforced]
  ring

omit [DecidableEq ι] in
/-- The product mass of joint continuation is at most each selected player's
own Continue probability. -/
theorem quittingStationaryContinueMass_le_ownContinueProbability
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass root ≤ (root who false).toReal := by
  classical
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    ← Finset.mul_prod_erase Finset.univ
      (fun player ↦ (root player false).toReal) (Finset.mem_univ who)]
  have hprod :
      (∏ player ∈ Finset.univ.erase who, (root player false).toReal) ≤ 1 :=
    Finset.prod_le_one
      (fun _ _ ↦ ENNReal.toReal_nonneg)
      (fun player _ ↦ ENNReal.toReal_mono ENNReal.one_ne_top
        ((root player).coe_le_one false))
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg hprod

/-- Forcing one coordinate to Continue can only increase the all-continue
mass. -/
theorem quittingStationaryContinueMass_le_update_pure_false
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass root ≤
      quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_le_prod
  · intro player _
    exact ENNReal.toReal_nonneg
  · intro player _
    by_cases hplayer : player = who
    · subst player
      simp only [Function.update_self, PMF.pure_apply]
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        ((root who).coe_le_one false)
    · simp [Function.update_of_ne hplayer]

/-- One-stage probability that the product root action absorbs. -/
def quittingRootAbsorptionMass (root : ι → PMF Bool) : ℝ :=
  1 - quittingStationaryContinueMass root

omit [DecidableEq ι] in
/-- Root absorption mass is nonnegative. -/
theorem quittingRootAbsorptionMass_nonneg
    (root : ι → PMF Bool) :
    0 ≤ quittingRootAbsorptionMass root := by
  exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one root)

/-- One-stage absorption probability after forcing `who` to Continue.  This
is the opponent-absorption hazard faced by `who`. -/
def quittingRootOpponentAbsorptionMass
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootAbsorptionMass
    (Function.update root who (PMF.pure false))

/-- Probability that every opponent of `who` continues at `root`. -/
def quittingRootOpponentContinueMass
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingStationaryContinueMass
    (Function.update root who (PMF.pure false))

/-- Opponent absorption is the union probability of the opponents' Quit
marginals. -/
theorem quittingRootOpponentAbsorptionMass_eq_one_sub_prod
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentAbsorptionMass root who =
      1 - ∏ other ∈ Finset.univ.erase who,
        (1 - (root other true).toReal) := by
  classical
  have hproduct :
      (∏ player,
          (Function.update root who (PMF.pure false) player false).toReal) =
        ∏ other ∈ Finset.univ.erase who,
          (root other false).toReal := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun player =>
        (Function.update root who (PMF.pure false) player false).toReal)
      (Finset.mem_univ who)]
    rw [Function.update_self]
    simp only [PMF.pure_apply, if_true, ENNReal.toReal_one, one_mul]
    apply Finset.prod_congr rfl
    intro other hother
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability, hproduct]
  congr 1
  apply Finset.prod_congr rfl
  intro other _
  have hsum : (root other false).toReal + (root other true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one (root other)
  linarith

theorem quittingRootOpponentContinueMass_nonneg
    (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingRootOpponentContinueMass root who :=
  quittingStationaryContinueMass_nonneg _

theorem quittingRootOpponentContinueMass_le_one
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentContinueMass root who ≤ 1 :=
  quittingStationaryContinueMass_le_one _

/-- Opponent Continue mass and opponent absorption mass are complementary. -/
theorem quittingRootOpponentContinueMass_eq_one_sub_absorptionMass
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentContinueMass root who =
      1 - quittingRootOpponentAbsorptionMass root who := by
  unfold quittingRootOpponentContinueMass
    quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  ring

theorem quittingRootOpponentAbsorptionMass_nonneg
    (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingRootOpponentAbsorptionMass root who := by
  have hcontinue := quittingRootOpponentContinueMass_le_one root who
  rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass] at hcontinue
  linarith

theorem quittingRootOpponentAbsorptionMass_le_one
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentAbsorptionMass root who ≤ 1 := by
  have hcontinue := quittingRootOpponentContinueMass_nonneg root who
  rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass] at hcontinue
  linarith

/-- Deleted Continue mass is at most every displayed opponent's Continue
probability. -/
theorem quittingRootOpponentContinueMass_le_continueProbability_of_ne
    (root : ι → PMF Bool) {who other : ι} (hne : other ≠ who) :
    quittingRootOpponentContinueMass root who ≤
      (root other false).toReal := by
  have hmass := quittingStationaryContinueMass_le_ownContinueProbability
    (Function.update root who (PMF.pure false)) other
  simpa [quittingRootOpponentContinueMass, Function.update_of_ne hne] using
    hmass

/-- Forcing one player to Continue only removes absorption events. -/
theorem quittingRootOpponentAbsorptionMass_le_absorptionMass
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentAbsorptionMass root who ≤
      quittingRootAbsorptionMass root := by
  have hcontinue :=
    quittingStationaryContinueMass_le_update_pure_false root who
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  linarith

omit [DecidableEq ι] in
/-- The expectation of the indicator of a nonempty quitter set is exactly
the one-stage absorption mass. -/
theorem expect_quittingNonemptyIndicator_eq_absorptionMass
    (root : ι → PMF Bool) :
    expect (pmfPi root) (fun action ↦
        if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) =
      quittingRootAbsorptionMass root := by
  let allContinue : ι → Bool := quittingAllContinueAction
  have hindicator :
      (fun action : ι → Bool ↦
          if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) =
        fun action ↦ 1 - if action = allContinue then (1 : ℝ) else 0 := by
    funext action
    by_cases hquit : (quittingQuitters action).Nonempty
    · have hne : action ≠ allContinue := by
        intro heq
        subst action
        simp [allContinue] at hquit
      simp [hquit, hne]
    · have heq : action = allContinue :=
        eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
          action hquit
      subst action
      simp [allContinue]
  rw [hindicator, expect_sub, expect_const,
    ← Math.Probability.apply_toReal_eq_expect_indicator]
  rfl

omit [DecidableEq ι] in
/-- Stationarity makes the conditional all-continue probability independent
of the time and the live history. -/
@[simp] theorem quittingJointContinueMass_stationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (time : ℕ) :
    quittingJointContinueMass reward
        (quittingStationaryProfile reward root) time =
      quittingStationaryContinueMass root :=
  rfl

omit [DecidableEq ι] in
/-- Exact geometric survival under a stationary quitting profile. -/
@[simp] theorem quittingLiveMass_stationary_eq_pow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (time : ℕ) :
    quittingLiveMass reward (quittingStationaryProfile reward root) time =
      quittingStationaryContinueMass root ^ time := by
  classical
  induction time with
  | zero => simp
  | succ time ih =>
      rw [quittingLiveMass_succ, ih,
        quittingJointContinueMass_stationary, pow_succ]

omit [DecidableEq ι] in
/-- If the stationary profile sometimes absorbs, its live mass converges
geometrically to zero. -/
theorem tendsto_quittingLiveMass_stationary_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (hquit : quittingStationaryContinueMass root < 1) :
    Filter.Tendsto
      (quittingLiveMass reward (quittingStationaryProfile reward root))
      Filter.atTop (nhds 0) := by
  have hlive :
      quittingLiveMass reward (quittingStationaryProfile reward root) =
        fun time => quittingStationaryContinueMass root ^ time := by
    funext time
    exact quittingLiveMass_stationary_eq_pow reward root time
  rw [hlive]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (quittingStationaryContinueMass_nonneg root) hquit

omit [DecidableEq ι] in
/-- If the stationary all-continue probability is one, the profile remains
live with probability one at every finite time. -/
theorem quittingLiveMass_stationary_eq_one_of_continueMass_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (hcontinue : quittingStationaryContinueMass root = 1)
    (time : ℕ) :
    quittingLiveMass reward (quittingStationaryProfile reward root) time = 1 := by
  rw [quittingLiveMass_stationary_eq_pow, hcontinue, one_pow]

omit [DecidableEq ι] in
/-- Every stationary quitting profile lies in the persistent-live
endpoint or the geometrically absorbing regime. -/
theorem quittingStationary_liveMass_regime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingStationaryContinueMass root = 1 ∨
      Filter.Tendsto
        (quittingLiveMass reward (quittingStationaryProfile reward root))
        Filter.atTop (nhds 0) := by
  rcases eq_or_lt_of_le (quittingStationaryContinueMass_le_one root) with
    hcontinue | hquit
  · exact Or.inl hcontinue
  · exact Or.inr
      (tendsto_quittingLiveMass_stationary_zero reward root hquit)

end GameTheory
