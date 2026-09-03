/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CyclicSupersolution
import UniformEquilibrium.Quitting.Cycles.SingletonArcCycle
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# A two-block uniform payoff on a four-player singleton fibre

Two prescribed singleton rows support a cyclic singleton-mesh profile whose
terminal Nash error tends to zero while its payoff approaches the second row.
Only own-singleton floors are required from the other two rows.  Every
nonsingleton terminal reward remains arbitrary and enters only through the
finite collision bound.
-/

noncomputable section

namespace GameTheory
namespace FinFourTwoBlockSingletonFiber

open Filter Math.Probability Math.PMFProduct StochasticGame

abbrev Player := Fin 4

private theorem player_cases (who : Player) :
    who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
  fin_cases who <;> simp

private theorem block_cases (block : Fin 2) : block = 0 ∨ block = 1 := by
  fin_cases block <;> simp

/-- Singleton reward of the first active owner. -/
def firstOwnerSingletonRow (who : Player) : ℝ :=
  if who.val = 0 then 1 else if who.val = 1 then -3 / 4
  else if who.val = 2 then 0 else 1 / 2

/-- Singleton reward of the second active owner and the limiting target. -/
def targetPayoff (who : Player) : ℝ :=
  if who.val = 0 then 1 else if who.val = 1 then -1 / 2
  else if who.val = 2 then 0 else -1 / 4

/-- The third singleton row in the original four-row fibre. -/
def playerTwoSingletonRow (who : Player) : ℝ :=
  if who.val = 0 then 0 else if who.val = 1 then 1
  else if who.val = 2 then -1 else 0

/-- The fourth singleton row in the original four-row fibre. -/
def playerThreeSingletonRow (who : Player) : ℝ :=
  if who.val = 0 then 1 / 4 else if who.val = 1 then 1 / 2
  else if who.val = 2 then 1 / 4 else -1 / 4

/-- The exact singleton information used by the two-block construction.

The off-diagonal coordinates of singleton rows two and three are deliberately
absent: only those players' own singleton rewards enter unilateral stopping
bounds. -/
structure TwoBlockTargetSingletonConditions
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) : Prop where
  firstOwnerRow : quittingSoloReward reward 0 = firstOwnerSingletonRow
  secondOwnerRow : quittingSoloReward reward 1 = targetPayoff
  playerTwoOwnSingleton_le : quittingSoloReward reward 2 2 ≤ 0
  playerThreeOwnSingleton_le : quittingSoloReward reward 3 3 ≤ -1 / 4

/-- Positive first-block total hazards. -/
abbrev HazardParameter := Set.Ioo (0 : ℝ) 1

/-- Value at the entrance to the first owner block. -/
def firstBlockPayoff (δ : HazardParameter) (who : Player) : ℝ :=
  if who.val = 0 then 1
  else if who.val = 1 then -1 / 2 - δ.1 / (2 * (1 + δ.1))
  else if who.val = 2 then 0
  else -1 / 4 + 3 * δ.1 / (2 * (1 + δ.1))

/-- Value at the entrance to the second owner block. -/
def secondBlockPayoff (δ : HazardParameter) (who : Player) : ℝ :=
  if who.val = 0 then 1
  else if who.val = 1 then -1 / 2 - δ.1 / (4 * (1 + δ.1))
  else if who.val = 2 then 0
  else -1 / 4 + 3 * δ.1 / (4 * (1 + δ.1))

/-- Owners of the two coarse blocks. -/
def blockOwner (block : Fin 2) : Player := if block.val = 0 then 0 else 1

/-- Total absorption hazard of each coarse block. -/
def blockHazard (δ : HazardParameter) (block : Fin 2) : ℝ :=
  if block.val = 0 then δ.1 else 1 / 2

/-- The two coarse values in chronological order. -/
def coarsePayoff (δ : HazardParameter) (block : Fin 2) : Payoff Player :=
  if block.val = 0 then firstBlockPayoff δ else secondBlockPayoff δ

/-- Largest own-singleton deficit of the two coarse values. -/
def singletonDefect (δ : HazardParameter) : ℝ :=
  δ.1 / (2 * (1 + δ.1))

theorem blockHazard_nonneg (δ : HazardParameter) (block : Fin 2) :
    0 ≤ blockHazard δ block := by
  fin_cases block <;> simp [blockHazard, δ.2.1.le]

theorem blockHazard_lt_one (δ : HazardParameter) (block : Fin 2) :
    blockHazard δ block < 1 := by
  fin_cases block
  · simpa [blockHazard] using δ.2.2
  · norm_num [blockHazard]

theorem singletonDefect_nonneg (δ : HazardParameter) :
    0 ≤ singletonDefect δ := by
  exact div_nonneg δ.2.1.le
    (mul_nonneg (by norm_num) (by linarith [δ.2.1]))

/-- The displayed coarse values solve the exact two-block Bellman cycle. -/
theorem coarsePayoff_arc
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : TwoBlockTargetSingletonConditions reward)
    (δ : HazardParameter) (block : Fin 2) :
    coarsePayoff δ block =
      quittingSingletonArcPayoff (blockHazard δ block)
        (quittingSoloReward reward (blockOwner block))
        (coarsePayoff δ (finRotate 2 block)) := by
  rcases conditions with ⟨hzero, hone, _htwo, _hthree⟩
  have hdenom : 1 + δ.1 ≠ 0 := ne_of_gt (by linarith [δ.2.1])
  have hrotateZero : finRotate 2 (0 : Fin 2) = 1 := by decide
  have hrotateOne : finRotate 2 (1 : Fin 2) = 0 := by decide
  rcases block_cases block with rfl | rfl <;> funext who <;>
    rcases player_cases who with rfl | rfl | rfl | rfl <;>
      norm_num [coarsePayoff, blockHazard, blockOwner, firstBlockPayoff,
        secondBlockPayoff, quittingSingletonArcPayoff, hzero, hone,
        firstOwnerSingletonRow, targetPayoff, hrotateZero, hrotateOne]
  all_goals field_simp [hdenom]
  all_goals ring

/-- The second block value approaches the fixed target at the displayed
coordinatewise rate. -/
theorem secondBlockPayoff_sub_target_abs_le (δ : HazardParameter)
    (who : Player) :
    |secondBlockPayoff δ who - targetPayoff who| ≤
      3 * δ.1 / (4 * (1 + δ.1)) := by
  have hdenom : 0 < 4 * (1 + δ.1) := by nlinarith [δ.2.1]
  have hratio : 0 ≤ δ.1 / (4 * (1 + δ.1)) :=
    div_nonneg δ.2.1.le hdenom.le
  have hthreeRatio : 0 ≤ 3 * δ.1 / (4 * (1 + δ.1)) := by
    exact div_nonneg (mul_nonneg (by norm_num) δ.2.1.le) hdenom.le
  rcases player_cases who with rfl | rfl | rfl | rfl
  · norm_num [secondBlockPayoff, targetPayoff]
    exact hthreeRatio
  · norm_num [secondBlockPayoff, targetPayoff]
    rw [show -(1 / 2 : ℝ) - δ.1 / (4 * (1 + δ.1)) + 1 / 2 =
      -(δ.1 / (4 * (1 + δ.1))) by ring, abs_neg,
      abs_of_nonneg hratio]
    rw [show 3 * δ.1 / (4 * (1 + δ.1)) =
      3 * (δ.1 / (4 * (1 + δ.1))) by ring]
    nlinarith
  · norm_num [secondBlockPayoff, targetPayoff]
    exact hthreeRatio
  · norm_num [secondBlockPayoff, targetPayoff]
    rw [abs_of_nonneg hthreeRatio]

/-- Both coarse values lie no more than `singletonDefect` below every
player's own singleton reward. -/
theorem soloReward_le_coarsePayoff_add_singletonDefect
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : TwoBlockTargetSingletonConditions reward)
    (δ : HazardParameter) (block : Fin 2) (who : Player) :
    quittingSoloReward reward who who ≤
      coarsePayoff δ block who + singletonDefect δ := by
  rcases conditions with ⟨hzero, hone, htwo, hthree⟩
  have hdefect := singletonDefect_nonneg δ
  have hdenom : 0 < 1 + δ.1 := by linarith [δ.2.1]
  have hzeroOwn : quittingSoloReward reward 0 0 = 1 := by
    simpa [firstOwnerSingletonRow] using congrFun hzero (0 : Player)
  have honeOwn : quittingSoloReward reward 1 1 = -1 / 2 := by
    simpa [targetPayoff] using congrFun hone (1 : Player)
  rcases block_cases block with rfl | rfl
  · rcases player_cases who with rfl | rfl | rfl | rfl
    · simp [coarsePayoff, firstBlockPayoff, hzeroOwn]
      exact hdefect
    · rw [honeOwn]
      simp [coarsePayoff, firstBlockPayoff, singletonDefect]
    · simpa [coarsePayoff, firstBlockPayoff] using htwo.trans hdefect
    · refine hthree.trans ?_
      simp [coarsePayoff, firstBlockPayoff, singletonDefect]
      have hratio : 0 ≤ 3 * δ.1 / (2 * (1 + δ.1)) := by
        exact div_nonneg (mul_nonneg (by norm_num) δ.2.1.le)
          (mul_nonneg (by norm_num) hdenom.le)
      have hdefect' : 0 ≤ δ.1 / (2 * (1 + δ.1)) := by
        exact div_nonneg δ.2.1.le
          (mul_nonneg (by norm_num) hdenom.le)
      linarith
  · rcases player_cases who with rfl | rfl | rfl | rfl
    · simp [coarsePayoff, secondBlockPayoff, hzeroOwn]
      exact hdefect
    · rw [honeOwn]
      simp [coarsePayoff, secondBlockPayoff, singletonDefect]
      field_simp [hdenom.ne']
      nlinarith [δ.2.1]
    · simpa [coarsePayoff, secondBlockPayoff] using htwo.trans hdefect
    · refine hthree.trans ?_
      simp [coarsePayoff, secondBlockPayoff, singletonDefect]
      have hratio : 0 ≤ 3 * δ.1 / (4 * (1 + δ.1)) := by
        exact div_nonneg (mul_nonneg (by norm_num) δ.2.1.le)
          (mul_nonneg (by norm_num) hdenom.le)
      have hdefect' : 0 ≤ δ.1 / (2 * (1 + δ.1)) := by
        exact div_nonneg δ.2.1.le
          (mul_nonneg (by norm_num) hdenom.le)
      linarith

/-- The subdivided singleton-root cycle. -/
def meshCycleRoot (δ : HazardParameter) (m : ℕ) :
    Fin (2 * m) → Player → PMF Bool :=
  quittingSingletonArcCycleRoot blockOwner (blockHazard δ) m
    (blockHazard_nonneg δ) (blockHazard_lt_one δ)

/-- Bellman value attached to every subdivided phase. -/
def meshCycleValue
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (δ : HazardParameter) (m : ℕ) : Fin (2 * m) → Payoff Player :=
  quittingSingletonArcCycleValue reward blockOwner (blockHazard δ)
    (coarsePayoff δ) m

/-- The periodic profile starts at the second owner block. -/
def meshProfile
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (δ : HazardParameter) (m : ℕ) (hm : 0 < m) :
    (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward (meshCycleRoot δ m)
    (quittingSingletonMeshInitialPhase (1 : Fin 2) m hm)

/-- The mesh values satisfy exact prescribed-policy Bellman transport. -/
theorem meshCycleValue_policy
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : TwoBlockTargetSingletonConditions reward)
    (δ : HazardParameter) (m : ℕ) (hm : 0 < m)
    (phase : Fin (2 * m)) :
    meshCycleValue reward δ m phase =
      quittingRootSuccessorPayoff reward
        (meshCycleValue reward δ m (finRotate (2 * m) phase))
        (meshCycleRoot δ m phase) := by
  let block := quittingSingletonMeshBlock phase
  let offset := quittingSingletonMeshOffset phase
  have hnext := quittingSingletonArcCycleValue_rotate
    reward blockOwner (blockHazard δ) (coarsePayoff δ) m hm
      (blockHazard_lt_one δ) (coarsePayoff_arc conditions δ) phase
  have hstep := quittingMeshPayoffInterpolant_hazard_step
    (blockHazard_lt_one δ block)
    (quittingSoloReward reward (blockOwner block)) (coarsePayoff δ block)
    m offset.val
  rw [← hnext] at hstep
  dsimp only [meshCycleValue, meshCycleRoot,
    quittingSingletonArcCycleValue, quittingSingletonArcCycleRoot,
    block, offset]
  rw [quittingRootSuccessorPayoff_solo,
    quittingMeshHazardCoin_true_toReal,
    quittingMeshHazardCoin_false_toReal]
  exact hstep

/-- The own-singleton deficit bound holds at every microphase. -/
theorem soloReward_le_meshCycleValue_add_singletonDefect
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : TwoBlockTargetSingletonConditions reward)
    (δ : HazardParameter) (m : ℕ) (hm : 0 < m)
    (phase : Fin (2 * m)) (who : Player) :
    quittingSoloReward reward who who ≤
      meshCycleValue reward δ m phase who + singletonDefect δ := by
  let block := quittingSingletonMeshBlock phase
  let offset := quittingSingletonMeshOffset phase
  have hlower := le_quittingMeshPayoffInterpolant_of_arcEndpoints
    (blockHazard_nonneg δ block) (blockHazard_lt_one δ block) hm
    (coarsePayoff_arc conditions δ block)
    (lower := fun player =>
      quittingSoloReward reward player player - singletonDefect δ)
    (fun player => by
      linarith [soloReward_le_coarsePayoff_add_singletonDefect
        conditions δ block player])
    (fun player => by
      linarith [soloReward_le_coarsePayoff_add_singletonDefect
        conditions δ (finRotate 2 block) player])
    offset.val offset.isLt.le who
  change quittingSoloReward reward who who ≤
    quittingMeshPayoffInterpolant
        (quittingSoloReward reward (blockOwner block))
        (coarsePayoff δ block)
        (1 - quittingMeshHazard (blockHazard δ block) m)
        offset.val who + singletonDefect δ
  linarith

/-- Every pure-Continue branch is weakly below the current mesh value. -/
theorem meshCycle_continueValue_le
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : TwoBlockTargetSingletonConditions reward)
    (δ : HazardParameter) (m : ℕ) (hm : 0 < m)
    (phase : Fin (2 * m)) (who : Player) :
    quittingStationaryFixedOpponentsContinueReward reward
          (meshCycleRoot δ m phase) who +
        quittingStationaryFixedOpponentsContinueMass
            (meshCycleRoot δ m phase) who *
          meshCycleValue reward δ m (finRotate (2 * m) phase) who ≤
      meshCycleValue reward δ m phase who := by
  let block := quittingSingletonMeshBlock phase
  let offset := quittingSingletonMeshOffset phase
  let owner := blockOwner block
  let h := quittingMeshHazard (blockHazard δ block) m
  have hp0 : 0 ≤ blockHazard δ block := blockHazard_nonneg δ block
  have hp1 : blockHazard δ block < 1 := blockHazard_lt_one δ block
  have hh0 : 0 ≤ h := quittingMeshHazard_nonneg m hp0 hp1.le
  have hh1 : h < 1 := quittingMeshHazard_lt_one hp1 m
  have hpow := one_sub_quittingMeshHazard_pow hp1.le hm
  have hpPos : 0 < blockHazard δ block := by
    rcases block_cases block with hblock | hblock
    · rw [hblock]
      simpa [blockHazard] using δ.2.1
    · rw [hblock]
      norm_num [blockHazard]
  have hhPos : 0 < h := by
    apply lt_of_le_of_ne hh0
    intro hzero
    have hzero' : h = 0 := hzero.symm
    dsimp only [h] at hzero'
    rw [hzero'] at hpow
    simp only [sub_zero, one_pow] at hpow
    linarith
  by_cases hwho : who = owner
  · subst who
    have hcurrentLeSolo :
        meshCycleValue reward δ m phase owner ≤
          quittingSoloReward reward owner owner := by
      dsimp only [meshCycleValue, quittingSingletonArcCycleValue,
        block, offset, owner]
      rcases block_cases (quittingSingletonMeshBlock phase) with hblock | hblock
      · rw [hblock]
        have hrow := congrFun conditions.firstOwnerRow (0 : Player)
        change quittingMeshPayoffInterpolant
            (quittingSoloReward reward 0) (firstBlockPayoff δ)
              (1 - quittingMeshHazard (blockHazard δ 0) m)
              (quittingSingletonMeshOffset phase).val 0 ≤
          quittingSoloReward reward 0 0
        have hactive : firstBlockPayoff δ 0 =
            quittingSoloReward reward 0 0 := by
          rw [hrow]
          norm_num [firstBlockPayoff, firstOwnerSingletonRow]
        exact (quittingMeshPayoffInterpolant_eq_root_of_eq hactive _).le
      · rw [hblock]
        have hrow := congrFun conditions.secondOwnerRow (1 : Player)
        norm_num [targetPayoff] at hrow
        have hdenom : 0 < 4 * (1 + δ.1) := by
          nlinarith [δ.2.1]
        have hfactor : 0 ≤
            ((((1 - blockHazard δ 1) ^ ((m : ℝ)⁻¹ : ℝ)) ^
              (quittingSingletonMeshOffset phase).val : ℝ)⁻¹) := by
          exact inv_nonneg.mpr (pow_nonneg
            (Real.rpow_nonneg (sub_nonneg.mpr
              (blockHazard_lt_one δ 1).le) _) _)
        change quittingMeshPayoffInterpolant
            (quittingSoloReward reward 1) (secondBlockPayoff δ)
              (1 - quittingMeshHazard (blockHazard δ 1) m)
              (quittingSingletonMeshOffset phase).val 1 ≤
          quittingSoloReward reward 1 1
        unfold quittingMeshPayoffInterpolant quittingMeshInterpolant
        rw [hrow]
        norm_num [secondBlockPayoff, targetPayoff]
        have hnegative :
            -(1 / 2 : ℝ) - δ.1 / (4 * (1 + δ.1)) - -(1 / 2) ≤ 0 := by
          nlinarith [div_nonneg δ.2.1.le hdenom.le]
        exact mul_nonpos_of_nonneg_of_nonpos hfactor (by linarith)
    have hpolicyWho := congrFun
      (meshCycleValue_policy conditions δ m hm phase) owner
    dsimp only [meshCycleRoot, quittingSingletonArcCycleRoot,
      block, offset, owner, h] at hpolicyWho ⊢
    rw [quittingRootSuccessorPayoff_solo,
      quittingMeshHazardCoin_true_toReal,
      quittingMeshHazardCoin_false_toReal] at hpolicyWho
    rw [quittingStationaryFixedOpponentsContinueReward_solo_owner,
      quittingStationaryFixedOpponentsContinueMass_solo_owner]
    simp only [zero_add, one_mul]
    change meshCycleValue reward δ m (finRotate (2 * m) phase) owner ≤
      meshCycleValue reward δ m phase owner
    nlinarith
  · have hpolicyWho := congrFun
      (meshCycleValue_policy conditions δ m hm phase) who
    dsimp only [meshCycleRoot, quittingSingletonArcCycleRoot,
      block, offset, owner, h] at hpolicyWho ⊢
    rw [quittingRootSuccessorPayoff_solo,
      quittingMeshHazardCoin_true_toReal,
      quittingMeshHazardCoin_false_toReal] at hpolicyWho
    rw [quittingStationaryFixedOpponentsContinueReward_solo_other
        reward hwho,
      quittingStationaryFixedOpponentsContinueMass_solo_other hwho,
      quittingMeshHazardCoin_true_toReal,
      quittingMeshHazardCoin_false_toReal]
    exact hpolicyWho.ge

/-- Every pure-Quit branch is bounded by the coarse singleton defect plus the
microhazard-scaled collision cap. -/
theorem meshCycle_quitValue_le
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : TwoBlockTargetSingletonConditions reward)
    (δ : HazardParameter) (m : ℕ) (hm : 0 < m)
    (phase : Fin (2 * m)) (who : Player) :
    quittingStationaryFixedOpponentsQuitValue reward
        (meshCycleRoot δ m phase) who ≤
      meshCycleValue reward δ m phase who +
        (singletonDefect δ + 2 * quittingRewardBound reward *
          quittingMeshHazard
            (blockHazard δ (quittingSingletonMeshBlock phase)) m) := by
  let block := quittingSingletonMeshBlock phase
  let owner := blockOwner block
  let h := quittingMeshHazard (blockHazard δ block) m
  have hh0 : 0 ≤ h := quittingMeshHazard_nonneg m
    (blockHazard_nonneg δ block) (blockHazard_lt_one δ block).le
  have hsolo := soloReward_le_meshCycleValue_add_singletonDefect
    conditions δ m hm phase who
  by_cases hwho : who = owner
  · subst who
    dsimp only [meshCycleRoot, quittingSingletonArcCycleRoot,
      block, owner, h]
    rw [quittingStationaryFixedOpponentsQuitValue_solo_owner]
    have hcollision0 :
        0 ≤ 2 * quittingRewardBound reward * h :=
      mul_nonneg (mul_nonneg (by norm_num)
        (quittingRewardBound_nonneg reward)) hh0
    linarith
  · have hcollision := abs_reward_le_quittingRewardBound reward
      ⟨{owner, who}, by simp⟩ who
    have hsoloBound := abs_reward_le_quittingRewardBound reward
      ⟨{who}, by simp⟩ who
    have hgap : max
        (quittingSingletonCollisionReward reward owner who -
          quittingSoloReward reward who who) 0 ≤
        2 * quittingRewardBound reward := by
      have hdiff : quittingSingletonCollisionReward reward owner who -
          quittingSoloReward reward who who ≤
          2 * quittingRewardBound reward := by
        unfold quittingSingletonCollisionReward quittingSoloReward at *
        rw [abs_le] at hcollision hsoloBound
        linarith
      exact max_le hdiff (mul_nonneg (by norm_num)
        (quittingRewardBound_nonneg reward))
    have hmix := singletonQuitMix_le_value_add_hazard_mul
      hh0 hsolo hgap
    dsimp only [meshCycleRoot, quittingSingletonArcCycleRoot,
      block, owner, h]
    rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
      reward hwho,
      quittingMeshHazardCoin_false_toReal,
      quittingMeshHazardCoin_true_toReal]
    dsimp only [block, owner, h] at hmix
    linarith

/-- Exact deleted-opponent survival through one complete mesh cycle. -/
theorem meshCycle_opponentProduct_eq (δ : HazardParameter)
    (m : ℕ) (hm : 0 < m) (who : Player) :
    (∏ phase : Fin (2 * m),
      quittingStationaryFixedOpponentsContinueMass
        (meshCycleRoot δ m phase) who) =
      ![(1 / 2 : ℝ), 1 - δ.1, (1 - δ.1) / 2,
        (1 - δ.1) / 2] who := by
  dsimp only [meshCycleRoot]
  rw [prod_quittingSingletonArcCycleRoot_continueMass
    blockOwner (blockHazard δ) m hm (blockHazard_nonneg δ)
      (blockHazard_lt_one δ) who]
  fin_cases who <;>
    norm_num [blockOwner, blockHazard, Fin.prod_univ_two] <;> ring

/-- One fixed mesh is terminal Nash with the explicit two-scale error and has
exactly the second block's payoff. -/
theorem meshProfile_isTerminalNash_and_hasPayoff
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : TwoBlockTargetSingletonConditions reward)
    (δ : HazardParameter) (m : ℕ) (hm : 0 < m) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (singletonDefect δ + 2 * quittingRewardBound reward *
          max (quittingMeshHazard δ.1 m)
            (quittingMeshHazard (1 / 2) m))
        (meshProfile reward δ m hm) ∧
      quittingTerminalPayoff reward (meshProfile reward δ m hm) =
        secondBlockPayoff δ := by
  let e := singletonDefect δ + 2 * quittingRewardBound reward *
    max (quittingMeshHazard δ.1 m)
      (quittingMeshHazard (1 / 2) m)
  let initial := quittingSingletonMeshInitialPhase (1 : Fin 2) m hm
  have hmax0 : 0 ≤ max (quittingMeshHazard δ.1 m)
      (quittingMeshHazard (1 / 2) m) := by
    exact (quittingMeshHazard_nonneg m δ.2.1.le δ.2.2.le).trans
      (le_max_left _ _)
  have he0 : 0 ≤ e := add_nonneg (singletonDefect_nonneg δ)
    (mul_nonneg (mul_nonneg (by norm_num)
      (quittingRewardBound_nonneg reward)) hmax0)
  have hpolicy := meshCycleValue_policy conditions δ m hm
  have hquit : ∀ phase who,
      quittingStationaryFixedOpponentsQuitValue reward
          (meshCycleRoot δ m phase) who ≤
        meshCycleValue reward δ m phase who + e := by
    intro phase who
    have hlocal := meshCycle_quitValue_le conditions δ m hm phase who
    have hhazard : quittingMeshHazard
        (blockHazard δ (quittingSingletonMeshBlock phase)) m ≤
        max (quittingMeshHazard δ.1 m)
          (quittingMeshHazard (1 / 2) m) := by
      rcases block_cases (quittingSingletonMeshBlock phase) with hblock | hblock
      · rw [hblock]
        simp [blockHazard]
      · rw [hblock]
        simp [blockHazard]
    have hscaled :
        2 * quittingRewardBound reward *
            quittingMeshHazard
              (blockHazard δ (quittingSingletonMeshBlock phase)) m ≤
          2 * quittingRewardBound reward *
            max (quittingMeshHazard δ.1 m)
              (quittingMeshHazard (1 / 2) m) :=
      mul_le_mul_of_nonneg_left hhazard
        (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
    exact hlocal.trans (by dsimp only [e]; linarith)
  have hcontinue := meshCycle_continueValue_le conditions δ m hm
  have hcontracts : ∀ who,
      (∏ phase : Fin (2 * m),
        quittingStationaryFixedOpponentsContinueMass
          (meshCycleRoot δ m phase) who) < 1 := by
    intro who
    rw [meshCycle_opponentProduct_eq δ m hm who]
    fin_cases who <;> norm_num <;> nlinarith [δ.2.1, δ.2.2]
  have hnash :=
    isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_and_continueUpperBound
      reward (meshCycleRoot δ m) (meshCycleValue reward δ m) initial he0
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) hpolicy hquit hcontinue hcontracts
  constructor
  · simpa only [meshProfile, initial, e] using hnash
  · have hcyclicValue :=
      eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
        reward (meshCycleRoot δ m) (meshCycleValue reward δ m)
          hpolicy hcontracts
    change quittingTerminalPayoff reward
        (quittingCyclicBehaviorProfile reward (meshCycleRoot δ m) initial) =
      secondBlockPayoff δ
    rw [quittingTerminalPayoff_cyclicBehaviorProfile, ← hcyclicValue]
    exact quittingSingletonArcCycleValue_initialPhase
      reward blockOwner (blockHazard δ) (coarsePayoff δ) (1 : Fin 2) m hm

/-- At every positive accuracy, one terminal approximate Nash profile both
approximates the fixed target and is evaluated against unrestricted behavioral
deviations. -/
theorem exists_terminalNash_and_payoff_close_to_target
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : TwoBlockTargetSingletonConditions reward)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        ∀ who,
          |quittingTerminalPayoff reward profile who - targetPayoff who| ≤ ε := by
  let δValue : ℝ := min (1 / 2) (ε / 4)
  have hδValue0 : 0 < δValue := by
    dsimp only [δValue]
    exact lt_min (by norm_num) (div_pos hε (by norm_num))
  have hδValue1 : δValue < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  let δ : HazardParameter := ⟨δValue, hδValue0, hδValue1⟩
  have hδLe : δ.1 ≤ ε / 4 := by
    exact min_le_right _ _
  have hdefect : singletonDefect δ < ε / 2 := by
    have hdenom : 0 < 2 * (1 + δ.1) := by nlinarith [δ.2.1]
    rw [singletonDefect, div_lt_iff₀ hdenom]
    have hεδ : 0 < ε * δ.1 := mul_pos hε δ.2.1
    nlinarith
  have htarget : 3 * δ.1 / (4 * (1 + δ.1)) < ε := by
    have hdenom : 0 < 4 * (1 + δ.1) := by nlinarith [δ.2.1]
    rw [div_lt_iff₀ hdenom]
    have hεδ : 0 < ε * δ.1 := mul_pos hε δ.2.1
    nlinarith
  let aStar := max (quittingMeshIntensity δ.1)
    (quittingMeshIntensity (1 / 2))
  have hintensityδ0 : 0 ≤ quittingMeshIntensity δ.1 :=
    quittingMeshIntensity_nonneg δ.2.1.le δ.2.2.le
  have hintensityHalf0 : 0 ≤ quittingMeshIntensity (1 / 2) :=
    quittingMeshIntensity_nonneg (by norm_num) (by norm_num)
  have haStar0 : 0 ≤ aStar := by
    exact hintensityδ0.trans (le_max_left _ _)
  let collisionScale := 2 * quittingRewardBound reward * aStar
  have hcollisionScale0 : 0 ≤ collisionScale :=
    mul_nonneg (mul_nonneg (by norm_num)
      (quittingRewardBound_nonneg reward)) haStar0
  obtain ⟨m, hmLarge⟩ :=
    exists_nat_gt (2 * collisionScale / ε)
  have hmReal : 0 < (m : ℝ) := by
    have hthreshold0 : 0 ≤ 2 * collisionScale / ε :=
      div_nonneg (mul_nonneg (by norm_num) hcollisionScale0) hε.le
    exact lt_of_le_of_lt hthreshold0 hmLarge
  have hm : 0 < m := by exact_mod_cast hmReal
  have hcollisionSmall : collisionScale / (m : ℝ) < ε / 2 := by
    have hscaled : 2 * collisionScale < (m : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hmLarge
    rw [div_lt_iff₀ hmReal]
    nlinarith
  have hhazardδ : quittingMeshHazard δ.1 m ≤ aStar / (m : ℝ) := by
    exact (quittingMeshHazard_le_intensity_div δ.2.2).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg m))
  have hhazardHalf : quittingMeshHazard (1 / 2) m ≤
      aStar / (m : ℝ) := by
    exact (quittingMeshHazard_le_intensity_div (by norm_num)).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg m))
  have hhazardMax : max (quittingMeshHazard δ.1 m)
      (quittingMeshHazard (1 / 2) m) ≤ aStar / (m : ℝ) :=
    max_le hhazardδ hhazardHalf
  have hcollisionError :
      2 * quittingRewardBound reward *
          max (quittingMeshHazard δ.1 m)
            (quittingMeshHazard (1 / 2) m) < ε / 2 := by
    have hscaled :
        2 * quittingRewardBound reward *
            max (quittingMeshHazard δ.1 m)
              (quittingMeshHazard (1 / 2) m) ≤
          2 * quittingRewardBound reward * (aStar / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hhazardMax
        (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
    have hrewrite : 2 * quittingRewardBound reward *
        (aStar / (m : ℝ)) = collisionScale / (m : ℝ) := by
      dsimp only [collisionScale]
      ring
    rw [hrewrite] at hscaled
    exact hscaled.trans_lt hcollisionSmall
  obtain ⟨hnash, hpayoff⟩ :=
    meshProfile_isTerminalNash_and_hasPayoff conditions δ m hm
  refine ⟨meshProfile reward δ m hm, ?_, ?_⟩
  · exact StochasticGame.IsεAsymptoticNash.mono hnash (by linarith)
  · intro who
    rw [hpayoff]
    exact (secondBlockPayoff_sub_target_abs_le δ who).trans htarget.le

/-- The target is a uniform-equilibrium payoff under exactly the singleton
conditions used by the construction. -/
theorem TwoBlockTargetSingletonConditions.target_isUniformEquilibriumPayoff
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : TwoBlockTargetSingletonConditions reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none targetPayoff := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance
  exact exists_terminalNash_and_payoff_close_to_target conditions

/-- In particular, fixing all four displayed singleton rows and leaving every
nonsingleton reward coordinate arbitrary gives the same uniform payoff. -/
theorem target_isUniformEquilibriumPayoff_of_exactFourSingletonRows
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hzero : quittingSoloReward reward 0 = firstOwnerSingletonRow)
    (hone : quittingSoloReward reward 1 = targetPayoff)
    (htwo : quittingSoloReward reward 2 = playerTwoSingletonRow)
    (hthree : quittingSoloReward reward 3 = playerThreeSingletonRow) :
    (quittingGame reward).IsUniformEquilibriumPayoff none targetPayoff := by
  apply TwoBlockTargetSingletonConditions.target_isUniformEquilibriumPayoff
  exact
    { firstOwnerRow := hzero
      secondOwnerRow := hone
      playerTwoOwnSingleton_le := by rw [htwo]; norm_num [playerTwoSingletonRow]
      playerThreeOwnSingleton_le := by
        rw [hthree]
        norm_num [playerThreeSingletonRow] }

end FinFourTwoBlockSingletonFiber
end GameTheory
