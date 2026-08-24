/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.CoalitionTargetMassLedger
import MathUE.Probability.SquareRootCoalitionClock
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchDeviationCap
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Boundary.Holonomy.TwoOwnerCommonWordRealization
import UniformEquilibrium.Quitting.Paths.OpponentActionMass
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-!
# Six-player one-pair mass forcing and target locks

This file connects a finite coalition-law ledger to the literal terminal law of
an arbitrary behavioral quitting profile.  The six-player table forces mass on
one displayed pair and controls the leftover.  It also has a pure exact target
equilibrium, so it does not force the second pair and is not a counterexample.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open QuittingBoundaryHolonomy
open QuittingSureSetOwnerRepair

variable {Player : Type} [Fintype Player] [DecidableEq Player]

/-- A target-membership table with a direct outsider cross penalty and a bounded
completion on every other outsider row. -/
def IsQuittingTargetCrossPenaltyCompletion
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (target : Finset Player) (penalty radius : ℝ) : Prop :=
  (∀ terminal member, member ∈ target →
      reward terminal member = if member ∈ terminal.1 then 1 else 0) ∧
    ∀ terminal outsider, outsider ∉ target →
      if target ⊆ terminal.1 ∧ outsider ∈ terminal.1 then
        reward terminal outsider = -penalty
      else
        |reward terminal outsider| ≤ radius

/-- Mask every coordinate except one player's passive rows. -/
private def passiveCoordinateMask
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (who : Player) : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal player =>
    if player = who ∧ who ∉ terminal.1 then reward terminal who else 0

omit [Fintype Player] in
private theorem passiveCoordinateMask_abs_le
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (who : Player) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (habsent : ∀ terminal, who ∉ terminal.1 →
      |reward terminal who| ≤ radius)
    (terminal : {S : Finset Player // S.Nonempty}) (player : Player) :
    |passiveCoordinateMask reward who terminal player| ≤ radius := by
  unfold passiveCoordinateMask
  split_ifs with h
  · exact habsent terminal h.2
  · simpa using hradius

private theorem quittingRootAbsorbingContribution_passiveCoordinateMask
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (root : Player → PMF Bool) (who : Player) :
    quittingRootAbsorbingContribution (passiveCoordinateMask reward who)
        (Function.update root who (PMF.pure false)) who =
      quittingRootAbsorbingContribution reward
        (Function.update root who (PMF.pure false)) who := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro action haction
  have hfalse := action_eq_false_of_mem_support_pmfPi_update_pure_false
    root who action haction
  by_cases hquit : (quittingQuitters action).Nonempty
  · have hnotmem : who ∉ quittingQuitters action := by
      simp [quittingQuitters, hfalse]
    simp [quittingRootPayoff, hquit, passiveCoordinateMask, hnotmem]
  · simp [quittingRootPayoff, hquit]

private theorem quittingRootSequenceTerminalValue_passiveCoordinateMask
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (roots : ℕ → Player → PMF Bool) (who : Player) :
    quittingRootSequenceTerminalValue (passiveCoordinateMask reward who)
        (quittingRootSequenceUpdate roots who quittingAlwaysContinueHazard) who 0 =
      quittingRootSequenceTerminalValue reward
        (quittingRootSequenceUpdate roots who quittingAlwaysContinueHazard) who 0 := by
  rw [quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution,
    quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution]
  apply tsum_congr
  intro time
  congr 1
  simp only [Nat.zero_add, quittingRootSequenceUpdate,
    quittingAlwaysContinueHazard]
  exact quittingRootAbsorbingContribution_passiveCoordinateMask
    reward (roots time) who

/-- A player who Never quits receives a payoff bounded by the rows that omit
that player; rewards on impossible rows containing the player are irrelevant. -/
theorem abs_quittingTerminalPayoff_update_never_le_of_absent_bound
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile) (who : Player)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (habsent : ∀ terminal, who ∉ terminal.1 →
      |reward terminal who| ≤ radius) :
    |quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who none)) who| ≤ radius := by
  let roots := quittingProfileLiveRoot reward profile
  have hmask := abs_quittingRootSequenceTerminalValue_le
    (passiveCoordinateMask reward who)
    (quittingRootSequenceUpdate roots who quittingAlwaysContinueHazard)
    who 0 hradius (passiveCoordinateMask_abs_le reward who hradius habsent)
  have hvalue : quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who none)) who =
      quittingRootSequenceTerminalValue reward
        (quittingRootSequenceUpdate roots who quittingAlwaysContinueHazard) who 0 := by
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    unfold quittingRootSequencePureTimeTerminalValue
    congr 3
  rw [hvalue, ← quittingRootSequenceTerminalValue_passiveCoordinateMask
    reward roots who]
  exact hmask

/-- A target member's immediate-Quit deviation pays one under membership
coordinates, independently of every opponent behavior and tie. -/
theorem quittingTerminalPayoff_update_quitNow_eq_one_of_targetMembership
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile)
    (target : Finset Player) (member : Player) (hmember : member ∈ target)
    (htarget : ∀ terminal player, player ∈ target →
      reward terminal player = if player ∈ terminal.1 then 1 else 0) :
    quittingTerminalPayoff reward
        (Function.update profile member
          (quittingPureTimeBehaviorStrategy reward member (some 0))) member = 1 := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
  unfold quittingStationaryFixedOpponentsQuitValue quittingFixedOpponentsQuitValue
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  calc
    expect (pmfPi (Function.update
        (quittingProfileLiveRoot reward profile 0) member (PMF.pure true)))
        (fun action => quittingRootPayoff reward (0 : Payoff Player) action member) =
      expect (pmfPi (Function.update
        (quittingProfileLiveRoot reward profile 0) member (PMF.pure true)))
        (fun _action => (1 : ℝ)) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro action haction
      have htrue := action_eq_true_of_mem_support_pmfPi_update_pure_true
        (quittingProfileLiveRoot reward profile 0) member action haction
      have hquit : (quittingQuitters action).Nonempty := by
        exact ⟨member, by simp [quittingQuitters, htrue]⟩
      have hmemQuitters : member ∈ quittingQuitters action := by
        simp [quittingQuitters, htrue]
      simp [quittingRootPayoff, hquit, htarget _ member hmember, hmemQuitters]
    _ = 1 := expect_const _ _

private theorem coalitionMemberMass_terminalOutcomeMass_eq_payoff
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile)
    (target : Finset Player) (member : Player) (hmember : member ∈ target)
    (htarget : ∀ terminal player, player ∈ target →
      reward terminal player = if player ∈ terminal.1 then 1 else 0) :
    coalitionMemberMass (quittingTerminalOutcomeMass reward profile) member =
      quittingTerminalPayoff reward profile member := by
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass reward profile) member
  rw [← hmoment]
  unfold coalitionMemberMass coalitionEventMass quittingTerminalRewardMoment
  apply Finset.sum_congr rfl
  intro outcome _
  cases outcome with
  | none => simp [CoalitionOutcome.coalition, quittingTerminalOutcomeReward]
  | some terminal =>
      simp [CoalitionOutcome.coalition, quittingTerminalOutcomeReward,
        htarget terminal member hmember]

private theorem targetOutsider_payoff_le_radius_sub_incidence
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile)
    (target : Finset Player) (outsider : Player) (houtside : outsider ∉ target)
    (penalty radius : ℝ) (hradius : 0 ≤ radius)
    (hcompletion : IsQuittingTargetCrossPenaltyCompletion
      reward target penalty radius) :
    quittingTerminalPayoff reward profile outsider ≤
      radius - (penalty + radius) *
        targetOutsiderIncidenceMass
          (quittingTerminalOutcomeMass reward profile) target outsider := by
  let mass := quittingTerminalOutcomeMass reward profile
  have hmass := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass reward profile) outsider
  rw [← hmoment]
  unfold quittingTerminalRewardMoment targetOutsiderIncidenceMass
    coalitionEventMass
  calc
    (∑ outcome, mass outcome *
        quittingTerminalOutcomeReward reward outcome outsider) ≤
      ∑ outcome, mass outcome *
        (if target ⊆ CoalitionOutcome.coalition outcome ∧
            outsider ∈ CoalitionOutcome.coalition outcome then
          -penalty else radius) := by
      apply Finset.sum_le_sum
      intro outcome _
      apply mul_le_mul_of_nonneg_left _ (hmass.1 outcome)
      cases outcome with
      | none =>
          simp [CoalitionOutcome.coalition, quittingTerminalOutcomeReward,
            hradius]
      | some terminal =>
          by_cases hcross : target ⊆ terminal.1 ∧ outsider ∈ terminal.1
          · have hrow := hcompletion.2 terminal outsider houtside
            rw [if_pos hcross] at hrow
            simp only [CoalitionOutcome.coalition, quittingTerminalOutcomeReward,
              hcross, and_self, if_true]
            exact le_of_eq hrow
          · have hbound := hcompletion.2 terminal outsider houtside
            simp only [hcross, if_false] at hbound
            simp only [CoalitionOutcome.coalition, quittingTerminalOutcomeReward,
              hcross, if_false]
            exact (le_abs_self _).trans hbound
    _ = radius - (penalty + radius) *
        ∑ outcome,
          if target ⊆ CoalitionOutcome.coalition outcome ∧
              outsider ∈ CoalitionOutcome.coalition outcome then
            mass outcome else 0 := by
      rw [show (∑ outcome, mass outcome *
          (if target ⊆ CoalitionOutcome.coalition outcome ∧
              outsider ∈ CoalitionOutcome.coalition outcome then
            -penalty else radius)) =
          ∑ outcome, (mass outcome * radius -
            (penalty + radius) *
              if target ⊆ CoalitionOutcome.coalition outcome ∧
                  outsider ∈ CoalitionOutcome.coalition outcome then
                mass outcome else 0) by
        apply Finset.sum_congr rfl
        intro outcome _
        split_ifs <;> ring]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass.2, one_mul,
        ← Finset.mul_sum]

private theorem targetMember_security_of_completion_of_isεAsymptoticNash
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile)
    (target : Finset Player) (member : Player) (hmember : member ∈ target)
    (penalty radius : ℝ) {epsilon : ℝ}
    (hcompletion : IsQuittingTargetCrossPenaltyCompletion
      reward target penalty radius)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) epsilon profile) :
    1 - epsilon ≤
      coalitionMemberMass (quittingTerminalOutcomeMass reward profile) member := by
  have hdeviation := hnash member
    (quittingPureTimeBehaviorStrategy reward member (some 0))
  rw [quittingTerminalPayoff_update_quitNow_eq_one_of_targetMembership
      reward profile target member hmember hcompletion.1,
    ← coalitionMemberMass_terminalOutcomeMass_eq_payoff
      reward profile target member hmember hcompletion.1] at hdeviation
  linarith

private theorem targetOutsider_incidence_le_of_isεAsymptoticNash
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile)
    (target : Finset Player) (outsider : Player) (houtside : outsider ∉ target)
    (penalty radius : ℝ) (hradius : 0 ≤ radius)
    (hdenom : 0 < penalty + radius) {epsilon : ℝ}
    (hcompletion : IsQuittingTargetCrossPenaltyCompletion
      reward target penalty radius)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) epsilon profile) :
    targetOutsiderIncidenceMass
        (quittingTerminalOutcomeMass reward profile) target outsider ≤
      (2 * radius + epsilon) / (penalty + radius) := by
  have habsent : ∀ terminal, outsider ∉ terminal.1 →
      |reward terminal outsider| ≤ radius := by
    intro terminal habsent
    have hrow := hcompletion.2 terminal outsider houtside
    simp only [habsent, and_false, if_false] at hrow
    exact hrow
  have hneverAbs := abs_quittingTerminalPayoff_update_never_le_of_absent_bound
    reward profile outsider hradius habsent
  have hnever := hnash outsider
    (quittingPureTimeBehaviorStrategy reward outsider none)
  have hprescribed := targetOutsider_payoff_le_radius_sub_incidence
    reward profile target outsider houtside penalty radius hradius hcompletion
  rw [abs_le] at hneverAbs
  apply (le_div_iff₀ hdenom).2
  linarith

/-- General robust target forcing for arbitrary behavioral profiles. -/
theorem exactCoalitionMass_ge_of_targetCrossPenaltyCompletion
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile)
    (target : Finset Player) (htarget : target.Nonempty)
    (penalty radius : ℝ) (hradius : 0 ≤ radius)
    (hdenom : 0 < penalty + radius) {epsilon : ℝ}
    (hcompletion : IsQuittingTargetCrossPenaltyCompletion
      reward target penalty radius)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) epsilon profile) :
    1 - (target.card : ℝ) * epsilon -
        ((Finset.univ \ target).card : ℝ) *
          ((2 * radius + epsilon) / (penalty + radius)) ≤
      exactCoalitionMass (quittingTerminalOutcomeMass reward profile) target := by
  apply exactCoalitionMass_ge_of_memberSecurity_of_outsiderIncidence
    (quittingTerminalOutcomeMass_mem_stdSimplex reward profile) target htarget
  · intro member hmember
    exact targetMember_security_of_completion_of_isεAsymptoticNash
      reward profile target member hmember penalty radius hcompletion hnash
  · intro outsider houtside
    exact targetOutsider_incidence_le_of_isεAsymptoticNash
      reward profile target outsider houtside penalty radius hradius hdenom
      hcompletion hnash

/-- Membership-toggle inequalities give both the exact all-behavior terminal
Nash conclusion and the uniform-payoff consumer. -/
theorem pureSet_terminalNash_and_uniformPayoff_of_membershipToggles
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (target : Finset Player)
    (hmember : ∀ member ∈ target,
      quittingSetReward reward (target.erase member) member ≤
        quittingSetReward reward target member)
    (houtsider : ∀ outsider ∉ target,
      quittingSetReward reward (insert outsider target) outsider ≤
        quittingSetReward reward target outsider) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (quittingPureSetRoot target)) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSetReward reward target) := by
  have hsure : IsQuittingSureExitSet reward target := ⟨hmember, houtsider⟩
  exact ⟨
    (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
      reward target).2 hsure,
    isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward hsure⟩

namespace SixPlayerOnePair

/-- The literal six-player label type.  Labels `1`, ..., `6` are represented
by `0`, ..., `5` in `Fin 6`. -/
abbrev SixPlayer := Fin 6

def player1 : SixPlayer := 0
def player2 : SixPlayer := 1
def player3 : SixPlayer := 2
def player4 : SixPlayer := 3
def player5 : SixPlayer := 4
def player6 : SixPlayer := 5

/-- The pair called `A = {1,2}` in the packet. -/
def targetA : Finset SixPlayer := {player1, player2}

/-- The pair called `B = {3,4}` in the packet. -/
def targetB : Finset SixPlayer := {player3, player4}

theorem targetA_nonempty : targetA.Nonempty := by
  simp [targetA]

theorem targetA_card : targetA.card = 2 := by
  decide

theorem targetA_compl_card : ((Finset.univ \ targetA).card : ℕ) = 4 := by
  decide

theorem targetA_ne_targetB : targetA ≠ targetB := by
  decide

/-- The complete integer reward table: target members receive their
membership indicators, and every outsider receives `-31` exactly on rows
containing both the target and that outsider. -/
def integerReward :
    {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer :=
  fun terminal who =>
    if who = player1 then
      if player1 ∈ terminal.1 then 1 else 0
    else if who = player2 then
      if player2 ∈ terminal.1 then 1 else 0
    else if targetA ⊆ terminal.1 ∧ who ∈ terminal.1 then -31 else 0

theorem integerReward_isCrossPenaltyCompletion :
    IsQuittingTargetCrossPenaltyCompletion integerReward targetA 31 0 := by
  constructor
  · intro terminal member hmember
    simp only [targetA, Finset.mem_insert, Finset.mem_singleton] at hmember
    rcases hmember with rfl | rfl
    · simp [integerReward, player1]
    · simp [integerReward, player1, player2]
  · intro terminal outsider houtside
    have hout1 : outsider ≠ player1 := by
      intro h
      apply houtside
      simp [targetA, h]
    have hout2 : outsider ≠ player2 := by
      intro h
      apply houtside
      simp [targetA, h]
    simp [integerReward, hout1, hout2]

/-- Terminal mass on `A`. -/
def firstPairMass
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  exactCoalitionMass (quittingTerminalOutcomeMass reward profile) targetA

/-- Terminal mass on `B`. -/
def secondPairMass
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  exactCoalitionMass (quittingTerminalOutcomeMass reward profile) targetB

/-- All mass other than the two displayed target atoms, including Never. -/
def leftoverMass
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  1 - firstPairMass reward profile - secondPairMass reward profile

theorem firstPairMass_nonneg
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ firstPairMass reward profile :=
  exactCoalitionMass_nonneg
    (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 targetA

theorem secondPairMass_nonneg
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ secondPairMass reward profile :=
  exactCoalitionMass_nonneg
    (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 targetB

theorem leftoverMass_nonneg
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ leftoverMass reward profile := by
  have hsum := exactCoalitionMass_add_le_one_of_ne
    (quittingTerminalOutcomeMass_mem_stdSimplex reward profile)
    targetA_ne_targetB
  unfold leftoverMass firstPairMass secondPairMass
  linarith

/-- Exact `31/66` lower bound on literal all-behavior exploitability. -/
theorem integerReward_exploitability_ge
    (profile : (quittingGame integerReward).BehaviorProfile) :
    31 * (1 - firstPairMass integerReward profile) / 66 ≤
      quittingTerminalExploitability integerReward profile := by
  let exploitability := quittingTerminalExploitability integerReward profile
  have hnash : (quittingGame integerReward).IsεAsymptoticNash
      (quittingTerminalPayoff integerReward) exploitability profile :=
    isεAsymptoticNash_of_quittingTerminalExploitability_le profile le_rfl
  have hmass := exactCoalitionMass_ge_of_targetCrossPenaltyCompletion
    integerReward profile targetA targetA_nonempty 31 0 (by norm_num)
    (by norm_num) integerReward_isCrossPenaltyCompletion hnash
  rw [targetA_card, targetA_compl_card] at hmass
  change 31 * (1 - firstPairMass integerReward profile) / 66 ≤ exploitability
  unfold firstPairMass
  norm_num at hmass ⊢
  linarith

/-- Low literal exploitability forces the exact `A` mass and the leftover
bound, without restricting the profile's behavioral strategy class. -/
theorem integerReward_mass_and_leftover_of_exploitability_le
    (profile : (quittingGame integerReward).BehaviorProfile)
    {epsilon : ℝ}
    (hexploit : quittingTerminalExploitability integerReward profile ≤ epsilon) :
    1 - 66 * epsilon / 31 ≤ firstPairMass integerReward profile ∧
      leftoverMass integerReward profile ≤ 66 * epsilon / 31 := by
  have hlower := integerReward_exploitability_ge profile
  have hsecond := secondPairMass_nonneg integerReward profile
  constructor <;> unfold leftoverMass at * <;> linarith

/-- Robust `[-1,1]` outsider completions retain the stated `17/8` forcing
constant. -/
theorem robustCompletion_firstPairMass_ge
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) {epsilon : ℝ}
    (hcompletion : IsQuittingTargetCrossPenaltyCompletion reward targetA 31 1)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) epsilon profile) :
    3 / 4 - 17 * epsilon / 8 ≤ firstPairMass reward profile := by
  have hmass := exactCoalitionMass_ge_of_targetCrossPenaltyCompletion
    reward profile targetA targetA_nonempty 31 1 (by norm_num) (by norm_num)
    hcompletion hnash
  rw [targetA_card, targetA_compl_card] at hmass
  norm_num [firstPairMass] at hmass ⊢
  linarith

theorem robustCompletion_leftoverMass_le
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile) {epsilon : ℝ}
    (hcompletion : IsQuittingTargetCrossPenaltyCompletion reward targetA 31 1)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) epsilon profile) :
    leftoverMass reward profile ≤ 1 / 4 + 17 * epsilon / 8 := by
  have hfirst := robustCompletion_firstPairMass_ge
    reward profile hcompletion hnash
  have hsecond := secondPairMass_nonneg reward profile
  unfold leftoverMass
  linarith

/-- The packet's exact numerical specialization at error `1/10`. -/
theorem integerReward_one_tenth_bounds
    (profile : (quittingGame integerReward).BehaviorProfile)
    (hexploit : quittingTerminalExploitability integerReward profile ≤ 1 / 10) :
    122 / 155 ≤ firstPairMass integerReward profile ∧
      leftoverMass integerReward profile ≤ 33 / 155 := by
  have h := integerReward_mass_and_leftover_of_exploitability_le profile hexploit
  norm_num at h ⊢
  exact h

/-- Every robust completion has the packet's stronger one-tenth bounds. -/
theorem robustCompletion_one_tenth_bounds
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (profile : (quittingGame reward).BehaviorProfile)
    (hcompletion : IsQuittingTargetCrossPenaltyCompletion reward targetA 31 1)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (1 / 10) profile) :
    43 / 80 ≤ firstPairMass reward profile ∧
      leftoverMass reward profile ≤ 37 / 80 := by
  constructor
  · have h := robustCompletion_firstPairMass_ge
      reward profile hcompletion hnash
    norm_num at h ⊢
    exact h
  · have h := robustCompletion_leftoverMass_le
      reward profile hcompletion hnash
    norm_num at h ⊢
    exact h

/-- The checked independent-clock square-root inequality converts the forced
`A` mass and leftover bound into the packet's quantitative upper bound on
the `B` mass. -/
theorem integerReward_secondPairMass_le_of_clock
    (profile : (quittingGame integerReward).BehaviorProfile)
    {epsilon : ℝ}
    (hexploit : quittingTerminalExploitability integerReward profile ≤ epsilon)
    (hepsilon : epsilon < 31 / 66)
    (hclock : Real.sqrt (firstPairMass integerReward profile) +
      Real.sqrt (secondPairMass integerReward profile) ≤ 1) :
    secondPairMass integerReward profile ≤
      (66 * epsilon / 31) ^ 2 /
        (4 * (1 - 66 * epsilon / 31)) := by
  let first := firstPairMass integerReward profile
  let second := secondPairMass integerReward profile
  let leftover := leftoverMass integerReward profile
  let upper := 66 * epsilon / 31
  have hfirst0 : 0 ≤ first := firstPairMass_nonneg integerReward profile
  have hsecond0 : 0 ≤ second := secondPairMass_nonneg integerReward profile
  have hleftover0 : 0 ≤ leftover := leftoverMass_nonneg integerReward profile
  have hexploit0 : 0 ≤ quittingTerminalExploitability integerReward profile :=
    quittingTerminalExploitability_nonneg integerReward profile
  have hepsilon0 : 0 ≤ epsilon := hexploit0.trans hexploit
  have hupper0 : 0 ≤ upper := by
    dsimp only [upper]
    positivity
  have hupper1 : upper < 1 := by
    dsimp only [upper]
    norm_num at hepsilon ⊢
    linarith
  have hmass := integerReward_mass_and_leftover_of_exploitability_le
    profile hexploit
  have hfirstLower : 1 - upper ≤ first := by
    simpa only [first, upper] using hmass.1
  have hleftoverUpper : leftover ≤ upper := by
    simpa only [leftover, upper] using hmass.2
  have hfour : 4 * first * second ≤ leftover ^ 2 := by
    have h := four_mul_twoTargetMass_le_leftover_sq hfirst0 hsecond0
      (by simpa only [first, second] using hclock)
    simpa only [leftover, leftoverMass, first, second] using h
  have hleftoverSq : leftover ^ 2 ≤ upper ^ 2 := by
    nlinarith
  have hdenom : 0 < 4 * (1 - upper) := by positivity
  change second ≤ upper ^ 2 / (4 * (1 - upper))
  apply (le_div_iff₀ hdenom).2
  nlinarith

theorem integerReward_one_tenth_secondPairMass_le
    (profile : (quittingGame integerReward).BehaviorProfile)
    (hexploit : quittingTerminalExploitability integerReward profile ≤ 1 / 10)
    (hclock : Real.sqrt (firstPairMass integerReward profile) +
      Real.sqrt (secondPairMass integerReward profile) ≤ 1) :
    secondPairMass integerReward profile ≤ 1089 / 75640 := by
  have h := integerReward_secondPairMass_le_of_clock profile hexploit
    (by norm_num) hclock
  norm_num at h ⊢
  exact h

theorem one_tenth_secondPair_bound_lt_one_div_sixty_nine :
    (1089 / 75640 : ℝ) < 1 / 69 := by
  norm_num

/-- Every robust outsider-coordinate completion locks the pure target row
`A`: exact all-behavior terminal Nash and its uniform-payoff conclusion both
hold. -/
theorem robustCompletion_targetA_terminalNash_and_uniformPayoff
    (reward : {S : Finset SixPlayer // S.Nonempty} → Payoff SixPlayer)
    (hcompletion : IsQuittingTargetCrossPenaltyCompletion reward targetA 31 1) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (quittingPureSetRoot targetA)) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSetReward reward targetA) := by
  have hne : player1 ≠ player2 := by decide
  have hsure : IsQuittingSureExitSet reward targetA := by
    rw [show targetA = ({player1, player2} : Finset SixPlayer) from rfl,
      isQuittingSureExitSet_pair_iff reward hne]
    refine ⟨?_, ?_, ?_⟩
    · change reward ⟨{player2}, by simp⟩ player1 ≤
        reward ⟨{player2, player1}, by simp⟩ player1
      rw [hcompletion.1 ⟨{player2}, by simp⟩ player1 (by simp [targetA]),
        hcompletion.1 ⟨{player2, player1}, by simp⟩ player1
          (by simp [targetA])]
      simp [player1, player2]
    · change reward ⟨{player1}, by simp⟩ player2 ≤
        reward ⟨{player1, player2}, by simp⟩ player2
      rw [hcompletion.1 ⟨{player1}, by simp⟩ player2 (by simp [targetA]),
        hcompletion.1 ⟨{player1, player2}, by simp⟩ player2
          (by simp [targetA])]
      simp [player1, player2]
    · intro outsider hout1 hout2
      have houtside : outsider ∉ targetA := by
        simp [targetA, hout1, hout2]
      let base : {S : Finset SixPlayer // S.Nonempty} :=
        ⟨targetA, targetA_nonempty⟩
      let joined : {S : Finset SixPlayer // S.Nonempty} :=
        ⟨insert outsider targetA, Finset.insert_nonempty _ _⟩
      have hbase := hcompletion.2 base outsider houtside
      have hbaseNoCross :
          ¬ (targetA ⊆ base.1 ∧ outsider ∈ base.1) := by
        simp [base, houtside]
      rw [if_neg hbaseNoCross] at hbase
      have hjoined := hcompletion.2 joined outsider houtside
      have hjoinedCross : targetA ⊆ joined.1 ∧ outsider ∈ joined.1 := by
        simp [joined]
      rw [if_pos hjoinedCross] at hjoined
      rw [quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _),
        quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _)]
      change reward joined outsider ≤ reward base outsider
      rw [hjoined]
      rw [abs_le] at hbase
      linarith
  exact ⟨
    (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
      reward targetA).2 hsure,
    isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward hsure⟩

/-- Pure `A` is an exact equilibrium of the integer table and puts zero mass
on `B`; this is the explicit regression preventing any second-pair or
counterexample interpretation. -/
theorem integerReward_pureTarget_exactNash_uniform_and_secondMass_zero :
    (quittingGame integerReward).IsεAsymptoticNash
        (quittingTerminalPayoff integerReward) 0
        (quittingStationaryProfile integerReward (quittingPureSetRoot targetA)) ∧
      (quittingGame integerReward).IsUniformEquilibriumPayoff none
        (quittingSetReward integerReward targetA) ∧
      secondPairMass integerReward
        (quittingStationaryProfile integerReward (quittingPureSetRoot targetA)) = 0 := by
  have hlock := robustCompletion_targetA_terminalNash_and_uniformPayoff
    integerReward (by
      have h := integerReward_isCrossPenaltyCompletion
      constructor
      · exact h.1
      · intro terminal outsider houtside
        have hrow := h.2 terminal outsider houtside
        split_ifs at hrow ⊢
        · exact hrow
        · simpa using (le_trans hrow (by norm_num : (0 : ℝ) ≤ 1)))
  refine ⟨hlock.1, hlock.2, ?_⟩
  let profile :=
    quittingStationaryProfile integerReward (quittingPureSetRoot targetA)
  have hfirst := exactCoalitionMass_ge_of_targetCrossPenaltyCompletion
    integerReward profile targetA targetA_nonempty 31 0 (by norm_num)
    (by norm_num) integerReward_isCrossPenaltyCompletion hlock.1
  rw [targetA_card, targetA_compl_card] at hfirst
  norm_num at hfirst
  have hsum := exactCoalitionMass_add_le_one_of_ne
    (quittingTerminalOutcomeMass_mem_stdSimplex integerReward profile)
    targetA_ne_targetB
  have hsecond := secondPairMass_nonneg integerReward profile
  change secondPairMass integerReward profile = 0
  unfold secondPairMass at hsecond ⊢
  linarith

end SixPlayerOnePair

end GameTheory
