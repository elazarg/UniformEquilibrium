/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.LiveMass
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack

/-!
# Survival through a finite literal root stack

This module owns the joint, player-deleted, and player-own survival products
of a finite literal root word.  It proves their positivity, factorization,
comparison laws, and agreement with the survival factor in the corresponding
terminal-debt aggregate block.

The results are finite-word identities.  They assume no counterexample
regime, frontier, atom, or asymptotic chronology.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open Math.SurvivalWeightedObstruction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Full joint survival through a finite literal root stack. -/
def quittingLiteralRootStackJointSurvival
    (roots : List (ι → PMF Bool)) : ℝ :=
  (roots.map quittingStationaryContinueMass).prod

/-- Survival through a finite root stack after deleting one player's own
hazards.  This is the survival factor transporting that player's debt. -/
def quittingLiteralRootStackOpponentSurvival
    (roots : List (ι → PMF Bool)) (who : ι) : ℝ :=
  (roots.map fun root => quittingRootOpponentContinueMass root who).prod

/-- Product of one player's own Continue probabilities through a finite root
stack. -/
def quittingLiteralRootStackOwnSurvival
    (roots : List (ι → PMF Bool)) (who : ι) : ℝ :=
  (roots.map fun root => (root who false).toReal).prod

omit [Fintype ι] [DecidableEq ι] in
theorem quittingLiteralRootStackOwnSurvival_nonneg
    (roots : List (ι → PMF Bool)) (who : ι) :
    0 ≤ quittingLiteralRootStackOwnSurvival roots who := by
  induction roots with
  | nil => simp [quittingLiteralRootStackOwnSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackOwnSurvival, List.map_cons,
        List.prod_cons]
      exact mul_nonneg ENNReal.toReal_nonneg ih

omit [Fintype ι] [DecidableEq ι] in
theorem quittingLiteralRootStackOwnSurvival_le_one
    (roots : List (ι → PMF Bool)) (who : ι) :
    quittingLiteralRootStackOwnSurvival roots who ≤ 1 := by
  induction roots with
  | nil => simp [quittingLiteralRootStackOwnSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackOwnSurvival, List.map_cons,
        List.prod_cons]
      have hhead : (root who false).toReal ≤ 1 :=
        ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one false)
      have hhead0 : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
      have htail0 := quittingLiteralRootStackOwnSurvival_nonneg roots who
      change (root who false).toReal *
        quittingLiteralRootStackOwnSurvival roots who ≤ 1
      nlinarith [mul_nonneg hhead0 htail0,
        mul_nonneg (sub_nonneg.mpr hhead) htail0]

theorem quittingLiteralRootStackOpponentSurvival_nonneg
    (roots : List (ι → PMF Bool)) (who : ι) :
    0 ≤ quittingLiteralRootStackOpponentSurvival roots who := by
  induction roots with
  | nil => simp [quittingLiteralRootStackOpponentSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackOpponentSurvival, List.map_cons,
        List.prod_cons]
      exact mul_nonneg (quittingRootOpponentContinueMass_nonneg root who) ih

theorem quittingLiteralRootStackOpponentSurvival_le_one
    (roots : List (ι → PMF Bool)) (who : ι) :
    quittingLiteralRootStackOpponentSurvival roots who ≤ 1 := by
  induction roots with
  | nil => simp [quittingLiteralRootStackOpponentSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackOpponentSurvival, List.map_cons,
        List.prod_cons]
      have hroot0 := quittingRootOpponentContinueMass_nonneg root who
      have hroot1 := quittingRootOpponentContinueMass_le_one root who
      have htail0 := quittingLiteralRootStackOpponentSurvival_nonneg roots who
      change quittingRootOpponentContinueMass root who *
        quittingLiteralRootStackOpponentSurvival roots who ≤ 1
      nlinarith [mul_nonneg hroot0 htail0,
        mul_nonneg (sub_nonneg.mpr hroot1) htail0]

omit [DecidableEq ι] in
theorem quittingLiteralRootStackJointSurvival_nonneg
    (roots : List (ι → PMF Bool)) :
    0 ≤ quittingLiteralRootStackJointSurvival roots := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackJointSurvival, List.map_cons,
        List.prod_cons]
      exact mul_nonneg (quittingStationaryContinueMass_nonneg root) ih

omit [DecidableEq ι] in
theorem quittingLiteralRootStackJointSurvival_le_one
    (roots : List (ι → PMF Bool)) :
    quittingLiteralRootStackJointSurvival roots ≤ 1 := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackJointSurvival, List.map_cons,
        List.prod_cons]
      have hroot0 := quittingStationaryContinueMass_nonneg root
      have hroot1 := quittingStationaryContinueMass_le_one root
      have htail0 := quittingLiteralRootStackJointSurvival_nonneg roots
      change quittingStationaryContinueMass root *
        quittingLiteralRootStackJointSurvival roots ≤ 1
      nlinarith [mul_nonneg hroot0 htail0,
        mul_nonneg (sub_nonneg.mpr hroot1) htail0]

/-- Joint survival factors into one player's debt-transport survival and
that player's own survival. -/
theorem quittingLiteralRootStackJointSurvival_eq_opponent_mul_own
    (roots : List (ι → PMF Bool)) (who : ι) :
    quittingLiteralRootStackJointSurvival roots =
      quittingLiteralRootStackOpponentSurvival roots who *
        quittingLiteralRootStackOwnSurvival roots who := by
  induction roots with
  | nil => simp [quittingLiteralRootStackJointSurvival,
      quittingLiteralRootStackOpponentSurvival,
      quittingLiteralRootStackOwnSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackJointSurvival,
        quittingLiteralRootStackOpponentSurvival,
        quittingLiteralRootStackOwnSurvival, List.map_cons, List.prod_cons]
      rw [quittingStationaryContinueMass_eq_forcedContinue_mul_own]
      change (quittingRootOpponentContinueMass root who *
          (root who false).toReal) *
          quittingLiteralRootStackJointSurvival roots = _
      rw [ih]
      change (quittingRootOpponentContinueMass root who *
          (root who false).toReal) *
          (quittingLiteralRootStackOpponentSurvival roots who *
            quittingLiteralRootStackOwnSurvival roots who) =
        (quittingRootOpponentContinueMass root who *
          quittingLiteralRootStackOpponentSurvival roots who) *
        ((root who false).toReal *
          quittingLiteralRootStackOwnSurvival roots who)
      ring

/-- Deleting `other` leaves a survival product no larger than `who`'s own
survival when the labels are distinct. -/
theorem quittingLiteralRootStackOpponentSurvival_le_ownSurvival_of_ne
    (roots : List (ι → PMF Bool)) {who other : ι}
    (hne : who ≠ other) :
    quittingLiteralRootStackOpponentSurvival roots other ≤
      quittingLiteralRootStackOwnSurvival roots who := by
  induction roots with
  | nil => simp [quittingLiteralRootStackOpponentSurvival,
      quittingLiteralRootStackOwnSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralRootStackOpponentSurvival,
        quittingLiteralRootStackOwnSurvival, List.map_cons, List.prod_cons]
      have hhead : quittingRootOpponentContinueMass root other ≤
          (root who false).toReal :=
        quittingRootOpponentContinueMass_le_continueProbability_of_ne
          root (who := other) (other := who) hne
      have hleft0 := quittingRootOpponentContinueMass_nonneg root other
      have htail0 := quittingLiteralRootStackOpponentSurvival_nonneg roots other
      have hown0 : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
      exact mul_le_mul hhead ih htail0 hown0

/-- Two distinct deleted-player survival products control full joint
survival from below. -/
theorem mul_opponentSurvival_le_jointSurvival_of_ne
    (roots : List (ι → PMF Bool)) {first second : ι}
    (hne : first ≠ second) :
    quittingLiteralRootStackOpponentSurvival roots first *
        quittingLiteralRootStackOpponentSurvival roots second ≤
      quittingLiteralRootStackJointSurvival roots := by
  rw [quittingLiteralRootStackJointSurvival_eq_opponent_mul_own roots first]
  exact mul_le_mul_of_nonneg_left
    (quittingLiteralRootStackOpponentSurvival_le_ownSurvival_of_ne
      roots hne)
    (quittingLiteralRootStackOpponentSurvival_nonneg roots first)

/-- The player-deleted stack survival is literally the survival factor of
the aggregate terminal-debt block. -/
theorem quittingLiteralTerminalDebtAggregateBlock_survival_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingLiteralTerminalDebtAggregateBlock reward roots terminal who).survival =
      quittingLiteralRootStackOpponentSurvival roots who := by
  induction roots with
  | nil => simp [quittingLiteralTerminalDebtAggregateBlock,
      quittingLiteralTerminalDebtBlocks,
      quittingLiteralRootStackOpponentSurvival]
  | cons root roots ih =>
      simp only [quittingLiteralTerminalDebtAggregateBlock,
        quittingLiteralTerminalDebtBlocks, Block.concatList_cons,
        Block.concat_survival, quittingLiteralTerminalDebtBlock_survival,
        quittingLiteralRootStackOpponentSurvival, List.map_cons,
        List.prod_cons]
      change quittingRootOpponentContinueMass root who *
          (quittingLiteralTerminalDebtAggregateBlock
            reward roots terminal who).survival =
        quittingRootOpponentContinueMass root who *
          quittingLiteralRootStackOpponentSurvival roots who
      rw [ih]

/-- Full joint survival through a finite root word is bounded by every
player-deleted survival through that word. -/
theorem quittingLiteralRootStackJointSurvival_le_opponentSurvival
    (roots : List (ι → PMF Bool)) (who : ι) :
    quittingLiteralRootStackJointSurvival roots ≤
      quittingLiteralRootStackOpponentSurvival roots who := by
  rw [quittingLiteralRootStackJointSurvival_eq_opponent_mul_own roots who]
  calc
    quittingLiteralRootStackOpponentSurvival roots who *
        quittingLiteralRootStackOwnSurvival roots who ≤
      quittingLiteralRootStackOpponentSurvival roots who * 1 :=
        mul_le_mul_of_nonneg_left
          (quittingLiteralRootStackOwnSurvival_le_one roots who)
          (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
    _ = quittingLiteralRootStackOpponentSurvival roots who := mul_one _

/-- Joint survival tending to one forces every fixed player-deleted survival
factor to tend to one. -/
theorem tendsto_quittingLiteralRootStackOpponentSurvival_one
    (roots : ℕ → List (ι → PMF Bool)) (who : ι)
    (hjoint : Tendsto
      (fun rank ↦ quittingLiteralRootStackJointSurvival (roots rank))
      atTop (nhds 1)) :
    Tendsto (fun rank ↦
      quittingLiteralRootStackOpponentSurvival (roots rank) who)
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hjoint tendsto_const_nhds
  · exact fun rank ↦
      quittingLiteralRootStackJointSurvival_le_opponentSurvival
        (roots rank) who
  · exact fun rank ↦
      quittingLiteralRootStackOpponentSurvival_le_one (roots rank) who

end GameTheory
