/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Cycles.PureTimeExtremality
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine

/-!
# Exact forward controller--tester ledger

One prescribed product-root chronology is evaluated by a finite-dimensional
forward state. For `n` players it has `4 * n + 1` real coordinates: prescribed
accumulation and survival, plus each player's deviation accumulation,
opponent survival, and best elapsed finite Quit value.

The update is exact and continuous. This module records the coordinate
recurrences, their finite closed forms, and the sharp reward-box invariants.
The terminal cap and semantic-pair identifications are downstream results;
no strategy-class restriction is introduced here.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The `4 * card ι + 1` coordinate forward ledger. -/
structure QuittingControllerTesterLedger (ι : Type) where
  prescribedAccumulator : Payoff ι
  prescribedSurvival : ℝ
  deviationAccumulator : Payoff ι
  opponentSurvival : Payoff ι
  finiteQuitCap : Payoff ι

/-- Ordinary Euclidean coordinates underlying the controller--tester ledger. -/
abbrev QuittingControllerTesterLedgerCoordinates (ι : Type) :=
  Payoff ι × ℝ × Payoff ι × Payoff ι × Payoff ι

/-- Coordinate readout of a controller--tester ledger. -/
def QuittingControllerTesterLedger.toCoordinates
    (ledger : QuittingControllerTesterLedger ι) :
    QuittingControllerTesterLedgerCoordinates ι :=
  (ledger.prescribedAccumulator, ledger.prescribedSurvival,
    ledger.deviationAccumulator, ledger.opponentSurvival,
    ledger.finiteQuitCap)

/-- Reconstruct a ledger from its Euclidean coordinates. -/
def quittingControllerTesterLedgerOfCoordinates
    (coordinates : QuittingControllerTesterLedgerCoordinates ι) :
    QuittingControllerTesterLedger ι where
  prescribedAccumulator := coordinates.1
  prescribedSurvival := coordinates.2.1
  deviationAccumulator := coordinates.2.2.1
  opponentSurvival := coordinates.2.2.2.1
  finiteQuitCap := coordinates.2.2.2.2

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingControllerTesterLedgerOfCoordinates_toCoordinates
    (ledger : QuittingControllerTesterLedger ι) :
    quittingControllerTesterLedgerOfCoordinates ledger.toCoordinates = ledger := by
  cases ledger
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem QuittingControllerTesterLedger.toCoordinates_ofCoordinates
    (coordinates : QuittingControllerTesterLedgerCoordinates ι) :
    (quittingControllerTesterLedgerOfCoordinates coordinates).toCoordinates =
      coordinates := by
  rcases coordinates with ⟨prescribedAccumulator, prescribedSurvival,
    deviationAccumulator, opponentSurvival, finiteQuitCap⟩
  rfl

/-- The ledger carries the topology induced by its literal Euclidean
coordinate readout. -/
instance : TopologicalSpace (QuittingControllerTesterLedger ι) :=
  TopologicalSpace.induced QuittingControllerTesterLedger.toCoordinates
    inferInstance

omit [Fintype ι] [DecidableEq ι] in
theorem QuittingControllerTesterLedger.injective_toCoordinates :
    Function.Injective (QuittingControllerTesterLedger.toCoordinates :
      QuittingControllerTesterLedger ι →
        QuittingControllerTesterLedgerCoordinates ι) := by
  intro first second heq
  rw [← quittingControllerTesterLedgerOfCoordinates_toCoordinates first,
    ← quittingControllerTesterLedgerOfCoordinates_toCoordinates second,
    heq]

instance : T2Space (QuittingControllerTesterLedger ι) :=
  QuittingControllerTesterLedger.injective_toCoordinates.isEmbedding_induced.t2Space

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_quittingControllerTesterLedger_toCoordinates :
    Continuous (QuittingControllerTesterLedger.toCoordinates :
      QuittingControllerTesterLedger ι →
        QuittingControllerTesterLedgerCoordinates ι) :=
  continuous_induced_dom

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_quittingControllerTesterLedgerOfCoordinates :
    Continuous (quittingControllerTesterLedgerOfCoordinates :
      QuittingControllerTesterLedgerCoordinates ι →
        QuittingControllerTesterLedger ι) := by
  rw [continuous_induced_rng]
  change Continuous (fun coordinates :
    QuittingControllerTesterLedgerCoordinates ι => coordinates)
  exact continuous_id

/-- Prescribed one-stage absorbing contribution `g`. -/
def quittingControllerAbsorbingContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : Payoff ι :=
  quittingRootAbsorbingContribution reward root

/-- Prescribed one-stage all-Continue mass `c`. -/
def quittingControllerContinueMass (root : ι → PMF Bool) : ℝ :=
  quittingStationaryContinueMass root

/-- Payoff `q_i` when player `who` Quits at the current root. -/
def quittingTesterQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootQuitPayoff reward (0 : Payoff ι) root who

/-- Immediate payoff contribution `a_i` when player `who` Continues. -/
def quittingTesterContinueContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootContinuePayoff reward (0 : Payoff ι) root who

/-- Opponent all-Continue mass `chi_i`. -/
def quittingTesterOpponentContinueMass
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootOpponentContinueMass root who

/-- Initial ledger at the canonical reward bound. -/
def quittingControllerTesterLedgerInitial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingControllerTesterLedger ι where
  prescribedAccumulator := 0
  prescribedSurvival := 1
  deviationAccumulator := 0
  opponentSurvival := 1
  finiteQuitCap := fun _ => -quittingRewardBound reward

/-- One exact forward update under a product root. -/
def QuittingControllerTesterLedger.step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (ledger : QuittingControllerTesterLedger ι) :
    QuittingControllerTesterLedger ι where
  prescribedAccumulator := fun who =>
    ledger.prescribedAccumulator who + ledger.prescribedSurvival *
      quittingControllerAbsorbingContribution reward root who
  prescribedSurvival :=
    ledger.prescribedSurvival * quittingControllerContinueMass root
  deviationAccumulator := fun who =>
    ledger.deviationAccumulator who + ledger.opponentSurvival who *
      quittingTesterContinueContribution reward root who
  opponentSurvival := fun who =>
    ledger.opponentSurvival who *
      quittingTesterOpponentContinueMass root who
  finiteQuitCap := fun who =>
    max (ledger.finiteQuitCap who)
      (ledger.deviationAccumulator who + ledger.opponentSurvival who *
        quittingTesterQuitValue reward root who)

omit [DecidableEq ι] in
/-- Prescribed all-Continue mass is continuous in simplex root coordinates. -/
theorem continuous_quittingControllerContinueMass_simplex :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingControllerContinueMass (quittingRootOfSimplex root)) := by
  simp_rw [quittingControllerContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingRootOfSimplex_apply_toReal]
  exact continuous_finsetProd _ fun who _ => (continuous_apply false).comp
    (continuous_subtype_val.comp (continuous_apply who))

/-- Opponent all-Continue mass is continuous in simplex root coordinates. -/
theorem continuous_quittingTesterOpponentContinueMass_simplex (who : ι) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingTesterOpponentContinueMass (quittingRootOfSimplex root) who) := by
  change Continuous (fun root : QuittingRootSimplex ι =>
    quittingStationaryContinueMass
      (Function.update (quittingRootOfSimplex root) who (PMF.pure false)))
  convert continuous_quittingControllerContinueMass_simplex.comp
    (continuous_quittingRootSimplexUpdate who false) using 1
  funext root
  simp only [Function.comp_apply, quittingControllerContinueMass]
  exact congrArg quittingStationaryContinueMass
    (quittingRootOfSimplex_update root who false).symm

/-- The full ledger update is jointly continuous in the simplex root and all
literal ledger coordinates. -/
theorem continuous_quittingControllerTesterLedger_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (fun point :
        QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      point.2.step reward (quittingRootOfSimplex point.1)) := by
  rw [continuous_induced_rng]
  have hcoordinates : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      point.2.toCoordinates) :=
    continuous_quittingControllerTesterLedger_toCoordinates.comp continuous_snd
  have hprescribedAccumulator : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      point.2.prescribedAccumulator) := continuous_fst.comp hcoordinates
  have hprescribedSurvival : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      point.2.prescribedSurvival) :=
    continuous_fst.comp (continuous_snd.comp hcoordinates)
  have hdeviationAccumulator : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      point.2.deviationAccumulator) :=
    continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hcoordinates))
  have hopponentSurvival : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      point.2.opponentSurvival) :=
    continuous_fst.comp (continuous_snd.comp <|
      continuous_snd.comp (continuous_snd.comp hcoordinates))
  have hfiniteQuitCap : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      point.2.finiteQuitCap) :=
    continuous_snd.comp (continuous_snd.comp <|
      continuous_snd.comp (continuous_snd.comp hcoordinates))
  have habsorbing (who : ι) : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      quittingControllerAbsorbingContribution reward
        (quittingRootOfSimplex point.1) who) := by
    have hmap : Continuous (fun point :
        QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      ((0 : Payoff ι), point.1)) := continuous_const.prodMk continuous_fst
    have h := (continuous_quittingRootExpectedPayoff_simplex reward who).comp
      hmap
    change Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
        quittingRootExpectedPayoff reward 0
          (quittingRootOfSimplex point.1) who) at h
    simpa [quittingControllerAbsorbingContribution,
      quittingRootExpectedPayoff_eq_absorbingContribution_add] using h
  have hcontinue : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      quittingControllerContinueMass (quittingRootOfSimplex point.1)) :=
    continuous_quittingControllerContinueMass_simplex.comp continuous_fst
  have htesterContinue (who : ι) : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      quittingTesterContinueContribution reward
        (quittingRootOfSimplex point.1) who) := by
    have hmap : Continuous (fun point :
        QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      ((0 : Payoff ι), point.1)) := continuous_const.prodMk continuous_fst
    have h := (continuous_quittingRootContinuePayoff_simplex reward who).comp
      hmap
    change Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
        quittingRootContinuePayoff reward 0
          (quittingRootOfSimplex point.1) who) at h
    exact h
  have hopponentContinue (who : ι) : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      quittingTesterOpponentContinueMass
        (quittingRootOfSimplex point.1) who) :=
    (continuous_quittingTesterOpponentContinueMass_simplex who).comp
      continuous_fst
  have htesterQuit (who : ι) : Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      quittingTesterQuitValue reward (quittingRootOfSimplex point.1) who) := by
    have hmap : Continuous (fun point :
        QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
      ((0 : Payoff ι), point.1)) := continuous_const.prodMk continuous_fst
    have h := (continuous_quittingRootQuitPayoff_simplex reward who).comp
      hmap
    change Continuous (fun point :
      QuittingRootSimplex ι × QuittingControllerTesterLedger ι =>
        quittingRootQuitPayoff reward 0
          (quittingRootOfSimplex point.1) who) at h
    exact h
  apply Continuous.prodMk
  · apply continuous_pi
    intro who
    exact ((continuous_apply who).comp hprescribedAccumulator).add
      (hprescribedSurvival.mul (habsorbing who))
  apply Continuous.prodMk
  · exact hprescribedSurvival.mul hcontinue
  apply Continuous.prodMk
  · apply continuous_pi
    intro who
    exact ((continuous_apply who).comp hdeviationAccumulator).add
      (((continuous_apply who).comp hopponentSurvival).mul
        (htesterContinue who))
  apply Continuous.prodMk
  · apply continuous_pi
    intro who
    exact ((continuous_apply who).comp hopponentSurvival).mul
      (hopponentContinue who)
  · apply continuous_pi
    intro who
    exact ((continuous_apply who).comp hfiniteQuitCap).max
      (((continuous_apply who).comp hdeviationAccumulator).add
        (((continuous_apply who).comp hopponentSurvival).mul
          (htesterQuit who)))

/-- Ledger after the first `cutoff` roots of a prescribed chronology. -/
def quittingControllerTesterLedgerRun
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) : ℕ → QuittingControllerTesterLedger ι
  | 0 => quittingControllerTesterLedgerInitial reward
  | cutoff + 1 =>
      (quittingControllerTesterLedgerRun reward roots cutoff).step
        reward (roots cutoff)

@[simp] theorem quittingControllerTesterLedgerRun_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) :
    quittingControllerTesterLedgerRun reward roots 0 =
      quittingControllerTesterLedgerInitial reward := rfl

@[simp] theorem quittingControllerTesterLedgerRun_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingControllerTesterLedgerRun reward roots (cutoff + 1) =
      (quittingControllerTesterLedgerRun reward roots cutoff).step
        reward (roots cutoff) := rfl

/-- Closed form for prescribed survival. -/
theorem quittingControllerTesterLedgerRun_prescribedSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    (quittingControllerTesterLedgerRun reward roots cutoff).prescribedSurvival =
      ∏ time ∈ Finset.range cutoff,
        quittingControllerContinueMass (roots time) := by
  induction cutoff with
  | zero => simp [quittingControllerTesterLedgerRun,
      quittingControllerTesterLedgerInitial]
  | succ cutoff ih =>
      rw [quittingControllerTesterLedgerRun_succ]
      change _ * quittingControllerContinueMass (roots cutoff) = _
      rw [ih, Finset.prod_range_succ]

/-- Closed form for prescribed accumulated payoff. -/
theorem quittingControllerTesterLedgerRun_prescribedAccumulator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (who : ι) :
    (quittingControllerTesterLedgerRun reward roots cutoff).prescribedAccumulator who =
      ∑ time ∈ Finset.range cutoff,
        (∏ earlier ∈ Finset.range time,
          quittingControllerContinueMass (roots earlier)) *
        quittingControllerAbsorbingContribution reward (roots time) who := by
  induction cutoff with
  | zero => simp [quittingControllerTesterLedgerRun,
      quittingControllerTesterLedgerInitial]
  | succ cutoff ih =>
      rw [quittingControllerTesterLedgerRun_succ]
      change _ + _ * _ = _
      rw [ih, quittingControllerTesterLedgerRun_prescribedSurvival,
        Finset.sum_range_succ]

/-- Closed form for one player's opponent survival. -/
theorem quittingControllerTesterLedgerRun_opponentSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (who : ι) :
    (quittingControllerTesterLedgerRun reward roots cutoff).opponentSurvival who =
      ∏ time ∈ Finset.range cutoff,
        quittingTesterOpponentContinueMass (roots time) who := by
  induction cutoff with
  | zero => simp [quittingControllerTesterLedgerRun,
      quittingControllerTesterLedgerInitial]
  | succ cutoff ih =>
      rw [quittingControllerTesterLedgerRun_succ]
      change _ * quittingTesterOpponentContinueMass (roots cutoff) who = _
      rw [ih, Finset.prod_range_succ]

/-- Closed form for one player's opponent-absorption payoff accumulator. -/
theorem quittingControllerTesterLedgerRun_deviationAccumulator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (who : ι) :
    (quittingControllerTesterLedgerRun reward roots cutoff).deviationAccumulator who =
      ∑ time ∈ Finset.range cutoff,
        (∏ earlier ∈ Finset.range time,
          quittingTesterOpponentContinueMass (roots earlier) who) *
        quittingTesterContinueContribution reward (roots time) who := by
  induction cutoff with
  | zero => simp [quittingControllerTesterLedgerRun,
      quittingControllerTesterLedgerInitial]
  | succ cutoff ih =>
      rw [quittingControllerTesterLedgerRun_succ]
      change _ + _ * _ = _
      rw [ih, quittingControllerTesterLedgerRun_opponentSurvival,
        Finset.sum_range_succ]

omit [DecidableEq ι] in
theorem abs_quittingControllerAbsorbingContribution_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    |quittingControllerAbsorbingContribution reward root who| ≤
      quittingRewardBound reward *
        (1 - quittingControllerContinueMass root) := by
  exact abs_quittingRootAbsorbingContribution_le reward root who
    (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward)

theorem abs_quittingTesterContinueContribution_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    |quittingTesterContinueContribution reward root who| ≤
      quittingRewardBound reward *
        (1 - quittingTesterOpponentContinueMass root who) := by
  unfold quittingTesterContinueContribution quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  simp only [Pi.zero_apply, mul_zero, add_zero]
  exact abs_quittingRootAbsorbingContribution_le reward
    (Function.update root who (PMF.pure false)) who
    (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward)

theorem abs_quittingTesterQuitValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    |quittingTesterQuitValue reward root who| ≤
      quittingRewardBound reward := by
  unfold quittingTesterQuitValue quittingRootQuitPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingStationaryContinueMass_update_pure_true_eq_zero]
  simp only [zero_mul, add_zero]
  have hbound := abs_quittingRootAbsorbingContribution_le reward
    (Function.update root who (PMF.pure true)) who
    (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward)
  simpa [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_update_pure_true_eq_zero] using hbound

/-- Sharp coordinatewise invariant package for a reachable ledger. -/
structure QuittingControllerTesterLedger.IsBounded
    (bound : ℝ) (ledger : QuittingControllerTesterLedger ι) : Prop where
  prescribedSurvival_nonneg : 0 ≤ ledger.prescribedSurvival
  prescribedSurvival_le_one : ledger.prescribedSurvival ≤ 1
  prescribedAccumulator_le : ∀ who,
    |ledger.prescribedAccumulator who| ≤
      bound * (1 - ledger.prescribedSurvival)
  opponentSurvival_nonneg : ∀ who, 0 ≤ ledger.opponentSurvival who
  opponentSurvival_le_one : ∀ who, ledger.opponentSurvival who ≤ 1
  deviationAccumulator_le : ∀ who,
    |ledger.deviationAccumulator who| ≤
      bound * (1 - ledger.opponentSurvival who)
  finiteQuitCap_lower : ∀ who, -bound ≤ ledger.finiteQuitCap who
  finiteQuitCap_upper : ∀ who, ledger.finiteQuitCap who ≤ bound

omit [DecidableEq ι] in
theorem quittingControllerTesterLedgerInitial_isBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingControllerTesterLedgerInitial reward).IsBounded
      (quittingRewardBound reward) := by
  constructor <;> simp [quittingControllerTesterLedgerInitial,
    quittingRewardBound_nonneg]

theorem QuittingControllerTesterLedger.IsBounded.step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (ledger : QuittingControllerTesterLedger ι)
    (hledger : ledger.IsBounded (quittingRewardBound reward)) :
    (ledger.step reward root).IsBounded (quittingRewardBound reward) := by
  let bound := quittingRewardBound reward
  have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
  have hc0 : 0 ≤ quittingControllerContinueMass root :=
    quittingStationaryContinueMass_nonneg root
  have hc1 : quittingControllerContinueMass root ≤ 1 :=
    quittingStationaryContinueMass_le_one root
  constructor
  · exact mul_nonneg hledger.prescribedSurvival_nonneg hc0
  · exact mul_le_one₀ hledger.prescribedSurvival_le_one hc0 hc1
  · intro who
    have hg := abs_quittingControllerAbsorbingContribution_le
      reward root who
    have htriangle := abs_add_le (ledger.prescribedAccumulator who)
      (ledger.prescribedSurvival *
        quittingControllerAbsorbingContribution reward root who)
    have hscaled :
        |ledger.prescribedSurvival *
            quittingControllerAbsorbingContribution reward root who| ≤
          ledger.prescribedSurvival *
            (bound * (1 - quittingControllerContinueMass root)) := by
      rw [abs_mul, abs_of_nonneg hledger.prescribedSurvival_nonneg]
      exact mul_le_mul_of_nonneg_left hg
        hledger.prescribedSurvival_nonneg
    change |_ + _ * _| ≤ bound * (1 - _ * _)
    calc
      |_ + _ * _| ≤ |ledger.prescribedAccumulator who| +
          |ledger.prescribedSurvival *
            quittingControllerAbsorbingContribution reward root who| :=
        htriangle
      _ ≤ bound * (1 - ledger.prescribedSurvival) +
          ledger.prescribedSurvival *
            (bound * (1 - quittingControllerContinueMass root)) :=
        add_le_add (hledger.prescribedAccumulator_le who) hscaled
      _ = bound * (1 - ledger.prescribedSurvival *
          quittingControllerContinueMass root) := by ring
  · intro who
    exact mul_nonneg (hledger.opponentSurvival_nonneg who)
      (quittingRootOpponentContinueMass_nonneg root who)
  · intro who
    exact mul_le_one₀ (hledger.opponentSurvival_le_one who)
      (quittingRootOpponentContinueMass_nonneg root who)
      (quittingRootOpponentContinueMass_le_one root who)
  · intro who
    have ha := abs_quittingTesterContinueContribution_le reward root who
    have htriangle := abs_add_le (ledger.deviationAccumulator who)
      (ledger.opponentSurvival who *
        quittingTesterContinueContribution reward root who)
    have hscaled :
        |ledger.opponentSurvival who *
            quittingTesterContinueContribution reward root who| ≤
          ledger.opponentSurvival who *
            (bound * (1 - quittingTesterOpponentContinueMass root who)) := by
      rw [abs_mul, abs_of_nonneg (hledger.opponentSurvival_nonneg who)]
      exact mul_le_mul_of_nonneg_left ha
        (hledger.opponentSurvival_nonneg who)
    change |_ + _ * _| ≤ bound * (1 - _ * _)
    calc
      |_ + _ * _| ≤ |ledger.deviationAccumulator who| +
          |ledger.opponentSurvival who *
            quittingTesterContinueContribution reward root who| := htriangle
      _ ≤ bound * (1 - ledger.opponentSurvival who) +
          ledger.opponentSurvival who *
            (bound * (1 - quittingTesterOpponentContinueMass root who)) :=
        add_le_add (hledger.deviationAccumulator_le who) hscaled
      _ = bound * (1 - ledger.opponentSurvival who *
          quittingTesterOpponentContinueMass root who) := by ring
  · intro who
    exact le_max_of_le_left (hledger.finiteQuitCap_lower who)
  · intro who
    apply max_le (hledger.finiteQuitCap_upper who)
    have hq := abs_quittingTesterQuitValue_le reward root who
    have hp := hledger.deviationAccumulator_le who
    have hL := hledger.opponentSurvival_nonneg who
    have hqUpper := le_of_abs_le hq
    have hpUpper := le_of_abs_le hp
    have hLUpper := hledger.opponentSurvival_le_one who
    calc
      ledger.deviationAccumulator who + ledger.opponentSurvival who *
          quittingTesterQuitValue reward root who ≤
        bound * (1 - ledger.opponentSurvival who) +
          ledger.opponentSurvival who * bound := by
            gcongr
      _ = bound := by ring

/-- Every reachable ledger satisfies the sharp telescope bounds and keeps
all finite Quit candidates inside the reward box. -/
theorem quittingControllerTesterLedgerRun_isBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    (quittingControllerTesterLedgerRun reward roots cutoff).IsBounded
      (quittingRewardBound reward) := by
  induction cutoff with
  | zero => exact quittingControllerTesterLedgerInitial_isBounded reward
  | succ cutoff ih =>
      exact ih.step reward (roots cutoff)

/-- Compact coordinate domain containing every forward ledger reachable from
the canonical initial state. -/
abbrev QuittingControllerTesterLedgerBoxCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  (ι → Set.Icc (-quittingRewardBound reward) (quittingRewardBound reward)) ×
    Set.Icc (0 : ℝ) 1 ×
    (ι → Set.Icc (-quittingRewardBound reward) (quittingRewardBound reward)) ×
    (ι → Set.Icc (0 : ℝ) 1) ×
    (ι → Set.Icc (-quittingRewardBound reward) (quittingRewardBound reward))

/-- Forget the interval proofs in compact ledger-box coordinates. -/
def quittingControllerTesterLedgerOfBoxCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (coordinates : QuittingControllerTesterLedgerBoxCoordinates reward) :
    QuittingControllerTesterLedger ι where
  prescribedAccumulator := fun who => coordinates.1 who
  prescribedSurvival := coordinates.2.1
  deviationAccumulator := fun who => coordinates.2.2.1 who
  opponentSurvival := fun who => coordinates.2.2.2.1 who
  finiteQuitCap := fun who => coordinates.2.2.2.2 who

omit [DecidableEq ι] in
/-- Forgetting the ledger-box interval proofs is continuous. -/
theorem continuous_quittingControllerTesterLedgerOfBoxCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (quittingControllerTesterLedgerOfBoxCoordinates reward) := by
  rw [continuous_induced_rng]
  apply Continuous.prodMk
  · apply continuous_pi
    intro who
    exact continuous_subtype_val.comp
      ((continuous_apply who).comp continuous_fst)
  apply Continuous.prodMk
  · exact continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  apply Continuous.prodMk
  · apply continuous_pi
    intro who
    exact continuous_subtype_val.comp ((continuous_apply who).comp <|
      continuous_fst.comp (continuous_snd.comp continuous_snd))
  apply Continuous.prodMk
  · apply continuous_pi
    intro who
    exact continuous_subtype_val.comp ((continuous_apply who).comp <|
      continuous_fst.comp (continuous_snd.comp <|
        continuous_snd.comp continuous_snd))
  · apply continuous_pi
    intro who
    exact continuous_subtype_val.comp ((continuous_apply who).comp <|
      continuous_snd.comp (continuous_snd.comp <|
        continuous_snd.comp continuous_snd))

/-- A literal compact box of forward ledger coordinates. -/
def quittingControllerTesterLedgerBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingControllerTesterLedger ι) :=
  Set.range (quittingControllerTesterLedgerOfBoxCoordinates reward)

omit [DecidableEq ι] in
/-- The literal ledger coordinate box is compact. -/
theorem quittingControllerTesterLedgerBox_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingControllerTesterLedgerBox reward) :=
  isCompact_range
    (continuous_quittingControllerTesterLedgerOfBoxCoordinates reward)

/-- Every reachable ledger lies in the literal compact coordinate box. -/
theorem quittingControllerTesterLedgerRun_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingControllerTesterLedgerRun reward roots cutoff ∈
      quittingControllerTesterLedgerBox reward := by
  let ledger := quittingControllerTesterLedgerRun reward roots cutoff
  have hledger : ledger.IsBounded (quittingRewardBound reward) :=
    quittingControllerTesterLedgerRun_isBounded reward roots cutoff
  have hbound : 0 ≤ quittingRewardBound reward :=
    quittingRewardBound_nonneg reward
  have hprescribed (who : ι) :
      -quittingRewardBound reward ≤ ledger.prescribedAccumulator who ∧
        ledger.prescribedAccumulator who ≤ quittingRewardBound reward := by
    apply abs_le.mp
    exact (hledger.prescribedAccumulator_le who).trans <| by
      have hsurvival := hledger.prescribedSurvival_nonneg
      nlinarith [hledger.prescribedSurvival_le_one]
  have hdeviation (who : ι) :
      -quittingRewardBound reward ≤ ledger.deviationAccumulator who ∧
        ledger.deviationAccumulator who ≤ quittingRewardBound reward := by
    apply abs_le.mp
    exact (hledger.deviationAccumulator_le who).trans <| by
      have hsurvival := hledger.opponentSurvival_nonneg who
      nlinarith [hledger.opponentSurvival_le_one who]
  refine ⟨((fun who => ⟨ledger.prescribedAccumulator who,
      hprescribed who⟩),
    ⟨ledger.prescribedSurvival, hledger.prescribedSurvival_nonneg,
      hledger.prescribedSurvival_le_one⟩,
    (fun who => ⟨ledger.deviationAccumulator who, hdeviation who⟩),
    (fun who => ⟨ledger.opponentSurvival who,
      hledger.opponentSurvival_nonneg who,
      hledger.opponentSurvival_le_one who⟩),
    (fun who => ⟨ledger.finiteQuitCap who,
      hledger.finiteQuitCap_lower who,
      hledger.finiteQuitCap_upper who⟩)), ?_⟩
  rfl

/-- Forward ledgers reachable by finite simplex root words. -/
def quittingControllerTesterReachableLedgers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingControllerTesterLedger ι) :=
  {ledger | ∃ roots : ℕ → QuittingRootSimplex ι, ∃ cutoff : ℕ,
    ledger = quittingControllerTesterLedgerRun reward
      (fun time => quittingRootOfSimplex (roots time)) cutoff}

/-- The closure of all finitely reachable forward ledgers is compact. -/
theorem quittingControllerTesterReachableLedgers_closure_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (closure (quittingControllerTesterReachableLedgers reward)) := by
  apply (quittingControllerTesterLedgerBox_isCompact reward).of_isClosed_subset
    isClosed_closure
  apply closure_minimal
  · rintro ledger ⟨roots, cutoff, rfl⟩
    exact quittingControllerTesterLedgerRun_mem_box reward _ cutoff
  · exact (quittingControllerTesterLedgerBox_isCompact reward).isClosed

/-- Every elapsed pure finite Quit value is recorded by the cap coordinate. -/
theorem quittingControllerTesterLedgerRun_candidate_le_finiteQuitCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (who : ι)
    {time : ℕ} (htime : time < cutoff) :
    (quittingControllerTesterLedgerRun reward roots time).deviationAccumulator who +
        (quittingControllerTesterLedgerRun reward roots time).opponentSurvival who *
          quittingTesterQuitValue reward (roots time) who ≤
      (quittingControllerTesterLedgerRun reward roots cutoff).finiteQuitCap who := by
  induction cutoff with
  | zero => omega
  | succ cutoff ih =>
      rw [quittingControllerTesterLedgerRun_succ]
      change _ ≤ max _ _
      by_cases hlast : time = cutoff
      · subst time
        exact le_max_right _ _
      · exact (ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ htime) hlast)).trans
          (le_max_left _ _)

/-- The cap coordinate is the least upper bound generated from the `-R`
sentinel and all elapsed pure finite Quit candidates. -/
theorem quittingControllerTesterLedgerRun_finiteQuitCap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (who : ι) (bound : ℝ)
    (hsentinel : -quittingRewardBound reward ≤ bound)
    (hcandidate : ∀ time < cutoff,
      (quittingControllerTesterLedgerRun reward roots time).deviationAccumulator who +
          (quittingControllerTesterLedgerRun reward roots time).opponentSurvival who *
            quittingTesterQuitValue reward (roots time) who ≤ bound) :
    (quittingControllerTesterLedgerRun reward roots cutoff).finiteQuitCap who ≤ bound := by
  induction cutoff with
  | zero => simpa [quittingControllerTesterLedgerRun,
      quittingControllerTesterLedgerInitial] using hsentinel
  | succ cutoff ih =>
      rw [quittingControllerTesterLedgerRun_succ]
      change max _ _ ≤ bound
      apply max_le
      · exact ih fun time htime => hcandidate time (Nat.lt_succ_of_lt htime)
      · exact hcandidate cutoff (Nat.lt_add_one cutoff)

/-- Semantic pair read from a finite ledger when every later root is
all-Continue. The elapsed cap is compared with later solo Quit and Never. -/
def QuittingControllerTesterLedger.neverTailSemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ledger : QuittingControllerTesterLedger ι) :
    QuittingTerminalSemanticPair ι :=
  (ledger.prescribedAccumulator, fun who =>
    max (ledger.finiteQuitCap who)
      (ledger.deviationAccumulator who + ledger.opponentSurvival who *
        max (reward (quittingSingletonTerminal who) who) 0))

end GameTheory
