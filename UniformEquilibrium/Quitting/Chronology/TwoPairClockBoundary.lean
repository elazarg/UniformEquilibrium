/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.SquareRootCoalitionClock
import MathUE.ProbabilityMassFunction.Simplex
import MathUE.Topology.FiniteLimitDecomposition
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseLawComparison
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Projective.AnalyticPacket
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass
import UniformEquilibrium.Quitting.Root.SequencePayoff

/-!
# The finite two-pair clock boundary

This module defines the literal two-stage gate exposed by sharp two-pair clock saturation.  It
also records the finite strategic consumer.  The results here do not assert that a reward gadget
forces positive target masses or vanishing square-root defect; those remain producer hypotheses.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Four distinct roles arranged into two disjoint clock pairs. -/
structure QuittingTwoPairGateRoles (ι : Type) [DecidableEq ι] where
  firstA : ι
  secondA : ι
  firstB : ι
  secondB : ι
  firstA_ne_secondA : firstA ≠ secondA
  firstB_ne_secondB : firstB ≠ secondB
  pairs_disjoint : Disjoint ({firstA, secondA} : Finset ι) {firstB, secondB}

namespace QuittingTwoPairGateRoles

/-! ## Source-native chronological coalition laws -/

/-- Unconditional exact-coalition mass at one live date of a root sequence. -/
def rootSequenceStageCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (coalition : Finset ι) : ℝ :=
  quittingJointSurvivalWeight roots 0 time *
    quittingRootCoalitionMass (roots time) coalition

theorem rootSequenceStageCoalitionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (coalition : Finset ι) :
    0 ≤ rootSequenceStageCoalitionMass roots time coalition :=
  mul_nonneg (quittingJointSurvivalWeight_nonneg roots 0 time)
    (quittingRootCoalitionMass_nonneg' (roots time) coalition)

/-- Total absorption mass at one date. -/
def rootSequenceStageAbsorptionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  quittingJointSurvivalWeight roots 0 time *
    (1 - quittingStationaryContinueMass (roots time))

omit [DecidableEq ι] in
theorem rootSequenceStageAbsorptionMass_eq_survival_sub_succ
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    rootSequenceStageAbsorptionMass roots time =
      quittingJointSurvivalWeight roots 0 time -
        quittingJointSurvivalWeight roots 0 (time + 1) := by
  rw [rootSequenceStageAbsorptionMass, quittingJointSurvivalWeight_succ]
  simp only [Nat.zero_add]
  ring

omit [DecidableEq ι] in
theorem rootSequenceStageAbsorptionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    0 ≤ rootSequenceStageAbsorptionMass roots time := by
  exact mul_nonneg (quittingJointSurvivalWeight_nonneg roots 0 time)
    (sub_nonneg.mpr (quittingStationaryContinueMass_le_one (roots time)))

omit [DecidableEq ι] in
theorem summable_rootSequenceStageAbsorptionMass
    (roots : ℕ → ι → PMF Bool) :
    Summable (rootSequenceStageAbsorptionMass roots) := by
  apply summable_of_sum_range_le (rootSequenceStageAbsorptionMass_nonneg roots)
  intro horizon
  simp_rw [rootSequenceStageAbsorptionMass_eq_survival_sub_succ]
  rw [Finset.sum_range_sub']
  have hnonneg := quittingJointSurvivalWeight_nonneg roots 0 horizon
  simp [quittingJointSurvivalWeight] at hnonneg ⊢
  linarith

theorem rootSequenceStageCoalitionMass_le_absorptionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (coalition : Finset ι) (coalition_nonempty : coalition.Nonempty) :
    rootSequenceStageCoalitionMass roots time coalition ≤
      rootSequenceStageAbsorptionMass roots time := by
  have hmem : coalition ∈
      (Finset.univ : Finset (Finset ι)).erase ∅ := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact Finset.nonempty_iff_ne_empty.mp coalition_nonempty
  have hcoalition_le : quittingRootCoalitionMass (roots time) coalition ≤
      ∑ other ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
        quittingRootCoalitionMass (roots time) other := by
    exact Finset.single_le_sum
      (fun other _ => quittingRootCoalitionMass_nonneg' (roots time) other) hmem
  rw [quittingRootCoalitionMass_sum_nonempty] at hcoalition_le
  exact mul_le_mul_of_nonneg_left hcoalition_le
    (quittingJointSurvivalWeight_nonneg roots 0 time)

theorem summable_rootSequenceStageCoalitionMass
    (roots : ℕ → ι → PMF Bool) (coalition : Finset ι)
    (coalition_nonempty : coalition.Nonempty) :
    Summable (fun time => rootSequenceStageCoalitionMass roots time coalition) :=
  Summable.of_nonneg_of_le
    (fun time => rootSequenceStageCoalitionMass_nonneg roots time coalition)
    (fun time => rootSequenceStageCoalitionMass_le_absorptionMass
      roots time coalition coalition_nonempty)
    (summable_rootSequenceStageAbsorptionMass roots)

/-- Actual infinite first-absorption law of a root sequence. -/
def rootSequenceTerminalCoalitionMass
    (roots : ℕ → ι → PMF Bool) (coalition : Finset ι) : ℝ :=
  ∑' time, rootSequenceStageCoalitionMass roots time coalition

/-- Quit-probability clock read directly from a root sequence. -/
def rootSequenceHazard (roots : ℕ → ι → PMF Bool) (time : ℕ) (player : ι) : ℝ :=
  (roots time player true).toReal

omit [Fintype ι] [DecidableEq ι] in
theorem rootSequenceHazard_mem_Icc
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (player : ι) :
    rootSequenceHazard roots time player ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · have hle := PMF.coe_le_one (roots time player) true
    exact (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (roots time player) true) (by norm_num)).mpr hle |>.trans_eq (by simp)

theorem finiteJointContinueClock_rootSequenceHazard_range
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    Math.Probability.finiteJointContinueClock (Finset.range cutoff) Finset.univ
        (rootSequenceHazard roots) =
      quittingJointSurvivalWeight roots 0 cutoff := by
  rw [quittingJointSurvivalWeight_eq_prod]
  unfold Math.Probability.finiteJointContinueClock rootSequenceHazard
  apply Finset.prod_congr rfl
  intro time _
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_congr rfl
  intro player _
  simp [pmfBool_false_toReal]

theorem finiteJointContinueClock_rootSequenceHazard
    (roots : ℕ → ι → PMF Bool) (dates : Finset ℕ) :
    Math.Probability.finiteJointContinueClock dates Finset.univ
        (rootSequenceHazard roots) =
      ∏ time ∈ dates, quittingStationaryContinueMass (roots time) := by
  unfold Math.Probability.finiteJointContinueClock rootSequenceHazard
  apply Finset.prod_congr rfl
  intro time _
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_congr rfl
  intro player _
  rw [pmfBool_false_toReal]

theorem quittingRootDeletedContinueMass_eq_prod_erase
    (root : ι → PMF Bool) (who : ι) :
    quittingRootDeletedContinueMass root who =
      ∏ player ∈ (Finset.univ : Finset ι).erase who,
        (root player false).toReal := by
  rw [quittingRootDeletedContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    ← Finset.mul_prod_erase Finset.univ
      (fun player => (Function.update root who (PMF.pure false) player false).toReal)
      (Finset.mem_univ who)]
  have hown : (Function.update root who (PMF.pure false) who false).toReal = 1 := by
    simp
  rw [hown, one_mul]
  apply Finset.prod_congr rfl
  intro player hplayer
  simp [Function.update, Finset.ne_of_mem_erase hplayer]

theorem finiteDeletedContinueClock_rootSequenceHazard
    (roots : ℕ → ι → PMF Bool) (dates : Finset ℕ) (who : ι) :
    Math.Probability.finiteDeletedContinueClock dates Finset.univ
        (rootSequenceHazard roots) who =
      ∏ time ∈ dates, quittingRootDeletedContinueMass (roots time) who := by
  unfold Math.Probability.finiteDeletedContinueClock rootSequenceHazard
  apply Finset.prod_congr rfl
  intro time _
  rw [quittingRootDeletedContinueMass_eq_prod_erase]
  apply Finset.prod_congr rfl
  intro player _
  rw [pmfBool_false_toReal]

omit [DecidableEq ι] in
theorem sum_range_rootSequenceStageAbsorptionMass
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff, rootSequenceStageAbsorptionMass roots time) =
      1 - quittingJointSurvivalWeight roots 0 cutoff := by
  simp_rw [rootSequenceStageAbsorptionMass_eq_survival_sub_succ]
  rw [Finset.sum_range_sub']
  simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]

omit [DecidableEq ι] in
theorem sum_Ico_rootSequenceStageAbsorptionMass
    (roots : ℕ → ι → PMF Bool) (first second : ℕ) (h : first ≤ second) :
    (∑ time ∈ Finset.Ico first second, rootSequenceStageAbsorptionMass roots time) =
      quittingJointSurvivalWeight roots 0 first -
        quittingJointSurvivalWeight roots 0 second := by
  rw [Finset.sum_Ico_eq_sub _ h,
    sum_range_rootSequenceStageAbsorptionMass,
    sum_range_rootSequenceStageAbsorptionMass]
  ring

theorem rootSequenceTerminalCoalitionMass_eq_split_two_dates
    (roots : ℕ → ι → PMF Bool) (coalition : Finset ι)
    (coalition_nonempty : coalition.Nonempty)
    (first second : ℕ) (first_lt_second : first < second) :
    rootSequenceTerminalCoalitionMass roots coalition =
      (∑ time ∈ Finset.range first,
        rootSequenceStageCoalitionMass roots time coalition) +
      rootSequenceStageCoalitionMass roots first coalition +
      (∑ time ∈ Finset.Ico (first + 1) second,
        rootSequenceStageCoalitionMass roots time coalition) +
      rootSequenceStageCoalitionMass roots second coalition +
      ∑' offset, rootSequenceStageCoalitionMass roots (second + 1 + offset) coalition := by
  have hsummable :=
    summable_rootSequenceStageCoalitionMass roots coalition coalition_nonempty
  have hsplit := hsummable.sum_add_tsum_nat_add (second + 1)
  have hprefix :
      (∑ time ∈ Finset.range (second + 1),
        rootSequenceStageCoalitionMass roots time coalition) =
        (∑ time ∈ Finset.range first,
          rootSequenceStageCoalitionMass roots time coalition) +
        rootSequenceStageCoalitionMass roots first coalition +
        (∑ time ∈ Finset.Ico (first + 1) second,
          rootSequenceStageCoalitionMass roots time coalition) +
        rootSequenceStageCoalitionMass roots second coalition := by
    rw [Finset.sum_range_succ,
      ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_iff.mpr first_lt_second),
      Finset.sum_range_succ]
  rw [rootSequenceTerminalCoalitionMass, ← hsplit, hprefix]
  simp only [Nat.add_comm, Nat.add_left_comm]

theorem tail_rootSequenceStageCoalitionMass_le_survival
    (roots : ℕ → ι → PMF Bool) (coalition : Finset ι)
    (coalition_nonempty : coalition.Nonempty) (start : ℕ) :
    (∑' offset, rootSequenceStageCoalitionMass roots (start + offset) coalition) ≤
      quittingJointSurvivalWeight roots 0 start := by
  have hcoalition : Summable (fun offset =>
      rootSequenceStageCoalitionMass roots (start + offset) coalition) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff start).2
        (summable_rootSequenceStageCoalitionMass roots coalition coalition_nonempty)
  have habsorption : Summable (fun offset =>
      rootSequenceStageAbsorptionMass roots (start + offset)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff start).2 (summable_rootSequenceStageAbsorptionMass roots)
  calc
    (∑' offset, rootSequenceStageCoalitionMass roots (start + offset) coalition) ≤
        ∑' offset, rootSequenceStageAbsorptionMass roots (start + offset) :=
      hcoalition.tsum_le_tsum
        (fun offset => rootSequenceStageCoalitionMass_le_absorptionMass
          roots (start + offset) coalition coalition_nonempty)
        habsorption
    _ ≤ quittingJointSurvivalWeight roots 0 start := by
      apply Real.tsum_le_of_sum_range_le
      · intro offset
        exact rootSequenceStageAbsorptionMass_nonneg roots (start + offset)
      · intro horizon
        have hrewrite : ∀ offset,
            rootSequenceStageAbsorptionMass roots (start + offset) =
              quittingJointSurvivalWeight roots 0 (start + offset) -
                quittingJointSurvivalWeight roots 0 (start + (offset + 1)) := by
          intro offset
          rw [rootSequenceStageAbsorptionMass_eq_survival_sub_succ]
          congr 2
        simp_rw [hrewrite]
        rw [Finset.sum_range_sub']
        have hnonneg := quittingJointSurvivalWeight_nonneg roots 0 (start + horizon)
        simp only [Nat.add_zero]
        linarith

/-- First root of the literal `A → B` gate: the `A` pair uses the common hazard `p`. -/
def firstRoot (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1) :
    ι → PMF Bool := fun player =>
  if player = roles.firstA ∨ player = roles.secondA then
    bernoulliBool p p.property.1 p.property.2
  else PMF.pure false

/-- Second root of the literal gate: the `B` pair quits surely. -/
def secondRoot (roles : QuittingTwoPairGateRoles ι) : ι → PMF Bool := fun player =>
  if player = roles.firstB ∨ player = roles.secondB then
    PMF.pure true
  else PMF.pure false

/-- Root sequence of the literal two-stage gate.  Later roots are irrelevant because the second
pair supplies a sure exit. -/
def roots (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1) :
    ℕ → ι → PMF Bool
  | 0 => roles.firstRoot p
  | 1 => roles.secondRoot
  | _ => fun _ => PMF.pure false

/-- Literal history-independent behavior profile generated by the two-stage gate. -/
def profile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward (roles.roots p) 0

/-- Exact terminal-coalition mass of a two-stage profile whose second root is reached only after
all players continue at the first root. -/
def twoStageCoalitionMass
    (first second : ι → PMF Bool) (coalition : Finset ι) : ℝ :=
  quittingRootCoalitionMass first coalition +
    quittingStationaryContinueMass first *
      quittingRootCoalitionMass second coalition

/-- Literal `A → B` two-gate coalition law. -/
def coalitionMass (roles : QuittingTwoPairGateRoles ι)
    (p : Set.Icc (0 : ℝ) 1) (coalition : Finset ι) : ℝ :=
  twoStageCoalitionMass (roles.firstRoot p) roles.secondRoot coalition

/-- The three pure-time ports that suffice against a literal two-stage gate. -/
inductive PurePort
  | firstGate
  | secondGate
  | never
  deriving DecidableEq, Fintype

instance : Nonempty PurePort := ⟨.never⟩

/-- The deterministic quit time represented by a displayed port at selected source dates. -/
def PurePort.quitTime (first second : ℕ) : PurePort → Option ℕ
  | .firstGate => some first
  | .secondGate => some second
  | .never => none

/-- Source root sequence after one player chooses one of the three selected pure-time ports. -/
def sourcePortRootSequence (source : ℕ → ι → PMF Bool) (who : ι)
    (first second : ℕ) (port : PurePort) : ℕ → ι → PMF Bool :=
  quittingRootSequenceUpdate source who
    (quittingPureTimeHazard (port.quitTime first second))

theorem sourcePort_survival_before_eq_deletedClock
    (source : ℕ → ι → PMF Bool) (who : ι)
    (first second : ℕ) (first_lt_second : first < second) (port : PurePort) :
    quittingJointSurvivalWeight
        (sourcePortRootSequence source who first second port) 0 first =
      Math.Probability.finiteDeletedContinueClock (Finset.range first) Finset.univ
        (rootSequenceHazard source) who := by
  rw [finiteDeletedContinueClock_rootSequenceHazard,
    quittingJointSurvivalWeight_eq_prod]
  apply Finset.prod_congr rfl
  intro time htime
  have time_lt : time < first := Finset.mem_range.mp htime
  cases port <;>
    simp [sourcePortRootSequence, PurePort.quitTime, quittingRootSequenceUpdate,
      quittingPureTimeHazard, quittingRootDeletedContinueMass,
      ne_of_lt time_lt, ne_of_lt (time_lt.trans first_lt_second)]

theorem sourcePort_survival_second_eq_firstSuccessor_mul_deletedClock
    (source : ℕ → ι → PMF Bool) (who : ι)
    (first second : ℕ) (first_lt_second : first < second) (port : PurePort) :
    quittingJointSurvivalWeight
        (sourcePortRootSequence source who first second port) 0 second =
      quittingJointSurvivalWeight
          (sourcePortRootSequence source who first second port) 0 (first + 1) *
        Math.Probability.finiteDeletedContinueClock
          (Finset.Ico (first + 1) second) Finset.univ
          (rootSequenceHazard source) who := by
  rw [finiteDeletedContinueClock_rootSequenceHazard,
    quittingJointSurvivalWeight_eq_prod, quittingJointSurvivalWeight_eq_prod]
  simp only [Nat.zero_add]
  have htail :
      (∏ time ∈ Finset.Ico (first + 1) second,
        quittingStationaryContinueMass
          (sourcePortRootSequence source who first second port time)) =
        ∏ time ∈ Finset.Ico (first + 1) second,
          quittingRootDeletedContinueMass (source time) who := by
    apply Finset.prod_congr rfl
    intro time htime
    have time_gt : first < time := Nat.lt_of_succ_le (Finset.mem_Ico.mp htime).1
    have time_lt : time < second := (Finset.mem_Ico.mp htime).2
    cases port <;>
      simp [sourcePortRootSequence, PurePort.quitTime, quittingRootSequenceUpdate,
        quittingPureTimeHazard, quittingRootDeletedContinueMass,
        ne_of_gt time_gt, ne_of_lt time_lt]
  rw [← Finset.prod_range_mul_prod_Ico _ (Nat.succ_le_iff.mpr first_lt_second),
    htail]

theorem source_survival_second_eq_firstSuccessor_mul_jointClock
    (source : ℕ → ι → PMF Bool)
    (first second : ℕ) (first_lt_second : first < second) :
    quittingJointSurvivalWeight source 0 second =
      quittingJointSurvivalWeight source 0 (first + 1) *
        Math.Probability.finiteJointContinueClock
          (Finset.Ico (first + 1) second) Finset.univ
          (rootSequenceHazard source) := by
  rw [finiteJointContinueClock_rootSequenceHazard,
    quittingJointSurvivalWeight_eq_prod, quittingJointSurvivalWeight_eq_prod]
  simp only [Nat.zero_add]
  rw [← Finset.prod_range_mul_prod_Ico _ (Nat.succ_le_iff.mpr first_lt_second)]

theorem sourcePort_before_tendsto_zero_of_source
    (source : ℕ → ℕ → ι → PMF Bool) (first second : ℕ → ℕ)
    (first_lt_second : ∀ n, first n < second n)
    (source_tendsto : Tendsto (fun n =>
      1 - quittingJointSurvivalWeight (source n) 0 (first n)) atTop (nhds 0))
    (who : ι) (port : PurePort) :
    Tendsto (fun n => 1 - quittingJointSurvivalWeight
      (sourcePortRootSequence (source n) who (first n) (second n) port)
        0 (first n)) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    rw [sourcePort_survival_before_eq_deletedClock
      (source n) who (first n) (second n) (first_lt_second n) port]
    exact sub_nonneg.mpr (Math.Probability.finiteDeletedContinueClock_le_one
      (Finset.range (first n)) Finset.univ (rootSequenceHazard (source n)) who
      (fun time _ player _ => rootSequenceHazard_mem_Icc (source n) time player))
  · intro n
    show 1 - quittingJointSurvivalWeight
        (sourcePortRootSequence (source n) who (first n) (second n) port)
          0 (first n) ≤
      1 - quittingJointSurvivalWeight (source n) 0 (first n)
    rw [sourcePort_survival_before_eq_deletedClock
      (source n) who (first n) (second n) (first_lt_second n) port,
      ← finiteJointContinueClock_rootSequenceHazard_range]
    have hle := Math.Probability.finiteJointContinueClock_le_deleted
      (Finset.range (first n)) Finset.univ (rootSequenceHazard (source n)) who
      (Finset.mem_univ who)
      (fun time _ player _ => rootSequenceHazard_mem_Icc (source n) time player)
    linarith
  · exact source_tendsto

theorem sourcePort_between_tendsto_zero_of_source
    (source : ℕ → ℕ → ι → PMF Bool) (first second : ℕ → ℕ)
    (first_lt_second : ∀ n, first n < second n) {reachFloor : ℝ}
    (reachFloor_pos : 0 < reachFloor)
    (sourceReach_ge : ∀ n,
      reachFloor ≤ quittingJointSurvivalWeight (source n) 0 (first n + 1))
    (source_tendsto : Tendsto (fun n =>
      quittingJointSurvivalWeight (source n) 0 (first n + 1) -
        quittingJointSurvivalWeight (source n) 0 (second n)) atTop (nhds 0))
    (who : ι) (port : PurePort) :
    Tendsto (fun n =>
      quittingJointSurvivalWeight
          (sourcePortRootSequence (source n) who (first n) (second n) port)
            0 (first n + 1) -
        quittingJointSurvivalWeight
          (sourcePortRootSequence (source n) who (first n) (second n) port)
            0 (second n)) atTop (nhds 0) := by
  let sourceAbsorption : ℕ → ℝ := fun n =>
    quittingJointSurvivalWeight (source n) 0 (first n + 1) -
      quittingJointSurvivalWeight (source n) 0 (second n)
  have hmajorant : Tendsto (fun n => sourceAbsorption n / reachFloor) atTop (nhds 0) := by
    simpa [sourceAbsorption] using source_tendsto.div_const reachFloor
  apply squeeze_zero
  · intro n
    exact sub_nonneg.mpr (antitone_quittingJointSurvivalWeight
      (sourcePortRootSequence (source n) who (first n) (second n) port) 0
      (Nat.succ_le_iff.mpr (first_lt_second n)))
  · intro n
    show quittingJointSurvivalWeight
          (sourcePortRootSequence (source n) who (first n) (second n) port)
            0 (first n + 1) -
        quittingJointSurvivalWeight
          (sourcePortRootSequence (source n) who (first n) (second n) port)
            0 (second n) ≤ sourceAbsorption n / reachFloor
    rw [sourcePort_survival_second_eq_firstSuccessor_mul_deletedClock
      (source n) who (first n) (second n) (first_lt_second n) port]
    have hbound := Math.Probability.finiteClock_deletedCounterfactualAbsorption_le_div
      (Finset.Ico (first n + 1) (second n)) Finset.univ
      (rootSequenceHazard (source n)) who (Finset.mem_univ who)
      (fun time _ player _ => rootSequenceHazard_mem_Icc (source n) time player)
      (sourceReach_ge n) reachFloor_pos
      ⟨quittingJointSurvivalWeight_nonneg
          (sourcePortRootSequence (source n) who (first n) (second n) port)
          0 (first n + 1),
        quittingJointSurvivalWeight_le_one
          (sourcePortRootSequence (source n) who (first n) (second n) port)
          0 (first n + 1)⟩
      (baselineAbsorption := sourceAbsorption n)
      (by dsimp only [sourceAbsorption]
          rw [source_survival_second_eq_firstSuccessor_mul_jointClock
          (source n) (first n) (second n) (first_lt_second n)]
          ring)
    dsimp only [sourceAbsorption] at hbound ⊢
    linarith
  · exact hmajorant

/-- The two roots after one player chooses a displayed pure port. -/
def portRoots (roles : QuittingTwoPairGateRoles ι)
    (p : Set.Icc (0 : ℝ) 1) (who : ι) : PurePort →
      (ι → PMF Bool) × (ι → PMF Bool)
  | .firstGate =>
      (Function.update (roles.firstRoot p) who (PMF.pure true),
        Function.update roles.secondRoot who (PMF.pure false))
  | .secondGate =>
      (Function.update (roles.firstRoot p) who (PMF.pure false),
        Function.update roles.secondRoot who (PMF.pure true))
  | .never =>
      (Function.update (roles.firstRoot p) who (PMF.pure false),
        Function.update roles.secondRoot who (PMF.pure false))

omit [Fintype ι] in
theorem secondRoot_exists_sureQuitter_ne
    (roles : QuittingTwoPairGateRoles ι) (who : ι) :
    ∃ quitter, quitter ≠ who ∧ roles.secondRoot quitter = PMF.pure true := by
  by_cases hfirst : roles.firstB = who
  · refine ⟨roles.secondB, ?_, ?_⟩
    · intro hsecond
      exact roles.firstB_ne_secondB (hfirst.trans hsecond.symm)
    · simp [secondRoot]
  · exact ⟨roles.firstB, hfirst, by simp [secondRoot]⟩

theorem portRoots_second_continueMass_eq_zero
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (who : ι) (port : PurePort) :
    quittingStationaryContinueMass (roles.portRoots p who port).2 = 0 := by
  obtain ⟨quitter, quitter_ne, quitter_sure⟩ := roles.secondRoot_exists_sureQuitter_ne who
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  refine Finset.prod_eq_zero (Finset.mem_univ quitter) ?_
  cases port <;>
    simp [portRoots, Function.update, quitter_ne, quitter_sure]

theorem secondRoot_continueMass_eq_zero
    (roles : QuittingTwoPairGateRoles ι) :
    quittingStationaryContinueMass roles.secondRoot = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  refine Finset.prod_eq_zero (Finset.mem_univ roles.firstB) ?_
  simp [secondRoot]

omit [Fintype ι] in
theorem sourcePortRootSequence_firstRoot_tendsto
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (source : ℕ → ℕ → ι → PMF Bool) (first second : ℕ → ℕ)
    (first_lt_second : ∀ n, first n < second n)
    (coordinate : ∀ player,
      Tendsto (fun n => (source n (first n) player true).toReal) atTop
        (nhds ((roles.firstRoot p player true).toReal)))
    (who player : ι) (port : PurePort) :
    Tendsto (fun n =>
      (sourcePortRootSequence (source n) who (first n) (second n) port
        (first n) player true).toReal) atTop
      (nhds (((roles.portRoots p who port).1 player true).toReal)) := by
  by_cases player_eq : player = who
  · subst player
    cases port <;>
      simp [sourcePortRootSequence, PurePort.quitTime, quittingRootSequenceUpdate,
        quittingPureTimeHazard, portRoots, ne_of_lt (first_lt_second _)]
  · cases port <;>
      simpa [sourcePortRootSequence, PurePort.quitTime, quittingRootSequenceUpdate,
        quittingPureTimeHazard, portRoots, player_eq,
        ne_of_lt (first_lt_second _)] using
        coordinate player

omit [Fintype ι] in
theorem sourcePortRootSequence_secondRoot_tendsto
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (source : ℕ → ℕ → ι → PMF Bool) (first second : ℕ → ℕ)
    (first_lt_second : ∀ n, first n < second n)
    (coordinate : ∀ player,
      Tendsto (fun n => (source n (second n) player true).toReal) atTop
        (nhds ((roles.secondRoot player true).toReal)))
    (who player : ι) (port : PurePort) :
    Tendsto (fun n =>
      (sourcePortRootSequence (source n) who (first n) (second n) port
        (second n) player true).toReal) atTop
      (nhds (((roles.portRoots p who port).2 player true).toReal)) := by
  by_cases player_eq : player = who
  · subst player
    cases port <;>
      simp [sourcePortRootSequence, PurePort.quitTime, quittingRootSequenceUpdate,
        quittingPureTimeHazard, portRoots, ne_of_gt (first_lt_second _)]
  · cases port <;>
      simpa [sourcePortRootSequence, PurePort.quitTime, quittingRootSequenceUpdate,
        quittingPureTimeHazard, portRoots, player_eq,
        ne_of_gt (first_lt_second _)] using
        coordinate player

/-- Terminal payoff under a supplied pair of roots when the second row absorbs surely. -/
def twoStagePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootAbsorbingContribution reward first who +
    quittingStationaryContinueMass first *
      quittingRootAbsorbingContribution reward second who

/-- Expected payoff of a supplied terminal-coalition law. -/
def coalitionLawPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : Finset ι → ℝ) (who : ι) : ℝ :=
  ∑ terminal : {S : Finset ι // S.Nonempty}, mass terminal.val * reward terminal who

/-- The absorbing contribution is the expected reward of the exact root-coalition law. -/
theorem quittingRootAbsorbingContribution_eq_coalitionLawPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorbingContribution reward root who =
      coalitionLawPayoff reward (quittingRootCoalitionMass root) who := by
  rw [quittingRootAbsorbingContribution_eq_sum_coalitionMass]
  let f : Finset ι → ℝ := fun S =>
    Math.PMFProduct.coalitionMass
        (fun owner => ((root owner) true).toReal) S *
      quittingProjectiveCoalitionReward reward S who
  have hfilter :
      ∑ S ∈ (Finset.univ.filter fun S : Finset ι => S.Nonempty), f S =
        ∑ S ∈ (Finset.univ : Finset (Finset ι)), f S := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S _ hnot
    have hempty : ¬ S.Nonempty := by simpa using hnot
    simp [f, hempty, quittingProjectiveCoalitionReward]
  change (∑ S ∈ (Finset.univ : Finset (Finset ι)), f S) = _
  rw [← hfilter]
  rw [Finset.sum_subtype (Finset.univ.filter fun S : Finset ι => S.Nonempty)]
  · apply Finset.sum_congr rfl
    intro terminal _
    simp only [f, quittingProjectiveCoalitionReward, terminal.property, dite_true]
    congr 1
  · intro S
    simp

/-- The source-native infinite coalition law evaluates to the actual terminal payoff of its
root-sequence profile.  The event of never absorbing carries the production terminal value zero. -/
theorem quittingRootSequenceTerminalValue_eq_coalitionLawPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    quittingRootSequenceTerminalValue reward roots who 0 =
      coalitionLawPayoff reward (rootSequenceTerminalCoalitionMass roots) who := by
  rw [quittingRootSequenceTerminalValue_eq_tsum_absorbingContribution]
  simp_rw [quittingRootAbsorbingContribution_eq_coalitionLawPayoff,
    coalitionLawPayoff, Finset.mul_sum]
  have hsummable : ∀ terminal : {S : Finset ι // S.Nonempty},
      Summable (fun time =>
        rootSequenceStageCoalitionMass roots time terminal.val * reward terminal who) := by
    intro terminal
    exact (summable_rootSequenceStageCoalitionMass roots terminal.val
      terminal.property).mul_right (reward terminal who)
  simp only [Nat.zero_add, ← mul_assoc]
  change (∑' time : ℕ, ∑ terminal,
      rootSequenceStageCoalitionMass roots time terminal.val * reward terminal who) = _
  rw [Summable.tsum_finsetSum fun terminal _ => hsummable terminal]
  apply Finset.sum_congr rfl
  intro terminal _
  rw [tsum_mul_right]
  rfl

/-- The recursive two-stage payoff is the expected reward of the displayed two-stage law. -/
theorem twoStagePayoff_eq_coalitionLawPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι → PMF Bool) (who : ι) :
    twoStagePayoff reward first second who =
      coalitionLawPayoff reward (twoStageCoalitionMass first second) who := by
  rw [twoStagePayoff, quittingRootAbsorbingContribution_eq_coalitionLawPayoff,
    quittingRootAbsorbingContribution_eq_coalitionLawPayoff]
  unfold coalitionLawPayoff twoStageCoalitionMass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro terminal _
  ring

/-- Prescribed payoff of the literal gate. -/
def prescribedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (who : ι) : ℝ :=
  twoStagePayoff reward (roles.firstRoot p) roles.secondRoot who

/-- Payoff from one of the three literal pure ports. -/
def purePortPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (who : ι) (port : PurePort) : ℝ :=
  twoStagePayoff reward (roles.portRoots p who port).1
    (roles.portRoots p who port).2 who

omit [DecidableEq ι] in
/-- A root carrying a sure quitter has zero all-Continue mass. -/
theorem continueMass_eq_zero_of_sureQuitter
    {root : ι → PMF Bool} {quitter : ι}
    (hquit : root quitter = PMF.pure true) :
    quittingStationaryContinueMass root = 0 := by
  exact quittingStationaryContinueMass_of_sureQuitter hquit

/-- Updating one coordinate of the second gate cannot remove both distinct sure quitters. -/
theorem secondRoot_update_continueMass_eq_zero
    (roles : QuittingTwoPairGateRoles ι) (who : ι) (marginal : PMF Bool) :
    quittingStationaryContinueMass
      (Function.update roles.secondRoot who marginal) = 0 := by
  by_cases hwho : who = roles.firstB
  · apply continueMass_eq_zero_of_sureQuitter (quitter := roles.secondB)
    rw [Function.update_of_ne]
    · simp [secondRoot]
    · exact Ne.symm (hwho.trans_ne roles.firstB_ne_secondB)
  · apply continueMass_eq_zero_of_sureQuitter (quitter := roles.firstB)
    rw [Function.update_of_ne]
    · simp [secondRoot]
    · exact Ne.symm hwho

/-- Two-step evaluation when the updated second row absorbs surely. -/
theorem hazardTerminalValue_eq_twoStagePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool)
    (hmass : quittingStationaryContinueMass
      (Function.update (roots 1) who (hazard 1)) = 0) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 =
      twoStagePayoff reward
        (Function.update (roots 0) who (hazard 0))
        (Function.update (roots 1) who (hazard 1)) who := by
  rw [quittingRootSequenceHazardTerminalValue_eq_rootExpectedPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  rw [quittingRootSequenceHazardTerminalValue_eq_rootExpectedPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add, hmass]
  simp [twoStagePayoff]

omit [DecidableEq ι] in
/-- A prescribed root sequence also reduces to two rows when the second row absorbs surely. -/
theorem terminalValue_eq_twoStagePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hmass : quittingStationaryContinueMass (roots 1) = 0) :
    quittingRootSequenceTerminalValue reward roots who 0 =
      twoStagePayoff reward (roots 0) (roots 1) who := by
  rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add, hmass]
  simp [twoStagePayoff]

/-- The live root sequence of the literal history-independent profile is its declared sequence. -/
theorem profileLiveRoot_eq_roots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1) :
    quittingProfileLiveRoot reward (roles.profile reward p) = roles.roots p := by
  funext time player
  simp [quittingProfileLiveRoot, profile, quittingRootSequenceProfile]

/-- The literal profile's terminal payoff is the displayed two-stage payoff. -/
theorem terminalPayoff_profile_eq_prescribedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (who : ι) :
    quittingTerminalPayoff reward (roles.profile reward p) who =
      roles.prescribedPayoff reward p who := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    profileLiveRoot_eq_roots]
  apply terminalValue_eq_twoStagePayoff
  apply continueMass_eq_zero_of_sureQuitter (quitter := roles.firstB)
  simp [roots, secondRoot]

/-- Every deterministic quit time collapses to one of the three displayed ports. -/
def portOfQuitTime : Option ℕ → PurePort
  | some 0 => .firstGate
  | some 1 => .secondGate
  | _ => .never

/-- Pure-time deviations against the literal profile have exactly their displayed port payoff. -/
theorem pureTimeTerminalPayoff_eq_purePortPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (who : ι) (quitTime : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update (roles.profile reward p) who
          (quittingPureTimeBehaviorStrategy reward who quitTime)) who =
      roles.purePortPayoff reward p who (portOfQuitTime quitTime) := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    profileLiveRoot_eq_roots]
  apply Eq.trans (hazardTerminalValue_eq_twoStagePayoff reward
    (roles.roots p) who (quittingPureTimeHazard quitTime) (by
      apply secondRoot_update_continueMass_eq_zero))
  cases quitTime with
  | none => simp [roots, portOfQuitTime, purePortPayoff, portRoots]
  | some quitTime =>
      cases quitTime with
      | zero =>
          have hzero : quittingStationaryContinueMass
              (Function.update (roles.firstRoot p) who (PMF.pure true)) = 0 :=
            continueMass_eq_zero_of_sureQuitter (quitter := who) (by simp)
          simp [roots, portOfQuitTime, purePortPayoff, portRoots,
            quittingPureTimeHazard, twoStagePayoff, hzero]
      | succ quitTime =>
          cases quitTime with
          | zero => simp [roots, portOfQuitTime, purePortPayoff, portRoots,
              quittingPureTimeHazard]
          | succ quitTime => simp [roots, portOfQuitTime, purePortPayoff, portRoots,
              quittingPureTimeHazard]

/-- Finite exploitability of the literal gate.  The zero option records the prescribed strategy
itself, so the quantity is nonnegative without an attainment argument. -/
def exploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1) : ℝ :=
  Finset.univ.sup' ⟨roles.firstA, Finset.mem_univ _⟩ fun who =>
    max 0 (Finset.univ.sup' Finset.univ_nonempty fun port =>
      roles.purePortPayoff reward p who port - roles.prescribedPayoff reward p who)

/-- The unrestricted behavioral best response against the literal gate is the maximum of its
three pure ports. -/
theorem continuationBestResponseValue_eq_sup_purePortPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (who : ι) :
    quittingContinuationBestResponseValue reward (roles.profile reward p) who =
      Finset.univ.sup' Finset.univ_nonempty fun port =>
        roles.purePortPayoff reward p who port := by
  rw [quittingContinuationBestResponseValue,
    sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro _ ⟨quitTime, rfl⟩
      change quittingTerminalPayoff reward
        (Function.update (roles.profile reward p) who
          (quittingPureTimeBehaviorStrategy reward who quitTime)) who ≤ _
      rw [pureTimeTerminalPayoff_eq_purePortPayoff]
      exact Finset.le_sup' (fun port =>
        roles.purePortPayoff reward p who port) (Finset.mem_univ _)
  · apply Finset.sup'_le
    intro port _
    let quitTime : Option ℕ := match port with
      | .firstGate => some 0
      | .secondGate => some 1
      | .never => none
    have hport : portOfQuitTime quitTime = port := by
      cases port <;> rfl
    rw [← hport, ← pureTimeTerminalPayoff_eq_purePortPayoff]
    apply le_csSup
    · refine ⟨quittingRewardBound reward, ?_⟩
      rintro _ ⟨time, rfl⟩
      exact (le_abs_self _).trans
        (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ who)
    · exact ⟨quitTime, rfl⟩

/-- The finite three-port quantity is exactly literal unrestricted behavioral exploitability. -/
theorem terminalExploitability_eq_exploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1) :
    @quittingTerminalExploitability ι inferInstance inferInstance
        ⟨roles.firstA⟩ reward (roles.profile reward p) =
      roles.exploitability reward p := by
  unfold quittingTerminalExploitability QuittingBoundaryHolonomy.finitePlayerMax
    exploitability
  congr 1
  funext who
  rw [continuationBestResponseValue_eq_sup_purePortPayoff,
    terminalPayoff_profile_eq_prescribedPayoff]
  congr 1
  simpa only [sub_eq_add_neg] using Finset.sup'_add Finset.univ
    (fun port => roles.purePortPayoff reward p who port)
    (-roles.prescribedPayoff reward p who) Finset.univ_nonempty

theorem exploitability_eq_zero_of_purePort_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (noGain : ∀ who port,
      roles.purePortPayoff reward p who port ≤ roles.prescribedPayoff reward p who) :
    roles.exploitability reward p = 0 := by
  apply le_antisymm
  · unfold exploitability
    apply Finset.sup'_le
    intro who _
    rw [max_le_iff]
    constructor
    · exact le_rfl
    · apply Finset.sup'_le
      intro port _
      linarith [noGain who port]
  · unfold exploitability
    exact Finset.le_sup' (fun who =>
      max 0 (Finset.univ.sup' Finset.univ_nonempty fun port =>
        roles.purePortPayoff reward p who port - roles.prescribedPayoff reward p who))
      (Finset.mem_univ roles.firstA) |>.trans' (le_max_left _ _)

/-! ## Coordinatewise convergence of the selected two-stage law -/

/-- Exact before/gate/between/gate/after disintegration of one terminal-coalition coordinate.
The selected gate roots are conditional laws; the two reach equations expose the price of
moving them from their source dates to dates zero and one. -/
structure TwoGateCoalitionDecomposition where
  beforeTotal : ℝ
  betweenTotal : ℝ
  afterTotal : ℝ
  beforeCoalition : ℝ
  betweenCoalition : ℝ
  afterCoalition : ℝ
  firstReach : ℝ
  secondReach : ℝ
  firstMass : ℝ
  secondMass : ℝ
  firstContinue : ℝ
  actualMass : ℝ
  beforeTotal_nonneg : 0 ≤ beforeTotal
  betweenTotal_nonneg : 0 ≤ betweenTotal
  afterTotal_nonneg : 0 ≤ afterTotal
  beforeCoalition_nonneg : 0 ≤ beforeCoalition
  betweenCoalition_nonneg : 0 ≤ betweenCoalition
  afterCoalition_nonneg : 0 ≤ afterCoalition
  beforeCoalition_le : beforeCoalition ≤ beforeTotal
  betweenCoalition_le : betweenCoalition ≤ betweenTotal
  afterCoalition_le : afterCoalition ≤ afterTotal
  firstMass_mem : firstMass ∈ Set.Icc (0 : ℝ) 1
  secondMass_mem : secondMass ∈ Set.Icc (0 : ℝ) 1
  firstContinue_mem : firstContinue ∈ Set.Icc (0 : ℝ) 1
  firstReach_eq : firstReach = 1 - beforeTotal
  secondReach_eq : secondReach =
    (1 - beforeTotal) * firstContinue - betweenTotal
  actualMass_eq : actualMass = beforeCoalition + firstReach * firstMass +
    betweenCoalition + secondReach * secondMass + afterCoalition

theorem quittingRootCoalitionMass_mem_Icc
    (root : ι → PMF Bool) (coalition : Finset ι) (coalition_nonempty : coalition.Nonempty) :
    quittingRootCoalitionMass root coalition ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact quittingRootCoalitionMass_nonneg' root coalition
  · have hmem : coalition ∈
        (Finset.univ : Finset (Finset ι)).erase ∅ := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact Finset.nonempty_iff_ne_empty.mp coalition_nonempty
    have hle : quittingRootCoalitionMass root coalition ≤
        ∑ other ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
          quittingRootCoalitionMass root other :=
      Finset.single_le_sum
        (fun other _ => quittingRootCoalitionMass_nonneg' root other) hmem
    rw [quittingRootCoalitionMass_sum_nonempty] at hle
    exact hle.trans (sub_le_self 1 (quittingStationaryContinueMass_nonneg root))

/-- Every root sequence has a literal chronological coalition decomposition at any two distinct
selected dates.  This is the source-native disintegration consumed by the changed-reach bound. -/
def sourceNativeTwoGateCoalitionDecomposition
    (roots : ℕ → ι → PMF Bool) (coalition : Finset ι)
    (coalition_nonempty : coalition.Nonempty)
    (first second : ℕ) (first_lt_second : first < second) :
    TwoGateCoalitionDecomposition where
  beforeTotal := 1 - quittingJointSurvivalWeight roots 0 first
  betweenTotal := quittingJointSurvivalWeight roots 0 (first + 1) -
    quittingJointSurvivalWeight roots 0 second
  afterTotal := quittingJointSurvivalWeight roots 0 (second + 1)
  beforeCoalition := ∑ time ∈ Finset.range first,
    rootSequenceStageCoalitionMass roots time coalition
  betweenCoalition := ∑ time ∈ Finset.Ico (first + 1) second,
    rootSequenceStageCoalitionMass roots time coalition
  afterCoalition := ∑' offset,
    rootSequenceStageCoalitionMass roots (second + 1 + offset) coalition
  firstReach := quittingJointSurvivalWeight roots 0 first
  secondReach := quittingJointSurvivalWeight roots 0 second
  firstMass := quittingRootCoalitionMass (roots first) coalition
  secondMass := quittingRootCoalitionMass (roots second) coalition
  firstContinue := quittingStationaryContinueMass (roots first)
  actualMass := rootSequenceTerminalCoalitionMass roots coalition
  beforeTotal_nonneg := sub_nonneg.mpr
    (quittingJointSurvivalWeight_le_one roots 0 first)
  betweenTotal_nonneg := sub_nonneg.mpr
    (antitone_quittingJointSurvivalWeight roots 0
      (Nat.succ_le_iff.mpr first_lt_second))
  afterTotal_nonneg := quittingJointSurvivalWeight_nonneg roots 0 (second + 1)
  beforeCoalition_nonneg := Finset.sum_nonneg fun time _ =>
    rootSequenceStageCoalitionMass_nonneg roots time coalition
  betweenCoalition_nonneg := Finset.sum_nonneg fun time _ =>
    rootSequenceStageCoalitionMass_nonneg roots time coalition
  afterCoalition_nonneg := tsum_nonneg fun offset =>
    rootSequenceStageCoalitionMass_nonneg roots (second + 1 + offset) coalition
  beforeCoalition_le := by
    rw [← sum_range_rootSequenceStageAbsorptionMass roots first]
    exact Finset.sum_le_sum fun time _ =>
      rootSequenceStageCoalitionMass_le_absorptionMass
        roots time coalition coalition_nonempty
  betweenCoalition_le := by
    rw [← sum_Ico_rootSequenceStageAbsorptionMass roots (first + 1) second
      (Nat.succ_le_iff.mpr first_lt_second)]
    exact Finset.sum_le_sum fun time _ =>
      rootSequenceStageCoalitionMass_le_absorptionMass
        roots time coalition coalition_nonempty
  afterCoalition_le :=
    tail_rootSequenceStageCoalitionMass_le_survival
      roots coalition coalition_nonempty (second + 1)
  firstMass_mem := quittingRootCoalitionMass_mem_Icc
    (roots first) coalition coalition_nonempty
  secondMass_mem := quittingRootCoalitionMass_mem_Icc
    (roots second) coalition coalition_nonempty
  firstContinue_mem := ⟨quittingStationaryContinueMass_nonneg (roots first),
    quittingStationaryContinueMass_le_one (roots first)⟩
  firstReach_eq := by ring
  secondReach_eq := by
    rw [quittingJointSurvivalWeight_succ]
    simp only [Nat.zero_add]
    ring
  actualMass_eq := by
    rw [rootSequenceTerminalCoalitionMass_eq_split_two_dates
      roots coalition coalition_nonempty first second first_lt_second]
    simp only [rootSequenceStageCoalitionMass]

namespace TwoGateCoalitionDecomposition

/-- A chronological disintegration bounds one coalition's law error by twice the total
counterfactual absorption outside the selected gates, plus the surviving after-tail. -/
theorem abs_actualMass_sub_twoStage_le (data : TwoGateCoalitionDecomposition) :
    |data.actualMass -
        (data.firstMass + data.firstContinue * data.secondMass)| ≤
      2 * (data.beforeTotal + data.betweenTotal) + data.afterTotal := by
  rw [data.actualMass_eq, data.firstReach_eq, data.secondReach_eq]
  have hbeforeMass : data.beforeTotal * data.firstMass ≤ data.beforeTotal := by
    nlinarith [mul_nonneg data.beforeTotal_nonneg data.firstMass_mem.1,
      mul_le_mul_of_nonneg_left data.firstMass_mem.2 data.beforeTotal_nonneg]
  have hbeforeMass_nonneg : 0 ≤ data.beforeTotal * data.firstMass :=
    mul_nonneg data.beforeTotal_nonneg data.firstMass_mem.1
  have hbeforeContinue :
      data.beforeTotal * data.firstContinue ≤ data.beforeTotal := by
    nlinarith [mul_nonneg data.beforeTotal_nonneg data.firstContinue_mem.1,
      mul_le_mul_of_nonneg_left data.firstContinue_mem.2 data.beforeTotal_nonneg]
  have hsecondLoss :
      (data.beforeTotal * data.firstContinue + data.betweenTotal) *
          data.secondMass ≤ data.beforeTotal + data.betweenTotal := by
    have hcoefficient : 0 ≤
        data.beforeTotal * data.firstContinue + data.betweenTotal :=
      add_nonneg (mul_nonneg data.beforeTotal_nonneg data.firstContinue_mem.1)
        data.betweenTotal_nonneg
    calc
      (data.beforeTotal * data.firstContinue + data.betweenTotal) *
          data.secondMass ≤
          data.beforeTotal * data.firstContinue + data.betweenTotal := by
        simpa using mul_le_mul_of_nonneg_left data.secondMass_mem.2 hcoefficient
      _ ≤ data.beforeTotal + data.betweenTotal := by linarith
  have hsecondLoss_nonneg : 0 ≤
      (data.beforeTotal * data.firstContinue + data.betweenTotal) *
        data.secondMass :=
    mul_nonneg
      (add_nonneg (mul_nonneg data.beforeTotal_nonneg data.firstContinue_mem.1)
        data.betweenTotal_nonneg)
      data.secondMass_mem.1
  have houtside : data.beforeCoalition + data.betweenCoalition +
      data.afterCoalition ≤
        data.beforeTotal + data.betweenTotal + data.afterTotal := by
    linarith [data.beforeCoalition_le, data.betweenCoalition_le,
      data.afterCoalition_le]
  have houtside_nonneg : 0 ≤
      data.beforeCoalition + data.betweenCoalition + data.afterCoalition := by
    exact add_nonneg (add_nonneg data.beforeCoalition_nonneg
      data.betweenCoalition_nonneg) data.afterCoalition_nonneg
  have hbeforeTotal_nonneg := data.beforeTotal_nonneg
  have hbetweenTotal_nonneg := data.betweenTotal_nonneg
  have hafterTotal_nonneg := data.afterTotal_nonneg
  have hrewrite :
      data.beforeCoalition + (1 - data.beforeTotal) * data.firstMass +
            data.betweenCoalition +
            ((1 - data.beforeTotal) * data.firstContinue - data.betweenTotal) *
              data.secondMass + data.afterCoalition -
          (data.firstMass + data.firstContinue * data.secondMass) =
        data.beforeCoalition + data.betweenCoalition + data.afterCoalition -
          data.beforeTotal * data.firstMass -
          (data.beforeTotal * data.firstContinue + data.betweenTotal) *
            data.secondMass := by
    ring
  rw [hrewrite]
  rw [abs_le]
  constructor <;> linarith

end TwoGateCoalitionDecomposition

/-- The finite deleted-clock calculation supplies the outside-absorption term in the
chronological coalition comparison.  In particular, no coalition-law closeness estimate is an
input to this theorem. -/
theorem twoGateCoalition_abs_sub_le_of_changedReach
    {Player : Type*} [DecidableEq Player]
    (before between : Finset ℕ) (players : Finset Player)
    (hazard : ℕ → Player → ℝ) (who : Player) (who_mem : who ∈ players)
    (hazard_mem : ∀ time ∈ before ∪ between, ∀ player ∈ players,
      hazard time player ∈ Set.Icc (0 : ℝ) 1)
    (data : TwoGateCoalitionDecomposition)
    {betweenBaselineReach beforeAbsorption betweenAbsorption reachFloor : ℝ}
    (betweenBaselineReach_ge : reachFloor ≤ betweenBaselineReach)
    (reachFloor_pos : 0 < reachFloor)
    (firstReach_mem : data.firstReach ∈ Set.Icc (0 : ℝ) 1)
    (beforeAbsorption_eq : beforeAbsorption =
      1 * (1 - Math.Probability.finiteJointContinueClock before players hazard))
    (betweenAbsorption_eq : betweenAbsorption = betweenBaselineReach *
      (1 - Math.Probability.finiteJointContinueClock between players hazard))
    (changedBefore_eq : data.beforeTotal = 1 *
      (1 - Math.Probability.finiteDeletedContinueClock before players hazard who))
    (changedBetween_eq : data.betweenTotal = data.firstReach * data.firstContinue *
      (1 - Math.Probability.finiteDeletedContinueClock between players hazard who)) :
    |data.actualMass -
        (data.firstMass + data.firstContinue * data.secondMass)| ≤
      2 * (beforeAbsorption + betweenAbsorption / reachFloor) + data.afterTotal := by
  have hchangedBetween_mem : data.firstReach * data.firstContinue ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg firstReach_mem.1 data.firstContinue_mem.1
    · have hle := mul_le_mul_of_nonneg_left data.firstContinue_mem.2 firstReach_mem.1
      nlinarith [firstReach_mem.2]
  have houtside := Math.Probability.finiteClock_twoWindowDeletedAbsorption_le
    before between players hazard who who_mem hazard_mem
    betweenBaselineReach_ge reachFloor_pos
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) hchangedBetween_mem
    beforeAbsorption_eq betweenAbsorption_eq
  rw [← changedBefore_eq, ← changedBetween_eq] at houtside
  exact (data.abs_actualMass_sub_twoStage_le).trans (by
    linarith [data.afterTotal_nonneg])

theorem quittingRootCoalitionMass_tendsto
    {roots : ℕ → ι → PMF Bool} {root : ι → PMF Bool}
    (coordinate : ∀ player,
      Tendsto (fun n => (roots n player true).toReal) atTop
        (nhds ((root player true).toReal)))
    (coalition : Finset ι) :
    Tendsto (fun n => quittingRootCoalitionMass (roots n) coalition) atTop
      (nhds (quittingRootCoalitionMass root coalition)) := by
  unfold quittingRootCoalitionMass quittingRootQuitRates Math.PMFProduct.coalitionMass
  apply Tendsto.mul
  · apply tendsto_finsetProd
    intro player hplayer
    exact coordinate player
  · apply tendsto_finsetProd
    intro player hplayer
    exact tendsto_const_nhds.sub (coordinate player)

omit [DecidableEq ι] in
theorem quittingStationaryContinueMass_tendsto
    {roots : ℕ → ι → PMF Bool} {root : ι → PMF Bool}
    (coordinate : ∀ player,
      Tendsto (fun n => (roots n player true).toReal) atTop
        (nhds ((root player true).toReal))) :
    Tendsto (fun n => quittingStationaryContinueMass (roots n)) atTop
      (nhds (quittingStationaryContinueMass root)) := by
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    pmfBool_false_toReal]
  apply tendsto_finsetProd
  intro player _
  exact tendsto_const_nhds.sub (coordinate player)

theorem source_after_tendsto_zero
    (roles : QuittingTwoPairGateRoles ι)
    (source : ℕ → ℕ → ι → PMF Bool) (second : ℕ → ℕ)
    (secondCoordinate : ∀ player,
      Tendsto (fun n => (source n (second n) player true).toReal) atTop
        (nhds ((roles.secondRoot player true).toReal))) :
    Tendsto (fun n => quittingJointSurvivalWeight (source n) 0 (second n + 1))
      atTop (nhds 0) := by
  have hcontinue := quittingStationaryContinueMass_tendsto secondCoordinate
  rw [roles.secondRoot_continueMass_eq_zero] at hcontinue
  apply squeeze_zero
  · intro n
    exact quittingJointSurvivalWeight_nonneg _ 0 (second n + 1)
  · intro n
    show quittingJointSurvivalWeight (source n) 0 (second n + 1) ≤
      quittingStationaryContinueMass (source n (second n))
    rw [quittingJointSurvivalWeight_succ]
    simp only [Nat.zero_add]
    exact mul_le_of_le_one_left
      (quittingStationaryContinueMass_nonneg (source n (second n)))
      (quittingJointSurvivalWeight_le_one (source n) 0 (second n))
  · exact hcontinue

theorem sourcePort_after_tendsto_zero
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (source : ℕ → ℕ → ι → PMF Bool) (first second : ℕ → ℕ)
    (first_lt_second : ∀ n, first n < second n)
    (secondCoordinate : ∀ player,
      Tendsto (fun n => (source n (second n) player true).toReal) atTop
        (nhds ((roles.secondRoot player true).toReal)))
    (who : ι) (port : PurePort) :
    Tendsto (fun n => quittingJointSurvivalWeight
      (sourcePortRootSequence (source n) who (first n) (second n) port)
        0 (second n + 1)) atTop (nhds 0) := by
  have hcontinue := quittingStationaryContinueMass_tendsto
    (fun player => sourcePortRootSequence_secondRoot_tendsto
      roles p source first second first_lt_second secondCoordinate who player port)
  rw [roles.portRoots_second_continueMass_eq_zero p who port] at hcontinue
  apply squeeze_zero
  · intro n
    exact quittingJointSurvivalWeight_nonneg _ 0 (second n + 1)
  · intro n
    show quittingJointSurvivalWeight
        (sourcePortRootSequence (source n) who (first n) (second n) port)
          0 (second n + 1) ≤
      quittingStationaryContinueMass
        (sourcePortRootSequence (source n) who (first n) (second n) port (second n))
    rw [quittingJointSurvivalWeight_succ]
    simp only [Nat.zero_add]
    exact mul_le_of_le_one_left
      (quittingStationaryContinueMass_nonneg
        (sourcePortRootSequence (source n) who (first n) (second n) port (second n)))
      (quittingJointSurvivalWeight_le_one
        (sourcePortRootSequence (source n) who (first n) (second n) port)
        0 (second n))
  · exact hcontinue

theorem twoStageCoalitionMass_tendsto
    {firstRoots secondRoots : ℕ → ι → PMF Bool}
    {firstRoot secondRoot : ι → PMF Bool}
    (firstCoordinate : ∀ player,
      Tendsto (fun n => (firstRoots n player true).toReal) atTop
        (nhds ((firstRoot player true).toReal)))
    (secondCoordinate : ∀ player,
      Tendsto (fun n => (secondRoots n player true).toReal) atTop
        (nhds ((secondRoot player true).toReal)))
    (coalition : Finset ι) :
    Tendsto (fun n =>
      twoStageCoalitionMass (firstRoots n) (secondRoots n) coalition) atTop
      (nhds (twoStageCoalitionMass firstRoot secondRoot coalition)) := by
  exact (quittingRootCoalitionMass_tendsto firstCoordinate coalition).add
    ((quittingStationaryContinueMass_tendsto firstCoordinate).mul
      (quittingRootCoalitionMass_tendsto secondCoordinate coalition))

/-- Terminal-coalition convergence from the literal chronological disintegration.  Unlike a
black-box law-comparison hypothesis, the input records the before/between/after atoms and the
two selected source reaches separately. -/
theorem terminalCoalitionMass_tendsto_of_chronologicalDecomposition
    {firstRoots secondRoots : ℕ → ι → PMF Bool}
    {firstRoot secondRoot : ι → PMF Bool}
    (firstCoordinate : ∀ player,
      Tendsto (fun n => (firstRoots n player true).toReal) atTop
        (nhds ((firstRoot player true).toReal)))
    (secondCoordinate : ∀ player,
      Tendsto (fun n => (secondRoots n player true).toReal) atTop
        (nhds ((secondRoot player true).toReal)))
    (actualMass : ℕ → Finset ι → ℝ)
    (beforeError betweenError afterError : ℕ → ℝ)
    (before_tendsto : Tendsto beforeError atTop (nhds 0))
    (between_tendsto : Tendsto betweenError atTop (nhds 0))
    (after_tendsto : Tendsto afterError atTop (nhds 0))
    (data : ∀ _n _coalition, TwoGateCoalitionDecomposition)
    (actual_eq : ∀ n coalition, (data n coalition).actualMass = actualMass n coalition)
    (firstMass_eq : ∀ n coalition, (data n coalition).firstMass =
      quittingRootCoalitionMass (firstRoots n) coalition)
    (secondMass_eq : ∀ n coalition, (data n coalition).secondMass =
      quittingRootCoalitionMass (secondRoots n) coalition)
    (firstContinue_eq : ∀ n coalition, (data n coalition).firstContinue =
      quittingStationaryContinueMass (firstRoots n))
    (before_le : ∀ n coalition, (data n coalition).beforeTotal ≤ beforeError n)
    (between_le : ∀ n coalition, (data n coalition).betweenTotal ≤ betweenError n)
    (after_le : ∀ n coalition, (data n coalition).afterTotal ≤ afterError n)
    (coalition : Finset ι) :
    Tendsto (fun n => actualMass n coalition) atTop
      (nhds (twoStageCoalitionMass firstRoot secondRoot coalition)) := by
  have hbound : Tendsto (fun n =>
      2 * (beforeError n + betweenError n) + afterError n) atTop (nhds 0) := by
    simpa using ((before_tendsto.add between_tendsto).const_mul 2).add after_tendsto
  have hdifference : Tendsto (fun n =>
      actualMass n coalition -
        twoStageCoalitionMass (firstRoots n) (secondRoots n) coalition) atTop (nhds 0) := by
    apply Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _ hbound
    exact Filter.Eventually.of_forall fun n => by
      have h := (data n coalition).abs_actualMass_sub_twoStage_le
      rw [actual_eq, firstMass_eq, secondMass_eq, firstContinue_eq] at h
      exact h.trans (by
        linarith [before_le n coalition, between_le n coalition,
          after_le n coalition])
  have htwoStage := twoStageCoalitionMass_tendsto
    firstCoordinate secondCoordinate coalition
  convert hdifference.add htwoStage using 1 <;> simp

/-- Source-native specialization: selected root convergence and vanishing actual absorption
outside the two dates force convergence of the infinite first-absorption law. -/
theorem rootSequenceTerminalCoalitionMass_tendsto_of_two_dates
    (source : ℕ → ℕ → ι → PMF Bool)
    (first second : ℕ → ℕ) (first_lt_second : ∀ n, first n < second n)
    {firstRoot secondRoot : ι → PMF Bool}
    (firstCoordinate : ∀ player,
      Tendsto (fun n => (source n (first n) player true).toReal) atTop
        (nhds ((firstRoot player true).toReal)))
    (secondCoordinate : ∀ player,
      Tendsto (fun n => (source n (second n) player true).toReal) atTop
        (nhds ((secondRoot player true).toReal)))
    (before_tendsto : Tendsto (fun n =>
      1 - quittingJointSurvivalWeight (source n) 0 (first n)) atTop (nhds 0))
    (between_tendsto : Tendsto (fun n =>
      quittingJointSurvivalWeight (source n) 0 (first n + 1) -
        quittingJointSurvivalWeight (source n) 0 (second n)) atTop (nhds 0))
    (after_tendsto : Tendsto (fun n =>
      quittingJointSurvivalWeight (source n) 0 (second n + 1)) atTop (nhds 0))
    (coalition : Finset ι) (coalition_nonempty : coalition.Nonempty) :
    Tendsto (fun n => rootSequenceTerminalCoalitionMass (source n) coalition) atTop
      (nhds (twoStageCoalitionMass firstRoot secondRoot coalition)) := by
  let data : ∀ n, TwoGateCoalitionDecomposition := fun n =>
    sourceNativeTwoGateCoalitionDecomposition (source n) coalition coalition_nonempty
      (first n) (second n) (first_lt_second n)
  have hbound : Tendsto (fun n =>
      2 * ((1 - quittingJointSurvivalWeight (source n) 0 (first n)) +
        (quittingJointSurvivalWeight (source n) 0 (first n + 1) -
          quittingJointSurvivalWeight (source n) 0 (second n))) +
        quittingJointSurvivalWeight (source n) 0 (second n + 1))
      atTop (nhds 0) := by
    simpa using ((before_tendsto.add between_tendsto).const_mul 2).add after_tendsto
  have hdifference : Tendsto (fun n =>
      rootSequenceTerminalCoalitionMass (source n) coalition -
        twoStageCoalitionMass (source n (first n)) (source n (second n)) coalition)
      atTop (nhds 0) := by
    apply Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _ hbound
    exact Filter.Eventually.of_forall fun n => by
      simpa [data, sourceNativeTwoGateCoalitionDecomposition,
        twoStageCoalitionMass] using
        (data n).abs_actualMass_sub_twoStage_le
  have htwoStage := twoStageCoalitionMass_tendsto
    firstCoordinate secondCoordinate coalition
  convert hdifference.add htwoStage using 1 <;> simp

/-- Source-native changed-reach version of terminal-law convergence.  The outside-law estimate
is proved here from the deleted finite clocks and the exact chronological decomposition. -/
theorem terminalCoalitionMass_tendsto_of_changedReachClock
    {firstRoots secondRoots : ℕ → ι → PMF Bool}
    {firstRoot secondRoot : ι → PMF Bool}
    (firstCoordinate : ∀ player,
      Tendsto (fun n => (firstRoots n player true).toReal) atTop
        (nhds ((firstRoot player true).toReal)))
    (secondCoordinate : ∀ player,
      Tendsto (fun n => (secondRoots n player true).toReal) atTop
        (nhds ((secondRoot player true).toReal)))
    (who : ι) (before between : ℕ → Finset ℕ)
    (hazard : ℕ → ℕ → ι → ℝ)
    (hazard_mem : ∀ n, ∀ time ∈ before n ∪ between n,
      ∀ player ∈ (Finset.univ : Finset ι),
        hazard n time player ∈ Set.Icc (0 : ℝ) 1)
    (actualMass : ℕ → Finset ι → ℝ)
    (data : ∀ _n _coalition, TwoGateCoalitionDecomposition)
    (actual_eq : ∀ n coalition, (data n coalition).actualMass = actualMass n coalition)
    (firstMass_eq : ∀ n coalition, (data n coalition).firstMass =
      quittingRootCoalitionMass (firstRoots n) coalition)
    (secondMass_eq : ∀ n coalition, (data n coalition).secondMass =
      quittingRootCoalitionMass (secondRoots n) coalition)
    (firstContinue_eq : ∀ n coalition, (data n coalition).firstContinue =
      quittingStationaryContinueMass (firstRoots n))
    (betweenBaselineReach beforeAbsorption betweenAbsorption afterError : ℕ → ℝ)
    (reachFloor : ℝ) (reachFloor_pos : 0 < reachFloor)
    (betweenBaselineReach_ge : ∀ n, reachFloor ≤ betweenBaselineReach n)
    (firstReach_mem : ∀ n coalition,
      (data n coalition).firstReach ∈ Set.Icc (0 : ℝ) 1)
    (beforeAbsorption_eq : ∀ n, beforeAbsorption n = 1 *
      (1 - Math.Probability.finiteJointContinueClock (before n) Finset.univ
        (hazard n)))
    (betweenAbsorption_eq : ∀ n, betweenAbsorption n = betweenBaselineReach n *
      (1 - Math.Probability.finiteJointContinueClock (between n) Finset.univ
        (hazard n)))
    (changedBefore_eq : ∀ n coalition, (data n coalition).beforeTotal = 1 *
        (1 - Math.Probability.finiteDeletedContinueClock
          (before n) Finset.univ (hazard n) who))
    (changedBetween_eq : ∀ n coalition, (data n coalition).betweenTotal =
      (data n coalition).firstReach * (data n coalition).firstContinue *
        (1 - Math.Probability.finiteDeletedContinueClock
          (between n) Finset.univ (hazard n) who))
    (after_le : ∀ n coalition, (data n coalition).afterTotal ≤ afterError n)
    (before_tendsto : Tendsto beforeAbsorption atTop (nhds 0))
    (between_tendsto : Tendsto betweenAbsorption atTop (nhds 0))
    (after_tendsto : Tendsto afterError atTop (nhds 0))
    (coalition : Finset ι) :
    Tendsto (fun n => actualMass n coalition) atTop
      (nhds (twoStageCoalitionMass firstRoot secondRoot coalition)) := by
  have hbound : Tendsto (fun n =>
      2 * (beforeAbsorption n + betweenAbsorption n / reachFloor) +
        afterError n) atTop (nhds 0) := by
    simpa using
      ((before_tendsto.add (between_tendsto.div_const reachFloor)).const_mul 2).add
        after_tendsto
  have hdifference : Tendsto (fun n => actualMass n coalition -
      twoStageCoalitionMass (firstRoots n) (secondRoots n) coalition)
      atTop (nhds 0) := by
    apply Math.tendsto_zero_of_abs_le_of_tendsto_zero _ _ hbound
    exact Filter.Eventually.of_forall fun n => by
      have h := twoGateCoalition_abs_sub_le_of_changedReach
        (before n) (between n) (Finset.univ : Finset ι) (hazard n) who
        (Finset.mem_univ who) (hazard_mem n) (data n coalition)
        (betweenBaselineReach_ge n) reachFloor_pos
        (firstReach_mem n coalition)
        (beforeAbsorption_eq n) (betweenAbsorption_eq n)
        (changedBefore_eq n coalition) (changedBetween_eq n coalition)
      rw [actual_eq, firstMass_eq, secondMass_eq, firstContinue_eq] at h
      exact h.trans (by linarith [after_le n coalition])
  have htwoStage := twoStageCoalitionMass_tendsto
    firstCoordinate secondCoordinate coalition
  convert hdifference.add htwoStage using 1 <;> simp

omit [DecidableEq ι] in
/-- Coordinatewise convergence of a finite terminal-coalition law implies convergence of every
payoff coordinate. -/
theorem coalitionLawPayoff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {mass : ℕ → Finset ι → ℝ} {limitMass : Finset ι → ℝ}
    (mass_tendsto : ∀ coalition, coalition.Nonempty →
      Tendsto (fun n => mass n coalition) atTop (nhds (limitMass coalition)))
    (who : ι) :
    Tendsto (fun n => coalitionLawPayoff reward (mass n) who) atTop
      (nhds (coalitionLawPayoff reward limitMass who)) := by
  unfold coalitionLawPayoff
  apply tendsto_finsetSum
  intro terminal _
  exact (mass_tendsto terminal.val terminal.property).mul_const (reward terminal who)

/-! ## Conditional strategic endpoint -/

/-- Boundary-zero consumer after the clock producer and source-matched payoff transport have been
supplied.  It is deliberately stated with those convergence hypotheses explicit. -/
theorem exploitability_eq_zero_of_sourceMatched_limit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (sourcePrescribed : ℕ → ι → ℝ)
    (sourcePort : ℕ → ι → PurePort → ℝ) (error : ℕ → ℝ)
    (error_tendsto : Tendsto error atTop (nhds 0))
    (source_nash : ∀ n who port,
      sourcePort n who port - sourcePrescribed n who ≤ error n)
    (prescribed_tendsto : ∀ who,
      Tendsto (fun n => sourcePrescribed n who) atTop
        (nhds (roles.prescribedPayoff reward p who)))
    (port_tendsto : ∀ who port,
      Tendsto (fun n => sourcePort n who port) atTop
        (nhds (roles.purePortPayoff reward p who port))) :
    roles.exploitability reward p = 0 := by
  apply exploitability_eq_zero_of_purePort_le
  intro who port
  have hlimit := (port_tendsto who port).sub (prescribed_tendsto who)
  have hgap : roles.purePortPayoff reward p who port -
      roles.prescribedPayoff reward p who ≤ 0 := by
    have hnonpos := le_of_tendsto' (hlimit.sub error_tendsto) (fun n =>
      show sourcePort n who port - sourcePrescribed n who - error n ≤ 0 by
        linarith [source_nash n who port])
    simpa using hnonpos
  linarith

/-- Full source-matched finite-law endpoint.  The only strategic input is the source Nash
inequality; payoff convergence is derived from convergence of every terminal-coalition weight. -/
theorem terminalExploitability_eq_zero_of_sourceMatched_coalitionLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (sourcePrescribedMass : ℕ → Finset ι → ℝ)
    (sourcePortMass : ℕ → ι → PurePort → Finset ι → ℝ)
    (error : ℕ → ℝ)
    (error_tendsto : Tendsto error atTop (nhds 0))
    (source_nash : ∀ n who port,
      coalitionLawPayoff reward (sourcePortMass n who port) who -
          coalitionLawPayoff reward (sourcePrescribedMass n) who ≤ error n)
    (prescribedMass_tendsto : ∀ coalition, coalition.Nonempty →
      Tendsto (fun n => sourcePrescribedMass n coalition) atTop
        (nhds (roles.coalitionMass p coalition)))
    (portMass_tendsto : ∀ who port coalition, coalition.Nonempty →
      Tendsto (fun n => sourcePortMass n who port coalition) atTop
        (nhds (twoStageCoalitionMass (roles.portRoots p who port).1
          (roles.portRoots p who port).2 coalition))) :
    @quittingTerminalExploitability ι inferInstance inferInstance
        ⟨roles.firstA⟩ reward (roles.profile reward p) = 0 := by
  rw [terminalExploitability_eq_exploitability]
  apply exploitability_eq_zero_of_sourceMatched_limit reward roles p
    (fun n who => coalitionLawPayoff reward (sourcePrescribedMass n) who)
    (fun n who port => coalitionLawPayoff reward (sourcePortMass n who port) who)
    error error_tendsto source_nash
  · intro who
    have h := coalitionLawPayoff_tendsto reward prescribedMass_tendsto who
    change Tendsto (fun n => coalitionLawPayoff reward (sourcePrescribedMass n) who)
      atTop (nhds (coalitionLawPayoff reward
        (twoStageCoalitionMass (roles.firstRoot p) roles.secondRoot) who)) at h
    rw [← twoStagePayoff_eq_coalitionLawPayoff] at h
    exact h
  · intro who port
    have h := coalitionLawPayoff_tendsto reward
      (portMass_tendsto who port) who
    rw [← twoStagePayoff_eq_coalitionLawPayoff] at h
    exact h

/-- Literal source-root endpoint.  No payoff or terminal-law comparison is supplied: both are
derived from the actual infinite root sequences and their before/between/after survival bounds.
The remaining producer obligations are precisely those survival bounds and source Nash. -/
theorem terminalExploitability_eq_zero_of_sourceRootChronology
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (source : ℕ → ℕ → ι → PMF Bool)
    (first second : ℕ → ℕ) (first_lt_second : ∀ n, first n < second n)
    (error : ℕ → ℝ) (error_tendsto : Tendsto error atTop (nhds 0))
    (source_nash : ∀ n who port,
      quittingRootSequenceTerminalValue reward
          (sourcePortRootSequence (source n) who (first n) (second n) port) who 0 -
        quittingRootSequenceTerminalValue reward (source n) who 0 ≤ error n)
    (firstCoordinate : ∀ player,
      Tendsto (fun n => (source n (first n) player true).toReal) atTop
        (nhds ((roles.firstRoot p player true).toReal)))
    (secondCoordinate : ∀ player,
      Tendsto (fun n => (source n (second n) player true).toReal) atTop
        (nhds ((roles.secondRoot player true).toReal)))
    (before_tendsto : Tendsto (fun n =>
      1 - quittingJointSurvivalWeight (source n) 0 (first n)) atTop (nhds 0))
    (between_tendsto : Tendsto (fun n =>
      quittingJointSurvivalWeight (source n) 0 (first n + 1) -
        quittingJointSurvivalWeight (source n) 0 (second n)) atTop (nhds 0))
    (after_tendsto : Tendsto (fun n =>
      quittingJointSurvivalWeight (source n) 0 (second n + 1)) atTop (nhds 0))
    (portBefore_tendsto : ∀ who port, Tendsto (fun n =>
      1 - quittingJointSurvivalWeight
        (sourcePortRootSequence (source n) who (first n) (second n) port)
          0 (first n)) atTop (nhds 0))
    (portBetween_tendsto : ∀ who port, Tendsto (fun n =>
      quittingJointSurvivalWeight
          (sourcePortRootSequence (source n) who (first n) (second n) port)
            0 (first n + 1) -
        quittingJointSurvivalWeight
          (sourcePortRootSequence (source n) who (first n) (second n) port)
            0 (second n)) atTop (nhds 0))
    (portAfter_tendsto : ∀ who port, Tendsto (fun n =>
      quittingJointSurvivalWeight
        (sourcePortRootSequence (source n) who (first n) (second n) port)
          0 (second n + 1)) atTop (nhds 0)) :
    @quittingTerminalExploitability ι inferInstance inferInstance
        ⟨roles.firstA⟩ reward (roles.profile reward p) = 0 := by
  apply terminalExploitability_eq_zero_of_sourceMatched_coalitionLaws
    reward roles p
    (fun n coalition => rootSequenceTerminalCoalitionMass (source n) coalition)
    (fun n who port coalition => rootSequenceTerminalCoalitionMass
      (sourcePortRootSequence (source n) who (first n) (second n) port) coalition)
    error error_tendsto
  · intro n who port
    simpa only [quittingRootSequenceTerminalValue_eq_coalitionLawPayoff] using
      source_nash n who port
  · intro coalition coalition_nonempty
    exact rootSequenceTerminalCoalitionMass_tendsto_of_two_dates
      source first second first_lt_second firstCoordinate secondCoordinate
      before_tendsto between_tendsto after_tendsto coalition coalition_nonempty
  · intro who port coalition coalition_nonempty
    exact rootSequenceTerminalCoalitionMass_tendsto_of_two_dates
      (fun n => sourcePortRootSequence (source n) who (first n) (second n) port)
      first second first_lt_second
      (fun player => sourcePortRootSequence_firstRoot_tendsto
        roles p source first second first_lt_second firstCoordinate who player port)
      (fun player => sourcePortRootSequence_secondRoot_tendsto
        roles p source first second first_lt_second secondCoordinate who player port)
      (portBefore_tendsto who port) (portBetween_tendsto who port)
      (portAfter_tendsto who port) coalition coalition_nonempty

/-- Counterfactual-free source endpoint.  Baseline defect concentration, a positive reach floor,
selected-root convergence, and source Nash automatically produce all three pure-port chronology
bounds through finite deleted-clock comparison and the surviving second-gate quitter. -/
theorem terminalExploitability_eq_zero_of_sourceRootClockConcentration
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (source : ℕ → ℕ → ι → PMF Bool)
    (first second : ℕ → ℕ) (first_lt_second : ∀ n, first n < second n)
    (error : ℕ → ℝ) (error_tendsto : Tendsto error atTop (nhds 0))
    (source_nash : ∀ n who port,
      quittingRootSequenceTerminalValue reward
          (sourcePortRootSequence (source n) who (first n) (second n) port) who 0 -
        quittingRootSequenceTerminalValue reward (source n) who 0 ≤ error n)
    (firstCoordinate : ∀ player,
      Tendsto (fun n => (source n (first n) player true).toReal) atTop
        (nhds ((roles.firstRoot p player true).toReal)))
    (secondCoordinate : ∀ player,
      Tendsto (fun n => (source n (second n) player true).toReal) atTop
        (nhds ((roles.secondRoot player true).toReal)))
    {reachFloor : ℝ} (reachFloor_pos : 0 < reachFloor)
    (sourceReach_ge : ∀ n,
      reachFloor ≤ quittingJointSurvivalWeight (source n) 0 (first n + 1))
    (before_tendsto : Tendsto (fun n =>
      1 - quittingJointSurvivalWeight (source n) 0 (first n)) atTop (nhds 0))
    (between_tendsto : Tendsto (fun n =>
      quittingJointSurvivalWeight (source n) 0 (first n + 1) -
        quittingJointSurvivalWeight (source n) 0 (second n)) atTop (nhds 0)) :
    @quittingTerminalExploitability ι inferInstance inferInstance
        ⟨roles.firstA⟩ reward (roles.profile reward p) = 0 := by
  apply terminalExploitability_eq_zero_of_sourceRootChronology
    reward roles p source first second first_lt_second error error_tendsto
    source_nash firstCoordinate secondCoordinate before_tendsto between_tendsto
    (source_after_tendsto_zero roles source second secondCoordinate)
  · intro who port
    exact sourcePort_before_tendsto_zero_of_source
      source first second first_lt_second before_tendsto who port
  · intro who port
    exact sourcePort_between_tendsto_zero_of_source
      source first second first_lt_second reachFloor_pos sourceReach_ge
      between_tendsto who port
  · intro who port
    exact sourcePort_after_tendsto_zero roles p source first second
      first_lt_second secondCoordinate who port

/-- End-to-end square-root-clock rigidity consumer.  Dominant-date chronology supplies the
baseline concentration and positive between-window reach needed by the source-native strategic
endpoint.  The theorem still assumes the reward-side source Nash producer. -/
theorem terminalExploitability_eq_zero_of_dominantSquareRootClock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roles : QuittingTwoPairGateRoles ι) (p : Set.Icc (0 : ℝ) 1)
    (source : ℕ → ℕ → ι → PMF Bool)
    (clock : ℕ → Math.Probability.TwoPairHazardClock)
    (horizon first second : ℕ → ℕ)
    (first_mem : ∀ n, first n ∈ Finset.range (horizon n))
    (second_mem : ∀ n, second n ∈ Finset.range (horizon n))
    (first_lt_second : ∀ n, first n < second n)
    (first_maximal : ∀ n time, time ∈ Finset.range (horizon n) →
      (clock n).firstTargetAmplitude time ≤ (clock n).firstTargetAmplitude (first n))
    (second_maximal : ∀ n time, time ∈ Finset.range (horizon n) →
      (clock n).secondTargetAmplitude time ≤ (clock n).secondTargetAmplitude (second n))
    (sourceSurvival_sq : ∀ n time,
      quittingJointSurvivalWeight (source n) 0 time = (clock n).survivalRoot time ^ 2)
    {targetFloor : ℝ} (targetFloor_pos : 0 < targetFloor)
    (secondTarget_ge : ∀ n,
      targetFloor ≤ (clock n).secondTargetAmplitude (second n))
    (delta_tendsto : Tendsto (fun n =>
      1 - Real.sqrt (∑ time ∈ Finset.range (horizon n),
          (clock n).firstTargetAmplitude time ^ 2) -
        Real.sqrt (∑ time ∈ Finset.range (horizon n),
          (clock n).secondTargetAmplitude time ^ 2)) atTop (nhds 0))
    (error : ℕ → ℝ) (error_tendsto : Tendsto error atTop (nhds 0))
    (source_nash : ∀ n who port,
      quittingRootSequenceTerminalValue reward
          (sourcePortRootSequence (source n) who (first n) (second n) port) who 0 -
        quittingRootSequenceTerminalValue reward (source n) who 0 ≤ error n)
    (firstCoordinate : ∀ player,
      Tendsto (fun n => (source n (first n) player true).toReal) atTop
        (nhds ((roles.firstRoot p player true).toReal)))
    (secondCoordinate : ∀ player,
      Tendsto (fun n => (source n (second n) player true).toReal) atTop
        (nhds ((roles.secondRoot player true).toReal))) :
    @quittingTerminalExploitability ι inferInstance inferInstance
        ⟨roles.firstA⟩ reward (roles.profile reward p) = 0 := by
  let delta : ℕ → ℝ := fun n =>
    1 - Real.sqrt (∑ time ∈ Finset.range (horizon n),
        (clock n).firstTargetAmplitude time ^ 2) -
      Real.sqrt (∑ time ∈ Finset.range (horizon n),
        (clock n).secondTargetAmplitude time ^ 2)
  have delta_zero : Tendsto delta atTop (nhds 0) := by
    simpa only [delta] using delta_tendsto
  have chronology : ∀ n,
      (∑ time ∈ Finset.range (first n),
          ((clock n).survivalRoot time ^ 2 -
            (clock n).survivalRoot (time + 1) ^ 2)) ≤ 10 * delta n ∧
        (∑ time ∈ Finset.Ico (first n + 1) (second n),
          ((clock n).survivalRoot time ^ 2 -
            (clock n).survivalRoot (time + 1) ^ 2)) ≤ 10 * delta n ∧
        (clock n).survivalRoot (second n + 1) ≤ 6 * delta n := by
    intro n
    simpa only [delta] using
      (Math.Probability.finite_twoTarget_dominant_chronology_bounds
        (clock n).firstTargetAmplitude (clock n).secondTargetAmplitude
        (clock n).survivalRoot (clock n).localDefect
        (horizon n) (first n) (second n) (first_mem n) (second_mem n)
        (first_lt_second n) (clock n).firstTargetAmplitude_nonneg
        (clock n).secondTargetAmplitude_nonneg (clock n).localDefect_nonneg
        (fun time _ => ⟨(clock n).survivalRoot_nonneg time,
          (clock n).survivalRoot_le_one time⟩)
        (clock n).survivalRoot_zero (fun time _ => (clock n).local_conservation time)
        (first_maximal n) (second_maximal n))
  have before_tendsto : Tendsto (fun n =>
      1 - quittingJointSurvivalWeight (source n) 0 (first n)) atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact sub_nonneg.mpr (quittingJointSurvivalWeight_le_one _ 0 (first n))
    · intro n
      show 1 - quittingJointSurvivalWeight (source n) 0 (first n) ≤ 10 * delta n
      rw [sourceSurvival_sq]
      have hsum := (chronology n).1
      rw [Finset.sum_range_sub'] at hsum
      rw [(clock n).survivalRoot_zero] at hsum
      norm_num at hsum
      linarith
    · simpa using delta_zero.const_mul 10
  have between_tendsto : Tendsto (fun n =>
      quittingJointSurvivalWeight (source n) 0 (first n + 1) -
        quittingJointSurvivalWeight (source n) 0 (second n)) atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact sub_nonneg.mpr (antitone_quittingJointSurvivalWeight (source n) 0
        (Nat.succ_le_iff.mpr (first_lt_second n)))
    · intro n
      show quittingJointSurvivalWeight (source n) 0 (first n + 1) -
          quittingJointSurvivalWeight (source n) 0 (second n) ≤ 10 * delta n
      rw [sourceSurvival_sq, sourceSurvival_sq]
      have hsum := (chronology n).2.1
      rw [Finset.sum_Ico_eq_sub _ (Nat.succ_le_iff.mpr (first_lt_second n)),
        Finset.sum_range_sub', Finset.sum_range_sub'] at hsum
      linarith
    · simpa using delta_zero.const_mul 10
  have sourceReach_ge : ∀ n,
      targetFloor ^ 2 ≤ quittingJointSurvivalWeight (source n) 0 (first n + 1) := by
    intro n
    have hsecond_le : (clock n).secondTargetAmplitude (second n) ≤
        (clock n).survivalRoot (second n) := by
      have hlocal := (clock n).local_conservation (second n)
      linarith [(clock n).firstTargetAmplitude_nonneg (second n),
        (clock n).localDefect_nonneg (second n),
        (clock n).survivalRoot_nonneg (second n + 1)]
    have hsqSecond : targetFloor ^ 2 ≤ (clock n).survivalRoot (second n) ^ 2 := by
      nlinarith [(clock n).survivalRoot_nonneg (second n), secondTarget_ge n]
    have hsqSecond' : targetFloor ^ 2 ≤
        quittingJointSurvivalWeight (source n) 0 (second n) := by
      rw [sourceSurvival_sq]
      exact hsqSecond
    exact hsqSecond'.trans (antitone_quittingJointSurvivalWeight (source n) 0
      (Nat.succ_le_iff.mpr (first_lt_second n)))
  exact terminalExploitability_eq_zero_of_sourceRootClockConcentration
    reward roles p source first second first_lt_second error error_tendsto
    source_nash firstCoordinate secondCoordinate (sq_pos_of_pos targetFloor_pos)
    sourceReach_ge before_tendsto between_tendsto

end QuittingTwoPairGateRoles

end GameTheory
