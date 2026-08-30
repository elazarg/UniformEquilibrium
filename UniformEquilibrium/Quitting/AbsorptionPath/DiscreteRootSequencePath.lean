/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ContinuousPath
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity

/-!
# Finite discrete absorption paths from quitting root sequences

A root sequence whose joint survival is exactly zero after a finite stage
defines a right-continuous absorption path.  The path clock is cumulative
absorption mass.  At a positive stage its value is the post-jump cumulative
mass, while its left value is the pre-jump cumulative mass.  Zero-absorption
dates are therefore collapsed without changing any mass coordinate.

This is a finite constructor.  It does not assert continuity, compactness,
path convergence, preservation of zero-mass chronology, or any equilibrium
property of the source roots.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Finset Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Survival clocks and cumulative coalition mass -/

/-- Probability of reaching stage `time` along the root sequence. -/
def quittingRootSequenceSurvival
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  quittingJointSurvivalWeight roots 0 time

/-- Cumulative absorption clock immediately before stage `time`. -/
def quittingRootSequenceClock
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  1 - quittingRootSequenceSurvival roots time

/-- Unconditional mass assigned to one coalition at one stage. -/
def quittingRootSequenceStageCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  quittingRootSequenceSurvival roots time *
    quittingRootCoalitionMass (roots time) coalition.1

/-- Coalition mass accumulated strictly before stage `time`. -/
def quittingRootSequenceCumulativeCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  ∑ stage ∈ Finset.range time,
    quittingRootSequenceStageCoalitionMass roots stage coalition

omit [DecidableEq ι] in
@[simp] theorem quittingRootSequenceSurvival_zero
    (roots : ℕ → ι → PMF Bool) :
    quittingRootSequenceSurvival roots 0 = 1 := by
  simp [quittingRootSequenceSurvival, quittingJointSurvivalWeight,
    quittingFiniteContinueWeight]

omit [DecidableEq ι] in
theorem quittingRootSequenceSurvival_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    0 ≤ quittingRootSequenceSurvival roots time :=
  quittingJointSurvivalWeight_nonneg roots 0 time

omit [DecidableEq ι] in
theorem quittingRootSequenceSurvival_le_one
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    quittingRootSequenceSurvival roots time ≤ 1 :=
  quittingJointSurvivalWeight_le_one roots 0 time

omit [DecidableEq ι] in
theorem antitone_quittingRootSequenceSurvival
    (roots : ℕ → ι → PMF Bool) :
    Antitone (quittingRootSequenceSurvival roots) :=
  antitone_quittingJointSurvivalWeight roots 0

omit [DecidableEq ι] in
@[simp] theorem quittingRootSequenceClock_zero
    (roots : ℕ → ι → PMF Bool) :
    quittingRootSequenceClock roots 0 = 0 := by
  simp [quittingRootSequenceClock]

omit [DecidableEq ι] in
theorem quittingRootSequenceClock_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    0 ≤ quittingRootSequenceClock roots time := by
  unfold quittingRootSequenceClock
  linarith [quittingRootSequenceSurvival_le_one roots time]

omit [DecidableEq ι] in
theorem quittingRootSequenceClock_le_one
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    quittingRootSequenceClock roots time ≤ 1 := by
  unfold quittingRootSequenceClock
  linarith [quittingRootSequenceSurvival_nonneg roots time]

omit [DecidableEq ι] in
theorem monotone_quittingRootSequenceClock
    (roots : ℕ → ι → PMF Bool) :
    Monotone (quittingRootSequenceClock roots) := by
  intro first second hle
  unfold quittingRootSequenceClock
  linarith [antitone_quittingRootSequenceSurvival roots hle]

omit [DecidableEq ι] in
theorem quittingRootSequenceSurvival_succ
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    quittingRootSequenceSurvival roots (time + 1) =
      quittingRootSequenceSurvival roots time *
        quittingStationaryContinueMass (roots time) := by
  simpa [quittingRootSequenceSurvival] using
    quittingJointSurvivalWeight_succ roots 0 time

theorem quittingRootSequenceStageCoalitionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (coalition : {S : Finset ι // S.Nonempty}) :
    0 ≤ quittingRootSequenceStageCoalitionMass roots time coalition := by
  exact mul_nonneg (quittingRootSequenceSurvival_nonneg roots time)
    (quittingRootCoalitionMass_nonneg (roots time) coalition.1)

theorem sum_quittingRootSequenceStageCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (∑ coalition,
      quittingRootSequenceStageCoalitionMass roots time coalition) =
      quittingRootSequenceSurvival roots time -
        quittingRootSequenceSurvival roots (time + 1) := by
  calc
    (∑ coalition,
        quittingRootSequenceStageCoalitionMass roots time coalition) =
        ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingRootSequenceSurvival roots time *
            quittingRootCoalitionMass (roots time) coalition := by
      rw [Finset.sum_subtype (Finset.univ.erase (∅ : Finset ι))
        (fun coalition => by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact Finset.nonempty_iff_ne_empty.symm)]
      rfl
    _ = quittingRootSequenceSurvival roots time *
        (1 - quittingStationaryContinueMass (roots time)) := by
      rw [← Finset.mul_sum, quittingRootCoalitionMass_sum_nonempty]
    _ = quittingRootSequenceSurvival roots time -
        quittingRootSequenceSurvival roots (time + 1) := by
      rw [quittingRootSequenceSurvival_succ]
      ring

@[simp] theorem quittingRootSequenceCumulativeCoalitionMass_zero
    (roots : ℕ → ι → PMF Bool)
    (coalition : {S : Finset ι // S.Nonempty}) :
    quittingRootSequenceCumulativeCoalitionMass roots 0 coalition = 0 := by
  simp [quittingRootSequenceCumulativeCoalitionMass]

theorem quittingRootSequenceCumulativeCoalitionMass_succ
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (coalition : {S : Finset ι // S.Nonempty}) :
    quittingRootSequenceCumulativeCoalitionMass roots (time + 1) coalition =
      quittingRootSequenceCumulativeCoalitionMass roots time coalition +
        quittingRootSequenceStageCoalitionMass roots time coalition := by
  unfold quittingRootSequenceCumulativeCoalitionMass
  rw [Finset.sum_range_succ]

theorem quittingRootSequenceCumulativeCoalitionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (coalition : {S : Finset ι // S.Nonempty}) :
    0 ≤ quittingRootSequenceCumulativeCoalitionMass roots time coalition := by
  exact Finset.sum_nonneg fun stage _ =>
    quittingRootSequenceStageCoalitionMass_nonneg roots stage coalition

theorem sum_quittingRootSequenceCumulativeCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (∑ coalition,
      quittingRootSequenceCumulativeCoalitionMass roots time coalition) =
      quittingRootSequenceClock roots time := by
  simp only [quittingRootSequenceCumulativeCoalitionMass]
  rw [Finset.sum_comm]
  simp_rw [sum_quittingRootSequenceStageCoalitionMass]
  unfold quittingRootSequenceClock
  induction time with
  | zero => simp
  | succ time ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-! ## Finite post-jump step path -/

/-- A literal certificate that joint survival vanishes after a finite row. -/
structure QuittingFiniteRootSequenceAbsorption
    (roots : ℕ → ι → PMF Bool) where
  cutoff : ℕ
  survival_zero : quittingRootSequenceSurvival roots (cutoff + 1) = 0

namespace QuittingFiniteRootSequenceAbsorption

variable {roots : ℕ → ι → PMF Bool}

/-- The cumulative finite step function, using the post-jump value at each
absorption clock. -/
def value (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (time : ℝ) (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  ∑ stage ∈ Finset.range (certificate.cutoff + 1),
    if quittingRootSequenceClock roots stage ≤ time then
      quittingRootSequenceStageCoalitionMass roots stage coalition else 0

/-- The pre-jump value at each absorption clock. -/
def leftValue (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (time : ℝ) (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  ∑ stage ∈ Finset.range (certificate.cutoff + 1),
    if quittingRootSequenceClock roots stage < time then
      quittingRootSequenceStageCoalitionMass roots stage coalition else 0

theorem value_nonneg
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (time : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    0 ≤ certificate.value time coalition := by
  exact Finset.sum_nonneg fun stage _ => by
    split
    · exact quittingRootSequenceStageCoalitionMass_nonneg roots stage coalition
    · exact le_rfl

theorem value_le_cumulative
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (time : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    certificate.value time coalition ≤
      quittingRootSequenceCumulativeCoalitionMass roots
        (certificate.cutoff + 1) coalition := by
  unfold value quittingRootSequenceCumulativeCoalitionMass
  apply Finset.sum_le_sum
  intro stage _
  split
  · exact le_rfl
  · exact quittingRootSequenceStageCoalitionMass_nonneg roots stage coalition

theorem cumulative_cutoff_le_one
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (coalition : {S : Finset ι // S.Nonempty}) :
    quittingRootSequenceCumulativeCoalitionMass roots
        (certificate.cutoff + 1) coalition ≤ 1 := by
  calc
    quittingRootSequenceCumulativeCoalitionMass roots
          (certificate.cutoff + 1) coalition ≤
        ∑ terminal,
          quittingRootSequenceCumulativeCoalitionMass roots
            (certificate.cutoff + 1) terminal :=
      Finset.single_le_sum
        (fun terminal _ => quittingRootSequenceCumulativeCoalitionMass_nonneg
          roots (certificate.cutoff + 1) terminal)
        (Finset.mem_univ coalition)
    _ = quittingRootSequenceClock roots (certificate.cutoff + 1) :=
      sum_quittingRootSequenceCumulativeCoalitionMass roots _
    _ = 1 := by simp [quittingRootSequenceClock, certificate.survival_zero]

private theorem tendsto_right_stage
    (stage : ℕ) (time : ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto
        (fun s => if quittingRootSequenceClock roots stage ≤ s then
          quittingRootSequenceStageCoalitionMass roots stage coalition else 0)
        (nhdsWithin time (Icc time 1))
        (𝓝 (if quittingRootSequenceClock roots stage ≤ time then
          quittingRootSequenceStageCoalitionMass roots stage coalition else 0)) := by
  by_cases hclock : quittingRootSequenceClock roots stage ≤ time
  · rw [if_pos hclock]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [if_pos (hclock.trans hs.1)]
  · have htime : time < quittingRootSequenceClock roots stage := lt_of_not_ge hclock
    rw [if_neg hclock]
    apply tendsto_const_nhds.congr'
    have hevent : ∀ᶠ s in nhdsWithin time (Icc time 1),
        s < quittingRootSequenceClock roots stage :=
      (eventually_lt_nhds htime).filter_mono inf_le_left
    filter_upwards [hevent] with s hs
    rw [if_neg (not_le_of_gt hs)]

private theorem tendsto_left_stage
    (stage : ℕ) (time : ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto
        (fun s => if quittingRootSequenceClock roots stage ≤ s then
          quittingRootSequenceStageCoalitionMass roots stage coalition else 0)
        (nhdsWithin time (Icc 0 time \ {time}))
        (𝓝 (if quittingRootSequenceClock roots stage < time then
          quittingRootSequenceStageCoalitionMass roots stage coalition else 0)) := by
  by_cases hclock : quittingRootSequenceClock roots stage < time
  · rw [if_pos hclock]
    apply tendsto_const_nhds.congr'
    have hevent : ∀ᶠ s in nhdsWithin time (Icc 0 time \ {time}),
        quittingRootSequenceClock roots stage < s :=
      (lt_mem_nhds hclock).filter_mono inf_le_left
    filter_upwards [hevent] with s hs
    rw [if_pos hs.le]
  · rw [if_neg hclock]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : s < time := by
      exact lt_of_le_of_ne hs.1.2 hs.2
    simp [not_le_of_gt (hst.trans_le (not_lt.mp hclock))]

/-- The finite post-jump step function is a coordinatewise monotone càdlàg
path. -/
def cadlagPath
    (certificate : QuittingFiniteRootSequenceAbsorption roots) :
    CadlagPath (ι := ι) where
  value := certificate.value
  leftValue := certificate.leftValue
  value_mem := by
    intro time _ coalition
    exact ⟨certificate.value_nonneg time coalition,
      (certificate.value_le_cumulative time coalition).trans
        (certificate.cumulative_cutoff_le_one coalition)⟩
  monotone := by
    intro coalition first _ second _ hle
    unfold value
    apply Finset.sum_le_sum
    intro stage _
    by_cases hfirst : quittingRootSequenceClock roots stage ≤ first
    · rw [if_pos hfirst, if_pos (hfirst.trans hle)]
    · rw [if_neg hfirst]
      split
      · exact quittingRootSequenceStageCoalitionMass_nonneg roots stage coalition
      · exact le_rfl
  right_continuous := by
    intro coalition time _
    unfold value
    apply tendsto_finsetSum
    intro stage _
    exact tendsto_right_stage stage time coalition
  left_limit := by
    intro coalition time _
    unfold value leftValue
    apply tendsto_finsetSum
    intro stage _
    exact tendsto_left_stage stage time coalition
  left_zero := by
    intro coalition
    unfold leftValue
    apply Finset.sum_eq_zero
    intro stage _
    rw [if_neg (not_lt_of_ge (quittingRootSequenceClock_nonneg roots stage))]

/-! ## Finite plateaus and clock domination -/

omit [DecidableEq ι] in
private theorem exists_minimal_clock_after
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {time : ℝ} (htime1 : time < 1) :
    ∃ stage ≤ certificate.cutoff,
      time < quittingRootSequenceClock roots (stage + 1) ∧
      ∀ earlier < stage,
        quittingRootSequenceClock roots (earlier + 1) ≤ time := by
  have hlast : quittingRootSequenceClock roots (certificate.cutoff + 1) = 1 := by
    simp [quittingRootSequenceClock, certificate.survival_zero]
  have hexists : ∃ stage,
      time < quittingRootSequenceClock roots (stage + 1) :=
    ⟨certificate.cutoff, by simpa [hlast] using htime1⟩
  let stage := Nat.find hexists
  have hstage : stage ≤ certificate.cutoff := by
    exact Nat.find_min' hexists (by simpa [hlast] using htime1)
  refine ⟨stage, hstage, Nat.find_spec hexists, ?_⟩
  intro earlier hearlier
  exact not_lt.mp (Nat.find_min hexists hearlier)

private theorem value_eq_cumulative_of_minimal
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {base time : ℝ} {stage : ℕ}
    (hbase0 : 0 ≤ base)
    (hstage : stage ≤ certificate.cutoff)
    (hnext : time < quittingRootSequenceClock roots (stage + 1))
    (hbase : base ≤ time)
    (hminimal : ∀ earlier < stage,
      quittingRootSequenceClock roots (earlier + 1) ≤ base)
    (coalition : {S : Finset ι // S.Nonempty}) :
    certificate.value time coalition =
      quittingRootSequenceCumulativeCoalitionMass roots (stage + 1) coalition := by
  unfold value quittingRootSequenceCumulativeCoalitionMass
  let mass := fun earlier =>
    quittingRootSequenceStageCoalitionMass roots earlier coalition
  have hsubset : Finset.range (stage + 1) ⊆
      Finset.range (certificate.cutoff + 1) := by
    exact Finset.range_mono (Nat.add_le_add_right hstage 1)
  calc
    (∑ earlier ∈ Finset.range (certificate.cutoff + 1),
        if quittingRootSequenceClock roots earlier ≤ time then
          mass earlier else 0) =
        ∑ earlier ∈ Finset.range (stage + 1),
          if quittingRootSequenceClock roots earlier ≤ time then
            mass earlier else 0 := by
      symm
      apply Finset.sum_subset hsubset
      intro earlier _ hnotSmall
      have hearler : stage + 1 ≤ earlier := by
        simpa only [Finset.mem_range, not_lt] using hnotSmall
      have hclock : quittingRootSequenceClock roots (stage + 1) ≤
          quittingRootSequenceClock roots earlier :=
        monotone_quittingRootSequenceClock roots hearler
      rw [if_neg (not_le_of_gt (hnext.trans_le hclock))]
    _ = ∑ earlier ∈ Finset.range (stage + 1), mass earlier := by
      apply Finset.sum_congr rfl
      intro earlier hearlier
      rw [if_pos]
      rcases Nat.eq_zero_or_pos earlier with rfl | hearler0
      · exact (quittingRootSequenceClock_zero roots).le.trans hbase0 |>.trans hbase
      · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hearler0.ne'
        exact (hminimal previous (by simpa using hearlier)).trans hbase
    _ = ∑ earlier ∈ Finset.range (stage + 1),
        quittingRootSequenceStageCoalitionMass roots earlier coalition := rfl

private theorem leftValue_eq_cumulative_of_minimal
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {base time : ℝ} {stage : ℕ}
    (hbase0 : 0 ≤ base)
    (hstage : stage ≤ certificate.cutoff)
    (hbase : base < time)
    (hnext : time ≤ quittingRootSequenceClock roots (stage + 1))
    (hminimal : ∀ earlier < stage,
      quittingRootSequenceClock roots (earlier + 1) ≤ base)
    (coalition : {S : Finset ι // S.Nonempty}) :
    certificate.leftValue time coalition =
      quittingRootSequenceCumulativeCoalitionMass roots (stage + 1) coalition := by
  unfold leftValue quittingRootSequenceCumulativeCoalitionMass
  let mass := fun earlier =>
    quittingRootSequenceStageCoalitionMass roots earlier coalition
  have hsubset : Finset.range (stage + 1) ⊆
      Finset.range (certificate.cutoff + 1) := by
    exact Finset.range_mono (Nat.add_le_add_right hstage 1)
  calc
    (∑ earlier ∈ Finset.range (certificate.cutoff + 1),
        if quittingRootSequenceClock roots earlier < time then
          mass earlier else 0) =
        ∑ earlier ∈ Finset.range (stage + 1),
          if quittingRootSequenceClock roots earlier < time then
            mass earlier else 0 := by
      symm
      apply Finset.sum_subset hsubset
      intro earlier _ hnotSmall
      have hearler : stage + 1 ≤ earlier := by
        simpa only [Finset.mem_range, not_lt] using hnotSmall
      have hclock : quittingRootSequenceClock roots (stage + 1) ≤
          quittingRootSequenceClock roots earlier :=
        monotone_quittingRootSequenceClock roots hearler
      rw [if_neg (not_lt_of_ge (hnext.trans hclock))]
    _ = ∑ earlier ∈ Finset.range (stage + 1), mass earlier := by
      apply Finset.sum_congr rfl
      intro earlier hearlier
      rw [if_pos]
      rcases Nat.eq_zero_or_pos earlier with rfl | hearler0
      · exact (quittingRootSequenceClock_zero roots).trans_lt
          (hbase0.trans_lt hbase)
      · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hearler0.ne'
        exact (hminimal previous (by simpa using hearlier)).trans_lt hbase
    _ = ∑ earlier ∈ Finset.range (stage + 1),
        quittingRootSequenceStageCoalitionMass roots earlier coalition := rfl

private theorem pathTotal_eq_clock_of_minimal
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {base time : ℝ} {stage : ℕ}
    (hbase0 : 0 ≤ base)
    (hstage : stage ≤ certificate.cutoff)
    (hnext : time < quittingRootSequenceClock roots (stage + 1))
    (hbase : base ≤ time)
    (hminimal : ∀ earlier < stage,
      quittingRootSequenceClock roots (earlier + 1) ≤ base) :
    pathTotal certificate.cadlagPath time =
      quittingRootSequenceClock roots (stage + 1) := by
  unfold pathTotal
  simp only [cadlagPath]
  simp_rw [certificate.value_eq_cumulative_of_minimal hbase0 hstage hnext
    hbase hminimal]
  exact sum_quittingRootSequenceCumulativeCoalitionMass roots (stage + 1)

@[simp] theorem pathTotal_cadlagPath_one
    (certificate : QuittingFiniteRootSequenceAbsorption roots) :
    pathTotal certificate.cadlagPath 1 = 1 := by
  unfold pathTotal
  simp only [cadlagPath, value]
  simp_rw [if_pos (quittingRootSequenceClock_le_one roots _)]
  change (∑ coalition,
    quittingRootSequenceCumulativeCoalitionMass roots
      (certificate.cutoff + 1) coalition) = 1
  rw [sum_quittingRootSequenceCumulativeCoalitionMass]
  simp [quittingRootSequenceClock, certificate.survival_zero]

@[simp] theorem value_cadlagPath_one
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    (coalition : {S : Finset ι // S.Nonempty}) :
    certificate.cadlagPath.value 1 coalition =
      quittingRootSequenceCumulativeCoalitionMass roots
        (certificate.cutoff + 1) coalition := by
  change certificate.value 1 coalition = _
  unfold value quittingRootSequenceCumulativeCoalitionMass
  apply Finset.sum_congr rfl
  intro stage _
  rw [if_pos (quittingRootSequenceClock_le_one roots stage)]

/-- Before terminal time, total path mass strictly overshoots the clock. -/
theorem lt_pathTotal_cadlagPath
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {time : ℝ} (htime : time ∈ Ico (0 : ℝ) 1) :
    time < pathTotal certificate.cadlagPath time := by
  obtain ⟨stage, hstage, hnext, hminimal⟩ :=
    certificate.exists_minimal_clock_after htime.2
  rw [certificate.pathTotal_eq_clock_of_minimal htime.1 hstage hnext
    le_rfl hminimal]
  exact hnext

/-- The path total dominates the clock throughout the unit interval. -/
theorem le_pathTotal_cadlagPath
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1) :
    time ≤ pathTotal certificate.cadlagPath time := by
  rcases htime.2.eq_or_lt with rfl | htime1
  · simp
  · exact (certificate.lt_pathTotal_cadlagPath ⟨htime.1, htime1⟩).le

theorem pathTimes_cadlagPath
    (certificate : QuittingFiniteRootSequenceAbsorption roots) :
    pathTimes certificate.cadlagPath = {1} := by
  ext time
  simp only [pathTimes, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨htime, heq⟩
    by_contra hne
    have hlt : time < 1 := lt_of_le_of_ne htime.2 hne
    exact (certificate.lt_pathTotal_cadlagPath ⟨htime.1, hlt⟩).ne heq.symm
  · rintro rfl
    exact ⟨by simp, certificate.pathTotal_cadlagPath_one⟩

private theorem sum_leftValue_at_nextClock
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {base : ℝ} {stage : ℕ}
    (hbase0 : 0 ≤ base)
    (hstage : stage ≤ certificate.cutoff)
    (hnext : base < quittingRootSequenceClock roots (stage + 1))
    (hminimal : ∀ earlier < stage,
      quittingRootSequenceClock roots (earlier + 1) ≤ base) :
    (∑ coalition,
      certificate.leftValue (quittingRootSequenceClock roots (stage + 1))
        coalition) = quittingRootSequenceClock roots (stage + 1) := by
  simp_rw [certificate.leftValue_eq_cumulative_of_minimal hbase0 hstage hnext
    le_rfl hminimal]
  exact sum_quittingRootSequenceCumulativeCoalitionMass roots (stage + 1)

private theorem nextClock_mem_jumps_or_times
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {base : ℝ} {stage : ℕ}
    (hbase0 : 0 ≤ base)
    (hstage : stage ≤ certificate.cutoff)
    (hnext : base < quittingRootSequenceClock roots (stage + 1))
    (hminimal : ∀ earlier < stage,
      quittingRootSequenceClock roots (earlier + 1) ≤ base) :
    quittingRootSequenceClock roots (stage + 1) ∈
      pathJumps certificate.cadlagPath ∪ pathTimes certificate.cadlagPath := by
  let next := quittingRootSequenceClock roots (stage + 1)
  have hnextMem : next ∈ Icc (0 : ℝ) 1 :=
    ⟨quittingRootSequenceClock_nonneg roots _,
      quittingRootSequenceClock_le_one roots _⟩
  rcases hnextMem.2.eq_or_lt with hnextOne | hnextLt
  · apply Or.inr
    rw [certificate.pathTimes_cadlagPath]
    simpa [next] using hnextOne
  · apply Or.inl
    refine ⟨hnextMem, ?_⟩
    have hstrict : next < pathTotal certificate.cadlagPath next :=
      certificate.lt_pathTotal_cadlagPath ⟨hnextMem.1, hnextLt⟩
    by_contra hnoJump
    have hnoJumpAll : ∀ coalition,
        pathJump certificate.cadlagPath next coalition = 0 := by
      intro coalition
      by_contra hcoalition
      exact hnoJump ⟨coalition, hcoalition⟩
    have hsumJump : (∑ coalition,
        pathJump certificate.cadlagPath next coalition) = 0 := by
      simp [hnoJumpAll]
    have hsumLeft : (∑ coalition,
        certificate.leftValue next coalition) = next := by
      exact certificate.sum_leftValue_at_nextClock hbase0 hstage hnext hminimal
    unfold pathJump at hsumJump
    rw [Finset.sum_sub_distrib] at hsumJump
    change pathTotal certificate.cadlagPath next -
      (∑ coalition, certificate.leftValue next coalition) = 0 at hsumJump
    rw [hsumLeft] at hsumJump
    linarith

private theorem Ico_subset_path_complement
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {base : ℝ} (hbase : base ∈ Icc (0 : ℝ) 1 \
      (pathJumps certificate.cadlagPath ∪ pathTimes certificate.cadlagPath))
    {stage : ℕ} (hstage : stage ≤ certificate.cutoff)
    (_hnext : base < quittingRootSequenceClock roots (stage + 1))
    (hminimal : ∀ earlier < stage,
      quittingRootSequenceClock roots (earlier + 1) ≤ base) :
    Ico base (quittingRootSequenceClock roots (stage + 1)) ⊆
      Icc (0 : ℝ) 1 \
        (pathJumps certificate.cadlagPath ∪ pathTimes certificate.cadlagPath) := by
  intro time htime
  by_cases heq : time = base
  · simpa [heq] using hbase
  have hbaseLt : base < time := lt_of_le_of_ne htime.1 (Ne.symm heq)
  have htimeMem : time ∈ Icc (0 : ℝ) 1 :=
    ⟨hbase.1.1.trans htime.1,
      (htime.2.le.trans (quittingRootSequenceClock_le_one roots _))⟩
  refine ⟨htimeMem, ?_⟩
  have hvalue (coalition : {S : Finset ι // S.Nonempty}) :
      certificate.value time coalition =
        quittingRootSequenceCumulativeCoalitionMass roots (stage + 1) coalition :=
    certificate.value_eq_cumulative_of_minimal hbase.1.1 hstage htime.2
      htime.1 hminimal coalition
  have hleft (coalition : {S : Finset ι // S.Nonempty}) :
      certificate.leftValue time coalition =
        quittingRootSequenceCumulativeCoalitionMass roots (stage + 1) coalition :=
    certificate.leftValue_eq_cumulative_of_minimal hbase.1.1 hstage hbaseLt
      htime.2.le hminimal coalition
  have hnotJump : time ∉ pathJumps certificate.cadlagPath := by
    rintro ⟨_, coalition, hcoalition⟩
    apply hcoalition
    simp [pathJump, cadlagPath, hvalue coalition, hleft coalition]
  have htotal : pathTotal certificate.cadlagPath time =
      quittingRootSequenceClock roots (stage + 1) :=
    certificate.pathTotal_eq_clock_of_minimal hbase.1.1 hstage htime.2
      htime.1 hminimal
  have hnotTime : time ∉ pathTimes certificate.cadlagPath := by
    rintro ⟨_, heqTotal⟩
    exact htime.2.ne (heqTotal.symm.trans htotal)
  exact fun h => h.elim hnotJump hnotTime

/-- Every plateau has total mass equal to the supremum of its connected
component, so the finite step path satisfies absorption-path axiom A2. -/
theorem absorptionPathA2_cadlagPath
    (certificate : QuittingFiniteRootSequenceAbsorption roots) :
    AbsorptionPathA2 certificate.cadlagPath := by
  intro base hbase time htime
  let support := Icc (0 : ℝ) 1 \
    (pathJumps certificate.cadlagPath ∪ pathTimes certificate.cadlagPath)
  have htimeSupport : time ∈ support :=
    connectedComponentIn_subset support base htime
  have htimeLtOne : time < 1 := by
    have hne : time ≠ 1 := by
      intro heq
      apply htimeSupport.2
      apply Or.inr
      rw [certificate.pathTimes_cadlagPath, heq]
      simp
    exact lt_of_le_of_ne htimeSupport.1.2 hne
  obtain ⟨stage, hstage, hnext, hminimal⟩ :=
    certificate.exists_minimal_clock_after htimeLtOne
  let next := quittingRootSequenceClock roots (stage + 1)
  let component := connectedComponentIn support time
  have hnextBoundary : next ∈
      pathJumps certificate.cadlagPath ∪ pathTimes certificate.cadlagPath :=
    certificate.nextClock_mem_jumps_or_times htimeSupport.1.1 hstage hnext
      hminimal
  have hcomponentSubset : component ⊆ support :=
    connectedComponentIn_subset support time
  have hcomponentNonempty : component.Nonempty :=
    ⟨time, mem_connectedComponentIn htimeSupport⟩
  have hupper : ∀ point ∈ component, point ≤ next := by
    intro point hpoint
    by_contra hnotLe
    have hnextLt : next < point := lt_of_not_ge hnotLe
    have hnextComponent : next ∈ component :=
      isPreconnected_connectedComponentIn.ordConnected.out
        (mem_connectedComponentIn htimeSupport) hpoint ⟨hnext.le, hnextLt.le⟩
    exact (hcomponentSubset hnextComponent).2 hnextBoundary
  have hplateauSubset : Ico time next ⊆ component := by
    apply isPreconnected_Ico.subset_connectedComponentIn
      (left_mem_Ico.mpr hnext)
    exact certificate.Ico_subset_path_complement htimeSupport hstage hnext
      hminimal
  have hcofinal : ∀ point < next, ∃ member ∈ component, point < member := by
    intro point hpoint
    by_cases hpointTime : point < time
    · exact ⟨time, mem_connectedComponentIn htimeSupport, hpointTime⟩
    · let member := (point + next) / 2
      have hpointMember : point < member := by
        dsimp only [member]
        linarith
      have hmemberNext : member < next := by
        dsimp only [member]
        linarith
      have htimeMember : time ≤ member :=
        (not_lt.mp hpointTime).trans hpointMember.le
      exact ⟨member, hplateauSubset ⟨htimeMember, hmemberNext⟩, hpointMember⟩
  have hsup : sSup component = next :=
    csSup_eq_of_forall_le_of_forall_lt_exists_gt hcomponentNonempty hupper hcofinal
  have hcomponentEq :
      connectedComponentIn support base = connectedComponentIn support time :=
    connectedComponentIn_eq htime
  rw [hcomponentEq, hsup]
  exact certificate.pathTotal_eq_clock_of_minimal htimeSupport.1.1 hstage
    hnext le_rfl hminimal

/-! ## Literal positive-stage jumps -/

theorem sum_quittingRootSequenceStageCoalitionMass_eq_clock_sub
    (roots : ℕ → ι → PMF Bool) (stage : ℕ) :
    (∑ coalition,
      quittingRootSequenceStageCoalitionMass roots stage coalition) =
      quittingRootSequenceClock roots (stage + 1) -
        quittingRootSequenceClock roots stage := by
  rw [sum_quittingRootSequenceStageCoalitionMass]
  unfold quittingRootSequenceClock
  ring

theorem quittingRootSequenceStageCoalitionMass_eq_zero_of_clock_succ_eq
    (roots : ℕ → ι → PMF Bool) (stage : ℕ)
    (hclock : quittingRootSequenceClock roots (stage + 1) =
      quittingRootSequenceClock roots stage)
    (coalition : {S : Finset ι // S.Nonempty}) :
    quittingRootSequenceStageCoalitionMass roots stage coalition = 0 := by
  have hsum : (∑ terminal,
      quittingRootSequenceStageCoalitionMass roots stage terminal) = 0 := by
    rw [sum_quittingRootSequenceStageCoalitionMass_eq_clock_sub, hclock]
    ring
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun terminal _ => quittingRootSequenceStageCoalitionMass_nonneg
      roots stage terminal)).mp hsum coalition (Finset.mem_univ coalition)

theorem pathJump_cadlagPath_at_positive_stage
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {stage : ℕ} (hstage : stage ≤ certificate.cutoff)
    (hpositive : quittingRootSequenceClock roots stage <
      quittingRootSequenceClock roots (stage + 1))
    (coalition : {S : Finset ι // S.Nonempty}) :
    pathJump certificate.cadlagPath
        (quittingRootSequenceClock roots stage) coalition =
      quittingRootSequenceStageCoalitionMass roots stage coalition := by
  unfold pathJump cadlagPath value leftValue
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single stage]
  · simp
  · intro earlier hearlier hne
    rcases lt_or_gt_of_ne hne with hearler | hearler
    · have hclockLe : quittingRootSequenceClock roots earlier ≤
          quittingRootSequenceClock roots stage :=
        monotone_quittingRootSequenceClock roots hearler.le
      by_cases hclockLt : quittingRootSequenceClock roots earlier <
          quittingRootSequenceClock roots stage
      · rw [if_pos hclockLe, if_pos hclockLt, sub_self]
      · have hclockEq : quittingRootSequenceClock roots earlier =
            quittingRootSequenceClock roots stage :=
          le_antisymm hclockLe (not_lt.mp hclockLt)
        have hsuccLe : quittingRootSequenceClock roots (earlier + 1) ≤
            quittingRootSequenceClock roots stage :=
          monotone_quittingRootSequenceClock roots (by omega)
        have hclockSucc : quittingRootSequenceClock roots (earlier + 1) =
            quittingRootSequenceClock roots earlier := by
          exact le_antisymm (hsuccLe.trans_eq hclockEq.symm)
            (monotone_quittingRootSequenceClock roots (Nat.le_succ earlier))
        rw [if_pos hclockLe, if_neg hclockLt,
          quittingRootSequenceStageCoalitionMass_eq_zero_of_clock_succ_eq
            roots earlier hclockSucc]
        ring
    · have hsuccLe : quittingRootSequenceClock roots (stage + 1) ≤
          quittingRootSequenceClock roots earlier :=
        monotone_quittingRootSequenceClock roots (by omega)
      have hclockLt : quittingRootSequenceClock roots stage <
          quittingRootSequenceClock roots earlier := hpositive.trans_le hsuccLe
      rw [if_neg (not_le_of_gt hclockLt), if_neg (not_lt_of_ge hclockLt.le)]
      ring
  · exact fun hnotMem => (hnotMem (by simpa using hstage)).elim

/-- At a positive source stage the right-continuous value is the cumulative
mass through that stage. -/
theorem value_cadlagPath_at_positive_stage
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {stage : ℕ} (hstage : stage ≤ certificate.cutoff)
    (hpositive : quittingRootSequenceClock roots stage <
      quittingRootSequenceClock roots (stage + 1))
    (coalition : {S : Finset ι // S.Nonempty}) :
    certificate.cadlagPath.value
        (quittingRootSequenceClock roots stage) coalition =
      quittingRootSequenceCumulativeCoalitionMass roots (stage + 1) coalition := by
  change certificate.value (quittingRootSequenceClock roots stage) coalition = _
  apply certificate.value_eq_cumulative_of_minimal
    (quittingRootSequenceClock_nonneg roots stage) hstage hpositive le_rfl
  intro earlier hearlier
  exact monotone_quittingRootSequenceClock roots (by omega)

/-- At a positive source stage the stored left value is the cumulative mass
strictly before that stage. -/
theorem leftValue_cadlagPath_at_positive_stage
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {stage : ℕ} (hstage : stage ≤ certificate.cutoff)
    (hpositive : quittingRootSequenceClock roots stage <
      quittingRootSequenceClock roots (stage + 1))
    (coalition : {S : Finset ι // S.Nonempty}) :
    certificate.cadlagPath.leftValue
        (quittingRootSequenceClock roots stage) coalition =
      quittingRootSequenceCumulativeCoalitionMass roots stage coalition := by
  change certificate.leftValue (quittingRootSequenceClock roots stage) coalition = _
  have hjump := certificate.pathJump_cadlagPath_at_positive_stage
    hstage hpositive coalition
  have hvalue := certificate.value_cadlagPath_at_positive_stage
    hstage hpositive coalition
  rw [quittingRootSequenceCumulativeCoalitionMass_succ] at hvalue
  unfold pathJump at hjump
  change certificate.value (quittingRootSequenceClock roots stage) coalition -
      certificate.leftValue (quittingRootSequenceClock roots stage) coalition =
    quittingRootSequenceStageCoalitionMass roots stage coalition at hjump
  change certificate.value (quittingRootSequenceClock roots stage) coalition = _
    at hvalue
  linarith

/-- The post-jump total at a positive stage is the next absorption clock. -/
theorem pathTotal_cadlagPath_at_positive_stage
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {stage : ℕ} (hstage : stage ≤ certificate.cutoff)
    (hpositive : quittingRootSequenceClock roots stage <
      quittingRootSequenceClock roots (stage + 1)) :
    pathTotal certificate.cadlagPath
        (quittingRootSequenceClock roots stage) =
      quittingRootSequenceClock roots (stage + 1) := by
  unfold pathTotal
  simp_rw [certificate.value_cadlagPath_at_positive_stage hstage hpositive]
  exact sum_quittingRootSequenceCumulativeCoalitionMass roots (stage + 1)

/-- A positive source stage realizes its literal normalized path jump. -/
theorem jumpRelation_at_positive_stage
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {stage : ℕ} (hstage : stage ≤ certificate.cutoff)
    (hpositive : quittingRootSequenceClock roots stage <
      quittingRootSequenceClock roots (stage + 1)) :
    ∀ coalition,
      pathJump certificate.cadlagPath
          (quittingRootSequenceClock roots stage) coalition /
          (1 - quittingRootSequenceClock roots stage) =
        quittingRootCoalitionMass (roots stage) coalition.1 := by
  intro coalition
  rw [certificate.pathJump_cadlagPath_at_positive_stage hstage hpositive]
  unfold quittingRootSequenceStageCoalitionMass quittingRootSequenceClock
  have hsurvival : quittingRootSequenceSurvival roots stage ≠ 0 := by
    intro hzero
    have hnextZero : quittingRootSequenceSurvival roots (stage + 1) = 0 := by
      have hnonneg := quittingRootSequenceSurvival_nonneg roots (stage + 1)
      have hanti := antitone_quittingRootSequenceSurvival roots
        (Nat.le_succ stage)
      linarith
    unfold quittingRootSequenceClock at hpositive
    rw [hzero, hnextZero] at hpositive
    linarith
  rw [show 1 - (1 - quittingRootSequenceSurvival roots stage) =
    quittingRootSequenceSurvival roots stage by ring]
  exact mul_div_cancel_left₀ _ hsurvival

private theorem exists_positive_source_stage_of_jump
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {time : ℝ} (htime : time ∈ pathJumps certificate.cadlagPath) :
    ∃ stage ≤ certificate.cutoff,
      time = quittingRootSequenceClock roots stage ∧
      quittingRootSequenceClock roots stage <
        quittingRootSequenceClock roots (stage + 1) := by
  obtain ⟨coalition, hcoalition⟩ := htime.2
  unfold pathJump cadlagPath value leftValue at hcoalition
  rw [← Finset.sum_sub_distrib] at hcoalition
  obtain ⟨stage, hstageMem, hstageTerm⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hcoalition
  have hclockLe : quittingRootSequenceClock roots stage ≤ time := by
    by_contra hnotLe
    have hclockGt : time < quittingRootSequenceClock roots stage :=
      lt_of_not_ge hnotLe
    rw [if_neg (not_le_of_gt hclockGt),
      if_neg (not_lt_of_ge hclockGt.le)] at hstageTerm
    exact hstageTerm (sub_self 0)
  have hnotClockLt : ¬quittingRootSequenceClock roots stage < time := by
    intro hclockLt
    rw [if_pos hclockLe, if_pos hclockLt] at hstageTerm
    exact hstageTerm (sub_self _)
  have htimeEq : time = quittingRootSequenceClock roots stage :=
    le_antisymm (not_lt.mp hnotClockLt) hclockLe
  have hmassNe :
      quittingRootSequenceStageCoalitionMass roots stage coalition ≠ 0 := by
    rwa [if_pos hclockLe, if_neg hnotClockLt, sub_zero] at hstageTerm
  have hmassPos : 0 <
      quittingRootSequenceStageCoalitionMass roots stage coalition :=
    lt_of_le_of_ne
      (quittingRootSequenceStageCoalitionMass_nonneg roots stage coalition)
      hmassNe.symm
  have hmassLe : quittingRootSequenceStageCoalitionMass roots stage coalition ≤
      ∑ terminal,
        quittingRootSequenceStageCoalitionMass roots stage terminal :=
    Finset.single_le_sum
      (fun terminal _ => quittingRootSequenceStageCoalitionMass_nonneg
        roots stage terminal) (Finset.mem_univ coalition)
  have hpositive : quittingRootSequenceClock roots stage <
      quittingRootSequenceClock roots (stage + 1) := by
    rw [sum_quittingRootSequenceStageCoalitionMass_eq_clock_sub] at hmassLe
    linarith
  exact ⟨stage, by simpa using hstageMem, htimeEq, hpositive⟩

/-- Every path jump retains a literal positive source row. -/
theorem exists_positive_source_stage
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {time : ℝ} (htime : time ∈ pathJumps certificate.cadlagPath) :
    ∃ stage ≤ certificate.cutoff,
      time = quittingRootSequenceClock roots stage ∧
      quittingRootSequenceClock roots stage <
        quittingRootSequenceClock roots (stage + 1) ∧
      ∀ coalition,
        pathJump certificate.cadlagPath time coalition / (1 - time) =
          quittingRootCoalitionMass (roots stage) coalition.1 := by
  obtain ⟨stage, hstage, htimeEq, hpositive⟩ :=
    certificate.exists_positive_source_stage_of_jump htime
  refine ⟨stage, hstage, htimeEq, hpositive, ?_⟩
  subst time
  exact certificate.jumpRelation_at_positive_stage hstage hpositive

/-- The finite post-jump càdlàg path satisfies all four absorption-path
axioms. -/
theorem isAbsorptionPath_cadlagPath
    (certificate : QuittingFiniteRootSequenceAbsorption roots) :
    IsAbsorptionPath certificate.cadlagPath := by
  refine ⟨?_, certificate.absorptionPathA2_cadlagPath, ?_, ?_⟩
  · intro time htime
    exact certificate.le_pathTotal_cadlagPath htime
  · intro time htime
    obtain ⟨stage, _, _, _, hrelation⟩ :=
      certificate.exists_positive_source_stage htime
    exact ⟨roots stage, hrelation⟩
  · intro time htime hneOne
    rw [certificate.pathTimes_cadlagPath] at htime
    exact (hneOne htime).elim

/-- The ordinary absorption path generated by a finite-hit-zero root
sequence. -/
def absorptionPath
    (certificate : QuittingFiniteRootSequenceAbsorption roots) :
    AbsorptionPath (ι := ι) :=
  ⟨certificate.cadlagPath, certificate.isAbsorptionPath_cadlagPath⟩

/-- The bundled path retains the literal product row at every positive
source stage. -/
theorem absorptionPathJumpRelation_at_positive_stage
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {stage : ℕ} (hstage : stage ≤ certificate.cutoff)
    (hpositive : quittingRootSequenceClock roots stage <
      quittingRootSequenceClock roots (stage + 1)) :
    AbsorptionPathJumpRelation certificate.absorptionPath
      (quittingRootSequenceClock roots stage) (roots stage) :=
  certificate.jumpRelation_at_positive_stage hstage hpositive

end QuittingFiniteRootSequenceAbsorption

end GameTheory.QuittingAbsorptionPath
