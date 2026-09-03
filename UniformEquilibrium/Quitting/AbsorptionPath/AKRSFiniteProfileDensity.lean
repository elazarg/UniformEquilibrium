/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.AKRSPartitionSmallCell
import UniformEquilibrium.Quitting.AbsorptionPath.DiscreteRootSequencePath
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletion
import UniformEquilibrium.Quitting.AbsorptionPath.WeakPathConvergence

/-!
# Finite-profile density for unit-bounded AKRS absorption paths

This module implements the corrected construction behind AKRS Proposition 4.8.
It partitions a unit-bounded absorption path, copies every large jump exactly,
productizes each small cell with the complete normalized cell increment, and
adds a final absorbing filler row. The resulting completely absorbing finite
root sequences induce unit-bounded paths converging weakly to the target.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- Collision domination at one partition stage only needs that stage's cut
to lie strictly below one. -/
theorem hasPartitionSmallCellCollisionDominationAt
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (stage : ℕ) (hcut : partitionCut path resolution stage < 1)
    (hsmall : pathTotal path.1 (partitionCut path resolution stage) ≤
      partitionProbe resolution (partitionCut path resolution stage)) :
    ∀ coalition player,
      2 ≤ coalition.card → player ∈ coalition →
        pathCellLaw path.1 (partitionCut path resolution stage)
            (partitionCut path resolution (stage + 1)) coalition ≤
          partitionSmallCellError resolution *
            pathCellLaw path.1 (partitionCut path resolution stage)
              (partitionCut path resolution (stage + 1)) {player} := by
  intro coalition player hcard hplayer
  have hresolutionOne : 1 ≤ resolution := by omega
  have hstartIcc := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne stage
  have hstartIco :
      partitionCut path resolution stage ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨hstartIcc.1, hcut⟩
  have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne stage
  rw [partitionCut_succ]
  exact
    pathCellLaw_le_partitionSmallCellError_mul_singleton_of_small_partition_cell
      path hpathTotal resolution hresolution hstartIco hstartBoundary hsmall
      coalition player hcard hplayer

/-- A decoder row at a single subterminal partition stage. -/
theorem nonempty_partitionCellRowData_of_cut_lt_one
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (stage : ℕ) (hcut : partitionCut path resolution stage < 1) :
    Nonempty (PartitionCellRowData path resolution stage) := by
  have hresolutionOne : 1 ≤ resolution := by omega
  let start := partitionCut path resolution stage
  let stop := partitionCut path resolution (stage + 1)
  have hstartMem : start ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨(partitionCut_mem_Icc path hpathTotal resolution hresolutionOne stage).1,
      hcut⟩
  have hstartBoundary : start ∈ partitionBoundaryTimes path :=
    partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
      hresolutionOne stage
  by_cases hlarge : partitionProbe resolution start < pathTotal path.1 start
  · have hjump : start ∈ pathJumps path.1 :=
      mem_pathJumps_of_probe_lt_pathTotal_of_boundary path resolution
        hstartBoundary hlarge
    have hstop : stop = pathTotal path.1 start := by
      simpa only [stop, start, partitionCut_succ] using
        nextPartitionCut_eq_pathTotal_of_probe_lt path resolution start hlarge
    refine ⟨{
      root := absorptionPathJumpRoot path start
      absorption_exact := ?_
      source := Or.inl ⟨hjump, hstop, rfl⟩
    }⟩
    exact copiedJumpRoot_absorption_eq_pathCellAbsorption path
      hpathTotal hjump hstop
  · have hsmall : pathTotal path.1 start ≤ partitionProbe resolution start :=
      not_lt.mp hlarge
    have hcellCollision : ∀ coalition player,
        2 ≤ coalition.card → player ∈ coalition →
          pathCellLaw path.1 start
              (nextPartitionCut path resolution start) coalition ≤
            partitionSmallCellError resolution *
              pathCellLaw path.1 start
                (nextPartitionCut path resolution start) {player} := by
      simpa only [start, partitionCut_succ] using
        hasPartitionSmallCellCollisionDominationAt path hpathTotal resolution
          hresolution stage hcut (by simpa only [start] using hsmall)
    let cell := smallPathCellOfPartition path hpathTotal resolution
      hresolution hstartMem hstartBoundary hsmall hcellCollision
    let packet := Classical.choice <|
      cell.nonempty_productization
        (partitionSmallCellError_pos resolution hresolution)
        (partitionSmallCellError_le_half resolution hresolution)
    refine ⟨{
      root := packet.quittingRoot
      absorption_exact := ?_
      source := Or.inr ⟨cell, packet, rfl, rfl, rfl⟩
    }⟩
    change quittingRootAbsorptionMass packet.quittingRoot =
      pathCellAbsorption path.1 start stop
    rw [packet.quittingRoot_absorption_exact, cell.law_absorption]
    rfl

end GameTheory.QuittingAbsorptionPath

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem exists_partitionDensityCutoff
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution) :
    ∃ cutoff, 1 - 1 / (resolution : ℝ) <
      partitionCut path resolution cutoff := by
  have hresolutionReal : (0 : ℝ) < resolution := by
    exact_mod_cast (Nat.zero_lt_of_lt hresolution)
  have hthreshold : 1 - 1 / (resolution : ℝ) < 1 := by
    have : (0 : ℝ) < 1 / (resolution : ℝ) := one_div_pos.mpr hresolutionReal
    linarith
  have heventually : ∀ᶠ cutoff in atTop,
      1 - 1 / (resolution : ℝ) < partitionCut path resolution cutoff :=
    (tendsto_partitionCut_one path hpathTotal resolution hresolution).eventually
      (Ioi_mem_nhds hthreshold)
  obtain ⟨cutoff, hcutoff⟩ := (eventually_atTop.1 heventually)
  exact ⟨cutoff, hcutoff cutoff le_rfl⟩

/-- The first recursive cut whose live remainder is below `1/resolution`. -/
def partitionDensityCutoff
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution) : ℕ :=
  Nat.find (exists_partitionDensityCutoff path hpathTotal resolution hresolution)

omit [Nonempty ι] in
theorem partitionDensityCutoff_spec
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution) :
    1 - 1 / (resolution : ℝ) < partitionCut path resolution
      (partitionDensityCutoff path hpathTotal resolution hresolution) :=
  Nat.find_spec (exists_partitionDensityCutoff path hpathTotal resolution hresolution)

omit [Nonempty ι] in
theorem partitionCut_le_threshold_of_lt_partitionDensityCutoff
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    {stage : ℕ}
    (hstage : stage < partitionDensityCutoff path hpathTotal resolution
      hresolution) :
    partitionCut path resolution stage ≤ 1 - 1 / (resolution : ℝ) := by
  exact not_lt.mp (Nat.find_min
    (exists_partitionDensityCutoff path hpathTotal resolution hresolution)
    hstage)

omit [Nonempty ι] in
theorem partitionCut_lt_one_of_lt_partitionDensityCutoff
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    {stage : ℕ}
    (hstage : stage < partitionDensityCutoff path hpathTotal resolution
      hresolution) :
    partitionCut path resolution stage < 1 := by
  have hresolutionReal : (0 : ℝ) < resolution := by
    exact_mod_cast (Nat.zero_lt_of_lt hresolution)
  have hthreshold : 1 - 1 / (resolution : ℝ) < 1 := by
    have : (0 : ℝ) < 1 / (resolution : ℝ) := one_div_pos.mpr hresolutionReal
    linarith
  exact (partitionCut_le_threshold_of_lt_partitionDensityCutoff path
    hpathTotal resolution hresolution hstage).trans_lt hthreshold

omit [Nonempty ι] in
theorem one_sub_partitionCut_partitionDensityCutoff_lt
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution) :
    1 - partitionCut path resolution
        (partitionDensityCutoff path hpathTotal resolution hresolution) <
      1 / (resolution : ℝ) := by
  linarith [partitionDensityCutoff_spec path hpathTotal resolution hresolution]

end GameTheory.QuittingAbsorptionPath

namespace GameTheory.QuittingAbsorptionPath

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The selected product row at one locally subterminal cell. -/
def partitionCellRootOfCutLtOne
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (stage : ℕ) (hcut : partitionCut path resolution stage < 1) :
    ι → PMF Bool :=
  (Classical.choice <| nonempty_partitionCellRowData_of_cut_lt_one path
    hpathTotal resolution hresolution stage hcut).root

theorem partitionCellRootOfCutLtOne_absorption_exact
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (stage : ℕ) (hcut : partitionCut path resolution stage < 1) :
    quittingRootAbsorptionMass
        (partitionCellRootOfCutLtOne path hpathTotal resolution hresolution
          stage hcut) =
      pathCellAbsorption path.1 (partitionCut path resolution stage)
        (partitionCut path resolution (stage + 1)) :=
  (Classical.choice <| nonempty_partitionCellRowData_of_cut_lt_one path
    hpathTotal resolution hresolution stage hcut).absorption_exact

/-- An arbitrary total extension of the locally defined pre-cutoff rows. -/
def partitionDensitySourceRoots
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution) :
    ℕ → ι → PMF Bool := fun stage ↦
  if hstage : stage < partitionDensityCutoff path hpathTotal resolution
      (by omega : 1 ≤ resolution) then
    partitionCellRootOfCutLtOne path hpathTotal resolution hresolution stage
      (partitionCut_lt_one_of_lt_partitionDensityCutoff path hpathTotal
        resolution (by omega) hstage)
  else
    quittingAllContinueRoot

@[simp] theorem partitionDensitySourceRoots_of_lt_cutoff
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {stage : ℕ}
    (hstage : stage < partitionDensityCutoff path hpathTotal resolution
      (by omega : 1 ≤ resolution)) :
    partitionDensitySourceRoots path hpathTotal resolution hresolution stage =
      partitionCellRootOfCutLtOne path hpathTotal resolution hresolution stage
        (partitionCut_lt_one_of_lt_partitionDensityCutoff path hpathTotal
          resolution (by omega) hstage) := by
  simp [partitionDensitySourceRoots, hstage]

/-- Complete the finite partition prefix by one sure-solo absorbing row. -/
def partitionDensityRoots
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution) :
    ℕ → ι → PMF Bool :=
  quittingLateSureSoloRoots
    (partitionDensitySourceRoots path hpathTotal resolution hresolution)
    (Classical.choice inferInstance)
    (partitionDensityCutoff path hpathTotal resolution (by omega))

@[simp] theorem partitionDensityRoots_of_lt_cutoff
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {stage : ℕ}
    (hstage : stage < partitionDensityCutoff path hpathTotal resolution
      (by omega : 1 ≤ resolution)) :
    partitionDensityRoots path hpathTotal resolution hresolution stage =
      partitionCellRootOfCutLtOne path hpathTotal resolution hresolution stage
        (partitionCut_lt_one_of_lt_partitionDensityCutoff path hpathTotal
          resolution (by omega) hstage) := by
  rw [partitionDensityRoots, quittingLateSureSoloRoots,
    quittingElementaryTailRoots_of_lt _ _ hstage]
  exact partitionDensitySourceRoots_of_lt_cutoff path hpathTotal resolution
    hresolution hstage

theorem quittingRootSequenceSurvival_partitionDensityRoots
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {stage : ℕ}
    (hstage : stage ≤ partitionDensityCutoff path hpathTotal resolution
      (by omega : 1 ≤ resolution)) :
    quittingRootSequenceSurvival
        (partitionDensityRoots path hpathTotal resolution hresolution) stage =
      1 - partitionCut path resolution stage := by
  induction stage with
  | zero => simp [partitionCut]
  | succ stage ih =>
      have hstageLt : stage < partitionDensityCutoff path hpathTotal resolution
          (by omega : 1 ≤ resolution) := by omega
      have hcut := partitionCut_lt_one_of_lt_partitionDensityCutoff path
        hpathTotal resolution (by omega : 1 ≤ resolution) hstageLt
      rw [quittingRootSequenceSurvival_succ, ih (by omega),
        partitionDensityRoots_of_lt_cutoff path hpathTotal resolution
          hresolution hstageLt]
      have habsorption := partitionCellRootOfCutLtOne_absorption_exact path
        hpathTotal resolution hresolution stage hcut
      have hcontinue : quittingStationaryContinueMass
          (partitionCellRootOfCutLtOne path hpathTotal resolution hresolution
            stage hcut) =
          1 - pathCellAbsorption path.1
            (partitionCut path resolution stage)
            (partitionCut path resolution (stage + 1)) := by
        unfold quittingRootAbsorptionMass at habsorption
        linarith
      rw [hcontinue, one_sub_pathCellAbsorption_of_boundaries path
        (partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
          (by omega) stage)
        (partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
          (by omega) (stage + 1)) hcut]
      field_simp [ne_of_gt (sub_pos.mpr hcut)]

theorem quittingRootSequenceClock_partitionDensityRoots
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {stage : ℕ}
    (hstage : stage ≤ partitionDensityCutoff path hpathTotal resolution
      (by omega : 1 ≤ resolution)) :
    quittingRootSequenceClock
        (partitionDensityRoots path hpathTotal resolution hresolution) stage =
      partitionCut path resolution stage := by
  unfold quittingRootSequenceClock
  rw [quittingRootSequenceSurvival_partitionDensityRoots path hpathTotal
    resolution hresolution hstage]
  ring

/-- The completed roots hit zero survival at the filler row. -/
def partitionDensityCertificate
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution) :
    QuittingFiniteRootSequenceAbsorption
      (partitionDensityRoots path hpathTotal resolution hresolution) where
  cutoff := partitionDensityCutoff path hpathTotal resolution (by omega)
  survival_zero := by
    rw [quittingRootSequenceSurvival_succ]
    apply mul_eq_zero_of_right
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_eq_zero
      (Finset.mem_univ (Classical.choice inferInstance))
    change ((partitionDensityRoots path hpathTotal resolution hresolution
      (partitionDensityCutoff path hpathTotal resolution (by omega))
      (Classical.choice inferInstance)) false).toReal = 0
    rw [partitionDensityRoots, quittingLateSureSoloRoots_cutoff_owner]
    norm_num

end GameTheory.QuittingAbsorptionPath

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology
open QuittingFiniteRootSequenceAbsorption

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An absorption path induced by one completely absorbing root sequence.
The definition records the exact clock, jump-set, and cumulative
coalition-mass identities independently of the Literature presentation. -/
def IsInducedByCompletelyAbsorbingRootSequence
    (path : AbsorptionPath (ι := ι)) : Prop :=
  ∃ roots : ℕ → ι → PMF Bool,
    IsCompletelyAbsorbing roots ∧
      pathTimes path.1 = {1} ∧
      pathJumps path.1 =
        {time | ∃ stage,
          time = quittingRootSequenceClock roots stage ∧
            quittingRootSequenceClock roots stage <
              quittingRootSequenceClock roots (stage + 1)} ∧
      ∀ stage,
        quittingRootSequenceClock roots stage <
            quittingRootSequenceClock roots (stage + 1) →
          ∀ coalition,
            path.1.value (quittingRootSequenceClock roots stage) coalition =
              quittingRootSequenceCumulativeCoalitionMass roots
                (stage + 1) coalition

omit [DecidableEq ι] in
theorem finiteRootSequenceAbsorption_isCompletelyAbsorbing
    {roots : ℕ → ι → PMF Bool}
    (certificate : QuittingFiniteRootSequenceAbsorption roots) :
    IsCompletelyAbsorbing roots := by
  unfold IsCompletelyAbsorbing
  have hzero : quittingSurvivalPrefix roots (certificate.cutoff + 1) = 0 := by
    calc
      quittingSurvivalPrefix roots (certificate.cutoff + 1) =
          quittingJointSurvivalWeight roots 0 (certificate.cutoff + 1) := by
        simpa using (quittingJointSurvivalWeight_eq_quittingSurvivalPrefix
          roots 0 (certificate.cutoff + 1)).symm
      _ = 0 := certificate.survival_zero
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨certificate.cutoff + 1, fun stage hstage ↦ ?_⟩
  have hle := quittingSurvivalPrefix_antitone roots hstage
  rw [hzero] at hle
  have hnonneg := quittingSurvivalPrefix_nonneg roots stage
  have heq : quittingSurvivalPrefix roots stage = 0 := le_antisymm hle hnonneg
  simp [heq, hε]

theorem finiteRootSequenceAbsorption_hasUnitBoundedTotalMass
    {roots : ℕ → ι → PMF Bool}
    (certificate : QuittingFiniteRootSequenceAbsorption roots) :
    HasUnitBoundedTotalMass certificate.absorptionPath := by
  intro time htime
  unfold pathTotal
  calc
    (∑ coalition, certificate.cadlagPath.value time coalition) ≤
        ∑ coalition,
          quittingRootSequenceCumulativeCoalitionMass roots
            (certificate.cutoff + 1) coalition :=
      Finset.sum_le_sum fun coalition _ ↦
        certificate.value_le_cumulative time coalition
    _ = quittingRootSequenceClock roots (certificate.cutoff + 1) :=
      sum_quittingRootSequenceCumulativeCoalitionMass roots _
    _ = 1 := by
      simp [quittingRootSequenceClock, certificate.survival_zero]

omit [DecidableEq ι] in
private theorem stage_le_cutoff_of_clock_lt_succ
    {roots : ℕ → ι → PMF Bool}
    (certificate : QuittingFiniteRootSequenceAbsorption roots)
    {stage : ℕ}
    (hpositive : quittingRootSequenceClock roots stage <
      quittingRootSequenceClock roots (stage + 1)) :
    stage ≤ certificate.cutoff := by
  by_contra hnot
  have hcutoffSucc : certificate.cutoff + 1 ≤ stage := by omega
  have hsurvivalStageLe : quittingRootSequenceSurvival roots stage ≤ 0 := by
    have hanti := antitone_quittingRootSequenceSurvival roots hcutoffSucc
    rw [certificate.survival_zero] at hanti
    exact hanti
  have hsurvivalStage : quittingRootSequenceSurvival roots stage = 0 :=
    le_antisymm hsurvivalStageLe
      (quittingRootSequenceSurvival_nonneg roots stage)
  have hsurvivalSuccLe :
      quittingRootSequenceSurvival roots (stage + 1) ≤ 0 := by
    exact (antitone_quittingRootSequenceSurvival roots
      (Nat.le_succ stage)).trans hsurvivalStageLe
  have hsurvivalSucc : quittingRootSequenceSurvival roots (stage + 1) = 0 :=
    le_antisymm hsurvivalSuccLe
      (quittingRootSequenceSurvival_nonneg roots (stage + 1))
  unfold quittingRootSequenceClock at hpositive
  rw [hsurvivalStage, hsurvivalSucc] at hpositive
  norm_num at hpositive

theorem finiteRootSequenceAbsorption_isInducedByCompletelyAbsorbingRootSequence
    {roots : ℕ → ι → PMF Bool}
    (certificate : QuittingFiniteRootSequenceAbsorption roots) :
    IsInducedByCompletelyAbsorbingRootSequence certificate.absorptionPath := by
  refine ⟨roots, finiteRootSequenceAbsorption_isCompletelyAbsorbing certificate,
    certificate.pathTimes_cadlagPath, ?_, ?_⟩
  · ext time
    constructor
    · intro htime
      obtain ⟨stage, _, htimeEq, hpositive, _⟩ :=
        certificate.exists_positive_source_stage htime
      exact ⟨stage, htimeEq, hpositive⟩
    · rintro ⟨stage, rfl, hpositive⟩
      have hstage := stage_le_cutoff_of_clock_lt_succ certificate hpositive
      have hsumPositive : 0 < ∑ coalition,
          quittingRootSequenceStageCoalitionMass roots stage coalition := by
        rw [sum_quittingRootSequenceStageCoalitionMass_eq_clock_sub]
        linarith
      obtain ⟨coalition, _, hmass⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero hsumPositive.ne'
      refine ⟨⟨quittingRootSequenceClock_nonneg roots stage,
        quittingRootSequenceClock_le_one roots stage⟩, coalition, ?_⟩
      change pathJump certificate.cadlagPath
        (quittingRootSequenceClock roots stage) coalition ≠ 0
      rw [certificate.pathJump_cadlagPath_at_positive_stage hstage hpositive]
      exact hmass
  · intro stage hpositive coalition
    exact certificate.value_cadlagPath_at_positive_stage
      (stage_le_cutoff_of_clock_lt_succ certificate hpositive) hpositive coalition

end GameTheory.QuittingAbsorptionPath

namespace GameTheory.QuittingAbsorptionPath

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem partitionCellRootOfCutLtOne_source
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (stage : ℕ) (hcut : partitionCut path resolution stage < 1) :
    (∃ (_hjump : partitionCut path resolution stage ∈ pathJumps path.1),
      partitionCut path resolution (stage + 1) =
          pathTotal path.1 (partitionCut path resolution stage) ∧
        partitionCellRootOfCutLtOne path hpathTotal resolution hresolution
            stage hcut =
          absorptionPathJumpRoot path (partitionCut path resolution stage)) ∨
    (∃ (cell : SmallPathCell path.1
          (partitionSmallCellError resolution))
        (packet : SmallCellProductization
          (partitionSmallCellError resolution)
          (pathCellLaw path.1 cell.start cell.stop)),
      cell.start = partitionCut path resolution stage ∧
        cell.stop = partitionCut path resolution (stage + 1) ∧
        partitionCellRootOfCutLtOne path hpathTotal resolution hresolution
          stage hcut = packet.quittingRoot) :=
  (Classical.choice <| nonempty_partitionCellRowData_of_cut_lt_one path
    hpathTotal resolution hresolution stage hcut).source

/-- The selected local row satisfies the corrected per-coordinate product
error estimate. -/
theorem partitionCellRootOfCutLtOne_coalition_coordinate_error
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (stage : ℕ) (hcut : partitionCut path resolution stage < 1)
    (coalition : Finset ι) (hcoalition : coalition.Nonempty) :
    |quittingRootCoalitionMass
          (partitionCellRootOfCutLtOne path hpathTotal resolution hresolution
            stage hcut) coalition -
        pathCellLaw path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) coalition| ≤
      akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError resolution *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hdataSource := partitionCellRootOfCutLtOne_source path hpathTotal
    resolution hresolution stage hcut
  have habsorptionNonneg : 0 ≤ pathCellAbsorption path.1
      (partitionCut path resolution stage)
      (partitionCut path resolution (stage + 1)) := by
    rw [← partitionCellRootOfCutLtOne_absorption_exact path hpathTotal
      resolution hresolution stage hcut]
    exact quittingRootAbsorptionMass_nonneg _
  rcases hdataSource with hcopied | hsmall
  · obtain ⟨hjump, hstopTotal, hroot⟩ := hcopied
    have hstartMem := partitionCut_mem_Icc path hpathTotal resolution
      hresolutionOne stage
    have hstopMem := partitionCut_mem_Icc path hpathTotal resolution
      hresolutionOne (stage + 1)
    have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
      hpathTotal resolution hresolutionOne stage
    have hstopBoundary := partitionCut_mem_partitionBoundaryTimes path
      hpathTotal resolution hresolutionOne (stage + 1)
    have hstartIco : partitionCut path resolution stage ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨hstartMem.1, hcut⟩
    have hstartStop : partitionCut path resolution stage <
        partitionCut path resolution (stage + 1) := by
      rw [partitionCut_succ]
      exact lt_nextPartitionCut path hpathTotal resolution hresolutionTwo
        hstartIco hstartBoundary
    have htotal : pathLeftTotal path.1
        (partitionCut path resolution (stage + 1)) =
          pathTotal path.1 (partitionCut path resolution stage) := by
      rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary,
        hstopTotal]
    have hlaw := pathCellLaw_eq_pathJump_div_of_copiedJump path hstartMem
      hstopMem hstartStop htotal ⟨coalition, hcoalition⟩
    have hmass := copiedJumpRoot_coalitionMass path hjump
      ⟨coalition, hcoalition⟩
    have hmass' : quittingRootCoalitionMass
        (absorptionPathJumpRoot path (partitionCut path resolution stage))
          coalition =
        pathJump path.1 (partitionCut path resolution stage)
          ⟨coalition, hcoalition⟩ /
            (1 - partitionCut path resolution stage) := by
      simpa using hmass
    have hlaw' : pathCellLaw path.1 (partitionCut path resolution stage)
        (partitionCut path resolution (stage + 1)) coalition =
        pathJump path.1 (partitionCut path resolution stage)
          ⟨coalition, hcoalition⟩ /
            (1 - partitionCut path resolution stage) := by
      simpa using hlaw
    rw [hroot, hmass', hlaw', sub_self, abs_zero]
    have hconstant : 0 ≤ akrsSmallCellCoordinateConstant ι := by
      unfold akrsSmallCellCoordinateConstant
      exact_mod_cast Nat.zero_le (2 ^ Fintype.card ι)
    exact mul_nonneg
      (mul_nonneg hconstant
        (partitionSmallCellError_pos resolution hresolution).le)
      habsorptionNonneg
  · obtain ⟨cell, packet, hcellStart, hcellStop, hroot⟩ := hsmall
    have hpacket := packet.quittingRoot_coalition_coordinate_error
      coalition hcoalition
    rw [cell.law_absorption] at hpacket
    simpa only [hroot, hcellStart, hcellStop] using hpacket

/-- Multiplying the normalized row error by exact survival yields the
unconditional coordinate increment error for one pre-cutoff stage. -/
theorem partitionDensityStageCoalitionMass_error
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {stage : ℕ}
    (hstage : stage < partitionDensityCutoff path hpathTotal resolution
      (by omega : 1 ≤ resolution))
    (coalition : {S : Finset ι // S.Nonempty}) :
    |quittingRootSequenceStageCoalitionMass
          (partitionDensityRoots path hpathTotal resolution hresolution)
          stage coalition -
        (path.1.leftValue (partitionCut path resolution (stage + 1)) coalition -
          path.1.leftValue (partitionCut path resolution stage) coalition)| ≤
      akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError resolution *
        (partitionCut path resolution (stage + 1) -
          partitionCut path resolution stage) := by
  let cut := partitionCut path resolution
  have hcut : cut stage < 1 :=
    partitionCut_lt_one_of_lt_partitionDensityCutoff path hpathTotal
      resolution (by omega) hstage
  have hrow := partitionCellRootOfCutLtOne_coalition_coordinate_error path
    hpathTotal resolution hresolution stage hcut coalition.1 coalition.2
  have hsurvival := quittingRootSequenceSurvival_partitionDensityRoots path
    hpathTotal resolution hresolution hstage.le
  have hroot :
      partitionDensityRoots path hpathTotal resolution hresolution stage =
        partitionCellRootOfCutLtOne path hpathTotal resolution hresolution
          stage hcut := by
    simpa only using partitionDensityRoots_of_lt_cutoff path hpathTotal
      resolution hresolution hstage
  rw [quittingRootSequenceStageCoalitionMass_eq_one_sub_clock_mul,
    quittingRootSequenceClock_partitionDensityRoots path hpathTotal resolution
      hresolution hstage.le, hroot]
  rw [pathCellLaw_nonempty] at hrow
  have hpositive : 0 < 1 - cut stage := sub_pos.mpr hcut
  have hscaled := mul_le_mul_of_nonneg_left hrow hpositive.le
  have hrewrite :
      (1 - cut stage) *
          (quittingRootCoalitionMass
              (partitionCellRootOfCutLtOne path hpathTotal resolution
                hresolution stage hcut) coalition.1 -
            (path.1.leftValue (cut (stage + 1)) coalition -
              path.1.leftValue (cut stage) coalition) / (1 - cut stage)) =
        quittingRootCoalitionMass
              (partitionCellRootOfCutLtOne path hpathTotal resolution
                hresolution stage hcut) coalition.1 * (1 - cut stage) -
          (path.1.leftValue (cut (stage + 1)) coalition -
            path.1.leftValue (cut stage) coalition) := by
    field_simp [hpositive.ne']
  have habsRewrite :
      |(1 - cut stage) *
          (quittingRootCoalitionMass
              (partitionCellRootOfCutLtOne path hpathTotal resolution
                hresolution stage hcut) coalition.1 -
            (path.1.leftValue (cut (stage + 1)) coalition -
              path.1.leftValue (cut stage) coalition) / (1 - cut stage))| =
        (1 - cut stage) *
          |quittingRootCoalitionMass
              (partitionCellRootOfCutLtOne path hpathTotal resolution
                hresolution stage hcut) coalition.1 -
            (path.1.leftValue (cut (stage + 1)) coalition -
              path.1.leftValue (cut stage) coalition) / (1 - cut stage)| := by
    rw [abs_mul, abs_of_nonneg hpositive.le]
  rw [← habsRewrite] at hscaled
  rw [hrewrite] at hscaled
  have hcell : (1 - cut stage) * pathCellAbsorption path.1
      (cut stage) (cut (stage + 1)) = cut (stage + 1) - cut stage := by
    unfold pathCellAbsorption
    rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path
      (partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
        (by omega) (stage + 1)),
      pathLeftTotal_eq_of_mem_partitionBoundaryTimes path
        (partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
          (by omega) stage)]
    field_simp [hpositive.ne']
    ring
  have hscaled' :
      |quittingRootCoalitionMass
            (partitionCellRootOfCutLtOne path hpathTotal resolution hresolution
              stage hcut) coalition.1 * (1 - cut stage) -
          (path.1.leftValue (cut (stage + 1)) coalition -
            path.1.leftValue (cut stage) coalition)| ≤
        akrsSmallCellCoordinateConstant ι *
          partitionSmallCellError resolution *
          ((1 - cut stage) * pathCellAbsorption path.1
            (cut stage) (cut (stage + 1))) := by
    calc
      _ ≤ (1 - cut stage) *
          (akrsSmallCellCoordinateConstant ι *
            partitionSmallCellError resolution *
              pathCellAbsorption path.1 (cut stage) (cut (stage + 1))) :=
        hscaled
      _ = _ := by ring
  rw [hcell] at hscaled'
  simpa only [cut, Nat.add_comm, mul_comm] using hscaled'

/-- The errors through the selected finite prefix telescope against the cut
increments, giving the published `2^|I|/(k-1)` bound. -/
theorem partitionDensityCumulativeCoalitionMass_error_of_le_cutoff
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (fuel : ℕ)
    (hfuel : fuel ≤ partitionDensityCutoff path hpathTotal resolution
      (by omega : 1 ≤ resolution))
    (coalition : {S : Finset ι // S.Nonempty}) :
    |quittingRootSequenceCumulativeCoalitionMass
          (partitionDensityRoots path hpathTotal resolution hresolution)
          fuel coalition -
        path.1.leftValue
          (partitionCut path resolution fuel) coalition| ≤
      akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError resolution *
        partitionCut path resolution fuel := by
  let cutoff := partitionDensityCutoff path hpathTotal resolution
    (by omega : 1 ≤ resolution)
  let cut := partitionCut path resolution
  let roots := partitionDensityRoots path hpathTotal resolution hresolution
  change |(∑ stage ∈ Finset.range fuel,
      quittingRootSequenceStageCoalitionMass roots stage coalition) -
        path.1.leftValue (cut fuel) coalition| ≤ _
  have htelescoping :
      (∑ stage ∈ Finset.range fuel,
        (path.1.leftValue (cut (stage + 1)) coalition -
          path.1.leftValue (cut stage) coalition)) =
        path.1.leftValue (cut fuel) coalition := by
    have hsum := Finset.sum_range_sub
      (fun stage ↦ path.1.leftValue (cut stage) coalition) fuel
    have hcutZero : cut 0 = 0 := by simp [cut]
    have hleftZero : path.1.leftValue (cut 0) coalition = 0 := by
      rw [hcutZero]
      exact path.1.left_zero coalition
    rw [hleftZero, sub_zero] at hsum
    simpa only using hsum
  rw [← htelescoping, ← Finset.sum_sub_distrib]
  calc
    |(∑ stage ∈ Finset.range fuel,
        (quittingRootSequenceStageCoalitionMass roots stage coalition -
          (path.1.leftValue (cut (stage + 1)) coalition -
            path.1.leftValue (cut stage) coalition)))| ≤
        ∑ stage ∈ Finset.range fuel,
          |quittingRootSequenceStageCoalitionMass roots stage coalition -
            (path.1.leftValue (cut (stage + 1)) coalition -
              path.1.leftValue (cut stage) coalition)| := by
      simpa only using Finset.abs_sum_le_sum_abs
        (fun stage ↦ quittingRootSequenceStageCoalitionMass roots stage
          coalition -
            (path.1.leftValue (cut (stage + 1)) coalition -
              path.1.leftValue (cut stage) coalition))
        (Finset.range fuel)
    _ ≤ ∑ stage ∈ Finset.range fuel,
        akrsSmallCellCoordinateConstant ι *
          partitionSmallCellError resolution *
          (cut (stage + 1) - cut stage) := by
      apply Finset.sum_le_sum
      intro stage hstage
      have hstageLt : stage < fuel := Finset.mem_range.mp hstage
      have hstageCutoff : stage < cutoff := hstageLt.trans_le hfuel
      simpa only [roots, cut, cutoff] using
        partitionDensityStageCoalitionMass_error path hpathTotal resolution
          hresolution hstageCutoff coalition
    _ = akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError resolution * cut fuel := by
      rw [← Finset.mul_sum]
      have hsum := Finset.sum_range_sub cut fuel
      rw [show cut 0 = 0 by simp [cut], sub_zero] at hsum
      rw [show (∑ stage ∈ Finset.range fuel,
          (cut (stage + 1) - cut stage)) = cut fuel by
        simpa only using hsum]

theorem partitionDensityCumulativeCoalitionMass_error
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (coalition : {S : Finset ι // S.Nonempty}) :
    |quittingRootSequenceCumulativeCoalitionMass
          (partitionDensityRoots path hpathTotal resolution hresolution)
          (partitionDensityCutoff path hpathTotal resolution (by omega))
          coalition -
        path.1.leftValue
          (partitionCut path resolution
            (partitionDensityCutoff path hpathTotal resolution (by omega)))
          coalition| ≤
      akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError resolution *
        partitionCut path resolution
          (partitionDensityCutoff path hpathTotal resolution (by omega)) := by
  exact partitionDensityCumulativeCoalitionMass_error_of_le_cutoff path
    hpathTotal resolution hresolution _ le_rfl coalition

end GameTheory.QuittingAbsorptionPath

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology
open QuittingFiniteRootSequenceAbsorption

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem exists_partitionCut_gt
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    {time : ℝ} (htime : time < 1) :
    ∃ stage, time < partitionCut path resolution stage := by
  have heventually : ∀ᶠ stage in atTop,
      time < partitionCut path resolution stage :=
    (tendsto_partitionCut_one path hpathTotal resolution hresolution).eventually
      (Ioi_mem_nhds htime)
  obtain ⟨stage, hstage⟩ := eventually_atTop.1 heventually
  exact ⟨stage, hstage stage le_rfl⟩

/-- First recursive partition cut lying strictly to the right of `time`. -/
def partitionTimeCrossing
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    (time : ℝ) (htime : time < 1) : ℕ :=
  Nat.find (exists_partitionCut_gt path hpathTotal resolution hresolution htime)

omit [Nonempty ι] in
theorem partitionTimeCrossing_spec
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    (time : ℝ) (htime : time < 1) :
    time < partitionCut path resolution
      (partitionTimeCrossing path hpathTotal resolution hresolution time htime) :=
  Nat.find_spec
    (exists_partitionCut_gt path hpathTotal resolution hresolution htime)

omit [Nonempty ι] in
theorem partitionCut_le_time_of_lt_partitionTimeCrossing
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    (time : ℝ) (htime : time < 1) {stage : ℕ}
    (hstage : stage <
      partitionTimeCrossing path hpathTotal resolution hresolution time htime) :
    partitionCut path resolution stage ≤ time := by
  exact not_lt.mp (Nat.find_min
    (exists_partitionCut_gt path hpathTotal resolution hresolution htime)
    hstage)

omit [Nonempty ι] in
theorem partitionTimeCrossing_pos
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    (time : ℝ) (htimeNonneg : 0 ≤ time) (htime : time < 1) :
    0 < partitionTimeCrossing path hpathTotal resolution hresolution time
      htime := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hcrossingZero :
      partitionTimeCrossing path hpathTotal resolution hresolution time htime =
        0 := hzero
  have hspec := partitionTimeCrossing_spec path hpathTotal resolution
    hresolution time htime
  rw [hcrossingZero] at hspec
  simp only [partitionCut] at hspec
  linarith

omit [Nonempty ι] in
theorem partitionTimeCrossing_le_partitionDensityCutoff
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    (time : ℝ) (htime : time < 1)
    (hthreshold : time < 1 - 1 / (resolution : ℝ)) :
    partitionTimeCrossing path hpathTotal resolution hresolution time htime ≤
      partitionDensityCutoff path hpathTotal resolution hresolution := by
  apply Nat.find_min'
    (exists_partitionCut_gt path hpathTotal resolution hresolution htime)
  exact hthreshold.trans
    (partitionDensityCutoff_spec path hpathTotal resolution hresolution)

/-- At a time before the completion cutoff, the finite step path is exactly
the cumulative law through the first partition cut strictly to its right. -/
theorem partitionDensityCertificate_value_eq_cumulative_crossing
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (time : ℝ) (htime : time ∈ Set.Ico (0 : ℝ) 1)
    (hthreshold : time < 1 - 1 / (resolution : ℝ))
    (coalition : {S : Finset ι // S.Nonempty}) :
    ((partitionDensityCertificate path hpathTotal resolution hresolution).absorptionPath).1.value
        time coalition =
      quittingRootSequenceCumulativeCoalitionMass
        (partitionDensityRoots path hpathTotal resolution hresolution)
        (partitionTimeCrossing path hpathTotal resolution (by omega) time
          htime.2) coalition := by
  let roots := partitionDensityRoots path hpathTotal resolution hresolution
  let certificate := partitionDensityCertificate path hpathTotal resolution
    hresolution
  let crossing := partitionTimeCrossing path hpathTotal resolution
    (by omega : 1 ≤ resolution) time htime.2
  let cutoff := partitionDensityCutoff path hpathTotal resolution
    (by omega : 1 ≤ resolution)
  have hcrossingCutoff : crossing ≤ cutoff :=
    partitionTimeCrossing_le_partitionDensityCutoff path hpathTotal resolution
      (by omega) time htime.2 hthreshold
  change certificate.value time coalition =
    quittingRootSequenceCumulativeCoalitionMass roots crossing coalition
  unfold QuittingFiniteRootSequenceAbsorption.value
    quittingRootSequenceCumulativeCoalitionMass
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext stage
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hstageCutoff, hclock⟩
      change stage < cutoff + 1 at hstageCutoff
      have hstageLe : stage ≤ cutoff := by omega
      have hclockEq := quittingRootSequenceClock_partitionDensityRoots path
        hpathTotal resolution hresolution hstageLe
      have hcutLe : partitionCut path resolution stage ≤ time := by
        simpa only [roots] using hclockEq.symm.trans_le hclock
      have hstageCrossing : stage < crossing := by
        by_contra hnot
        have hcrossingLe : crossing ≤ stage := not_lt.mp hnot
        have hmono := monotone_partitionCut path hpathTotal resolution
          (by omega : 1 ≤ resolution) hcrossingLe
        have hspec := partitionTimeCrossing_spec path hpathTotal resolution
          (by omega) time htime.2
        exact (not_le_of_gt hspec) (hmono.trans hcutLe)
      exact hstageCrossing
    · intro hstageCrossing
      have hstageCutoff : stage < cutoff + 1 := by omega
      have hstageLe : stage ≤ cutoff := by omega
      have hclockEq := quittingRootSequenceClock_partitionDensityRoots path
        hpathTotal resolution hresolution hstageLe
      have hcutLe := partitionCut_le_time_of_lt_partitionTimeCrossing path
        hpathTotal resolution (by omega) time htime.2 hstageCrossing
      exact ⟨hstageCutoff, by simpa only [roots] using hclockEq.trans_le hcutLe⟩
  · intro stage hstage
    simp only [Finset.mem_range] at hstage
    rfl

omit [Nonempty ι] in
/-- At a continuity time, the reference left value at the first cut to the
right is either exact (copied large jump) or lies before the mesh probe based
at that time. -/
theorem leftValue_partitionTimeCrossing_eq_or_cut_le_probe
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    (time : ℝ) (htime : time ∈ Set.Ico (0 : ℝ) 1)
    (hnotJump : time ∉ pathJumps path.1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    path.1.leftValue
          (partitionCut path resolution
            (partitionTimeCrossing path hpathTotal resolution (by omega)
              time htime.2)) coalition =
        path.1.value time coalition ∨
      partitionCut path resolution
          (partitionTimeCrossing path hpathTotal resolution (by omega)
            time htime.2) ≤
        partitionProbe resolution time := by
  let crossing := partitionTimeCrossing path hpathTotal resolution
    (by omega : 1 ≤ resolution) time htime.2
  change path.1.leftValue (partitionCut path resolution crossing) coalition =
      path.1.value time coalition ∨
    partitionCut path resolution crossing ≤ partitionProbe resolution time
  have hcrossingPos := partitionTimeCrossing_pos path hpathTotal resolution
    (by omega : 1 ≤ resolution) time htime.1 htime.2
  change 0 < crossing at hcrossingPos
  obtain ⟨stage, hcrossing⟩ := Nat.exists_eq_succ_of_ne_zero
    hcrossingPos.ne'
  have hcrossingEq : crossing = stage + 1 := by omega
  have hstageCrossing : stage < crossing := by omega
  have hstartLe : partitionCut path resolution stage ≤ time :=
    partitionCut_le_time_of_lt_partitionTimeCrossing path hpathTotal
      resolution (by omega) time htime.2 hstageCrossing
  have hstopGt : time < partitionCut path resolution (stage + 1) := by
    rw [← hcrossingEq]
    exact partitionTimeCrossing_spec path hpathTotal resolution
      (by omega) time htime.2
  have hstartMem := partitionCut_mem_Icc path hpathTotal resolution
    (by omega : 1 ≤ resolution) stage
  have hstopMem := partitionCut_mem_Icc path hpathTotal resolution
    (by omega : 1 ≤ resolution) (stage + 1)
  have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution (by omega : 1 ≤ resolution) stage
  have hstopBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution (by omega : 1 ≤ resolution) (stage + 1)
  by_cases hlarge : partitionProbe resolution
      (partitionCut path resolution stage) <
        pathTotal path.1 (partitionCut path resolution stage)
  · apply Or.inl
    have hjump : partitionCut path resolution stage ∈ pathJumps path.1 :=
      mem_pathJumps_of_probe_lt_pathTotal_of_boundary path resolution
        hstartBoundary hlarge
    have hstartLt : partitionCut path resolution stage < time :=
      lt_of_le_of_ne hstartLe (fun heq ↦ hnotJump (heq ▸ hjump))
    have hstopTotal : partitionCut path resolution (stage + 1) =
        pathTotal path.1 (partitionCut path resolution stage) := by
      rw [partitionCut_succ]
      exact nextPartitionCut_eq_pathTotal_of_probe_lt path resolution _ hlarge
    have hcoordinateLe (terminal : {S : Finset ι // S.Nonempty}) :
        path.1.value (partitionCut path resolution stage) terminal ≤
          path.1.leftValue (partitionCut path resolution (stage + 1))
            terminal :=
      path.1.value_le_leftValue_of_lt terminal hstartMem hstopMem
        (hstartLt.trans hstopGt)
    have hsumEq :
        (∑ terminal,
          path.1.value (partitionCut path resolution stage) terminal) =
        ∑ terminal,
          path.1.leftValue (partitionCut path resolution (stage + 1))
            terminal := by
      change pathTotal path.1 (partitionCut path resolution stage) =
        pathLeftTotal path.1 (partitionCut path resolution (stage + 1))
      rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary,
        hstopTotal]
    have hcoordinateEq :
        path.1.value (partitionCut path resolution stage) coalition =
          path.1.leftValue (partitionCut path resolution (stage + 1))
            coalition :=
      (Finset.sum_eq_sum_iff_of_le fun terminal _ ↦
        hcoordinateLe terminal).mp hsumEq coalition (Finset.mem_univ coalition)
    rw [hcrossingEq]
    apply le_antisymm
    · rw [← hcoordinateEq]
      exact path.1.monotone coalition hstartMem
        ⟨htime.1, htime.2.le⟩ hstartLe
    · exact path.1.value_le_leftValue_of_lt coalition
        ⟨htime.1, htime.2.le⟩ hstopMem hstopGt
  · apply Or.inr
    have hsmall : pathTotal path.1 (partitionCut path resolution stage) ≤
        partitionProbe resolution (partitionCut path resolution stage) :=
      not_lt.mp hlarge
    rw [hcrossingEq, partitionCut_succ]
    exact (nextPartitionCut_le_probe_of_pathTotal_le path resolution _ hsmall).trans
      (partitionProbe_mono resolution (by omega) hstartLe)

omit [Nonempty ι] in
/-- The reference coordinate error is controlled by the target path's
right-continuity modulus at the published mesh probe. -/
theorem abs_leftValue_partitionTimeCrossing_sub_value_le
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    (time : ℝ) (htime : time ∈ Set.Ico (0 : ℝ) 1)
    (hnotJump : time ∉ pathJumps path.1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    |path.1.leftValue
          (partitionCut path resolution
            (partitionTimeCrossing path hpathTotal resolution (by omega)
              time htime.2)) coalition -
        path.1.value time coalition| ≤
      path.1.value (partitionProbe resolution time) coalition -
        path.1.value time coalition := by
  let stop := partitionCut path resolution
    (partitionTimeCrossing path hpathTotal resolution
      (by omega : 1 ≤ resolution) time htime.2)
  have hstopMem := partitionCut_mem_Icc path hpathTotal resolution
    (by omega : 1 ≤ resolution)
    (partitionTimeCrossing path hpathTotal resolution (by omega) time htime.2)
  have hstopGt : time < stop :=
    partitionTimeCrossing_spec path hpathTotal resolution (by omega) time htime.2
  have hprobe := partitionProbe_mem_Ioo resolution hresolution htime
  have hrightNonneg : 0 ≤
      path.1.value (partitionProbe resolution time) coalition -
        path.1.value time coalition :=
    sub_nonneg.mpr <| path.1.monotone coalition
      ⟨htime.1, htime.2.le⟩
      ⟨htime.1.trans hprobe.1.le, hprobe.2.le⟩ hprobe.1.le
  rcases leftValue_partitionTimeCrossing_eq_or_cut_le_probe path hpathTotal
      resolution hresolution time htime hnotJump coalition with heq | hstopProbe
  · rw [heq, sub_self, abs_zero]
    exact hrightNonneg
  · have hlower : path.1.value time coalition ≤
        path.1.leftValue stop coalition :=
      path.1.value_le_leftValue_of_lt coalition ⟨htime.1, htime.2.le⟩
        hstopMem hstopGt
    have hupper : path.1.leftValue stop coalition ≤
        path.1.value (partitionProbe resolution time) coalition :=
      (path.1.leftValue_le_value coalition hstopMem).trans <|
        path.1.monotone coalition hstopMem
          ⟨htime.1.trans hprobe.1.le, hprobe.2.le⟩
          hstopProbe
    rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
    linarith

/-- Resolution schedule used by the density sequence. -/
def partitionDensityResolution (index : ℕ) : ℕ := index + 3

omit [Nonempty ι] in
theorem tendsto_one_div_partitionDensityResolution :
    Tendsto (fun index : ℕ ↦ 1 / (partitionDensityResolution index : ℝ))
      atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 2)
  convert h using 1
  funext index
  simp only [Function.comp_apply, partitionDensityResolution, Nat.cast_add,
    Nat.cast_ofNat]
  congr 1
  ring

omit [Nonempty ι] in
theorem tendsto_partitionSmallCellError_partitionDensityResolution :
    Tendsto (fun index : ℕ ↦
      partitionSmallCellError (partitionDensityResolution index))
      atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  funext index
  simp only [Function.comp_apply, partitionSmallCellError,
    partitionDensityResolution, Nat.cast_add, Nat.cast_ofNat]
  congr 1
  ring

/-- Canonical finite absorbing approximation at one scheduled resolution. -/
def partitionDensityApproximant
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : HasUnitBoundedTotalMass path) (index : ℕ) :
    AbsorptionPath (ι := ι) :=
  (partitionDensityCertificate path hpathTotal
    (partitionDensityResolution index)
      (by simp [partitionDensityResolution])).absorptionPath

/-- Pointwise error bound before terminal time: productization error plus
the target path's right-continuity modulus at the mesh probe. -/
theorem abs_partitionDensityApproximant_sub_value_le
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : HasUnitBoundedTotalMass path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (time : ℝ) (htime : time ∈ Set.Ico (0 : ℝ) 1)
    (hnotJump : time ∉ pathJumps path.1)
    (hthreshold : time < 1 - 1 / (resolution : ℝ))
    (coalition : {S : Finset ι // S.Nonempty}) :
    |(QuittingFiniteRootSequenceAbsorption.absorptionPath
          (partitionDensityCertificate path hpathTotal resolution hresolution)).1.value
          time coalition -
        path.1.value time coalition| ≤
      akrsSmallCellCoordinateConstant ι *
          partitionSmallCellError resolution +
        (path.1.value (partitionProbe resolution time) coalition -
          path.1.value time coalition) := by
  let crossing := partitionTimeCrossing path hpathTotal resolution
    (by omega : 1 ≤ resolution) time htime.2
  let approximant := partitionDensityCertificate path hpathTotal resolution
    hresolution
  have hcrossingCutoff :=
    partitionTimeCrossing_le_partitionDensityCutoff path hpathTotal resolution
      (by omega : 1 ≤ resolution) time htime.2 hthreshold
  have hvalue := partitionDensityCertificate_value_eq_cumulative_crossing path
    hpathTotal resolution hresolution time htime hthreshold coalition
  have hcumulative :=
    partitionDensityCumulativeCoalitionMass_error_of_le_cutoff path hpathTotal
      resolution hresolution crossing hcrossingCutoff coalition
  have hreference := abs_leftValue_partitionTimeCrossing_sub_value_le path
    hpathTotal resolution (by omega) time htime hnotJump coalition
  have hcutLe : partitionCut path resolution crossing ≤ 1 :=
    (partitionCut_mem_Icc path hpathTotal resolution (by omega) crossing).2
  have hcoefficientNonneg : 0 ≤
      akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError resolution := by
    exact mul_nonneg (by
      unfold akrsSmallCellCoordinateConstant
      exact_mod_cast Nat.zero_le (2 ^ Fintype.card ι))
      (partitionSmallCellError_pos resolution hresolution).le
  have hproductLe :
      akrsSmallCellCoordinateConstant ι *
          partitionSmallCellError resolution *
          partitionCut path resolution crossing ≤
        akrsSmallCellCoordinateConstant ι *
          partitionSmallCellError resolution := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hcutLe hcoefficientNonneg
  change |approximant.absorptionPath.1.value time coalition -
      path.1.value time coalition| ≤ _
  rw [hvalue]
  calc
    |quittingRootSequenceCumulativeCoalitionMass
          (partitionDensityRoots path hpathTotal resolution hresolution)
          crossing coalition - path.1.value time coalition| ≤
        |quittingRootSequenceCumulativeCoalitionMass
            (partitionDensityRoots path hpathTotal resolution hresolution)
            crossing coalition -
          path.1.leftValue (partitionCut path resolution crossing) coalition| +
        |path.1.leftValue (partitionCut path resolution crossing) coalition -
          path.1.value time coalition| := abs_sub_le _ _ _
    _ ≤ akrsSmallCellCoordinateConstant ι *
          partitionSmallCellError resolution *
          partitionCut path resolution crossing +
        (path.1.value (partitionProbe resolution time) coalition -
          path.1.value time coalition) := add_le_add hcumulative hreference
    _ ≤ _ := add_le_add hproductLe le_rfl

theorem tendsto_partitionDensityApproximant_value_of_lt_one
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : HasUnitBoundedTotalMass path)
    (time : ℝ) (htime : time ∈ Set.Ico (0 : ℝ) 1)
    (hnotJump : time ∉ pathJumps path.1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun index ↦
      (partitionDensityApproximant path hpathTotal index).1.value time
        coalition) atTop (nhds (path.1.value time coalition)) := by
  have hinv : Tendsto (fun index : ℕ ↦
      1 / (partitionDensityResolution index : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_partitionDensityResolution
  have hthresholdTendsto : Tendsto (fun index : ℕ ↦
      1 - 1 / (partitionDensityResolution index : ℝ)) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hinv using 1
    all_goals norm_num
  have hthreshold : ∀ᶠ index in atTop,
      time < 1 - 1 / (partitionDensityResolution index : ℝ) :=
    hthresholdTendsto.eventually (Ioi_mem_nhds htime.2)
  have hprobeTendsto : Tendsto (fun index ↦
      partitionProbe (partitionDensityResolution index) time) atTop
      (nhds time) := by
    have hgap : Tendsto (fun index : ℕ ↦
        (1 - time) * (1 / (partitionDensityResolution index : ℝ)))
        atTop (nhds 0) := by
      convert (tendsto_const_nhds.mul hinv) using 1
      all_goals ring
    simpa [partitionProbe, div_eq_mul_inv] using
      tendsto_const_nhds.add hgap
  have hprobeWithin : Tendsto (fun index ↦
      partitionProbe (partitionDensityResolution index) time) atTop
      (nhdsWithin time (Set.Icc time 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hprobeTendsto, Filter.Eventually.of_forall fun index ↦ ?_⟩
    have hprobe := partitionProbe_mem_Ioo
      (partitionDensityResolution index) (by simp [partitionDensityResolution])
      htime
    exact ⟨hprobe.1.le, hprobe.2.le⟩
  have hvalueProbe : Tendsto (fun index ↦
      path.1.value (partitionProbe (partitionDensityResolution index) time)
        coalition) atTop (nhds (path.1.value time coalition)) :=
    (path.1.right_continuous coalition time ⟨htime.1, htime.2.le⟩).comp
      hprobeWithin
  have hmodulus : Tendsto (fun index ↦
      path.1.value (partitionProbe (partitionDensityResolution index) time)
          coalition - path.1.value time coalition) atTop (nhds 0) := by
    convert hvalueProbe.sub tendsto_const_nhds using 1
    all_goals ring
  have hproductization : Tendsto (fun index : ℕ ↦
      akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError (partitionDensityResolution index))
      atTop (nhds 0) := by
    have herror : Tendsto (fun index : ℕ ↦
        partitionSmallCellError (partitionDensityResolution index))
        atTop (nhds 0) :=
      tendsto_partitionSmallCellError_partitionDensityResolution
    convert herror.const_mul (akrsSmallCellCoordinateConstant ι) using 1
    all_goals ring
  have hboundTendsto : Tendsto (fun index : ℕ ↦
      akrsSmallCellCoordinateConstant ι *
          partitionSmallCellError (partitionDensityResolution index) +
        (path.1.value
            (partitionProbe (partitionDensityResolution index) time) coalition -
          path.1.value time coalition)) atTop (nhds 0) := by
    simpa only [zero_add] using hproductization.add hmodulus
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    (hthreshold.mono fun index hindex ↦ ?_)
    hboundTendsto
  rw [Real.norm_eq_abs]
  exact abs_partitionDensityApproximant_sub_value_le path hpathTotal
    (partitionDensityResolution index)
      (by simp [partitionDensityResolution]) time htime hnotJump hindex coalition

omit [Nonempty ι] in
theorem tendsto_leftValue_partitionDensityCutoff
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : HasUnitBoundedTotalMass path)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun index ↦ path.1.leftValue
      (partitionCut path (partitionDensityResolution index)
        (partitionDensityCutoff path hpathTotal
          (partitionDensityResolution index) (by
            simp [partitionDensityResolution]))) coalition)
      atTop (nhds (path.1.value 1 coalition)) := by
  have hnotJump : (1 : ℝ) ∉ pathJumps path.1 :=
    one_not_mem_pathJumps_of_unitBoundedTotalMass path hpathTotal
  let threshold := fun index : ℕ ↦
    1 - 1 / (partitionDensityResolution index : ℝ)
  let cut := fun index : ℕ ↦
    partitionCut path (partitionDensityResolution index)
      (partitionDensityCutoff path hpathTotal
        (partitionDensityResolution index) (by
          simp [partitionDensityResolution]))
  have hinv : Tendsto (fun index : ℕ ↦
      1 / (partitionDensityResolution index : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_partitionDensityResolution
  have hthreshold : Tendsto threshold atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hinv using 1
    all_goals norm_num
  have hthresholdWithin : Tendsto threshold atTop
      (nhdsWithin 1 (Set.Icc (0 : ℝ) 1 \ {1})) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hthreshold, Filter.Eventually.of_forall fun index ↦ ?_⟩
    have hresolution : (1 : ℝ) ≤ partitionDensityResolution index := by
      exact_mod_cast (show 1 ≤ partitionDensityResolution index by
        simp [partitionDensityResolution])
    have hinvPos : (0 : ℝ) < 1 / partitionDensityResolution index :=
      one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hresolution)
    have hinvLe : (1 : ℝ) / partitionDensityResolution index ≤ 1 :=
      (div_le_one (lt_of_lt_of_le zero_lt_one hresolution)).2 hresolution
    have hthresholdNonneg : 0 ≤ threshold index := by
      dsimp only [threshold]
      linarith
    exact ⟨⟨hthresholdNonneg, (sub_lt_self 1 hinvPos).le⟩,
      by simp only [Set.mem_singleton_iff]; exact (sub_lt_self 1 hinvPos).ne⟩
  have hvalueThreshold : Tendsto (fun index ↦
      path.1.value (threshold index) coalition) atTop
      (nhds (path.1.leftValue 1 coalition)) :=
    (path.1.left_limit coalition 1 (by norm_num)).comp hthresholdWithin
  have honeEq : path.1.leftValue 1 coalition = path.1.value 1 coalition := by
    have hjumpZero : pathJump path.1 1 coalition = 0 := by
      by_contra hne
      exact hnotJump ⟨by norm_num, coalition, hne⟩
    unfold pathJump at hjumpZero
    linarith
  rw [honeEq] at hvalueThreshold
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hvalueThreshold
    tendsto_const_nhds
  · exact Filter.Eventually.of_forall fun index ↦ by
      apply path.1.value_le_leftValue_of_lt coalition
      · have hresolution : (1 : ℝ) ≤ partitionDensityResolution index := by
          exact_mod_cast (show 1 ≤ partitionDensityResolution index by
            simp [partitionDensityResolution])
        have hinvPos : (0 : ℝ) < 1 / partitionDensityResolution index :=
          one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hresolution)
        have hinvLe : (1 : ℝ) / partitionDensityResolution index ≤ 1 :=
          (div_le_one (lt_of_lt_of_le zero_lt_one hresolution)).2 hresolution
        exact ⟨by dsimp only [threshold]; linarith,
          (sub_lt_self 1 hinvPos).le⟩
      · exact partitionCut_mem_Icc path hpathTotal
          (partitionDensityResolution index) (by
            simp [partitionDensityResolution]) _
      · exact partitionDensityCutoff_spec path hpathTotal
          (partitionDensityResolution index) (by
            simp [partitionDensityResolution])
  · exact Filter.Eventually.of_forall fun index ↦
      (path.1.leftValue_le_value coalition
        (partitionCut_mem_Icc path hpathTotal
          (partitionDensityResolution index) (by
            simp [partitionDensityResolution]) _)).trans
      (path.1.monotone coalition
        (partitionCut_mem_Icc path hpathTotal
          (partitionDensityResolution index) (by
            simp [partitionDensityResolution]) _)
        (by norm_num)
        (partitionCut_mem_Icc path hpathTotal
          (partitionDensityResolution index) (by
            simp [partitionDensityResolution]) _).2)

theorem tendsto_partitionDensityApproximant_value_one
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : HasUnitBoundedTotalMass path)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun index : ℕ ↦
      (partitionDensityApproximant path hpathTotal index).1.value 1 coalition)
      atTop (nhds (path.1.value 1 coalition)) := by
  let resolution := partitionDensityResolution
  let cutoff := fun index : ℕ ↦ partitionDensityCutoff path hpathTotal
    (resolution index) (by simp [resolution, partitionDensityResolution])
  let roots := fun index : ℕ ↦ partitionDensityRoots path hpathTotal
    (resolution index) (by simp [resolution, partitionDensityResolution])
  let prefixMass := fun index : ℕ ↦
    quittingRootSequenceCumulativeCoalitionMass
    (roots index) (cutoff index) coalition
  let reference := fun index : ℕ ↦ path.1.leftValue
    (partitionCut path (resolution index) (cutoff index)) coalition
  let filler := fun index : ℕ ↦ quittingRootSequenceStageCoalitionMass
    (roots index) (cutoff index) coalition
  have hreference : Tendsto reference atTop
      (nhds (path.1.value 1 coalition)) := by
    simpa only [reference, resolution, cutoff] using
      tendsto_leftValue_partitionDensityCutoff path hpathTotal coalition
  have herror : Tendsto (fun index : ℕ ↦
      partitionSmallCellError (partitionDensityResolution index))
      atTop (nhds 0) :=
    tendsto_partitionSmallCellError_partitionDensityResolution
  have hcoefficient : Tendsto (fun index : ℕ ↦
      akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError (resolution index)) atTop (nhds 0) := by
    convert herror.const_mul (akrsSmallCellCoordinateConstant ι) using 1
    all_goals ring
  have hprefixDiff : Tendsto (fun index : ℕ ↦
      prefixMass index - reference index)
      atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun index ↦
      akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError (resolution index))
    · exact Filter.Eventually.of_forall fun index ↦ by
        have hbound := partitionDensityCumulativeCoalitionMass_error path
          hpathTotal (resolution index)
          (by simp [resolution, partitionDensityResolution]) coalition
        have hcutLe := (partitionCut_mem_Icc path hpathTotal
          (resolution index) (by simp [resolution, partitionDensityResolution])
          (cutoff index)).2
        have hnonneg : 0 ≤ akrsSmallCellCoordinateConstant ι *
            partitionSmallCellError (resolution index) := by
          exact mul_nonneg (by
            unfold akrsSmallCellCoordinateConstant
            exact_mod_cast Nat.zero_le (2 ^ Fintype.card ι))
            (partitionSmallCellError_pos (resolution index)
              (by simp [resolution, partitionDensityResolution])).le
        have hbound' := hbound.trans (by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hcutLe hnonneg)
        simpa only [Real.norm_eq_abs, prefixMass, reference, roots, cutoff,
          resolution] using hbound'
    · exact hcoefficient
  have hprefix : Tendsto prefixMass atTop
      (nhds (path.1.value 1 coalition)) := by
    convert hprefixDiff.add hreference using 1
    all_goals ring
  have hinv : Tendsto (fun index : ℕ ↦ 1 / (resolution index : ℝ))
      atTop (nhds 0) := tendsto_one_div_partitionDensityResolution
  have hfiller : Tendsto filler atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun index ↦
        quittingRootSequenceStageCoalitionMass_nonneg
          (roots index) (cutoff index) coalition)
      (Filter.Eventually.of_forall fun index ↦ ?_) hinv
    have hsingle : filler index ≤ ∑ terminal,
        quittingRootSequenceStageCoalitionMass
          (roots index) (cutoff index) terminal :=
      Finset.single_le_sum (fun terminal _ ↦
        quittingRootSequenceStageCoalitionMass_nonneg
          (roots index) (cutoff index) terminal) (Finset.mem_univ coalition)
    rw [sum_quittingRootSequenceStageCoalitionMass_eq_clock_sub] at hsingle
    have hclock := quittingRootSequenceClock_partitionDensityRoots path
      hpathTotal (resolution index)
      (by simp [resolution, partitionDensityResolution]) le_rfl
    have hnext : quittingRootSequenceClock (roots index) (cutoff index + 1) = 1 := by
      have hzero := (partitionDensityCertificate path hpathTotal
        (resolution index) (by
          simp [resolution, partitionDensityResolution])).survival_zero
      change quittingRootSequenceSurvival (roots index) (cutoff index + 1) = 0
        at hzero
      unfold quittingRootSequenceClock
      rw [hzero]
      ring
    rw [hclock, hnext] at hsingle
    exact le_trans hsingle
      (one_sub_partitionCut_partitionDensityCutoff_lt path hpathTotal
        (resolution index)
        (by simp [resolution, partitionDensityResolution])).le
  have hfinal : Tendsto (fun index : ℕ ↦
      prefixMass index + filler index) atTop
      (nhds (path.1.value 1 coalition)) := by
    simpa only [add_zero] using hprefix.add hfiller
  convert hfinal using 1
  funext index
  change (partitionDensityCertificate path hpathTotal
    (resolution index) (by
      simp [resolution, partitionDensityResolution])).cadlagPath.value 1
        coalition = prefixMass index + filler index
  rw [QuittingFiniteRootSequenceAbsorption.value_cadlagPath_one,
    quittingRootSequenceCumulativeCoalitionMass_succ]
  rfl

theorem weaklyConverges_partitionDensityApproximant
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : HasUnitBoundedTotalMass path) :
    WeaklyConvergesAbsorptionPaths
      (partitionDensityApproximant path hpathTotal) path := by
  intro time htime hnotJump
  apply tendsto_pi_nhds.mpr
  intro coalition
  rcases htime.2.eq_or_lt with htimeOne | htimeLt
  · subst time
    exact tendsto_partitionDensityApproximant_value_one path hpathTotal
      coalition
  · exact tendsto_partitionDensityApproximant_value_of_lt_one path
      hpathTotal time ⟨htime.1, htimeLt⟩ hnotJump coalition

theorem partitionDensityApproximant_isInduced
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : HasUnitBoundedTotalMass path) (index : ℕ) :
    IsInducedByCompletelyAbsorbingRootSequence
      (partitionDensityApproximant path hpathTotal index) := by
  exact finiteRootSequenceAbsorption_isInducedByCompletelyAbsorbingRootSequence
    (partitionDensityCertificate path hpathTotal
      (partitionDensityResolution index) (by
        simp [partitionDensityResolution]))

theorem partitionDensityApproximant_hasUnitBoundedTotalMass
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : HasUnitBoundedTotalMass path) (index : ℕ) :
    HasUnitBoundedTotalMass
      (partitionDensityApproximant path hpathTotal index) := by
  exact finiteRootSequenceAbsorption_hasUnitBoundedTotalMass
    (partitionDensityCertificate path hpathTotal
      (partitionDensityResolution index) (by
        simp [partitionDensityResolution]))

/-- Constructive nonempty-player form of corrected journal Proposition 4.8. -/
private theorem
    unitBoundedAbsorptionPaths_are_weakLimits_of_completelyAbsorbingRootSequences_of_nonempty :
    ∀ path : AbsorptionPath (ι := ι),
      HasUnitBoundedTotalMass path →
        ∃ approximants : ℕ → AbsorptionPath (ι := ι),
          (∀ index,
            IsInducedByCompletelyAbsorbingRootSequence (approximants index)) ∧
          (∀ index, HasUnitBoundedTotalMass (approximants index)) ∧
          WeaklyConvergesAbsorptionPaths approximants path := by
  intro path hpathTotal
  exact ⟨partitionDensityApproximant path hpathTotal,
    partitionDensityApproximant_isInduced path hpathTotal,
    partitionDensityApproximant_hasUnitBoundedTotalMass path hpathTotal,
    weaklyConverges_partitionDensityApproximant path hpathTotal⟩

omit [Nonempty ι] in
/-- Corrected unit-bounded form of journal Proposition 4.8, with no unnecessary
nonemptiness assumption on the finite player type. -/
theorem unitBoundedAbsorptionPaths_are_weakLimits_of_completelyAbsorbingRootSequences :
    ∀ path : AbsorptionPath (ι := ι),
      HasUnitBoundedTotalMass path →
        ∃ approximants : ℕ → AbsorptionPath (ι := ι),
          (∀ index,
            IsInducedByCompletelyAbsorbingRootSequence (approximants index)) ∧
          (∀ index, HasUnitBoundedTotalMass (approximants index)) ∧
          WeaklyConvergesAbsorptionPaths approximants path := by
  intro path hpathTotal
  letI : Nonempty ι := by
    classical
    by_contra hempty
    haveI : IsEmpty ι := ⟨fun player ↦ hempty ⟨player⟩⟩
    haveI : IsEmpty {S : Finset ι // S.Nonempty} :=
      ⟨fun coalition ↦ by
        obtain ⟨player, _⟩ := coalition.2
        exact isEmptyElim player⟩
    have hclock := path.property.1 1
      (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
    unfold pathTotal at hclock
    norm_num at hclock
  exact unitBoundedAbsorptionPaths_are_weakLimits_of_completelyAbsorbingRootSequences_of_nonempty
    path hpathTotal

end GameTheory.QuittingAbsorptionPath
