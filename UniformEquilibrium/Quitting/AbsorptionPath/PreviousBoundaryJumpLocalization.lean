/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.WeakPathConvergence

/-!
# The last path boundary before a clock probe

The compactness proof localizes a source jump by taking the last jump-or-clock
boundary no later than a right probe.  If total mass at the probe is strictly
above its clock, this last boundary is a jump and the path is constant from
its post-jump value through the probe.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The supremum of all literal path boundaries no later than a clock probe. -/
def previousPartitionBoundary
    (path : AbsorptionPath (ι := ι)) (probe : ℝ) : ℝ :=
  sSup (partitionBoundaryTimes path ∩ Iic probe)

/-- The last boundary before a probe in the unit interval is itself a literal
boundary and lies between zero and the probe. -/
theorem previousPartitionBoundary_mem_and_le
    (path : AbsorptionPath (ι := ι))
    {probe : ℝ} (hprobe : probe ∈ Icc (0 : ℝ) 1) :
    previousPartitionBoundary path probe ∈ partitionBoundaryTimes path ∧
      0 ≤ previousPartitionBoundary path probe ∧
      previousPartitionBoundary path probe ≤ probe := by
  let source := partitionBoundaryTimes path ∩ Iic probe
  have hzero : (0 : ℝ) ∈ source :=
    ⟨zero_mem_partitionBoundaryTimes path, hprobe.1⟩
  have hnonempty : source.Nonempty := ⟨0, hzero⟩
  have hbdd : BddAbove source := ⟨probe, fun _ hpoint ↦ hpoint.2⟩
  have hlower : 0 ≤ sSup source := le_csSup hbdd hzero
  have hupper : sSup source ≤ probe :=
    csSup_le hnonempty fun _ hpoint ↦ hpoint.2
  have hmem : sSup source ∈ Icc (0 : ℝ) 1 :=
    ⟨hlower, hupper.trans hprobe.2⟩
  exact ⟨csSup_mem_partitionBoundaryTimes path hnonempty
    (fun _ hpoint ↦ hpoint.1) hbdd hmem, hlower, hupper⟩

/-- No literal boundary lies strictly after the last boundary and at or before
the probe. -/
theorem not_mem_partitionBoundaryTimes_of_previousPartitionBoundary_lt
    (path : AbsorptionPath (ι := ι))
    {probe point : ℝ}
    (hpreviousPoint : previousPartitionBoundary path probe < point)
    (hpointProbe : point ≤ probe) :
    point ∉ partitionBoundaryTimes path := by
  intro hpoint
  let source := partitionBoundaryTimes path ∩ Iic probe
  have hsource : point ∈ source := ⟨hpoint, hpointProbe⟩
  have hbdd : BddAbove source := ⟨probe, fun _ hmem ↦ hmem.2⟩
  have hle : point ≤ sSup source := le_csSup hbdd hsource
  exact (not_le_of_gt hpreviousPoint) hle

/-- If a probe lies strictly below its path total, the last boundary before
the probe is a jump and every post-jump coordinate equals its value at the
probe. -/
theorem previousPartitionBoundary_mem_pathJumps_and_value_eq
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path)
    {probe : ℝ} (hprobe : probe ∈ Icc (0 : ℝ) 1)
    (hprobeTotal : probe < pathTotal path.1 probe) :
    previousPartitionBoundary path probe ∈ pathJumps path.1 ∧
      ∀ coalition,
        path.1.value (previousPartitionBoundary path probe) coalition =
          path.1.value probe coalition := by
  let previous := previousPartitionBoundary path probe
  obtain ⟨hpreviousBoundary, hpreviousNonneg, hpreviousLe⟩ :=
    previousPartitionBoundary_mem_and_le path hprobe
  have hpreviousMem : previous ∈ Icc (0 : ℝ) 1 :=
    ⟨hpreviousNonneg, hpreviousLe.trans hprobe.2⟩
  rcases hpreviousLe.eq_or_lt with hpreviousEq | hpreviousLt
  · have hpreviousEq' : previous = probe := hpreviousEq
    have hnotClock : previous ∉ pathTimes path.1 := by
      rintro ⟨_, htotal⟩
      have hbad : previous < previous := by
        calc
          previous = probe := hpreviousEq'
          _ < pathTotal path.1 probe := hprobeTotal
          _ = pathTotal path.1 previous := congrArg _ hpreviousEq'.symm
          _ = previous := htotal
      exact (lt_irrefl previous hbad).elim
    have hjump : previous ∈ pathJumps path.1 :=
      hpreviousBoundary.resolve_right hnotClock
    exact ⟨hjump, fun _ ↦ congrArg (fun point ↦ path.1.value point _)
      hpreviousEq'⟩
  · have hnotClock : previous ∉ pathTimes path.1 := by
      intro hclock
      obtain ⟨between, hbetweenBoundary, hpreviousBetween,
          hbetweenProbe⟩ :=
        exists_partitionBoundaryTimes_between_of_mem_pathTimes path hbounded
          hclock hprobe hpreviousLt
      exact
        (not_mem_partitionBoundaryTimes_of_previousPartitionBoundary_lt path
          hpreviousBetween hbetweenProbe.le) hbetweenBoundary
    have hjump : previous ∈ pathJumps path.1 :=
      hpreviousBoundary.resolve_right hnotClock
    have hprobeLtPreviousTotal : probe < pathTotal path.1 previous := by
      by_contra hnot
      have htotalLe : pathTotal path.1 previous ≤ probe := le_of_not_gt hnot
      have htotalBoundary : pathTotal path.1 previous ∈
          partitionBoundaryTimes path :=
        pathTotal_mem_partitionBoundaryTimes path hbounded hpreviousMem
      have hpreviousLtTotal : previous < pathTotal path.1 previous :=
        lt_pathTotal_of_mem_pathJumps path hjump
      exact
        (not_mem_partitionBoundaryTimes_of_previousPartitionBoundary_lt path
          hpreviousLtTotal htotalLe) htotalBoundary
    have htotalEq : pathTotal path.1 probe = pathTotal path.1 previous :=
      pathTotal_eq_of_le_of_lt_pathTotal path hpreviousMem hprobe
        hpreviousLt.le hprobeLtPreviousTotal
    refine ⟨hjump, fun coalition ↦ ?_⟩
    exact (CadlagPath.value_eq_of_total_eq path.1 hpreviousMem hprobe
      hpreviousLt.le htotalEq coalition).symm

end GameTheory.QuittingAbsorptionPath
