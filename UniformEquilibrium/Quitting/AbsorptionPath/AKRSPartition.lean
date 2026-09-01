/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Algebra.Module.Cardinality
import MathUE.Topology.OneSidedDiniFencing
import UniformEquilibrium.Quitting.AbsorptionPath.ContinuousPath

/-!
# Canonical AKRS absorption-path partition

This module constructs the boundary cuts and exact correlated cell laws used
by the AKRS discretization.  It proves only the path and cut identities
stated below; it does not claim the full weak-convergence statement of
published Proposition 4.8.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Topology
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingAbsorptionPath

/-- Every jump is nonterminal in the exact sense needed by path sequential
perfection: after the jump, positive live mass remains. -/
def HasNoTerminalTotalJump (path : AbsorptionPath (ι := ι)) : Prop :=
  ∀ time ∈ pathJumps path.1, pathTotal path.1 time < 1


def pathLeftTotal (path : CadlagPath (ι := ι)) (time : ℝ) : ℝ :=
  ∑ coalition, path.leftValue time coalition

/-- Conditional mass absorbed between two left-limit cuts. -/
def pathCellAbsorption (path : CadlagPath (ι := ι))
    (start stop : ℝ) : ℝ :=
  (pathLeftTotal path stop - pathLeftTotal path start) / (1 - start)

/-- The correlated action law of one left-limit path cell.  Nonempty
coalitions carry the normalized coordinate increment; the empty coalition is
the residual live mass. -/
def pathCellLaw (path : CadlagPath (ι := ι))
    (start stop : ℝ) (coalition : Finset ι) : ℝ :=
  if hcoalition : coalition.Nonempty then
    (path.leftValue stop ⟨coalition, hcoalition⟩ -
      path.leftValue start ⟨coalition, hcoalition⟩) / (1 - start)
  else
    1 - pathCellAbsorption path start stop

omit [DecidableEq ι] [Nonempty ι] in
@[simp] theorem pathCellLaw_empty
    (path : CadlagPath (ι := ι)) (start stop : ℝ) :
    pathCellLaw path start stop ∅ =
      1 - pathCellAbsorption path start stop := by
  simp [pathCellLaw]

omit [DecidableEq ι] [Nonempty ι] in
theorem pathCellLaw_nonempty
    (path : CadlagPath (ι := ι)) (start stop : ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) :
    pathCellLaw path start stop coalition.1 =
      (path.leftValue stop coalition - path.leftValue start coalition) /
        (1 - start) := by
  simp [pathCellLaw, coalition.2]

omit [DecidableEq ι] [Nonempty ι] in
theorem sum_pathCellLaw_nonempty
    (path : CadlagPath (ι := ι)) (start stop : ℝ) :
    (∑ coalition : {S : Finset ι // S.Nonempty},
        pathCellLaw path start stop coalition.1) =
      pathCellAbsorption path start stop := by
  simp_rw [pathCellLaw_nonempty]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rfl

omit [Nonempty ι] in
theorem sum_pathCellLaw
    (path : CadlagPath (ι := ι)) (start stop : ℝ) :
    (∑ coalition, pathCellLaw path start stop coalition) = 1 := by
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := pathCellLaw path start stop)
    (Finset.mem_univ (∅ : Finset ι))
  have hnonempty :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          pathCellLaw path start stop coalition) =
        ∑ coalition : {S : Finset ι // S.Nonempty},
          pathCellLaw path start stop coalition.1 := by
    rw [Finset.sum_subtype (Finset.univ.erase (∅ : Finset ι))]
    intro coalition
    simp [Finset.nonempty_iff_ne_empty]
  rw [← hsplit, hnonempty, sum_pathCellLaw_nonempty, pathCellLaw_empty]
  ring

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- A càdlàg coordinate's left limit is below its value at every path time. -/
theorem CadlagPath.leftValue_le_value
    (path : CadlagPath (ι := ι))
    (coalition : {S : Finset ι // S.Nonempty})
    {time : ℝ} (htime : time ∈ Set.Icc (0 : ℝ) 1) :
    path.leftValue time coalition ≤ path.value time coalition := by
  by_cases hzero : time = 0
  · subst time
    rw [path.left_zero]
    exact (path.value_mem 0 (by norm_num) coalition).1
  · have htime_pos : 0 < time := lt_of_le_of_ne htime.1 (Ne.symm hzero)
    let leftFilter := 𝓝[Set.Icc (0 : ℝ) time \ {time}] time
    have hsubset : Set.Ioo (0 : ℝ) time ⊆
        Set.Icc (0 : ℝ) time \ {time} := by
      intro point hpoint
      exact ⟨⟨hpoint.1.le, hpoint.2.le⟩, hpoint.2.ne⟩
    letI : leftFilter.NeBot :=
      (right_nhdsWithin_Ioo_neBot htime_pos).mono
        (nhdsWithin_mono time hsubset)
    apply le_of_tendsto (path.left_limit coalition time htime)
    filter_upwards [self_mem_nhdsWithin] with point hpoint
    have hpointMem : point ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hpoint.1.1, hpoint.1.2.trans htime.2⟩
    exact path.monotone coalition hpointMem htime hpoint.1.2

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Left limits inherit coordinatewise monotonicity on the path interval. -/
theorem CadlagPath.leftValue_mono
    (path : CadlagPath (ι := ι))
    (coalition : {S : Finset ι // S.Nonempty})
    {start stop : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1) (hstartStop : start ≤ stop) :
    path.leftValue start coalition ≤ path.leftValue stop coalition := by
  rcases hstartStop.eq_or_lt with rfl | hlt
  · exact le_rfl
  · let leftFilter := 𝓝[Set.Icc (0 : ℝ) stop \ {stop}] stop
    have hsubset : Set.Ioo start stop ⊆
        Set.Icc (0 : ℝ) stop \ {stop} := by
      intro point hpoint
      exact ⟨⟨hstart.1.trans hpoint.1.le, hpoint.2.le⟩, hpoint.2.ne⟩
    letI : leftFilter.NeBot :=
      (right_nhdsWithin_Ioo_neBot hlt).mono
        (nhdsWithin_mono stop hsubset)
    apply ge_of_tendsto (path.left_limit coalition stop hstop)
    have hIoi : Set.Ioi start ∈ leftFilter :=
      mem_inf_of_left (Ioi_mem_nhds hlt)
    filter_upwards [self_mem_nhdsWithin, hIoi]
      with point hdomain hstartPoint
    have hpoint : point ∈ Set.Ioo start stop :=
      ⟨hstartPoint, lt_of_le_of_ne hdomain.1.2 hdomain.2⟩
    have hpointMem : point ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hstart.1.trans hpoint.1.le, hpoint.2.le.trans hstop.2⟩
    exact (path.leftValue_le_value coalition hstart).trans
      (path.monotone coalition hstart hpointMem hpoint.1.le)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- An earlier coordinate value is below the left limit at every strictly
later path time. -/
theorem CadlagPath.value_le_leftValue_of_lt
    (path : CadlagPath (ι := ι))
    (coalition : {S : Finset ι // S.Nonempty})
    {earlier later : ℝ}
    (hearler : earlier ∈ Set.Icc (0 : ℝ) 1)
    (hlater : later ∈ Set.Icc (0 : ℝ) 1)
    (hearlerLater : earlier < later) :
    path.value earlier coalition ≤ path.leftValue later coalition := by
  let leftFilter :=
    nhdsWithin later (Set.Icc (0 : ℝ) later \ {later})
  have hsubset : Set.Ioo earlier later ⊆
      Set.Icc (0 : ℝ) later \ {later} := by
    intro point hpoint
    exact ⟨⟨hearler.1.trans hpoint.1.le, hpoint.2.le⟩,
      hpoint.2.ne⟩
  letI : leftFilter.NeBot :=
    (right_nhdsWithin_Ioo_neBot hearlerLater).mono
      (nhdsWithin_mono later hsubset)
  apply ge_of_tendsto (path.left_limit coalition later hlater)
  have hearlerEventually : ∀ᶠ point in leftFilter, earlier < point :=
    mem_inf_of_left (Ioi_mem_nhds hearlerLater)
  filter_upwards [self_mem_nhdsWithin, hearlerEventually]
    with point hpoint hearlerPoint
  have hpointMem : point ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hearler.1.trans hearlerPoint.le,
      hpoint.1.2.trans hlater.2⟩
  exact path.monotone coalition hearler hpointMem hearlerPoint.le

omit [DecidableEq ι] [Nonempty ι] in
/-- Total mass at an earlier time is below total mass immediately before a
strictly later time. -/
theorem pathTotal_le_pathLeftTotal_of_lt
    (path : CadlagPath (ι := ι))
    {earlier later : ℝ}
    (hearler : earlier ∈ Set.Icc (0 : ℝ) 1)
    (hlater : later ∈ Set.Icc (0 : ℝ) 1)
    (hearlerLater : earlier < later) :
    pathTotal path earlier ≤ pathLeftTotal path later := by
  unfold pathTotal pathLeftTotal
  exact Finset.sum_le_sum fun coalition _ ↦
    path.value_le_leftValue_of_lt coalition hearler hlater hearlerLater

omit [DecidableEq ι] [Nonempty ι] in
/-- Under ordered cuts, every nonempty coordinate of the normalized cell law
is nonnegative. -/
theorem pathCellLaw_nonneg_of_nonempty
    (path : CadlagPath (ι := ι))
    {start stop : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1) (hstartStop : start ≤ stop)
    (hstartOne : start < 1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    0 ≤ pathCellLaw path start stop coalition.1 := by
  rw [pathCellLaw_nonempty]
  exact div_nonneg
    (sub_nonneg.mpr (path.leftValue_mono coalition hstart hstop hstartStop))
    (sub_nonneg.mpr hstartOne.le)

omit [DecidableEq ι] [Nonempty ι] in
theorem pathLeftTotal_mono
    (path : CadlagPath (ι := ι))
    {start stop : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1) (hstartStop : start ≤ stop) :
    pathLeftTotal path start ≤ pathLeftTotal path stop := by
  unfold pathLeftTotal
  exact Finset.sum_le_sum fun coalition _ =>
    path.leftValue_mono coalition hstart hstop hstartStop

omit [DecidableEq ι] [Nonempty ι] in
theorem pathLeftTotal_le_pathTotal
    (path : CadlagPath (ι := ι))
    {time : ℝ} (htime : time ∈ Set.Icc (0 : ℝ) 1) :
    pathLeftTotal path time ≤ pathTotal path time := by
  unfold pathLeftTotal pathTotal
  exact Finset.sum_le_sum fun coalition _ =>
    path.leftValue_le_value coalition htime

omit [Nonempty ι] in
/-- Clock domination passes to the left total at every path time.  This is
the left-limit half of the boundary identity used by the published
partition. -/
theorem le_pathLeftTotal
    (path : AbsorptionPath (ι := ι))
    {time : ℝ} (htime : time ∈ Set.Icc (0 : ℝ) 1) :
    time ≤ pathLeftTotal path.1 time := by
  by_cases hzero : time = 0
  · subst time
    simp [pathLeftTotal, path.1.left_zero]
  · have htimePos : 0 < time := lt_of_le_of_ne htime.1 (Ne.symm hzero)
    let leftFilter := nhdsWithin time (Set.Icc (0 : ℝ) time \ {time})
    have hsubset : Set.Ioo (0 : ℝ) time ⊆
        Set.Icc (0 : ℝ) time \ {time} := by
      intro point hpoint
      exact ⟨⟨hpoint.1.le, hpoint.2.le⟩, hpoint.2.ne⟩
    letI : leftFilter.NeBot :=
      (right_nhdsWithin_Ioo_neBot htimePos).mono
        (nhdsWithin_mono time hsubset)
    have htimeTendsto : Tendsto (fun point : ℝ ↦ point) leftFilter
        (nhds time) :=
      tendsto_id.mono_left inf_le_left
    have htotalTendsto : Tendsto (fun point ↦ pathTotal path.1 point)
        leftFilter (nhds (pathLeftTotal path.1 time)) := by
      unfold pathTotal pathLeftTotal
      exact tendsto_finsetSum Finset.univ fun coalition _ ↦
        path.1.left_limit coalition time htime
    apply le_of_tendsto_of_tendsto htimeTendsto htotalTendsto
    filter_upwards [self_mem_nhdsWithin] with point hpoint
    have hpointMem : point ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hpoint.1.1, hpoint.1.2.trans htime.2⟩
    exact path.property.1 point hpointMem

omit [Nonempty ι] in
/-- At a continuous-clock boundary, the total immediately before the cut is
the clock itself. -/
theorem pathLeftTotal_eq_of_mem_pathTimes
    (path : AbsorptionPath (ι := ι))
    {time : ℝ} (htime : time ∈ pathTimes path.1) :
    pathLeftTotal path.1 time = time := by
  apply le_antisymm
  · exact (pathLeftTotal_le_pathTotal path.1 htime.1).trans_eq htime.2
  · exact le_pathLeftTotal path htime.1

omit [DecidableEq ι] [Nonempty ι] in
/-- If the entrance has at least clock mass and the exit has at most unit
mass, the cell's conditional absorption is at most one. -/
theorem pathCellAbsorption_le_one
    (path : CadlagPath (ι := ι)) {start stop : ℝ}
    (hstartOne : start < 1)
    (hstartLower : start ≤ pathLeftTotal path start)
    (hstopUpper : pathLeftTotal path stop ≤ 1) :
    pathCellAbsorption path start stop ≤ 1 := by
  unfold pathCellAbsorption
  apply (div_le_iff₀ (sub_pos.mpr hstartOne)).2
  linarith

omit [DecidableEq ι] [Nonempty ι] in
/-- Every coordinate, including the residual all-Continue coordinate, of a
valid normalized path cell is nonnegative. -/
theorem pathCellLaw_nonneg
    (path : CadlagPath (ι := ι))
    {start stop : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1) (hstartStop : start ≤ stop)
    (hstartOne : start < 1)
    (hstartLower : start ≤ pathLeftTotal path start)
    (hstopUpper : pathLeftTotal path stop ≤ 1)
    (coalition : Finset ι) :
    0 ≤ pathCellLaw path start stop coalition := by
  by_cases hcoalition : coalition.Nonempty
  · exact pathCellLaw_nonneg_of_nonempty path hstart hstop hstartStop
      hstartOne ⟨coalition, hcoalition⟩
  · have hempty : coalition = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcoalition
    subst coalition
    rw [pathCellLaw_empty]
    exact sub_nonneg.mpr
      (pathCellAbsorption_le_one path hstartOne hstartLower hstopUpper)

/-! ## Canonical cut recursion -/

/-- Times that can serve as cell boundaries: literal jump times and literal
continuous-clock times. -/
def partitionBoundaryTimes (path : AbsorptionPath (ι := ι)) : Set ℝ :=
  pathJumps path.1 ∪ pathTimes path.1

omit [DecidableEq ι] [Nonempty ι] in
/-- The total path mass is monotone on the clock interval. -/
theorem monotoneOn_pathTotal (path : CadlagPath (ι := ι)) :
    MonotoneOn (pathTotal path) (Set.Icc (0 : ℝ) 1) := by
  intro earlier hearler later hlater hearlerLater
  unfold pathTotal
  exact Finset.sum_le_sum fun coalition _ ↦
    path.monotone coalition hearler hlater hearlerLater

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Every coordinate jump is nonnegative. -/
theorem pathJump_nonneg
    (path : CadlagPath (ι := ι))
    {time : ℝ} (htime : time ∈ Set.Icc (0 : ℝ) 1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    0 ≤ pathJump path time coalition := by
  exact sub_nonneg.mpr (path.leftValue_le_value coalition htime)

omit [DecidableEq ι] [Nonempty ι] in
theorem pathTotal_sub_pathLeftTotal_eq_sum_pathJump
    (path : CadlagPath (ι := ι)) (time : ℝ) :
    pathTotal path time - pathLeftTotal path time =
      ∑ coalition, pathJump path time coalition := by
  unfold pathTotal pathLeftTotal pathJump
  rw [Finset.sum_sub_distrib]

omit [DecidableEq ι] [Nonempty ι] in
/-- A literal jump strictly raises total mass above its left limit. -/
theorem pathLeftTotal_lt_pathTotal_of_mem_pathJumps
    (path : CadlagPath (ι := ι))
    {time : ℝ} (htime : time ∈ pathJumps path) :
    pathLeftTotal path time < pathTotal path time := by
  obtain ⟨coalition, hcoalition⟩ := htime.2
  have hcoalitionPos : 0 < pathJump path time coalition :=
    lt_of_le_of_ne (pathJump_nonneg path htime.1 coalition)
      (Ne.symm hcoalition)
  have hsumPos : 0 < ∑ terminal, pathJump path time terminal :=
    hcoalitionPos.trans_le <| Finset.single_le_sum
      (fun terminal _ ↦ pathJump_nonneg path htime.1 terminal)
      (Finset.mem_univ coalition)
  rw [← pathTotal_sub_pathLeftTotal_eq_sum_pathJump] at hsumPos
  linarith

omit [Nonempty ι] in
/-- A jump boundary has strictly more post-jump mass than clock time. -/
theorem lt_pathTotal_of_mem_pathJumps
    (path : AbsorptionPath (ι := ι))
    {time : ℝ} (htime : time ∈ pathJumps path.1) :
    time < pathTotal path.1 time :=
  (le_pathLeftTotal path htime.1).trans_lt
    (pathLeftTotal_lt_pathTotal_of_mem_pathJumps path.1 htime)

omit [DecidableEq ι] [Nonempty ι] in
/-- The jump times of a finite-coordinate càdlàg monotone path are
countable.  The possible time-zero jump is separated because continuity from
the right does not see its prescribed left value. -/
theorem countable_pathJumps (path : CadlagPath (ι := ι)) :
    (pathJumps path).Countable := by
  let discontinuities := fun coalition :
      {S : Finset ι // S.Nonempty} ↦
    {time ∈ Set.Icc (0 : ℝ) 1 |
      ¬ ContinuousWithinAt (fun point ↦ path.value point coalition)
        (Set.Icc (0 : ℝ) 1) time}
  have hcountable (coalition : {S : Finset ι // S.Nonempty}) :
      (discontinuities coalition).Countable := by
    exact (path.monotone coalition).countable_not_continuousWithinAt
  have hunion : ({0} ∪ ⋃ coalition, discontinuities coalition).Countable :=
    (Set.countable_singleton 0).union (Set.countable_iUnion hcountable)
  apply hunion.mono
  intro time htime
  by_cases hzero : time = 0
  · exact Or.inl (by simp [hzero])
  · apply Or.inr
    rw [Set.mem_iUnion]
    obtain ⟨coalition, hcoalition⟩ := htime.2
    refine ⟨coalition, htime.1, ?_⟩
    intro hcontinuous
    have htimePos : 0 < time :=
      lt_of_le_of_ne htime.1.1 (Ne.symm hzero)
    let leftFilter :=
      nhdsWithin time (Set.Icc (0 : ℝ) time \ {time})
    have hleftSubset : Set.Icc (0 : ℝ) time \ {time} ⊆
        Set.Icc (0 : ℝ) 1 := by
      intro point hpoint
      exact ⟨hpoint.1.1, hpoint.1.2.trans htime.1.2⟩
    have hIooSubset : Set.Ioo (0 : ℝ) time ⊆
        Set.Icc (0 : ℝ) time \ {time} := by
      intro point hpoint
      exact ⟨⟨hpoint.1.le, hpoint.2.le⟩, hpoint.2.ne⟩
    letI : leftFilter.NeBot :=
      (right_nhdsWithin_Ioo_neBot htimePos).mono
        (nhdsWithin_mono time hIooSubset)
    have hvalueTendsto : Tendsto
        (fun point ↦ path.value point coalition) leftFilter
        (nhds (path.value time coalition)) :=
      (hcontinuous.mono hleftSubset).tendsto
    have hleftTendsto : Tendsto
        (fun point ↦ path.value point coalition) leftFilter
        (nhds (path.leftValue time coalition)) :=
      path.left_limit coalition time htime.1
    have heq : path.value time coalition =
        path.leftValue time coalition :=
      tendsto_nhds_unique hvalueTendsto hleftTendsto
    exact hcoalition (by simp [pathJump, heq])

omit [Nonempty ι] in
/-- A point outside the jump/clock boundary carries its whole half-open
plateau up to the current path total inside one connected component.  This is
the literal interval consequence of absorption-path axiom A2. -/
theorem Ico_subset_boundaryComponent
    (path : AbsorptionPath (ι := ι))
    {base : ℝ}
    (hbase : base ∈ Set.Icc (0 : ℝ) 1 \ partitionBoundaryTimes path) :
    Set.Ico base (pathTotal path.1 base) ⊆
      connectedComponentIn
        (Set.Icc (0 : ℝ) 1 \ partitionBoundaryTimes path) base := by
  let support := Set.Icc (0 : ℝ) 1 \ partitionBoundaryTimes path
  let component := connectedComponentIn support base
  have hbaseComponent : base ∈ component :=
    mem_connectedComponentIn hbase
  have hsup : pathTotal path.1 base = sSup component := by
    exact path.property.2.1 base hbase base hbaseComponent
  intro point hpoint
  rcases hpoint.1.eq_or_lt with rfl | hbasePoint
  · exact hbaseComponent
  · have hpointSup : point < sSup component := by
      rw [← hsup]
      exact hpoint.2
    obtain ⟨upper, hupperComponent, hpointUpper⟩ :=
      exists_lt_of_lt_csSup ⟨base, hbaseComponent⟩ hpointSup
    exact isPreconnected_connectedComponentIn.ordConnected.out
      hbaseComponent hupperComponent ⟨hbasePoint.le, hpointUpper.le⟩

omit [Nonempty ι] in
/-- A nonboundary path point is followed by no jump or continuous-clock
boundary before its current total. -/
theorem Ico_subset_boundaryComplement
    (path : AbsorptionPath (ι := ι))
    {base : ℝ}
    (hbase : base ∈ Set.Icc (0 : ℝ) 1 \ partitionBoundaryTimes path) :
    Set.Ico base (pathTotal path.1 base) ⊆
      Set.Icc (0 : ℝ) 1 \ partitionBoundaryTimes path := by
  exact (Ico_subset_boundaryComponent path hbase).trans
    (connectedComponentIn_subset _ _)

omit [Nonempty ι] in
/-- Axiom A2 makes the total constant on the half-open plateau beginning at
every nonboundary point. -/
theorem pathTotal_eq_of_mem_Ico_of_not_boundary
    (path : AbsorptionPath (ι := ι))
    {base point : ℝ}
    (hbase : base ∈ Set.Icc (0 : ℝ) 1 \ partitionBoundaryTimes path)
    (hpoint : point ∈ Set.Ico base (pathTotal path.1 base)) :
    pathTotal path.1 point = pathTotal path.1 base := by
  have hpointComponent := Ico_subset_boundaryComponent path hbase hpoint
  have hbaseComponent : base ∈ connectedComponentIn
      (Set.Icc (0 : ℝ) 1 \ partitionBoundaryTimes path) base :=
    mem_connectedComponentIn hbase
  rw [path.property.2.1 base hbase point hpointComponent,
    path.property.2.1 base hbase base hbaseComponent]

omit [Nonempty ι] in
/-- Axiom A2 recovers the clock-gap law: the total cannot change before the
current post-jump/plateau total is reached.  At a jump time the proof
approaches from nonjump points on the right and uses right continuity. -/
theorem pathTotal_eq_of_le_of_lt_pathTotal
    (path : AbsorptionPath (ι := ι))
    {time later : ℝ}
    (htime : time ∈ Set.Icc (0 : ℝ) 1)
    (hlater : later ∈ Set.Icc (0 : ℝ) 1)
    (htimeLater : time ≤ later)
    (hlaterTotal : later < pathTotal path.1 time) :
    pathTotal path.1 later = pathTotal path.1 time := by
  rcases htimeLater.eq_or_lt with rfl | htimeLater
  · rfl
  · by_cases hboundary : time ∈ partitionBoundaryTimes path
    · rcases hboundary with hjump | hclock
      · have hdense : Dense ((pathJumps path.1)ᶜ) :=
          (countable_pathJumps path.1).dense_compl ℝ
        obtain ⟨approach, _hstrictAnti, happroachMem,
          happroachTendsto⟩ :=
          hdense.exists_seq_strictAnti_tendsto_of_lt
            (α := ℝ) htimeLater
        have happroachClock (stage : ℕ) :
            approach stage ∉ pathTimes path.1 := by
          rintro ⟨_, hfixed⟩
          have hmono : pathTotal path.1 time ≤
              pathTotal path.1 (approach stage) :=
            monotoneOn_pathTotal path.1 htime
              ⟨htime.1.trans (happroachMem stage).1.1.le,
                (happroachMem stage).1.2.le.trans hlater.2⟩
              (happroachMem stage).1.1.le
          have hstrict : approach stage <
              pathTotal path.1 (approach stage) :=
            (happroachMem stage).1.2.trans hlaterTotal |>.trans_le hmono
          exact hstrict.ne hfixed.symm
        have happroachBoundary (stage : ℕ) :
            approach stage ∈
              Set.Icc (0 : ℝ) 1 \ partitionBoundaryTimes path := by
          refine ⟨⟨htime.1.trans (happroachMem stage).1.1.le,
            (happroachMem stage).1.2.le.trans hlater.2⟩, ?_⟩
          intro hbad
          exact hbad.elim (happroachMem stage).2
            (happroachClock stage)
        have htotalApproach (stage : ℕ) :
            pathTotal path.1 (approach stage) =
              pathTotal path.1 later := by
          apply (pathTotal_eq_of_mem_Ico_of_not_boundary path
            (happroachBoundary stage) ?_).symm
          constructor
          · exact (happroachMem stage).1.2.le
          · have hmono : pathTotal path.1 time ≤
                pathTotal path.1 (approach stage) :=
              monotoneOn_pathTotal path.1 htime
                (happroachBoundary stage).1
                (happroachMem stage).1.1.le
            exact hlaterTotal.trans_le hmono
        have happroachWithin : Tendsto approach atTop
            (nhdsWithin time (Set.Icc time 1)) := by
          rw [tendsto_nhdsWithin_iff]
          exact ⟨happroachTendsto,
            Filter.Eventually.of_forall fun stage ↦
              ⟨(happroachMem stage).1.1.le,
                (happroachMem stage).1.2.le.trans hlater.2⟩⟩
        have htotalTendsto : Tendsto
            (fun stage ↦ pathTotal path.1 (approach stage)) atTop
            (nhds (pathTotal path.1 time)) := by
          unfold pathTotal
          exact tendsto_finsetSum Finset.univ fun coalition _ ↦
            (path.1.right_continuous coalition time htime).comp
              happroachWithin
        have hconstantTendsto : Tendsto
            (fun stage ↦ pathTotal path.1 (approach stage)) atTop
            (nhds (pathTotal path.1 later)) :=
          tendsto_const_nhds.congr' <|
            Filter.Eventually.of_forall fun stage ↦
              (htotalApproach stage).symm
        exact tendsto_nhds_unique hconstantTendsto htotalTendsto
      · exact False.elim <| (not_le_of_gt hlaterTotal) <|
          hclock.2.le.trans htimeLater.le
    · exact pathTotal_eq_of_mem_Ico_of_not_boundary path
        ⟨htime, hboundary⟩ ⟨htimeLater.le, hlaterTotal⟩

/-- A concrete sequence approaching a continuous-clock time from the right,
with total path overshoot bounded by twice clock displacement.  This is the
local `[0,1]` analogue of `HasClockGap.ControlledRightSequence`; it needs no
global extension of the path outside its semantic clock interval. -/
structure PathTotalControlledRightSequence
    (path : AbsorptionPath (ι := ι)) (time : ℝ) where
  point : ℕ → ℝ
  point_mem : ∀ rank, point rank ∈ Set.Ioo time 1
  tendsto : Tendsto point atTop (nhds time)
  pathTotal_sub_le_two_mul : ∀ rank,
    pathTotal path.1 (point rank) - pathTotal path.1 time ≤
      2 * (point rank - time)

omit [Nonempty ι] in
/-- Axiom A2's clock-gap law supplies controlled right points at every
nonterminal fixed point of the path total. -/
theorem nonempty_pathTotalControlledRightSequence
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    {time : ℝ} (htime : time ∈ pathTimes path.1) (htimeOne : time ≠ 1) :
    Nonempty (PathTotalControlledRightSequence path time) := by
  have htimeLtOne : time < 1 :=
    lt_of_le_of_ne htime.1.2 htimeOne
  let scale := fun rank : ℕ ↦ (1 : ℝ) / ((rank : ℝ) + 1)
  let probe := fun rank : ℕ ↦
    time + (1 - time) / 2 * scale rank
  have hscalePos (rank : ℕ) : 0 < scale rank := by
    dsimp only [scale]
    positivity
  have hscaleLeOne (rank : ℕ) : scale rank ≤ 1 := by
    dsimp only [scale]
    rw [div_le_one (by positivity : (0 : ℝ) < (rank : ℝ) + 1)]
    norm_num
  have hprobeMem (rank : ℕ) : probe rank ∈ Set.Ioo time 1 := by
    constructor <;> dsimp only [probe]
    · have := hscalePos rank
      nlinarith
    · have := hscaleLeOne rank
      nlinarith
  have hprobeTendsto : Tendsto probe atTop (nhds time) := by
    have hscaleTendsto : Tendsto scale atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [probe, mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hscaleTendsto)
  have hprobeWithin : Tendsto probe atTop
      (nhdsWithin time (Set.Icc time 1)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hprobeTendsto,
      Filter.Eventually.of_forall fun rank ↦
        ⟨(hprobeMem rank).1.le, (hprobeMem rank).2.le⟩⟩
  have htotalProbeTendsto : Tendsto
      (fun rank ↦ pathTotal path.1 (probe rank)) atTop (nhds time) := by
    rw [← htime.2]
    unfold pathTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦
      (path.1.right_continuous coalition time htime.1).comp hprobeWithin
  have hexists (rank : ℕ) : ∃ point : ℝ,
      point ∈ Set.Ioo time 1 ∧
      probe rank ≤ point ∧
      point ≤ pathTotal path.1 (probe rank) ∧
      pathTotal path.1 point - pathTotal path.1 time ≤
        2 * (point - time) := by
    have hprobeIcc : probe rank ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨htime.1.1.trans (hprobeMem rank).1.le, (hprobeMem rank).2.le⟩
    by_cases heq : pathTotal path.1 (probe rank) = probe rank
    · refine ⟨probe rank, hprobeMem rank, le_rfl, heq.ge, ?_⟩
      rw [heq, htime.2]
      linarith [hprobeMem rank |>.1]
    · have hprobeLt : probe rank < pathTotal path.1 (probe rank) :=
        lt_of_le_of_ne (path.property.1 (probe rank) hprobeIcc) (Ne.symm heq)
      let lower := max (probe rank)
        ((pathTotal path.1 (probe rank) + time) / 2)
      have hlowerLt : lower < pathTotal path.1 (probe rank) := by
        rw [max_lt_iff]
        exact ⟨hprobeLt, by linarith [hprobeMem rank |>.1]⟩
      let point := (lower + pathTotal path.1 (probe rank)) / 2
      have hlowerPoint : lower < point := by
        dsimp only [point]
        linarith
      have hpointTotal : point < pathTotal path.1 (probe rank) := by
        dsimp only [point]
        linarith
      have hprobePoint : probe rank < point :=
        (le_max_left _ _).trans_lt hlowerPoint
      have hpointMem : point ∈ Set.Ioo time 1 :=
        ⟨(hprobeMem rank).1.trans hprobePoint,
          hpointTotal.trans_le (hpathTotal (probe rank) hprobeIcc)⟩
      have hpointIcc : point ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨htime.1.1.trans hpointMem.1.le, hpointMem.2.le⟩
      have htotalPoint : pathTotal path.1 point =
          pathTotal path.1 (probe rank) :=
        pathTotal_eq_of_le_of_lt_pathTotal path hprobeIcc hpointIcc
          hprobePoint.le hpointTotal
      refine ⟨point, hpointMem, hprobePoint.le, hpointTotal.le, ?_⟩
      rw [htotalPoint, htime.2]
      have hmidpoint :
          (pathTotal path.1 (probe rank) + time) / 2 < point :=
        (le_max_right _ _).trans_lt hlowerPoint
      linarith
  choose point hpoint using hexists
  refine ⟨{
    point := point
    point_mem := fun rank ↦ (hpoint rank).1
    tendsto := ?_
    pathTotal_sub_le_two_mul := fun rank ↦ (hpoint rank).2.2.2
  }⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hprobeTendsto
    htotalProbeTendsto
  · exact fun rank ↦ (hpoint rank).2.1
  · exact fun rank ↦ (hpoint rank).2.2.1

omit [DecidableEq ι] [Nonempty ι] in
/-- One monotone coordinate increment is bounded by the corresponding total
path increment. -/
theorem CadlagPath.value_sub_le_pathTotal_sub
    (path : CadlagPath (ι := ι))
    {earlier later : ℝ}
    (hearler : earlier ∈ Set.Icc (0 : ℝ) 1)
    (hlater : later ∈ Set.Icc (0 : ℝ) 1)
    (hearlerLater : earlier ≤ later)
    (coalition : {S : Finset ι // S.Nonempty}) :
    path.value later coalition - path.value earlier coalition ≤
      pathTotal path later - pathTotal path earlier := by
  have hnonneg (other : {S : Finset ι // S.Nonempty}) :
      0 ≤ path.value later other - path.value earlier other :=
    sub_nonneg.mpr <| path.monotone other hearler hlater hearlerLater
  have hsingle := Finset.single_le_sum
    (fun other _ ↦ hnonneg other) (Finset.mem_univ coalition)
  unfold pathTotal
  rw [← Finset.sum_sub_distrib]
  exact hsingle

omit [DecidableEq ι] [Nonempty ι] in
/-- If the total mass is unchanged between two ordered clock points, every
coordinate is unchanged. -/
theorem CadlagPath.value_eq_of_total_eq
    (path : CadlagPath (ι := ι))
    {earlier later : ℝ}
    (hearler : earlier ∈ Set.Icc (0 : ℝ) 1)
    (hlater : later ∈ Set.Icc (0 : ℝ) 1)
    (hearlerLater : earlier ≤ later)
    (htotal : pathTotal path later = pathTotal path earlier)
    (coalition : {S : Finset ι // S.Nonempty}) :
    path.value later coalition = path.value earlier coalition := by
  apply le_antisymm
  · have hbound := CadlagPath.value_sub_le_pathTotal_sub path
      (earlier := earlier) (later := later) hearler hlater hearlerLater
      coalition
    rw [htotal, sub_self] at hbound
    linarith
  · exact path.monotone coalition hearler hlater hearlerLater

omit [Nonempty ι] in
/-- At a nonterminal continuous-clock time, the A2 clock-gap structure makes
every coordinate right-slope quotient frequently bounded above.  This is the
missing boundedness premise needed to read the real-valued `liminf`
literally. -/
theorem frequently_coordinateSlope_le_two_of_mem_pathTimes
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    {time stop : ℝ} (htime : time ∈ pathTimes path.1)
    (htimeStop : time < stop) (hstopOne : stop ≤ 1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    ∃ᶠ later in nhdsWithin time (Set.Ioo time stop),
      (path.1.value later coalition - path.1.value time coalition) /
          (later - time) ≤ 2 := by
  have htimeOne : time ≠ 1 := ne_of_lt (htimeStop.trans_le hstopOne)
  let controlled := Classical.choice <|
    nonempty_pathTotalControlledRightSequence path hpathTotal htime htimeOne
  let quotient := fun later : ℝ ↦
    (path.1.value later coalition - path.1.value time coalition) /
      (later - time)
  have hpointEventuallyStop : ∀ᶠ rank in atTop,
      controlled.point rank < stop :=
    controlled.tendsto (Iio_mem_nhds htimeStop)
  have hpointGood : ∀ᶠ rank in atTop,
      controlled.point rank ∈ Set.Ioo time stop ∧
        quotient (controlled.point rank) ≤ 2 := by
    filter_upwards [hpointEventuallyStop] with rank hrankStop
    have hpointMem := controlled.point_mem rank
    have hpointIcc : controlled.point rank ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨htime.1.1.trans hpointMem.1.le, hpointMem.2.le⟩
    have hcoordinate := CadlagPath.value_sub_le_pathTotal_sub path.1
      htime.1 hpointIcc hpointMem.1.le coalition
    have hdenominatorPos : 0 < controlled.point rank - time :=
      sub_pos.mpr hpointMem.1
    refine ⟨⟨hpointMem.1, hrankStop⟩, ?_⟩
    unfold quotient
    apply (div_le_iff₀ hdenominatorPos).2
    exact hcoordinate.trans <| controlled.pathTotal_sub_le_two_mul rank
  have hclosure : time ∈ closure
      {later | later ∈ Set.Ioo time stop ∧ quotient later ≤ 2} := by
    exact mem_closure_of_tendsto controlled.tendsto hpointGood
  rw [frequently_nhdsWithin_iff]
  have hfrequent := mem_closure_iff_frequently.mp hclosure
  exact hfrequent.mono fun later hlater ↦
    ⟨hlater.2, hlater.1⟩

/-- Coalition mass corrected by an incident singleton coordinate. -/
def incidentCorrectedValue
    (path : CadlagPath (ι := ι)) (ε : ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) (player : ι)
    (time : ℝ) : ℝ :=
  path.value time coalition -
    ε * path.value time ⟨{player}, Finset.singleton_nonempty player⟩

/-- Left-limit version of the incident-corrected coordinate. -/
def incidentCorrectedLeftValue
    (path : CadlagPath (ι := ι)) (ε : ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) (player : ι)
    (time : ℝ) : ℝ :=
  path.leftValue time coalition -
    ε * path.leftValue time ⟨{player}, Finset.singleton_nonempty player⟩

/-- On a half-open cell, use the actual corrected path value before the
right endpoint and the corrected left limit at the endpoint. -/
def incidentCorrectedCellValue
    (path : CadlagPath (ι := ι)) (ε : ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) (player : ι)
    (stop time : ℝ) : ℝ :=
  if time = stop then
    incidentCorrectedLeftValue path ε coalition player stop
  else incidentCorrectedValue path ε coalition player time

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- A jump-level incident-collision estimate is exactly the assertion that
the corrected coordinate has no upward jump. -/
theorem incidentCorrectedValue_le_leftValue_of_pathJump_le
    (path : CadlagPath (ι := ι)) (ε : ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) (player : ι)
    (time : ℝ)
    (hjump : pathJump path time coalition ≤
      ε * pathJump path time
        ⟨{player}, Finset.singleton_nonempty player⟩) :
    incidentCorrectedValue path ε coalition player time ≤
      incidentCorrectedLeftValue path ε coalition player time := by
  unfold incidentCorrectedValue incidentCorrectedLeftValue pathJump at *
  linarith

omit [Nonempty ι] in
/-- The A2/A4 adapter: if every discrete jump on a cell satisfies an
incident-collision estimate, then the entire half-open cell satisfies the
same estimate.  A2 supplies flat clock gaps; A4 supplies zero nonsingleton
lower-right slope at continuous-clock points. -/
theorem leftValue_incidentCoalitionIncrement_le_of_pathJump_bounds
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 point ≤ 1)
    {ε start stop : ℝ} (hε : 0 ≤ ε)
    (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1)
    (hstartStop : start < stop)
    (coalition : Finset ι) (player : ι)
    (hcard : 2 ≤ coalition.card)
    (hjumpBound : ∀ time ∈ Set.Ico start stop,
      pathJump path.1 time
          ⟨coalition, Finset.card_pos.mp
            (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ ≤
        ε * pathJump path.1 time
          ⟨{player}, Finset.singleton_nonempty player⟩) :
    path.1.leftValue stop
          ⟨coalition, Finset.card_pos.mp
            (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ -
        path.1.leftValue start
          ⟨coalition, Finset.card_pos.mp
            (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ ≤
      ε * (path.1.leftValue stop
          ⟨{player}, Finset.singleton_nonempty player⟩ -
        path.1.leftValue start
          ⟨{player}, Finset.singleton_nonempty player⟩) := by
  let terminal : {S : Finset ι // S.Nonempty} :=
    ⟨coalition, Finset.card_pos.mp
      (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩
  let singleton : {S : Finset ι // S.Nonempty} :=
    ⟨{player}, Finset.singleton_nonempty player⟩
  let corrected := incidentCorrectedValue path.1 ε terminal player
  let correctedLeft := incidentCorrectedLeftValue path.1 ε terminal player
  let cellValue := incidentCorrectedCellValue path.1 ε terminal player stop
  have hpointJumpBound (point : ℝ) (hpoint : point ∈ Set.Ico start stop) :
      pathJump path.1 point terminal ≤
        ε * pathJump path.1 point singleton := by
    simpa only [terminal, singleton] using hjumpBound point hpoint
  have hnoUpward (point : ℝ) (hpoint : point ∈ Set.Ico start stop) :
      corrected point ≤ correctedLeft point := by
    apply incidentCorrectedValue_le_leftValue_of_pathJump_le
    exact hpointJumpBound point hpoint
  have hright (point : ℝ) (hpoint : point ∈ Set.Ico start stop) :
      Tendsto cellValue (nhdsWithin point (Set.Icc point stop))
        (nhds (cellValue point)) := by
    have hdomain : Set.Icc point stop ⊆ Set.Icc point 1 := by
      intro later hlater
      exact ⟨hlater.1, hlater.2.trans hstop.2⟩
    have hcoalitionTendsto :=
      (path.1.right_continuous terminal point
        ⟨hstart.1.trans hpoint.1, hpoint.2.le.trans hstop.2⟩).mono_left
          (nhdsWithin_mono point hdomain)
    have hsingletonTendsto :=
      (path.1.right_continuous singleton point
        ⟨hstart.1.trans hpoint.1, hpoint.2.le.trans hstop.2⟩).mono_left
          (nhdsWithin_mono point hdomain)
    have hcorrectedTendsto : Tendsto corrected
        (nhdsWithin point (Set.Icc point stop)) (nhds (corrected point)) := by
      exact hcoalitionTendsto.sub (tendsto_const_nhds.mul hsingletonTendsto)
    have hpointNeStop : point ≠ stop := ne_of_lt hpoint.2
    have heq : ∀ᶠ later in nhdsWithin point (Set.Icc point stop),
        cellValue later = corrected later := by
      filter_upwards [mem_inf_of_left (Iio_mem_nhds hpoint.2)] with later hlater
      change incidentCorrectedCellValue path.1 ε terminal player stop later =
        incidentCorrectedValue path.1 ε terminal player later
      simp only [incidentCorrectedCellValue,
        if_neg (ne_of_lt (show later < stop from hlater))]
    have htarget : cellValue point = corrected point := by
      change incidentCorrectedCellValue path.1 ε terminal player stop point =
        incidentCorrectedValue path.1 ε terminal player point
      simp only [incidentCorrectedCellValue, if_neg hpointNeStop]
    rw [htarget]
    exact hcorrectedTendsto.congr' (Filter.EventuallyEq.symm heq)
  have hleftTendsto (point : ℝ) (hpoint : point ∈ Set.Ioc start stop) :
      Tendsto cellValue (nhdsWithin point (Set.Ico start point))
        (nhds (correctedLeft point)) := by
    have hdomain : Set.Ico start point ⊆
        Set.Icc (0 : ℝ) point \ {point} := by
      intro earlier hearler
      exact ⟨⟨hstart.1.trans hearler.1, hearler.2.le⟩,
        hearler.2.ne⟩
    have hcoalitionTendsto :=
      (path.1.left_limit terminal point
        ⟨hstart.1.trans hpoint.1.le, hpoint.2.trans hstop.2⟩).mono_left
          (nhdsWithin_mono point hdomain)
    have hsingletonTendsto :=
      (path.1.left_limit singleton point
        ⟨hstart.1.trans hpoint.1.le, hpoint.2.trans hstop.2⟩).mono_left
          (nhdsWithin_mono point hdomain)
    have hcorrectedTendsto : Tendsto corrected
        (nhdsWithin point (Set.Ico start point))
        (nhds (correctedLeft point)) := by
      exact hcoalitionTendsto.sub (tendsto_const_nhds.mul hsingletonTendsto)
    have heq : ∀ᶠ earlier in nhdsWithin point (Set.Ico start point),
        cellValue earlier = corrected earlier := by
      filter_upwards [self_mem_nhdsWithin] with earlier hearler
      change incidentCorrectedCellValue path.1 ε terminal player stop earlier =
        incidentCorrectedValue path.1 ε terminal player earlier
      simp only [incidentCorrectedCellValue,
        if_neg (ne_of_lt (hearler.2.trans_le hpoint.2))]
    exact hcorrectedTendsto.congr' (Filter.EventuallyEq.symm heq)
  have hjump (point : ℝ) (hpoint : point ∈ Set.Ioc start stop) :
      cellValue point ≤ correctedLeft point := by
    rcases hpoint.2.eq_or_lt with rfl | hpointStop
    · change incidentCorrectedCellValue path.1 ε terminal player point point ≤
        incidentCorrectedLeftValue path.1 ε terminal player point
      simp [incidentCorrectedCellValue]
    · have hpointIco : point ∈ Set.Ico start stop :=
        ⟨hpoint.1.le, hpointStop⟩
      have hpointNeStop : point ≠ stop := ne_of_lt hpointStop
      simpa only [cellValue, incidentCorrectedCellValue,
        if_neg hpointNeStop] using hnoUpward point hpointIco
  have hstartLe : cellValue start ≤ correctedLeft start := by
    have hstartIco : start ∈ Set.Ico start stop :=
      ⟨le_rfl, hstartStop⟩
    have hstartNeStop : start ≠ stop := ne_of_lt hstartStop
    simpa only [cellValue, incidentCorrectedCellValue,
      if_neg hstartNeStop] using hnoUpward start hstartIco
  have hslope (point : ℝ) (hpoint : point ∈ Set.Ico start stop)
      (rate : ℝ) (hrate : 0 < rate) :
      ∃ᶠ later in nhdsWithin point (Set.Ioo point stop),
        slope cellValue point later < rate := by
    have hpointIcc : point ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hstart.1.trans hpoint.1, hpoint.2.le.trans hstop.2⟩
    have hpointNeStop : point ≠ stop := ne_of_lt hpoint.2
    by_cases hclock : point ∈ pathTimes path.1
    · have hpointOne : point ≠ 1 :=
        ne_of_lt (hpoint.2.trans_le hstop.2)
      have hderivativeZero : pathRightDerivative path.1 point terminal = 0 := by
        by_contra hne
        have hsingletonCard := path.property.2.2.2 point hclock hpointOne
          terminal hne
        change coalition.card = 1 at hsingletonCard
        omega
      let coalitionSlope := fun later : ℝ ↦
        (path.1.value later terminal - path.1.value point terminal) /
          (later - point)
      have hbounded : ∃ᶠ later in nhdsWithin point (Set.Ioo point stop),
          coalitionSlope later ≤ 2 := by
        simpa only [coalitionSlope] using
          frequently_coordinateSlope_le_two_of_mem_pathTimes path hpathTotal
            hclock hpoint.2 hstop.2 terminal
      have hcobounded :
          (nhdsWithin point (Set.Ioo point stop)).IsCoboundedUnder
            (· ≥ ·) coalitionSlope :=
        Filter.IsCoboundedUnder.of_frequently_le hbounded
      have hfilters : nhdsWithin point (Set.Ioo point stop) =
          nhdsWithin point (Set.Ioo point 1) := by
        rw [nhdsWithin_Ioo_eq_nhdsGT hpoint.2,
          nhdsWithin_Ioo_eq_nhdsGT (hpoint.2.trans_le hstop.2)]
      have hliminf : Filter.liminf coalitionSlope
          (nhdsWithin point (Set.Ioo point stop)) = 0 := by
        rw [hfilters]
        simpa only [coalitionSlope, pathRightDerivative] using hderivativeZero
      have hcoalitionFrequent : ∃ᶠ later in
          nhdsWithin point (Set.Ioo point stop),
          coalitionSlope later < rate := by
        apply frequently_lt_of_liminf_lt hcobounded
        rw [hliminf]
        exact hrate
      have hcoalitionFrequentWithMem :=
        hcoalitionFrequent.and_eventually self_mem_nhdsWithin
      apply hcoalitionFrequentWithMem.mono
      intro later hlater
      have hlaterMem : later ∈ Set.Ioo point stop := by
        exact (show later ∈ Set.Ioo point stop from hlater.2)
      have hsingletonMono : path.1.value point singleton ≤
          path.1.value later singleton :=
        path.1.monotone singleton hpointIcc
          ⟨hpointIcc.1.trans hlaterMem.1.le,
            hlaterMem.2.le.trans hstop.2⟩ hlaterMem.1.le
      have hcorrectedSlope : slope cellValue point later ≤
          coalitionSlope later := by
        rw [slope_def_field]
        simp only [cellValue, incidentCorrectedCellValue,
          if_neg hpointNeStop, if_neg (ne_of_lt hlaterMem.2)]
        unfold incidentCorrectedValue coalitionSlope
        apply (div_le_div_iff_of_pos_right (sub_pos.mpr hlaterMem.1)).2
        nlinarith
      exact hcorrectedSlope.trans_lt hlater.1
    · have hpointLtTotal : point < pathTotal path.1 point :=
        lt_of_le_of_ne (path.property.1 point hpointIcc) <| by
          intro heq
          exact hclock ⟨hpointIcc, heq.symm⟩
      letI : (nhdsWithin point (Set.Ioo point stop)).NeBot :=
        left_nhdsWithin_Ioo_neBot hpoint.2
      have heventually : ∀ᶠ later in nhdsWithin point (Set.Ioo point stop),
          later < pathTotal path.1 point :=
        mem_inf_of_left (Iio_mem_nhds hpointLtTotal)
      have hzeroSlope : ∀ᶠ later in
          nhdsWithin point (Set.Ioo point stop),
          slope cellValue point later = 0 := by
        filter_upwards [heventually, self_mem_nhdsWithin]
          with later hlaterTotal hlaterMem
        have hlaterIcc : later ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨hpointIcc.1.trans hlaterMem.1.le,
            hlaterMem.2.le.trans hstop.2⟩
        have htotalEq := pathTotal_eq_of_le_of_lt_pathTotal path
          hpointIcc hlaterIcc hlaterMem.1.le hlaterTotal
        have hcoalitionEq := CadlagPath.value_eq_of_total_eq path.1
          (earlier := point) (later := later) hpointIcc hlaterIcc
          hlaterMem.1.le htotalEq terminal
        have hsingletonEq := CadlagPath.value_eq_of_total_eq path.1
          (earlier := point) (later := later) hpointIcc hlaterIcc
          hlaterMem.1.le htotalEq singleton
        rw [slope_def_field]
        simp only [cellValue, incidentCorrectedCellValue,
          if_neg hpointNeStop, if_neg (ne_of_lt hlaterMem.2)]
        unfold incidentCorrectedValue
        rw [hcoalitionEq, hsingletonEq, sub_self, zero_div]
      exact (hzeroSlope.mono fun later heq ↦ heq.symm ▸ hrate).frequently
  have hend :=
    endpoint_le_of_rightContinuous_leftLimit_noUpwardJump_liminfSlope_nonpos
      hstartStop.le hstartLe hright hleftTendsto hjump hslope
  have hcellStop : cellValue stop = correctedLeft stop := by
    change incidentCorrectedCellValue path.1 ε terminal player stop stop =
      incidentCorrectedLeftValue path.1 ε terminal player stop
    simp [incidentCorrectedCellValue]
  rw [hcellStop] at hend
  unfold correctedLeft incidentCorrectedLeftValue at hend
  dsimp only [terminal, singleton] at hend
  linarith

omit [Nonempty ι] in
/-- At every jump boundary, the total immediately before the jump is exactly
the clock.  This is Remark 4.4's boundary identity, derived here from A1,
A2, monotonicity, and left limits. -/
theorem pathLeftTotal_eq_of_mem_pathJumps
    (path : AbsorptionPath (ι := ι))
    {time : ℝ} (htime : time ∈ pathJumps path.1) :
    pathLeftTotal path.1 time = time := by
  apply le_antisymm
  · by_cases hzero : time = 0
    · subst time
      simp [pathLeftTotal, path.1.left_zero]
    · have htimePos : 0 < time :=
        lt_of_le_of_ne htime.1.1 (Ne.symm hzero)
      let leftFilter :=
        nhdsWithin time (Set.Icc (0 : ℝ) time \ {time})
      have hIooSubset : Set.Ioo (0 : ℝ) time ⊆
          Set.Icc (0 : ℝ) time \ {time} := by
        intro point hpoint
        exact ⟨⟨hpoint.1.le, hpoint.2.le⟩, hpoint.2.ne⟩
      letI : leftFilter.NeBot :=
        (right_nhdsWithin_Ioo_neBot htimePos).mono
          (nhdsWithin_mono time hIooSubset)
      have htotalTendsto : Tendsto
          (fun point ↦ pathTotal path.1 point) leftFilter
          (nhds (pathLeftTotal path.1 time)) := by
        unfold pathTotal pathLeftTotal
        exact tendsto_finsetSum Finset.univ fun coalition _ ↦
          path.1.left_limit coalition time htime.1
      apply le_of_tendsto htotalTendsto
      filter_upwards [self_mem_nhdsWithin] with point hpoint
      have hpointLt : point < time :=
        lt_of_le_of_ne hpoint.1.2 hpoint.2
      have hpointMem : point ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨hpoint.1.1, hpointLt.le.trans htime.1.2⟩
      by_contra hnotLe
      have htimeLtTotal : time < pathTotal path.1 point :=
        lt_of_not_ge hnotLe
      have hgap := pathTotal_eq_of_le_of_lt_pathTotal path
        hpointMem htime.1 hpointLt.le htimeLtTotal
      have hbefore := pathTotal_le_pathLeftTotal_of_lt path.1
        hpointMem htime.1 hpointLt
      have hstrict :=
        pathLeftTotal_lt_pathTotal_of_mem_pathJumps path.1 htime
      exact (not_le_of_gt hstrict) (hgap.le.trans hbefore)
  · exact le_pathLeftTotal path htime.1

omit [Nonempty ι] in
/-- Every admissible partition boundary has left total exactly equal to its
clock coordinate. -/
theorem pathLeftTotal_eq_of_mem_partitionBoundaryTimes
    (path : AbsorptionPath (ι := ι))
    {time : ℝ} (htime : time ∈ partitionBoundaryTimes path) :
    pathLeftTotal path.1 time = time := by
  rcases htime with hjump | hclock
  · exact pathLeftTotal_eq_of_mem_pathJumps path hjump
  · exact pathLeftTotal_eq_of_mem_pathTimes path hclock

omit [Nonempty ι] in
/-- The left total at the end of a nontrivial clock gap equals the total at
the gap entrance. -/
theorem pathLeftTotal_pathTotal_eq_at_currentTotal
    (path : AbsorptionPath (ι := ι))
    {base : ℝ} (hbase : base ∈ Set.Icc (0 : ℝ) 1)
    (htotalLe : pathTotal path.1 base ≤ 1)
    (hbaseTotal : base < pathTotal path.1 base) :
    pathLeftTotal path.1 (pathTotal path.1 base) =
      pathTotal path.1 base := by
  let boundary := pathTotal path.1 base
  have hboundaryMem : boundary ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hbase.1.trans hbaseTotal.le, htotalLe⟩
  let leftFilter :=
    nhdsWithin boundary (Set.Icc (0 : ℝ) boundary \ {boundary})
  have hIooSubset : Set.Ioo base boundary ⊆
      Set.Icc (0 : ℝ) boundary \ {boundary} := by
    intro point hpoint
    exact ⟨⟨hbase.1.trans hpoint.1.le, hpoint.2.le⟩,
      hpoint.2.ne⟩
  letI : leftFilter.NeBot :=
    (right_nhdsWithin_Ioo_neBot hbaseTotal).mono
      (nhdsWithin_mono boundary hIooSubset)
  have htotalTendsto : Tendsto (fun point ↦ pathTotal path.1 point)
      leftFilter (nhds (pathLeftTotal path.1 boundary)) := by
    unfold pathTotal pathLeftTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦
      path.1.left_limit coalition boundary hboundaryMem
  have hbaseEventually : ∀ᶠ point in leftFilter, base < point :=
    mem_inf_of_left (Ioi_mem_nhds hbaseTotal)
  have hconstant : ∀ᶠ point in leftFilter,
      pathTotal path.1 point = pathTotal path.1 base := by
    filter_upwards [self_mem_nhdsWithin, hbaseEventually]
      with point hpoint hbasePoint
    have hpointLt : point < boundary :=
      lt_of_le_of_ne hpoint.1.2 hpoint.2
    have hpointMem : point ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hbase.1.trans hbasePoint.le,
        hpointLt.le.trans hboundaryMem.2⟩
    exact pathTotal_eq_of_le_of_lt_pathTotal path hbase hpointMem
      hbasePoint.le hpointLt
  have hconstantTendsto : Tendsto (fun point ↦ pathTotal path.1 point)
      leftFilter (nhds (pathTotal path.1 base)) :=
    tendsto_const_nhds.congr' <|
      hconstant.mono fun _ heq ↦ heq.symm
  exact tendsto_nhds_unique htotalTendsto hconstantTendsto

omit [Nonempty ι] in
/-- The current post-jump/plateau total is itself a jump or clock boundary.
This is the source fact that makes the published supremum recursion close on
boundary points. -/
theorem pathTotal_mem_partitionBoundaryTimes
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    {base : ℝ} (hbase : base ∈ Set.Icc (0 : ℝ) 1) :
    pathTotal path.1 base ∈ partitionBoundaryTimes path := by
  let boundary := pathTotal path.1 base
  have hbaseBoundary : base ≤ boundary := path.property.1 base hbase
  have hboundaryMem : boundary ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hbase.1.trans hbaseBoundary, hpathTotal base hbase⟩
  by_cases hclock : pathTotal path.1 boundary = boundary
  · exact Or.inr ⟨hboundaryMem, hclock⟩
  · apply Or.inl
    refine ⟨hboundaryMem, ?_⟩
    have hstrict : boundary < pathTotal path.1 boundary :=
      lt_of_le_of_ne (path.property.1 boundary hboundaryMem)
        (Ne.symm hclock)
    have hbaseStrict : base < boundary := by
      exact lt_of_le_of_ne hbaseBoundary <| by
        intro heq
        apply hclock
        calc
          pathTotal path.1 boundary = pathTotal path.1 base :=
            congrArg (pathTotal path.1) heq.symm
          _ = boundary := rfl
    have hleft := pathLeftTotal_pathTotal_eq_at_currentTotal path hbase
      (hpathTotal base hbase) hbaseStrict
    by_contra hnoJump
    have hzero (coalition : {S : Finset ι // S.Nonempty}) :
        pathJump path.1 boundary coalition = 0 := by
      by_contra hcoalition
      exact hnoJump ⟨coalition, hcoalition⟩
    have hsumJump : (∑ coalition, pathJump path.1 boundary coalition) = 0 := by
      simp [hzero]
    rw [← pathTotal_sub_pathLeftTotal_eq_sum_pathJump, hleft] at hsumJump
    exact (not_le_of_gt hstrict) (sub_eq_zero.mp hsumJump).le

omit [Nonempty ι] in
/-- The post-total at an earlier boundary cannot pass a strictly later
boundary. -/
theorem pathTotal_le_of_boundary_lt_boundary
    (path : AbsorptionPath (ι := ι))
    {earlier later : ℝ}
    (hearler : earlier ∈ partitionBoundaryTimes path)
    (hlater : later ∈ partitionBoundaryTimes path)
    (hearlerLater : earlier < later) :
    pathTotal path.1 earlier ≤ later := by
  exact (pathTotal_le_pathLeftTotal_of_lt path.1
    (hearler.elim And.left And.left) (hlater.elim And.left And.left)
    hearlerLater).trans_eq
      (pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hlater)

omit [Nonempty ι] in
/-- A nonempty bounded family of partition boundaries contains its supremum
whenever that supremum remains in the unit clock interval. -/
theorem csSup_mem_partitionBoundaryTimes
    (path : AbsorptionPath (ι := ι))
    {source : Set ℝ} (hsourceNonempty : source.Nonempty)
    (hsourceBoundary : source ⊆ partitionBoundaryTimes path)
    (hsourceBdd : BddAbove source)
    (hsupMem : sSup source ∈ Set.Icc (0 : ℝ) 1) :
    sSup source ∈ partitionBoundaryTimes path := by
  by_cases hsupSource : sSup source ∈ source
  · exact hsourceBoundary hsupSource
  · obtain ⟨approach, _happroachMono, happroachTendsto,
        happroachSource⟩ :=
      exists_seq_tendsto_sSup hsourceNonempty hsourceBdd
    have happroachLt (stage : ℕ) : approach stage < sSup source := by
      exact lt_of_le_of_ne
        (le_csSup hsourceBdd (happroachSource stage)) <| by
          intro heq
          exact hsupSource (heq ▸ happroachSource stage)
    have happroachBoundary (stage : ℕ) :
        approach stage ∈ partitionBoundaryTimes path :=
      hsourceBoundary (happroachSource stage)
    have happroachMem (stage : ℕ) :
        approach stage ∈ Set.Icc (0 : ℝ) 1 :=
      (happroachBoundary stage).elim And.left And.left
    have htotalUpper (stage : ℕ) :
        pathTotal path.1 (approach stage) ≤ sSup source := by
      obtain ⟨later, hlaterSource, hstageLater⟩ :=
        exists_lt_of_lt_csSup hsourceNonempty (happroachLt stage)
      exact (pathTotal_le_of_boundary_lt_boundary path
        (happroachBoundary stage) (hsourceBoundary hlaterSource)
        hstageLater).trans (le_csSup hsourceBdd hlaterSource)
    have htotalTendstoSup : Tendsto
        (fun stage ↦ pathTotal path.1 (approach stage)) atTop
        (nhds (sSup source)) := by
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        happroachTendsto tendsto_const_nhds
        (fun stage ↦ path.property.1 (approach stage)
          (happroachMem stage))
        htotalUpper
    have happroachWithin : Tendsto approach atTop
        (nhdsWithin (sSup source)
          (Set.Icc (0 : ℝ) (sSup source) \ {sSup source})) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨happroachTendsto,
        Filter.Eventually.of_forall fun stage ↦
          ⟨⟨(happroachMem stage).1, (happroachLt stage).le⟩,
            (happroachLt stage).ne⟩⟩
    have htotalTendstoLeft : Tendsto
        (fun stage ↦ pathTotal path.1 (approach stage)) atTop
        (nhds (pathLeftTotal path.1 (sSup source))) := by
      unfold pathTotal pathLeftTotal
      exact tendsto_finsetSum Finset.univ fun coalition _ ↦
        (path.1.left_limit coalition (sSup source) hsupMem).comp
          happroachWithin
    have hleft : pathLeftTotal path.1 (sSup source) = sSup source :=
      tendsto_nhds_unique htotalTendstoLeft htotalTendstoSup
    by_contra hnotBoundary
    have hnotJump : sSup source ∉ pathJumps path.1 :=
      fun hjump ↦ hnotBoundary (Or.inl hjump)
    have hzero (coalition : {S : Finset ι // S.Nonempty}) :
        pathJump path.1 (sSup source) coalition = 0 := by
      by_contra hcoalition
      exact hnotJump ⟨hsupMem, coalition, hcoalition⟩
    have hsumJump :
        (∑ coalition, pathJump path.1 (sSup source) coalition) = 0 := by
      simp [hzero]
    rw [← pathTotal_sub_pathLeftTotal_eq_sum_pathJump, hleft] at hsumJump
    apply hnotBoundary
    apply Or.inr
    exact ⟨hsupMem, sub_eq_zero.mp hsumJump⟩

omit [Nonempty ι] in
/-- A continuous-clock boundary below a ceiling is followed by another
boundary before that ceiling.  Right continuity supplies a nearby point; if
it is not itself a clock time, its current total is the required boundary. -/
theorem exists_partitionBoundaryTimes_between_of_mem_pathTimes
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    {time ceiling : ℝ} (htime : time ∈ pathTimes path.1)
    (hceiling : ceiling ∈ Set.Icc (0 : ℝ) 1)
    (htimeCeiling : time < ceiling) :
    ∃ boundary ∈ partitionBoundaryTimes path,
      time < boundary ∧ boundary < ceiling := by
  obtain ⟨approach, _hstrictAnti, happroachMem, happroachTendsto⟩ :=
    (show Dense (Set.univ : Set ℝ) from dense_univ)
      |>.exists_seq_strictAnti_tendsto_of_lt htimeCeiling
  have happroachWithin : Tendsto approach atTop
      (nhdsWithin time (Set.Icc time 1)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨happroachTendsto,
      Filter.Eventually.of_forall fun stage ↦
        ⟨(happroachMem stage).1.1.le,
          (happroachMem stage).1.2.le.trans hceiling.2⟩⟩
  have htotalTendsto : Tendsto
      (fun stage ↦ pathTotal path.1 (approach stage)) atTop
      (nhds time) := by
    rw [← htime.2]
    unfold pathTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦
      (path.1.right_continuous coalition time htime.1).comp
        happroachWithin
  obtain ⟨stage, hstageTotal⟩ :=
    (htotalTendsto.eventually_lt_const htimeCeiling).exists
  have hstageMem : approach stage ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htime.1.1.trans (happroachMem stage).1.1.le,
      (happroachMem stage).1.2.le.trans hceiling.2⟩
  by_cases hclock : pathTotal path.1 (approach stage) = approach stage
  · exact ⟨approach stage, Or.inr ⟨hstageMem, hclock⟩,
      (happroachMem stage).1.1, (happroachMem stage).1.2⟩
  · let boundary := pathTotal path.1 (approach stage)
    have hstageBoundary : approach stage < boundary :=
      lt_of_le_of_ne (path.property.1 (approach stage) hstageMem)
        (Ne.symm hclock)
    exact ⟨boundary,
      pathTotal_mem_partitionBoundaryTimes path hpathTotal hstageMem,
      (happroachMem stage).1.1.trans hstageBoundary,
      hstageTotal⟩

/-- The resolution-`k` upper probe from a live clock cut. -/
def partitionProbe (resolution : ℕ) (start : ℝ) : ℝ :=
  start + (1 - start) / resolution

/-- The next cut in the published Proposition 4.8 recursion.  Besides
boundary times below the resolution probe, the candidate set contains the
current post-jump total, which copies a discrete jump in one literal row. -/
def nextPartitionCut (path : AbsorptionPath (ι := ι))
    (resolution : ℕ) (start : ℝ) : ℝ :=
  sSup (((partitionBoundaryTimes path) ∩
    Set.Iic (partitionProbe resolution start)) ∪
      {pathTotal path.1 start})

/-- The complete countable cut sequence used by the AKRS path decoder. -/
def partitionCut (path : AbsorptionPath (ι := ι))
    (resolution : ℕ) : ℕ → ℝ
  | 0 => 0
  | stage + 1 => nextPartitionCut path resolution
      (partitionCut path resolution stage)

omit [Nonempty ι] in
theorem partitionProbe_mem_Icc
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1) :
    partitionProbe resolution start ∈ Set.Icc start 1 := by
  have hresolutionReal : (1 : ℝ) ≤ resolution := by exact_mod_cast hresolution
  have hresolutionPos : (0 : ℝ) < resolution := zero_lt_one.trans_le hresolutionReal
  unfold partitionProbe
  constructor
  · exact le_add_of_nonneg_right
      (div_nonneg (sub_nonneg.mpr hstart.2) hresolutionPos.le)
  · have hdiv : (1 - start) / (resolution : ℝ) ≤ 1 - start :=
      div_le_self (sub_nonneg.mpr hstart.2) hresolutionReal
    linarith

omit [Nonempty ι] in
/-- At resolution at least two, the probe of a nonterminal cut is strictly
between that cut and one. -/
theorem partitionProbe_mem_Ioo
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Ico (0 : ℝ) 1) :
    partitionProbe resolution start ∈ Set.Ioo start 1 := by
  have hresolutionReal : (2 : ℝ) ≤ resolution := by
    exact_mod_cast hresolution
  have hresolutionPos : (0 : ℝ) < resolution := by positivity
  unfold partitionProbe
  constructor
  · exact lt_add_of_pos_right _ <|
      div_pos (sub_pos.mpr hstart.2) hresolutionPos
  · have hresolutionOne : (1 : ℝ) < resolution := by linarith
    have hdiv : (1 - start) / (resolution : ℝ) < 1 - start :=
      div_lt_self (sub_pos.mpr hstart.2) hresolutionOne
    linarith

omit [Nonempty ι] in
/-- Every next-cut candidate is bounded by one when the path total is. -/
theorem nextPartitionCut_mem_Icc
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1) :
    nextPartitionCut path resolution start ∈ Set.Icc start 1 := by
  let candidates : Set ℝ :=
    ((partitionBoundaryTimes path) ∩
      Set.Iic (partitionProbe resolution start)) ∪
        {pathTotal path.1 start}
  have hprobe := partitionProbe_mem_Icc resolution hresolution hstart
  have hupper : ∀ point ∈ candidates, point ≤ 1 := by
    intro point hpoint
    rcases hpoint with hboundary | htotal
    · exact hboundary.2.trans hprobe.2
    · simpa only [Set.mem_singleton_iff] using
        htotal ▸ hpathTotal start hstart
  have hbdd : BddAbove candidates := ⟨1, hupper⟩
  have htotalMem : pathTotal path.1 start ∈ candidates :=
    Or.inr (Set.mem_singleton _)
  have hnonempty : candidates.Nonempty :=
    ⟨pathTotal path.1 start, htotalMem⟩
  change sSup candidates ∈ Set.Icc start 1
  constructor
  · exact (path.property.1 start hstart).trans
      (le_csSup hbdd htotalMem)
  · exact csSup_le hnonempty hupper

omit [Nonempty ι] in
/-- The published supremum can overshoot the resolution probe only by copying
the current post-jump total. -/
theorem nextPartitionCut_le_max_probe_pathTotal
    (path : AbsorptionPath (ι := ι))
    (resolution : ℕ) (start : ℝ) :
    nextPartitionCut path resolution start ≤
      max (partitionProbe resolution start) (pathTotal path.1 start) := by
  let candidates : Set ℝ :=
    ((partitionBoundaryTimes path) ∩
      Set.Iic (partitionProbe resolution start)) ∪
        {pathTotal path.1 start}
  have hupper : ∀ point ∈ candidates,
      point ≤ max (partitionProbe resolution start)
        (pathTotal path.1 start) := by
    intro point hpoint
    rcases hpoint with hboundary | htotal
    · exact hboundary.2.trans (le_max_left _ _)
    · rw [Set.mem_singleton_iff.mp htotal]
      exact le_max_right _ _
  have hnonempty : candidates.Nonempty :=
    ⟨pathTotal path.1 start, Or.inr (Set.mem_singleton _)⟩
  exact csSup_le hnonempty hupper

omit [Nonempty ι] in
/-- The next cut always lies at or after the current post-jump total. -/
theorem pathTotal_le_nextPartitionCut
    (path : AbsorptionPath (ι := ι))
    (resolution : ℕ) (start : ℝ) :
    pathTotal path.1 start ≤ nextPartitionCut path resolution start := by
  let candidates : Set ℝ :=
    ((partitionBoundaryTimes path) ∩
      Set.Iic (partitionProbe resolution start)) ∪
        {pathTotal path.1 start}
  have hbdd : BddAbove candidates := by
    refine ⟨max (partitionProbe resolution start)
      (pathTotal path.1 start), ?_⟩
    intro point hpoint
    rcases hpoint with hboundary | htotal
    · exact hboundary.2.trans (le_max_left _ _)
    · rw [Set.mem_singleton_iff.mp htotal]
      exact le_max_right _ _
  exact le_csSup hbdd (Or.inr (Set.mem_singleton _))

omit [Nonempty ι] in
/-- A post-jump total strictly beyond the resolution probe is copied exactly
as the next cut. -/
theorem nextPartitionCut_eq_pathTotal_of_probe_lt
    (path : AbsorptionPath (ι := ι))
    (resolution : ℕ) (start : ℝ)
    (hlarge : partitionProbe resolution start < pathTotal path.1 start) :
    nextPartitionCut path resolution start = pathTotal path.1 start := by
  apply le_antisymm
  · exact (nextPartitionCut_le_max_probe_pathTotal path resolution start).trans_eq
      (max_eq_right hlarge.le)
  · let candidates : Set ℝ :=
      ((partitionBoundaryTimes path) ∩
        Set.Iic (partitionProbe resolution start)) ∪
          {pathTotal path.1 start}
    have hbdd : BddAbove candidates := by
      refine ⟨pathTotal path.1 start, ?_⟩
      intro point hpoint
      rcases hpoint with hboundary | htotal
      · exact hboundary.2.trans hlarge.le
      · rw [Set.mem_singleton_iff.mp htotal]
    exact le_csSup hbdd (Or.inr (Set.mem_singleton _))

omit [Nonempty ι] in
/-- Outside the copied-jump arm, the next cut remains below the resolution
probe. -/
theorem nextPartitionCut_le_probe_of_pathTotal_le
    (path : AbsorptionPath (ι := ι))
    (resolution : ℕ) (start : ℝ)
    (hsmall : pathTotal path.1 start ≤ partitionProbe resolution start) :
    nextPartitionCut path resolution start ≤
      partitionProbe resolution start := by
  exact (nextPartitionCut_le_max_probe_pathTotal path resolution start).trans_eq
    (max_eq_left hsmall)

omit [Nonempty ι] in
/-- The initial clock zero is always a partition boundary: either it is a
clock time or the path has a literal initial jump. -/
theorem zero_mem_partitionBoundaryTimes
    (path : AbsorptionPath (ι := ι)) :
    (0 : ℝ) ∈ partitionBoundaryTimes path := by
  by_cases hzero : pathTotal path.1 0 = 0
  · exact Or.inr ⟨by norm_num, hzero⟩
  · apply Or.inl
    refine ⟨by norm_num, ?_⟩
    by_contra hnoJump
    have hcoordinateZero (coalition : {S : Finset ι // S.Nonempty}) :
        pathJump path.1 0 coalition = 0 := by
      by_contra hcoalition
      exact hnoJump ⟨coalition, hcoalition⟩
    have hsumJump : (∑ coalition, pathJump path.1 0 coalition) = 0 := by
      simp [hcoordinateZero]
    rw [← pathTotal_sub_pathLeftTotal_eq_sum_pathJump] at hsumJump
    have hleftZero : pathLeftTotal path.1 0 = 0 := by
      simp [pathLeftTotal, path.1.left_zero]
    rw [hleftZero, sub_zero] at hsumJump
    exact hzero hsumJump

omit [Nonempty ι] in
/-- Every successor selected by the published supremum recursion is itself a
literal jump or continuous-clock boundary. -/
theorem nextPartitionCut_mem_partitionBoundaryTimes
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1) :
    nextPartitionCut path resolution start ∈
      partitionBoundaryTimes path := by
  let candidates : Set ℝ :=
    ((partitionBoundaryTimes path) ∩
      Set.Iic (partitionProbe resolution start)) ∪
        {pathTotal path.1 start}
  have htotalBoundary : pathTotal path.1 start ∈
      partitionBoundaryTimes path :=
    pathTotal_mem_partitionBoundaryTimes path hpathTotal hstart
  have hsourceBoundary : candidates ⊆ partitionBoundaryTimes path := by
    intro point hpoint
    exact hpoint.elim And.left fun htotal ↦
      Set.mem_singleton_iff.mp htotal ▸ htotalBoundary
  have hnonempty : candidates.Nonempty :=
    ⟨pathTotal path.1 start, Or.inr (Set.mem_singleton _)⟩
  have hbdd : BddAbove candidates := by
    refine ⟨1, ?_⟩
    intro point hpoint
    exact (hsourceBoundary hpoint).elim And.left And.left |>.2
  apply csSup_mem_partitionBoundaryTimes path hnonempty hsourceBoundary hbdd
  change nextPartitionCut path resolution start ∈ Set.Icc (0 : ℝ) 1
  have hnext := nextPartitionCut_mem_Icc path hpathTotal
    resolution hresolution hstart
  exact ⟨hstart.1.trans hnext.1, hnext.2⟩

omit [Nonempty ι] in
/-- A nonterminal partition boundary has post-total strictly below one. -/
theorem pathTotal_lt_one_of_boundary
    (path : AbsorptionPath (ι := ι))
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    {start : ℝ} (hstart : start ∈ Set.Ico (0 : ℝ) 1)
    (hstartBoundary : start ∈ partitionBoundaryTimes path) :
    pathTotal path.1 start < 1 := by
  rcases hstartBoundary with hjump | hclock
  · exact hnoTerminalJump start hjump
  · rw [hclock.2]
    exact hstart.2

omit [Nonempty ι] in
/-- Starting from a nonterminal boundary, a resolution-at-least-two successor
is still strictly below one. -/
theorem nextPartitionCut_lt_one
    (path : AbsorptionPath (ι := ι))
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Ico (0 : ℝ) 1)
    (hstartBoundary : start ∈ partitionBoundaryTimes path) :
    nextPartitionCut path resolution start < 1 := by
  exact (nextPartitionCut_le_max_probe_pathTotal path resolution start).trans_lt <|
    max_lt (partitionProbe_mem_Ioo resolution hresolution hstart).2
      (pathTotal_lt_one_of_boundary path hnoTerminalJump hstart
        hstartBoundary)

omit [Nonempty ι] in
/-- Every nonterminal boundary advances strictly at the next recursive cut. -/
theorem lt_nextPartitionCut
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Ico (0 : ℝ) 1)
    (hstartBoundary : start ∈ partitionBoundaryTimes path) :
    start < nextPartitionCut path resolution start := by
  rcases hstartBoundary with hjump | hclock
  · exact (lt_pathTotal_of_mem_pathJumps path hjump).trans_le
      (pathTotal_le_nextPartitionCut path resolution start)
  · have hprobe := partitionProbe_mem_Ioo resolution hresolution hstart
    have hprobeMem : partitionProbe resolution start ∈
        Set.Icc (0 : ℝ) 1 :=
      ⟨hstart.1.trans hprobe.1.le, hprobe.2.le⟩
    obtain ⟨boundary, hboundary, hstartBoundaryLt, hboundaryProbe⟩ :=
      exists_partitionBoundaryTimes_between_of_mem_pathTimes path
        hpathTotal hclock hprobeMem hprobe.1
    let candidates : Set ℝ :=
      ((partitionBoundaryTimes path) ∩
        Set.Iic (partitionProbe resolution start)) ∪
          {pathTotal path.1 start}
    have hbdd : BddAbove candidates := by
      refine ⟨max (partitionProbe resolution start)
        (pathTotal path.1 start), ?_⟩
      intro point hpoint
      rcases hpoint with hcandidate | htotal
      · exact hcandidate.2.trans (le_max_left _ _)
      · rw [Set.mem_singleton_iff.mp htotal]
        exact le_max_right _ _
    exact hstartBoundaryLt.trans_le <|
      le_csSup hbdd (Or.inl ⟨hboundary, hboundaryProbe.le⟩)

omit [Nonempty ι] in
@[simp] theorem partitionCut_zero
    (path : AbsorptionPath (ι := ι)) (resolution : ℕ) :
    partitionCut path resolution 0 = 0 :=
  rfl

omit [Nonempty ι] in
theorem partitionCut_succ
    (path : AbsorptionPath (ι := ι)) (resolution stage : ℕ) :
    partitionCut path resolution (stage + 1) =
      nextPartitionCut path resolution (partitionCut path resolution stage) :=
  rfl

omit [Nonempty ι] in
/-- All recursively selected cuts stay in the path clock interval. -/
theorem partitionCut_mem_Icc
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    (stage : ℕ) :
    partitionCut path resolution stage ∈ Set.Icc (0 : ℝ) 1 := by
  induction stage with
  | zero => simp
  | succ stage ih =>
      rw [partitionCut_succ]
      have hnext := nextPartitionCut_mem_Icc path hpathTotal
        resolution hresolution ih
      exact ⟨ih.1.trans hnext.1, hnext.2⟩

omit [Nonempty ι] in
/-- Every recursive cut is a literal jump or continuous-clock boundary. -/
theorem partitionCut_mem_partitionBoundaryTimes
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    (stage : ℕ) :
    partitionCut path resolution stage ∈
      partitionBoundaryTimes path := by
  induction stage with
  | zero => exact zero_mem_partitionBoundaryTimes path
  | succ stage _ =>
      rw [partitionCut_succ]
      exact nextPartitionCut_mem_partitionBoundaryTimes path hpathTotal
        resolution hresolution
        (partitionCut_mem_Icc path hpathTotal resolution hresolution stage)

omit [Nonempty ι] in
/-- Under the no-terminal-jump hypothesis, every finite recursive cut remains
strictly below one. -/
theorem partitionCut_lt_one
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 2 ≤ resolution)
    (stage : ℕ) :
    partitionCut path resolution stage < 1 := by
  have hresolutionOne : 1 ≤ resolution := by omega
  induction stage with
  | zero => simp
  | succ stage ih =>
      rw [partitionCut_succ]
      exact nextPartitionCut_lt_one path hnoTerminalJump resolution
        hresolution
        ⟨(partitionCut_mem_Icc path hpathTotal resolution
          hresolutionOne stage).1, ih⟩
        (partitionCut_mem_partitionBoundaryTimes path hpathTotal
          resolution hresolutionOne stage)

omit [Nonempty ι] in
/-- In at most two recursion steps, the cuts cross the current resolution
probe.  The possible intermediate step is exactly a boundary encountered
before the probe. -/
theorem partitionProbe_le_secondNextPartitionCut
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Icc (0 : ℝ) 1) :
    partitionProbe resolution start ≤
      nextPartitionCut path resolution
        (nextPartitionCut path resolution start) := by
  let middle := nextPartitionCut path resolution start
  have hmiddleFromStart := nextPartitionCut_mem_Icc path hpathTotal
    resolution hresolution hstart
  have hmiddleMem : middle ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hstart.1.trans hmiddleFromStart.1, hmiddleFromStart.2⟩
  have hmiddleBoundary : middle ∈ partitionBoundaryTimes path :=
    nextPartitionCut_mem_partitionBoundaryTimes path hpathTotal
      resolution hresolution hstart
  by_cases hprobeMiddle : partitionProbe resolution start ≤ middle
  · exact hprobeMiddle.trans <|
      (path.property.1 middle hmiddleMem).trans <|
        pathTotal_le_nextPartitionCut path resolution middle
  · have hmiddleProbe : middle < partitionProbe resolution start :=
      lt_of_not_ge hprobeMiddle
    have hprobeFromStart := partitionProbe_mem_Icc resolution hresolution hstart
    have hprobeMem : partitionProbe resolution start ∈
        Set.Icc (0 : ℝ) 1 :=
      ⟨hstart.1.trans hprobeFromStart.1, hprobeFromStart.2⟩
    have htotalBeyond : partitionProbe resolution start <
        pathTotal path.1 middle := by
      by_contra hnotBeyond
      have htotalLeProbe : pathTotal path.1 middle ≤
          partitionProbe resolution start := not_lt.mp hnotBeyond
      let candidates : Set ℝ :=
        ((partitionBoundaryTimes path) ∩
          Set.Iic (partitionProbe resolution start)) ∪
            {pathTotal path.1 start}
      have hbdd : BddAbove candidates := by
        refine ⟨1, ?_⟩
        intro point hpoint
        rcases hpoint with hboundary | htotal
        · exact (hboundary.1.elim And.left And.left).2
        · rw [Set.mem_singleton_iff.mp htotal]
          exact hpathTotal start hstart
      have hcandidateLe {point : ℝ} (hpoint : point ∈ candidates) :
          point ≤ middle := by
        exact le_csSup hbdd hpoint
      rcases (path.property.1 middle hmiddleMem).eq_or_lt with
        hfixed | hstrict
      · have hclock : middle ∈ pathTimes path.1 :=
          ⟨hmiddleMem, hfixed.symm⟩
        obtain ⟨boundary, hboundary, hmiddleBoundaryLt,
          hboundaryProbe⟩ :=
          exists_partitionBoundaryTimes_between_of_mem_pathTimes path
            hpathTotal hclock hprobeMem hmiddleProbe
        have hle : boundary ≤ middle := hcandidateLe <|
          Or.inl ⟨hboundary, hboundaryProbe.le⟩
        exact (not_le_of_gt hmiddleBoundaryLt) hle
      · have htotalBoundary : pathTotal path.1 middle ∈
            partitionBoundaryTimes path :=
          pathTotal_mem_partitionBoundaryTimes path hpathTotal hmiddleMem
        have hle : pathTotal path.1 middle ≤ middle :=
          hcandidateLe (Or.inl ⟨htotalBoundary, htotalLeProbe⟩)
        exact (not_le_of_gt hstrict) hle
    exact htotalBeyond.le.trans
      (pathTotal_le_nextPartitionCut path resolution middle)

omit [Nonempty ι] in
/-- The published cut recursion is monotone. -/
theorem monotone_partitionCut
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution) :
    Monotone (partitionCut path resolution) := by
  exact monotone_nat_of_le_succ fun stage => by
    rw [partitionCut_succ]
    exact (nextPartitionCut_mem_Icc path hpathTotal resolution hresolution
      (partitionCut_mem_Icc path hpathTotal resolution hresolution stage)).1

omit [Nonempty ι] in
/-- Every pair of recursive steps crosses the resolution probe based at the
earlier cut. -/
theorem partitionProbe_partitionCut_le_add_two
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    (stage : ℕ) :
    partitionProbe resolution (partitionCut path resolution stage) ≤
      partitionCut path resolution (stage + 2) := by
  rw [show stage + 2 = (stage + 1) + 1 by omega,
    partitionCut_succ, partitionCut_succ]
  exact partitionProbe_le_secondNextPartitionCut path hpathTotal
    resolution hresolution
    (partitionCut_mem_Icc path hpathTotal resolution hresolution stage)

omit [Nonempty ι] in
/-- The published recursive cuts converge to the terminal clock one. -/
theorem tendsto_partitionCut_one
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution) :
    Tendsto (partitionCut path resolution) atTop (nhds 1) := by
  let cuts := partitionCut path resolution
  let limit : ℝ := ⨆ stage, cuts stage
  have hmono : Monotone cuts :=
    monotone_partitionCut path hpathTotal resolution hresolution
  have hbdd : BddAbove (Set.range cuts) := by
    refine ⟨1, ?_⟩
    rintro point ⟨stage, rfl⟩
    exact (partitionCut_mem_Icc path hpathTotal resolution hresolution stage).2
  have htendsto : Tendsto cuts atTop (nhds limit) :=
    tendsto_atTop_ciSup hmono hbdd
  have hlimitLe : limit ≤ 1 := by
    dsimp only [limit]
    exact ciSup_le fun stage ↦
      (partitionCut_mem_Icc path hpathTotal resolution hresolution stage).2
  have hprobeTendsto : Tendsto
      (fun stage ↦ partitionProbe resolution (cuts stage)) atTop
      (nhds (partitionProbe resolution limit)) := by
    unfold partitionProbe
    exact htendsto.add ((tendsto_const_nhds.sub htendsto).div_const _)
  have hshiftTendsto : Tendsto (fun stage ↦ cuts (stage + 2)) atTop
      (nhds limit) :=
    htendsto.comp (tendsto_add_atTop_nat 2)
  have hprobeLimit : partitionProbe resolution limit ≤ limit :=
    le_of_tendsto_of_tendsto hprobeTendsto hshiftTendsto <|
      Filter.Eventually.of_forall fun stage ↦
        partitionProbe_partitionCut_le_add_two path hpathTotal
          resolution hresolution stage
  have hresolutionPos : (0 : ℝ) < resolution := by
    exact_mod_cast (Nat.zero_lt_of_lt hresolution)
  have hdiv : (1 - limit) / (resolution : ℝ) ≤ 0 := by
    unfold partitionProbe at hprobeLimit
    linarith
  have hlimitGe : 1 ≤ limit := by
    have hnumerator : 1 - limit ≤ 0 := by
      have := (div_le_iff₀ hresolutionPos).mp hdiv
      simpa using this
    linarith
  have hlimit : limit = 1 := le_antisymm hlimitLe hlimitGe
  simpa only [hlimit] using htendsto

omit [Nonempty ι] in
/-- A boundary whose post-total lies beyond its probe is necessarily a
literal jump boundary. -/
theorem mem_pathJumps_of_probe_lt_pathTotal_of_boundary
    (path : AbsorptionPath (ι := ι))
    (resolution : ℕ) {start : ℝ}
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hlarge : partitionProbe resolution start < pathTotal path.1 start) :
    start ∈ pathJumps path.1 := by
  rcases hstartBoundary with hjump | hclock
  · exact hjump
  · exact False.elim <| (not_le_of_gt hlarge) <|
      hclock.2.le.trans <|
        le_add_of_nonneg_right (div_nonneg
          (sub_nonneg.mpr hclock.1.2) (Nat.cast_nonneg resolution))

end QuittingAbsorptionPath
end GameTheory
