/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.ClockGap
import UniformEquilibrium.Quitting.AbsorptionPath.ContinuousPath

/-!
# Clock gaps imply absorption-path axiom A2

For a càdlàg coalition path, clock domination and the clock-gap law force each
component outside the jump and clock-time sets to be one plateau.  This is the
decoder-facing form of absorption-path axiom A2.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Finset Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem sum_leftValue_eq_of_clockGap
    (path : CadlagPath (ι := ι))
    (hgap : MathUE.HasClockGapOn (pathTotal path) (Icc (0 : ℝ) 1))
    {base time : ℝ} (hbase : base ∈ Icc (0 : ℝ) 1)
    (htime : time ∈ Icc (0 : ℝ) 1) (hbaseTime : base < time)
    (htimeGap : time ≤ pathTotal path base) :
    (∑ coalition, path.leftValue time coalition) = pathTotal path base := by
  let leftFilter := 𝓝[Icc (0 : ℝ) time \ {time}] time
  have hsubset : Ioo base time ⊆ Icc (0 : ℝ) time \ {time} := by
    intro point hpoint
    exact ⟨⟨hbase.1.trans hpoint.1.le, hpoint.2.le⟩, hpoint.2.ne⟩
  letI : leftFilter.NeBot :=
    (right_nhdsWithin_Ioo_neBot hbaseTime).mono
      (nhdsWithin_mono time hsubset)
  have hsumTendsto : Tendsto (fun point ↦ pathTotal path point) leftFilter
      (𝓝 (∑ coalition, path.leftValue time coalition)) := by
    unfold pathTotal
    exact tendsto_finsetSum Finset.univ fun coalition _ ↦
      path.left_limit coalition time htime
  have heventually : ∀ᶠ point in leftFilter,
      pathTotal path point = pathTotal path base := by
    have hfilter : leftFilter ≤ 𝓝 time := by
      exact inf_le_left
    have hbaseEventually : ∀ᶠ point in leftFilter, point ∈ Ioi base :=
      Filter.Eventually.filter_mono hfilter (Ioi_mem_nhds hbaseTime)
    filter_upwards [self_mem_nhdsWithin,
      hbaseEventually] with point hpoint hbasePoint
    have hpointTime : point < time :=
      lt_of_le_of_ne hpoint.1.2 hpoint.2
    have hpointMem : point ∈ Icc (0 : ℝ) 1 :=
      ⟨hpoint.1.1, hpointTime.le.trans htime.2⟩
    exact hgap hbase hpointMem hbasePoint.le
      (hpointTime.trans_le htimeGap)
  have hconstantTendsto : Tendsto (fun point ↦ pathTotal path point)
      leftFilter (𝓝 (pathTotal path base)) :=
    tendsto_const_nhds.congr' <|
      heventually.mono fun _ hpoint ↦ hpoint.symm
  exact tendsto_nhds_unique hsumTendsto hconstantTendsto

omit [DecidableEq ι] in
private theorem pathJump_eq_zero_of_clockGap
    (path : CadlagPath (ι := ι))
    (hgap : MathUE.HasClockGapOn (pathTotal path) (Icc (0 : ℝ) 1))
    {base time : ℝ} (hbase : base ∈ Icc (0 : ℝ) 1)
    (htime : time ∈ Icc (0 : ℝ) 1) (hbaseTime : base < time)
    (htimeGap : time < pathTotal path base)
    (coalition : {S : Finset ι // S.Nonempty}) :
    pathJump path time coalition = 0 := by
  have htotalTime : pathTotal path time = pathTotal path base :=
    hgap hbase htime hbaseTime.le htimeGap
  have hsumLeft := sum_leftValue_eq_of_clockGap path hgap hbase htime
    hbaseTime htimeGap.le
  let leftFilter := 𝓝[Icc (0 : ℝ) time \ {time}] time
  have hsubset : Ioo base time ⊆ Icc (0 : ℝ) time \ {time} := by
    intro point hpoint
    exact ⟨⟨hbase.1.trans hpoint.1.le, hpoint.2.le⟩, hpoint.2.ne⟩
  letI : leftFilter.NeBot :=
    (right_nhdsWithin_Ioo_neBot hbaseTime).mono
      (nhdsWithin_mono time hsubset)
  have hleftLe (other : {S : Finset ι // S.Nonempty}) :
      path.leftValue time other ≤ path.value time other := by
    apply le_of_tendsto (path.left_limit other time htime)
    filter_upwards [self_mem_nhdsWithin] with point hpoint
    have hpointMem : point ∈ Icc (0 : ℝ) 1 :=
      ⟨hpoint.1.1, hpoint.1.2.trans htime.2⟩
    exact path.monotone other hpointMem htime hpoint.1.2
  have hsumJump : (∑ other, pathJump path time other) = 0 := by
    unfold pathJump
    rw [Finset.sum_sub_distrib]
    change pathTotal path time -
      (∑ other, path.leftValue time other) = 0
    rw [htotalTime, hsumLeft, sub_self]
  have hall : (fun other ↦ pathJump path time other) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg fun other ↦
      sub_nonneg.mpr (hleftLe other)).mp hsumJump
  exact congrFun hall coalition

omit [DecidableEq ι] in
private theorem pathTotal_mem_jumps_or_times_of_clockGap
    (path : CadlagPath (ι := ι))
    (hdomination : ∀ time ∈ Icc (0 : ℝ) 1,
      time ≤ pathTotal path time)
    (htotalLe : ∀ time ∈ Icc (0 : ℝ) 1,
      pathTotal path time ≤ 1)
    (hgap : MathUE.HasClockGapOn (pathTotal path) (Icc (0 : ℝ) 1))
    {base : ℝ}
    (hbase : base ∈ Icc (0 : ℝ) 1 \
      (pathJumps path ∪ pathTimes path)) :
    pathTotal path base ∈ pathJumps path ∪ pathTimes path := by
  let boundary := pathTotal path base
  have hbaseBoundary : base < boundary := by
    exact lt_of_le_of_ne (hdomination base hbase.1) <| by
      intro heq
      exact hbase.2 <| Or.inr ⟨hbase.1, by
        simpa only [boundary] using heq.symm⟩
  have hboundaryMem : boundary ∈ Icc (0 : ℝ) 1 :=
    ⟨hbase.1.1.trans hbaseBoundary.le, htotalLe base hbase.1⟩
  by_cases htime : pathTotal path boundary = boundary
  · exact Or.inr ⟨hboundaryMem, htime⟩
  · apply Or.inl
    refine ⟨hboundaryMem, ?_⟩
    have hstrict : boundary < pathTotal path boundary :=
      lt_of_le_of_ne (hdomination boundary hboundaryMem) (Ne.symm htime)
    have hsumLeft := sum_leftValue_eq_of_clockGap path hgap hbase.1
      hboundaryMem hbaseBoundary le_rfl
    by_contra hnoJump
    have hzero (coalition : {S : Finset ι // S.Nonempty}) :
        pathJump path boundary coalition = 0 := by
      by_contra hcoalition
      exact hnoJump ⟨coalition, hcoalition⟩
    have hsumJump : (∑ coalition, pathJump path boundary coalition) = 0 := by
      simp [hzero]
    unfold pathJump at hsumJump
    rw [Finset.sum_sub_distrib] at hsumJump
    change pathTotal path boundary -
      (∑ coalition, path.leftValue boundary coalition) = 0 at hsumJump
    rw [hsumLeft] at hsumJump
    linarith

omit [DecidableEq ι] in
private theorem Ico_subset_path_complement_of_clockGap
    (path : CadlagPath (ι := ι))
    (htotalLe : ∀ time ∈ Icc (0 : ℝ) 1,
      pathTotal path time ≤ 1)
    (hgap : MathUE.HasClockGapOn (pathTotal path) (Icc (0 : ℝ) 1))
    {base : ℝ}
    (hbase : base ∈ Icc (0 : ℝ) 1 \
      (pathJumps path ∪ pathTimes path)) :
    Ico base (pathTotal path base) ⊆
      Icc (0 : ℝ) 1 \ (pathJumps path ∪ pathTimes path) := by
  intro time htime
  by_cases heq : time = base
  · simpa only [heq] using hbase
  have hbaseTime : base < time := lt_of_le_of_ne htime.1 (Ne.symm heq)
  have htimeMem : time ∈ Icc (0 : ℝ) 1 :=
    ⟨hbase.1.1.trans htime.1,
      htime.2.le.trans (htotalLe base hbase.1)⟩
  have htotalTime : pathTotal path time = pathTotal path base :=
    hgap hbase.1 htimeMem htime.1 htime.2
  have hnotTime : time ∉ pathTimes path := by
    rintro ⟨_, heqTime⟩
    exact htime.2.ne (heqTime.symm.trans htotalTime)
  have hnotJump : time ∉ pathJumps path := by
    rintro ⟨_, coalition, hcoalition⟩
    exact hcoalition <| pathJump_eq_zero_of_clockGap path hgap hbase.1
      htimeMem hbaseTime htime.2 coalition
  exact ⟨htimeMem, fun hbad ↦ hbad.elim hnotJump hnotTime⟩

omit [DecidableEq ι] in
/-- Clock domination, a unit total-mass bound, and the clock-gap law imply
absorption-path axiom A2. -/
theorem absorptionPathA2_of_clockGap
    (path : CadlagPath (ι := ι))
    (hdomination : ∀ time ∈ Icc (0 : ℝ) 1,
      time ≤ pathTotal path time)
    (htotalLe : ∀ time ∈ Icc (0 : ℝ) 1,
      pathTotal path time ≤ 1)
    (hgap : MathUE.HasClockGapOn (pathTotal path) (Icc (0 : ℝ) 1)) :
    AbsorptionPathA2 path := by
  intro base hbase time htime
  let support := Icc (0 : ℝ) 1 \ (pathJumps path ∪ pathTimes path)
  have htimeSupport : time ∈ support :=
    connectedComponentIn_subset support base htime
  let boundary := pathTotal path time
  have htimeBoundary : time < boundary := by
    exact lt_of_le_of_ne (hdomination time htimeSupport.1) <| by
      intro heq
      exact htimeSupport.2 <| Or.inr ⟨htimeSupport.1, by
        simpa only [boundary] using heq.symm⟩
  let component := connectedComponentIn support time
  have hboundaryExcluded : boundary ∈ pathJumps path ∪ pathTimes path :=
    pathTotal_mem_jumps_or_times_of_clockGap path hdomination htotalLe hgap
      htimeSupport
  have hcomponentSubset : component ⊆ support :=
    connectedComponentIn_subset support time
  have hcomponentNonempty : component.Nonempty :=
    ⟨time, mem_connectedComponentIn htimeSupport⟩
  have hupper : ∀ point ∈ component, point ≤ boundary := by
    intro point hpoint
    by_contra hnotLe
    have hboundaryLt : boundary < point := lt_of_not_ge hnotLe
    have hboundaryComponent : boundary ∈ component :=
      isPreconnected_connectedComponentIn.ordConnected.out
        (mem_connectedComponentIn htimeSupport) hpoint
        ⟨htimeBoundary.le, hboundaryLt.le⟩
    exact (hcomponentSubset hboundaryComponent).2 hboundaryExcluded
  have hplateauSubset : Ico time boundary ⊆ component := by
    apply isPreconnected_Ico.subset_connectedComponentIn
      (left_mem_Ico.mpr htimeBoundary)
    exact Ico_subset_path_complement_of_clockGap path htotalLe hgap
      htimeSupport
  have hcofinal : ∀ point < boundary,
      ∃ member ∈ component, point < member := by
    intro point hpoint
    by_cases hpointTime : point < time
    · exact ⟨time, mem_connectedComponentIn htimeSupport, hpointTime⟩
    · let member := (point + boundary) / 2
      have hpointMember : point < member := by
        dsimp only [member]
        linarith
      have hmemberBoundary : member < boundary := by
        dsimp only [member]
        linarith
      have htimeMember : time ≤ member :=
        (not_lt.mp hpointTime).trans hpointMember.le
      exact ⟨member, hplateauSubset ⟨htimeMember, hmemberBoundary⟩,
        hpointMember⟩
  have hsup : sSup component = boundary :=
    csSup_eq_of_forall_le_of_forall_lt_exists_gt hcomponentNonempty hupper
      hcofinal
  have hcomponentEq :
      connectedComponentIn support base = connectedComponentIn support time :=
    connectedComponentIn_eq htime
  rw [hcomponentEq, hsup]

end GameTheory.QuittingAbsorptionPath
