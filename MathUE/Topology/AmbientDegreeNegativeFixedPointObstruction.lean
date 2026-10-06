import MathUE.Topology.AmbientDegreeNonlinearLocalIndex
import MathUE.Topology.AmbientDegreeSelfMapNormalization
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.Equiv

/-! # A cube-valued map cannot have only negative regular fixed points

The actual compact fixed-point set is discrete by nonlinear local isolation,
hence finite. Binary ambient additivity then removes one isolated chart at a
time. The degree is nonpositive, contradicting the existing self-map degree
one normalization. No census, local index, or simultaneous neighborhood
selection is supplied. Dimension zero is included.
-/

noncomputable section

namespace Math.Topology

open Set Filter _root_.Topology

private theorem ambientDegree_nonpos_of_finite_negative_zeros
    {n : ℕ} (field : (Fin n → ℝ) → Fin n → ℝ) (hcontinuous : Continuous field)
    (zeros : Finset (Fin n → ℝ)) (region : Set (Fin n → ℝ))
    (hopen : IsOpen region) (hbounded : Bornology.IsBounded region)
    (hfrontier : ∀ point ∈ frontier region, field point ≠ 0)
    (hcover : ∀ point ∈ region, field point = 0 → point ∈ zeros)
    (hnegative : ∀ point ∈ region, field point = 0 →
      ∃ derivative : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
        HasFDerivAt field derivative point ∧
          (LinearMap.toMatrix' derivative.toLinearMap).det < 0) :
    ambientDegree field region 0 hopen hbounded hcontinuous.continuousOn hfrontier ≤ 0 := by
  classical
  induction zeros using Finset.induction_on generalizing region with
  | empty =>
      have hnone : ∀ point ∈ region, field point ≠ 0 := by
        intro point hpoint hzero
        simpa using hcover point hpoint hzero
      rw [ambientDegree_eq_zero_of_forall_ne field region 0 hopen hbounded
        hcontinuous.continuousOn hfrontier hnone]
  | @insert root zeros _hnotmem ih =>
      by_cases hroot : root ∈ region ∧ field root = 0
      · obtain ⟨derivative, hdiff, hdet⟩ := hnegative root hroot.1 hroot.2
        obtain ⟨radius, hpositive, hclosure, hisolated, hlocal, hlocalFrontier, hindex⟩ :=
          exists_ambientDegree_eq_sign_det_of_hasFDerivAt_on_nhds field root derivative
            region (hopen.mem_nhds hroot.1) hcontinuous.continuousOn hroot.2 hdiff
            (ne_of_lt hdet)
        let localRegion := Math.affineRootRegion root radius
        let remainder := region \ closure localRegion
        have hlocalOpen : IsOpen localRegion := isOpen_affineRootRegion root radius
        have hlocalSubset : localRegion ⊆ region := subset_closure.trans hclosure
        have hrootLocal : root ∈ localRegion := by
          intro coordinate
          constructor <;> linarith
        have hrestOpen : IsOpen remainder :=
          hopen.inter (isClosed_closure : IsClosed (closure localRegion)).isOpen_compl
        have hrestSubset : remainder ⊆ region := fun _ hpoint => hpoint.1
        have hdisjoint : Disjoint localRegion remainder := by
          apply Set.disjoint_left.mpr
          intro point hlocalPoint hrestPoint
          exact hrestPoint.2 (subset_closure hlocalPoint)
        have hsplit : ∀ point ∈ region, field point = 0 →
            point ∈ localRegion ∪ remainder := by
          intro point hpoint hzero
          by_cases hclosed : point ∈ closure localRegion
          · left
            rw [(hisolated point hclosed).mp hzero]
            exact hrootLocal
          · exact Or.inr ⟨hpoint, hclosed⟩
        have hrestFrontier := frontier_avoids_of_disjoint_rootCover field region remainder
          localRegion 0 hrestOpen hlocalOpen hrestSubset hdisjoint.symm hfrontier
          (fun point hpoint hzero => (hsplit point hpoint hzero).symm)
        have hrestCover : ∀ point ∈ remainder, field point = 0 → point ∈ zeros := by
          intro point hpoint hzero
          have hmem := hcover point hpoint.1 hzero
          rcases Finset.mem_insert.mp hmem with hequal | hmem
          · subst point
            exact (hpoint.2 (subset_closure hrootLocal)).elim
          · exact hmem
        have hrestNegative : ∀ point ∈ remainder, field point = 0 →
            ∃ derivative : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
              HasFDerivAt field derivative point ∧
                (LinearMap.toMatrix' derivative.toLinearMap).det < 0 :=
          fun point hpoint hzero => hnegative point hpoint.1 hzero
        have hrestDegree := ih remainder hrestOpen (hbounded.subset hrestSubset)
          hrestFrontier hrestCover hrestNegative
        have hlocalDegree : ambientDegree field localRegion 0 hlocalOpen
            (isBounded_affineRootRegion root radius) hlocal hlocalFrontier = -1 := by
          rw [hindex, sign_neg hdet]
          rfl
        have hadd := ambientDegree_additive field region localRegion remainder 0
          hopen hbounded hcontinuous.continuousOn hfrontier hlocalOpen hrestOpen
          hlocalSubset hrestSubset hdisjoint hsplit
        dsimp only at hadd
        linarith
      · apply ih region hopen hbounded hfrontier ?_ hnegative
        intro point hpoint hzero
        rcases Finset.mem_insert.mp (hcover point hpoint hzero) with hequal | hmem
        · subst point
          exact (hroot ⟨hpoint, hzero⟩).elim
        · exact hmem

theorem not_all_fixedPoints_have_negative_det
    {n : ℕ} (map : (Fin n → ℝ) → Fin n → ℝ) (hcontinuous : Continuous map)
    (hcube : ∀ point, map point ∈ Icc (fun _ => 0) (fun _ => 1)) :
    ¬(∀ point, map point = point →
      ∃ derivative : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
        HasFDerivAt (fun point => point - map point) derivative point ∧
          (LinearMap.toMatrix' derivative.toLinearMap).det < 0) := by
  classical
  intro hnegative
  let field := fun point => point - map point
  let fixed := {point | map point = point}
  have hfield : Continuous field := continuous_id.sub hcontinuous
  have hfixedClosed : IsClosed fixed := isClosed_eq hcontinuous continuous_id
  have hfixedCube : fixed ⊆ Icc (fun _ => 0) (fun _ => 1) := by
    intro point hpoint
    change map point = point at hpoint
    simpa only [hpoint] using hcube point
  have hcompact : IsCompact fixed := isCompact_Icc.of_isClosed_subset hfixedClosed hfixedCube
  have hdiscrete : IsDiscrete fixed := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro root hroot
    obtain ⟨derivative, hdiff, hdet⟩ := hnegative root hroot
    obtain ⟨radius, hpositive, _, hisolated, _, _, _⟩ :=
      exists_ambientDegree_eq_sign_det_of_hasFDerivAt_on_nhds field root derivative
        univ (by simp) hfield.continuousOn (by exact sub_eq_zero.mpr hroot.symm)
        hdiff (ne_of_lt hdet)
    refine ⟨Math.affineRootRegion root radius, isOpen_affineRootRegion root radius, ?_⟩
    ext point
    constructor
    · intro hpoint
      have hzero : field point = 0 := sub_eq_zero.mpr hpoint.2.symm
      exact Set.mem_singleton_iff.mpr ((hisolated point (subset_closure hpoint.1)).mp hzero)
    · intro hpoint
      obtain rfl := Set.mem_singleton_iff.mp hpoint
      refine ⟨?_, hroot⟩
      intro coordinate
      constructor <;> linarith
  have hfinite := hcompact.finite hdiscrete
  let center : Fin n → ℝ := fun _ => 1 / 2
  let region := Math.affineRootRegion center 2
  have hopen : IsOpen region := isOpen_affineRootRegion center 2
  have hbounded : Bornology.IsBounded region := isBounded_affineRootRegion center 2
  have hclosure : closure region ⊆
      {point | ∀ coordinate, (-2 : ℝ) < point coordinate ∧ point coordinate < 3} := by
    intro point hpoint coordinate
    have hbound := closure_affineRootRegion_subset center (by norm_num : (0 : ℝ) < 2)
      hpoint coordinate
    dsimp [center] at hbound
    constructor <;> linarith [hbound.1, hbound.2]
  have hself : MapsTo map (Icc (fun _ => (-2 : ℝ)) (fun _ => 3))
      (Icc (fun _ => (-2 : ℝ)) (fun _ => 3)) := by
    intro point _
    constructor
    · intro coordinate
      have := (hcube point).1 coordinate
      linarith
    · intro coordinate
      have := (hcube point).2 coordinate
      linarith
  have hretain : ∀ point ∈ Icc (fun _ => (-2 : ℝ)) (fun _ => 3),
      point = map point → point ∈ region := by
    intro point _ hfixed
    have hpointCube := hfixedCube hfixed.symm
    intro coordinate
    have hlow := hpointCube.1 coordinate
    have hhigh := hpointCube.2 coordinate
    change 1 / 2 - 2 / 2 < point coordinate ∧ point coordinate < 1 / 2 + 2 / 2
    constructor <;> linarith
  have hfrontier := selfMapField_ne_zero_on_frontier
    (fun _ => (-2 : ℝ)) (fun _ => 3) map region hopen hclosure hretain
  have htotal := ambientDegree_of_selfMap_eq_one (fun _ => (-2 : ℝ)) (fun _ => 3)
    (by intro coordinate; norm_num) map hcontinuous hself region hopen hbounded hclosure hretain
  have hcover : ∀ point ∈ region, field point = 0 → point ∈ hfinite.toFinset := by
    intro point _ hzero
    exact hfinite.mem_toFinset.mpr (sub_eq_zero.mp hzero).symm
  have hnonpos := ambientDegree_nonpos_of_finite_negative_zeros field hfield
    hfinite.toFinset region hopen hbounded hfrontier hcover
    (fun point _ hzero => hnegative point (sub_eq_zero.mp hzero).symm)
  linarith

theorem not_all_fixedPoints_have_negative_det_finite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (map : (ι → ℝ) → ι → ℝ) (hcontinuous : Continuous map)
    (hcube : ∀ point, map point ∈ Icc (fun _ => 0) (fun _ => 1)) :
    ¬(∀ point, map point = point →
      ∃ derivative : (ι → ℝ) →L[ℝ] (ι → ℝ),
        HasFDerivAt (fun point => point - map point) derivative point ∧
          (LinearMap.toMatrix' derivative.toLinearMap).det < 0) := by
  intro hnegative
  let equivalence := (Fintype.equivFin ι).symm
  let reindex := (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : ι => ℝ) equivalence).symm
  let pulledMap := fun point => reindex (map (reindex.symm point))
  have hmapContinuous : Continuous pulledMap :=
    reindex.continuous.comp (hcontinuous.comp reindex.symm.continuous)
  have hmapCube : ∀ point, pulledMap point ∈ Icc (fun _ => 0) (fun _ => 1) := by
    intro point
    exact ⟨fun who => (hcube (reindex.symm point)).1 (equivalence who),
      fun who => (hcube (reindex.symm point)).2 (equivalence who)⟩
  apply not_all_fixedPoints_have_negative_det pulledMap hmapContinuous hmapCube
  intro point hfixed
  have horiginal : map (reindex.symm point) = reindex.symm point := by
    apply reindex.injective
    simpa only [pulledMap, reindex.apply_symm_apply] using hfixed
  obtain ⟨derivative, hdiff, hdet⟩ := hnegative (reindex.symm point) horiginal
  let pulledDerivative := reindex.toContinuousLinearMap.comp
    (derivative.comp reindex.symm.toContinuousLinearMap)
  have hinner := hdiff.comp point reindex.symm.toContinuousLinearMap.hasFDerivAt
  have houter := reindex.toContinuousLinearMap.hasFDerivAt.comp point hinner
  have hnormalized : HasFDerivAt (fun point => point - pulledMap point)
      pulledDerivative point := by
    apply houter.congr_of_eventuallyEq
    filter_upwards [] with next
    change next - reindex (map (reindex.symm next)) =
      reindex (reindex.symm next - map (reindex.symm next))
    rw [reindex.map_sub, reindex.apply_symm_apply]
  refine ⟨pulledDerivative, hnormalized, ?_⟩
  have hconjugate : (LinearMap.toMatrix' pulledDerivative.toLinearMap).det =
      (LinearMap.toMatrix' derivative.toLinearMap).det := by
    rw [LinearMap.det_toMatrix', LinearMap.det_toMatrix']
    exact LinearMap.det_conj derivative.toLinearMap reindex.toLinearEquiv
  rwa [hconjugate]

end Math.Topology
