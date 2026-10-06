import MathUE.Topology.AmbientDegreeNonlinearLocalIndex
import MathUE.Topology.AmbientDegreeSelfMapNormalization
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.Equiv

/-! # The actual index of a unique cube-valued fixed point

Local nonlinear index, ambient excision, and the existing self-map degree
normalization supply the index. The expanded chart contains zero and sure
coordinates in its interior. There is no face index or new degree definition.
Finite-coordinate transport uses ordinary continuous linear equivalences and
the existing determinant conjugation theorem.
-/

noncomputable section

namespace Math.Topology

open Set Filter _root_.Topology

theorem sign_det_eq_one_of_unique_cubeValued_fixedPoint
    {n : ℕ} (map : (Fin n → ℝ) → Fin n → ℝ) (hcontinuous : Continuous map)
    (hcube : ∀ point, map point ∈ Icc (fun _ => 0) (fun _ => 1))
    (root : Fin n → ℝ) (hfixed : map root = root)
    (hunique : ∀ point, map point = point → point = root)
    (derivative : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hdiff : HasFDerivAt (fun point => point - map point) derivative root)
    (hdet : (LinearMap.toMatrix' derivative.toLinearMap).det ≠ 0) :
    (SignType.sign (LinearMap.toMatrix' derivative.toLinearMap).det : ℤ) = 1 := by
  let center : Fin n → ℝ := fun _ => 1 / 2
  let region := Math.affineRootRegion center 2
  have hopen : IsOpen region := isOpen_affineRootRegion center 2
  have hbounded : Bornology.IsBounded region := isBounded_affineRootRegion center 2
  have hrootCube : root ∈ Icc (fun _ => 0) (fun _ => 1) := by
    simpa only [hfixed] using hcube root
  have hrootRegion : root ∈ region := by
    intro who
    have hlow := hrootCube.1 who
    have hhigh := hrootCube.2 who
    change 1 / 2 - 2 / 2 < root who ∧ root who < 1 / 2 + 2 / 2
    constructor <;> linarith
  have hclosure : closure region ⊆
      {point | ∀ who, (-2 : ℝ) < point who ∧ point who < 3} := by
    intro point hpoint who
    have hbound := closure_affineRootRegion_subset center (by norm_num : (0 : ℝ) < 2)
      hpoint who
    dsimp [center] at hbound
    constructor <;> linarith [hbound.1, hbound.2]
  have hself : MapsTo map (Icc (fun _ => (-2 : ℝ)) (fun _ => 3))
      (Icc (fun _ => (-2 : ℝ)) (fun _ => 3)) := by
    intro point _
    constructor
    · intro who
      have := (hcube point).1 who
      linarith
    · intro who
      have := (hcube point).2 who
      linarith
  have hretain : ∀ point ∈ Icc (fun _ => (-2 : ℝ)) (fun _ => 3),
      point = map point → point ∈ region := by
    intro point _ hpoint
    rw [hunique point hpoint.symm]
    exact hrootRegion
  have hfrontier := selfMapField_ne_zero_on_frontier
    (fun _ => (-2 : ℝ)) (fun _ => 3) map region hopen hclosure hretain
  have htotal := ambientDegree_of_selfMap_eq_one (fun _ => (-2 : ℝ)) (fun _ => 3)
    (by intro who; norm_num) map hcontinuous hself region hopen hbounded hclosure hretain
  obtain ⟨radius, hpositive, hsmallClosure, _hisolated, hlocal, hlocalFrontier, hindex⟩ :=
    exists_ambientDegree_eq_sign_det_of_hasFDerivAt_on_nhds
      (fun point => point - map point) root derivative region (hopen.mem_nhds hrootRegion)
      (continuous_id.sub hcontinuous).continuousOn (by rw [hfixed, sub_self]) hdiff hdet
  have hsmallSubset : Math.affineRootRegion root radius ⊆ region :=
    subset_closure.trans hsmallClosure
  have hsmallRoot : root ∈ Math.affineRootRegion root radius := by
    intro who
    constructor <;> linarith
  have hfiber : ∀ point ∈ region, point - map point = 0 →
      point ∈ Math.affineRootRegion root radius := by
    intro point _ hzero
    rw [hunique point (sub_eq_zero.mp hzero).symm]
    exact hsmallRoot
  have hexcision := ambientDegree_excision (fun point => point - map point)
    region (Math.affineRootRegion root radius) 0 hopen hbounded
    (continuous_id.sub hcontinuous).continuousOn hfrontier
    (isOpen_affineRootRegion root radius) hsmallSubset hfiber
  have hlocalOne : ambientDegree (fun point => point - map point)
      (Math.affineRootRegion root radius) 0 (isOpen_affineRootRegion root radius)
      (isBounded_affineRootRegion root radius) hlocal hlocalFrontier = 1 :=
    hexcision.symm.trans htotal
  exact hindex.symm.trans hlocalOne

theorem exists_fixedPoint_ne_of_negative_det
    {n : ℕ} (map : (Fin n → ℝ) → Fin n → ℝ) (hcontinuous : Continuous map)
    (hcube : ∀ point, map point ∈ Icc (fun _ => 0) (fun _ => 1))
    (root : Fin n → ℝ) (hfixed : map root = root)
    (derivative : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hdiff : HasFDerivAt (fun point => point - map point) derivative root)
    (hnegative : (LinearMap.toMatrix' derivative.toLinearMap).det < 0) :
    ∃ point, map point = point ∧ point ≠ root := by
  by_contra hnone
  have hunique : ∀ point, map point = point → point = root := by
    intro point hpoint
    by_contra hne
    exact hnone ⟨point, hpoint, hne⟩
  have hindex := sign_det_eq_one_of_unique_cubeValued_fixedPoint map hcontinuous hcube
    root hfixed hunique derivative hdiff (ne_of_lt hnegative)
  rw [sign_neg hnegative] at hindex
  norm_num at hindex

/-- Arbitrary finite coordinate names are transported to the existing ambient
degree chart. Determinant conjugation, not a game-specific index, preserves
the actual derivative's determinant. -/
theorem exists_fixedPoint_ne_of_negative_det_finite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (map : (ι → ℝ) → ι → ℝ) (hcontinuous : Continuous map)
    (hcube : ∀ point, map point ∈ Icc (fun _ => 0) (fun _ => 1))
    (root : ι → ℝ) (hfixed : map root = root)
    (derivative : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hdiff : HasFDerivAt (fun point => point - map point) derivative root)
    (hnegative : (LinearMap.toMatrix' derivative.toLinearMap).det < 0) :
    ∃ point, map point = point ∧ point ≠ root := by
  let equivalence := (Fintype.equivFin ι).symm
  let reindex := (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : ι => ℝ) equivalence).symm
  let pulledMap := fun point => reindex (map (reindex.symm point))
  let pulledDerivative := reindex.toContinuousLinearMap.comp
    (derivative.comp reindex.symm.toContinuousLinearMap)
  have hmapContinuous : Continuous pulledMap :=
    reindex.continuous.comp (hcontinuous.comp reindex.symm.continuous)
  have hmapCube : ∀ point, pulledMap point ∈ Icc (fun _ => 0) (fun _ => 1) := by
    intro point
    constructor
    · intro who
      exact (hcube (reindex.symm point)).1 (equivalence who)
    · intro who
      exact (hcube (reindex.symm point)).2 (equivalence who)
  have hmapFixed : pulledMap (reindex root) = reindex root := by
    simp only [pulledMap, reindex.symm_apply_apply, hfixed]
  have hfieldDerivative : HasFDerivAt
      (fun point => point - pulledMap point) pulledDerivative (reindex root) := by
    have hdiffBase : HasFDerivAt (fun point => point - map point) derivative
        (reindex.symm (reindex root)) := by
      simpa only [reindex.symm_apply_apply] using hdiff
    have hinner := hdiffBase.comp (reindex root)
      reindex.symm.toContinuousLinearMap.hasFDerivAt
    have houter := reindex.toContinuousLinearMap.hasFDerivAt.comp (reindex root) hinner
    apply houter.congr_of_eventuallyEq
    filter_upwards [] with point
    change point - reindex (map (reindex.symm point)) =
      reindex (reindex.symm point - map (reindex.symm point))
    rw [reindex.map_sub, reindex.apply_symm_apply]
  have hdet : (LinearMap.toMatrix' pulledDerivative.toLinearMap).det =
      (LinearMap.toMatrix' derivative.toLinearMap).det := by
    rw [LinearMap.det_toMatrix', LinearMap.det_toMatrix']
    exact LinearMap.det_conj derivative.toLinearMap reindex.toLinearEquiv
  obtain ⟨point, hpoint, hne⟩ := exists_fixedPoint_ne_of_negative_det pulledMap
    hmapContinuous hmapCube (reindex root) hmapFixed pulledDerivative hfieldDerivative
    (by rw [hdet]; exact hnegative)
  refine ⟨reindex.symm point, ?_, ?_⟩
  · apply reindex.injective
    simpa only [reindex.apply_symm_apply, pulledMap] using hpoint
  · intro heq
    exact hne (by simpa only [reindex.apply_symm_apply] using congrArg reindex heq)

end Math.Topology
