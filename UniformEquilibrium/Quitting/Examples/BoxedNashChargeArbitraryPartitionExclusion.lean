import MathUE.LinearProgramming.CyclicChildSharedPartitionClassification
import UniformEquilibrium.Quitting.Examples.BoxedNashChargeAxisResponse
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantFiniteLabels

/-! # Every response-invariant block map of the boxed fixtures is discrete

The shared matrix forces either injectivity or the pivot/child partition.
Actual nonlinear responses exclude the latter. Arbitrary original labels are
compressed without a finiteness or surjectivity assumption.
-/

noncomputable section

namespace GameTheory.BoxedNashChargeSharedMatrix

open Math.CyclicChildJointPhase.SharedFixture

private theorem full_finite_block_injective {k : ℕ} (block : Fin 4 → Fin k)
    (hresponse : QuittingResponseInvariantOnUnitCube BoxedNashChargeFullCoreFixture.reward
      block) : Function.Injective block := by
  have hrows : ∀ first second, block first = block second →
      ∀ coordinate, labelRowSum block first coordinate = labelRowSum block second coordinate := by
    intro first second hsame coordinate
    have heq := quittingSingletonBlockRowSum_eq_of_responseInvariant
      BoxedNashChargeFullCoreFixture.reward block hresponse first second hsame coordinate
    simpa only [quittingSingletonBlockRowSum, labelRowSum, full_singletonMatrix_eq] using heq
  rcases injective_or_child_block_of_labelRowSum_eq block hrows with hinj | ⟨h01, h12, h23⟩
  · exact hinj
  · have h03 : block 0 ≠ block 3 := fun h => h01 (h.trans (h12.trans h23).symm)
    let point : Fin k → ℝ := fun coordinate => if coordinate = block 0 then 1 / 2 else 0
    have hpoint : ∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1 := by
      intro coordinate
      dsimp only [point]
      split_ifs <;> norm_num
    have heq := hresponse point hpoint 1 2 h12
    have hlift : quittingBlockLift block point = singletonRow (1 / 2) 0 := by
      funext player
      fin_cases player <;>
        simp [quittingBlockLift, point, singletonRow, h12, h23, Ne.symm h03]
    rw [hlift] at heq
    have hfirst := full_axis_response (1 / 2) 0
    have hsecond := full_axis_response (1 / 2) 1
    norm_num at hfirst hsecond
    rw [hfirst, hsecond] at heq
    norm_num at heq

private theorem triple_label_rowSum_reindex {k : ℕ} (block : Fin 4 → Fin k)
    (receiver : Fin 4) (coordinate : Fin k) :
    quittingSingletonBlockRowSum BoxedNashChargeTripleFixture.reward block
      (canonicalToTriple receiver) coordinate =
        labelRowSum (fun player => block (canonicalToTriple player)) receiver coordinate := by
  unfold quittingSingletonBlockRowSum labelRowSum
  rw [← canonicalToTriple.sum_comp (fun owner =>
    if block owner = coordinate then
      QuittingLCPClassification.quittingSingletonMatrix BoxedNashChargeTripleFixture.reward
        (canonicalToTriple receiver) owner else 0)]
  change (∑ owner, if block (canonicalToTriple owner) = coordinate then
    Matrix.submatrix
      (QuittingLCPClassification.quittingSingletonMatrix BoxedNashChargeTripleFixture.reward)
      canonicalToTriple canonicalToTriple receiver owner else 0) = _
  rw [triple_singletonMatrix_relabel_eq]

private theorem triple_finite_block_injective {k : ℕ} (block : Fin 4 → Fin k)
    (hresponse : QuittingResponseInvariantOnUnitCube BoxedNashChargeTripleFixture.reward
      block) : Function.Injective block := by
  have hrows : ∀ first second,
      block (canonicalToTriple first) = block (canonicalToTriple second) →
      ∀ coordinate,
        labelRowSum (fun player => block (canonicalToTriple player)) first coordinate =
          labelRowSum (fun player => block (canonicalToTriple player)) second coordinate := by
    intro first second hsame coordinate
    have heq := quittingSingletonBlockRowSum_eq_of_responseInvariant
      BoxedNashChargeTripleFixture.reward block hresponse
      (canonicalToTriple first) (canonicalToTriple second) hsame coordinate
    rw [triple_label_rowSum_reindex, triple_label_rowSum_reindex] at heq
    exact heq
  rcases injective_or_child_block_of_labelRowSum_eq
      (fun player => block (canonicalToTriple player)) hrows with hinj | ⟨h30, h01, h12⟩
  · intro first second hsame
    apply canonicalToTriple.symm.injective
    apply hinj
    simpa only [Equiv.apply_symm_apply] using hsame
  · change block 3 ≠ block 0 at h30
    change block 0 = block 1 at h01
    change block 1 = block 2 at h12
    have h32 : block 3 ≠ block 2 := fun h => h30 (h.trans (h01.trans h12).symm)
    let point : Fin k → ℝ := fun coordinate => if coordinate = block 3 then 1 / 2 else 0
    have hpoint : ∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1 := by
      intro coordinate
      dsimp only [point]
      split_ifs <;> norm_num
    have heq := hresponse point hpoint 0 1 h01
    have hlift : quittingBlockLift block point = singletonRow (1 / 2) 3 := by
      funext player
      fin_cases player <;>
        simp [quittingBlockLift, point, singletonRow, h01, h12, Ne.symm h32]
    rw [hlift] at heq
    have hfirst := triple_axis_response (1 / 2) 0
    have hsecond := triple_axis_response (1 / 2) 1
    norm_num at hfirst hsecond
    rw [hfirst, hsecond] at heq
    norm_num at heq

theorem full_block_injective_of_responseInvariant {κ : Type*} (block : Fin 4 → κ)
    (hresponse : QuittingResponseInvariantOnUnitCube BoxedNashChargeFullCoreFixture.reward
      block) : Function.Injective block := by
  obtain ⟨compressed, hsame, hinvariant⟩ := exists_responseInvariant_finite_compression
    BoxedNashChargeFullCoreFixture.reward block hresponse
  have hinj := full_finite_block_injective compressed hinvariant
  intro first second heq
  exact hinj ((hsame first second).mpr heq)

theorem triple_block_injective_of_responseInvariant {κ : Type*} (block : Fin 4 → κ)
    (hresponse : QuittingResponseInvariantOnUnitCube BoxedNashChargeTripleFixture.reward
      block) : Function.Injective block := by
  obtain ⟨compressed, hsame, hinvariant⟩ := exists_responseInvariant_finite_compression
    BoxedNashChargeTripleFixture.reward block hresponse
  have hinj := triple_finite_block_injective compressed hinvariant
  intro first second heq
  exact hinj ((hsame first second).mpr heq)

end GameTheory.BoxedNashChargeSharedMatrix
