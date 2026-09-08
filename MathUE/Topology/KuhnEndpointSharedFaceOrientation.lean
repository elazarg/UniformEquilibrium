import MathUE.Topology.OrientedSimplexFacetDeterminant
import FixedPointTheorems.cubical_sperner_prep

/-!
# Opposite orientations of endpoint-sharing Kuhn parents

Two actual full-dimensional ordered Kuhn simplices whose endpoint deletions
give the same face have reflected apices. The pinned full-simplex coordinate
increment identity supplies that reflection, hence their induced facet
determinants cancel. This treats faces between adjacent grid boxes, not yet
the interior-deletion case within one box.
-/

noncomputable section

namespace Math.KuhnSharedFace

open OrientedSimplexFacet

/-- Actual endpoint-sharing parents have opposite induced facet determinants.
The same common face is kept in its inherited increasing vertex order. -/
theorem endpointParents_facetDeterminant_add_eq_zero
    (cube : SpernerCube) (hdimension : 0 < cube.n)
    (lower upper : Fin (cube.n + 1) → cube.G)
    (hlower : simplex cube cube.n lower) (hupper : simplex cube cube.n upper)
    (hface : ∀ kept : Fin cube.n, lower kept.succ = upper kept.castSucc) :
    facetDeterminant (fun kept coordinate => ((lower kept.succ coordinate).val : ℤ))
        (fun coordinate => ((lower 0 coordinate).val : ℤ)) +
      facetDeterminant (fun kept coordinate => ((lower kept.succ coordinate).val : ℤ))
        (fun coordinate => ((upper (Fin.last cube.n) coordinate).val : ℤ)) = 0 := by
  cases cube with
  | mk dimension resolution label hlabel =>
    cases dimension with
    | zero => simp at hdimension
    | succ dimension =>
      apply facetDeterminant_add_eq_zero_of_reflection _ _ _ 0 (Fin.last dimension)
      funext coordinate
      have hlow := last_eq_first_add_one _ lower hlower coordinate
      have hupp := last_eq_first_add_one _ upper hupper coordinate
      change (lower (Fin.last (dimension + 1)) coordinate).val =
        (lower 0 coordinate).val + 1 at hlow
      change (upper (Fin.last (dimension + 1)) coordinate).val =
        (upper 0 coordinate).val + 1 at hupp
      have hstart := congrArg (fun vertex => (vertex coordinate).val) (hface 0)
      simp only [Pi.add_apply]
      norm_cast
      simp only [Fin.castSucc_zero, Fin.succ_last, Nat.succ_eq_add_one] at hstart hlow hupp ⊢
      omega

/-- The same actual shared face gives cancellation with the explicit
alternating endpoint-deletion signs on the two full cell determinants. -/
theorem endpointParents_signed_determinant_add_eq_zero
    (cube : SpernerCube) (hdimension : 0 < cube.n)
    (lower upper : Fin (cube.n + 1) → cube.G)
    (hlower : simplex cube cube.n lower) (hupper : simplex cube cube.n upper)
    (hface : ∀ kept : Fin cube.n, lower kept.succ = upper kept.castSucc) :
    determinant (fun vertex coordinate => ((lower vertex coordinate).val : ℤ)) +
      (-1) ^ cube.n *
        determinant (fun vertex coordinate => ((upper vertex coordinate).val : ℤ)) = 0 := by
  have h := endpointParents_facetDeterminant_add_eq_zero
    cube hdimension lower upper hlower hupper hface
  have hlowerFace := facetDeterminant_delete
    (fun vertex coordinate => ((lower vertex coordinate).val : ℤ)) 0
  have hupperFace := facetDeterminant_delete
    (fun vertex coordinate => ((upper vertex coordinate).val : ℤ)) (Fin.last cube.n)
  have hfaceCast : (fun (kept : Fin cube.n) coordinate =>
      ((lower kept.succ coordinate).val : ℤ)) =
      (fun (kept : Fin cube.n) coordinate => ((upper kept.castSucc coordinate).val : ℤ)) := by
    funext kept coordinate
    rw [hface]
  simp only [Fin.succAbove_zero, Fin.val_zero, pow_zero, one_mul] at hlowerFace
  simp only [Fin.succAbove_last, Fin.val_last] at hupperFace
  rw [hlowerFace, hfaceCast, hupperFace] at h
  exact h

end Math.KuhnSharedFace
