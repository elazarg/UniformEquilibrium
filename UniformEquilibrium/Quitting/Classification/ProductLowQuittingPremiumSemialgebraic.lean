import MathUE.Semialgebraic.FiniteQuantification
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumPolynomial

/-! # Semialgebraicity of product-low real reward tables -/

noncomputable section

namespace GameTheory

variable {n : Nat}

/-- Product-low recognition with unrestricted real reward entries defines a
semialgebraic subset of the fixed reward-table coordinate space. -/
theorem isSemialgebraic_hasProductLowQuittingPremium_rewardTables :
    MathUE.IsSemialgebraic {table |
      HasProductLowQuittingPremium
        (quittingRewardTableFromCoordinates (n := n) table)} := by
  let rewardCoordinates := Fintype.card (QuittingRewardTableVariable (Fin n))
  let hazardVariable : Fin n →
      MvPolynomial (Fin (rewardCoordinates + n)) ℝ := fun player =>
    MvPolynomial.X (quittingProductLowHazardCoordinate player)
  have hnonnegative : MathUE.IsSemialgebraic {point |
      ∀ player : Fin n, 0 ≤ MvPolynomial.eval point (hazardVariable player)} := by
    have hall := MathUE.IsSemialgebraic.forall_finset (Finset.univ : Finset (Fin n))
      (fun player point => 0 ≤ MvPolynomial.eval point (hazardVariable player))
      (fun player _ => MathUE.IsSemialgebraic.polynomial_nonneg
        (hazardVariable player))
    simpa only [Finset.mem_univ, forall_const] using hall
  have hatMostOne : MathUE.IsSemialgebraic {point |
      ∀ player : Fin n, MvPolynomial.eval point (hazardVariable player) ≤ 1} := by
    have hall := MathUE.IsSemialgebraic.forall_finset (Finset.univ : Finset (Fin n))
      (fun player point => MvPolynomial.eval point (hazardVariable player) ≤ 1)
      (fun player _ => by
        have hnonpos :=
          MathUE.IsSemialgebraic.polynomial_nonpos (hazardVariable player - 1)
        convert hnonpos using 1
        ext point
        simp only [Set.mem_setOf_eq, map_sub, map_one, sub_nonpos])
    simpa only [Finset.mem_univ, forall_const] using hall
  have hactive : MathUE.IsSemialgebraic {point |
      ∃ player : Fin n, 0 < MvPolynomial.eval point (hazardVariable player)} := by
    have hexists := MathUE.IsSemialgebraic.exists_finset
      (Finset.univ : Finset (Fin n))
      (fun player point => 0 < MvPolynomial.eval point (hazardVariable player))
      (fun player _ => MathUE.IsSemialgebraic.polynomial_pos
        (hazardVariable player))
    convert hexists using 1
    ext point
    simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and]
  have hlow : MathUE.IsSemialgebraic {point |
      ∃ player : Fin n,
        0 < MvPolynomial.eval point (hazardVariable player) ∧
          MvPolynomial.eval point (quittingProductLowPremiumPolynomial player) ≤ 0} := by
    have hexists := MathUE.IsSemialgebraic.exists_finset
      (Finset.univ : Finset (Fin n))
      (fun player point =>
        0 < MvPolynomial.eval point (hazardVariable player) ∧
          MvPolynomial.eval point (quittingProductLowPremiumPolynomial player) ≤ 0)
      (fun player _ =>
        (MathUE.IsSemialgebraic.polynomial_pos (hazardVariable player)).inter
          (MathUE.IsSemialgebraic.polynomial_nonpos
            (quittingProductLowPremiumPolynomial player)))
    convert hexists using 1
    ext point
    simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and]
  have hjoint : MathUE.IsSemialgebraic {point |
      ((∀ player : Fin n, 0 ≤ MvPolynomial.eval point (hazardVariable player)) ∧
          (∀ player : Fin n, MvPolynomial.eval point (hazardVariable player) ≤ 1) ∧
          (∃ player : Fin n, 0 < MvPolynomial.eval point (hazardVariable player))) →
        ∃ player : Fin n,
          0 < MvPolynomial.eval point (hazardVariable player) ∧
            MvPolynomial.eval point
              (quittingProductLowPremiumPolynomial player) ≤ 0} := by
    have himp := ((hnonnegative.inter hatMostOne).inter hactive).compl.union hlow
    convert himp using 1
    ext point
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro himp
      by_cases habc :
          ((∀ player : Fin n,
              0 ≤ MvPolynomial.eval point (hazardVariable player)) ∧
            (∀ player : Fin n,
              MvPolynomial.eval point (hazardVariable player) ≤ 1)) ∧
            ∃ player : Fin n,
              0 < MvPolynomial.eval point (hazardVariable player)
      · exact Or.inr (himp ⟨habc.1.1, habc.1.2, habc.2⟩)
      · exact Or.inl habc
    · intro h habc
      rcases h with hnot | hlowAtPoint
      · exact (hnot ⟨⟨habc.1, habc.2.1⟩, habc.2.2⟩).elim
      · exact hlowAtPoint
  have hforall := hjoint.forall_last_coordinates
  convert hforall using 1
  ext table
  simp only [Set.mem_setOf_eq]
  rw [hasProductLowQuittingPremium_iff_hazard]
  constructor
  · intro hlowProduct hazard
    rintro ⟨hzero, hone, hactive⟩
    have hzero' : ∀ player : Fin n, 0 ≤ hazard player := by
      simpa only [hazardVariable, rewardCoordinates, MvPolynomial.eval_X,
        quittingProductLowHazardCoordinate, Fin.append_right] using hzero
    have hone' : ∀ player : Fin n, hazard player ≤ 1 := by
      simpa only [hazardVariable, rewardCoordinates, MvPolynomial.eval_X,
        quittingProductLowHazardCoordinate, Fin.append_right] using hone
    have hactive' : ∃ player : Fin n, 0 < hazard player := by
      simpa only [hazardVariable, rewardCoordinates, MvPolynomial.eval_X,
        quittingProductLowHazardCoordinate, Fin.append_right] using hactive
    have hresult := hlowProduct hazard hzero' hone' hactive'
    simp only [quittingProductLowHazardCoordinate, Fin.append_right,
      eval_quittingProductLowPremiumPolynomial, hazardVariable,
      rewardCoordinates, MvPolynomial.eval_X]
    exact hresult
  · intro hprojected hazard hzero hone hactive
    have hresult := hprojected hazard (show
      (∀ player : Fin n,
          0 ≤ MvPolynomial.eval (Fin.append table hazard)
            (hazardVariable player)) ∧
        (∀ player : Fin n,
          MvPolynomial.eval (Fin.append table hazard)
            (hazardVariable player) ≤ 1) ∧
        ∃ player : Fin n,
          0 < MvPolynomial.eval (Fin.append table hazard)
            (hazardVariable player) by
      simp only [hazardVariable, rewardCoordinates, MvPolynomial.eval_X,
        quittingProductLowHazardCoordinate, Fin.append_right]
      exact ⟨hzero, hone, hactive⟩)
    simpa only [hazardVariable, rewardCoordinates, MvPolynomial.eval_X,
      quittingProductLowHazardCoordinate, Fin.append_right,
      eval_quittingProductLowPremiumPolynomial] using hresult

end GameTheory
