import MathUE.Semialgebraic.FiniteQuantification
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumInwardViolation
import UniformEquilibrium.Quitting.Root.RewardTableCoordinates

/-! # Semialgebraicity of product-low real reward tables -/

noncomputable section

namespace GameTheory

variable {n : Nat}

/-- A hazard coordinate in the last block of the joint reward-hazard layout. -/
def quittingProductLowHazardCoordinate (player : Fin n) :
    Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) + n) :=
  Fin.natAdd (Fintype.card (QuittingRewardTableVariable (Fin n))) player

/-- A reward coordinate in the first block of the joint reward-hazard layout. -/
def quittingProductLowRewardCoordinate
    (terminal : {S : Finset (Fin n) // S.Nonempty}) (observer : Fin n) :
    Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) + n) :=
  Fin.castAdd n
    (Fintype.equivFin (QuittingRewardTableVariable (Fin n)) (terminal, observer))

/-- The singleton-relative Quit premium, jointly polynomial in the reward table
and hazard coordinates. -/
def quittingProductLowPremiumPolynomial (player : Fin n) :
    MvPolynomial
      (Fin (Fintype.card (QuittingRewardTableVariable (Fin n)) + n)) ℝ :=
  ∑ coalition ∈ (Finset.univ.erase player).powerset,
    ((∏ other ∈ coalition,
        MvPolynomial.X (quittingProductLowHazardCoordinate other)) *
      ∏ other ∈ Finset.univ.erase player \ coalition,
        (1 - MvPolynomial.X (quittingProductLowHazardCoordinate other))) *
      (MvPolynomial.X (quittingProductLowRewardCoordinate
          ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player) -
        MvPolynomial.X (quittingProductLowRewardCoordinate
          (quittingSingletonTerminal player) player))

@[simp]
theorem eval_quittingProductLowPremiumPolynomial
    (table : Fin (Fintype.card (QuittingRewardTableVariable (Fin n))) → ℝ)
    (hazard : Fin n → ℝ) (player : Fin n) :
    MvPolynomial.eval (Fin.append table hazard)
        (quittingProductLowPremiumPolynomial player) =
      quittingHazardQuitPremium (quittingRewardTableFromCoordinates table)
        hazard player := by
  unfold quittingProductLowPremiumPolynomial quittingHazardQuitPremium
  simp only [map_sum, map_mul, map_prod, map_sub, MvPolynomial.eval_X, map_one,
    quittingProductLowHazardCoordinate, quittingProductLowRewardCoordinate,
    Fin.append_right, Fin.append_left, quittingRewardTableFromCoordinates]

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
