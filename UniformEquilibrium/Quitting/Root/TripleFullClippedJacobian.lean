import UniformEquilibrium.Quitting.Root.TripleEndpointPartials
import Mathlib.Tactic.FinCases

/-! # The full ambient triple determinant and its two directed cycles

The actual gap partials determine the canonical derivative's determinant at
any hazard vector. Proper exact Nash and strict inactive gaps identify that
operator as the actual full clipped displacement derivative. Its off-support
columns are not removed. A positive sum of the two directed cycles gives a
negative nonsingular determinant; individual partials may be signed.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingRealHazardEndpointPartial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (point : ι → ℝ) (row column : ι) : ℝ :=
  fderiv ℝ (fun hazard => quittingRealHazardEndpointGap reward tail hazard row)
    point (Pi.single column 1)

theorem quittingRealHazardEndpointPartial_pos_of_triple_joining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsupport : quittingPositiveHazardSupport root ⊆ {first, second, third})
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hfirst : (root first true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (root second true).toReal ∈ Ioo (0 : ℝ) 1)
    (hthird : (root third true).toReal < 1)
    (hpair : 0 < quittingPairJoiningGap reward first second)
    (htriple : 0 ≤ quittingTripleJoiningGap reward first second third) :
    0 < quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) first second := by
  unfold quittingRealHazardEndpointPartial
  rw [quittingRealHazardEndpointGap_triple_cross_partial_of_exactNash reward tail root
    hfirstSecond hfirstThird hsecondThird hsupport hnash hfirst hsecond hthird]
  apply mul_pos (div_pos (sub_pos.mpr hthird) (sub_pos.mpr hsecond.2))
  apply add_pos_of_pos_of_nonneg hpair
  exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) htriple

theorem quittingRealHazardEndpointPartial_neg_of_triple_joining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsupport : quittingPositiveHazardSupport root ⊆ {first, second, third})
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hfirst : (root first true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (root second true).toReal ∈ Ioo (0 : ℝ) 1)
    (hthird : (root third true).toReal < 1)
    (hpair : quittingPairJoiningGap reward first second < 0)
    (htriple : quittingTripleJoiningGap reward first second third ≤ 0) :
    quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) first second < 0 := by
  unfold quittingRealHazardEndpointPartial
  rw [quittingRealHazardEndpointGap_triple_cross_partial_of_exactNash reward tail root
    hfirstSecond hfirstThird hsecondThird hsupport hnash hfirst hsecond hthird]
  apply mul_neg_of_pos_of_neg (div_pos (sub_pos.mpr hthird) (sub_pos.mpr hsecond.2))
  apply add_neg_of_neg_of_nonpos hpair
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) htriple

omit [Fintype ι] in
private def tripleCoordinateEquiv {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Fin 3 ≃ {who // who ∈ ({first, second, third} : Finset ι)} where
  toFun index := if index = 0 then ⟨first, by simp⟩
    else if index = 1 then ⟨second, by simp⟩ else ⟨third, by simp⟩
  invFun who := if who.val = first then 0 else if who.val = second then 1 else 2
  left_inv := by
    intro index
    fin_cases index <;> simp [hfirstSecond.symm, hfirstThird.symm, hsecondThird.symm]
  right_inv := by
    rintro ⟨who, hwho⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
    rcases hwho with rfl | rfl | rfl <;>
      simp [hfirstSecond.symm, hfirstThird.symm, hsecondThird.symm]

theorem quittingFullClippedDisplacementDerivative_triple_det
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (point : ι → ℝ) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second, third}
        point).toLinearMap).det =
      -(quittingRealHazardEndpointPartial reward tail point first second *
          quittingRealHazardEndpointPartial reward tail point second third *
          quittingRealHazardEndpointPartial reward tail point third first +
        quittingRealHazardEndpointPartial reward tail point first third *
          quittingRealHazardEndpointPartial reward tail point second first *
          quittingRealHazardEndpointPartial reward tail point third second) := by
  rw [quittingFullClippedDisplacementDerivative_det_eq_active_det]
  rw [← Matrix.det_submatrix_equiv_self
    (tripleCoordinateEquiv hfirstSecond hfirstThird hsecondThird)]
  rw [Matrix.det_fin_three]
  have hcoordinateZero :
      (tripleCoordinateEquiv hfirstSecond hfirstThird hsecondThird (0 : Fin 3)).val = first :=
    rfl
  have hcoordinateOne :
      (tripleCoordinateEquiv hfirstSecond hfirstThird hsecondThird (1 : Fin 3)).val = second :=
    rfl
  have hcoordinateTwo :
      (tripleCoordinateEquiv hfirstSecond hfirstThird hsecondThird (2 : Fin 3)).val = third :=
    rfl
  have hfirstMem : first ∈ ({first, second, third} : Finset ι) := by simp
  have hsecondMem : second ∈ ({first, second, third} : Finset ι) := by simp
  have hthirdMem : third ∈ ({first, second, third} : Finset ι) := by simp
  simp only [Matrix.submatrix_apply, hcoordinateZero, hcoordinateOne, hcoordinateTwo,
    quittingFullClippedDisplacementDerivative_matrix_entry, hfirstMem, hsecondMem, hthirdMem,
    ite_true, quittingRealHazardEndpointGap_own_partial_eq_zero]
  unfold quittingRealHazardEndpointPartial
  ring

theorem tripleNash_hasFDerivAt_and_negative_det_fullClippedDisplacement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsupport : quittingPositiveHazardSupport root = {first, second, third})
    (hproper : ∀ player ∈ ({first, second, third} : Finset ι),
      (root player true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hnegative : ∀ player ∉ ({first, second, third} : Finset ι),
      quittingRootEndpointDifference reward tail root player < 0)
    (hcycles : 0 <
      quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) first second *
        quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) second third *
        quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) third first +
      quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) first third *
        quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) second first *
        quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) third second) :
    HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
      (quittingFullClippedDisplacementDerivative reward tail {first, second, third}
        (hazardOfRoot root)) (hazardOfRoot root) ∧
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second, third}
        (hazardOfRoot root)).toLinearMap).det < 0 ∧
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second, third}
        (hazardOfRoot root)).toLinearMap).det ≠ 0 := by
  have hdiff := hasFDerivAt_quittingFullClippedDisplacement_of_properSupportNash
    reward tail root {first, second, third} hsupport hproper hnash hnegative
  have hdet : (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second, third}
        (hazardOfRoot root)).toLinearMap).det < 0 := by
    rw [quittingFullClippedDisplacementDerivative_triple_det reward tail (hazardOfRoot root)
      hfirstSecond hfirstThird hsecondThird]
    exact neg_neg_of_pos hcycles
  exact ⟨hdiff, hdet, ne_of_lt hdet⟩

theorem tripleNash_negative_det_of_positive_partials
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsupport : quittingPositiveHazardSupport root = {first, second, third})
    (hproper : ∀ player ∈ ({first, second, third} : Finset ι),
      (root player true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hnegative : ∀ player ∉ ({first, second, third} : Finset ι),
      quittingRootEndpointDifference reward tail root player < 0)
    (hpositive : ∀ row ∈ ({first, second, third} : Finset ι),
      ∀ column ∈ ({first, second, third} : Finset ι), row ≠ column →
        0 < quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) row column) :
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second, third}
        (hazardOfRoot root)).toLinearMap).det < 0 := by
  apply (tripleNash_hasFDerivAt_and_negative_det_fullClippedDisplacement reward tail root
    hfirstSecond hfirstThird hsecondThird hsupport hproper hnash hnegative ?_).2.1
  exact add_pos
    (mul_pos (mul_pos (hpositive first (by simp) second (by simp) hfirstSecond)
      (hpositive second (by simp) third (by simp) hsecondThird))
      (hpositive third (by simp) first (by simp) hfirstThird.symm))
    (mul_pos (mul_pos (hpositive first (by simp) third (by simp) hfirstThird)
      (hpositive second (by simp) first (by simp) hfirstSecond.symm))
      (hpositive third (by simp) second (by simp) hsecondThird.symm))

theorem tripleNash_negative_det_of_mixed_partials
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsupport : quittingPositiveHazardSupport root = {first, second, third})
    (hproper : ∀ player ∈ ({first, second, third} : Finset ι),
      (root player true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hnegative : ∀ player ∉ ({first, second, third} : Finset ι),
      quittingRootEndpointDifference reward tail root player < 0)
    (hpartials :
      0 < quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) first second ∧
      0 < quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) second first ∧
      quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) first third < 0 ∧
      quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) second third < 0 ∧
      quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) third first < 0 ∧
      quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) third second < 0) :
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second, third}
        (hazardOfRoot root)).toLinearMap).det < 0 := by
  rcases hpartials with ⟨h12, h21, h13, h23, h31, h32⟩
  apply (tripleNash_hasFDerivAt_and_negative_det_fullClippedDisplacement reward tail root
    hfirstSecond hfirstThird hsecondThird hsupport hproper hnash hnegative ?_).2.1
  exact add_pos
    (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg h12 h23) h31)
    (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos h13 h21) h32)

end GameTheory
