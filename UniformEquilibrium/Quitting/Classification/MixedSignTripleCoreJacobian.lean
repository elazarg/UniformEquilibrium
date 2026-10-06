import UniformEquilibrium.Quitting.Classification.MixedSignTripleCoreSureClassification
import UniformEquilibrium.Quitting.Root.TripleFullClippedJacobian

/-! # Actual mixed-sign full triple derivatives

The printed equality stratum gives two positive and four negative actual
off-diagonal partials. Both directed triangle products are positive. Inactive
rows are handled by the full ambient clipping derivative, not a face index.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mixedSignTripleNash_hasFDerivAt_and_negative_det
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second third : ι} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hjoining : HasMixedSignTripleJoining reward first second third)
    (root : ι → PMF Bool)
    (hsupport : quittingPositiveHazardSupport root = {first, second, third})
    (hproper : ∀ player ∈ ({first, second, third} : Finset ι),
      (root player true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hnegative : ∀ player ∉ ({first, second, third} : Finset ι),
      quittingRootEndpointDifference reward tail root player < 0) :
    HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
      (quittingFullClippedDisplacementDerivative reward tail {first, second, third}
        (hazardOfRoot root)) (hazardOfRoot root) ∧
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second, third}
        (hazardOfRoot root)).toLinearMap).det < 0 := by
  have hpermuted : ∀ a b c : ι, ({a, b, c} : Finset ι) = {first, second, third} →
      quittingPositiveHazardSupport root ⊆ {a, b, c} := by
    intro a b c heq
    rw [heq]
    exact hsupport.subset
  have hsecondFirstThird : ({second, first, third} : Finset ι) = {first, second, third} := by
    ext player
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hfirstThirdSecond : ({first, third, second} : Finset ι) = {first, second, third} := by
    ext player
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hsecondThirdFirst : ({second, third, first} : Finset ι) = {first, second, third} := by
    ext player
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hthirdFirstSecond : ({third, first, second} : Finset ι) = {first, second, third} := by
    ext player
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hthirdSecondFirst : ({third, second, first} : Finset ι) = {first, second, third} := by
    ext player
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hfirst := hproper first (by simp)
  have hsecond := hproper second (by simp)
  have hthird := hproper third (by simp)
  have h12 := quittingRealHazardEndpointPartial_pos_of_triple_joining reward tail root
    hfirstSecond hfirstThird hsecondThird hsupport.subset hnash hfirst hsecond hthird.2
    hjoining.first_second_pos (le_of_eq hjoining.first_triple_zero.symm)
  have h21 := quittingRealHazardEndpointPartial_pos_of_triple_joining reward tail root
    hfirstSecond.symm hsecondThird hfirstThird (hpermuted _ _ _ hsecondFirstThird)
    hnash hsecond hfirst hthird.2 hjoining.second_first_pos
    (le_of_eq hjoining.second_triple_zero.symm)
  have hfirstThirdZero : quittingTripleJoiningGap reward first third second = 0 := by
    simpa only [quittingTripleJoiningGap, Finset.pair_comm] using hjoining.first_triple_zero
  have hsecondThirdZero : quittingTripleJoiningGap reward second third first = 0 := by
    simpa only [quittingTripleJoiningGap, Finset.pair_comm] using hjoining.second_triple_zero
  have hthirdSecondNeg : quittingTripleJoiningGap reward third second first < 0 := by
    simpa only [quittingTripleJoiningGap, Finset.pair_comm] using hjoining.third_triple_neg
  have h13 := quittingRealHazardEndpointPartial_neg_of_triple_joining reward tail root
    hfirstThird hfirstSecond hsecondThird.symm (hpermuted _ _ _ hfirstThirdSecond)
    hnash hfirst hthird hsecond.2 hjoining.first_third_neg (le_of_eq hfirstThirdZero)
  have h23 := quittingRealHazardEndpointPartial_neg_of_triple_joining reward tail root
    hsecondThird hfirstSecond.symm hfirstThird.symm (hpermuted _ _ _ hsecondThirdFirst)
    hnash hsecond hthird hfirst.2 hjoining.second_third_neg (le_of_eq hsecondThirdZero)
  have h31 := quittingRealHazardEndpointPartial_neg_of_triple_joining reward tail root
    hfirstThird.symm hsecondThird.symm hfirstSecond (hpermuted _ _ _ hthirdFirstSecond)
    hnash hthird hfirst hsecond.2 hjoining.third_first_neg hjoining.third_triple_neg.le
  have h32 := quittingRealHazardEndpointPartial_neg_of_triple_joining reward tail root
    hsecondThird.symm hfirstThird.symm hfirstSecond.symm (hpermuted _ _ _ hthirdSecondFirst)
    hnash hthird hsecond hfirst.2 hjoining.third_second_neg hthirdSecondNeg.le
  have hcycles := add_pos
    (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg h12 h23) h31)
    (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos h13 h21) h32)
  have hcertificate := tripleNash_hasFDerivAt_and_negative_det_fullClippedDisplacement
    reward tail root hfirstSecond hfirstThird hsecondThird hsupport hproper hnash
    hnegative hcycles
  exact ⟨hcertificate.1, hcertificate.2.1⟩

end GameTheory
