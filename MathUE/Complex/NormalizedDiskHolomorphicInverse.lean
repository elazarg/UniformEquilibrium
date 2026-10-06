module

public import MathUE.Complex.NormalizedDiskBijection
public import MathUE.Complex.HolomorphicInjectiveInverse

/-! # A normalized disk bijection with its actual holomorphic inverse

The forward map comes from the constructed derivative maximum. The inverse is
the actual `invFunOn`, whose holomorphicity follows from the generic removable-
singularity proof. Neither derivative nonvanishing nor an inverse is supplied
as an additional hypothesis. No closed-disk extension is asserted.
-/

public section

namespace Math.ComplexAnalysis

open Set Metric Function

theorem exists_normalized_disk_holomorphic_inverse {U : Set ℂ}
    (hU : IsOpen U) (hconnected : IsSimplyConnected U) (hproper : U ≠ univ)
    {base : ℂ} (hbase : base ∈ U) :
    ∃ f g : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f U (ball 0 1) ∧ BijOn g (ball 0 1) U ∧
      LeftInvOn g f U ∧ RightInvOn g f (ball 0 1) ∧
      f base = 0 ∧ g 0 = base ∧ (∀ z ∈ U, deriv f z ≠ 0) ∧
      (∀ w ∈ ball 0 1, deriv g w ≠ 0) := by
  classical
  obtain ⟨f, hfd, hfbij, hfzero⟩ :=
    exists_bijOn_unitBall_map_eq_zero hU hconnected hproper hbase
  have hgd := differentiableOn_invFunOn_of_holomorphic_injOn hU hfd hfbij.injOn
  rw [hfbij.image_eq] at hgd
  have hleft := hfbij.injOn.leftInvOn_invFunOn
  have hright := hfbij.surjOn.rightInvOn_invFunOn
  have hgbij : BijOn (invFunOn f U) (ball 0 1) U :=
    hfbij.invOn_invFunOn.symm.bijOn hfbij.surjOn.mapsTo_invFunOn hfbij.mapsTo
  refine ⟨f, invFunOn f U, hfd, hgd, hfbij,
    hgbij, hleft, hright, hfzero, ?_, ?_, ?_⟩
  · simpa only [hfzero] using hleft hbase
  · intro z hz
    exact deriv_ne_zero_of_holomorphic_injOn hU hfd hfbij.injOn hz
  · intro w hw
    exact deriv_ne_zero_of_holomorphic_injOn isOpen_ball hgd hgbij.injOn hw

end Math.ComplexAnalysis
