import MathUE.LinearAlgebra.RationalAffineFunctional
import Mathlib.Analysis.Convex.Topology

/-!
# Sign control from supplied finite affine partitions

This module does not construct Bernstein coefficients.  It consumes a
supplied finite nonnegative partition-of-unity expansion and proves both its
pointwise sign consequences and the openness of the exact rational-affine
coefficient chamber.  Tensor Bernstein bases are one intended supplier.
-/

noncomputable section

open Finset Set

namespace Math

variable {Coordinate Index Term Parameter PositiveIndex NegativeIndex : Type*}

namespace RationalAffineFunctional

/-- Evaluation of a rational-affine functional is continuous on a finite
real coordinate space. -/
theorem continuous_eval [Fintype Coordinate]
    (functional : RationalAffineFunctional Coordinate) :
    Continuous functional.eval := by
  apply continuous_const.add
  exact continuous_finsetSum Finset.univ fun coordinate _ =>
    continuous_const.mul (continuous_apply coordinate)

end RationalAffineFunctional

/-- The simultaneous strict-positive chamber cut out by a finite family of
rational-affine functionals. -/
def StrictPositiveRationalAffineChamber [Fintype Coordinate]
    [Fintype Index]
    (functional : Index → RationalAffineFunctional Coordinate) :
    Set (Coordinate → ℝ) :=
  {point | ∀ index, 0 < (functional index).eval point}

/-- A finite strict rational-affine chamber is open. -/
theorem isOpen_strictPositiveRationalAffineChamber
    [Fintype Coordinate] [Fintype Index]
    (functional : Index → RationalAffineFunctional Coordinate) :
    IsOpen (StrictPositiveRationalAffineChamber functional) := by
  rw [show StrictPositiveRationalAffineChamber functional =
      ⋂ index, {point | 0 < (functional index).eval point} by
    ext point
    simp [StrictPositiveRationalAffineChamber]]
  apply isOpen_iInter_of_finite
  intro index
  exact isOpen_lt continuous_const
    (RationalAffineFunctional.continuous_eval (functional index))

/-- A supplied finite nonnegative partition of unity transports strict
coefficient positivity to strict pointwise positivity. -/
theorem positive_of_finite_nonnegative_partitionOfUnity
    [Fintype Term]
    (weight : Parameter → Term → ℝ)
    (coefficient : Term → ℝ)
    (value : Parameter → ℝ)
    (hweight : ∀ point term, 0 ≤ weight point term)
    (hsum : ∀ point, ∑ term, weight point term = 1)
    (hreconstruct : ∀ point,
      value point = ∑ term, weight point term * coefficient term)
    (hcoefficient : ∀ term, 0 < coefficient term) :
    ∀ point, 0 < value point := by
  intro point
  rw [hreconstruct]
  apply Finset.sum_pos'
  · intro term _
    exact mul_nonneg (hweight point term) (hcoefficient term).le
  · have hpositiveWeight : ∃ term, 0 < weight point term := by
      by_contra hnot
      push Not at hnot
      have hzero : ∀ term, weight point term = 0 := fun term =>
        le_antisymm (hnot term) (hweight point term)
      have hone := hsum point
      simp [hzero] at hone
    obtain ⟨term, hterm⟩ := hpositiveWeight
    exact ⟨term, Finset.mem_univ term,
      mul_pos hterm (hcoefficient term)⟩

/-- Strictly negative supplied coefficients give a strictly negative
reconstructed function. -/
theorem negative_of_finite_nonnegative_partitionOfUnity
    [Fintype Term]
    (weight : Parameter → Term → ℝ)
    (coefficient : Term → ℝ)
    (value : Parameter → ℝ)
    (hweight : ∀ point term, 0 ≤ weight point term)
    (hsum : ∀ point, ∑ term, weight point term = 1)
    (hreconstruct : ∀ point,
      value point = ∑ term, weight point term * coefficient term)
    (hcoefficient : ∀ term, coefficient term < 0) :
    ∀ point, value point < 0 := by
  intro point
  have hpositive := positive_of_finite_nonnegative_partitionOfUnity
    weight (fun term => -coefficient term) (fun point => -value point)
    hweight hsum
    (fun point => by
      rw [hreconstruct]
      simp_rw [mul_neg]
      rw [← Finset.sum_neg_distrib])
    (fun term => neg_pos.mpr (hcoefficient term)) point
  linarith

/-- Strict positivity of every supplied rational-affine coefficient implies
strict pointwise positivity of every represented field coordinate. -/
theorem positive_of_rationalAffine_partition_coefficients
    [Fintype Coordinate] [Fintype Index] [Fintype Term]
    (functional : Index → Term → RationalAffineFunctional Coordinate)
    (weight : Parameter → Term → ℝ)
    (field : (Coordinate → ℝ) → Index → Parameter → ℝ)
    (hweight : ∀ point term, 0 ≤ weight point term)
    (hsum : ∀ point, ∑ term, weight point term = 1)
    (hreconstruct : ∀ reward index point,
      field reward index point =
        ∑ term, weight point term * (functional index term).eval reward)
    (reward : Coordinate → ℝ)
    (hreward : ∀ index term, 0 < (functional index term).eval reward) :
    ∀ index point, 0 < field reward index point := by
  intro index
  exact positive_of_finite_nonnegative_partitionOfUnity
    weight (fun term => (functional index term).eval reward)
      (field reward index) hweight hsum
      (hreconstruct reward index) (hreward index)

/-- Strict negativity of every supplied rational-affine coefficient implies
strict pointwise negativity of every represented field coordinate. -/
theorem negative_of_rationalAffine_partition_coefficients
    [Fintype Coordinate] [Fintype Index] [Fintype Term]
    (functional : Index → Term → RationalAffineFunctional Coordinate)
    (weight : Parameter → Term → ℝ)
    (field : (Coordinate → ℝ) → Index → Parameter → ℝ)
    (hweight : ∀ point term, 0 ≤ weight point term)
    (hsum : ∀ point, ∑ term, weight point term = 1)
    (hreconstruct : ∀ reward index point,
      field reward index point =
        ∑ term, weight point term * (functional index term).eval reward)
    (reward : Coordinate → ℝ)
    (hreward : ∀ index term, (functional index term).eval reward < 0) :
    ∀ index point, field reward index point < 0 := by
  intro index
  exact negative_of_finite_nonnegative_partitionOfUnity
    weight (fun term => (functional index term).eval reward)
      (field reward index) hweight hsum
      (hreconstruct reward index) (hreward index)

/-- The simultaneous supplied coefficient-sign conditions form a finite
open rational-affine chamber. -/
theorem positive_rationalAffine_partition_chamber_isOpen
    [Fintype Coordinate] [Fintype Index] [Fintype Term]
    (functional : Index → Term → RationalAffineFunctional Coordinate) :
    IsOpen {reward : Coordinate → ℝ |
      ∀ index term, 0 < (functional index term).eval reward} := by
  let flatten : Index × Term → RationalAffineFunctional Coordinate :=
    fun pair => functional pair.1 pair.2
  simpa only [StrictPositiveRationalAffineChamber, flatten,
    Prod.forall] using isOpen_strictPositiveRationalAffineChamber flatten

/-- Simultaneous positive and negative coefficient requirements for supplied
finite affine partitions form an open finite-halfspace chamber. -/
theorem rationalAffine_partition_sign_chamber_isOpen
    [Fintype Coordinate] [Fintype Term]
    [Fintype PositiveIndex] [Fintype NegativeIndex]
    (positiveFunctional :
      PositiveIndex → Term → RationalAffineFunctional Coordinate)
    (negativeFunctional :
      NegativeIndex → Term → RationalAffineFunctional Coordinate) :
    IsOpen {reward : Coordinate → ℝ |
      (∀ index term, 0 < (positiveFunctional index term).eval reward) ∧
        ∀ index term, (negativeFunctional index term).eval reward < 0} := by
  rw [show {reward : Coordinate → ℝ |
        (∀ index term, 0 < (positiveFunctional index term).eval reward) ∧
          ∀ index term, (negativeFunctional index term).eval reward < 0} =
      {reward | ∀ index term,
        0 < (positiveFunctional index term).eval reward} ∩
      {reward | ∀ index term,
        (negativeFunctional index term).eval reward < 0} by
    ext reward
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]]
  apply IsOpen.inter
  · exact positive_rationalAffine_partition_chamber_isOpen
      positiveFunctional
  · rw [show {reward : Coordinate → ℝ | ∀ index term,
          (negativeFunctional index term).eval reward < 0} =
        ⋂ pair : NegativeIndex × Term,
          {reward | (negativeFunctional pair.1 pair.2).eval reward < 0} by
      ext reward
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Prod.forall]]
    apply isOpen_iInter_of_finite
    intro pair
    exact isOpen_lt
      (RationalAffineFunctional.continuous_eval
        (negativeFunctional pair.1 pair.2)) continuous_const

end Math

end
