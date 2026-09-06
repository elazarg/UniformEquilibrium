import MathUE.LinearAlgebra.RationalAffineFunctional
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Rational-valued affine functionals on real coordinate spaces -/

noncomputable section

namespace Math

open scoped BigOperators

/-- A real number represented exactly by a rational number. -/
def IsRationalReal (value : ℝ) : Prop := ∃ rational : ℚ, value = rational

/-- An affine real functional whose value is rational whenever all of its
coordinates are rational. -/
def HasRationalAffineCoefficients {Coordinate : Type*}
    (functional : (Coordinate → ℝ) → ℝ) : Prop :=
  (∀ first second scale,
    functional (scale • first + (1 - scale) • second) =
      scale * functional first + (1 - scale) * functional second) ∧
  ∀ point, (∀ coordinate, IsRationalReal (point coordinate)) →
    IsRationalReal (functional point)

namespace IsRationalReal

theorem zero : IsRationalReal 0 := ⟨0, by norm_num⟩

theorem one : IsRationalReal 1 := ⟨1, by norm_num⟩

theorem add {first second : ℝ}
    (hfirst : IsRationalReal first) (hsecond : IsRationalReal second) :
    IsRationalReal (first + second) := by
  rcases hfirst with ⟨first, rfl⟩
  rcases hsecond with ⟨second, rfl⟩
  exact ⟨first + second, (Rat.cast_add first second).symm⟩

theorem sub {first second : ℝ}
    (hfirst : IsRationalReal first) (hsecond : IsRationalReal second) :
    IsRationalReal (first - second) := by
  rcases hfirst with ⟨first, rfl⟩
  rcases hsecond with ⟨second, rfl⟩
  exact ⟨first - second, (Rat.cast_sub first second).symm⟩

theorem mul {first second : ℝ}
    (hfirst : IsRationalReal first) (hsecond : IsRationalReal second) :
    IsRationalReal (first * second) := by
  rcases hfirst with ⟨first, rfl⟩
  rcases hsecond with ⟨second, rfl⟩
  exact ⟨first * second, (Rat.cast_mul first second).symm⟩

theorem sum {Index : Type*} (set : Finset Index) (value : Index → ℝ)
    (hvalue : ∀ index ∈ set, IsRationalReal (value index)) :
    IsRationalReal (∑ index ∈ set, value index) := by
  classical
  induction set using Finset.induction_on with
  | empty => simpa using zero
  | @insert index set hindex induction =>
      rw [Finset.sum_insert hindex]
      exact (hvalue index (by simp)).add
        (induction fun other hother ↦ hvalue other (by simp [hother]))

theorem prod {Index : Type*} (set : Finset Index) (value : Index → ℝ)
    (hvalue : ∀ index ∈ set, IsRationalReal (value index)) :
    IsRationalReal (∏ index ∈ set, value index) := by
  classical
  induction set using Finset.induction_on with
  | empty => simpa using one
  | @insert index set hindex induction =>
      rw [Finset.prod_insert hindex]
      exact (hvalue index (by simp)).mul
        (induction fun other hother ↦ hvalue other (by simp [hother]))

end IsRationalReal

namespace HasRationalAffineCoefficients

theorem offset_rational {Coordinate : Type*}
    {functional : (Coordinate → ℝ) → ℝ}
    (hfunctional : HasRationalAffineCoefficients functional) :
    IsRationalReal (functional 0) :=
  hfunctional.2 0 fun _ ↦ IsRationalReal.zero

theorem basisCoefficient_rational {Coordinate : Type*} [DecidableEq Coordinate]
    {functional : (Coordinate → ℝ) → ℝ}
    (hfunctional : HasRationalAffineCoefficients functional) (coordinate : Coordinate) :
    IsRationalReal (functional (Pi.single coordinate 1) - functional 0) := by
  apply IsRationalReal.sub
  · apply hfunctional.2
    intro other
    by_cases hother : other = coordinate
    · subst other
      simpa using IsRationalReal.one
    · simpa [Pi.single_apply, hother] using IsRationalReal.zero
  · exact hfunctional.offset_rational

/-- A real affine functional is reconstructed from its offset and coordinate
basis differences. -/
theorem eq_offset_add_sum_basisCoefficient
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {functional : (Coordinate → ℝ) → ℝ}
    (hfunctional : HasRationalAffineCoefficients functional)
    (point : Coordinate → ℝ) :
    functional point = functional 0 +
      ∑ coordinate,
        (functional (Pi.single coordinate 1) - functional 0) * point coordinate := by
  have hhomogeneous (vector : Coordinate → ℝ) (scale : ℝ) :
      functional (scale • vector) - functional 0 =
        scale * (functional vector - functional 0) := by
    have haffine := hfunctional.1 vector 0 scale
    have hargument : scale • vector + (1 - scale) • (0 : Coordinate → ℝ) =
        scale • vector := by
      ext coordinate
      simp
    rw [hargument] at haffine
    rw [haffine]
    ring
  have hadditive (first second : Coordinate → ℝ) :
      functional (first + second) - functional 0 =
        (functional first - functional 0) +
          (functional second - functional 0) := by
    have hfirst := hfunctional.1 first second (1 / 2 : ℝ)
    have hsecond := hfunctional.1 (first + second) 0 (1 / 2 : ℝ)
    have harguments :
        (1 / 2 : ℝ) • first + (1 - 1 / 2 : ℝ) • second =
          (1 / 2 : ℝ) • (first + second) + (1 - 1 / 2 : ℝ) • 0 := by
      ext coordinate
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply]
      ring
    rw [harguments, hsecond] at hfirst
    linarith
  have hsum (set : Finset Coordinate) (term : Coordinate → Coordinate → ℝ) :
      functional (∑ coordinate ∈ set, term coordinate) - functional 0 =
        ∑ coordinate ∈ set, (functional (term coordinate) - functional 0) := by
    induction set using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, sub_self]
    | @insert coordinate set hcoordinate induction =>
        rw [Finset.sum_insert hcoordinate, hadditive, Finset.sum_insert hcoordinate,
          induction]
  have hdecompose :
      (∑ coordinate, point coordinate • Pi.single coordinate (1 : ℝ)) = point := by
    exact (pi_eq_sum_univ' point).symm
  have hreconstruct := hsum Finset.univ
    (fun coordinate ↦ point coordinate • Pi.single coordinate (1 : ℝ))
  rw [hdecompose] at hreconstruct
  calc
    functional point = functional 0 + (functional point - functional 0) := by ring
    _ = functional 0 + ∑ coordinate,
        (functional (point coordinate • Pi.single coordinate (1 : ℝ)) -
          functional 0) := by rw [hreconstruct]
    _ = functional 0 + ∑ coordinate,
        (functional (Pi.single coordinate 1) - functional 0) * point coordinate := by
      apply congrArg (functional 0 + ·)
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [hhomogeneous]
      ring

/-- In finite dimension, the preservation characterization produces literal
exact rational-affine coefficient data. -/
theorem exists_rationalAffineFunctional
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {functional : (Coordinate → ℝ) → ℝ}
    (hfunctional : HasRationalAffineCoefficients functional) :
    ∃ coded : RationalAffineFunctional Coordinate, coded.eval = functional := by
  choose offset hoffset using hfunctional.offset_rational
  choose coefficient hcoefficient using fun coordinate ↦
    hfunctional.basisCoefficient_rational coordinate
  let coded : RationalAffineFunctional Coordinate := ⟨offset, coefficient⟩
  refine ⟨coded, funext fun point ↦ ?_⟩
  rw [hfunctional.eq_offset_add_sum_basisCoefficient point]
  unfold RationalAffineFunctional.eval
  dsimp only [coded]
  rw [hoffset]
  apply congrArg ((offset : ℝ) + ·)
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [← hoffset, hcoefficient coordinate]

end HasRationalAffineCoefficients

namespace RationalAffineFunctional

/-- Evaluation of exact rational-affine data is rational at rational points. -/
theorem eval_rational {Coordinate : Type*} [Fintype Coordinate]
    (functional : RationalAffineFunctional Coordinate) (point : Coordinate → ℝ)
    (hpoint : ∀ coordinate, IsRationalReal (point coordinate)) :
    IsRationalReal (functional.eval point) := by
  unfold eval
  apply IsRationalReal.add
  · exact ⟨functional.offset, rfl⟩
  · apply IsRationalReal.sum
    intro coordinate _
    apply IsRationalReal.mul
    · exact ⟨functional.coefficient coordinate, rfl⟩
    · exact hpoint coordinate

/-- Exact rational-affine data supplies a rational-coefficient affine
functional in real coordinate space. -/
theorem hasRationalAffineCoefficients {Coordinate : Type*} [Fintype Coordinate]
    (functional : RationalAffineFunctional Coordinate) :
    HasRationalAffineCoefficients functional.eval := by
  constructor
  · intro first second scale
    unfold eval
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun coordinate _ ↦ by
      show (functional.coefficient coordinate : ℝ) *
          (scale * first coordinate + (1 - scale) * second coordinate) =
        scale * ((functional.coefficient coordinate : ℝ) * first coordinate) +
          (1 - scale) *
            ((functional.coefficient coordinate : ℝ) * second coordinate)
      ring]
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  · intro point hpoint
    exact functional.eval_rational point hpoint

end RationalAffineFunctional

end Math

end
