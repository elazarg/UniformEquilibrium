import MathUE.Polynomial.TensorBernsteinQuadratic

/-! # The half-ceiling residual shape in the generic tensor Bernstein interface -/

noncomputable section

namespace GameTheory

/-- The game-specific half-survival specialization of the generic bilinear algebra. -/
def quittingHalfCanonicalResidual (quit cont : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  Math.bilinearSurvivalDifference (1 / 2) quit cont x y

/-- The half-survival specialization has its exact quadratic tensor expansion. -/
theorem quittingHalfCanonicalResidual_eq_tensorBernstein
    (quit cont : ℝ → ℝ → ℝ) (x y : ℝ) :
    quittingHalfCanonicalResidual quit cont x y =
      ∑ first : Fin 3, ∑ second : Fin 3,
        Math.quadraticTensorBernsteinCoefficient (quittingHalfCanonicalResidual quit cont)
          first second *
          Math.quadraticBernsteinBasis first x * Math.quadraticBernsteinBasis second y :=
  Math.bilinearSurvivalDifference_eq_quadraticTensorBernstein (1 / 2) quit cont x y

end GameTheory
