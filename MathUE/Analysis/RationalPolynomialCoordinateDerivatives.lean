import MathUE.Analysis.CoordinateResetFTC
import MathUE.Interval.PolynomialLipschitz

/-! # Actual coordinate partials of the canonical rational polynomial evaluation -/

noncomputable section

namespace Math.Interval.RationalPolynomial

open scoped BigOperators

variable {dimension : ℕ}

theorem coordinatePartial_evalReal_eq
    (expression : RationalPolynomial dimension) (point : Fin dimension → ℝ)
    (coordinate : Fin dimension) :
    Math.coordinatePartial (fun input => evalReal input expression) point coordinate =
      evalReal point (formalPartial coordinate expression) := by
  rw [Math.coordinatePartial, (hasFDerivAt_evalReal expression point).fderiv]
  have hbasis : Math.piBasisVector coordinate = Pi.single coordinate (1 : ℝ) := by
    ext index
    simp [Math.piBasisVector, Pi.single_apply, eq_comm]
  simpa only [hbasis] using differential_piBasisVector point expression coordinate

theorem coordinateMixedPartial_evalReal_eq
    (expression : RationalPolynomial dimension) (point : Fin dimension → ℝ)
    (owner receiver : Fin dimension) :
    Math.coordinateMixedPartial (fun input => evalReal input expression) point owner receiver =
      evalReal point (formalPartial owner (formalPartial receiver expression)) := by
  have hfirst : (fun input =>
      Math.coordinatePartial (fun value => evalReal value expression) input receiver) =
      (fun input => evalReal input (formalPartial receiver expression)) :=
    funext fun input => coordinatePartial_evalReal_eq expression input receiver
  rw [Math.coordinateMixedPartial, hfirst]
  exact coordinatePartial_evalReal_eq (formalPartial receiver expression) point owner

end Math.Interval.RationalPolynomial
