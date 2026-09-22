import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawProducer

/-! # Exact quadratic Bernstein interpolation for the four-player half ceiling -/

noncomputable section

namespace GameTheory

/-- The packet's degree-two Bernstein basis, indexed by `0,1,2`. -/
def quittingHalfBernsteinBasis (index : Fin 3) (rate : ℝ) : ℝ :=
  if index = 0 then (1 - rate) ^ 2
  else if index = 1 then 2 * rate * (1 - rate)
  else rate ^ 2

/-- The exact interpolation transform at `0, 1/2, 1` from equation (3.3). -/
def quittingHalfBernsteinCoefficient (function : ℝ → ℝ) (index : Fin 3) : ℝ :=
  if index = 0 then function 0
  else if index = 1 then
    2 * function (1 / 2) - (function 0 + function 1) / 2
  else function 1

/-- Apply the one-dimensional interpolation rule independently in both variables. -/
def quittingHalfTensorCoefficient (function : ℝ → ℝ → ℝ)
    (first second : Fin 3) : ℝ :=
  quittingHalfBernsteinCoefficient
    (fun x => quittingHalfBernsteinCoefficient (fun y => function x y) second) first

/-- The half-face algebraic shape: a bilinear Quit sum times the survival
factor, minus a bilinear Continue sum. -/
def quittingHalfCanonicalResidual (quit cont : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (1 - (1 / 2) * (1 - x) * (1 - y)) *
    ((1 - x) * (1 - y) * quit 0 0 + x * (1 - y) * quit 1 0 +
      (1 - x) * y * quit 0 1 + x * y * quit 1 1) -
    ((1 - x) * (1 - y) * cont 0 0 + x * (1 - y) * cont 1 0 +
      (1 - x) * y * cont 0 1 + x * y * cont 1 1)

/-- A biquadratic polynomial reconstructs exactly from its nine samples. -/
theorem quittingHalfTensorInterpolation_biquadratic
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 x y : ℝ) :
    let function : ℝ → ℝ → ℝ := fun x y =>
      a00 + a01 * y + a02 * y ^ 2 +
        a10 * x + a11 * x * y + a12 * x * y ^ 2 +
          a20 * x ^ 2 + a21 * x ^ 2 * y + a22 * x ^ 2 * y ^ 2
    function x y =
      ∑ first : Fin 3, ∑ second : Fin 3,
        quittingHalfTensorCoefficient function first second *
          quittingHalfBernsteinBasis first x * quittingHalfBernsteinBasis second y := by
  simp [quittingHalfTensorCoefficient, quittingHalfBernsteinCoefficient,
    quittingHalfBernsteinBasis, Fin.sum_univ_succ]
  ring

/-- The particular stationary half-face shape reconstructs from the packet's
nine coefficient tests, without assuming any polynomial equality. -/
theorem quittingHalfCanonicalResidual_eq_tensorBernstein
    (quit cont : ℝ → ℝ → ℝ) (x y : ℝ) :
    quittingHalfCanonicalResidual quit cont x y =
      ∑ first : Fin 3, ∑ second : Fin 3,
        quittingHalfTensorCoefficient (quittingHalfCanonicalResidual quit cont)
          first second *
          quittingHalfBernsteinBasis first x * quittingHalfBernsteinBasis second y := by
  simp [quittingHalfCanonicalResidual, quittingHalfTensorCoefficient,
    quittingHalfBernsteinCoefficient, quittingHalfBernsteinBasis, Fin.sum_univ_succ]
  ring

end GameTheory
