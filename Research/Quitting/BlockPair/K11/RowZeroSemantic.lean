import UniformEquilibrium.Quitting.Examples.BlockPair.K11ActiveEquationInterval

namespace GameTheory.BlockPairK11.DyadicCertificate

open Math.Interval
open GameTheory.BlockPairK11
open GameTheory.BlockPairK11.LocalInterval

def rowZeroExpression : Expression := BlockPairK11.activeEquation 0

theorem row_zero_active_equation_semantic {precision : ℕ}
    (box : HazardIndex → DyadicInterval precision) :
    LocalInterval.activeEquationAt (buildCycleData box)
        (activeSlot 0).1 (activeSlot 0).2 =
      RationalPolynomial.evalCachedDyadic box rowZeroExpression := by
  exact LocalInterval.activeEquation_buildCycleData_eq_evalCachedDyadic box 0

theorem row_zero_derivative_semantic {precision : ℕ}
    (box : HazardIndex → DyadicInterval precision)
    (coordinate : Fin 31) :
    (LocalInterval.activeEquationAt (buildCycleData box)
        (activeSlot 0).1 (activeSlot 0).2).derivative.get coordinate =
      (RationalPolynomial.evalCachedDyadic box
        rowZeroExpression).derivative.get coordinate := by
  exact congrArg
    (fun dual : GlobalDual precision ↦ dual.derivative.get coordinate)
    (row_zero_active_equation_semantic box)

theorem row_zero_formal_partial_sound {precision : ℕ}
    (box : HazardIndex → DyadicInterval precision)
    (point : HazardIndex → ℝ)
    (hpoint : ∀ index, (box index).Contains (point index))
    (coordinate : Fin 31) :
    ((RationalPolynomial.evalDualDyadic box rowZeroExpression).derivative
        coordinate).Contains
      (RationalPolynomial.evalReal point
        (RationalPolynomial.formalPartial coordinate rowZeroExpression)) := by
  exact (RationalPolynomial.evalDualDyadic_sound
    rowZeroExpression box point hpoint).2 coordinate

end GameTheory.BlockPairK11.DyadicCertificate
