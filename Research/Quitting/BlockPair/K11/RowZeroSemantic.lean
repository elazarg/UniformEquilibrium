import Research.Quitting.BlockPair.K11.ActiveEquationSemanticAdapter
import Research.Quitting.BlockPair.K11.JacobianCache
import Research.Quitting.BlockPair.K11.RowZeroCacheData
import UniformEquilibrium.Quitting.Examples.BlockPair.K11DyadicData

namespace GameTheory.BlockPairK11.DyadicCertificate

open Math.Interval
open GameTheory.BlockPairK11
open GameTheory.BlockPairK11.LocalInterval

abbrev RowPrecision : ℕ := 80

def rowZeroExpression : Expression := BlockPairK11.activeEquation 0

theorem row_zero_active_equation_semantic :
    LocalInterval.activeEquationAt
        (buildCycleData (box : HazardIndex → DyadicInterval Precision))
        (activeSlot 0).1 (activeSlot 0).2 =
      RationalPolynomial.evalCachedDyadic box rowZeroExpression := by
  exact LocalInterval.activeEquation_buildCycleData_eq_evalCachedDyadic box 0

theorem row_zero_derivative_semantic (coordinate : Fin 31) :
    (LocalInterval.activeEquationAt
        (buildCycleData (box : HazardIndex → DyadicInterval Precision))
        (activeSlot 0).1 (activeSlot 0).2).derivative.get coordinate =
      (RationalPolynomial.evalCachedDyadic box rowZeroExpression).derivative.get coordinate := by
  exact congrArg (fun dual : GlobalDual Precision => dual.derivative.get coordinate)
      (row_zero_active_equation_semantic)

theorem row_zero_formal_partial_sound
    (box : HazardIndex → DyadicInterval Precision)
    (point : HazardIndex → ℝ)
    (hpoint : ∀ index, (box index).Contains (point index))
    (coordinate : Fin 31) :
    ((RationalPolynomial.evalDualDyadic box rowZeroExpression).derivative coordinate).Contains
      (RationalPolynomial.evalReal point
        (RationalPolynomial.formalPartial coordinate rowZeroExpression)) := by
  exact (RationalPolynomial.evalDualDyadic_sound rowZeroExpression box point hpoint).2 coordinate

end GameTheory.BlockPairK11.DyadicCertificate
