import Research.Quitting.BlockPair.K11.Preconditioner
import Research.Quitting.BlockPair.K11.JacobianCache
import Research.Quitting.BlockPair.K11.RowZeroCacheData
import MathUE.Interval.PolynomialKrawczyk

namespace GameTheory.BlockPairK11.DyadicCertificate

open Math.Interval

/-- Ordered interval sum, matching `K11System.expressionSum`. -/
def intervalSum {precision : ℕ} : {count : ℕ} →
    (Fin count → DyadicInterval precision) → DyadicInterval precision
  | 0, _ => DyadicInterval.ofInt 0
  | count + 1, term =>
      (intervalSum (fun index ↦ term index.castSucc)).add
        (term (Fin.last count))

/-- The checked interval product `A * J_H(box)`. -/
def conditionalAJCache
    (row column : HazardIndex) : DyadicInterval Precision :=
  intervalSum fun equation =>
    (DyadicInterval.ofRat (preconditioner row equation)).mul
      ((jacobianBoxCache.get equation).get column)

/-- The checked interval matrix `B = I - A * J_H(box)`. -/
def conditionalBCache
    (row column : HazardIndex) : DyadicInterval Precision :=
  (DyadicInterval.ofInt (if row = column then 1 else 0)).add
    (conditionalAJCache row column).neg

/-- The checked interval product `A * H(center)`. -/
def conditionalAH0Cache
    (row : HazardIndex) : DyadicInterval Precision :=
  intervalSum fun equation =>
    (DyadicInterval.ofRat (preconditioner row equation)).mul
      (residualAtCenterCache.get equation)

/-- The centered radius interval used in the Krawczyk remainder. -/
def centeredRadiusInterval : DyadicInterval Precision :=
  ⟨Rat.floor ((-radius) * DyadicInterval.scale Precision),
    Rat.ceil (radius * DyadicInterval.scale Precision)⟩

/-- Degenerate dyadic boxes used to evaluate the residual at its center. -/
def centerEvaluationBox (index : HazardIndex) : DyadicInterval Precision :=
  DyadicInterval.ofRat (center index)

/-- The checked interval product `B * [-radius,radius]^31`. -/
def conditionalRemainderCache
    (row : HazardIndex) : DyadicInterval Precision :=
  intervalSum fun column =>
    (conditionalBCache row column).mul centeredRadiusInterval

/-- The checked Krawczyk image coordinate
`center - A*H(center) + B*[-radius,radius]^31`. -/
def conditionalAssembledKrawczykCache
    (row : HazardIndex) : DyadicInterval Precision :=
  ((DyadicInterval.ofRat (center row)).add
    (conditionalAH0Cache row).neg).add
      (conditionalRemainderCache row)

/-- Polynomial syntax for one row of `A * H`. -/
def preconditionedResidualExpression (row : HazardIndex) : Expression :=
  expressionSum fun equation =>
    (.constant (preconditioner row equation)) * activeEquation equation

/-- Polynomial syntax for the Krawczyk fixed-point map `x - A*H(x)`. -/
def preconditionedStepExpression (row : HazardIndex) : Expression :=
  .var row - preconditionedResidualExpression row

end GameTheory.BlockPairK11.DyadicCertificate
