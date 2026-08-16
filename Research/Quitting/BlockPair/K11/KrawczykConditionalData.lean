import MathUE.Interval.PolynomialKrawczyk
import UniformEquilibrium.Quitting.Examples.BlockPair.K11System

namespace GameTheory.BlockPairK11.DyadicCertificate

open Math.Interval

/-- Exact inputs for a K11 Krawczyk check.  Concrete numeric payloads provide
this interface outside the reusable Research dependency boundary. -/
structure K11KrawczykData where
  precision : ℕ
  center : HazardIndex → ℚ
  radius : ℚ
  radius_nonneg : 0 ≤ radius
  box : HazardIndex → DyadicInterval precision
  preconditioner : HazardIndex → HazardIndex → ℚ
  jacobianBoxCache :
    HazardIndex → HazardIndex → DyadicInterval precision
  residualAtCenterCache : HazardIndex → DyadicInterval precision

/-- Ordered interval sum, matching `K11System.expressionSum`. -/
def intervalSum {precision : ℕ} : {count : ℕ} →
    (Fin count → DyadicInterval precision) → DyadicInterval precision
  | 0, _ => DyadicInterval.ofInt 0
  | count + 1, term =>
      (intervalSum (fun index ↦ term index.castSucc)).add
        (term (Fin.last count))

/-- The checked interval product `A * J_H(box)`. -/
def conditionalAJCache (data : K11KrawczykData)
    (row column : HazardIndex) : DyadicInterval data.precision :=
  intervalSum fun equation =>
    (DyadicInterval.ofRat (data.preconditioner row equation)).mul
      (data.jacobianBoxCache equation column)

/-- The checked interval matrix `B = I - A * J_H(box)`. -/
def conditionalBCache (data : K11KrawczykData)
    (row column : HazardIndex) : DyadicInterval data.precision :=
  (DyadicInterval.ofInt (if row = column then 1 else 0)).add
    (conditionalAJCache data row column).neg

/-- The checked interval product `A * H(center)`. -/
def conditionalAH0Cache (data : K11KrawczykData)
    (row : HazardIndex) : DyadicInterval data.precision :=
  intervalSum fun equation =>
    (DyadicInterval.ofRat (data.preconditioner row equation)).mul
      (data.residualAtCenterCache equation)

/-- The centered radius interval used in the Krawczyk remainder. -/
def centeredRadiusInterval
    (data : K11KrawczykData) : DyadicInterval data.precision :=
  ⟨Rat.floor ((-data.radius) * DyadicInterval.scale data.precision),
    Rat.ceil (data.radius * DyadicInterval.scale data.precision)⟩

/-- Degenerate dyadic boxes used to evaluate the residual at its center. -/
def centerEvaluationBox (data : K11KrawczykData)
    (index : HazardIndex) : DyadicInterval data.precision :=
  DyadicInterval.ofRat (data.center index)

/-- The checked interval product `B * [-radius,radius]^31`. -/
def conditionalRemainderCache (data : K11KrawczykData)
    (row : HazardIndex) : DyadicInterval data.precision :=
  intervalSum fun column =>
    (conditionalBCache data row column).mul
      (centeredRadiusInterval data)

/-- The checked Krawczyk image coordinate
`center - A*H(center) + B*[-radius,radius]^31`. -/
def conditionalAssembledKrawczykCache (data : K11KrawczykData)
    (row : HazardIndex) : DyadicInterval data.precision :=
  ((DyadicInterval.ofRat (data.center row)).add
    (conditionalAH0Cache data row).neg).add
      (conditionalRemainderCache data row)

/-- Polynomial syntax for one row of `A * H`. -/
def preconditionedResidualExpression (data : K11KrawczykData)
    (row : HazardIndex) : Expression :=
  expressionSum fun equation =>
    (.constant (data.preconditioner row equation)) * activeEquation equation

/-- Polynomial syntax for the Krawczyk fixed-point map `x - A*H(x)`. -/
def preconditionedStepExpression (data : K11KrawczykData)
    (row : HazardIndex) : Expression :=
  .var row - preconditionedResidualExpression data row

end GameTheory.BlockPairK11.DyadicCertificate
