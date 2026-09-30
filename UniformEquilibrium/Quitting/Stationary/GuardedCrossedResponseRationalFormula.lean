import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumFormula
import UniformEquilibrium.Quitting.Root.RationalReward
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseFaces

/-! # Rational sign formulas for the bounded crossed fixed-point locus

The formula includes both boundary faces. It encodes the actual auxiliary crossed
map, not an original-game Nash condition. No regularity or isolated-root condition
is imposed. The finite expression encoding does not assert an executable search.
-/

noncomputable section

namespace GameTheory

open Math.PolynomialSignCell.SignFormula
open MathUE.RealQuantifierElimination
open scoped BigOperators

variable {n : ℕ}

private def rationalCoalitionWeight (reward : RationalQuittingReward n)
    (coalition : Finset (Fin n)) (who : Fin n) : ℚ :=
  if h : coalition.Nonempty then reward ⟨coalition, h⟩ who else 0

private theorem rationalCoalitionWeight_cast (reward : RationalQuittingReward n)
    (coalition : Finset (Fin n)) (who : Fin n) :
    (rationalCoalitionWeight reward coalition who : ℝ) =
      weightOfReward (rationalQuittingRewardToReal reward) coalition who := by
  unfold rationalCoalitionWeight weightOfReward rationalQuittingRewardToReal
  split_ifs <;> simp

private def rationalCoalitionMassExpression (who : Fin n)
    (coalition : Finset (Fin n)) : RingExpression n :=
  hazardProductExpressionWithTerms RingExpression.var coalition *
    continueProductExpressionWithTerms RingExpression.var (Finset.univ.erase who \ coalition)

/-- The pure-Quit coalition sum as a rational expression in the actual hazards. -/
def rationalQuittingSigmaExpression (reward : RationalQuittingReward n)
    (who : Fin n) : RingExpression n :=
  RingExpression.sum ((Finset.univ.erase who).powerset.toList.map fun coalition =>
    rationalCoalitionMassExpression who coalition *
      .const (rationalCoalitionWeight reward (insert who coalition) who))

/-- The absorbing Continue coalition sum, excluding the empty coalition. -/
def rationalQuittingExcludedExpression (reward : RationalQuittingReward n)
    (who : Fin n) : RingExpression n :=
  RingExpression.sum (((Finset.univ.erase who).powerset.erase ∅).toList.map fun coalition =>
    rationalCoalitionMassExpression who coalition *
      .const (rationalCoalitionWeight reward coalition who))

@[simp]
theorem evalReal_rationalQuittingSigmaExpression (reward : RationalQuittingReward n)
    (who : Fin n) (hazard : Fin n → ℝ) :
    (rationalQuittingSigmaExpression reward who).evalReal hazard =
      sigmaValue (weightOfReward (rationalQuittingRewardToReal reward)) hazard who := by
  rw [rationalQuittingSigmaExpression, RingExpression.evalReal_sum,
    List.map_map, Finset.sum_map_toList]
  unfold sigmaValue
  apply Finset.sum_congr rfl
  intro coalition _
  simp [Function.comp_apply, rationalCoalitionMassExpression, rationalCoalitionWeight_cast]

@[simp]
theorem evalReal_rationalQuittingExcludedExpression (reward : RationalQuittingReward n)
    (who : Fin n) (hazard : Fin n → ℝ) :
    (rationalQuittingExcludedExpression reward who).evalReal hazard =
      excludedValue (weightOfReward (rationalQuittingRewardToReal reward)) hazard who := by
  rw [rationalQuittingExcludedExpression, RingExpression.evalReal_sum,
    List.map_map, Finset.sum_map_toList]
  unfold excludedValue
  apply Finset.sum_congr rfl
  intro coalition _
  simp [Function.comp_apply, rationalCoalitionMassExpression, rationalCoalitionWeight_cast]

/-- The actual zero-discount displacement polynomial with rational coefficients. -/
def rationalQuittingDisplacementExpression (reward : RationalQuittingReward n)
    (who : Fin n) : RingExpression n :=
  (1 + -continueProductExpressionWithTerms RingExpression.var (Finset.univ.erase who)) *
    rationalQuittingSigmaExpression reward who + -rationalQuittingExcludedExpression reward who

@[simp]
theorem evalReal_rationalQuittingDisplacementExpression (reward : RationalQuittingReward n)
    (who : Fin n) (hazard : Fin n → ℝ) :
    (rationalQuittingDisplacementExpression reward who).evalReal hazard =
      quittingDiscountedDisplacement (rationalQuittingRewardToReal reward) 0 hazard who := by
  simp [rationalQuittingDisplacementExpression, quittingDiscountedDisplacement,
    continueMassExcl, sub_eq_add_neg]

/-- Exchange payoff-recipient rows only, exactly as in the crossed response map. -/
def rationalQuittingCrossedResponseExpression (reward : RationalQuittingReward n)
    (first second coordinate : Fin n) : RingExpression n :=
  rationalQuittingDisplacementExpression reward ((Equiv.swap first second) coordinate)

@[simp]
theorem evalReal_rationalQuittingCrossedResponseExpression (reward : RationalQuittingReward n)
    (first second coordinate : Fin n) (hazard : Fin n → ℝ) :
    (rationalQuittingCrossedResponseExpression reward first second coordinate).evalReal hazard =
      quittingCrossedResponse
        (rationalQuittingRewardToReal reward) first second hazard coordinate :=
  evalReal_rationalQuittingDisplacementExpression reward _ hazard

private def expressionZeroFormula (expression : RingExpression n) : QuantifierFreeFormula n :=
  .atom expression 0

private def implicationFormula (left right : QuantifierFreeFormula n) :
    QuantifierFreeFormula n := .or (.not left) right

private theorem holdsAt_and (left right : QuantifierFreeFormula n) (hazard : Fin n → ℝ) :
    QuantifierFreeFormula.HoldsAt (.and left right : QuantifierFreeFormula n) hazard ↔
      left.HoldsAt hazard ∧ right.HoldsAt hazard := Iff.rfl

private theorem holdsAt_expressionZeroFormula (expression : RingExpression n)
    (hazard : Fin n → ℝ) :
    (expressionZeroFormula expression).HoldsAt hazard ↔ expression.evalReal hazard = 0 := by
  simp [expressionZeroFormula, QuantifierFreeFormula.HoldsAt, realSignAssignment,
    Math.PolynomialSignCell.SignFormula.Holds, sign_eq_zero_iff]

private theorem holdsAt_implicationFormula (left right : QuantifierFreeFormula n)
    (hazard : Fin n → ℝ) :
    (implicationFormula left right).HoldsAt hazard ↔
      (left.HoldsAt hazard → right.HoldsAt hazard) := by
  change (¬left.HoldsAt hazard ∨ right.HoldsAt hazard) ↔ _
  tauto

private def crossedCoordinateFormula (q ceiling response : RingExpression n) :
    QuantifierFreeFormula n :=
  .and (QuantifierFreeFormula.nonnegative q)
    (.and (QuantifierFreeFormula.nonpositive (q + -ceiling))
      (.and (implicationFormula (expressionZeroFormula q)
        (QuantifierFreeFormula.nonpositive response))
        (.and (implicationFormula (.and (QuantifierFreeFormula.positive q)
          (QuantifierFreeFormula.positive (ceiling + -q))) (expressionZeroFormula response))
          (implicationFormula (expressionZeroFormula (q + -ceiling))
            (QuantifierFreeFormula.nonnegative response)))))

private theorem holdsAt_crossedCoordinateFormula (q ceiling response : RingExpression n)
    (hazard : Fin n → ℝ) :
    (crossedCoordinateFormula q ceiling response).HoldsAt hazard ↔
      0 ≤ q.evalReal hazard ∧ q.evalReal hazard ≤ ceiling.evalReal hazard ∧
      (q.evalReal hazard = 0 → response.evalReal hazard ≤ 0) ∧
      (0 < q.evalReal hazard → q.evalReal hazard < ceiling.evalReal hazard →
        response.evalReal hazard = 0) ∧
      (q.evalReal hazard = ceiling.evalReal hazard → 0 ≤ response.evalReal hazard) := by
  simp only [crossedCoordinateFormula, holdsAt_and, holdsAt_implicationFormula,
    holdsAt_expressionZeroFormula, QuantifierFreeFormula.holdsAt_nonnegative_iff,
    QuantifierFreeFormula.holdsAt_nonpositive_iff, QuantifierFreeFormula.holdsAt_positive_iff,
    RingExpression.evalReal_add, RingExpression.evalReal_neg, ← sub_eq_add_neg,
    sub_nonpos, sub_pos, sub_eq_zero, and_imp]

private def rationalCrossedCeiling (first second coordinate : Fin n) (height : ℚ) : ℚ :=
  if coordinate = first ∨ coordinate = second then height else 1

private theorem rationalCrossedCeiling_cast (first second coordinate : Fin n) (height : ℚ) :
    (rationalCrossedCeiling first second coordinate height : ℝ) =
      quittingCrossedCeiling first second (height : ℝ) coordinate := by
  unfold rationalCrossedCeiling quittingCrossedCeiling
  split_ifs <;> simp

/-- Exact rational sign formula for nonzero crossed fixed points in the capped box.
Both zero and upper-bound hazards are retained. -/
def rationalQuittingCrossedFixedPointFormula (reward : RationalQuittingReward n)
    (first second : Fin n) (height : ℚ) : QuantifierFreeFormula n :=
  .and (activeHazardFormulaWithTerms RingExpression.var)
    (conjunction (List.ofFn fun coordinate : Fin n =>
      crossedCoordinateFormula (.var coordinate)
        (.const (rationalCrossedCeiling first second coordinate height))
        (rationalQuittingCrossedResponseExpression reward first second coordinate)))

/-- Membership is equivalent to the actual nonzero fixed-point equation, not to
a supplied sign certificate or an assumed degree comparison. -/
theorem rationalQuittingCrossedFixedPointFormula_holdsAt_iff
    (reward : RationalQuittingReward n) (first second : Fin n) (height : ℚ)
    (hheight : 0 < (height : ℝ)) (hazard : Fin n → ℝ) :
    (rationalQuittingCrossedFixedPointFormula reward first second height).HoldsAt hazard ↔
      hazard ≠ 0 ∧ quittingCrossedClippedMap (rationalQuittingRewardToReal reward)
        first second (height : ℝ) hazard = hazard := by
  have hcoordinates :
      QuantifierFreeFormula.HoldsAt (conjunction (List.ofFn fun coordinate : Fin n =>
        crossedCoordinateFormula (.var coordinate)
          (.const (rationalCrossedCeiling first second coordinate height))
          (rationalQuittingCrossedResponseExpression reward first second coordinate)))
          hazard ↔ ∀ coordinate,
        0 ≤ hazard coordinate ∧
        hazard coordinate ≤ quittingCrossedCeiling first second (height : ℝ) coordinate ∧
        (hazard coordinate = 0 → quittingCrossedResponse
          (rationalQuittingRewardToReal reward) first second hazard coordinate ≤ 0) ∧
        (0 < hazard coordinate →
          hazard coordinate < quittingCrossedCeiling first second (height : ℝ) coordinate →
          quittingCrossedResponse
            (rationalQuittingRewardToReal reward) first second hazard coordinate = 0) ∧
        (hazard coordinate = quittingCrossedCeiling first second (height : ℝ) coordinate →
          0 ≤ quittingCrossedResponse
            (rationalQuittingRewardToReal reward) first second hazard coordinate) := by
    rw [QuantifierFreeFormula.HoldsAt, holds_conjunction_iff]
    constructor
    · intro hall coordinate
      have hholds := hall _ (List.mem_ofFn.mpr ⟨coordinate, rfl⟩)
      have hdecoded := (holdsAt_crossedCoordinateFormula (.var coordinate)
        (.const (rationalCrossedCeiling first second coordinate height))
        (rationalQuittingCrossedResponseExpression reward first second coordinate) hazard).mp
          hholds
      simpa only [RingExpression.evalReal_var, RingExpression.evalReal_const,
        rationalCrossedCeiling_cast, evalReal_rationalQuittingCrossedResponseExpression] using
        hdecoded
    · intro hall formula hmem
      obtain ⟨coordinate, rfl⟩ := List.mem_ofFn.mp hmem
      apply (holdsAt_crossedCoordinateFormula (.var coordinate)
        (.const (rationalCrossedCeiling first second coordinate height))
        (rationalQuittingCrossedResponseExpression reward first second coordinate) hazard).mpr
      simpa only [RingExpression.evalReal_var, RingExpression.evalReal_const,
        rationalCrossedCeiling_cast, evalReal_rationalQuittingCrossedResponseExpression] using
        hall coordinate
  rw [rationalQuittingCrossedFixedPointFormula, holdsAt_and, hcoordinates,
    activeHazardFormulaWithTerms_holdsAt_iff]
  simp only [RingExpression.evalReal_var]
  constructor
  · rintro ⟨⟨coordinate, hpositive⟩, hfaces⟩
    refine ⟨?_, (quittingCrossedClippedMap_eq_self_iff
      (rationalQuittingRewardToReal reward) first second (height : ℝ) hheight hazard
      (fun i => (hfaces i).1) (fun i => (hfaces i).2.1)).mpr
        (fun i => (hfaces i).2.2)⟩
    intro hzero
    have : hazard coordinate = 0 := congrFun hzero coordinate
    linarith
  · rintro ⟨hnonzero, hfixed⟩
    have hbox := quittingCrossedClippedMap_fixed_mem_box
      (rationalQuittingRewardToReal reward) first second (height : ℝ) hheight.le hazard hfixed
    have hfaces := (quittingCrossedClippedMap_eq_self_iff
      (rationalQuittingRewardToReal reward) first second (height : ℝ) hheight hazard
      (fun i => (hbox i).1) (fun i => (hbox i).2)).mp hfixed
    refine ⟨?_, fun i => ⟨(hbox i).1, (hbox i).2, hfaces i⟩⟩
    by_contra hnone
    push Not at hnone
    apply hnonzero
    funext coordinate
    exact le_antisymm (hnone coordinate) (hbox coordinate).1

end GameTheory
