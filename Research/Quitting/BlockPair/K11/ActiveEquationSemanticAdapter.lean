import UniformEquilibrium.Quitting.Examples.BlockPair.K11OpponentLocalValue

namespace GameTheory.BlockPairK11.LocalInterval

open Math.Interval

variable {precision : ℕ}

/-- `CycleData` exposes the lifted opponent quitting-payoff summary. -/
theorem buildCycleData_opponentQuitValue_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (who : Player) :
    opponentQuitValue (buildCycleData box) phase who =
      RationalPolynomial.evalCachedDyadic box
        (BlockPairK11.opponentQuitValue phase who) := by
  simp only [opponentQuitValue, buildCycleData, buildLocalCyclePhases,
    Vector.get_ofFn]
  exact lift_buildLocalOpponentQuitValue_eq_evalCachedDyadic box phase who

/-- `CycleData` exposes the lifted opponent absorption summary. -/
theorem buildCycleData_opponentAbsorbingContribution_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (who : Player) :
    opponentAbsorbingContribution (buildCycleData box) phase who =
      RationalPolynomial.evalCachedDyadic box
        (BlockPairK11.opponentAbsorbingContribution phase who) := by
  simp only [opponentAbsorbingContribution, buildCycleData,
    buildLocalCyclePhases, Vector.get_ofFn]
  exact
    lift_buildLocalOpponentAbsorbingContribution_eq_evalCachedDyadic
      box phase who

/-- `CycleData` exposes the lifted opponent-survival summary. -/
theorem buildCycleData_opponentSurvival_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (who : Player) :
    opponentSurvival (buildCycleData box) phase who =
      RationalPolynomial.evalCachedDyadic box
        (BlockPairK11.opponentSurvival phase who) := by
  simp only [opponentSurvival, buildCycleData, buildLocalCyclePhases,
    Vector.get_ofFn]
  exact lift_buildLocalOpponentSurvival_eq_evalCachedDyadic box phase who

/-- The named derivative-preserving active-equation node agrees exactly with
canonical cached evaluation.  The proof composes the independently checked
cycle-survival, opponent-summary, and cyclic-numerator bridges. -/
theorem activeEquationAt_buildCycleData_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision)
    (phase : Phase) (who : Player) :
    activeEquationAt (buildCycleData box) phase who =
      RationalPolynomial.evalCachedDyadic box
        (BlockPairK11.activeEquationAt phase who) := by
  unfold activeEquationAt BlockPairK11.activeEquationAt
  rw [buildCycleData_jointSurvival_eq_evalCachedDyadic,
    buildCycleData_opponentQuitValue_eq_evalCachedDyadic,
    buildCycleData_opponentAbsorbingContribution_eq_evalCachedDyadic,
    buildCycleData_opponentSurvival_eq_evalCachedDyadic,
    cyclicValueNumerator_eq_evalCachedDyadic]
  rfl

/-- The active-equation vector uses the public `activeSlot` order without
changing the derivative-preserving semantics of any node. -/
theorem activeEquation_buildCycleData_eq_evalCachedDyadic
    (box : HazardIndex → DyadicInterval precision)
    (equation : HazardIndex) :
    activeEquationAt (buildCycleData box)
        (activeSlot equation).1 (activeSlot equation).2 =
      RationalPolynomial.evalCachedDyadic box
        (BlockPairK11.activeEquation equation) := by
  unfold BlockPairK11.activeEquation
  exact activeEquationAt_buildCycleData_eq_evalCachedDyadic box
    (activeSlot equation).1 (activeSlot equation).2


end GameTheory.BlockPairK11.LocalInterval
