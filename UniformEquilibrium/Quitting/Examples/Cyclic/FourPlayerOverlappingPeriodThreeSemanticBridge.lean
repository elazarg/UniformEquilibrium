import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeActiveRoot
import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeInactiveGapBounds
import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeSupport

/-!
# Semantic bridge for the overlapping-support period-three chart

The interval enclosure uses a factored polynomial evaluator.  This file
connects that evaluator literally to the period-three cleared endpoint gaps
consumed by the unrestricted behavioral-deviation compiler.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Math.Interval Math.Interval.RationalPolynomial
open QuittingFinFourEndpointRows
open _root_.Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

/-- Flatten a reward row and player into its normalized reward coordinate. -/
def rewardParameterIndex (row : RewardRow) (who : Player) : Fin 60 :=
  ⟨row.val * 4 + who.val, by omega⟩

/-- Convert sixty normalized reward parameters to the corresponding reward
coordinates in the certified radius around the displayed rational table. -/
def rewardCoordinatesOfNormalizedParameter
    (parameter : Fin 60 → ℝ) : RewardCoordinates :=
  fun row who ↦
    overlappingPeriodThreeRewardRow row who + rewardRadius *
      parameter (rewardParameterIndex row who)

@[simp] theorem leadingCoordinatePoint_hazardVariableIndex
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (coordinate : HazardCoordinate) :
    leadingCoordinatePoint point parameter (hazardVariableIndex coordinate) =
      point coordinate := by
  rw [show hazardVariableIndex coordinate = Fin.castAdd 60 coordinate by
    apply Fin.ext
    rfl]
  exact Fin.addCases_left coordinate

@[simp] theorem leadingCoordinatePoint_rewardVariableIndex
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (row : RewardRow) (who : Player) :
    leadingCoordinatePoint point parameter (rewardVariableIndex row who) =
      parameter (rewardParameterIndex row who) := by
  rw [show rewardVariableIndex row who =
      Fin.natAdd 8 (rewardParameterIndex row who) by
    apply Fin.ext
    simp [rewardVariableIndex, rewardParameterIndex, Nat.add_assoc]]
  exact Fin.addCases_right _

@[simp] theorem evalReal_leadingCoordinatePoint_hazardExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) :
    evalReal (leadingCoordinatePoint point parameter)
        (hazardExpression phase who) =
      hazardOfNormalized point phase who := by
  fin_cases phase <;> fin_cases who <;>
    simp [hazardExpression, hazardOfNormalized,
      Math.Interval.RationalPolynomial.evalReal]

@[simp] theorem evalReal_leadingCoordinatePoint_rewardExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (row : RewardRow) (who : Player) :
    evalReal (leadingCoordinatePoint point parameter)
        (rewardExpression row who) =
      rewardCoordinatesOfNormalizedParameter parameter row who := by
  simp [rewardExpression, rewardCoordinatesOfNormalizedParameter,
    rewardParameterIndex]

@[simp] theorem evalReal_one
    (coordinate : NormalizedCoordinate → ℝ) :
    evalReal coordinate (1 : RationalPolynomial 68) = 1 := by
  change evalReal coordinate (.constant 1) = 1
  simp [evalReal]

@[simp] theorem evalReal_zero
    (coordinate : NormalizedCoordinate → ℝ) :
    evalReal coordinate (0 : RationalPolynomial 68) = 0 := by
  change evalReal coordinate (.constant 0) = 0
  simp [evalReal]

@[simp] theorem evalReal_polynomialListSum
    (coordinate : NormalizedCoordinate → ℝ)
    (expressions : List (RationalPolynomial 68)) :
    evalReal coordinate (polynomialListSum expressions) =
      (expressions.map (evalReal coordinate)).sum := by
  unfold polynomialListSum
  induction expressions with
  | nil => simp
  | cons expression expressions ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons,
        evalReal_polynomialAdd]
      rw [ih]

theorem rowContains_eq_decide_mem_coalitionOfRow
    (row : RewardRow) (who : Player) :
    rowContains row who = decide (who ∈ coalitionOfRow row) := by
  fin_cases row <;> fin_cases who <;> decide

@[simp] theorem mem_coalitionOfRow_iff_rowContains
    (row : RewardRow) (who : Player) :
    who ∈ coalitionOfRow row ↔ rowContains row who = true := by
  rw [rowContains_eq_decide_mem_coalitionOfRow]
  simp

@[simp] theorem evalReal_leadingCoordinatePoint_rowHazardFactor
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (row : RewardRow) (who : Player) :
    evalReal (leadingCoordinatePoint point parameter)
        (rowHazardFactor phase row who) =
      if who ∈ coalitionOfRow row then
        hazardOfNormalized point phase who
      else 1 - hazardOfNormalized point phase who := by
  rw [rowHazardFactor]
  rw [rowContains_eq_decide_mem_coalitionOfRow]
  by_cases hmem : who ∈ coalitionOfRow row <;> simp [hmem]

@[simp] theorem evalReal_leadingCoordinatePoint_continueExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) :
    evalReal (leadingCoordinatePoint point parameter)
        (continueExpression phase) =
      continueMass (hazardOfNormalized point phase) := by
  fin_cases phase <;>
    simp [continueExpression, polynomialProduct, continueMass,
      Fin.prod_univ_succ]

@[simp] theorem continueMassExcl_zero (hazard : Player → ℝ) :
    continueMassExcl hazard 0 =
      (1 - hazard 1) * (1 - hazard 2) * (1 - hazard 3) := by
  rw [continueMassExcl,
    show Finset.univ.erase (0 : Player) = {1, 2, 3} by decide]
  simp
  ring

@[simp] theorem continueMassExcl_one (hazard : Player → ℝ) :
    continueMassExcl hazard 1 =
      (1 - hazard 0) * (1 - hazard 2) * (1 - hazard 3) := by
  rw [continueMassExcl,
    show Finset.univ.erase (1 : Player) = {0, 2, 3} by decide]
  simp
  ring

@[simp] theorem continueMassExcl_two (hazard : Player → ℝ) :
    continueMassExcl hazard 2 =
      (1 - hazard 0) * (1 - hazard 1) * (1 - hazard 3) := by
  rw [continueMassExcl,
    show Finset.univ.erase (2 : Player) = {0, 1, 3} by decide]
  simp
  ring

@[simp] theorem continueMassExcl_three (hazard : Player → ℝ) :
    continueMassExcl hazard 3 =
      (1 - hazard 0) * (1 - hazard 1) * (1 - hazard 2) := by
  rw [continueMassExcl,
    show Finset.univ.erase (3 : Player) = {0, 1, 2} by decide]
  simp
  ring

@[simp] theorem evalReal_leadingCoordinatePoint_opponentContinueExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) :
    evalReal (leadingCoordinatePoint point parameter)
        (opponentContinueExpression phase who) =
      continueMassExcl (hazardOfNormalized point phase) who := by
  fin_cases phase <;> fin_cases who <;>
    simp [opponentContinueExpression, polynomialProduct] <;>
    ring

theorem coalitionMass_eq_product_choice_fin_four
    (hazard : Player → ℝ) (coalition : Finset Player) :
    coalitionMass hazard coalition =
      ∏ player,
        if player ∈ coalition then hazard player else 1 - hazard player := by
  rw [coalitionMass]
  have hcomplement :
      (∏ player, if player ∈ coalition then 1 else 1 - hazard player) =
        ∏ player ∈ coalitionᶜ, (1 - hazard player) := by
    calc
      (∏ player, if player ∈ coalition then 1 else 1 - hazard player) =
          ∏ player,
            if player ∈ coalitionᶜ then 1 - hazard player else 1 := by
        apply Finset.prod_congr rfl
        intro player _
        by_cases hmem : player ∈ coalition <;> simp [hmem]
      _ = ∏ player ∈ coalitionᶜ, (1 - hazard player) :=
        Fintype.prod_ite_mem coalitionᶜ fun player ↦ 1 - hazard player
  have hcoalition :
      (∏ player, if player ∈ coalition then hazard player else 1) =
        ∏ player ∈ coalition, hazard player :=
    Fintype.prod_ite_mem coalition hazard
  rw [← hcoalition, ← hcomplement, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro player _
  by_cases hmem : player ∈ coalition <;> simp [hmem]

@[simp] theorem weightOfReward_rewardOfCoordinates_coalitionOfRow
    (rewardCoordinates : RewardCoordinates)
    (row : RewardRow) (who : Player) :
    weightOfReward (rewardOfCoordinates rewardCoordinates)
        (coalitionOfRow row) who =
      rewardCoordinates row who := by
  rw [show coalitionOfRow row = (coalitionRowEquiv row).1 from rfl]
  simp [weightOfReward, rewardOfCoordinates,
    (coalitionRowEquiv row).property]

theorem quittingPeriodThreeImmediateContribution_eq_sum_rows
    (rewardCoordinates : RewardCoordinates)
    (hazard : Fin 3 → Player → ℝ) (phase : Fin 3) (who : Player) :
    quittingPeriodThreeImmediateContribution
        (rewardOfCoordinates rewardCoordinates) hazard phase who =
      ∑ row : RewardRow,
        coalitionMass (hazard phase) (coalitionOfRow row) *
          rewardCoordinates row who := by
  let term : Finset Player → ℝ := fun coalition ↦
    coalitionMass (hazard phase) coalition *
      weightOfReward (rewardOfCoordinates rewardCoordinates) coalition who
  have hzero :
      (∑ coalition : {coalition : Finset Player // ¬coalition.Nonempty},
        term coalition) = 0 := by
    apply Finset.sum_eq_zero
    intro coalition _
    simp [term, weightOfReward, coalition.property]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun coalition : Finset Player ↦ coalition.Nonempty) term
  rw [hzero, add_zero] at hsplit
  rw [quittingPeriodThreeImmediateContribution]
  change (∑ coalition : Finset Player, term coalition) = _
  rw [← hsplit]
  symm
  apply Fintype.sum_equiv coalitionRowEquiv
  intro row
  change coalitionMass (hazard phase) (coalitionOfRow row) *
      rewardCoordinates row who =
    coalitionMass (hazard phase) (coalitionOfRow row) *
      weightOfReward (rewardOfCoordinates rewardCoordinates)
        (coalitionOfRow row) who
  rw [weightOfReward_rewardOfCoordinates_coalitionOfRow]

@[simp] theorem evalReal_leadingCoordinatePoint_supportedCoalitionMassExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (row : RewardRow) :
    evalReal (leadingCoordinatePoint point parameter)
        (supportedCoalitionMassExpression phase row) =
      coalitionMass (hazardOfNormalized point phase) (coalitionOfRow row) := by
  rw [coalitionMass_eq_product_choice_fin_four]
  fin_cases phase <;> fin_cases row <;>
    simp [supportedCoalitionMassExpression, coalitionOfRow,
      Fin.prod_univ_succ]

@[simp] theorem evalReal_leadingCoordinatePoint_supportedImmediateTerm
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) (row : RewardRow) :
    evalReal (leadingCoordinatePoint point parameter)
        (supportedImmediateTerm phase who row) =
      coalitionMass (hazardOfNormalized point phase) (coalitionOfRow row) *
        rewardCoordinatesOfNormalizedParameter parameter row who := by
  rw [supportedImmediateTerm, evalReal_polynomialMul,
    evalReal_leadingCoordinatePoint_supportedCoalitionMassExpression,
    evalReal_leadingCoordinatePoint_rewardExpression]

@[simp] theorem coalitionMass_coalitionOfRow_eq_zero_of_not_mem_supportRows
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (row : RewardRow)
    (hnot : row ∉ supportRows phase) :
    coalitionMass (hazardOfNormalized point phase) (coalitionOfRow row) = 0 := by
  rw [coalitionMass_eq_product_choice_fin_four]
  fin_cases phase <;> fin_cases row <;>
    simp [supportRows] at hnot ⊢ <;>
    simp [rowContains, hazardOfNormalized,
      Fin.prod_univ_succ]

@[simp] theorem evalReal_leadingCoordinatePoint_supportedImmediateExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) :
    evalReal (leadingCoordinatePoint point parameter)
        (supportedImmediateExpression phase who) =
      quittingPeriodThreeImmediateContribution
        (rewardOfCoordinates
          (rewardCoordinatesOfNormalizedParameter parameter))
        (hazardOfNormalized point) phase who := by
  rw [quittingPeriodThreeImmediateContribution_eq_sum_rows]
  fin_cases phase <;> fin_cases who <;>
    simp [supportedImmediateExpression, supportRows, Fin.sum_univ_succ]


@[simp] theorem evalReal_leadingCoordinatePoint_supportedOpponentMassExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) (row : RewardRow) :
    evalReal (leadingCoordinatePoint point parameter)
        (supportedOpponentMassExpression phase who row) =
      opponentCoalitionMass (hazardOfNormalized point phase) who
        (coalitionOfRow row) := by
  fin_cases who <;>
    simp [supportedOpponentMassExpression, opponentCoalitionMass,
      Fin.prod_univ_succ]

@[simp] theorem evalReal_leadingCoordinatePoint_supportedEndpointTerm
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) (row : RewardRow) :
    evalReal (leadingCoordinatePoint point parameter)
        (supportedEndpointTerm phase who row) =
      opponentCoalitionMass (hazardOfNormalized point phase) who
          (coalitionOfRow row) *
        rewardCoordinatesOfNormalizedParameter parameter row who := by
  rw [supportedEndpointTerm, evalReal_polynomialMul,
    evalReal_leadingCoordinatePoint_supportedOpponentMassExpression,
    evalReal_leadingCoordinatePoint_rewardExpression]


@[simp] theorem opponentCoalitionMass_eq_zero_of_pureQuitRow_not_supported
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (who : Player)
    (row : RewardRow) (hmember : who ∈ coalitionOfRow row)
    (hnot : row ∉ pureQuitRows phase who) :
    opponentCoalitionMass (hazardOfNormalized point phase) who
      (coalitionOfRow row) = 0 := by
  fin_cases phase <;> fin_cases who <;> fin_cases row <;>
    simp [pureQuitRows, coalitionOfRow, Math.Finset.finFourCoalitionOfRow]
      at hmember hnot ⊢ <;>
    simp [opponentCoalitionMass, hazardOfNormalized,
      Fin.prod_univ_succ]

@[simp] theorem opponentCoalitionMass_eq_zero_of_excludedRow_not_supported
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (who : Player)
    (row : RewardRow) (hnotMember : who ∉ coalitionOfRow row)
    (hnot : row ∉ excludedRows phase who) :
    opponentCoalitionMass (hazardOfNormalized point phase) who
      (coalitionOfRow row) = 0 := by
  fin_cases phase <;> fin_cases who <;> fin_cases row <;>
    simp [excludedRows, coalitionOfRow, Math.Finset.finFourCoalitionOfRow]
      at hnotMember hnot ⊢ <;>
    simp [opponentCoalitionMass, hazardOfNormalized,
      Fin.prod_univ_succ]

@[simp] theorem evalReal_leadingCoordinatePoint_supportedPureQuitExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) :
    evalReal (leadingCoordinatePoint point parameter)
        (supportedPureQuitExpression phase who) =
      sigmaValue
        (weightOfReward (rewardOfCoordinates
          (rewardCoordinatesOfNormalizedParameter parameter)))
        (hazardOfNormalized point phase) who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  unfold supportedPureQuitExpression
  rw [evalReal_polynomialListSum]
  simp only [List.map_map]
  let term : RewardRow → ℝ := fun row =>
    opponentCoalitionMass (hazardOfNormalized point phase) who
        (coalitionOfRow row) *
      rewardCoordinatesOfNormalizedParameter parameter row who
  have heval : List.map
      (evalReal (leadingCoordinatePoint point parameter) ∘
        fun row => supportedEndpointTerm phase who row)
        (pureQuitRows phase who) =
      List.map term (pureQuitRows phase who) := by
    apply List.map_congr_left
    intro row _
    exact evalReal_leadingCoordinatePoint_supportedEndpointTerm
      point parameter phase who row
  rw [heval]
  change ((pureQuitRows phase who).map term).sum = _
  have hnodup : (pureQuitRows phase who).Nodup := by
    fin_cases phase <;> fin_cases who <;> decide
  rw [← List.sum_toFinset term hnodup]
  unfold pureQuitEndpointRowSum
  simp_rw [weightOfReward_rewardOfCoordinates_coalitionOfRow]
  have hmembers : ∀ row ∈ pureQuitRows phase who,
      who ∈ coalitionOfRow row := by
    fin_cases phase <;> fin_cases who <;> intro row <;>
      fin_cases row <;> decide
  let fullTerm : RewardRow → ℝ := fun row =>
    if who ∈ coalitionOfRow row then term row else 0
  change (∑ row ∈ (pureQuitRows phase who).toFinset, term row) =
    ∑ row, fullTerm row
  calc
    (∑ row ∈ (pureQuitRows phase who).toFinset, term row) =
        ∑ row ∈ (pureQuitRows phase who).toFinset, fullTerm row := by
      apply Finset.sum_congr rfl
      intro row hrow
      have hmember := hmembers row (by simpa using hrow)
      dsimp only [fullTerm]
      rw [ite_eq_left hmember]
    _ = ∑ row, fullTerm row := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro row _ hnot
      by_cases hmember : who ∈ coalitionOfRow row
      · have hunsupported : row ∉ pureQuitRows phase who := by
          simpa using hnot
        dsimp only [fullTerm]
        rw [ite_eq_left hmember]
        unfold term
        rw [opponentCoalitionMass_eq_zero_of_pureQuitRow_not_supported
          point phase who row hmember hunsupported, zero_mul]
      · dsimp only [fullTerm]
        rw [ite_eq_right hmember]

@[simp] theorem evalReal_leadingCoordinatePoint_supportedExcludedExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) :
    evalReal (leadingCoordinatePoint point parameter)
        (supportedExcludedExpression phase who) =
      excludedValue
        (weightOfReward (rewardOfCoordinates
          (rewardCoordinatesOfNormalizedParameter parameter)))
        (hazardOfNormalized point phase) who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  unfold supportedExcludedExpression
  rw [evalReal_polynomialListSum]
  simp only [List.map_map]
  let term : RewardRow → ℝ := fun row =>
    opponentCoalitionMass (hazardOfNormalized point phase) who
        (coalitionOfRow row) *
      rewardCoordinatesOfNormalizedParameter parameter row who
  have heval : List.map
      (evalReal (leadingCoordinatePoint point parameter) ∘
        fun row => supportedEndpointTerm phase who row)
        (excludedRows phase who) =
      List.map term (excludedRows phase who) := by
    apply List.map_congr_left
    intro row _
    exact evalReal_leadingCoordinatePoint_supportedEndpointTerm
      point parameter phase who row
  rw [heval]
  change ((excludedRows phase who).map term).sum = _
  have hnodup : (excludedRows phase who).Nodup := by
    fin_cases phase <;> fin_cases who <;> decide
  rw [← List.sum_toFinset term hnodup]
  unfold excludedEndpointRowSum
  simp_rw [weightOfReward_rewardOfCoordinates_coalitionOfRow]
  have hmembers : ∀ row ∈ excludedRows phase who,
      who ∉ coalitionOfRow row := by
    fin_cases phase <;> fin_cases who <;> intro row <;>
      fin_cases row <;> decide
  let fullTerm : RewardRow → ℝ := fun row =>
    if who ∉ coalitionOfRow row then term row else 0
  change (∑ row ∈ (excludedRows phase who).toFinset, term row) =
    ∑ row, fullTerm row
  calc
    (∑ row ∈ (excludedRows phase who).toFinset, term row) =
        ∑ row ∈ (excludedRows phase who).toFinset, fullTerm row := by
      apply Finset.sum_congr rfl
      intro row hrow
      have hmember := hmembers row (by simpa using hrow)
      dsimp only [fullTerm]
      rw [ite_eq_left hmember]
    _ = ∑ row, fullTerm row := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro row _ hnot
      by_cases hmember : who ∉ coalitionOfRow row
      · have hunsupported : row ∉ excludedRows phase who := by
          simpa using hnot
        dsimp only [fullTerm]
        rw [ite_eq_left hmember]
        unfold term
        rw [opponentCoalitionMass_eq_zero_of_excludedRow_not_supported
          point phase who row hmember hunsupported, zero_mul]
      · dsimp only [fullTerm]
        rw [ite_eq_right hmember]

@[simp] theorem evalReal_leadingCoordinatePoint_denominatorExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ) :
    evalReal (leadingCoordinatePoint point parameter) denominatorExpression =
      quittingPeriodThreeAbsorptionDenominator (hazardOfNormalized point) := by
  simp [denominatorExpression, quittingPeriodThreeAbsorptionDenominator,
    quittingPeriodThreeContinueMass]

@[simp] theorem evalReal_leadingCoordinatePoint_supportedWindowExpression
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) :
    evalReal (leadingCoordinatePoint point parameter)
        (supportedWindowExpression phase who) =
      quittingPeriodThreeImmediateWindow
        (rewardOfCoordinates
          (rewardCoordinatesOfNormalizedParameter parameter))
        (hazardOfNormalized point) phase who := by
  fin_cases phase <;>
    simp [supportedWindowExpression, quittingPeriodThreeImmediateWindow,
      quittingPeriodThreeContinueMass] <;>
    ring

/-- The factored interval polynomial is literally the denominator-cleared
semantic pure-Quit minus pure-Continue endpoint difference. -/
theorem evalReal_supportedClearedGapExpression_eq_semantic
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (phase : Fin 3) (who : Player) :
    evalReal (leadingCoordinatePoint point parameter)
        (supportedClearedGapExpression phase who) =
      quittingPeriodThreeClearedEndpointDifference
        (rewardOfCoordinates
          (rewardCoordinatesOfNormalizedParameter parameter))
        (hazardOfNormalized point) phase who := by
  fin_cases phase <;>
    simp [supportedClearedGapExpression,
      quittingPeriodThreeClearedEndpointDifference, nextPhase]

end GameTheory.FourPlayerOverlappingPeriodThree

end
