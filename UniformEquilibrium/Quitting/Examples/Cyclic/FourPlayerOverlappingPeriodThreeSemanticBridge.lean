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
open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

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

/-- Product mass of one prescribed opponent coalition when the selected
player's own action is fixed separately. -/
def opponentCoalitionMass
    (hazard : Player → ℝ) (who : Player) (coalition : Finset Player) : ℝ :=
  ∏ other,
    if other = who then 1
    else if other ∈ coalition then hazard other else 1 - hazard other

/-- The opponent mass is unchanged by inserting the selected player into the
coalition whose opponents are prescribed. -/
@[simp] theorem opponentCoalitionMass_insert_self
    (hazard : Player → ℝ) (who : Player) (coalition : Finset Player) :
    opponentCoalitionMass hazard who (insert who coalition) =
      opponentCoalitionMass hazard who coalition := by
  unfold opponentCoalitionMass
  apply Finset.prod_congr rfl
  intro player _
  by_cases heq : player = who <;> simp [heq]

@[simp] theorem opponentCoalitionMass_singleton_self
    (hazard : Player → ℝ) (who : Player) :
    opponentCoalitionMass hazard who {who} =
      opponentCoalitionMass hazard who ∅ := by
  change opponentCoalitionMass hazard who (insert who ∅) =
    opponentCoalitionMass hazard who ∅
  exact opponentCoalitionMass_insert_self hazard who ∅

/-- Product-factor form of an opponent coalition mass when the selected
player is absent from the prescribed coalition. -/
theorem opponentCoalitionMass_eq_products_of_not_mem
    (hazard : Player → ℝ) (who : Player) (coalition : Finset Player)
    (hnot : who ∉ coalition) :
    opponentCoalitionMass hazard who coalition =
      (∏ player ∈ coalition, hazard player) *
        ∏ player ∈ Finset.univ.erase who \ coalition, (1 - hazard player) := by
  have hsub : coalition ⊆ Finset.univ.erase who := by
    intro player hplayer
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    exact hnot (heq ▸ hplayer)
  unfold opponentCoalitionMass
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ who)]
  simp
  calc
    (∏ player ∈ Finset.univ.erase who,
        if player = who then 1
        else if player ∈ coalition then hazard player else 1 - hazard player) =
        ∏ player ∈ Finset.univ.erase who,
          if player ∈ coalition then hazard player else 1 - hazard player := by
      apply Finset.prod_congr rfl
      intro player hplayer
      have hne : player ≠ who := Finset.ne_of_mem_erase hplayer
      simp [hne]
    _ = ∏ player ∈ coalition ∪ (Finset.univ.erase who \ coalition),
          if player ∈ coalition then hazard player else 1 - hazard player := by
      rw [Finset.union_sdiff_of_subset hsub]
    _ = (∏ player ∈ coalition,
          if player ∈ coalition then hazard player else 1 - hazard player) *
        ∏ player ∈ Finset.univ.erase who \ coalition,
          if player ∈ coalition then hazard player else 1 - hazard player := by
      rw [Finset.prod_union Finset.disjoint_sdiff]
    _ = _ := by
      congr 1
      · apply Finset.prod_congr rfl
        intro player hplayer
        simp [hplayer]
      · apply Finset.prod_congr rfl
        intro player hplayer
        have hnotMember : player ∉ coalition :=
          (Finset.mem_sdiff.mp hplayer).2
        simp [hnotMember]

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

/-- Full row-coordinate expansion of a player's sure-Quit endpoint value. -/
def pureQuitEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) (who : Player) : ℝ :=
  ∑ row : RewardRow,
    if who ∈ coalitionOfRow row then
      opponentCoalitionMass hazard who (coalitionOfRow row) *
        weightOfReward reward (coalitionOfRow row) who
    else 0

private theorem sigmaValue_zero_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) :
    sigmaValue (weightOfReward reward) hazard 0 =
      pureQuitEndpointRowSum reward hazard 0 := by
  rw [sigmaValue]
  rw [show (Finset.univ.erase (0 : Player)).powerset =
      ({∅, {1}, {2}, {1, 2}, {3}, {1, 3}, {2, 3}, {1, 2, 3}} :
        Finset (Finset Player)) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 0 ∅ (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {2, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 2, 3} (by decide)]
  simp [pureQuitEndpointRowSum, Fin.sum_univ_succ, coalitionOfRow,
    opponentCoalitionMass, Fin.prod_univ_succ]

private theorem sigmaValue_one_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) :
    sigmaValue (weightOfReward reward) hazard 1 =
      pureQuitEndpointRowSum reward hazard 1 := by
  rw [sigmaValue]
  rw [show (Finset.univ.erase (1 : Player)).powerset =
      ({∅, {0}, {2}, {0, 2}, {3}, {0, 3}, {2, 3}, {0, 2, 3}} :
        Finset (Finset Player)) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 1 ∅ (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {2, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 2, 3} (by decide)]
  rw [show ({1, 0} : Finset Player) = {0, 1} by decide,
    show ({1, 0, 2} : Finset Player) = {0, 1, 2} by decide,
    show ({1, 0, 3} : Finset Player) = {0, 1, 3} by decide,
    show ({1, 0, 2, 3} : Finset Player) = {0, 1, 2, 3} by decide]
  simp [pureQuitEndpointRowSum, Fin.sum_univ_succ, coalitionOfRow,
    opponentCoalitionMass, Fin.prod_univ_succ]

private theorem sigmaValue_two_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) :
    sigmaValue (weightOfReward reward) hazard 2 =
      pureQuitEndpointRowSum reward hazard 2 := by
  rw [sigmaValue]
  rw [show (Finset.univ.erase (2 : Player)).powerset =
      ({∅, {0}, {1}, {0, 1}, {3}, {0, 3}, {1, 3}, {0, 1, 3}} :
        Finset (Finset Player)) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 2 ∅ (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {1, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 1, 3} (by decide)]
  rw [show ({2, 0} : Finset Player) = {0, 2} by decide,
    show ({2, 1} : Finset Player) = {1, 2} by decide,
    show ({2, 0, 1} : Finset Player) = {0, 1, 2} by decide,
    show ({2, 0, 3} : Finset Player) = {0, 2, 3} by decide,
    show ({2, 1, 3} : Finset Player) = {1, 2, 3} by decide,
    show ({2, 0, 1, 3} : Finset Player) = {0, 1, 2, 3} by decide]
  simp [pureQuitEndpointRowSum, Fin.sum_univ_succ, coalitionOfRow,
    opponentCoalitionMass, Fin.prod_univ_succ]

private theorem sigmaValue_three_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) :
    sigmaValue (weightOfReward reward) hazard 3 =
      pureQuitEndpointRowSum reward hazard 3 := by
  rw [sigmaValue]
  rw [show (Finset.univ.erase (3 : Player)).powerset =
      ({∅, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}} :
        Finset (Finset Player)) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 3 ∅ (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {1, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 1, 2} (by decide)]
  rw [show ({3, 0} : Finset Player) = {0, 3} by decide,
    show ({3, 1} : Finset Player) = {1, 3} by decide,
    show ({3, 0, 1} : Finset Player) = {0, 1, 3} by decide,
    show ({3, 2} : Finset Player) = {2, 3} by decide,
    show ({3, 0, 2} : Finset Player) = {0, 2, 3} by decide,
    show ({3, 1, 2} : Finset Player) = {1, 2, 3} by decide,
    show ({3, 0, 1, 2} : Finset Player) = {0, 1, 2, 3} by decide]
  simp [pureQuitEndpointRowSum, Fin.sum_univ_succ, coalitionOfRow,
    opponentCoalitionMass, Fin.prod_univ_succ]

theorem sigmaValue_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) (who : Player) :
    sigmaValue (weightOfReward reward) hazard who =
      pureQuitEndpointRowSum reward hazard who := by
  fin_cases who
  · exact sigmaValue_zero_eq_pureQuitEndpointRowSum reward hazard
  · exact sigmaValue_one_eq_pureQuitEndpointRowSum reward hazard
  · exact sigmaValue_two_eq_pureQuitEndpointRowSum reward hazard
  · exact sigmaValue_three_eq_pureQuitEndpointRowSum reward hazard

/-- Full row-coordinate expansion of the nonempty-opponent Quit contribution
to the selected player's pure-Continue endpoint. -/
def excludedEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) (who : Player) : ℝ :=
  ∑ row : RewardRow,
    if who ∉ coalitionOfRow row then
      opponentCoalitionMass hazard who (coalitionOfRow row) *
        weightOfReward reward (coalitionOfRow row) who
    else 0

private theorem excludedValue_zero_eq_excludedEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) :
    excludedValue (weightOfReward reward) hazard 0 =
      excludedEndpointRowSum reward hazard 0 := by
  rw [excludedValue,
    show (Finset.univ.erase (0 : Player)).powerset.erase ∅ =
      ({ {1}, {2}, {1, 2}, {3}, {1, 3}, {2, 3}, {1, 2, 3} } :
        Finset (Finset Player)) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {2, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 2, 3} (by decide)]
  simp [excludedEndpointRowSum, Fin.sum_univ_succ, coalitionOfRow]

private theorem excludedValue_one_eq_excludedEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) :
    excludedValue (weightOfReward reward) hazard 1 =
      excludedEndpointRowSum reward hazard 1 := by
  rw [excludedValue,
    show (Finset.univ.erase (1 : Player)).powerset.erase ∅ =
      ({ {0}, {2}, {0, 2}, {3}, {0, 3}, {2, 3}, {0, 2, 3} } :
        Finset (Finset Player)) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {2, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 2, 3} (by decide)]
  simp [excludedEndpointRowSum, Fin.sum_univ_succ, coalitionOfRow]

private theorem excludedValue_two_eq_excludedEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) :
    excludedValue (weightOfReward reward) hazard 2 =
      excludedEndpointRowSum reward hazard 2 := by
  rw [excludedValue,
    show (Finset.univ.erase (2 : Player)).powerset.erase ∅ =
      ({ {0}, {1}, {0, 1}, {3}, {0, 3}, {1, 3}, {0, 1, 3} } :
        Finset (Finset Player)) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {1, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 1, 3} (by decide)]
  simp [excludedEndpointRowSum, Fin.sum_univ_succ, coalitionOfRow]

private theorem excludedValue_three_eq_excludedEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) :
    excludedValue (weightOfReward reward) hazard 3 =
      excludedEndpointRowSum reward hazard 3 := by
  rw [excludedValue,
    show (Finset.univ.erase (3 : Player)).powerset.erase ∅ =
      ({ {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2} } :
        Finset (Finset Player)) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {1, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 1, 2} (by decide)]
  simp [excludedEndpointRowSum, Fin.sum_univ_succ, coalitionOfRow]

theorem excludedValue_eq_excludedEndpointRowSum
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Player → ℝ) (who : Player) :
    excludedValue (weightOfReward reward) hazard who =
      excludedEndpointRowSum reward hazard who := by
  fin_cases who
  · exact excludedValue_zero_eq_excludedEndpointRowSum reward hazard
  · exact excludedValue_one_eq_excludedEndpointRowSum reward hazard
  · exact excludedValue_two_eq_excludedEndpointRowSum reward hazard
  · exact excludedValue_three_eq_excludedEndpointRowSum reward hazard

@[simp] theorem opponentCoalitionMass_eq_zero_of_pureQuitRow_not_supported
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (who : Player)
    (row : RewardRow) (hmember : who ∈ coalitionOfRow row)
    (hnot : row ∉ pureQuitRows phase who) :
    opponentCoalitionMass (hazardOfNormalized point phase) who
      (coalitionOfRow row) = 0 := by
  fin_cases phase <;> fin_cases who <;> fin_cases row <;>
    simp [pureQuitRows, coalitionOfRow] at hmember hnot ⊢ <;>
    simp [opponentCoalitionMass, hazardOfNormalized,
      Fin.prod_univ_succ]

@[simp] theorem opponentCoalitionMass_eq_zero_of_excludedRow_not_supported
    (point : HazardCoordinate → ℝ) (phase : Fin 3) (who : Player)
    (row : RewardRow) (hnotMember : who ∉ coalitionOfRow row)
    (hnot : row ∉ excludedRows phase who) :
    opponentCoalitionMass (hazardOfNormalized point phase) who
      (coalitionOfRow row) = 0 := by
  fin_cases phase <;> fin_cases who <;> fin_cases row <;>
    simp [excludedRows, coalitionOfRow] at hnotMember hnot ⊢ <;>
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
  fin_cases phase <;> fin_cases who <;>
    simp [supportedPureQuitExpression, pureQuitRows,
      pureQuitEndpointRowSum, rowContains, Fin.sum_univ_succ]

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
  fin_cases phase <;> fin_cases who <;>
    simp [supportedExcludedExpression, excludedRows,
      excludedEndpointRowSum, rowContains, Fin.sum_univ_succ]

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
