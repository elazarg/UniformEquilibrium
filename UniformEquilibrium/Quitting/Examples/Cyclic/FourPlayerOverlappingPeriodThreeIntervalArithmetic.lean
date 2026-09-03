import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreePolynomialSystem
import MathUE.Interval.SelectedCoordinatePolynomialLipschitz

/-!
# Exact interval arithmetic for the overlapping period-three reward table

The enclosure uses 64-bit dyadic outward rounding.  The eight hazard
coordinates are selected for automatic differentiation; the other sixty
coordinates remain independent reward parameters.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Math.Interval Math.Interval.RationalPolynomial

abbrev neighborhoodPrecision := 64

def fullNormalizedCoordinateBox : NormalizedCoordinate →
    DyadicInterval neighborhoodPrecision :=
  fun _ ↦ ⟨-DyadicInterval.scale neighborhoodPrecision,
    DyadicInterval.scale neighborhoodPrecision⟩

def rewardParameterCenterBox : NormalizedCoordinate →
    DyadicInterval neighborhoodPrecision :=
  fun coordinate ↦ if coordinate.val < 8 then DyadicInterval.ofInt 0
    else fullNormalizedCoordinateBox coordinate

def centeredActiveResidualDual (coordinate : HazardCoordinate) :=
  evalSelectedDualDyadic hazardVariableIndex rewardParameterCenterBox
    (activeResidualExpression coordinate)

def fullBoxActiveResidualDual (coordinate : HazardCoordinate) :=
  evalSelectedDualDyadic hazardVariableIndex fullNormalizedCoordinateBox
    (activeResidualExpression coordinate)

def fullBoxActiveResidualPartial
    (coordinate input : HazardCoordinate) :=
  evalDyadicPartial (hazardVariableIndex input)
    fullNormalizedCoordinateBox (activeResidualExpression coordinate)

def centeredActiveResidualEnclosure : HazardCoordinate →
    DyadicInterval neighborhoodPrecision :=
  ![⟨-676862693914, 676862617999⟩,
    ⟨-676862633396, 676862678526⟩,
    ⟨-676862638879, 676862673035⟩,
    ⟨-676862702578, 676862609339⟩,
    ⟨-676862644488, 676862667430⟩,
    ⟨-676862631491, 676862680416⟩,
    ⟨-676862640298, 676862671612⟩,
    ⟨-676862652621, 676862659289⟩]

local macro "verify_centered_active_residual" : tactic => `(tactic|
  (simp [centeredActiveResidualDual, centeredActiveResidualEnclosure,
      activeResidualExpression, supportedClearedGapExpression,
      supportedWindowExpression, supportedImmediateExpression,
      supportedPureQuitExpression, supportedExcludedExpression,
      supportedImmediateTerm, supportedEndpointTerm,
      supportedCoalitionMassExpression, supportedOpponentMassExpression,
      rowHazardFactor, rowContains, supportRows, pureQuitRows, excludedRows,
      polynomialListSum, denominatorExpression,
      opponentContinueExpression, continueExpression, hazardExpression,
      rewardExpression, activeSlot, nextPhase, hazardVariableIndex,
      rewardVariableIndex, hazardCenter, hazardRadius, rewardRadius,
      overlappingPeriodThreeRewardRow] <;>
    norm_num1 <;>
    simp [polynomialProduct, polynomialAdd, polynomialSub,
      polynomialNeg, polynomialMul] <;>
    norm_num [rewardParameterCenterBox, fullNormalizedCoordinateBox,
      DyadicInterval.ofRat, DyadicInterval.ofInt, DyadicInterval.add,
      DyadicInterval.neg, DyadicInterval.mul_eq_outward_four_corners,
      DyadicInterval.scale, Rat.floor_def, Rat.ceil,
      neighborhoodPrecision]))

private theorem centeredActiveResidualValue_zero_exact :
    (centeredActiveResidualDual 0).value =
      centeredActiveResidualEnclosure 0 := by
  verify_centered_active_residual

private theorem centeredActiveResidualValue_one_exact :
    (centeredActiveResidualDual 1).value =
      centeredActiveResidualEnclosure 1 := by
  verify_centered_active_residual

private theorem centeredActiveResidualValue_two_exact :
    (centeredActiveResidualDual 2).value =
      centeredActiveResidualEnclosure 2 := by
  verify_centered_active_residual

private theorem centeredActiveResidualValue_three_exact :
    (centeredActiveResidualDual 3).value =
      centeredActiveResidualEnclosure 3 := by
  verify_centered_active_residual

private theorem centeredActiveResidualValue_four_exact :
    (centeredActiveResidualDual 4).value =
      centeredActiveResidualEnclosure 4 := by
  verify_centered_active_residual

private theorem centeredActiveResidualValue_five_exact :
    (centeredActiveResidualDual 5).value =
      centeredActiveResidualEnclosure 5 := by
  verify_centered_active_residual

private theorem centeredActiveResidualValue_six_exact :
    (centeredActiveResidualDual 6).value =
      centeredActiveResidualEnclosure 6 := by
  verify_centered_active_residual

private theorem centeredActiveResidualValue_seven_exact :
    (centeredActiveResidualDual 7).value =
      centeredActiveResidualEnclosure 7 := by
  verify_centered_active_residual

@[simp] theorem centeredActiveResidualValue_exact
    (coordinate : HazardCoordinate) :
    (centeredActiveResidualDual coordinate).value =
      centeredActiveResidualEnclosure coordinate := by
  fin_cases coordinate
  · exact centeredActiveResidualValue_zero_exact
  · exact centeredActiveResidualValue_one_exact
  · exact centeredActiveResidualValue_two_exact
  · exact centeredActiveResidualValue_three_exact
  · exact centeredActiveResidualValue_four_exact
  · exact centeredActiveResidualValue_five_exact
  · exact centeredActiveResidualValue_six_exact
  · exact centeredActiveResidualValue_seven_exact

def fullBoxActiveResidualDerivativeEnclosure :
    HazardCoordinate → HazardCoordinate →
      DyadicInterval neighborhoodPrecision :=
  ![![⟨-554994, 554994⟩,
      ⟨2489052225036, 2489057658299⟩,
      ⟨-2831864097181, -2831857716369⟩,
      ⟨-2604125, 2604123⟩,
      ⟨2053941874517, 2053947399139⟩,
      ⟨-818258566461, -818254993244⟩,
      ⟨1947371157586, 1947374940259⟩,
      ⟨852118888375, 852121263245⟩],
    ![⟨2860708464434, 2860714633954⟩,
      ⟨-491976, 491976⟩,
      ⟨1933057466526, 1933062665933⟩,
      ⟨-2281100202178, -2281092694306⟩,
      ⟨-4164751590457, -4164743198797⟩,
      ⟨627305931064, 627308019998⟩,
      ⟨-937556, 937556⟩,
      ⟨-864524095392, -864521208208⟩],
    ![⟨-929242782743, -929239656959⟩,
      ⟨849963789581, 849966036432⟩,
      ⟨-564396, 564396⟩,
      ⟨-5550868079098, -5550859264534⟩,
      ⟨1782480117169, 1782487157512⟩,
      ⟨-1776115, 1776116⟩,
      ⟨852010050496, 852013383576⟩,
      ⟨719017861391, 719020911850⟩],
    ![⟨-964185, 964185⟩,
      ⟨306907079372, 306908540566⟩,
      ⟨-1386062990206, -1386052267098⟩,
      ⟨-595243, 595243⟩,
      ⟨5647054733896, 5647065048330⟩,
      ⟨-1220290387774, -1220285678571⟩,
      ⟨2904166586564, 2904171544526⟩,
      ⟨1270787483566, 1270791045178⟩],
    ![⟨641362223884, 641364033116⟩,
      ⟨-984051931740, -984049045880⟩,
      ⟨1959550173853, 1959556529977⟩,
      ⟨1146864119642, 1146869998572⟩,
      ⟨-552314, 552314⟩,
      ⟨1349911672580, 1349916969830⟩,
      ⟨-2879293839025, -2879287460460⟩,
      ⟨-2189272, 2189273⟩],
    ![⟨-2456892374158, -2456888025013⟩,
      ⟨2247283755983, 2247287556925⟩,
      ⟨-1010309, 1010309⟩,
      ⟨-1091937022818, -1091933667511⟩,
      ⟨435418147075, 435420092018⟩,
      ⟨-688452, 688452⟩,
      ⟨1732132995618, 1732138793066⟩,
      ⟨1047615786888, 1047621232555⟩],
    ![⟨982003453204, 982006889823⟩,
      ⟨-1340107, 1340107⟩,
      ⟨663566162905, 663568676969⟩,
      ⟨-783040777901, -783037080963⟩,
      ⟨-1429647857643, -1429643202809⟩,
      ⟨2198733580366, 2198741159577⟩,
      ⟨-497104, 497104⟩,
      ⟨-4627810524332, -4627802555933⟩],
    ![⟨1112376138177, 1112379298845⟩,
      ⟨-1706735080886, -1706731609049⟩,
      ⟨311924052418, 311925705799⟩,
      ⟨239243870964, 239245328217⟩,
      ⟨-918635, 918636⟩,
      ⟨4071546191398, 4071555532107⟩,
      ⟨-2292628931503, -2292619199802⟩,
      ⟨-594717, 594717⟩]]


local macro "verify_full_box_active_residual_derivative" : tactic => `(tactic|
  (simp [fullBoxActiveResidualPartial,
      fullBoxActiveResidualDerivativeEnclosure,
      evalDyadicPartial, DyadicPartialEvaluation.constant,
      DyadicPartialEvaluation.ofVariable, DyadicPartialEvaluation.add,
      DyadicPartialEvaluation.neg, DyadicPartialEvaluation.mul,
      activeResidualExpression, supportedClearedGapExpression,
      supportedWindowExpression, supportedImmediateExpression,
      supportedPureQuitExpression, supportedExcludedExpression,
      supportedImmediateTerm, supportedEndpointTerm,
      supportedCoalitionMassExpression, supportedOpponentMassExpression,
      rowHazardFactor, rowContains, supportRows, pureQuitRows, excludedRows,
      polynomialListSum, denominatorExpression,
      opponentContinueExpression, continueExpression, hazardExpression,
      rewardExpression, activeSlot, nextPhase, hazardVariableIndex,
      rewardVariableIndex, hazardCenter, hazardRadius, rewardRadius,
      overlappingPeriodThreeRewardRow] <;>
    norm_num1 <;>
    simp [polynomialProduct, polynomialAdd, polynomialSub,
      polynomialNeg, polynomialMul, evalDyadicPartial,
      DyadicPartialEvaluation.constant,
      DyadicPartialEvaluation.ofVariable, DyadicPartialEvaluation.add,
      DyadicPartialEvaluation.neg, DyadicPartialEvaluation.mul] <;>
    norm_num [fullNormalizedCoordinateBox, DyadicInterval.ofRat,
      DyadicInterval.ofInt, DyadicInterval.add, DyadicInterval.neg,
      DyadicInterval.mul_eq_outward_four_corners, DyadicInterval.scale,
      Rat.floor_def, Rat.ceil, neighborhoodPrecision]))

@[simp] private theorem fullBoxActiveResidualDerivative_zero_zero_exact :
    (fullBoxActiveResidualPartial 0 0).derivative =
      fullBoxActiveResidualDerivativeEnclosure 0 0 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_zero_one_exact :
    (fullBoxActiveResidualPartial 0 1).derivative =
      fullBoxActiveResidualDerivativeEnclosure 0 1 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_zero_two_exact :
    (fullBoxActiveResidualPartial 0 2).derivative =
      fullBoxActiveResidualDerivativeEnclosure 0 2 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_zero_three_exact :
    (fullBoxActiveResidualPartial 0 3).derivative =
      fullBoxActiveResidualDerivativeEnclosure 0 3 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_zero_four_exact :
    (fullBoxActiveResidualPartial 0 4).derivative =
      fullBoxActiveResidualDerivativeEnclosure 0 4 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_zero_five_exact :
    (fullBoxActiveResidualPartial 0 5).derivative =
      fullBoxActiveResidualDerivativeEnclosure 0 5 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_zero_six_exact :
    (fullBoxActiveResidualPartial 0 6).derivative =
      fullBoxActiveResidualDerivativeEnclosure 0 6 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_zero_seven_exact :
    (fullBoxActiveResidualPartial 0 7).derivative =
      fullBoxActiveResidualDerivativeEnclosure 0 7 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_one_zero_exact :
    (fullBoxActiveResidualPartial 1 0).derivative =
      fullBoxActiveResidualDerivativeEnclosure 1 0 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_one_one_exact :
    (fullBoxActiveResidualPartial 1 1).derivative =
      fullBoxActiveResidualDerivativeEnclosure 1 1 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_one_two_exact :
    (fullBoxActiveResidualPartial 1 2).derivative =
      fullBoxActiveResidualDerivativeEnclosure 1 2 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_one_three_exact :
    (fullBoxActiveResidualPartial 1 3).derivative =
      fullBoxActiveResidualDerivativeEnclosure 1 3 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_one_four_exact :
    (fullBoxActiveResidualPartial 1 4).derivative =
      fullBoxActiveResidualDerivativeEnclosure 1 4 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_one_five_exact :
    (fullBoxActiveResidualPartial 1 5).derivative =
      fullBoxActiveResidualDerivativeEnclosure 1 5 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_one_six_exact :
    (fullBoxActiveResidualPartial 1 6).derivative =
      fullBoxActiveResidualDerivativeEnclosure 1 6 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_one_seven_exact :
    (fullBoxActiveResidualPartial 1 7).derivative =
      fullBoxActiveResidualDerivativeEnclosure 1 7 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_two_zero_exact :
    (fullBoxActiveResidualPartial 2 0).derivative =
      fullBoxActiveResidualDerivativeEnclosure 2 0 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_two_one_exact :
    (fullBoxActiveResidualPartial 2 1).derivative =
      fullBoxActiveResidualDerivativeEnclosure 2 1 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_two_two_exact :
    (fullBoxActiveResidualPartial 2 2).derivative =
      fullBoxActiveResidualDerivativeEnclosure 2 2 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_two_three_exact :
    (fullBoxActiveResidualPartial 2 3).derivative =
      fullBoxActiveResidualDerivativeEnclosure 2 3 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_two_four_exact :
    (fullBoxActiveResidualPartial 2 4).derivative =
      fullBoxActiveResidualDerivativeEnclosure 2 4 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_two_five_exact :
    (fullBoxActiveResidualPartial 2 5).derivative =
      fullBoxActiveResidualDerivativeEnclosure 2 5 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_two_six_exact :
    (fullBoxActiveResidualPartial 2 6).derivative =
      fullBoxActiveResidualDerivativeEnclosure 2 6 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_two_seven_exact :
    (fullBoxActiveResidualPartial 2 7).derivative =
      fullBoxActiveResidualDerivativeEnclosure 2 7 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_three_zero_exact :
    (fullBoxActiveResidualPartial 3 0).derivative =
      fullBoxActiveResidualDerivativeEnclosure 3 0 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_three_one_exact :
    (fullBoxActiveResidualPartial 3 1).derivative =
      fullBoxActiveResidualDerivativeEnclosure 3 1 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_three_two_exact :
    (fullBoxActiveResidualPartial 3 2).derivative =
      fullBoxActiveResidualDerivativeEnclosure 3 2 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_three_three_exact :
    (fullBoxActiveResidualPartial 3 3).derivative =
      fullBoxActiveResidualDerivativeEnclosure 3 3 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_three_four_exact :
    (fullBoxActiveResidualPartial 3 4).derivative =
      fullBoxActiveResidualDerivativeEnclosure 3 4 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_three_five_exact :
    (fullBoxActiveResidualPartial 3 5).derivative =
      fullBoxActiveResidualDerivativeEnclosure 3 5 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_three_six_exact :
    (fullBoxActiveResidualPartial 3 6).derivative =
      fullBoxActiveResidualDerivativeEnclosure 3 6 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_three_seven_exact :
    (fullBoxActiveResidualPartial 3 7).derivative =
      fullBoxActiveResidualDerivativeEnclosure 3 7 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_four_zero_exact :
    (fullBoxActiveResidualPartial 4 0).derivative =
      fullBoxActiveResidualDerivativeEnclosure 4 0 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_four_one_exact :
    (fullBoxActiveResidualPartial 4 1).derivative =
      fullBoxActiveResidualDerivativeEnclosure 4 1 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_four_two_exact :
    (fullBoxActiveResidualPartial 4 2).derivative =
      fullBoxActiveResidualDerivativeEnclosure 4 2 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_four_three_exact :
    (fullBoxActiveResidualPartial 4 3).derivative =
      fullBoxActiveResidualDerivativeEnclosure 4 3 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_four_four_exact :
    (fullBoxActiveResidualPartial 4 4).derivative =
      fullBoxActiveResidualDerivativeEnclosure 4 4 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_four_five_exact :
    (fullBoxActiveResidualPartial 4 5).derivative =
      fullBoxActiveResidualDerivativeEnclosure 4 5 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_four_six_exact :
    (fullBoxActiveResidualPartial 4 6).derivative =
      fullBoxActiveResidualDerivativeEnclosure 4 6 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_four_seven_exact :
    (fullBoxActiveResidualPartial 4 7).derivative =
      fullBoxActiveResidualDerivativeEnclosure 4 7 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_five_zero_exact :
    (fullBoxActiveResidualPartial 5 0).derivative =
      fullBoxActiveResidualDerivativeEnclosure 5 0 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_five_one_exact :
    (fullBoxActiveResidualPartial 5 1).derivative =
      fullBoxActiveResidualDerivativeEnclosure 5 1 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_five_two_exact :
    (fullBoxActiveResidualPartial 5 2).derivative =
      fullBoxActiveResidualDerivativeEnclosure 5 2 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_five_three_exact :
    (fullBoxActiveResidualPartial 5 3).derivative =
      fullBoxActiveResidualDerivativeEnclosure 5 3 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_five_four_exact :
    (fullBoxActiveResidualPartial 5 4).derivative =
      fullBoxActiveResidualDerivativeEnclosure 5 4 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_five_five_exact :
    (fullBoxActiveResidualPartial 5 5).derivative =
      fullBoxActiveResidualDerivativeEnclosure 5 5 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_five_six_exact :
    (fullBoxActiveResidualPartial 5 6).derivative =
      fullBoxActiveResidualDerivativeEnclosure 5 6 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_five_seven_exact :
    (fullBoxActiveResidualPartial 5 7).derivative =
      fullBoxActiveResidualDerivativeEnclosure 5 7 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_six_zero_exact :
    (fullBoxActiveResidualPartial 6 0).derivative =
      fullBoxActiveResidualDerivativeEnclosure 6 0 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_six_one_exact :
    (fullBoxActiveResidualPartial 6 1).derivative =
      fullBoxActiveResidualDerivativeEnclosure 6 1 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_six_two_exact :
    (fullBoxActiveResidualPartial 6 2).derivative =
      fullBoxActiveResidualDerivativeEnclosure 6 2 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_six_three_exact :
    (fullBoxActiveResidualPartial 6 3).derivative =
      fullBoxActiveResidualDerivativeEnclosure 6 3 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_six_four_exact :
    (fullBoxActiveResidualPartial 6 4).derivative =
      fullBoxActiveResidualDerivativeEnclosure 6 4 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_six_five_exact :
    (fullBoxActiveResidualPartial 6 5).derivative =
      fullBoxActiveResidualDerivativeEnclosure 6 5 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_six_six_exact :
    (fullBoxActiveResidualPartial 6 6).derivative =
      fullBoxActiveResidualDerivativeEnclosure 6 6 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_six_seven_exact :
    (fullBoxActiveResidualPartial 6 7).derivative =
      fullBoxActiveResidualDerivativeEnclosure 6 7 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_seven_zero_exact :
    (fullBoxActiveResidualPartial 7 0).derivative =
      fullBoxActiveResidualDerivativeEnclosure 7 0 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_seven_one_exact :
    (fullBoxActiveResidualPartial 7 1).derivative =
      fullBoxActiveResidualDerivativeEnclosure 7 1 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_seven_two_exact :
    (fullBoxActiveResidualPartial 7 2).derivative =
      fullBoxActiveResidualDerivativeEnclosure 7 2 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_seven_three_exact :
    (fullBoxActiveResidualPartial 7 3).derivative =
      fullBoxActiveResidualDerivativeEnclosure 7 3 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_seven_four_exact :
    (fullBoxActiveResidualPartial 7 4).derivative =
      fullBoxActiveResidualDerivativeEnclosure 7 4 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_seven_five_exact :
    (fullBoxActiveResidualPartial 7 5).derivative =
      fullBoxActiveResidualDerivativeEnclosure 7 5 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_seven_six_exact :
    (fullBoxActiveResidualPartial 7 6).derivative =
      fullBoxActiveResidualDerivativeEnclosure 7 6 := by
  verify_full_box_active_residual_derivative

@[simp] private theorem fullBoxActiveResidualDerivative_seven_seven_exact :
    (fullBoxActiveResidualPartial 7 7).derivative =
      fullBoxActiveResidualDerivativeEnclosure 7 7 := by
  verify_full_box_active_residual_derivative

@[simp] theorem fullBoxActiveResidualDerivative_exact
    (coordinate input : HazardCoordinate) :
    (fullBoxActiveResidualDual coordinate).derivative input =
      fullBoxActiveResidualDerivativeEnclosure coordinate input := by
  unfold fullBoxActiveResidualDual
  rw [← evalDyadicPartial_derivative_eq_evalSelectedDualDyadic
    hazardVariableIndex fullNormalizedCoordinateBox
    (activeResidualExpression coordinate) input]
  change (fullBoxActiveResidualPartial coordinate input).derivative = _
  fin_cases coordinate <;> fin_cases input <;> simp

/-- The normalized fixed-point displacement whose strict cube-face signs
produce a zero of the preconditioned active gap field. -/
def normalizedHazardDisplacementExpression (output : HazardCoordinate) :
    RationalPolynomial 68 :=
  polynomialSub (.var (hazardVariableIndex output))
    (polynomialMul (.constant (1 / hazardRadius))
      (faceFieldExpression output))

def centeredNormalizedHazardDisplacementEnclosure : HazardCoordinate →
    DyadicInterval neighborhoodPrecision :=
  ![⟨-9681321655510000000, 9681321997450000000⟩,
    ⟨-14443051586620000000, 14443051570900000000⟩,
    ⟨-14321689384670000000, 14321689056600000000⟩,
    ⟨-4592142689980000000, 4592142809220000000⟩,
    ⟨-6993702869850000000, 6993703066810000000⟩,
    ⟨-8630459980260000000, 8630459868320000000⟩,
    ⟨-15184686543510000000, 15184686543750000000⟩,
    ⟨-7406320908240000000, 7406320924360000000⟩]

def fullBoxNormalizedHazardDisplacementDerivativeEnclosure :
    HazardCoordinate → HazardCoordinate →
      DyadicInterval neighborhoodPrecision :=
  ![![⟨-23721780448384, 23721809551616⟩,
      ⟨-20834170000000, 20834150000000⟩,
      ⟨-40083970000000, 40083980000000⟩,
      ⟨-36841610000000, 36841640000000⟩,
      ⟨-39724140000000, 39724100000000⟩,
      ⟨-23629120000000, 23629140000000⟩,
      ⟨-29811780000000, 29811740000000⟩,
      ⟨-26126190000000, 26126160000000⟩],
    ![⟨-26641100000000, 26641110000000⟩,
      ⟨-38172400448384, 38172419551616⟩,
      ⟨-55305920000000, 55305880000000⟩,
      ⟨-49939740000000, 49939730000000⟩,
      ⟨-39481550000000, 39481540000000⟩,
      ⟨-48516330000000, 48516280000000⟩,
      ⟨-55542870000000, 55542870000000⟩,
      ⟨-39488260000000, 39488270000000⟩],
    ![⟨-31391830000000, 31391780000000⟩,
      ⟨-31750050000000, 31750070000000⟩,
      ⟨-55765880448384, 55765829551616⟩,
      ⟨-47331280000000, 47331220000000⟩,
      ⟨-49040080000000, 49040120000000⟩,
      ⟨-44190050000000, 44190030000000⟩,
      ⟨-54421770000000, 54421770000000⟩,
      ⟨-39347770000000, 39347790000000⟩],
    ![⟨-10466290000000, 10466270000000⟩,
      ⟨-8735320000000, 8735280000000⟩,
      ⟨-11299330000000, 11299330000000⟩,
      ⟨-21006270448384, 21006359551616⟩,
      ⟨-19193430000000, 19193510000000⟩,
      ⟨-11824870000000, 11824850000000⟩,
      ⟨-14928140000000, 14928110000000⟩,
      ⟨-12948330000000, 12948330000000⟩],
    ![⟨-13775620000000, 13775650000000⟩,
      ⟨-13254920000000, 13254930000000⟩,
      ⟨-30278140000000, 30278130000000⟩,
      ⟨-23819790000000, 23819770000000⟩,
      ⟨-26336510448384, 26336499551616⟩,
      ⟨-25207870000000, 25207880000000⟩,
      ⟨-25156490000000, 25156490000000⟩,
      ⟨-20620760000000, 20620740000000⟩],
    ![⟨-22015460000000, 22015460000000⟩,
      ⟨-19626310000000, 19626310000000⟩,
      ⟨-19295640000000, 19295650000000⟩,
      ⟨-22360910000000, 22360870000000⟩,
      ⟨-21523110000000, 21523030000000⟩,
      ⟨-34862040448384, 34862079551616⟩,
      ⟨-41622010000000, 41621970000000⟩,
      ⟨-21748590000000, 21748540000000⟩],
    ![⟨-31773750000000, 31773700000000⟩,
      ⟨-32954950000000, 32954980000000⟩,
      ⟨-59649970000000, 59649960000000⟩,
      ⟨-54067310000000, 54067260000000⟩,
      ⟨-56035320000000, 56035390000000⟩,
      ⟨-46228200000000, 46228220000000⟩,
      ⟨-56000490448384, 56000539551616⟩,
      ⟨-40289650000000, 40289650000000⟩],
    ![⟨-20848290000000, 20848320000000⟩,
      ⟨-14586400000000, 14586370000000⟩,
      ⟨-17214110000000, 17214130000000⟩,
      ⟨-22458800000000, 22458770000000⟩,
      ⟨-24464970000000, 24464940000000⟩,
      ⟨-31289720000000, 31289730000000⟩,
      ⟨-22241490000000, 22241500000000⟩,
      ⟨-26576460448384, 26576439551616⟩]]


end GameTheory.FourPlayerOverlappingPeriodThree

end
