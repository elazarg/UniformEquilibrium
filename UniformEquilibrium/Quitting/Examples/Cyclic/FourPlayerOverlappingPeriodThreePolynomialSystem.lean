import MathUE.Interval.PolynomialKrawczyk
import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeReward

/-!
# Polynomial system for the four-player overlapping period-three block
-/

noncomputable section

namespace GameTheory
namespace FourPlayerOverlappingPeriodThree

open Function Metric Set
open Math.Interval
open Math.Interval.RationalPolynomial
open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction
open scoped NNReal

/-- The exact hazard-box center. -/
def hazardCenter : HazardCoordinate → ℚ :=
  ![3551693780902477 / 10 ^ 16,
    2588856210079327 / 10 ^ 16,
    2302690784708344 / 10 ^ 16,
    952220237568218 / 10 ^ 16,
    2528341986655558 / 10 ^ 16,
    4405211001832288 / 10 ^ 16,
    2821769183533719 / 10 ^ 16,
    1721135892992767 / 10 ^ 16]

def hazardRadius : ℚ := 1 / 10 ^ 7
def rewardRadius : ℚ := 1 / 50000000

/-- The literal active-coordinate order
`(F_01,F_02,F_10,F_11,F_13,F_20,F_22,F_23)`. -/
def activeSlot : HazardCoordinate → Fin 3 × Player :=
  ![(0, 1), (0, 2), (1, 0), (1, 1),
    (1, 3), (2, 0), (2, 2), (2, 3)]

/-- The overlapping three-phase hazard word from normalized coordinates. -/
def hazardOfNormalized (z : HazardCoordinate → ℝ) : Fin 3 → Player → ℝ :=
  ![![0, hazardCenter 0 + hazardRadius * z 0,
      hazardCenter 1 + hazardRadius * z 1, 0],
    ![hazardCenter 2 + hazardRadius * z 2,
      hazardCenter 3 + hazardRadius * z 3, 0,
      hazardCenter 4 + hazardRadius * z 4],
    ![hazardCenter 5 + hazardRadius * z 5, 0,
      hazardCenter 6 + hazardRadius * z 6,
      hazardCenter 7 + hazardRadius * z 7]]

/-- The normalized hazard chart has exactly the displayed overlapping
three-block form. -/
theorem hazardOfNormalized_values (z : HazardCoordinate → ℝ) :
    hazardOfNormalized z =
      ![![0, hazardCenter 0 + hazardRadius * z 0,
          hazardCenter 1 + hazardRadius * z 1, 0],
        ![hazardCenter 2 + hazardRadius * z 2,
          hazardCenter 3 + hazardRadius * z 3, 0,
          hazardCenter 4 + hazardRadius * z 4],
        ![hazardCenter 5 + hazardRadius * z 5, 0,
          hazardCenter 6 + hazardRadius * z 6,
          hazardCenter 7 + hazardRadius * z 7]] := by
  rfl

/-- The explicit coordinate equivalence witnessing `8 + 15*4 = 68`. -/
def normalizedCoordinateEquiv :
    HazardCoordinate ⊕ (RewardRow × Player) ≃ NormalizedCoordinate :=
  (Equiv.sumCongr (Equiv.refl HazardCoordinate) finProdFinEquiv).trans
    finSumFinEquiv

/-- The normalized chart has eight hazard coordinates and sixty independent
reward coordinates, for sixty-eight variables in total. -/
theorem normalizedCoordinate_cardinalities :
    Fintype.card HazardCoordinate = 8 ∧
      Fintype.card (RewardRow × Player) = 60 ∧
      Fintype.card NormalizedCoordinate = 68 := by
  decide

def hazardVariableIndex (coordinate : HazardCoordinate) : NormalizedCoordinate :=
  ⟨coordinate, by omega⟩

def rewardVariableIndex (row : RewardRow) (who : Player) : NormalizedCoordinate :=
  ⟨8 + row.val * 4 + who.val, by omega⟩

theorem hazardVariableIndex_eq (coordinate : HazardCoordinate) :
    hazardVariableIndex coordinate =
      normalizedCoordinateEquiv (Sum.inl coordinate) := by
  fin_cases coordinate <;> decide

theorem rewardVariableIndex_eq (row : RewardRow) (who : Player) :
    rewardVariableIndex row who =
      normalizedCoordinateEquiv (Sum.inr (row, who)) := by
  fin_cases row <;> fin_cases who <;> decide

private abbrev Polynomial := RationalPolynomial 68

def polynomialNeg : Polynomial → Polynomial
  | .constant value => .constant (-value)
  | .neg expression => expression
  | expression => .neg expression

def polynomialAdd : Polynomial → Polynomial → Polynomial
  | .constant first, .constant second => .constant (first + second)
  | .constant first, second =>
      if first = 0 then second else .add (.constant first) second
  | first, .constant second =>
      if second = 0 then first else .add first (.constant second)
  | first, second => .add first second

def polynomialSub (first second : Polynomial) : Polynomial :=
  polynomialAdd first (polynomialNeg second)

def polynomialMul : Polynomial → Polynomial → Polynomial
  | .constant first, .constant second => .constant (first * second)
  | .constant first, second =>
      if first = 0 then 0 else if first = 1 then second
      else .mul (.constant first) second
  | first, .constant second =>
      if second = 0 then 0 else if second = 1 then first
      else .mul first (.constant second)
  | first, second => .mul first second

@[simp] theorem evalReal_polynomialNeg
    (point : NormalizedCoordinate → ℝ) (expression : Polynomial) :
    evalReal point (polynomialNeg expression) = -evalReal point expression := by
  cases expression <;>
    simp [polynomialNeg, Math.Interval.RationalPolynomial.evalReal]

@[simp] theorem evalReal_polynomialAdd
    (point : NormalizedCoordinate → ℝ) (first second : Polynomial) :
    evalReal point (polynomialAdd first second) =
      evalReal point first + evalReal point second := by
  cases first <;> cases second <;>
    simp only [polynomialAdd, evalReal]
  all_goals (repeat' first | split) <;>
    simp_all [Math.Interval.RationalPolynomial.evalReal]

@[simp] theorem evalReal_polynomialSub
    (point : NormalizedCoordinate → ℝ) (first second : Polynomial) :
    evalReal point (polynomialSub first second) =
      evalReal point first - evalReal point second := by
  simp [polynomialSub, sub_eq_add_neg]

@[simp] theorem evalReal_polynomialMul
    (point : NormalizedCoordinate → ℝ) (first second : Polynomial) :
    evalReal point (polynomialMul first second) =
      evalReal point first * evalReal point second := by
  cases first <;> cases second <;>
    simp only [polynomialMul, evalReal]
  all_goals (repeat' first | split) <;>
    simp_all [Math.Interval.RationalPolynomial.evalReal]

def polynomialSum {n : ℕ} (term : Fin n → Polynomial) : Polynomial :=
  (List.ofFn term).foldr polynomialAdd 0

def polynomialProduct {n : ℕ} (term : Fin n → Polynomial) : Polynomial :=
  (List.ofFn term).foldr polynomialMul 1

def hazardExpression (phase : Fin 3) (who : Player) : Polynomial :=
  ![![0, polynomialAdd (.constant (hazardCenter 0))
        (polynomialMul (.constant hazardRadius) (.var (hazardVariableIndex 0))),
      polynomialAdd (.constant (hazardCenter 1))
        (polynomialMul (.constant hazardRadius) (.var (hazardVariableIndex 1))), 0],
    ![polynomialAdd (.constant (hazardCenter 2))
        (polynomialMul (.constant hazardRadius) (.var (hazardVariableIndex 2))),
      polynomialAdd (.constant (hazardCenter 3))
        (polynomialMul (.constant hazardRadius) (.var (hazardVariableIndex 3))), 0,
      polynomialAdd (.constant (hazardCenter 4))
        (polynomialMul (.constant hazardRadius) (.var (hazardVariableIndex 4)))],
    ![polynomialAdd (.constant (hazardCenter 5))
        (polynomialMul (.constant hazardRadius) (.var (hazardVariableIndex 5))), 0,
      polynomialAdd (.constant (hazardCenter 6))
        (polynomialMul (.constant hazardRadius) (.var (hazardVariableIndex 6))),
      polynomialAdd (.constant (hazardCenter 7))
        (polynomialMul (.constant hazardRadius) (.var (hazardVariableIndex 7)))]] phase who

def rewardExpression (row : RewardRow) (who : Player) : Polynomial :=
  polynomialAdd (.constant (overlappingPeriodThreeRewardRow row who))
    (polynomialMul (.constant rewardRadius) (.var (rewardVariableIndex row who)))

def normalizedPoint (z : HazardCoordinate → ℝ)
    (r : RewardCoordinates) : NormalizedCoordinate → ℝ :=
  fun coordinate ↦
    match normalizedCoordinateEquiv.symm coordinate with
    | Sum.inl hazardCoordinate => z hazardCoordinate
    | Sum.inr (row, who) =>
        (r row who - overlappingPeriodThreeRewardRow row who) / rewardRadius

@[simp] theorem normalizedPoint_hazard
    (z : HazardCoordinate → ℝ) (r : RewardCoordinates)
    (coordinate : HazardCoordinate) :
    normalizedPoint z r
        (normalizedCoordinateEquiv (Sum.inl coordinate)) = z coordinate := by
  simp [normalizedPoint]

@[simp] theorem normalizedPoint_hazardVariableIndex
    (z : HazardCoordinate → ℝ) (r : RewardCoordinates)
    (coordinate : HazardCoordinate) :
    normalizedPoint z r (hazardVariableIndex coordinate) = z coordinate := by
  rw [hazardVariableIndex_eq]
  exact normalizedPoint_hazard z r coordinate

@[simp] theorem normalizedPoint_reward
    (z : HazardCoordinate → ℝ) (r : RewardCoordinates)
    (row : RewardRow) (who : Player) :
    normalizedPoint z r
        (normalizedCoordinateEquiv (Sum.inr (row, who))) =
      (r row who - overlappingPeriodThreeRewardRow row who) / rewardRadius := by
  simp [normalizedPoint]

@[simp] theorem normalizedPoint_rewardVariableIndex
    (z : HazardCoordinate → ℝ) (r : RewardCoordinates)
    (row : RewardRow) (who : Player) :
    normalizedPoint z r (rewardVariableIndex row who) =
      (r row who - overlappingPeriodThreeRewardRow row who) / rewardRadius := by
  rw [rewardVariableIndex_eq]
  exact normalizedPoint_reward z r row who

@[simp] theorem hazardExpression_evalReal
    (z : HazardCoordinate → ℝ) (r : RewardCoordinates)
    (phase : Fin 3) (who : Player) :
  evalReal (normalizedPoint z r) (hazardExpression phase who) =
      hazardOfNormalized z phase who := by
  fin_cases phase <;> fin_cases who <;>
    simp [hazardExpression, hazardOfNormalized,
      Math.Interval.RationalPolynomial.evalReal]

@[simp] theorem rewardExpression_evalReal
    (z : HazardCoordinate → ℝ) (r : RewardCoordinates)
    (row : RewardRow) (who : Player) :
    evalReal (normalizedPoint z r) (rewardExpression row who) = r row who := by
  simp only [rewardExpression, evalReal_polynomialAdd,
    evalReal_polynomialMul, evalReal_constant, evalReal_var]
  rw [normalizedPoint_rewardVariableIndex]
  have hradius : (rewardRadius : ℝ) ≠ 0 := by
    norm_num [rewardRadius]
  field_simp [hradius]
  ring

/-! ## Factored 68-variable cleared-gap expressions -/

def coalitionMassExpression (phase : Fin 3)
    (coalition : Finset Player) : Polynomial :=
  polynomialProduct fun who ↦ if who ∈ coalition then hazardExpression phase who
    else polynomialSub 1 (hazardExpression phase who)

def immediateExpression (phase : Fin 3) (who : Player) : Polynomial :=
  polynomialSum fun row ↦
    polynomialMul (coalitionMassExpression phase (coalitionOfRow row))
      (rewardExpression row who)

def pureQuitExpression (phase : Fin 3) (who : Player) : Polynomial :=
  polynomialSum fun row ↦ if who ∈ coalitionOfRow row then
    polynomialMul (polynomialProduct fun other ↦ if other = who then 1 else
      if other ∈ coalitionOfRow row then hazardExpression phase other
      else polynomialSub 1 (hazardExpression phase other))
      (rewardExpression row who)
    else 0

def excludedExpression (phase : Fin 3) (who : Player) : Polynomial :=
  polynomialSum fun row ↦ if who ∉ coalitionOfRow row then
    polynomialMul (polynomialProduct fun other ↦ if other = who then 1 else
      if other ∈ coalitionOfRow row then hazardExpression phase other
      else polynomialSub 1 (hazardExpression phase other))
      (rewardExpression row who)
    else 0

def opponentContinueExpression (phase : Fin 3) (who : Player) : Polynomial :=
  polynomialProduct fun other ↦
    if other = who then 1 else polynomialSub 1 (hazardExpression phase other)

def continueExpression (phase : Fin 3) : Polynomial :=
  polynomialProduct fun who ↦ polynomialSub 1 (hazardExpression phase who)

def denominatorExpression : Polynomial :=
  polynomialSub 1 (polynomialMul (polynomialMul (continueExpression 0)
    (continueExpression 1)) (continueExpression 2))

def windowExpression : Fin 3 → Player → Polynomial
  | 0, who => polynomialAdd (immediateExpression 0 who)
      (polynomialAdd (polynomialMul (continueExpression 0) (immediateExpression 1 who))
        (polynomialMul (polynomialMul (continueExpression 0) (continueExpression 1))
          (immediateExpression 2 who)))
  | 1, who => polynomialAdd (immediateExpression 1 who)
      (polynomialAdd (polynomialMul (continueExpression 1) (immediateExpression 2 who))
        (polynomialMul (polynomialMul (continueExpression 1) (continueExpression 2))
          (immediateExpression 0 who)))
  | 2, who => polynomialAdd (immediateExpression 2 who)
      (polynomialAdd (polynomialMul (continueExpression 2) (immediateExpression 0 who))
        (polynomialMul (polynomialMul (continueExpression 2) (continueExpression 0))
          (immediateExpression 1 who)))

def nextPhase : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

def clearedGapExpression (phase : Fin 3) (who : Player) : Polynomial :=
  polynomialSub
    (polynomialMul denominatorExpression
      (polynomialSub (pureQuitExpression phase who) (excludedExpression phase who)))
    (polynomialMul (opponentContinueExpression phase who)
      (windowExpression (nextPhase phase) who))

/-! The enclosure evaluator uses the literal nonzero row lists of the
three displayed supports.  This is the same factored evaluation graph with
identically zero summands omitted before interval evaluation. -/

def supportRows : Fin 3 → List RewardRow
  | 0 => [1, 3, 5]
  | 1 => [0, 1, 2, 7, 8, 9, 10]
  | 2 => [0, 3, 4, 7, 8, 11, 12]

def pureQuitRows : Fin 3 → Player → List RewardRow
  | 0, 0 => [0, 2, 4, 6]
  | 0, 1 => [1, 5]
  | 0, 2 => [3, 5]
  | 0, 3 => [7, 9, 11, 13]
  | 1, 0 => [0, 2, 8, 10]
  | 1, 1 => [1, 2, 9, 10]
  | 1, 2 => [3, 4, 5, 6, 11, 12, 13, 14]
  | 1, 3 => [7, 8, 9, 10]
  | 2, 0 => [0, 4, 8, 12]
  | 2, 1 => [1, 2, 5, 6, 9, 10, 13, 14]
  | 2, 2 => [3, 4, 11, 12]
  | 2, 3 => [7, 8, 11, 12]

def excludedRows : Fin 3 → Player → List RewardRow
  | 0, 0 => [1, 3, 5]
  | 0, 1 => [3]
  | 0, 2 => [1]
  | 0, 3 => [1, 3, 5]
  | 1, 0 => [1, 7, 9]
  | 1, 1 => [0, 7, 8]
  | 1, 2 => [0, 1, 2, 7, 8, 9, 10]
  | 1, 3 => [0, 1, 2]
  | 2, 0 => [3, 7, 11]
  | 2, 1 => [0, 3, 4, 7, 8, 11, 12]
  | 2, 2 => [0, 7, 8]
  | 2, 3 => [0, 3, 4]

def polynomialListSum (expressions : List Polynomial) : Polynomial :=
  expressions.foldr polynomialAdd 0

/-- Whether the row's nonempty coalition contains the given player.  This
bit-level spelling lets the fixed-support evaluation reduce row membership
before constructing its polynomial syntax tree. -/
def rowContains (row : RewardRow) (who : Player) : Bool :=
  if who = 0 then
    row = 0 || row = 2 || row = 4 || row = 6 || row = 8 || row = 10 ||
      row = 12 || row = 14
  else if who = 1 then
    row = 1 || row = 2 || row = 5 || row = 6 || row = 9 || row = 10 ||
      row = 13 || row = 14
  else if who = 2 then
    row = 3 || row = 4 || row = 5 || row = 6 || row = 11 || row = 12 ||
      row = 13 || row = 14
  else
    row = 7 || row = 8 || row = 9 || row = 10 || row = 11 || row = 12 ||
      row = 13 || row = 14

def rowHazardFactor
    (phase : Fin 3) (row : RewardRow) (who : Player) : Polynomial :=
  if rowContains row who then hazardExpression phase who
  else polynomialSub 1 (hazardExpression phase who)

/-- Literal four-player product mass for a fixed row. -/
def supportedCoalitionMassExpression
    (phase : Fin 3) (row : RewardRow) : Polynomial :=
  polynomialMul (rowHazardFactor phase row 0)
    (polynomialMul (rowHazardFactor phase row 1)
      (polynomialMul (rowHazardFactor phase row 2)
        (rowHazardFactor phase row 3)))

/-- Literal three-opponent product mass for a fixed row and deviator. -/
def supportedOpponentMassExpression
    (phase : Fin 3) (who : Player) (row : RewardRow) : Polynomial :=
  polynomialMul (if who = 0 then 1 else rowHazardFactor phase row 0)
    (polynomialMul (if who = 1 then 1 else rowHazardFactor phase row 1)
      (polynomialMul (if who = 2 then 1 else rowHazardFactor phase row 2)
        (if who = 3 then 1 else rowHazardFactor phase row 3)))

def supportedImmediateTerm
    (phase : Fin 3) (who : Player) (row : RewardRow) : Polynomial :=
  polynomialMul (supportedCoalitionMassExpression phase row)
    (rewardExpression row who)

def supportedEndpointTerm
    (phase : Fin 3) (who : Player) (row : RewardRow) : Polynomial :=
  polynomialMul (supportedOpponentMassExpression phase who row)
    (rewardExpression row who)

def supportedImmediateExpression
    (phase : Fin 3) (who : Player) : Polynomial :=
  polynomialListSum <| (supportRows phase).map fun row ↦
    supportedImmediateTerm phase who row

def supportedPureQuitExpression
    (phase : Fin 3) (who : Player) : Polynomial :=
  polynomialListSum <| (pureQuitRows phase who).map fun row ↦
    supportedEndpointTerm phase who row

def supportedExcludedExpression
    (phase : Fin 3) (who : Player) : Polynomial :=
  polynomialListSum <| (excludedRows phase who).map fun row ↦
    supportedEndpointTerm phase who row

def supportedWindowExpression : Fin 3 → Player → Polynomial
  | 0, who => polynomialAdd (supportedImmediateExpression 0 who)
      (polynomialAdd
        (polynomialMul (continueExpression 0)
          (supportedImmediateExpression 1 who))
        (polynomialMul
          (polynomialMul (continueExpression 0) (continueExpression 1))
          (supportedImmediateExpression 2 who)))
  | 1, who => polynomialAdd (supportedImmediateExpression 1 who)
      (polynomialAdd
        (polynomialMul (continueExpression 1)
          (supportedImmediateExpression 2 who))
        (polynomialMul
          (polynomialMul (continueExpression 1) (continueExpression 2))
          (supportedImmediateExpression 0 who)))
  | 2, who => polynomialAdd (supportedImmediateExpression 2 who)
      (polynomialAdd
        (polynomialMul (continueExpression 2)
          (supportedImmediateExpression 0 who))
        (polynomialMul
          (polynomialMul (continueExpression 2) (continueExpression 0))
          (supportedImmediateExpression 1 who)))

def supportedClearedGapExpression
    (phase : Fin 3) (who : Player) : Polynomial :=
  polynomialSub
    (polynomialMul denominatorExpression
      (polynomialSub (supportedPureQuitExpression phase who)
        (supportedExcludedExpression phase who)))
    (polynomialMul (opponentContinueExpression phase who)
      (supportedWindowExpression (nextPhase phase) who))

def activeResidualExpression (coordinate : HazardCoordinate) : Polynomial :=
  supportedClearedGapExpression
    (activeSlot coordinate).1 (activeSlot coordinate).2

/-- The exact rational preconditioner. -/
def preconditioner : HazardCoordinate → HazardCoordinate → ℚ :=
  ![![315143353187 / 10 ^ 12, 366974958817 / 10 ^ 12,
      -49078078206 / 10 ^ 12, 184811852330 / 10 ^ 12,
      232875167579 / 10 ^ 12, -254869288005 / 10 ^ 12,
      -25099394501 / 10 ^ 12, -1470845305 / 10 ^ 12],
    ![602147704263 / 10 ^ 12, 145073028566 / 10 ^ 12,
      -9776944759 / 10 ^ 12, -100954767104 / 10 ^ 12,
      648395477518 / 10 ^ 12, 294319240668 / 10 ^ 12,
      121157930961 / 10 ^ 12, -211997987049 / 10 ^ 12],
    ![-309126321348 / 10 ^ 12, 258278517492 / 10 ^ 12,
      -102280783703 / 10 ^ 12, 318835250165 / 10 ^ 12,
      477261949039 / 10 ^ 12, 398272112383 / 10 ^ 12,
      56650468854 / 10 ^ 12, -195187547313 / 10 ^ 12],
    ![8141174505 / 10 ^ 12, -8490457215 / 10 ^ 12,
      -341152554699 / 10 ^ 12, 89200975646 / 10 ^ 12,
      81054707800 / 10 ^ 12, 142638748426 / 10 ^ 12,
      6864760919 / 10 ^ 12, -901901991 / 10 ^ 12],
    ![68266279421 / 10 ^ 12, -92414191444 / 10 ^ 12,
      99419891079 / 10 ^ 12, 230779479327 / 10 ^ 12,
      330411042247 / 10 ^ 12, -49452845261 / 10 ^ 12,
      97457493728 / 10 ^ 12, -65051669603 / 10 ^ 12],
    ![-4718561732 / 10 ^ 12, 76693224365 / 10 ^ 12,
      -112489910972 / 10 ^ 12, 84672772712 / 10 ^ 12,
      -120106797257 / 10 ^ 12, 339836466727 / 10 ^ 12,
      67508004707 / 10 ^ 12, 469042378865 / 10 ^ 12],
    ![-344947719758 / 10 ^ 12, 240513202079 / 10 ^ 12,
      -265825502558 / 10 ^ 12, 367886940515 / 10 ^ 12,
      -509613507555 / 10 ^ 12, 329832798069 / 10 ^ 12,
      25940159701 / 10 ^ 12, 158832741351 / 10 ^ 12],
    ![-2160865764 / 10 ^ 12, 181328381440 / 10 ^ 12,
      -51514764712 / 10 ^ 12, 38775903777 / 10 ^ 12,
      -55002918462 / 10 ^ 12, 155628140095 / 10 ^ 12,
      -395004284185 / 10 ^ 12, 214797999024 / 10 ^ 12]]

def faceFieldExpression (output : HazardCoordinate) : Polynomial :=
  polynomialSum fun input ↦ polynomialMul (.constant (preconditioner output input))
    (activeResidualExpression input)

def unitInterval : RationalInterval := ⟨-1, 1⟩

def normalizedBox : NormalizedCoordinate → RationalInterval :=
  fun _ ↦ unitInterval

def lowerFaceBox (coordinate : HazardCoordinate) :
    NormalizedCoordinate → RationalInterval :=
  Function.update normalizedBox
    (hazardVariableIndex coordinate)
    (RationalInterval.point (-1))

def upperFaceBox (coordinate : HazardCoordinate) :
    NormalizedCoordinate → RationalInterval :=
  Function.update normalizedBox
    (hazardVariableIndex coordinate)
    (RationalInterval.point 1)

def evalValueInterval (box : NormalizedCoordinate → RationalInterval) :
    Polynomial → RationalInterval
  | .constant value => RationalInterval.point value
  | .var index => box index
  | .add first second =>
      (evalValueInterval box first).add (evalValueInterval box second)
  | .neg expression => (evalValueInterval box expression).neg
  | .mul first second =>
      (evalValueInterval box first).mul (evalValueInterval box second)

theorem evalValueInterval_valid
    {box : NormalizedCoordinate → RationalInterval}
    (hbox : ∀ coordinate, (box coordinate).Valid)
    (expression : Polynomial) :
    (evalValueInterval box expression).Valid := by
  induction expression with
  | constant value => exact RationalInterval.valid_point value
  | var index => exact hbox index
  | add first second hfirst hsecond => exact hfirst.add hsecond
  | neg expression hexpression => exact hexpression.neg
  | mul first second _ _ => exact RationalInterval.valid_mul _ _

end FourPlayerOverlappingPeriodThree
end GameTheory

end
