import UniformEquilibrium.Quitting.Examples.BlockPair.K11ActiveEquationInterval
import UniformEquilibrium.Quitting.Examples.BlockPair.PredecessorCharts
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval Math.ProbabilityMassFunction StochasticGame

def reward (S : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  match decide (0 ∈ S.1), decide (1 ∈ S.1),
      decide (2 ∈ S.1), decide (3 ∈ S.1) with
  | false, false, false, false => fun _ ↦ 0
  | true, false, false, false => fun who ↦ (terminalTable 1 who : ℝ)
  | false, true, false, false => fun who ↦ (terminalTable 2 who : ℝ)
  | true, true, false, false => fun who ↦ (terminalTable 3 who : ℝ)
  | false, false, true, false => fun who ↦ (terminalTable 4 who : ℝ)
  | true, false, true, false => fun who ↦ (terminalTable 5 who : ℝ)
  | false, true, true, false => fun who ↦ (terminalTable 6 who : ℝ)
  | true, true, true, false => fun who ↦ (terminalTable 7 who : ℝ)
  | false, false, false, true => fun who ↦ (terminalTable 8 who : ℝ)
  | true, false, false, true => fun who ↦ (terminalTable 9 who : ℝ)
  | false, true, false, true => fun who ↦ (terminalTable 10 who : ℝ)
  | true, true, false, true => fun who ↦ (terminalTable 11 who : ℝ)
  | false, false, true, true => fun who ↦ (terminalTable 12 who : ℝ)
  | true, false, true, true => fun who ↦ (terminalTable 13 who : ℝ)
  | false, true, true, true => fun who ↦ (terminalTable 14 who : ℝ)
  | true, true, true, true => fun who ↦ (terminalTable 15 who : ℝ)

def hazard (x : HazardIndex → ℝ) (phase : Phase) (who : Player) : ℝ :=
  match LocalInterval.activeHazardIndex? phase who with
  | some index => x index
  | none => 0

theorem hazard_nonneg (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 ≤ x index)
    (phase : Phase) (who : Player) : 0 ≤ hazard x phase who := by
  unfold hazard
  cases LocalInterval.activeHazardIndex? phase who with
  | none => simp
  | some index => exact hx index

theorem hazard_le_one (x : HazardIndex → ℝ)
    (hx : ∀ index, x index ≤ 1)
    (phase : Phase) (who : Player) : hazard x phase who ≤ 1 := by
  unfold hazard
  cases LocalInterval.activeHazardIndex? phase who with
  | none => simp
  | some index => exact hx index

def rootOfHazard (h : Player → ℝ)
    (h0 : ∀ who, 0 ≤ h who) (h1 : ∀ who, h who ≤ 1) :
    Player → PMF Bool :=
  fun who ↦ quittingHazardCoin (h who) (h0 who) (h1 who)

@[simp] theorem rootOfHazard_true
    (h : Player → ℝ) (h0 : ∀ who, 0 ≤ h who)
    (h1 : ∀ who, h who ≤ 1) (who : Player) :
    ((rootOfHazard h h0 h1 who) true).toReal = h who := by
  simp [rootOfHazard]

@[simp] theorem rootOfHazard_false
    (h : Player → ℝ) (h0 : ∀ who, 0 ≤ h who)
    (h1 : ∀ who, h who ≤ 1) (who : Player) :
    ((rootOfHazard h h0 h1 who) false).toReal = 1 - h who := by
  simp [rootOfHazard]

def phaseRoot (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) : Player → PMF Bool :=
  rootOfHazard (hazard x phase)
    (hazard_nonneg x (fun index ↦ (hx index).1.le) phase)
    (hazard_le_one x (fun index ↦ (hx index).2.le) phase)

@[simp] theorem phaseRoot_true
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (who : Player) :
    ((phaseRoot x hx phase who) true).toReal = hazard x phase who := by
  apply rootOfHazard_true

@[simp] theorem phaseRoot_false
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (who : Player) :
    ((phaseRoot x hx phase who) false).toReal = 1 - hazard x phase who := by
  apply rootOfHazard_false

theorem evalReal_expressionSum {count : ℕ}
    (x : HazardIndex → ℝ) (term : Fin count → Expression) :
    RationalPolynomial.evalReal x (expressionSum term) =
      BlockPairCharts.realSum fun index ↦
        RationalPolynomial.evalReal x (term index) := by
  induction count with
  | zero => simp [expressionSum, BlockPairCharts.realSum,
      RationalPolynomial.evalReal]
  | succ count ih =>
      simp only [expressionSum, BlockPairCharts.realSum,
        RationalPolynomial.evalReal]
      rw [ih]

theorem evalReal_expressionProduct {count : ℕ}
    (x : HazardIndex → ℝ) (factor : Fin count → Expression) :
    RationalPolynomial.evalReal x (expressionProduct factor) =
      BlockPairCharts.realProduct fun index ↦
        RationalPolynomial.evalReal x (factor index) := by
  induction count with
  | zero => simp [expressionProduct, BlockPairCharts.realProduct,
      RationalPolynomial.evalReal]
  | succ count ih =>
      simp only [expressionProduct, BlockPairCharts.realProduct,
        RationalPolynomial.evalReal]
      rw [ih]

theorem evalReal_sub (x : HazardIndex → ℝ)
    (first second : Expression) :
    RationalPolynomial.evalReal x (first - second) =
      RationalPolynomial.evalReal x first -
        RationalPolynomial.evalReal x second := rfl

theorem evalReal_hazardExpression
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x (hazardExpression phase who) =
      hazard x phase who := by
  cases hindex : LocalInterval.activeHazardIndex? phase who with
  | none =>
      rw [LocalInterval.hazardExpression_eq_zero_of_activeHazardIndex?_eq_none
        hindex]
      simp [hazard, hindex, RationalPolynomial.evalReal]
  | some index =>
      have hslot : activeSlot index = (phase, who) :=
        (LocalInterval.activeHazardIndex?_eq_some_iff phase who index).mp hindex
      unfold hazard
      rw [hindex]
      calc
        RationalPolynomial.evalReal x (hazardExpression phase who) =
            RationalPolynomial.evalReal x
              (hazardExpression (activeSlot index).1
                (activeSlot index).2) := by rw [hslot]
        _ = x index := by
          rw [LocalInterval.hazardExpression_activeSlot]
          rfl

theorem evalReal_actionFactor
    (x : HazardIndex → ℝ) (phase : Phase) (mask : QuitterMask)
    (omitted : Option Player) (who : Player) :
    RationalPolynomial.evalReal x (actionFactor phase mask omitted who) =
      BlockPairCharts.actionFactor (hazard x phase) mask omitted who := by
  unfold actionFactor BlockPairCharts.actionFactor
  by_cases homitted : omitted = some who
  · rw [if_pos homitted, if_pos homitted]
    norm_num [RationalPolynomial.evalReal]
  · by_cases hmask : maskHasPlayer mask who = true
    · rw [if_neg homitted, if_neg homitted, if_pos hmask, if_pos hmask]
      exact evalReal_hazardExpression x phase who
    · rw [if_neg homitted, if_neg homitted, if_neg hmask, if_neg hmask,
        evalReal_sub]
      simpa only [RationalPolynomial.evalReal, Rat.cast_one] using
        congrArg (fun value : ℝ ↦ 1 - value)
          (evalReal_hazardExpression x phase who)

theorem evalReal_maskProbability
    (x : HazardIndex → ℝ) (phase : Phase) (mask : QuitterMask)
    (omitted : Option Player := none) :
    RationalPolynomial.evalReal x (maskProbability phase mask omitted) =
      BlockPairCharts.maskProbability (hazard x phase) mask omitted := by
  unfold maskProbability BlockPairCharts.maskProbability
  rw [evalReal_expressionProduct]
  apply congrArg BlockPairCharts.realProduct
  funext who
  exact evalReal_actionFactor x phase mask omitted who

theorem evalReal_phaseSurvival
    (x : HazardIndex → ℝ) (phase : Phase) :
    RationalPolynomial.evalReal x (phaseSurvival phase) =
      BlockPairCharts.maskProbability (hazard x phase) 0 :=
  evalReal_maskProbability x phase 0 none

theorem evalReal_opponentQuitValue
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x (opponentQuitValue phase who) =
      BlockPairCharts.opponentQuitValue (hazard x phase) who := by
  unfold opponentQuitValue BlockPairCharts.opponentQuitValue
  rw [evalReal_expressionSum]
  apply congrArg BlockPairCharts.realSum
  funext mask
  by_cases hmask : maskHasPlayer mask who = true
  · simp [hmask, RationalPolynomial.evalReal]
  · simp [hmask, RationalPolynomial.evalReal, evalReal_maskProbability]

theorem evalReal_opponentAbsorbingContribution
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x
        (opponentAbsorbingContribution phase who) =
      BlockPairCharts.opponentAbsorbingContribution (hazard x phase) who := by
  unfold opponentAbsorbingContribution
    BlockPairCharts.opponentAbsorbingContribution
  rw [evalReal_expressionSum]
  apply congrArg BlockPairCharts.realSum
  funext mask
  by_cases hzero : mask.val = 0
  · simp [hzero, RationalPolynomial.evalReal]
  · by_cases hmask : maskHasPlayer mask who = true
    · simp [hzero, hmask, RationalPolynomial.evalReal]
    · simp [hzero, hmask, RationalPolynomial.evalReal,
        evalReal_maskProbability]

theorem evalReal_opponentSurvival
    (x : HazardIndex → ℝ) (phase : Phase) (who : Player) :
    RationalPolynomial.evalReal x (opponentSurvival phase who) =
      BlockPairCharts.opponentSurvival (hazard x phase) who :=
  evalReal_maskProbability x phase 0 (some who)

def rho (x : HazardIndex → ℝ) : ℝ :=
  RationalPolynomial.evalReal x jointCycleSurvival

def phaseValue (x : HazardIndex → ℝ) (phase : Phase) : Payoff Player :=
  fun who ↦ RationalPolynomial.evalReal x
    (cyclicValueNumerator phase who) / (1 - rho x)

end GameTheory.BlockPairK11.ConditionalData
