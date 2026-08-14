import UniformEquilibrium.Quitting.Examples.BlockPair.K11ActiveEquationInterval
import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Quitting.Examples.BlockPair.PredecessorCharts
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

/-!
# Conditional strategic compiler for the K11 system

This ignored prototype deliberately separates the numerical root certificate
from its game-theoretic consumer.  It constructs the concrete K11 phase roots,
cyclic values, finite block, and periodic profile from a real hazard vector.
Two semantic translation hypotheses are kept explicit below: the Bellman
recurrence for the eliminated cyclic numerators and the cleared-equation bridge
from the public polynomial system to the quitting-game endpoint difference.
-/

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalStrategicCompiler

open Math.Interval Math.Probability Math.PMFProduct
  Math.ProbabilityMassFunction StochasticGame

/-- The terminal table as a quitting-game reward.  Bit `i` records membership
of player `i` in the quitting coalition, matching `terminalTable`. -/
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

/-- Real hazard at a phase/player slot.  Inactive slots are identically zero. -/
def hazard (x : HazardIndex → ℝ) (phase : Phase) (who : Player) : ℝ :=
  match LocalInterval.activeHazardIndex? phase who with
  | some index => x index
  | none => 0

theorem hazard_nonneg (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (who : Player) :
    0 ≤ hazard x phase who := by
  unfold hazard
  cases hindex : LocalInterval.activeHazardIndex? phase who with
  | none => simp
  | some index => simpa using (hx index).1.le

theorem hazard_le_one (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (who : Player) :
    hazard x phase who ≤ 1 := by
  unfold hazard
  cases hindex : LocalInterval.activeHazardIndex? phase who with
  | none => simp
  | some index => simpa using (hx index).2.le

/-- The concrete phase root: active hazards are the supplied coordinates and
inactive hazards are zero. -/
def phaseRoot (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) : Player → PMF Bool :=
  fun who ↦ quittingHazardCoin (hazard x phase who)
    (hazard_nonneg x hx phase who) (hazard_le_one x hx phase who)

@[simp] theorem phaseRoot_quitProbability
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (who : Player) :
    ((phaseRoot x hx phase who) true).toReal = hazard x phase who := by
  simp [phaseRoot]

@[simp] theorem phaseRoot_continueProbability
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (who : Player) :
    ((phaseRoot x hx phase who) false).toReal = 1 - hazard x phase who := by
  simp [phaseRoot]

theorem evalReal_expressionSum {count : ℕ}
    (x : HazardIndex → ℝ) (term : Fin count → Expression) :
    RationalPolynomial.evalReal x (expressionSum term) =
      BlockPairCharts.realSum fun index ↦
        RationalPolynomial.evalReal x (term index) := by
  induction count with
  | zero => simp [expressionSum, BlockPairCharts.realSum,
      RationalPolynomial.evalReal]
  | succ count inductionHypothesis =>
      simp only [expressionSum, BlockPairCharts.realSum,
        RationalPolynomial.evalReal]
      rw [inductionHypothesis]

theorem evalReal_expressionProduct {count : ℕ}
    (x : HazardIndex → ℝ) (factor : Fin count → Expression) :
    RationalPolynomial.evalReal x (expressionProduct factor) =
      BlockPairCharts.realProduct fun index ↦
        RationalPolynomial.evalReal x (factor index) := by
  induction count with
  | zero => simp [expressionProduct, BlockPairCharts.realProduct,
      RationalPolynomial.evalReal]
  | succ count inductionHypothesis =>
      simp only [expressionProduct, BlockPairCharts.realProduct,
        RationalPolynomial.evalReal]
      rw [inductionHypothesis]

theorem evalReal_sub (x : HazardIndex → ℝ)
    (first second : Expression) :
    RationalPolynomial.evalReal x (first - second) =
      RationalPolynomial.evalReal x first -
        RationalPolynomial.evalReal x second := by
  rfl

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
    · rw [if_neg homitted, if_neg homitted,
        if_pos hmask, if_pos hmask]
      exact evalReal_hazardExpression x phase who
    · rw [if_neg homitted, if_neg homitted,
        if_neg hmask, if_neg hmask]
      rw [evalReal_sub]
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
      BlockPairCharts.maskProbability (hazard x phase) 0 := by
  exact evalReal_maskProbability x phase 0 none

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
  · simp [hmask, RationalPolynomial.evalReal,
      evalReal_maskProbability]

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
      BlockPairCharts.opponentSurvival (hazard x phase) who := by
  exact evalReal_maskProbability x phase 0 (some who)

/-- Fubini expansion specialized to four Boolean product marginals. -/
theorem expect_quittingHazardCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quittingHazardCoin p hp0 hp1) f =
      (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

private theorem rootQuitPayoff_zero_eq_chart
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (phaseRoot x hx phase) 0 =
      BlockPairCharts.opponentQuitValue (hazard x phase) 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [phaseRoot, expect_quittingHazardCoin, reward,
    quittingRootPayoff, quittingQuitters, BlockPairCharts.opponentQuitValue,
    BlockPairCharts.realSum, BlockPairCharts.maskProbability,
    BlockPairCharts.realProduct, BlockPairCharts.actionFactor, hazard,
    BlockPairCharts.terminalRewardNat,
    LocalInterval.activeHazardIndex?, LocalInterval.activePlayersBefore,
    maskHasPlayer, maskWithPlayer]
  ring

private theorem rootQuitPayoff_one_eq_chart
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (phaseRoot x hx phase) 1 =
      BlockPairCharts.opponentQuitValue (hazard x phase) 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [phaseRoot, expect_quittingHazardCoin, reward,
    quittingRootPayoff, quittingQuitters, BlockPairCharts.opponentQuitValue,
    BlockPairCharts.realSum, BlockPairCharts.maskProbability,
    BlockPairCharts.realProduct, BlockPairCharts.actionFactor, hazard,
    BlockPairCharts.terminalRewardNat,
    LocalInterval.activeHazardIndex?, LocalInterval.activePlayersBefore,
    maskHasPlayer, maskWithPlayer]
  ring

private theorem rootQuitPayoff_two_eq_chart
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (phaseRoot x hx phase) 2 =
      BlockPairCharts.opponentQuitValue (hazard x phase) 2 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [phaseRoot, expect_quittingHazardCoin, reward,
    quittingRootPayoff, quittingQuitters, BlockPairCharts.opponentQuitValue,
    BlockPairCharts.realSum, BlockPairCharts.maskProbability,
    BlockPairCharts.realProduct, BlockPairCharts.actionFactor, hazard,
    BlockPairCharts.terminalRewardNat,
    LocalInterval.activeHazardIndex?, LocalInterval.activePlayersBefore,
    maskHasPlayer, maskWithPlayer]
  ring

private theorem rootQuitPayoff_three_eq_chart
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (phaseRoot x hx phase) 3 =
      BlockPairCharts.opponentQuitValue (hazard x phase) 3 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [phaseRoot, expect_quittingHazardCoin, reward,
    quittingRootPayoff, quittingQuitters, BlockPairCharts.opponentQuitValue,
    BlockPairCharts.realSum, BlockPairCharts.maskProbability,
    BlockPairCharts.realProduct, BlockPairCharts.actionFactor, hazard,
    BlockPairCharts.terminalRewardNat,
    LocalInterval.activeHazardIndex?, LocalInterval.activePlayersBefore,
    maskHasPlayer, maskWithPlayer]
  ring

/-- The quitting-game pure-Quit endpoint is the public terminal-table
opponent summary. -/
theorem rootQuitPayoff_eq_chart
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (who : Player) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (phaseRoot x hx phase) who =
      BlockPairCharts.opponentQuitValue (hazard x phase) who := by
  fin_cases who
  · exact rootQuitPayoff_zero_eq_chart x hx phase tail
  · exact rootQuitPayoff_one_eq_chart x hx phase tail
  · exact rootQuitPayoff_two_eq_chart x hx phase tail
  · exact rootQuitPayoff_three_eq_chart x hx phase tail

/-- Joint survival in the public eliminated polynomial system. -/
def rho (x : HazardIndex → ℝ) : ℝ :=
  RationalPolynomial.evalReal x jointCycleSurvival

/-- Cyclic continuation value obtained by dividing the public numerator by
the common positive denominator. -/
def phaseValue (x : HazardIndex → ℝ) (phase : Phase) : Payoff Player :=
  fun who ↦
    RationalPolynomial.evalReal x (cyclicValueNumerator phase who) /
      (1 - rho x)

/-- Simplex coordinates of the concrete product root. -/
def simplexRoot (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) : QuittingRootSimplex Player :=
  fun who ↦ stdSimplexEquiv (phaseRoot x hx phase who)

/-- The phase/player point used in the exact Nash--Bellman block. -/
def phasePoint (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) : QuittingNashBellmanPoint Player :=
  (phaseValue x phase, simplexRoot x hx phase)

/-- Interpret the twelve displayed path nodes cyclically as phases
`0,...,10,0`. -/
def pathPhase (time : Fin 12) : Phase := Fin.ofNat 11 time.val

def block (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1) :
    QuittingFiniteNashBellmanPath Player 11 :=
  fun time ↦ phasePoint x hx (pathPhase time)

@[simp] theorem pathPhase_zero : pathPhase 0 = 0 := rfl

@[simp] theorem pathPhase_last : pathPhase (Fin.last 11) = 0 := rfl

theorem pathPhase_succ (time : Fin 11) :
    pathPhase (Fin.succ time) = nextPhase (pathPhase (Fin.castSucc time)) := by
  fin_cases time <;> rfl

@[simp] theorem pathPhase_castSucc (phase : Phase) :
    pathPhase (Fin.castSucc phase) = phase := by
  fin_cases phase <;> rfl

@[simp] theorem rootOfSimplex_phasePoint
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) :
    quittingRootOfSimplex (phasePoint x hx phase).2 = phaseRoot x hx phase :=
  by
    funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
      (phaseRoot x hx phase who)

/-- Polynomial zeros and the cleared semantic equation make every active
phase/player endpoint difference vanish. -/
theorem active_endpointDifference_eq_zero
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1)
    (hequation : ∀ equation,
      RationalPolynomial.evalReal x (activeEquation equation) = 0)
    (hcleared : ∀ phase who,
      RationalPolynomial.evalReal x (activeEquationAt phase who) =
        (1 - rho x) * quittingRootEndpointDifference reward
          (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who)
    {phase : Phase} {who : Player} {index : HazardIndex}
    (hindex : LocalInterval.activeHazardIndex? phase who = some index) :
    quittingRootEndpointDifference reward
        (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who = 0 := by
  have hslot : activeSlot index = (phase, who) :=
    (LocalInterval.activeHazardIndex?_eq_some_iff phase who index).mp hindex
  have heval : RationalPolynomial.evalReal x
      (activeEquationAt phase who) = 0 := by
    have h := hequation index
    unfold activeEquation at h
    simpa only [hslot] using h
  rw [hcleared phase who] at heval
  have hdenominator : 1 - rho x ≠ 0 := by linarith
  exact (mul_eq_zero.mp heval).resolve_left hdenominator

/-- The exact endpoint-Nash certificate.  Active coordinates use the 31
polynomial equations; inactive coordinates use the supplied endpoint signs. -/
theorem phaseRoot_isZeroEndpointNash
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1)
    (hequation : ∀ equation,
      RationalPolynomial.evalReal x (activeEquation equation) = 0)
    (hcleared : ∀ phase who,
      RationalPolynomial.evalReal x (activeEquationAt phase who) =
        (1 - rho x) * quittingRootEndpointDifference reward
          (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who)
    (hinactive : ∀ phase who,
      LocalInterval.activeHazardIndex? phase who = none →
        quittingRootEndpointDifference reward
          (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who ≤ 0)
    (phase : Phase) :
    IsεQuittingRootEndpointNash reward (phaseValue x (nextPhase phase)) 0
      (phaseRoot x hx phase) := by
  intro who
  cases hindex : LocalInterval.activeHazardIndex? phase who with
  | none =>
      have hdiff := hinactive phase who hindex
      simp [phaseRoot_continueProbability, phaseRoot_quitProbability,
        hazard, hindex, hdiff]
  | some index =>
      have hdiff := active_endpointDifference_eq_zero x hx hrho hequation
        hcleared hindex
      simp [hdiff]

/-- Conditional construction of the concrete absorbing exact K11 cyclic
continuation block.  The two semantic bridges are kept visible as hypotheses
until the table-to-game and numerator-recurrence adapters are proved. -/
theorem block_isQuittingCyclicContinuationBlock
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1)
    (hequation : ∀ equation,
      RationalPolynomial.evalReal x (activeEquation equation) = 0)
    (hcleared : ∀ phase who,
      RationalPolynomial.evalReal x (activeEquationAt phase who) =
        (1 - rho x) * quittingRootEndpointDifference reward
          (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who)
    (hinactive : ∀ phase who,
      LocalInterval.activeHazardIndex? phase who = none →
        quittingRootEndpointDifference reward
          (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who ≤ 0)
    (hrecurrence : ∀ phase,
      phaseValue x phase = quittingRootSuccessorPayoff reward
        (phaseValue x (nextPhase phase)) (phaseRoot x hx phase))
    (hbound : ∀ phase who,
      |phaseValue x phase who| ≤ quittingRewardBound reward)
    (habsorb : ∃ phase,
      0 < quittingRootAbsorptionMass (phaseRoot x hx phase)) :
    IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
      (block x hx) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro time
    change phaseValue x (pathPhase time) ∈
      Set.Icc (fun _ : Player ↦ -(quittingRewardBound reward))
        (fun _ ↦ quittingRewardBound reward)
    exact ⟨fun who ↦ (abs_le.mp (hbound _ who)).1,
      fun who ↦ (abs_le.mp (hbound _ who)).2⟩
  · rfl
  · intro time
    have hphase := pathPhase_succ time
    constructor
    · change phaseValue x (pathPhase (Fin.castSucc time)) =
        quittingRootSuccessorPayoff reward
          (phaseValue x (pathPhase (Fin.succ time)))
          (quittingRootOfSimplex
            (phasePoint x hx (pathPhase (Fin.castSucc time))).2)
      rw [rootOfSimplex_phasePoint, hphase]
      exact hrecurrence _
    · change IsεQuittingRootEndpointNash reward
        (phaseValue x (pathPhase (Fin.succ time))) 0
        (quittingRootOfSimplex
          (phasePoint x hx (pathPhase (Fin.castSucc time))).2)
      rw [rootOfSimplex_phasePoint, hphase]
      exact phaseRoot_isZeroEndpointNash x hx hrho hequation hcleared
        hinactive _
  · rfl
  · obtain ⟨phase, hphase⟩ := habsorb
    refine ⟨phase, ?_⟩
    change 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex
        (phasePoint x hx (pathPhase (Fin.castSucc phase))).2)
    rw [rootOfSimplex_phasePoint]
    simpa using hphase

@[simp] theorem blockCycle_eq_phaseRoot
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (stage : Fin 11) :
    quittingCyclicContinuationBlockCycle 10 (block x hx) stage =
      phaseRoot x hx stage := by
  change quittingRootOfSimplex
    (phasePoint x hx (pathPhase (Fin.castSucc stage))).2 = _
  rw [rootOfSimplex_phasePoint]
  rw [pathPhase_castSucc]

/-- The periodic behavioral profile generated by the conditional block. -/
def profile (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingCyclicContinuationBlockProfile reward 10 (block x hx) 0

/-- Once the block and the standard cycle-admissibility predicate are
available, the existing arbitrary-deviation compiler gives exact terminal
Nash without any K11-specific deviation argument. -/
theorem profile_isExactTerminalNash
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hblock : IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
      (block x hx))
    (hadmissible : IsQuittingCycleAdmissible reward (phaseRoot x hx)) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 (profile x hx) := by
  have hcycle : quittingCyclicContinuationBlockCycle 10 (block x hx) =
      phaseRoot x hx := funext (blockCycle_eq_phaseRoot x hx)
  exact isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile reward
    (phaseValue x 0) 10 (block x hx) hblock (hcycle.symm ▸ hadmissible) 0

theorem profile_terminalPayoff
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hblock : IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
      (block x hx)) :
    quittingTerminalPayoff reward (profile x hx) = phaseValue x 0 :=
  quittingTerminalPayoff_quittingCyclicContinuationBlockProfile reward
    (phaseValue x 0) 10 (block x hx) hblock

/-- Conditional uniform-equilibrium payoff, with no claim that a numerical
K11 root exists until its interval certificate is completed. -/
theorem isUniformEquilibriumPayoff_phaseZero
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hblock : IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
      (block x hx))
    (hadmissible : IsQuittingCycleAdmissible reward (phaseRoot x hx)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (phaseValue x 0) := by
  have hnash := profile_isExactTerminalNash x hx hblock hadmissible
  have huniform := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward (profile x hx) hnash
  rwa [profile_terminalPayoff x hx hblock] at huniform

/-- End-to-end conditional compiler.  The conclusion packages the concrete
cyclic block, exact terminal Nash profile, and its named uniform-equilibrium
payoff. -/
theorem compile
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1)
    (hequation : ∀ equation,
      RationalPolynomial.evalReal x (activeEquation equation) = 0)
    (hcleared : ∀ phase who,
      RationalPolynomial.evalReal x (activeEquationAt phase who) =
        (1 - rho x) * quittingRootEndpointDifference reward
          (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who)
    (hinactive : ∀ phase who,
      LocalInterval.activeHazardIndex? phase who = none →
        quittingRootEndpointDifference reward
          (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) who ≤ 0)
    (hrecurrence : ∀ phase,
      phaseValue x phase = quittingRootSuccessorPayoff reward
        (phaseValue x (nextPhase phase)) (phaseRoot x hx phase))
    (hbound : ∀ phase who,
      |phaseValue x phase who| ≤ quittingRewardBound reward)
    (habsorb : ∃ phase,
      0 < quittingRootAbsorptionMass (phaseRoot x hx phase))
    (hadmissible : IsQuittingCycleAdmissible reward (phaseRoot x hx)) :
    IsQuittingCyclicContinuationBlock reward (phaseValue x 0) 11
        (block x hx) ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0 (profile x hx) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (phaseValue x 0) := by
  have hblock := block_isQuittingCyclicContinuationBlock x hx hrho
    hequation hcleared hinactive hrecurrence hbound habsorb
  exact ⟨hblock, profile_isExactTerminalNash x hx hblock hadmissible,
    isUniformEquilibriumPayoff_phaseZero x hx hblock hadmissible⟩

end GameTheory.BlockPairK11.ConditionalStrategicCompiler
