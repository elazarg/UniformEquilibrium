import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseAlgebraic
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseStrategic
import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap

/-! # Algebraic original-game stationary equilibrium from guarded crossed escape

The algebraic crossed witness is decoded without changing its hazards. Source
guards supply the original-game endpoint conditions. The actual terminal value
is algebraic by the finite coalition formulas and the absorbing payoff quotient.
The full behavioral cap and the uniform payoff refer to this same root and value.
No executable algebraic isolation or rational accuracy-only search is asserted.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming MathUE.RealQuantifierElimination

variable {n : ℕ}

/-- Rational rewards and algebraic hazards give algebraic actual stationary
terminal values whenever the stationary root absorbs. -/
theorem isAlgebraic_quittingTerminalPayoff_stationary_of_algebraic_hazards
    (reward : RationalQuittingReward n) (root : Fin n → PMF Bool)
    (halgebraic : ∀ who, IsAlgebraic ℚ (hazardOfRoot root who))
    (habsorbs : quittingStationaryContinueMass root < 1) (who : Fin n) :
    IsAlgebraic ℚ (quittingTerminalPayoff (rationalQuittingRewardToReal reward)
      (quittingStationaryProfile (rationalQuittingRewardToReal reward) root) who) := by
  have hcontinue (player : Fin n) :
      (root player false).toReal = 1 - hazardOfRoot root player := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root player
    change (root player false).toReal = 1 - (root player true).toReal
    linarith
  have hsigma : IsAlgebraic ℚ
      (sigmaValue (weightOfReward (rationalQuittingRewardToReal reward))
        (hazardOfRoot root) who) := by
    simpa only [evalReal_rationalQuittingSigmaExpression] using
      RingExpression.isAlgebraic_evalReal (hazardOfRoot root) halgebraic
        (rationalQuittingSigmaExpression reward who)
  have hexcluded : IsAlgebraic ℚ
      (excludedValue (weightOfReward (rationalQuittingRewardToReal reward))
        (hazardOfRoot root) who) := by
    simpa only [evalReal_rationalQuittingExcludedExpression] using
      RingExpression.isAlgebraic_evalReal (hazardOfRoot root) halgebraic
        (rationalQuittingExcludedExpression reward who)
  have hmassEval :
      (continueProductExpressionWithTerms RingExpression.var
        (Finset.univ : Finset (Fin n))).evalReal (hazardOfRoot root) =
          quittingStationaryContinueMass root := by
    rw [evalReal_continueProductExpressionWithTerms,
      quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_congr rfl
    intro player _
    exact (hcontinue player).symm
  have hmass : IsAlgebraic ℚ (quittingStationaryContinueMass root) := by
    rw [← hmassEval]
    exact RingExpression.isAlgebraic_evalReal (hazardOfRoot root) halgebraic _
  have hnumerator : IsAlgebraic ℚ
      (quittingRootAbsorbingContribution (rationalQuittingRewardToReal reward) root who) := by
    rw [quittingRootAbsorbingContribution_eq_hazard_mixture]
    exact ((halgebraic who).mul hsigma).add
      ((isAlgebraic_one.sub (halgebraic who)).mul hexcluded)
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    (rationalQuittingRewardToReal reward) root who habsorbs, div_eq_mul_inv]
  exact hnumerator.mul (isAlgebraic_one.sub hmass).inv

/-- The packet's rational source data produce one original-game stationary
equilibrium with algebraic hazards and actual value. Its complete behavioral
caps equal that same value, which is a uniform-equilibrium payoff. -/
theorem exists_isAlgebraic_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards
    (reward : RationalQuittingReward n) (first second : Fin n) (hdistinct : first ≠ second)
    (height : ℚ) (hheight : 0 < (height : ℝ)) (hheightOne : (height : ℝ) ≤ 1)
    (hguard : QuittingCrossedSourceGuards
      (rationalQuittingRewardToReal reward) first second (height : ℝ))
    (hreciprocalFirst : 0 < QuittingLCPClassification.quittingSingletonMatrix
      (rationalQuittingRewardToReal reward) first second)
    (hreciprocalSecond : 0 < QuittingLCPClassification.quittingSingletonMatrix
      (rationalQuittingRewardToReal reward) second first)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix
      (rationalQuittingRewardToReal reward) first second))
    (hdegree : r0Degree (quittingCrossedSingletonMatrix
      (rationalQuittingRewardToReal reward) first second) hR0 ≠ 1) :
    ∃ root : Fin n → PMF Bool, ∃ value : Payoff (Fin n),
      (∀ who, IsAlgebraic ℚ (hazardOfRoot root who)) ∧
      (∀ who, IsAlgebraic ℚ (value who)) ∧
      0 < hazardOfRoot root first ∧ hazardOfRoot root first < (height : ℝ) ∧
      0 < hazardOfRoot root second ∧ hazardOfRoot root second < (height : ℝ) ∧
      (∃ outsider, outsider ≠ first ∧ outsider ≠ second ∧
        0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff (rationalQuittingRewardToReal reward)
        (quittingStationaryProfile (rationalQuittingRewardToReal reward) root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (∀ who, quittingStationaryFullRateUnilateralCap
        (rationalQuittingRewardToReal reward) root who = value who) ∧
      (∀ who, quittingContinuationBestResponseValue (rationalQuittingRewardToReal reward)
        (quittingStationaryProfile (rationalQuittingRewardToReal reward) root) who = value who) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) 0
        (quittingStationaryProfile (rationalQuittingRewardToReal reward) root) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsUniformEquilibriumPayoff
        none value := by
  let realReward := rationalQuittingRewardToReal reward
  have hfullGuard := (quittingCrossedSourceGuards_iff_fullBoxGuards
    realReward first second hdistinct (height : ℝ) hheight).mp hguard
  obtain ⟨hazard, halgebraic, hnonzero, hcrossed⟩ :=
    exists_isAlgebraic_nonzero_quittingCrossedClippedMap_fixedPoint
      reward first second height hheight hheightOne hR0 hdegree
  have hout := quittingCrossedClippedMap_fixed_outsiderPositive_of_nonzero
    realReward first second hdistinct (height : ℝ) hheight hfullGuard
      hreciprocalFirst hreciprocalSecond hazard hnonzero hcrossed
  have hinterior := quittingCrossedClippedMap_fixed_selected_interior_of_outsider
    realReward first second (height : ℝ) hheight hfullGuard hazard hcrossed hout
  have hbox := quittingCrossedClippedMap_fixed_mem_box
    realReward first second (height : ℝ) hheight.le hazard hcrossed
  have hzero (who : Fin n) : 0 ≤ hazard who := (hbox who).1
  have hone (who : Fin n) : hazard who ≤ 1 := by
    have hceiling : quittingCrossedCeiling first second (height : ℝ) who ≤ 1 := by
      unfold quittingCrossedCeiling
      split_ifs <;> linarith
    exact (hbox who).2.trans hceiling
  have horiginal := quittingDiscountedClippedMap_fixed_of_crossed_fixed_guards
    realReward first second (height : ℝ) hheight hheightOne hfullGuard hazard hcrossed hout
  obtain ⟨root, value, hrootHazard, habsorption, hactual, hbellman, hendpoint⟩ :=
    stationaryEndpointCertificate_of_nonzero_clippedMap_fixed
      realReward hazard hzero hone hnonzero horiginal
  have hrootAlgebraic (who : Fin n) : IsAlgebraic ℚ (hazardOfRoot root who) := by
    rw [hrootHazard]
    exact halgebraic who
  have hfirst : 0 < (root first true).toReal := by
    change 0 < hazardOfRoot root first
    rw [hrootHazard]
    exact hinterior.1
  have hsecond : 0 < (root second true).toReal := by
    change 0 < hazardOfRoot root second
    rw [hrootHazard]
    exact hinterior.2.2.1
  have hcontracts (who : Fin n) :
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    by_cases hwho : first = who
    · subst who
      exact quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
        root hdistinct.symm hsecond
    · exact quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
        root hwho hfirst
  have habsorbs : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hnash := isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    realReward root value habsorbs hbellman hendpoint hcontracts
  have huniform := isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    realReward root value habsorbs hbellman hendpoint hcontracts
  have hvalueAlgebraic (who : Fin n) : IsAlgebraic ℚ (value who) := by
    rw [hactual]
    exact isAlgebraic_quittingTerminalPayoff_stationary_of_algebraic_hazards
      reward root hrootAlgebraic habsorbs who
  have hcaps (who : Fin n) :
      quittingStationaryFullRateUnilateralCap realReward root who = value who := by
    have hupper := (isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le
      realReward root 0).mp hnash who
    have hlower := quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap
      realReward root who ((quittingStationaryProfile realReward root) who)
    rw [Function.update_eq_self] at hlower
    rw [hactual]
    exact le_antisymm (by simpa only [add_zero] using hupper) hlower
  have hfullcaps (who : Fin n) : quittingContinuationBestResponseValue realReward
      (quittingStationaryProfile realReward root) who = value who := by
    rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap, hcaps]
  refine ⟨root, value, hrootAlgebraic, hvalueAlgebraic, ?_, ?_, ?_, ?_, ?_,
    hactual, hcontracts, hcaps, hfullcaps, hnash, huniform⟩
  · simpa only [hrootHazard] using hinterior.1
  · simpa only [hrootHazard] using hinterior.2.1
  · simpa only [hrootHazard] using hinterior.2.2.1
  · simpa only [hrootHazard] using hinterior.2.2.2
  · obtain ⟨outsider, hfirstNe, hsecondNe, hpos⟩ := hout
    exact ⟨outsider, hfirstNe, hsecondNe, by simpa only [hrootHazard] using hpos⟩

end GameTheory
