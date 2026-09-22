import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseGuards
import UniformEquilibrium.Quitting.Cycles.InteriorApproximateNashCyclicProfile

/-! # Original-game equilibrium and uniform payoff from guarded degree escape -/

noncomputable section

namespace GameTheory

open Math.LinearProgramming

variable {n : ℕ}

/-- Decode a nonzero unswapped stationary clipped root at zero discount into
the actual repeated payoff and its exact endpoint inequalities. -/
theorem stationaryEndpointCertificate_of_nonzero_clippedMap_fixed
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hazard : Fin n → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) (hnonzero : hazard ≠ 0)
    (hfixed : quittingDiscountedClippedMap reward 0 hazard = hazard) :
    ∃ root : Fin n → PMF Bool, ∃ value : Payoff (Fin n),
      hazardOfRoot root = hazard ∧
      0 < quittingRootAbsorptionMass root ∧
      value = quittingTerminalPayoff reward (quittingStationaryProfile reward root) ∧
      value = quittingRootSuccessorPayoff reward value root ∧
      IsεQuittingRootEndpointNash reward value 0 root := by
  let root := rootOfHazard hazard hzero hone
  have hrootHazard : hazardOfRoot root = hazard :=
    hazardOfRoot_rootOfHazard hazard hzero hone
  have hpositive : 0 < quittingRootAbsorptionMass root := by
    apply (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mpr
    have hcoordinate : ∃ coordinate, hazard coordinate ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hnonzero
      funext coordinate
      exact hnone coordinate
    obtain ⟨coordinate, hne⟩ := hcoordinate
    have hpos : 0 < hazard coordinate :=
      lt_of_le_of_ne (hzero coordinate) (Ne.symm hne)
    refine ⟨coordinate, ?_⟩
    have hrate : (root coordinate true).toReal = hazard coordinate := by
      simpa only [hazardOfRoot] using congrFun hrootHazard coordinate
    exact hrate.symm ▸ hpos
  let value : Payoff (Fin n) :=
    quittingTerminalPayoff reward (quittingStationaryProfile reward root)
  have hbellman : value = quittingRootSuccessorPayoff reward value root := by
    funext who
    exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who
  have hsign := (quittingDiscountedClippedMap_eq_self_iff reward 0 hazard
    hzero hone).mp hfixed
  have hendpoint : IsεQuittingRootEndpointNash reward value 0 root := by
    intro who
    have hmass := quittingRootAbsorptionMass_mul_endpointDifference_stationary
      reward root who
    have hdiff : quittingRootAbsorptionMass root *
        quittingRootEndpointDifference reward value root who =
          quittingDiscountedDisplacement reward 0 hazard who := by
      simpa only [value, hrootHazard] using hmass
    have hq0 := hzero who
    have hq1 := hone who
    have hcases := hsign who
    have hquit : (root who true).toReal = hazard who := by
      simpa only [hazardOfRoot] using congrFun hrootHazard who
    have hcontinue : (root who false).toReal = 1 - hazard who := by
      have hsum := quittingRoot_continueProbability_add_quitProbability root who
      linarith
    rw [hquit, hcontinue]
    by_cases hz : hazard who = 0
    · have hnonpos : quittingRootEndpointDifference reward value root who ≤ 0 := by
        nlinarith [hcases.1 hz]
      simp [hz, hnonpos]
    · by_cases ho : hazard who = 1
      · have hnonneg : 0 ≤ quittingRootEndpointDifference reward value root who := by
          nlinarith [hcases.2.2 ho]
        simp [ho, hnonneg]
      · have hpos : 0 < hazard who := lt_of_le_of_ne hq0 (Ne.symm hz)
        have hlt : hazard who < 1 := lt_of_le_of_ne hq1 ho
        have hzeroDiff : quittingRootEndpointDifference reward value root who = 0 := by
          nlinarith [hcases.2.1 hpos hlt]
        simp [hzeroDiff]
  exact ⟨root, value, hrootHazard, hpositive, rfl, hbellman, hendpoint⟩

/-- Source Theorem A: crossed `PΓ` degree escape yields one original-game
stationary behavioral terminal Nash profile and its fixed uniform payoff.
The auxiliary height does not restrict any original action or deviation. -/
theorem exists_guardedCrossed_stationaryTerminalNash_uniformPayoff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (height : ℝ) (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hguard : QuittingCrossedGuards reward first second height)
    (hreciprocalFirst : 0 < QuittingLCPClassification.quittingSingletonMatrix
      reward first second)
    (hreciprocalSecond : 0 < QuittingLCPClassification.quittingSingletonMatrix
      reward second first)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second))
    (hdegree : r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 ≠ 1) :
    ∃ root : Fin n → PMF Bool, ∃ value : Payoff (Fin n),
      0 < hazardOfRoot root first ∧ hazardOfRoot root first < height ∧
      0 < hazardOfRoot root second ∧ hazardOfRoot root second < height ∧
      (∃ outsider, outsider ≠ first ∧ outsider ≠ second ∧
        0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff reward (quittingStationaryProfile reward root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0 (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  obtain ⟨hazard, hnonzero, hcrossed⟩ :=
    exists_nonzero_quittingCrossedClippedMap_fixedPoint reward first second height
      hheight hheightOne hR0 hdegree
  have hout := quittingCrossedClippedMap_fixed_outsiderPositive_of_nonzero
    reward first second hdistinct height hheight hguard hreciprocalFirst
      hreciprocalSecond hazard hnonzero hcrossed
  have hinterior := quittingCrossedClippedMap_fixed_selected_interior_of_outsider
    reward first second height hheight hguard hazard hcrossed hout
  have hbox := quittingCrossedClippedMap_fixed_mem_box reward first second height
    hheight.le hazard hcrossed
  have hzero (who : Fin n) : 0 ≤ hazard who := (hbox who).1
  have hone (who : Fin n) : hazard who ≤ 1 := by
    have hceiling : quittingCrossedCeiling first second height who ≤ 1 := by
      unfold quittingCrossedCeiling
      split_ifs <;> linarith
    exact (hbox who).2.trans hceiling
  have horiginal := quittingDiscountedClippedMap_fixed_of_crossed_fixed_guards
    reward first second height hheight hheightOne hguard hazard hcrossed hout
  obtain ⟨root, value, hrootHazard, habsorption, hactual, hbellman, hendpoint⟩ :=
    stationaryEndpointCertificate_of_nonzero_clippedMap_fixed
      reward hazard hzero hone hnonzero horiginal
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
    reward root value habsorbs hbellman hendpoint hcontracts
  have huniform := isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    reward root value habsorbs hbellman hendpoint hcontracts
  refine ⟨root, value, ?_, ?_, ?_, ?_, ?_, hactual, hcontracts, hnash, huniform⟩
  · simpa only [hrootHazard] using hinterior.1
  · simpa only [hrootHazard] using hinterior.2.1
  · simpa only [hrootHazard] using hinterior.2.2.1
  · simpa only [hrootHazard] using hinterior.2.2.2
  · obtain ⟨outsider, hfirstNe, hsecondNe, hpos⟩ := hout
    exact ⟨outsider, hfirstNe, hsecondNe, by simpa only [hrootHazard] using hpos⟩

/-- Source-shaped Theorem A, with exactly the packet's `(q_partner,z)`
guards `G_h` rather than the equivalent full-box interface. -/
theorem exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (height : ℝ) (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hguard : QuittingCrossedSourceGuards reward first second height)
    (hreciprocalFirst : 0 < QuittingLCPClassification.quittingSingletonMatrix
      reward first second)
    (hreciprocalSecond : 0 < QuittingLCPClassification.quittingSingletonMatrix
      reward second first)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second))
    (hdegree : r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 ≠ 1) :
    ∃ root : Fin n → PMF Bool, ∃ value : Payoff (Fin n),
      0 < hazardOfRoot root first ∧ hazardOfRoot root first < height ∧
      0 < hazardOfRoot root second ∧ hazardOfRoot root second < height ∧
      (∃ outsider, outsider ≠ first ∧ outsider ≠ second ∧
        0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff reward (quittingStationaryProfile reward root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0 (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  apply exists_guardedCrossed_stationaryTerminalNash_uniformPayoff reward first second
    hdistinct height hheight hheightOne
      ((quittingCrossedSourceGuards_iff_fullBoxGuards reward first second
        hdistinct height hheight).mp hguard)
    hreciprocalFirst hreciprocalSecond hR0 hdegree

end GameTheory
