import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientDegreeEscape
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# Original-player Bellman decoding of a response-invariant quotient root

The degree producer supplies a nonzero block-coordinate clipped fixed point.
Raw response invariance transfers its signs to every original player; the
actual repeated stationary payoff supplies the Bellman continuation.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The zero-discount response polynomial equals absorption mass times the
original player's endpoint difference at the actual repeated payoff. -/
theorem quittingRootAbsorptionMass_mul_endpointDifference_stationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorptionMass root *
        quittingRootEndpointDifference reward
          (quittingTerminalPayoff reward (quittingStationaryProfile reward root))
          root who =
      quittingDiscountedDisplacement reward 0 (hazardOfRoot root) who := by
  rw [quittingRootEndpointDifference, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue]
  have h := one_sub_continueMass_mul_quittingTerminalPayoff_stationary
    reward root who
  rw [quittingRootAbsorbingContribution_eq_hazard_mixture] at h
  unfold quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_hazard_split root who]
  rw [quittingStationaryContinueMass_eq_hazard_split root who] at h
  unfold gammaValue quittingDiscountedDisplacement
  nlinarith [congrArg
    (fun value => value * continueMassExcl (hazardOfRoot root) who) h]

/-- A nonzero quotient clipped fixed point yields an absorbing stationary
Nash-Bellman root of the original game, with the actual repeated payoff.
This does not assert the Never-response boundary inequality. -/
theorem exists_original_stationaryBellmanRoot_of_quotientDegree_ne_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative))
    (hdegree : r0Degree (quittingResponseQuotientMatrix reward block representative)
      hR0 ≠ 1) :
    ∃ root : ι → PMF Bool, ∃ value : Payoff ι,
      0 < quittingRootAbsorptionMass root ∧
      value = quittingTerminalPayoff reward (quittingStationaryProfile reward root) ∧
      value = quittingRootSuccessorPayoff reward value root ∧
      IsεQuittingRootNash reward value 0 root ∧
      ∀ first second, block first = block second →
        hazardOfRoot root first = hazardOfRoot root second := by
  obtain ⟨point, hpointNe, hfixed⟩ :=
    exists_nonzero_quittingQuotientStationaryClippedMap_fixedPoint
      reward block representative hrepresentative hR0 hdegree
  have hcube := quittingQuotientStationaryClippedMap_mem_unitCube
    reward block representative point
  rw [hfixed] at hcube
  let hazard := quittingBlockLift block point
  have hzero (who : ι) : 0 ≤ hazard who := hcube.1 (block who)
  have hone (who : ι) : hazard who ≤ 1 := hcube.2 (block who)
  let root := rootOfHazard hazard hzero hone
  have hrootHazard : hazardOfRoot root = hazard :=
    hazardOfRoot_rootOfHazard hazard hzero hone
  have hpositive : 0 < quittingRootAbsorptionMass root := by
    apply (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mpr
    have hcoordinate : ∃ coordinate, point coordinate ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hpointNe
      funext coordinate
      exact hnone coordinate
    obtain ⟨coordinate, hne⟩ := hcoordinate
    have hpos : 0 < point coordinate := lt_of_le_of_ne (hcube.1 coordinate) (Ne.symm hne)
    refine ⟨representative coordinate, ?_⟩
    have hrate : (root (representative coordinate) true).toReal =
        point coordinate := by
      simpa [hazardOfRoot, hazard, quittingBlockLift,
        hrepresentative coordinate] using
          congrFun hrootHazard (representative coordinate)
    exact hrate.symm ▸ hpos
  let value : Payoff ι :=
    quittingTerminalPayoff reward (quittingStationaryProfile reward root)
  have hbellman : value = quittingRootSuccessorPayoff reward value root := by
    funext who
    exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who
  have hsign (who : ι) :
      (hazard who = 0 →
        quittingDiscountedDisplacement reward 0 hazard who ≤ 0) ∧
      (0 < hazard who → hazard who < 1 →
        quittingDiscountedDisplacement reward 0 hazard who = 0) ∧
      (hazard who = 1 →
        0 ≤ quittingDiscountedDisplacement reward 0 hazard who) := by
    have hpointSigns := (quittingQuotientStationaryClippedMap_eq_self_iff
      reward block representative point hcube.1 hcube.2).mp hfixed
    have hrep := hpointSigns (block who)
    have hsame := hresponse point (fun coordinate =>
      ⟨hcube.1 coordinate, hcube.2 coordinate⟩)
        who (representative (block who))
          (hrepresentative (block who)).symm
    simpa only [hazard, quittingBlockLift, quittingQuotientResponse] using
      (by rw [hsame] at *; exact hrep)
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
  refine ⟨root, value, hpositive, rfl, hbellman,
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward value root).mp hendpoint, ?_⟩
  intro first second hblock
  rw [hrootHazard]
  simp only [hazard, quittingBlockLift, hblock]

end GameTheory
