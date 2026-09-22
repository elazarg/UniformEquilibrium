import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientBellman
import UniformEquilibrium.Quitting.Cycles.InteriorApproximateNashCyclicProfile
import UniformEquilibrium.Quitting.Root.FaceGeometry

/-!
# Strategic consumption of a response-invariant quotient root

When every block has at least two original players, a nonzero block-constant
root has a positive opponent hazard for every player. The stationary endpoint
compiler then handles all behavioral deviations without a Never boundary
condition.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- A raw response-invariant partition with no singleton block and quotient
degree different from one gives an original-game uniform-equilibrium payoff.
No root or favorable strategy is supplied. -/
theorem exists_uniformEquilibriumPayoff_of_responseInvariant_noSingletonBlocks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hblock : ∀ who : ι, ∃ other : ι, other ≠ who ∧ block other = block who)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative))
    (hdegree : r0Degree (quittingResponseQuotientMatrix reward block representative)
      hR0 ≠ 1) :
    ∃ value, (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  obtain ⟨root, value, habsorption, _hactual, hfixed, hnash, hequal⟩ :=
    exists_original_stationaryBellmanRoot_of_quotientDegree_ne_one
      reward block representative hrepresentative hresponse hR0 hdegree
  obtain ⟨active, hactive⟩ :=
    (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mp habsorption
  obtain ⟨partner, hpartnerNe, hpartnerBlock⟩ := hblock active
  have hpartnerPos : 0 < (root partner true).toReal := by
    have heq := hequal partner active hpartnerBlock
    have hactiveHazard : 0 < hazardOfRoot root active := by
      simpa only [hazardOfRoot] using hactive
    have hpartnerHazard : 0 < hazardOfRoot root partner := by
      rw [heq]
      exact hactiveHazard
    simpa only [hazardOfRoot] using hpartnerHazard
  have hcontracts (who : ι) :
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    by_cases hwho : active = who
    · subst who
      exact quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
        root hpartnerNe hpartnerPos
    · exact quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
        root hwho hactive
  have habsorbs : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  refine ⟨value, ?_⟩
  exact isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    reward root value habsorbs hfixed
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward value root).mpr hnash) hcontracts

/-- Positive joint absorption and block-constant hazards leave a saturated
opponent face only at a singleton block. A nonnegative solo reward then
discharges exactly the stationary Never-response boundary condition. -/
theorem stationaryBoundaryAdmissible_of_blockwiseHazards_singletonSign
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (root : ι → PMF Bool) (value : Payoff ι)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hequal : ∀ first second, block first = block second →
      hazardOfRoot root first = hazardOfRoot root second)
    (hsign : ∀ who, (∀ other, other ≠ who → block other ≠ block who) →
      0 ≤ reward (quittingSingletonTerminal who) who) :
    IsQuittingStationaryBoundaryAdmissible reward root value := by
  intro who hmass
  obtain ⟨active, hactive⟩ :=
    (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mp habsorption
  have hactiveWho : active = who := by
    by_contra hne
    have hlt := quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
      root hne hactive
    rw [hmass] at hlt
    exact (lt_irrefl 1 hlt).elim
  subst active
  have hsingleton : ∀ other, other ≠ who → block other ≠ block who := by
    intro other hne hblock
    have heq := hequal other who hblock
    have hpositiveOther : 0 < (root other true).toReal := by
      have hactiveHazard : 0 < hazardOfRoot root who := by
        simpa only [hazardOfRoot] using hactive
      have hotherHazard : 0 < hazardOfRoot root other := by
        rw [heq]
        exact hactiveHazard
      simpa only [hazardOfRoot] using hotherHazard
    have hpure := opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
      root who hmass other hne
    rw [hpure] at hpositiveOther
    norm_num at hpositiveOther
  have hsoloNonneg := hsign who hsingleton
  have hpure := opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
    root who hmass
  have hendpoints := quittingRoot_endpoints_eq_singleton_tail_of_opponents_pureContinue
    reward value root who hpure
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix reward value root who
  rw [hendpoints.1, hendpoints.2] at hmix
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hvalue := congrFun hfixed who
  have hsumValue :
      (root who false).toReal * value who +
        (root who true).toReal * value who = value who := by
    calc
      _ = ((root who false).toReal + (root who true).toReal) * value who := by ring
      _ = value who := by rw [hsum]; ring
  have hproduct : (root who true).toReal *
      (value who - reward (quittingSingletonTerminal who) who) = 0 := by
    nlinarith [hmix, hvalue, hsumValue]
  have hvalueSolo : value who = reward (quittingSingletonTerminal who) who := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hactive))
  rw [hvalueSolo]
  simpa only [max_eq_right hsoloNonneg] using
    (le_refl (reward (quittingSingletonTerminal who) who))

/-- The source's nonnegative-singleton-block alternative gives a fixed
uniform-equilibrium payoff without a supplied stationary root. -/
theorem exists_uniformEquilibriumPayoff_of_responseInvariant_singletonSign
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hsign : ∀ who, (∀ other, other ≠ who → block other ≠ block who) →
      0 ≤ reward (quittingSingletonTerminal who) who)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative))
    (hdegree : r0Degree (quittingResponseQuotientMatrix reward block representative)
      hR0 ≠ 1) :
    ∃ value, (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  obtain ⟨root, value, habsorption, _hactual, hfixed, hnash, hequal⟩ :=
    exists_original_stationaryBellmanRoot_of_quotientDegree_ne_one
      reward block representative hrepresentative hresponse hR0 hdegree
  have hboundary := stationaryBoundaryAdmissible_of_blockwiseHazards_singletonSign
    reward block root value habsorption hfixed hequal hsign
  have habsorbs : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  refine ⟨value, ?_⟩
  exact isUniformEquilibriumPayoff_of_stationaryEndpointCertificate
    reward root value habsorbs hfixed
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward value root).mpr hnash) hboundary

end GameTheory
