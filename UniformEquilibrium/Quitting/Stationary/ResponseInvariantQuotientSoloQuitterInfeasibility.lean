import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientSameProfile
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium

/-!
# Actual quotient roots under sole-quitter joining infeasibility

For every negative singleton-block owner, exclude the canonical raw joining
criterion at every rate in (0,1]. A saturated deleted clock is then identified
as the actual sole-owner row at its own positive rate, and its own singleton
payoff cannot be negative. This derives the Never boundary and retains the
SAME independent stationary profile and its actual fixed payoff.

The criterion contains only opponents' joining inequalities; no owner
positivity is silently added. No infeasibility claim about other owners,
selected favorable root, or strategic cap is an input.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- A saturated deleted clock in an absorbing block-constant root identifies
the actual queried player as the sole positive-rate owner of a singleton block. -/
theorem soloRoot_and_singletonBlock_of_blockwiseHazards_saturatedOpponents
    (block : ι → Fin k) (root : ι → PMF Bool)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hequal : ∀ first second, block first = block second →
      hazardOfRoot root first = hazardOfRoot root second)
    (owner : ι) (hmass : quittingStationaryFixedOpponentsContinueMass root owner = 1) :
    root = quittingSoloStationaryRoot owner (root owner) ∧
      0 < (root owner true).toReal ∧ (root owner true).toReal ≤ 1 ∧
      ∀ other, other ≠ owner → block other ≠ block owner := by
  have hpure := opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
    root owner hmass
  have hroot := eq_quittingSoloStationaryRoot_of_others_continue hpure
  have habsolo : 0 < quittingRootAbsorptionMass
      (quittingSoloStationaryRoot owner (root owner)) := by
    rw [← hroot]
    exact habsorption
  have hpositive : 0 < (root owner true).toReal := by
    simpa only [quittingRootAbsorptionMass_soloStationaryRoot] using habsolo
  refine ⟨hroot, hpositive, hazardOfRoot_le_one root owner, ?_⟩
  intro other hne hblock
  have hotherPositive : 0 < (root other true).toReal := by
    change 0 < hazardOfRoot root other
    rw [hequal other owner hblock]
    exact hpositive
  rw [hpure other hne] at hotherPositive
  norm_num at hotherPositive

/-- The actual Bellman value on a saturated deleted clock yields the canonical
solo joining criterion. Its infeasibility at negative singleton-block owners
therefore produces the stationary Never boundary, rather than assuming it. -/
theorem stationaryBoundaryAdmissible_of_blockwiseHazards_soloQuitterInfeasibility
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (root : ι → PMF Bool) (value : Payoff ι)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hnash : IsεQuittingRootNash reward value 0 root)
    (hequal : ∀ first second, block first = block second →
      hazardOfRoot root first = hazardOfRoot root second)
    (hinfeasible : ∀ owner,
      (∀ other, other ≠ owner → block other ≠ block owner) →
      quittingSoloReward reward owner owner < 0 →
      ∀ rate : ℝ, 0 < rate → rate ≤ 1 → ¬ QuittingSoloQuitterCriterion reward owner rate) :
    IsQuittingStationaryBoundaryAdmissible reward root value := by
  have habsorbs : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hactual := (quittingTerminalPayoff_stationary_eq_of_fixedPoint
    reward root value habsorbs hfixed).symm
  have hendpoint := (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward value root).mpr hnash
  intro owner hmass
  obtain ⟨hroot, hpositive, hrateOne, hsingleton⟩ :=
    soloRoot_and_singletonBlock_of_blockwiseHazards_saturatedOpponents
      block root habsorption hequal owner hmass
  have hvalueSolo : value = quittingSoloReward reward owner := by
    funext player
    calc
      value player =
          quittingTerminalPayoff reward (quittingStationaryProfile reward root) player :=
        congrFun hactual player
      _ = quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (quittingSoloStationaryRoot owner (root owner))) player :=
        congrArg (fun currentRoot =>
          quittingTerminalPayoff reward (quittingStationaryProfile reward currentRoot) player)
          hroot
      _ = quittingSoloReward reward owner player :=
        quittingTerminalPayoff_soloStationary reward owner player (root owner) hpositive
  have hsoloEndpoint : IsεQuittingRootEndpointNash reward (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner (root owner)) := by
    rw [← hroot, ← hvalueSolo]
    exact hendpoint
  have hinactive := (isεQuittingRootEndpointNash_soloStationaryRoot_iff
    reward owner (root owner)).mp hsoloEndpoint
  have hfalse : (root owner false).toReal = 1 - (root owner true).toReal := by
    linarith [quittingSoloHazardMass_add (root owner)]
  have hcriterion : QuittingSoloQuitterCriterion reward owner (root owner true).toReal := by
    intro other hne
    simpa only [hfalse] using hinactive other hne
  have hnonnegative : 0 ≤ quittingSoloReward reward owner owner := by
    by_contra hnegative
    exact hinfeasible owner hsingleton (lt_of_not_ge hnegative)
      (root owner true).toReal hpositive hrateOne hcriterion
  change max 0 (quittingSoloReward reward owner owner) ≤ value owner
  rw [hvalueSolo]
  exact max_le hnonnegative le_rfl

/-- EVERY actual nonzero quotient fixed point satisfies the derived boundary,
exact unrestricted terminal Nash and SAME-profile uniform witnesses at its actual
fixed payoff under literal negative-singleton-block sole-quitter infeasibility. -/
theorem boundary_and_sameProfileUniform_of_nonzero_quotientFixedPoint_soloQuitterInfeasibility
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (point : Fin k → ℝ) (hpointNe : point ≠ 0)
    (hfixed : quittingQuotientStationaryClippedMap reward block representative point = point)
    (root : ι → PMF Bool) (hhazard : hazardOfRoot root = quittingBlockLift block point)
    (hinfeasible : ∀ owner,
      (∀ other, other ≠ owner → block other ≠ block owner) →
      quittingSoloReward reward owner owner < 0 →
      ∀ rate : ℝ, 0 < rate → rate ≤ 1 → ¬ QuittingSoloQuitterCriterion reward owner rate) :
    IsQuittingStationaryBoundaryAdmissible reward root
        (quittingTerminalPayoff reward (quittingStationaryProfile reward root)) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingTerminalPayoff reward (quittingStationaryProfile reward root)) ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward root) who -
            quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
              accuracy := by
  obtain ⟨value, habsorption, hactual, hbellman, hnash, hequal⟩ :=
    stationaryBellmanCertificate_of_nonzero_quotientFixedPoint
      reward block representative hrepresentative hresponse point hpointNe hfixed root hhazard
  have hboundary := stationaryBoundaryAdmissible_of_blockwiseHazards_soloQuitterInfeasibility
    reward block root value habsorption hbellman hnash hequal hinfeasible
  obtain ⟨hterminal, hsame⟩ := terminalNash_and_sameProfileUniform_of_stationaryBoundary
    reward root value habsorption hbellman hnash hboundary
  have hboundaryActual : IsQuittingStationaryBoundaryAdmissible reward root
      (quittingTerminalPayoff reward (quittingStationaryProfile reward root)) := by
    rw [← hactual]
    exact hboundary
  have huniform : (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingTerminalPayoff reward (quittingStationaryProfile reward root)) := by
    intro accuracy haccuracy
    obtain ⟨threshold, hthreshold⟩ := hsame accuracy haccuracy
    exact ⟨quittingStationaryProfile reward root, threshold, hthreshold⟩
  exact ⟨hboundaryActual, hterminal, huniform, hsame⟩

/-- The actual R0/degree source produces one Bellman root and fixed value
with the same-profile conclusion under the raw sole-quitter infeasibility test.
All original-player Bellman data and the quotient hazard equality are retained. -/
theorem exists_stationaryTerminalNash_sameProfileUniform_of_soloQuitterInfeasibility
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward block representative))
    (hdegree : r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 ≠ 1)
    (hinfeasible : ∀ owner,
      (∀ other, other ≠ owner → block other ≠ block owner) →
      quittingSoloReward reward owner owner < 0 →
      ∀ rate : ℝ, 0 < rate → rate ≤ 1 → ¬ QuittingSoloQuitterCriterion reward owner rate) :
    ∃ point : Fin k → ℝ, ∃ root : ι → PMF Bool, ∃ value : Payoff ι,
      point ≠ 0 ∧
      quittingQuotientStationaryClippedMap reward block representative point = point ∧
      hazardOfRoot root = quittingBlockLift block point ∧
      0 < quittingRootAbsorptionMass root ∧
      value = quittingTerminalPayoff reward (quittingStationaryProfile reward root) ∧
      value = quittingRootSuccessorPayoff reward value root ∧
      IsεQuittingRootNash reward value 0 root ∧
      (∀ first second, block first = block second →
        hazardOfRoot root first = hazardOfRoot root second) ∧
      IsQuittingStationaryBoundaryAdmissible reward root value ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward root) who - value who| ≤ accuracy := by
  obtain ⟨point, hpointNe, hfixed⟩ :=
    exists_nonzero_quittingQuotientStationaryClippedMap_fixedPoint
      reward block representative hrepresentative hR0 hdegree
  obtain ⟨root, value, hhazard, habsorption, hactual, hbellman, hnash, hequal⟩ :=
    exists_original_stationaryBellmanRoot_of_nonzero_quotientFixedPoint
      reward block representative hrepresentative hresponse point hpointNe hfixed
  obtain ⟨hboundary, hterminal, huniform, hsame⟩ :=
    boundary_and_sameProfileUniform_of_nonzero_quotientFixedPoint_soloQuitterInfeasibility
      reward block representative hrepresentative hresponse point hpointNe hfixed
      root hhazard hinfeasible
  rw [← hactual] at hboundary huniform hsame
  exact ⟨point, root, value, hpointNe, hfixed, hhazard, habsorption, hactual,
    hbellman, hnash, hequal, hboundary, hterminal, huniform, hsame⟩

end GameTheory
