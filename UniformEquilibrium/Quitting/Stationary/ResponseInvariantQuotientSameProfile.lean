import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientStrategic

/-! # Root-preserving strategic consequences of a response quotient

Every actual nonzero quotient fixed point is decoded using its original
independent stationary profile. Nonnegative singleton-block rewards discharge
the Never boundary; the endpoint compiler covers all behavioral replacements.
One constant Unit-indexed family retains that SAME profile at every accuracy.
There is no root regularity, contraction-rate, or sole-owner exclusion input.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- An absorbing stationary Bellman certificate and its actual Never boundary
retain the SAME profile at every positive accuracy. This is the single
Unit-family uniformization owner for the quotient consumers. -/
theorem terminalNash_and_sameProfileUniform_of_stationaryBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hnash : IsεQuittingRootNash reward value 0 root)
    (hboundary : IsQuittingStationaryBoundaryAdmissible reward root value) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward root) who -
            quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
              accuracy := by
  have habsorbs : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hterminal :=
    (isZeroAsymptoticNash_stationary_iff_boundary_of_fixedPoint_endpointNash
      reward root value habsorbs hfixed
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward value root).mpr hnash)).mpr hboundary
  refine ⟨hterminal, ?_⟩
  let profiles : Unit → (quittingGame reward).BehaviorProfile :=
    fun _ => quittingStationaryProfile reward root
  have haccept : ∀ accuracy : ℝ, 0 < accuracy → ∃ index : Unit,
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
        (profiles index) ∧
      ∀ who, |quittingTerminalPayoff reward (profiles index) who -
        quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
          accuracy := by
    intro accuracy haccuracy
    refine ⟨(), hterminal.mono haccuracy.le, ?_⟩
    intro who
    simpa only [profiles, sub_self, abs_zero] using haccuracy.le
  intro accuracy haccuracy
  obtain ⟨index, threshold, hwitness⟩ :=
    quittingGame_uniformPayoffWitnesses_of_terminalTargetAcceptance_family reward
      (quittingTerminalPayoff reward (quittingStationaryProfile reward root))
      profiles haccept accuracy haccuracy
  exact ⟨threshold, hwitness⟩

private theorem terminalNash_and_sameProfileUniform_of_blockwise_singletonSign
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (root : ι → PMF Bool) (value : Payoff ι)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hnash : IsεQuittingRootNash reward value 0 root)
    (hequal : ∀ first second, block first = block second →
      hazardOfRoot root first = hazardOfRoot root second)
    (hsign : ∀ who, (∀ other, other ≠ who → block other ≠ block who) →
      0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward root) who -
            quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
              accuracy := by

  have hboundary := stationaryBoundaryAdmissible_of_blockwiseHazards_singletonSign
    reward block root value habsorption hfixed hequal hsign
  exact terminalNash_and_sameProfileUniform_of_stationaryBoundary
    reward root value habsorption hfixed hnash hboundary

/-- Decode any actual original root whose hazards are an actual nonzero
quotient fixed point, retaining that very root rather than another selection. -/
theorem stationaryBellmanCertificate_of_nonzero_quotientFixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (point : Fin k → ℝ) (hpointNe : point ≠ 0)
    (hfixed : quittingQuotientStationaryClippedMap reward block representative point = point)
    (root : ι → PMF Bool) (hhazard : hazardOfRoot root = quittingBlockLift block point) :
    ∃ value : Payoff ι,
      0 < quittingRootAbsorptionMass root ∧
      value = quittingTerminalPayoff reward (quittingStationaryProfile reward root) ∧
      value = quittingRootSuccessorPayoff reward value root ∧
      IsεQuittingRootNash reward value 0 root ∧
      ∀ first second, block first = block second →
        hazardOfRoot root first = hazardOfRoot root second := by
  obtain ⟨selected, value, hselected, habsorption, hactual, hbellman, hnash, hequal⟩ :=
    exists_original_stationaryBellmanRoot_of_nonzero_quotientFixedPoint
      reward block representative hrepresentative hresponse point hpointNe hfixed
  have hroot : selected = root := by
    have heq : hazardOfRoot selected = hazardOfRoot root := hselected.trans hhazard.symm
    calc
      selected = rootOfHazard (hazardOfRoot selected)
          (hazardOfRoot_nonneg selected) (hazardOfRoot_le_one selected) :=
        (rootOfHazard_hazardOfRoot selected).symm
      _ = rootOfHazard (hazardOfRoot root)
          (hazardOfRoot_nonneg root) (hazardOfRoot_le_one root) := by
        congr 1
      _ = root := rootOfHazard_hazardOfRoot root
  subst selected
  exact ⟨value, habsorption, hactual, hbellman, hnash, hequal⟩

/-- EVERY actual nonzero quotient root retains its original stationary profile:
exact unrestricted terminal Nash and uniform horizon witnesses at its actual
fixed payoff. No Bellman continuation or favorable cap is supplied. -/
theorem terminalNash_and_sameProfileUniform_of_nonzero_quotientFixedPoint_singletonSign
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (point : Fin k → ℝ) (hpointNe : point ≠ 0)
    (hfixed : quittingQuotientStationaryClippedMap reward block representative point = point)
    (root : ι → PMF Bool) (hhazard : hazardOfRoot root = quittingBlockLift block point)
    (hsign : ∀ who, (∀ other, other ≠ who → block other ≠ block who) →
      0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward root) who -
            quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
              accuracy := by
  obtain ⟨value, habsorption, _hactual, hbellman, hnash, hequal⟩ :=
    stationaryBellmanCertificate_of_nonzero_quotientFixedPoint
      reward block representative hrepresentative hresponse point hpointNe hfixed root hhazard
  exact terminalNash_and_sameProfileUniform_of_blockwise_singletonSign
    reward block root value habsorption hbellman hnash hequal hsign

/-- The degree producer retains its nonzero quotient point, original root,
actual value, individual endpoint Nash, block equalities, exact terminal Nash,
and the SAME stationary profile's uniform witnesses at that value. -/
theorem exists_stationaryTerminalNash_sameProfileUniform_of_responseInvariant_singletonSign
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hsign : ∀ who, (∀ other, other ≠ who → block other ≠ block who) →
      0 ≤ reward (quittingSingletonTerminal who) who)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward block representative))
    (hdegree : r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 ≠ 1) :
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
  obtain ⟨hterminal, hwitness⟩ :=
    terminalNash_and_sameProfileUniform_of_blockwise_singletonSign
      reward block root value habsorption hbellman hnash hequal hsign
  have hsame : ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
      ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon accuracy
          (quittingStationaryProfile reward root) ∧
        ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
          (quittingStationaryProfile reward root) who - value who| ≤ accuracy := by
    rw [hactual]
    exact hwitness
  have huniform : (quittingGame reward).IsUniformEquilibriumPayoff none value := by
    intro accuracy haccuracy
    obtain ⟨threshold, hthreshold⟩ := hsame accuracy haccuracy
    exact ⟨quittingStationaryProfile reward root, threshold, hthreshold⟩
  exact ⟨point, root, value, hpointNe, hfixed, hhazard, habsorption, hactual,
    hbellman, hnash, hequal, hterminal, huniform, hsame⟩

/-- With no singleton blocks, the SAME-profile conclusion holds for arbitrary
signed rewards. All data from the actual degree producer are retained. -/
theorem exists_stationaryTerminalNash_sameProfileUniform_of_responseInvariant_noSingletonBlocks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hblock : ∀ who : ι, ∃ other : ι, other ≠ who ∧ block other = block who)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward block representative))
    (hdegree : r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 ≠ 1) :
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
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile reward root) ∧
          ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingStationaryProfile reward root) who - value who| ≤ accuracy := by
  apply exists_stationaryTerminalNash_sameProfileUniform_of_responseInvariant_singletonSign
    reward block representative hrepresentative ?_ hresponse hR0 hdegree
  intro who hsingleton
  obtain ⟨other, hne, heq⟩ := hblock who
  exact (hsingleton other hne heq).elim

end GameTheory
