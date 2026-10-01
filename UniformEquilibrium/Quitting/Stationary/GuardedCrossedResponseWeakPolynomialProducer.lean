import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakPolynomialFaces
import UniformEquilibrium.Quitting.Stationary.StationaryUniformPayoffWitnessSelection

/-! # Fixed original-game targets from weak polynomial half-face guards

Nearby literal tables supply fresh contracting stationary equilibria. Reward
robustness moves their complete terminal guarantees to the original table;
the existing payoff-subsequence selector fixes the target before accuracy.
No exact stationary attainment at the weak boundary is asserted.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification Math.LinearProgramming Math.LinearAlgebra

/-- The actual perturbation supplies arbitrarily close strict polynomial
games and fresh original-incentive stationary roots, with their actual values. -/
theorem exists_weakPolynomialPerturb_stationaryTerminalNash_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hguard : QuittingHalfWeakPolynomialGuards reward) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ 3 * epsilon ≤ delta ∧
      ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
        value = quittingTerminalPayoff (quittingCrossedWeakHalfPerturb epsilon reward)
          (quittingStationaryProfile (quittingCrossedWeakHalfPerturb epsilon reward) root) ∧
        (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
        (quittingGame (quittingCrossedWeakHalfPerturb epsilon reward)).IsεAsymptoticNash
          (quittingTerminalPayoff (quittingCrossedWeakHalfPerturb epsilon reward)) 0
          (quittingStationaryProfile (quittingCrossedWeakHalfPerturb epsilon reward) root) ∧
        (quittingGame (quittingCrossedWeakHalfPerturb epsilon reward)).IsUniformEquilibriumPayoff
          none value := by
  obtain ⟨hfirst, hsecond⟩ := hguard.reciprocal_pos hdet.ne' hinverse
  obtain ⟨threshold, hthreshold, hsmall⟩ :=
    exists_pos_strictlyPositiveInverse_sub_offDiagonalOnes
      (quittingSingletonMatrix reward) (by norm_num) hdet.ne' hinverse
  let bound := min (delta / 3)
    (min (quittingSingletonMatrix reward 0 1) (quittingSingletonMatrix reward 1 0))
  have hbound : 0 < bound := lt_min (by positivity) (lt_min hfirst hsecond)
  let epsilon := min threshold bound / 2
  have hepsilon : 0 < epsilon := half_pos (lt_min hthreshold hbound)
  have hepsilonThreshold : epsilon < threshold := by
    have hle : min threshold bound ≤ threshold := min_le_left _ _
    dsimp [epsilon]
    linarith
  have hepsilonBound : epsilon < bound := by
    have hle : min threshold bound ≤ bound := min_le_right _ _
    dsimp [epsilon]
    linarith
  have hclose : 3 * epsilon ≤ delta := by
    have hle : bound ≤ delta / 3 := min_le_left _ _
    linarith
  have hepsilonFirst : epsilon < quittingSingletonMatrix reward 0 1 :=
    hepsilonBound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsilonSecond : epsilon < quittingSingletonMatrix reward 1 0 :=
    hepsilonBound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hpositive, hsign, -⟩ := hsmall epsilon hepsilon hepsilonThreshold
  have hnearDet : 0 < (quittingSingletonMatrix
      (quittingCrossedWeakHalfPerturb epsilon reward)).det := by
    rw [quittingSingletonMatrix_weakHalfPerturb]
    exact sign_eq_one_iff.mp (hsign.trans (sign_pos hdet))
  have hnearInverse : ∀ row column,
      0 < (quittingSingletonMatrix (quittingCrossedWeakHalfPerturb epsilon reward))⁻¹
        row column := by
    rw [quittingSingletonMatrix_weakHalfPerturb]
    exact hpositive.2
  have hnearFirst : 0 < quittingSingletonMatrix
      (quittingCrossedWeakHalfPerturb epsilon reward) 0 1 := by
    rw [quittingSingletonMatrix_weakHalfPerturb]
    simpa [offDiagonalOnes] using sub_pos.mpr hepsilonFirst
  have hnearSecond : 0 < quittingSingletonMatrix
      (quittingCrossedWeakHalfPerturb epsilon reward) 1 0 := by
    rw [quittingSingletonMatrix_weakHalfPerturb]
    simpa [offDiagonalOnes] using sub_pos.mpr hepsilonSecond
  have hnearGuards := quittingCrossedSourceGuards_of_weakPolynomialPerturb
    epsilon hepsilon reward hguard
  obtain ⟨hR0, hdegree⟩ :=
    quittingCrossedSingletonMatrix_r0_degree_neg_one_of_positiveInverse
      (quittingCrossedWeakHalfPerturb epsilon reward) 0 1 (by decide) hnearDet hnearInverse
  have hdegreeNe : r0Degree
      (quittingCrossedSingletonMatrix (quittingCrossedWeakHalfPerturb epsilon reward) 0 1)
      hR0 ≠ 1 := by
    rw [hdegree]
    norm_num
  obtain ⟨root, value, -, -, -, -, -, hvalue, hcontracts, hnash, hUE⟩ :=
    exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards
      (quittingCrossedWeakHalfPerturb epsilon reward) 0 1 (by decide)
      (1 / 2) (by norm_num) (by norm_num) hnearGuards hnearFirst hnearSecond hR0 hdegreeNe
  exact ⟨epsilon, hepsilon, hclose, root, value, hvalue, hcontracts, hnash, hUE⟩

/-- The unchanged original reward has contracting stationary profiles with
arbitrarily small regret against every complete behavioral replacement. -/
theorem exists_stationary_terminalApproximation_of_weakHalfPolynomialGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hguard : QuittingHalfWeakPolynomialGuards reward) (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∃ root : Fin 4 → PMF Bool,
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
        (quittingStationaryProfile reward root) := by
  obtain ⟨epsilon, hepsilon, hclose, root, value, -, hcontracts, hnash, -⟩ :=
    exists_weakPolynomialPerturb_stationaryTerminalNash_uniformPayoff
      reward hdet hinverse hguard (accuracy / 2) (by positivity)
  have hnear := IsεAsymptoticNash.of_reward_close
    (quittingCrossedWeakHalfPerturb epsilon reward) reward
    (quittingStationaryProfile (quittingCrossedWeakHalfPerturb epsilon reward) root)
    (show 0 ≤ 3 * epsilon by positivity)
    (abs_quittingCrossedWeakHalfPerturb_sub_le epsilon hepsilon.le reward) hnash
  refine ⟨root, hcontracts, ?_⟩
  intro who deviation
  have h := hnear who deviation
  change quittingTerminalPayoff reward
      (Function.update (quittingStationaryProfile reward root) who deviation) who ≤
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) who +
      (0 + 2 * (3 * epsilon)) at h
  linarith

/-- The original signed game has one fixed UE target and actual stationary
witnesses for terminal approximation and all sufficiently long horizons.
Only polynomial weak faces, positive determinant, and nonnegative inverse
are inputs. No favorable root, coefficient certificate, or punishment is supplied. -/
theorem exists_stationary_uniformPayoff_witnesses_of_weakHalfPolynomialGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hguard : QuittingHalfWeakPolynomialGuards reward) :
    ∃ target : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none target ∧
      ∀ accuracy : ℝ, 0 < accuracy →
        ∃ root : Fin 4 → PMF Bool,
          (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
          (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
            (quittingStationaryProfile reward root) ∧
          (∀ who, |quittingTerminalPayoff reward (quittingStationaryProfile reward root) who -
            target who| ≤ accuracy) ∧
          ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
            (quittingGame reward).IsεHorizonNash none horizon accuracy
              (quittingStationaryProfile reward root) ∧
            ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
              (quittingStationaryProfile reward root) who - target who| ≤ accuracy :=
  exists_uniformPayoff_stationaryWitnesses_of_terminalApproximations reward
    (exists_stationary_terminalApproximation_of_weakHalfPolynomialGuards
      reward hdet hinverse hguard)

/-- The broader weak polynomial-face existence assertion, with a fixed target. -/
theorem exists_uniformEquilibriumPayoff_of_weakHalfPolynomialGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hguard : QuittingHalfWeakPolynomialGuards reward) :
    ∃ target : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨target, hUE, -⟩ :=
    exists_stationary_uniformPayoff_witnesses_of_weakHalfPolynomialGuards
      reward hdet hinverse hguard
  exact ⟨target, hUE⟩

end GameTheory
