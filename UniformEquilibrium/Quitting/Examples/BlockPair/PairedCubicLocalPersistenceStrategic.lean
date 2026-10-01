import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCubicLocalPersistence
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseStrategic

/-! # Original-game semantics of the full-table implicit stationary branch

Each perturbed reward table has its own fixed terminal target. The same actual
stationary profile realizes that target at every positive accuracy and caps
every complete behavioral deviation. The fourth hazard remains exactly zero.
-/

noncomputable section

namespace GameTheory.PairedCubicStationaryExample

private theorem actual_stationary_of_active_branch
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (point : Fin 3 → ℝ) (hinterior : ∀ coordinate, point coordinate ∈ Set.Ioo (0 : ℝ) 1)
    (hactive : activeResponse table point = 0)
    (hinactive : quittingDiscountedDisplacement table 0 (activeHazard point) 3 < 0) :
    ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      hazardOfRoot root = activeHazard point ∧
      value = quittingTerminalPayoff table (quittingStationaryProfile table root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (∀ who, quittingContinuationBestResponseValue table
        (quittingStationaryProfile table root) who = value who) ∧
      (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
        (quittingStationaryProfile table root) ∧
      (quittingGame table).IsUniformEquilibriumPayoff none value ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame table).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile table root) ∧
          ∀ who, |(quittingGame table).finiteAveragePayoff none horizon
            (quittingStationaryProfile table root) who - value who| ≤ accuracy := by
  have hbox : ∀ who, 0 ≤ activeHazard point who ∧ activeHazard point who ≤ 1 := by
    intro who
    fin_cases who
    · exact ⟨(hinterior 0).1.le, (hinterior 0).2.le⟩
    · exact ⟨(hinterior 1).1.le, (hinterior 1).2.le⟩
    · exact ⟨(hinterior 2).1.le, (hinterior 2).2.le⟩
    · norm_num [activeHazard]
  have hnonzero : activeHazard point ≠ 0 := by
    intro hequal
    have hcoordinate := congrFun hequal 0
    change point 0 = 0 at hcoordinate
    exact (ne_of_gt (hinterior 0).1) hcoordinate
  have hresidual (who : Fin 4) (hwho : who ≠ 3) :
      quittingDiscountedDisplacement table 0 (activeHazard point) who = 0 := by
    fin_cases who
    · exact congrFun hactive 0
    · exact congrFun hactive 1
    · exact congrFun hactive 2
    · exact (hwho rfl).elim
  have hsign : ∀ who,
      (activeHazard point who = 0 →
        quittingDiscountedDisplacement table 0 (activeHazard point) who ≤ 0) ∧
      (0 < activeHazard point who → activeHazard point who < 1 →
        quittingDiscountedDisplacement table 0 (activeHazard point) who = 0) ∧
      (activeHazard point who = 1 →
        0 ≤ quittingDiscountedDisplacement table 0 (activeHazard point) who) := by
    intro who
    by_cases hwho : who = 3
    · subst who
      refine ⟨fun _ => hinactive.le, ?_, ?_⟩
      · intro hpositive _
        norm_num [activeHazard] at hpositive
      · intro hone
        norm_num [activeHazard] at hone
    · have hequal := hresidual who hwho
      exact ⟨fun _ => hequal.le, fun _ _ => hequal, fun _ => hequal.ge⟩
  have hfixed := (quittingDiscountedClippedMap_eq_self_iff table 0 (activeHazard point)
    (fun who => (hbox who).1) (fun who => (hbox who).2)).mpr hsign
  obtain ⟨root, value, hroot, habsorption, hvalue, hbellman, hendpoint⟩ :=
    stationaryEndpointCertificate_of_nonzero_clippedMap_fixed table (activeHazard point)
      (fun who => (hbox who).1) (fun who => (hbox who).2) hnonzero hfixed
  have hfirst : 0 < (root 0 true).toReal := by
    change 0 < hazardOfRoot root 0
    rw [hroot]
    exact (hinterior 0).1
  have hsecond : 0 < (root 1 true).toReal := by
    change 0 < hazardOfRoot root 1
    rw [hroot]
    exact (hinterior 1).1
  have hcontracts (who : Fin 4) :
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    by_cases hwho : who = 0
    · subst who
      exact quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
        root (show (1 : Fin 4) ≠ 0 by decide) hsecond
    · exact quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
        root (Ne.symm hwho) hfirst
  have habsorbs : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hboundary := isQuittingStationaryBoundaryAdmissible_of_contracts
    table root value hcontracts
  have hcaps (who : Fin 4) :
      quittingContinuationBestResponseValue table (quittingStationaryProfile table root) who =
        value who := by
    rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap]
    exact quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash
      table root value habsorbs hbellman hendpoint hboundary who
  obtain ⟨hterminal, hsame⟩ := terminalNash_and_sameProfileUniform_of_stationaryBoundary
    table root value habsorption hbellman
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash table value root).mp hendpoint)
    hboundary
  refine ⟨root, value, hroot, hvalue, hcontracts, hcaps, hterminal, ?_, ?_⟩
  · exact isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
      table root value habsorbs hbellman hendpoint hcontracts
  · simpa only [← hvalue] using hsame

/-- The same smooth three-hazard branch supplies original complete-behavioral equilibria
throughout a neighborhood of the literal full sixty-entry table. -/
theorem exists_local_stationary_branch :
    ∃ branch : RewardParameters → (Fin 3 → ℝ),
      ∃ neighborhood : Set RewardParameters,
        IsOpen neighborhood ∧ baseParameters ∈ neighborhood ∧
        ContDiffOn ℝ 1 branch neighborhood ∧ branch baseParameters = activeBase ∧
        ∀ parameters ∈ neighborhood,
          (∀ coordinate, branch parameters coordinate ∈ Set.Ioo (0 : ℝ) 1) ∧
          jointActiveResponse (parameters, branch parameters) = 0 ∧
          jointDisplacement (parameters, branch parameters) 3 < 0 ∧
          ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
            let table := quittingRewardTableFromCoordinates parameters
            hazardOfRoot root = activeHazard (branch parameters) ∧
            value = quittingTerminalPayoff table (quittingStationaryProfile table root) ∧
            (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
            (∀ who, quittingContinuationBestResponseValue table
              (quittingStationaryProfile table root) who = value who) ∧
            (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
              (quittingStationaryProfile table root) ∧
            (quittingGame table).IsUniformEquilibriumPayoff none value ∧
            ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
              ∀ horizon, threshold ≤ horizon →
                (quittingGame table).IsεHorizonNash none horizon accuracy
                  (quittingStationaryProfile table root) ∧
                ∀ who, |(quittingGame table).finiteAveragePayoff none horizon
                  (quittingStationaryProfile table root) who - value who| ≤ accuracy := by
  obtain ⟨branch, neighborhood, hopen, hbase, hsmooth, hbranchBase, hsource⟩ :=
    exists_local_active_branch
  refine ⟨branch, neighborhood, hopen, hbase, hsmooth, hbranchBase, ?_⟩
  intro parameters hparameters
  obtain ⟨hinterior, hzero, hnegative⟩ := hsource parameters hparameters
  refine ⟨hinterior, hzero, hnegative, ?_⟩
  exact actual_stationary_of_active_branch (quittingRewardTableFromCoordinates parameters)
    (branch parameters) hinterior hzero hnegative

end GameTheory.PairedCubicStationaryExample
