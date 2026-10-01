import UniformEquilibrium.Quitting.Classification.LCP.FullNormalCoreHomogeneousTransfer
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardReindex
import UniformEquilibrium.Quitting.Classification.LCP.StandardQSideExample
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.StrictInversePassiveRowCycle
import UniformEquilibrium.Quitting.Classification.ThreePlayer.StationaryOrSmallHazardTransport

/-! # The stationary-or-small-hazard alternative with every reward sign retained

At three players, the remaining standard-Q normal core must be the full player
set. The existing zero-diagonal classification then constructs a strict directed
cycle of actual singleton differences. Its existing compiler has no sign premise
on the own-singleton rewards. The other gate branch already supplies stationary
roots. This assembles the known strategy-class producers, not merely UE existence.
-/

noncomputable section

namespace GameTheory.QuittingThreePlayerStrategyClass

open QuittingLCPClassification Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem normalizedSoloMatrix_rewardReindex (label : ι ≃ Fin 3)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    normalizedSoloMatrix (quittingRewardReindex label reward) =
      reindexMatrix label (normalizedSoloMatrix reward) := by
  funext receiver owner
  change (normalizedQuittingPayoffTable (quittingRewardReindex label reward)).singletonMatrix
      receiver owner =
    (normalizedQuittingPayoffTable reward).singletonMatrix
      (label.symm receiver) (label.symm owner)
  rw [normalized_singletonMatrix_eq_quittingSingletonMatrix,
    normalized_singletonMatrix_eq_quittingSingletonMatrix]
  exact congrFun (congrFun (quittingSingletonMatrix_rewardReindex label reward) receiver) owner

/-- The remaining standard-Q side on exactly three players constructs an actual
labeled strict singleton cycle, irrespective of signed own-singleton levels. -/
theorem exists_rightSingletonCycle_of_standardQSide_card_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι = 3)
    (hside : StandardQMatrixSide reward) :
    ∃ label : ι ≃ Fin 3, Nonempty (RightSingletonCycle (quittingRewardReindex label reward)) := by
  let matrix := normalizedSoloMatrix reward
  have hQcore : IsStandardQMatrix (normalPlayerMatrix matrix) := hside.normal_standardQ
  have hcore : normalCore matrix = Finset.univ := by
    have hthree : 3 ≤ (normalCore matrix).card := by
      rcases StandardQSideExample.normalCore_eq_empty_or_three_le_card
          matrix (normalizedSoloMatrix_diagonal reward) hQcore with hempty | hthree
      · have hnonempty : (normalCore matrix).Nonempty := hside.normal_nonempty
        rw [hempty] at hnonempty
        exact False.elim (Finset.not_nonempty_empty hnonempty)
      · exact hthree
    apply Finset.eq_univ_of_card
    have hbound : (normalCore matrix).card ≤ Fintype.card ι := Finset.card_le_univ _
    omega
  have hQ : IsStandardQMatrix matrix := by
    have htransport := isStandardQMatrix_reindexMatrix
      (fullNormalCoreEquiv matrix hcore) (normalPlayerMatrix matrix) hQcore
    rwa [reindex_normalPlayerMatrix_fullNormalCoreEquiv] at htransport
  have hhom : ¬HasHomogeneousSimplexSolution matrix := by
    intro hsolution
    exact hside.no_homogeneous
      ((singletonLCPFeasible_normalPlayerMatrix_iff_of_normalCore_eq_univ matrix hcore).mpr
        hsolution)
  obtain ⟨label, a, b, c, d, e, f, ha, hb, hc, hd, he, hf, hgap, hmatrix⟩ :=
    ThreeCoreCyclicLabelAdapter.exists_directedCycle_labeling matrix hcard
      (normalizedSoloMatrix_diagonal reward) hQ hhom
  have hactual : normalizedSoloMatrix (quittingRewardReindex label reward) =
      ThreeByThreeZeroDiagonalQ.directedCycleMatrix a b c d e f :=
    (normalizedSoloMatrix_rewardReindex label reward).trans hmatrix
  exact ⟨label, ⟨rightSingletonCycle_of_directedSoloMatrix
    (quittingRewardReindex label reward) a b c d e f ha hb hc hd he hf hgap hactual⟩⟩

/-- Every signed three-player table on the remaining gate side has the literal
stationary-or-small-hazard terminal equilibrium at each requested accuracy. -/
theorem of_standardQSide_of_card_eq_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι = 3)
    (hside : StandardQMatrixSide reward) {accuracy : ℝ} (haccuracy : 0 < accuracy) :
    StationaryOrSmallHazardTerminalEquilibrium reward accuracy := by
  obtain ⟨label, ⟨cycle⟩⟩ :=
    exists_rightSingletonCycle_of_standardQSide_card_three reward hcard hside
  exact of_reindex label reward
    (of_rightSingletonCycle (quittingRewardReindex label reward) cycle haccuracy)

/-- The unrestricted at-most-three-player strategy-class conclusion. The selected
profile is stationary or has every date/player hazard bounded by the same accuracy;
the terminal Nash bound covers complete behavioral deviations. -/
theorem of_card_le_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι ≤ 3)
    {accuracy : ℝ} (haccuracy : 0 < accuracy) :
    StationaryOrSmallHazardTerminalEquilibrium reward accuracy := by
  by_cases htwo : Fintype.card ι ≤ 2
  · exact Or.inl (exists_stationaryTerminalNash_of_card_le_two reward htwo haccuracy)
  · have hthree : Fintype.card ι = 3 := by omega
    rcases hasQuittingStationaryApproximateEquilibria_or_standardQMatrixSide reward with
      hstationary | hside
    · exact of_stationaryApproximateEquilibria reward hstationary haccuracy
    · exact of_standardQSide_of_card_eq_three reward hthree hside haccuracy

end GameTheory.QuittingThreePlayerStrategyClass
