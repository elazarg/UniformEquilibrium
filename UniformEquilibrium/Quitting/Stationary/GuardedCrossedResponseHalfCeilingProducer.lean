import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingAdapter

/-! # The four-player strict half-ceiling raw-table producer -/

noncomputable section

namespace GameTheory

open Math.LinearProgramming QuittingLCPClassification

/-- Packet Theorem B, strict half-ceiling branch: the actual nine-coefficient
tests on both reward rows produce an exact stationary behavioral Nash profile
and a fixed uniform-equilibrium payoff. -/
theorem exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 < (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingHalfStrictRawGuards reward) :
    ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      0 < hazardOfRoot root 0 ∧ hazardOfRoot root 0 < 1 / 2 ∧
      0 < hazardOfRoot root 1 ∧ hazardOfRoot root 1 < 1 / 2 ∧
      (∃ outsider, outsider ≠ 0 ∧ outsider ≠ 1 ∧
        0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff reward (quittingStationaryProfile reward root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0 (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  have hreciprocalFirst :=
    quittingCrossed_reciprocal_pos_of_lowerRanking_positiveInverse
      reward 0 1 hdet hinverse hraw.lowerFirst
  have hreciprocalSecond :=
    quittingCrossed_reciprocal_pos_of_lowerRanking_positiveInverse
      reward 1 0 hdet hinverse hraw.lowerSecond
  obtain ⟨hR0, hdegree⟩ :=
    quittingCrossedSingletonMatrix_r0_degree_neg_one_of_positiveInverse
      reward 0 1 (by decide) hdet hinverse
  have hdegreeNe : r0Degree (quittingCrossedSingletonMatrix reward 0 1) hR0 ≠ 1 := by
    rw [hdegree]
    norm_num
  exact exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards
    reward 0 1 (by decide) (1 / 2) (by norm_num) (by norm_num)
      (quittingCrossedSourceGuards_of_halfStrictRawGuards reward hraw)
      hreciprocalFirst hreciprocalSecond hR0 hdegreeNe

end GameTheory
