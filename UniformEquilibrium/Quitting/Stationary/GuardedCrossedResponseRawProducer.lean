import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawAdapter

/-! # Strict raw-table crossed degree escape -/

noncomputable section

namespace GameTheory

open Math.LinearProgramming QuittingLCPClassification

variable {n : ℕ}

/-- Packet (L) makes every selected-to-outsider singleton comparison negative. -/
theorem quittingCrossed_lowerRanking_outsider_singleton_neg
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient partner outsider : Fin n)
    (houtsider : outsider ∈ quittingCrossedRawOutsiders recipient partner)
    (hranking : QuittingCrossedStrictLowerRanking reward recipient partner) :
    quittingSingletonMatrix reward recipient outsider < 0 := by
  have hr := hranking ∅ {outsider}
    (Finset.empty_subset _)
    (Finset.singleton_subset_iff.mpr houtsider)
    (Finset.singleton_nonempty outsider)
  have hcomparison :
      reward ⟨{outsider}, Finset.singleton_nonempty outsider⟩ recipient <
        reward ⟨{recipient}, Finset.singleton_nonempty recipient⟩ recipient := by
    simpa [weightOfReward] using hr
  dsimp [quittingSingletonMatrix]
  linarith

/-- The positive full inverse rules out a nonpositive entire selected row;
the strict lower comparisons already make every outsider entry negative. -/
theorem quittingCrossed_reciprocal_pos_of_lowerRanking_positiveInverse
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient partner : Fin n)
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 < (quittingSingletonMatrix reward)⁻¹ row column)
    (hranking : QuittingCrossedStrictLowerRanking reward recipient partner) :
    0 < quittingSingletonMatrix reward recipient partner := by
  by_contra hnot
  have hpartner : quittingSingletonMatrix reward recipient partner ≤ 0 := le_of_not_gt hnot
  have hrow : ∀ column, quittingSingletonMatrix reward recipient column ≤ 0 := by
    intro column
    by_cases hself : column = recipient
    · subst column
      simp [quittingSingletonMatrix]
    by_cases hcol : column = partner
    · subst column
      exact hpartner
    · have hout : column ∈ quittingCrossedRawOutsiders recipient partner := by
        simp [quittingCrossedRawOutsiders, hself, hcol]
      exact (quittingCrossed_lowerRanking_outsider_singleton_neg
        reward recipient partner column hout hranking).le
  have hproduct : (quittingSingletonMatrix reward *
      (quittingSingletonMatrix reward)⁻¹) recipient recipient ≤ 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_nonpos
    intro column _
    exact mul_nonpos_of_nonpos_of_nonneg (hrow column)
      (hinverse column recipient).le
  have hidentity := congrFun (congrFun
    (Matrix.mul_nonsing_inv (quittingSingletonMatrix reward)
      (isUnit_iff_ne_zero.mpr hdet.ne')) recipient) recipient
  simp only [Matrix.one_apply_eq] at hidentity
  linarith

/-- Packet Theorem B, strict unit-ceiling branch: finite raw reward tests and
strict inverse positivity yield an exact stationary behavioral equilibrium
and one fixed uniform-equilibrium payoff. -/
theorem exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_strictRawUnit
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 < (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingCrossedStrictRawUnitGuards reward first second) :
    ∃ root : Fin n → PMF Bool, ∃ value : Payoff (Fin n),
      0 < hazardOfRoot root first ∧ hazardOfRoot root first < 1 ∧
      0 < hazardOfRoot root second ∧ hazardOfRoot root second < 1 ∧
      (∃ outsider, outsider ≠ first ∧ outsider ≠ second ∧
        0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff reward (quittingStationaryProfile reward root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0 (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  have hreciprocalFirst :=
    quittingCrossed_reciprocal_pos_of_lowerRanking_positiveInverse
      reward first second hdet hinverse hraw.lowerFirst
  have hreciprocalSecond :=
    quittingCrossed_reciprocal_pos_of_lowerRanking_positiveInverse
      reward second first hdet hinverse hraw.lowerSecond
  obtain ⟨hR0, hdegree⟩ :=
    quittingCrossedSingletonMatrix_r0_degree_neg_one_of_positiveInverse
      reward first second hdistinct hdet hinverse
  have hdegreeNe : r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 ≠
      1 := by
    rw [hdegree]
    norm_num
  exact exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards
    reward first second hdistinct 1 (by norm_num) (by norm_num)
      (quittingCrossedSourceGuards_of_strictRawUnitGuards reward first second
        hdistinct hraw)
      hreciprocalFirst hreciprocalSecond hR0 hdegreeNe

end GameTheory
