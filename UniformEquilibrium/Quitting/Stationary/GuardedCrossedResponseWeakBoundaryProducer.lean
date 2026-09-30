import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakHalfResidual
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakInverseUnitPerturbation
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Fixed uniform payoffs from weak inverse and weak half-ceiling raw tables -/

noncomputable section

namespace GameTheory

open QuittingLCPClassification Math.LinearProgramming Math.LinearAlgebra

/-- Packet Theorem C's weak half-ceiling assumptions are finite reward tests. -/
structure QuittingHalfWeakRawGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop where
  lowerFirst : QuittingCrossedWeakLowerRanking reward 0 1
  lowerSecond : QuittingCrossedWeakLowerRanking reward 1 0
  upper : QuittingHalfWeakBernsteinUpper reward

/-- Literal nearby tables produce roots afresh, with all deleted clocks contracting. -/
theorem exists_weakHalfPerturb_stationaryTerminalNash_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingHalfWeakRawGuards reward) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ 3 * epsilon ≤ delta ∧
      ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
        (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
        (quittingGame (quittingCrossedWeakHalfPerturb epsilon reward)).IsεAsymptoticNash
          (quittingTerminalPayoff (quittingCrossedWeakHalfPerturb epsilon reward)) 0
          (quittingStationaryProfile (quittingCrossedWeakHalfPerturb epsilon reward) root) ∧
        (quittingGame (quittingCrossedWeakHalfPerturb epsilon reward)).IsUniformEquilibriumPayoff
          none value := by
  obtain ⟨threshold, hthreshold, hsmall⟩ :=
    exists_pos_strictlyPositiveInverse_sub_offDiagonalOnes
      (quittingSingletonMatrix reward) (by norm_num) hdet.ne' hinverse
  let epsilon := min threshold (delta / 3) / 2
  have hepsilon : 0 < epsilon :=
    half_pos (lt_min hthreshold (by positivity))
  have hbound : epsilon < threshold := by
    have hle : min threshold (delta / 3) ≤ threshold := min_le_left _ _
    dsimp [epsilon]
    linarith
  have hclose : 3 * epsilon ≤ delta := by
    have hle : min threshold (delta / 3) ≤ delta / 3 := min_le_right _ _
    dsimp [epsilon]
    linarith
  obtain ⟨hpositive, hsign, -⟩ := hsmall epsilon hepsilon hbound
  have hnearDet : 0 < (quittingSingletonMatrix
      (quittingCrossedWeakHalfPerturb epsilon reward)).det := by
    rw [quittingSingletonMatrix_weakHalfPerturb]
    exact sign_eq_one_iff.mp (hsign.trans (sign_pos hdet))
  have hnearInverse : ∀ row column,
      0 < (quittingSingletonMatrix (quittingCrossedWeakHalfPerturb epsilon reward))⁻¹
        row column := by
    rw [quittingSingletonMatrix_weakHalfPerturb]
    exact hpositive.2
  have hnearRaw : QuittingHalfStrictRawGuards
      (quittingCrossedWeakHalfPerturb epsilon reward) :=
    ⟨quittingCrossed_strictLowerRanking_of_weakHalfPerturb epsilon hepsilon reward
        0 1 (Or.inl ⟨rfl, rfl⟩) hraw.lowerFirst,
      quittingCrossed_strictLowerRanking_of_weakHalfPerturb epsilon hepsilon reward
        1 0 (Or.inr ⟨rfl, rfl⟩) hraw.lowerSecond,
      quittingHalf_strictBernsteinUpper_of_weakHalfPerturb epsilon hepsilon reward hraw.upper⟩
  obtain ⟨root, value, -, -, -, -, -, -, hcontracts, hnash, hUE⟩ :=
    exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw
      (quittingCrossedWeakHalfPerturb epsilon reward) hnearDet hnearInverse hnearRaw
  exact ⟨epsilon, hepsilon, hclose, root, value, hcontracts, hnash, hUE⟩

/-- Theorem C, half-ceiling branch: one fixed target in the original signed game.
The closure consumer chooses a payoff subsequence before the final accuracy. -/
theorem exists_uniformEquilibriumPayoff_of_weakHalfRaw
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingHalfWeakRawGuards reward) :
    ∃ value : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables reward
  intro delta hdelta
  obtain ⟨epsilon, hepsilon, hclose, root, value, -, -, hUE⟩ :=
    exists_weakHalfPerturb_stationaryTerminalNash_uniformPayoff
      reward hdet hinverse hraw delta hdelta
  refine ⟨quittingCrossedWeakHalfPerturb epsilon reward, ?_, value, hUE⟩
  intro terminal player
  exact (abs_quittingCrossedWeakHalfPerturb_sub_le epsilon hepsilon.le reward
    terminal player).trans hclose

/-- Stationary profiles of the original table have arbitrarily small complete
terminal regret. Every deleted clock contracts; no exact weak-boundary root is claimed. -/
theorem exists_stationary_terminalApproximation_of_weakHalfRaw
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingHalfWeakRawGuards reward) (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∃ root : Fin 4 → PMF Bool,
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
        (quittingStationaryProfile reward root) := by
  obtain ⟨epsilon, hepsilon, hclose, root, value, hcontracts, hnash, -⟩ :=
    exists_weakHalfPerturb_stationaryTerminalNash_uniformPayoff
      reward hdet hinverse hraw (accuracy / 2) (by positivity)
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

variable {n : ℕ}

/-- Nearby singleton-perturbed tables produce exact stationary profiles in every
dimension at least three, under the original strict unit-ceiling guards. -/
theorem exists_singletonPerturb_stationaryTerminalNash_uniformPayoff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hcard : 3 ≤ n) (first second : Fin n) (hdistinct : first ≠ second)
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingCrossedStrictRawUnitGuards reward first second)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ delta ∧
      ∃ root : Fin n → PMF Bool, ∃ value : Payoff (Fin n),
        (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
        (quittingGame (subtractOffOwnSingletonReward epsilon reward)).IsεAsymptoticNash
          (quittingTerminalPayoff (subtractOffOwnSingletonReward epsilon reward)) 0
          (quittingStationaryProfile (subtractOffOwnSingletonReward epsilon reward) root) ∧
        (quittingGame (subtractOffOwnSingletonReward epsilon reward)).IsUniformEquilibriumPayoff
          none value := by
  obtain ⟨threshold, hthreshold, hsmall⟩ :=
    exists_pos_strictlyPositiveInverse_singletonMatrix_rewardApproximation
      reward (by simpa using hcard) hdet.ne' hinverse
  let firstGap := weightOfReward reward {second} first -
    weightOfReward reward (insert first {second}) first
  let secondGap := weightOfReward reward {first} second -
    weightOfReward reward (insert second {first}) second
  have hfirstGap : 0 < firstGap := by
    have h := hraw.upperFirst ∅ (Finset.empty_subset _)
    simpa [firstGap] using sub_pos.mpr h
  have hsecondGap : 0 < secondGap := by
    have h := hraw.upperSecond ∅ (Finset.empty_subset _)
    simpa [secondGap] using sub_pos.mpr h
  let epsilon := min (min threshold delta) (min firstGap secondGap) / 2
  have hepsilon : 0 < epsilon :=
    half_pos (lt_min (lt_min hthreshold hdelta) (lt_min hfirstGap hsecondGap))
  have hbound : epsilon < threshold := by
    have hle := (min_le_left (min threshold delta) (min firstGap secondGap)).trans
      (min_le_left threshold delta)
    dsimp [epsilon]
    linarith
  have hclose : epsilon ≤ delta := by
    have hle := (min_le_left (min threshold delta) (min firstGap secondGap)).trans
      (min_le_right threshold delta)
    dsimp [epsilon]
    linarith
  have hfirst : epsilon < firstGap := by
    have hle := (min_le_right (min threshold delta) (min firstGap secondGap)).trans
      (min_le_left firstGap secondGap)
    dsimp [epsilon]
    linarith
  have hsecond : epsilon < secondGap := by
    have hle := (min_le_right (min threshold delta) (min firstGap secondGap)).trans
      (min_le_right firstGap secondGap)
    dsimp [epsilon]
    linarith
  obtain ⟨hpositive, hsign, -⟩ := hsmall epsilon hepsilon hbound
  have hnearDet : 0 < (quittingSingletonMatrix
      (subtractOffOwnSingletonReward epsilon reward)).det :=
    sign_eq_one_iff.mp (hsign.trans (sign_pos hdet))
  have hnearRaw : QuittingCrossedStrictRawUnitGuards
      (subtractOffOwnSingletonReward epsilon reward) first second :=
    ⟨quittingCrossed_strictLowerRanking_subtractOffOwnSingletonReward
        epsilon hepsilon.le reward first second hraw.lowerFirst,
      quittingCrossed_strictLowerRanking_subtractOffOwnSingletonReward
        epsilon hepsilon.le reward second first hraw.lowerSecond,
      quittingCrossed_strictUnitJoining_subtractOffOwnSingletonReward
        epsilon reward first second hdistinct hraw.upperFirst hfirst,
      quittingCrossed_strictUnitJoining_subtractOffOwnSingletonReward
        epsilon reward second first hdistinct.symm hraw.upperSecond hsecond⟩
  obtain ⟨root, value, -, -, -, -, -, -, hcontracts, hnash, hUE⟩ :=
    exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_strictRawUnit
      (subtractOffOwnSingletonReward epsilon reward) first second hdistinct
      hnearDet hpositive.2 hnearRaw
  exact ⟨epsilon, hepsilon, hclose, root, value, hcontracts, hnash, hUE⟩

/-- Theorem C's strict unit-ceiling branch: nonnegative full inverse is enough
for one fixed payoff, in every dimension at least three. -/
theorem exists_uniformEquilibriumPayoff_of_strictRawUnit_nonnegativeInverse
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hcard : 3 ≤ n) (first second : Fin n) (hdistinct : first ≠ second)
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingCrossedStrictRawUnitGuards reward first second) :
    ∃ value : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables reward
  intro delta hdelta
  obtain ⟨epsilon, hepsilon, hclose, root, value, -, -, hUE⟩ :=
    exists_singletonPerturb_stationaryTerminalNash_uniformPayoff
      reward hcard first second hdistinct hdet hinverse hraw delta hdelta
  refine ⟨subtractOffOwnSingletonReward epsilon reward, ?_, value, hUE⟩
  intro terminal player
  exact (abs_subtractOffOwnSingletonReward_sub_le epsilon reward terminal player).trans
    (by simpa [abs_of_pos hepsilon] using hclose)

/-- Contracting stationary profiles in the original unit-ceiling table have
complete terminal regret tending to zero. -/
theorem exists_stationary_terminalApproximation_of_strictRawUnit_nonnegativeInverse
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hcard : 3 ≤ n) (first second : Fin n) (hdistinct : first ≠ second)
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hraw : QuittingCrossedStrictRawUnitGuards reward first second)
    (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∃ root : Fin n → PMF Bool,
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) accuracy
        (quittingStationaryProfile reward root) := by
  obtain ⟨epsilon, hepsilon, hclose, root, value, hcontracts, hnash, -⟩ :=
    exists_singletonPerturb_stationaryTerminalNash_uniformPayoff
      reward hcard first second hdistinct hdet hinverse hraw (accuracy / 2) (by positivity)
  have hrewardClose : ∀ terminal player,
      |subtractOffOwnSingletonReward epsilon reward terminal player -
        reward terminal player| ≤ epsilon := by
    intro terminal player
    simpa [abs_of_pos hepsilon] using
      abs_subtractOffOwnSingletonReward_sub_le epsilon reward terminal player
  have hnear := IsεAsymptoticNash.of_reward_close
    (subtractOffOwnSingletonReward epsilon reward) reward
    (quittingStationaryProfile (subtractOffOwnSingletonReward epsilon reward) root)
    hepsilon.le hrewardClose hnash
  refine ⟨root, hcontracts, ?_⟩
  intro who deviation
  have h := hnear who deviation
  change quittingTerminalPayoff reward
      (Function.update (quittingStationaryProfile reward root) who deviation) who ≤
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) who +
      (0 + 2 * epsilon) at h
  linarith

end GameTheory
