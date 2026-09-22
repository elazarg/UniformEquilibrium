import UniformEquilibrium.Quitting.Cycles.SoloRootSequenceValues
import UniformEquilibrium.Quitting.Paths.NormalizedSingletonPath
import UniformEquilibrium.Quitting.Paths.SurvivalWeightedSuffixRegret
import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw

/-!
# Deterministic deadline debt on an absorbing strict three-cycle

This is the game-semantic adapter for the quantitative strict-cycle response
bound.  The normalized path and its vertex-survival theorem supply the date;
the deviation is the literal pure-time quit at that date.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming Math.LinearProgramming.ThreeCycleInverseFormulas
open QuittingLCPClassification _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Largest negative normalized coordinate of an outsider's actual inverse
row on the strict three-cycle child. -/
def quittingStrictThreeCycleInverseRowDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child : Fin 3 ↪ ι) (a b c d e f : ℝ) (who : ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j =>
    max (-Matrix.vecMul
      (fun i => quittingSingletonMatrix reward who (child i))
      ((quittingSingletonMatrix reward).submatrix child child)⁻¹ j /
        columnWeight a b c d e f j) 0

omit [Fintype ι] [DecidableEq ι] in
private theorem exists_inverseRowDeficit_vertex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child : Fin 3 ↪ ι) (a b c d e f : ℝ) (who : ι) :
    ∃ j : Fin 3,
      max (-Matrix.vecMul
        (fun i => quittingSingletonMatrix reward who (child i))
        ((quittingSingletonMatrix reward).submatrix child child)⁻¹ j /
          columnWeight a b c d e f j) 0 =
        quittingStrictThreeCycleInverseRowDeficit reward child a b c d e f who := by
  unfold quittingStrictThreeCycleInverseRowDeficit
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ) (f := fun j : Fin 3 =>
      max (-Matrix.vecMul
        (fun i => quittingSingletonMatrix reward who (child i))
        ((quittingSingletonMatrix reward).submatrix child child)⁻¹ j /
          columnWeight a b c d e f j) 0) Finset.univ_nonempty
  exact ⟨j, hj.symm⟩

private theorem pureTimeDebt_ge_survival_mul_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (date : ℕ)
    {C gain : ℝ}
    (hsurvival : C ≤ quittingOpponentSurvivalWeight roots who 0 date)
    (hgain : gain ≤ quittingFixedOpponentsQuitValue reward roots who date -
      quittingRootSequencePureTimeTerminalValue reward roots who none date) :
    C * max gain 0 ≤
      quittingPureTimeBestResponseCap reward roots who 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who none 0 := by
  have hnever : quittingRootSequencePureTimeTerminalValue reward roots who none 0 ≤
      quittingPureTimeBestResponseCap reward roots who 0 := by
    unfold quittingPureTimeBestResponseCap
    apply le_csSup
    · exact bddAbove_range_quittingRootSequenceRelativePureTimeTerminalValue
        reward roots who 0
    · exact ⟨none, by simp [quittingRootSequenceRelativePureTimeTerminalValue]⟩
  by_cases hpositive : 0 < gain
  · have hexact :=
      quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
        reward roots who date none
    simp only [quittingAbsolutePureTime,
      quittingRootSequenceRelativePureTimeTerminalValue] at hexact
    have hquit : quittingRootSequencePureTimeTerminalValue reward roots who
        (some date) 0 ≤ quittingPureTimeBestResponseCap reward roots who 0 := by
      unfold quittingPureTimeBestResponseCap
      apply le_csSup
      · exact bddAbove_range_quittingRootSequenceRelativePureTimeTerminalValue
          reward roots who 0
      · exact ⟨some date, by
          simp [quittingRootSequenceRelativePureTimeTerminalValue]⟩
    have hweight := quittingOpponentSurvivalWeight_nonneg roots who 0 date
    have hscaled := mul_le_mul hsurvival hgain hpositive.le hweight
    rw [max_eq_left hpositive.le]
    linarith
  · rw [max_eq_right (le_of_not_gt hpositive), mul_zero]
    linarith

/-- On a solo child row, a spectator who quits now loses at most twice the
reward bound times the active child's hazard relative to quitting alone. -/
private theorem fixedOpponentsQuitValue_ge_singleton_sub_two_mul_hazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} {time : ℕ}
    (hsolo : ∀ player, player ≠ owner → roots time player = PMF.pure false)
    (hne : other ≠ owner) {M delta : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hhazard : (roots time owner true).toReal ≤ delta) :
    quittingSoloReward reward other other - 2 * M * delta ≤
      quittingFixedOpponentsQuitValue reward roots other time := by
  rw [quittingFixedOpponentsQuitValue_eq_of_soloRoot reward roots hsolo hne]
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (roots time) owner
  have hsingle := hreward (quittingSingletonTerminal other) other
  have hcollision := hreward ⟨{owner, other}, by simp⟩ other
  have hM : 0 ≤ M := (abs_nonneg _).trans hsingle
  have htrue : 0 ≤ (roots time owner true).toReal := ENNReal.toReal_nonneg
  have hdelta : 0 ≤ delta := htrue.trans hhazard
  unfold quittingSingletonCollisionReward quittingSoloReward
  rw [show (roots time owner false).toReal =
      1 - (roots time owner true).toReal by linarith]
  have hlowerSingle := neg_abs_le (reward (quittingSingletonTerminal other) other)
  have hlowerCollision :=
    neg_abs_le (reward ⟨{owner, other}, by simp⟩ other)
  have hsingleUpper : reward (quittingSingletonTerminal other) other ≤ M :=
    (abs_le.mp hsingle).2
  have hsingleUpper' : reward ⟨{other}, by simp⟩ other ≤ M := by
    simpa [quittingSingletonTerminal] using hsingleUpper
  have hcollisionLower : -M ≤ reward ⟨{owner, other}, by simp⟩ other :=
    (abs_le.mp hcollision).1
  have hscaledCollision :
      (roots time owner true).toReal * (-M) ≤
        (roots time owner true).toReal *
          reward ⟨{owner, other}, by simp⟩ other :=
    mul_le_mul_of_nonneg_left hcollisionLower htrue
  have hscaledSingleton :
      (roots time owner true).toReal * reward ⟨{other}, by simp⟩ other ≤
        (roots time owner true).toReal * M :=
    mul_le_mul_of_nonneg_left hsingleUpper' htrue
  have hscaledDelta :
      2 * M * (roots time owner true).toReal ≤ 2 * M * delta :=
    mul_le_mul_of_nonneg_left hhazard (by positivity : 0 ≤ 2 * M)
  nlinarith

/-- An actual absorbing strict-cycle solo schedule forces the outsider's full
behavioral response debt to obey the canonical deterministic-deadline bound. -/
theorem quittingBehaviorDeviationDebt_ge_of_strictThreeCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : Fin 3 ↪ ι) (owner : ℕ → Fin 3)
    (outside : ι) (houtside : ∀ i, outside ≠ child i)
    (a b c d e f M delta : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (hmatrix : (quittingSingletonMatrix reward).submatrix child child =
      directedCycleMatrix a b c d e f)
    (hsolo : ∀ time other, other ≠ child (owner time) →
      roots time other = PMF.pure false)
    (hquit : ∀ time, (roots time (child (owner time)) true).toReal < 1)
    (hhazard : ∀ time,
      (roots time (child (owner time)) true).toReal ≤ delta)
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0)
    (hfloor : ∀ time i, quittingSoloReward reward (child i) (child i) ≤
      quittingRootSequenceTerminalValue reward roots (child i) time)
    (htie : ∀ time, 0 < (roots time (child (owner time)) true).toReal →
      quittingRootSequenceTerminalValue reward roots (child (owner time)) time =
        quittingSoloReward reward (child (owner time)) (child (owner time)))
    (hreward : ∀ S player, |reward S player| ≤ M) :
    a * d * e / (b * c * f) *
        max (quittingStrictThreeCycleInverseRowDeficit
          reward child a b c d e f outside - 2 * M * delta) 0 ≤
      quittingBehaviorDeviationPayoffCap reward
          (quittingRootSequenceProfile reward roots 0) outside -
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward roots 0) outside := by
  let weight := columnWeight a b c d e f
  have hweight : ∀ i, 0 < weight i :=
    columnWeight_pos ha hb hc hd he hf hgap
  have hbalance : Matrix.vecMul weight
      ((quittingSingletonMatrix reward).submatrix child child) = 1 := by
    rw [hmatrix]
    exact columnWeight_vecMul a b c d e f hgap.ne'
  let path := normalizedSingletonPathOfRootSequence reward roots child owner
    hsolo hquit habsorb weight hweight hbalance hfloor htie
  let deficit := quittingStrictThreeCycleInverseRowDeficit
    reward child a b c d e f outside
  have hdeficit : 0 ≤ deficit := by
    unfold deficit quittingStrictThreeCycleInverseRowDeficit
    exact (le_max_right _ _).trans <| Finset.le_sup'
      (fun j : Fin 3 => max
        (-Matrix.vecMul
          (fun i => quittingSingletonMatrix reward outside (child i))
          ((quittingSingletonMatrix reward).submatrix child child)⁻¹ j /
            columnWeight a b c d e f j) 0) (Finset.mem_univ 0)
  by_cases hdeficitPositive : 0 < deficit
  · obtain ⟨j, hj⟩ := exists_inverseRowDeficit_vertex
      reward child a b c d e f outside
    have hvisits := exists_vertex_after_with_survival_ge ha hb hc hd he hf hgap
    rw [← hmatrix] at hvisits
    obtain ⟨date, _, hvertex, hsurvival⟩ := hvisits path 0 j
    have hdet : ((quittingSingletonMatrix reward).submatrix child child).det ≠ 0 := by
      rw [hmatrix, directedCycleMatrix_det]
      exact hgap.ne'
    let coefficient := Matrix.vecMul
      (fun i => quittingSingletonMatrix reward outside (child i))
      ((quittingSingletonMatrix reward).submatrix child child)⁻¹
    have hjNegative : max (-(coefficient j / weight j)) 0 = deficit := by
      simpa only [coefficient, weight, deficit, neg_div] using hj
    have hjValue : -(coefficient j / weight j) = deficit := by
      rw [max_eq_left] at hjNegative
      · exact hjNegative
      · by_contra hnot
        have : max (-(coefficient j / weight j)) 0 = 0 :=
          max_eq_right (le_of_not_ge hnot)
        linarith
    have hsurplus : quittingRootSequenceSingletonSurplus
        reward roots date outside = coefficient j / weight j := by
      have hinverse := quittingRootSequenceSingletonSurplus_eq_inverseRow
        reward roots child owner hsolo hquit habsorb hdet outside date
      calc
        quittingRootSequenceSingletonSurplus reward roots date outside =
            dotProduct coefficient (path.value date) := by
          unfold dotProduct path normalizedSingletonPathOfRootSequence
          simpa [coefficient] using hinverse
        _ = dotProduct coefficient
            (Pi.single j (1 / weight j) : Fin 3 → ℝ) := by rw [hvertex]
        _ = coefficient j / weight j := by
          rw [dotProduct_single]
          ring
    have hupdate : quittingRootSequenceUpdate roots outside
        (quittingPureTimeHazard none) = roots := by
      funext time player
      by_cases hplayer : player = outside
      · subst player
        simp [quittingRootSequenceUpdate, hsolo time outside
          (houtside (owner time))]
      · simp [quittingRootSequenceUpdate, Function.update_of_ne hplayer]
    have hnever : quittingRootSequencePureTimeTerminalValue reward roots outside
        none date = quittingSoloReward reward outside outside - deficit := by
      unfold quittingRootSequencePureTimeTerminalValue
        quittingRootSequenceHazardTerminalValue
      rw [hupdate]
      dsimp only [quittingRootSequenceSingletonSurplus] at hsurplus
      linarith [hjValue]
    have hownerNe : outside ≠ child (owner date) := houtside _
    have hquitLower := fixedOpponentsQuitValue_ge_singleton_sub_two_mul_hazard
      reward roots (hsolo date) hownerNe hreward (hhazard date)
    have hgain : deficit - 2 * M * delta ≤
        quittingFixedOpponentsQuitValue reward roots outside date -
          quittingRootSequencePureTimeTerminalValue reward roots outside none date := by
      rw [hnever]
      linarith
    have hsurvivalEq : quittingOpponentSurvivalWeight roots outside 0 date =
        Math.survivalProduct (fun time => 1 - path.hazard time) 0 date := by
      rw [quittingOpponentSurvivalWeight_eq_survivalProduct]
      apply congrArg (Math.survivalProduct · 0 date)
      funext time
      have hmass := quittingFixedOpponentsContinueMass_eq_of_soloRoot roots
        (hsolo time) (houtside (owner time))
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (roots time) (child (owner time))
      dsimp only [path, normalizedSingletonPathOfRootSequence]
      rw [hmass]
      linarith
    have hcore := pureTimeDebt_ge_survival_mul_max
      (C := a * d * e / (b * c * f)) reward roots outside date
      (by rw [hsurvivalEq]; simpa using hsurvival) hgain
    rw [quittingBehaviorDeviationPayoffCap_eq_pureTime]
    unfold quittingBehaviorPureTimePayoffCap quittingBehaviorPureTimePayoff
    rw [show sSup (Set.range fun choice : Option ℕ =>
        quittingTerminalPayoff reward
          (Function.update (quittingRootSequenceProfile reward roots 0) outside
            (quittingPureTimeBehaviorStrategy reward outside choice)) outside) =
        quittingPureTimeBestResponseCap reward roots outside 0 by
      unfold quittingPureTimeBestResponseCap
      apply congrArg sSup
      apply congrArg Set.range
      funext choice
      rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
      simp only [quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
        quittingRootSequenceRelativePureTimeTerminalValue,
        quittingAbsolutePureTime_zero]]
    simpa [deficit, quittingRootSequencePureTimeTerminalValue,
      quittingRootSequenceHazardTerminalValue, quittingRootSequenceTerminalValue,
      hupdate] using hcore
  · have hzero : deficit = 0 := le_antisymm (le_of_not_gt hdeficitPositive) hdeficit
    have hdelta : 0 ≤ delta := by
      exact (show 0 ≤ (roots 0 (child (owner 0)) true).toReal from
        ENNReal.toReal_nonneg).trans (hhazard 0)
    have hM : 0 ≤ M := (abs_nonneg _).trans
      (hreward (quittingSingletonTerminal outside) outside)
    change a * d * e / (b * c * f) * max (deficit - 2 * M * delta) 0 ≤ _
    rw [hzero, zero_sub, max_eq_right (neg_nonpos.mpr (mul_nonneg
      (mul_nonneg (by norm_num) hM) hdelta)), mul_zero]
    have hnever : quittingTerminalPayoff reward
        (quittingRootSequenceProfile reward roots 0) outside ≤
        quittingBehaviorDeviationPayoffCap reward
          (quittingRootSequenceProfile reward roots 0) outside := by
      unfold quittingBehaviorDeviationPayoffCap
      apply le_csSup
      · exact bddAbove_range_quittingTerminalPayoff_update reward
          (quittingRootSequenceProfile reward roots 0) outside
      · exact ⟨(quittingRootSequenceProfile reward roots 0) outside, by
          simp only [Function.update_eq_self]
        ⟩
    linarith

end GameTheory
