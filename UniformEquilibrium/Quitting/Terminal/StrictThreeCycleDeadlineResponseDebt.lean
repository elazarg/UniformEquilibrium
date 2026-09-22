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

/-- Rebase a pure-time reply on the fixed root schedule to the profile
started at a later live date. -/
private theorem pureTimeTerminalValue_eq_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (choice : Option ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (quittingAbsolutePureTime start choice) start =
      quittingRootSequencePureTimeTerminalValue reward
        (fun time => roots (start + time)) who choice 0 := by
  have hh : ∀ time,
      quittingPureTimeHazard (quittingAbsolutePureTime start choice)
          (start + time) = quittingPureTimeHazard choice time := by
    intro time
    cases choice with
    | none => rfl
    | some delay =>
        simp [quittingAbsolutePureTime, quittingPureTimeHazard]
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
  rw [quittingRootSequenceTerminalValue_eq_shift]
  congr 1
  funext time player
  simp only [quittingRootSequenceUpdate]
  rw [hh]

/-- First-disagreement identity when the source profile starts at an
arbitrary live date. -/
private theorem pureTimeGain_eq_survival_mul_at
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + fuel)) start -
      quittingRootSequencePureTimeTerminalValue reward roots who none start =
    quittingOpponentSurvivalWeight roots who start fuel *
      (quittingFixedOpponentsQuitValue reward roots who (start + fuel) -
        quittingRootSequencePureTimeTerminalValue reward roots who none
          (start + fuel)) := by
  have hnever : ∀ start fuel,
      quittingRootSequencePureTimeTerminalValue reward roots who none start =
        quittingLiveLedgerAccum reward roots who start fuel +
          quittingOpponentSurvivalWeight roots who start fuel *
            quittingRootSequencePureTimeTerminalValue reward roots who none
              (start + fuel) := by
    intro start fuel
    induction fuel generalizing start with
    | zero => simp [quittingOpponentSurvivalWeight, quittingLiveLedgerAccum]
    | succ fuel ih =>
        rw [quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents,
          ih (start + 1), quittingLiveLedgerAccum_shift,
          quittingOpponentSurvivalWeight_shift]
        rw [show start + (fuel + 1) = start + 1 + fuel by omega]
        ring
  rw [quittingRootSequencePureTimeTerminalValue_some_add, hnever]
  ring

/-- A positive strict-cycle response gap is realized by an actual finite
pure-time quit date, with the quantitative vertex-survival bound. -/
theorem exists_pureTimeDeviationGain_ge_of_strictThreeCycle_from_start
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : Fin 3 ↪ ι) (owner : ℕ → Fin 3)
    (start : ℕ)
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
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpositive : 0 < quittingStrictThreeCycleInverseRowDeficit
      reward child a b c d e f outside - 2 * M * delta) :
    ∃ date : ℕ, start ≤ date ∧
      a * d * e / (b * c * f) ≤
        quittingOpponentSurvivalWeight roots outside start (date - start) ∧
      a * d * e / (b * c * f) *
          (quittingStrictThreeCycleInverseRowDeficit
            reward child a b c d e f outside - 2 * M * delta) ≤
        quittingTerminalPayoff reward
            (Function.update (quittingRootSequenceProfile reward roots start) outside
              (quittingPureTimeBehaviorStrategy reward outside
                (some (date - start)))) outside -
          quittingTerminalPayoff reward
            (quittingRootSequenceProfile reward roots start) outside := by
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
  have hdeficitPositive : 0 < deficit := by
    have hdelta : 0 ≤ delta :=
      ENNReal.toReal_nonneg.trans (hhazard 0)
    have hM : 0 ≤ M := (abs_nonneg _).trans
      (hreward (quittingSingletonTerminal outside) outside)
    have hcost : 0 ≤ 2 * M * delta :=
      mul_nonneg (mul_nonneg (by norm_num) hM) hdelta
    change 0 < deficit - 2 * M * delta at hpositive
    linarith
  · obtain ⟨j, hj⟩ := exists_inverseRowDeficit_vertex
      reward child a b c d e f outside
    have hvisits := exists_vertex_after_with_survival_ge ha hb hc hd he hf hgap
    rw [← hmatrix] at hvisits
    obtain ⟨date, hdate, hvertex, hsurvival⟩ := hvisits path start j
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
    have hsurvivalEq :
        quittingOpponentSurvivalWeight roots outside start (date - start) =
          Math.survivalProduct (fun time => 1 - path.hazard time)
            start (date - start) := by
      rw [quittingOpponentSurvivalWeight_eq_survivalProduct]
      apply congrArg (Math.survivalProduct · start (date - start))
      funext time
      have hmass := quittingFixedOpponentsContinueMass_eq_of_soloRoot roots
        (hsolo time) (houtside (owner time))
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (roots time) (child (owner time))
      dsimp only [path, normalizedSingletonPathOfRootSequence]
      rw [hmass]
      linarith
    have hsurvivalBound : a * d * e / (b * c * f) ≤
        quittingOpponentSurvivalWeight roots outside start (date - start) := by
      rw [hsurvivalEq]
      simpa using hsurvival
    have hexact := pureTimeGain_eq_survival_mul_at
      reward roots outside start (date - start)
    rw [Nat.add_sub_of_le hdate] at hexact
    have hscaled := mul_le_mul hsurvivalBound hgain
      (le_of_lt hpositive)
      (quittingOpponentSurvivalWeight_nonneg roots outside start (date - start))
    have hpureTime : a * d * e / (b * c * f) * (deficit - 2 * M * delta) ≤
        quittingRootSequencePureTimeTerminalValue reward roots outside
            (some date) start -
          quittingRootSequencePureTimeTerminalValue reward roots outside none start := by
      calc
        _ ≤ quittingOpponentSurvivalWeight roots outside start (date - start) *
            (quittingFixedOpponentsQuitValue reward roots outside date -
              quittingRootSequencePureTimeTerminalValue reward roots outside none date) :=
          hscaled
        _ = _ := hexact.symm
    have hprescribed : quittingTerminalPayoff reward
        (quittingRootSequenceProfile reward roots start) outside =
        quittingRootSequencePureTimeTerminalValue reward roots outside none start := by
      unfold quittingRootSequencePureTimeTerminalValue
        quittingRootSequenceHazardTerminalValue quittingRootSequenceTerminalValue
      rw [hupdate]
    have hdeviation : quittingTerminalPayoff reward
        (Function.update (quittingRootSequenceProfile reward roots start) outside
          (quittingPureTimeBehaviorStrategy reward outside
            (some (date - start)))) outside =
        quittingRootSequencePureTimeTerminalValue reward roots outside
          (some date) start := by
      rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
        quittingRootSequenceProfile_eq_shift,
        quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
      rw [← pureTimeTerminalValue_eq_shift reward roots outside start
        (some (date - start))]
      simp only [quittingAbsolutePureTime, Nat.add_sub_of_le hdate]
    refine ⟨date, hdate, hsurvivalBound, ?_⟩
    simpa only [hdeviation, hprescribed] using hpureTime

/-- Zero-start specialization of the arbitrary-start deterministic reply. -/
theorem exists_pureTimeDeviationGain_ge_of_strictThreeCycle
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
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpositive : 0 < quittingStrictThreeCycleInverseRowDeficit
      reward child a b c d e f outside - 2 * M * delta) :
    ∃ date : ℕ,
      a * d * e / (b * c * f) ≤
        quittingOpponentSurvivalWeight roots outside 0 date ∧
      a * d * e / (b * c * f) *
          (quittingStrictThreeCycleInverseRowDeficit
            reward child a b c d e f outside - 2 * M * delta) ≤
        quittingTerminalPayoff reward
            (Function.update (quittingRootSequenceProfile reward roots 0) outside
              (quittingPureTimeBehaviorStrategy reward outside (some date))) outside -
          quittingTerminalPayoff reward
            (quittingRootSequenceProfile reward roots 0) outside := by
  obtain ⟨date, _, hsurvival, hgain⟩ :=
    exists_pureTimeDeviationGain_ge_of_strictThreeCycle_from_start
      reward roots child owner 0 outside houtside a b c d e f M delta
      ha hb hc hd he hf hgap hmatrix hsolo hquit hhazard habsorb
      hfloor htie hreward hpositive
  exact ⟨date, by simpa using hsurvival, by simpa using hgain⟩

/-- The concrete relative pure-time reply bounds full behavioral response debt
at any live start on the same absorbing strict-cycle solo schedule. -/
theorem quittingBehaviorDeviationDebt_ge_of_strictThreeCycle_from_start
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : Fin 3 ↪ ι) (owner : ℕ → Fin 3)
    (start : ℕ)
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
          (quittingRootSequenceProfile reward roots start) outside -
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward roots start) outside := by
  have hbaseline : quittingTerminalPayoff reward
      (quittingRootSequenceProfile reward roots start) outside ≤
      quittingBehaviorDeviationPayoffCap reward
        (quittingRootSequenceProfile reward roots start) outside := by
    unfold quittingBehaviorDeviationPayoffCap
    apply le_csSup
    · exact bddAbove_range_quittingTerminalPayoff_update reward
        (quittingRootSequenceProfile reward roots start) outside
    · exact ⟨(quittingRootSequenceProfile reward roots start) outside, by
        simp only [Function.update_eq_self]⟩
  by_cases hpositive : 0 < quittingStrictThreeCycleInverseRowDeficit
      reward child a b c d e f outside - 2 * M * delta
  · obtain ⟨date, _, _, hgain⟩ :=
      exists_pureTimeDeviationGain_ge_of_strictThreeCycle_from_start
        reward roots child owner start outside houtside a b c d e f M delta
        ha hb hc hd he hf hgap hmatrix hsolo hquit hhazard habsorb
        hfloor htie hreward hpositive
    have hcap : quittingTerminalPayoff reward
        (Function.update (quittingRootSequenceProfile reward roots start) outside
          (quittingPureTimeBehaviorStrategy reward outside
            (some (date - start)))) outside ≤
        quittingBehaviorDeviationPayoffCap reward
          (quittingRootSequenceProfile reward roots start) outside := by
      unfold quittingBehaviorDeviationPayoffCap
      apply le_csSup
      · exact bddAbove_range_quittingTerminalPayoff_update reward
          (quittingRootSequenceProfile reward roots start) outside
      · exact ⟨quittingPureTimeBehaviorStrategy reward outside
          (some (date - start)), rfl⟩
    rw [max_eq_left hpositive.le]
    linarith
  · rw [max_eq_right (le_of_not_gt hpositive), mul_zero]
    linarith

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
  exact quittingBehaviorDeviationDebt_ge_of_strictThreeCycle_from_start
    reward roots child owner 0 outside houtside a b c d e f M delta
    ha hb hc hd he hf hgap hmatrix hsolo hquit hhazard habsorb
    hfloor htie hreward

end GameTheory
