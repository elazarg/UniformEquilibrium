import UniformEquilibrium.Quitting.Paths.ExecutableRationalWeakSubsetSelection
import UniformEquilibrium.Quitting.Paths.RationalUnpreemptedSoloExit

/-! # The literal executable weak-exclusion preemption dispatch

Finite rational comparisons choose between the printed unpreempted solo word
and the canonical all-preempted selected-owner renewal. Correctness retains
that computed word, its independent finite/Never laws and its full caps.
Only eligible owners need nonnegative singletons; accuracy need not be at most M.
-/

namespace GameTheory

variable {players : ℕ}

private theorem exists_unpreemptedEligibleOwner
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hpreempted : ¬ RationalQuittingOwnersStrictPreempted reward owners) :
    ∃ owner, owner ∈ owners ∧ ∀ blocker,
      reward (quittingSingletonTerminal blocker) blocker ≤
        reward (quittingSingletonTerminal owner) blocker := by
  classical
  unfold RationalQuittingOwnersStrictPreempted at hpreempted
  push Not at hpreempted
  obtain ⟨owner, howner, hgap⟩ := hpreempted
  exact ⟨owner, howner, fun blocker => by linarith [hgap blocker]⟩

/-- A finite rational scan, not a chosen real root or strategic witness. -/
def rationalWeakExclusionUnpreemptedOwner
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hpreempted : ¬ RationalQuittingOwnersStrictPreempted reward owners) : Fin players :=
  Fin.find (fun owner => owner ∈ owners ∧ ∀ blocker,
    reward (quittingSingletonTerminal blocker) blocker ≤
      reward (quittingSingletonTerminal owner) blocker)
    (exists_unpreemptedEligibleOwner reward owners hpreempted)

theorem rationalWeakExclusionUnpreemptedOwner_spec
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hpreempted : ¬ RationalQuittingOwnersStrictPreempted reward owners) :
    let owner := rationalWeakExclusionUnpreemptedOwner reward owners hpreempted
    owner ∈ owners ∧ ∀ blocker,
      reward (quittingSingletonTerminal blocker) blocker ≤
        reward (quittingSingletonTerminal owner) blocker :=
  Fin.find_spec (exists_unpreemptedEligibleOwner reward owners hpreempted)

/-- Executable two-branch source selection at every positive rational accuracy.
The finite preemption predicate is unfolded so runtime uses rational comparisons. -/
def executableRationalWeakExclusionTwoBranchWord
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) : List (RationalQuittingRoot players) :=
  if hpreempted : ∀ owner ∈ owners, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker then
    executableRationalSelectedOwnerWords reward owners hWE hpreempted M hM hreward
      (executableRationalSelectedOwnerFirstPhase
        reward owners hWE hpreempted M hM hreward accuracy haccuracy)
  else
    rationalUnpreemptedSoloWord
      (rationalWeakExclusionUnpreemptedOwner reward owners hpreempted)
      M hM accuracy haccuracy

/-- Exact branch identity; all previous source tails are retained by the
canonical renewed-word construction. -/
theorem executableRationalWeakExclusionTwoBranchWord_eq_selectedOwnerFirstWord_of_preempted
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners) :
    executableRationalWeakExclusionTwoBranchWord
      reward owners hWE M hM hreward accuracy haccuracy =
      executableRationalSelectedOwnerWords reward owners hWE hpreempted M hM hreward
        (executableRationalSelectedOwnerFirstPhase
          reward owners hWE hpreempted M hM hreward accuracy haccuracy) := by
  unfold RationalQuittingOwnersStrictPreempted at hpreempted
  simp only [executableRationalWeakExclusionTwoBranchWord, dite_eq_left hpreempted]

/-- The other branch is exactly the printed hazard and least geometric cutoff,
including cutoff zero. Only its internally selected owner needs a sign. -/
theorem executableRationalWeakExclusionTwoBranchWord_eq_solo_of_not_preempted
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy)
    (hpreempted : ¬ RationalQuittingOwnersStrictPreempted reward owners) :
    executableRationalWeakExclusionTwoBranchWord
      reward owners hWE M hM hreward accuracy haccuracy =
      rationalUnpreemptedSoloWord
        (rationalWeakExclusionUnpreemptedOwner reward owners hpreempted)
        M hM accuracy haccuracy := by
  unfold RationalQuittingOwnersStrictPreempted at hpreempted
  simp only [executableRationalWeakExclusionTwoBranchWord, dite_eq_right hpreempted]

/-- The literal T3 phase and date bound, on precisely its all-preempted branch.
No additional singleton signs are required on this branch. -/
theorem executableRationalWeakExclusionTwoBranchWord_length_le_of_preempted
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners) :
    let initial := executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward 0
    let scale := (128 * M + 24 * initial) / 3
    let phase := executableRationalSelectedOwnerFirstPhase
      reward owners hWE hpreempted M hM hreward accuracy haccuracy
    phase ≤ Nat.ceil (scale / accuracy) ∧
      (executableRationalWeakExclusionTwoBranchWord
      reward owners hWE M hM hreward accuracy haccuracy).length ≤
        phase * executableRationalSelectedOwnerUniformPhaseRowBound
          (M : ℝ) (initial : ℝ) (accuracy : ℝ)
          (rationalQuittingSelectedOwnerPreemptionFloor reward owners hWE : ℝ) := by
  dsimp only
  rw [executableRationalWeakExclusionTwoBranchWord_eq_selectedOwnerFirstWord_of_preempted
    reward owners hWE M hM hreward accuracy haccuracy hpreempted]
  exact (executableRationalSelectedOwnerFirstWord_debt_and_length_le
    reward owners hWE hpreempted M hM hreward accuracy haccuracy).2

noncomputable section

/-- Complete behavioral terminal debt and Nash for the actual computed word,
not for an independently reselected profile. -/
theorem executableRationalWeakExclusionTwoBranchWord_actualDebt_and_nash
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy)
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    let word := executableRationalWeakExclusionTwoBranchWord
      reward owners hWE M hM hreward accuracy haccuracy
    let profile := quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
      (word.map RationalQuittingRoot.toPMF)
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) profile) ≤
        (accuracy : ℝ) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) (accuracy : ℝ)
        profile := by
  dsimp only
  have hdebt : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          ((executableRationalWeakExclusionTwoBranchWord
      reward owners hWE M hM hreward accuracy haccuracy).map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)))) ≤
      (accuracy : ℝ) := by
    by_cases hpreempted : RationalQuittingOwnersStrictPreempted reward owners
    · rw [executableRationalWeakExclusionTwoBranchWord_eq_selectedOwnerFirstWord_of_preempted
        reward owners hWE M hM hreward accuracy haccuracy hpreempted]
      exact (executableRationalSelectedOwnerFirstWord_actualDebt_nash_and_length_le
        reward owners hWE hpreempted M hM hreward accuracy haccuracy).1
    · rw [executableRationalWeakExclusionTwoBranchWord_eq_solo_of_not_preempted
        reward owners hWE M hM hreward accuracy haccuracy hpreempted]
      obtain ⟨howner, hcolumn⟩ :=
        rationalWeakExclusionUnpreemptedOwner_spec reward owners hpreempted
      exact rationalUnpreemptedSoloProfile_debtSum_le reward
        (rationalWeakExclusionUnpreemptedOwner reward owners hpreempted)
        M hM hreward (hsign _ howner) (fun who _ => hcolumn who) accuracy haccuracy
  exact ⟨hdebt, isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le _ _ hdebt⟩

/-- Rational correctness of the same runtime word; no real payoff or cap is
used as an executable input. -/
theorem executableRationalWeakExclusionTwoBranchWord_debt_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy)
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    rationalFiniteSourceDebt reward
      (executableRationalWeakExclusionTwoBranchWord
      reward owners hWE M hM hreward accuracy haccuracy) ≤ accuracy := by
  have hdebt := (executableRationalWeakExclusionTwoBranchWord_actualDebt_and_nash
    reward owners hWE M hM hreward accuracy haccuracy hsign).1
  rw [quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast] at hdebt
  exact_mod_cast hdebt

/-- One exact independent finite/Never law realization of the computed word.
Both actual total debt and every complete behavioral reply use this SAME law. -/
theorem executableRationalWeakExclusionTwoBranchWord_finiteLaws
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy)
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    let word := executableRationalWeakExclusionTwoBranchWord
      reward owners hWE M hM hreward accuracy haccuracy
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
            word.length mixed) =
        (rationalQuittingFiniteWordSemanticPair reward word).toReal ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
            (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
              word.length mixed)) ≤ (accuracy : ℝ) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) (accuracy : ℝ)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) := by
  dsimp only
  let word := executableRationalWeakExclusionTwoBranchWord
      reward owners hWE M hM hreward accuracy haccuracy
  obtain ⟨mixed, hmass, hpair⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  have hdebt : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed)) ≤ (accuracy : ℝ) := by
    rw [hpair]
    change quittingTerminalSemanticDebtSum
      (rationalQuittingFiniteWordSemanticPair reward word).toReal ≤ (accuracy : ℝ)
    rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
    exact_mod_cast executableRationalWeakExclusionTwoBranchWord_debt_le
      reward owners hWE M hM hreward accuracy haccuracy hsign
  exact ⟨mixed, hmass, hpair, hdebt,
    isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le _ _ hdebt⟩

end

end GameTheory
