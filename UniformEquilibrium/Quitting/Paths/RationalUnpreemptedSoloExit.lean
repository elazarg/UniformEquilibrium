import MathUE.RationalCalendarSearch
import UniformEquilibrium.Quitting.Paths.FiniteUnpreemptedSoloExit
import UniformEquilibrium.Quitting.Root.RationalFiniteSourceCapThresholdScan
import UniformEquilibrium.Quitting.Root.RationalFiniteWordSearch

/-! # Executable rational exit for a weakly unpreempted designated owner

The rate is exactly min(1/2, accuracy/(4 n M)); the cutoff is the least
natural number satisfying the printed tail test, including zero.
Only the designated owner's singleton needs a nonnegative sign. Other rewards
may be signed. No weak-exclusion, root, cap, or search-success input is used.
-/

namespace GameTheory

variable {players : ℕ}

def rationalUnpreemptedSoloHazard (players : ℕ) (M accuracy : ℚ) : ℚ :=
  min (1 / 2) (accuracy / (4 * players * M))

private theorem playerCount_pos (owner : Fin players) : (0 : ℚ) < players := by
  exact_mod_cast (lt_of_le_of_lt (Nat.zero_le owner.val) owner.isLt)

theorem rationalUnpreemptedSoloHazard_pos (owner : Fin players)
    {M accuracy : ℚ} (hM : 0 < M) (haccuracy : 0 < accuracy) :
    0 < rationalUnpreemptedSoloHazard players M accuracy := by
  have hn := playerCount_pos owner
  exact lt_min (by norm_num) (div_pos haccuracy (by positivity))

theorem rationalUnpreemptedSoloHazard_le_half (players : ℕ) (M accuracy : ℚ) :
    rationalUnpreemptedSoloHazard players M accuracy ≤ 1 / 2 :=
  min_le_left _ _

private theorem tailTolerance_pos (owner : Fin players)
    {M accuracy : ℚ} (hM : 0 < M) (haccuracy : 0 < accuracy) :
    0 < accuracy / (2 * players * M) := by
  have hn := playerCount_pos owner
  positivity

/-- The zero test plus the canonical first-positive geometric search gives the
least cutoff among all natural numbers, without a second search engine. -/
def rationalUnpreemptedSoloLength (owner : Fin players)
    (M : ℚ) (hM : 0 < M) (accuracy : ℚ) (haccuracy : 0 < accuracy) : ℕ :=
  if 1 ≤ accuracy / (2 * players * M) then 0 else
    Math.rationalPowerCutoff
      (1 - rationalUnpreemptedSoloHazard players M accuracy)
      (accuracy / (2 * players * M))
      (by
        have hhalf := rationalUnpreemptedSoloHazard_le_half players M accuracy
        linarith)
      (by linarith [rationalUnpreemptedSoloHazard_pos owner hM haccuracy])
      (tailTolerance_pos owner hM haccuracy)

theorem rationalUnpreemptedSoloLength_power (owner : Fin players)
    (M : ℚ) (hM : 0 < M) (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    (1 - rationalUnpreemptedSoloHazard players M accuracy) ^
      rationalUnpreemptedSoloLength owner M hM accuracy haccuracy ≤
        accuracy / (2 * players * M) := by
  unfold rationalUnpreemptedSoloLength
  split_ifs with hzero
  · simpa only [pow_zero] using hzero
  · exact Math.rationalPowerCutoff_spec _ _ _ _ _

theorem rationalUnpreemptedSoloLength_le (owner : Fin players)
    (M : ℚ) (hM : 0 < M) (accuracy : ℚ) (haccuracy : 0 < accuracy)
    (k : ℕ)
    (hk : M * (1 - rationalUnpreemptedSoloHazard players M accuracy) ^ k ≤
      accuracy / (2 * players)) :
    rationalUnpreemptedSoloLength owner M hM accuracy haccuracy ≤ k := by
  have hn := playerCount_pos owner
  have hden : (0 : ℚ) < 2 * players * M := by positivity
  have hpower : (1 - rationalUnpreemptedSoloHazard players M accuracy) ^ k ≤
      accuracy / (2 * players * M) := by
    apply (le_div_iff₀ hden).mpr
    have hscaled := (le_div_iff₀ (by positivity : (0 : ℚ) < 2 * players)).mp hk
    nlinarith
  unfold rationalUnpreemptedSoloLength
  split_ifs with hzero
  · exact Nat.zero_le _
  · apply Math.rationalPowerCutoff_min
    · by_contra h
      have hkzero : k = 0 := by omega
      subst k
      exact hzero (by simpa only [pow_zero] using hpower)
    · exact hpower

theorem rationalUnpreemptedSoloLength_tail (owner : Fin players)
    (M : ℚ) (hM : 0 < M) (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    M * (1 - rationalUnpreemptedSoloHazard players M accuracy) ^
      rationalUnpreemptedSoloLength owner M hM accuracy haccuracy ≤
        accuracy / (2 * players) := by
  have hn := playerCount_pos owner
  have hpower := rationalUnpreemptedSoloLength_power owner M hM accuracy haccuracy
  have hscaled := (le_div_iff₀ (by positivity : (0 : ℚ) < 2 * players * M)).mp hpower
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 * players)).mpr
  nlinarith

def rationalUnpreemptedSoloWord (owner : Fin players)
    (M : ℚ) (hM : 0 < M) (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    List (RationalQuittingRoot players) :=
  List.replicate (rationalUnpreemptedSoloLength owner M hM accuracy haccuracy)
    (rationalQuittingSoloRoot owner (rationalUnpreemptedSoloHazard players M accuracy))

private theorem rationalUnpreemptedSolo_budget (owner : Fin players)
    (M : ℚ) (hM : 0 < M) (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    (players : ℚ) *
      (2 * M * rationalUnpreemptedSoloHazard players M accuracy +
        M * (1 - rationalUnpreemptedSoloHazard players M accuracy) ^
          rationalUnpreemptedSoloLength owner M hM accuracy haccuracy) ≤ accuracy := by
  have hn := playerCount_pos owner
  have hrate : rationalUnpreemptedSoloHazard players M accuracy ≤
      accuracy / (4 * players * M) := min_le_right _ _
  have hrateScaled :=
    (le_div_iff₀ (by positivity : (0 : ℚ) < 4 * players * M)).mp hrate
  have htail := rationalUnpreemptedSoloLength_tail owner M hM accuracy haccuracy
  have htailScaled :=
    (le_div_iff₀ (by positivity : (0 : ℚ) < 2 * players)).mp htail
  nlinarith

noncomputable section

def rationalUnpreemptedSoloProfile (reward : RationalQuittingReward players)
    (owner : Fin players) (M : ℚ) (hM : 0 < M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    (quittingGame (rationalQuittingRewardToReal reward)).BehaviorProfile :=
  quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
    ((rationalUnpreemptedSoloWord owner M hM accuracy haccuracy).map
      RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))

theorem rationalUnpreemptedSoloProfile_debtSum_le
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who ≤
        reward (quittingSingletonTerminal owner) who)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (rationalUnpreemptedSoloProfile reward owner M hM accuracy haccuracy)) ≤
      (accuracy : ℝ) := by
  let rate := rationalUnpreemptedSoloHazard players M accuracy
  have hr0 : 0 ≤ rate := (rationalUnpreemptedSoloHazard_pos owner hM haccuracy).le
  have hr1 : rate ≤ 1 :=
    (rationalUnpreemptedSoloHazard_le_half players M accuracy).trans (by norm_num)
  have hbound : ∀ terminal who,
      |rationalQuittingRewardToReal reward terminal who| ≤ (M : ℝ) := by
    intro terminal who
    change |(reward terminal who : ℝ)| ≤ (M : ℝ)
    exact_mod_cast hreward terminal who
  have hownerReal :
      0 ≤ rationalQuittingRewardToReal reward (quittingSingletonTerminal owner) owner := by
    change (0 : ℝ) ≤ (reward (quittingSingletonTerminal owner) owner : ℝ)
    exact_mod_cast howner
  have hcolumnReal : ∀ who, who ≠ owner →
      rationalQuittingRewardToReal reward (quittingSingletonTerminal who) who ≤
        rationalQuittingRewardToReal reward (quittingSingletonTerminal owner) who := by
    intro who hne
    change (reward (quittingSingletonTerminal who) who : ℝ) ≤
      (reward (quittingSingletonTerminal owner) who : ℝ)
    exact_mod_cast hunpreempted who hne
  have hraw :=
    quittingTerminalSemanticDebtSum_replicate_solo_never_le_of_owner_nonnegative
      (rationalQuittingRewardToReal reward) owner (t := (rate : ℝ)) hbound
      (by exact_mod_cast hr0) (by exact_mod_cast hr1) hownerReal hcolumnReal
      (rationalUnpreemptedSoloLength owner M hM accuracy haccuracy)
  have hbudget := rationalUnpreemptedSolo_budget owner M hM accuracy haccuracy
  have hbudgetReal :
      (players : ℝ) *
        (2 * (M : ℝ) * (rate : ℝ) + (M : ℝ) * (1 - (rate : ℝ)) ^
          rationalUnpreemptedSoloLength owner M hM accuracy haccuracy) ≤ (accuracy : ℝ) := by
    exact_mod_cast hbudget
  dsimp only [rate] at hr0 hr1 hraw
  apply le_trans ?_ hbudgetReal
  simpa only [rationalUnpreemptedSoloProfile, rationalUnpreemptedSoloWord,
    List.map_replicate, rationalQuittingSoloRoot_toPMF_eq owner ⟨hr0, hr1⟩,
    Fintype.card_fin] using hraw

theorem rationalUnpreemptedSoloProfile_nash
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who ≤
        reward (quittingSingletonTerminal owner) who)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) (accuracy : ℝ)
      (rationalUnpreemptedSoloProfile reward owner M hM accuracy haccuracy) :=
  isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le _ _
    (rationalUnpreemptedSoloProfile_debtSum_le
      reward owner M hM hreward howner hunpreempted accuracy haccuracy)

/-- Same computed word, exact independent rational atoms, and the complete
semantic pair; late dates, unsupported dates, and Never are not discarded. -/
theorem rationalUnpreemptedSoloWord_finiteLaws
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who ≤
        reward (quittingSingletonTerminal owner) who)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := rationalUnpreemptedSoloWord owner M hM accuracy haccuracy
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) =
        quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (rationalUnpreemptedSoloProfile reward owner M hM accuracy haccuracy) ∧
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
            word.length mixed)) ≤ (accuracy : ℝ) := by
  dsimp only
  let word := rationalUnpreemptedSoloWord owner M hM accuracy haccuracy
  obtain ⟨mixed, hmass, hpair⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  have hequal := hpair.trans
    (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word).symm
  refine ⟨mixed, hmass, hequal, ?_⟩
  rw [hequal]
  exact rationalUnpreemptedSoloProfile_debtSum_le
    reward owner M hM hreward howner hunpreempted accuracy haccuracy

end

end GameTheory
