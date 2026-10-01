import UniformEquilibrium.Quitting.Paths.RationalPositiveSingletonColumnExit

/-! # The fixed working-rate positive-column exit

The working rate is exactly e/(16M), as in the reward-uniform weak-subset
selector. The exit discards the old source and returns a newly constructed
finite solo word at the ORIGINAL requested accuracy. It is not a renewing
debt-decrease prefix over the old word.
-/

namespace GameTheory

variable {players : ℕ}

/-- The exact working rate, independent of the final requested accuracy. -/
def rationalPositiveColumnWorkingHazard (M working : ℚ) : ℚ :=
  working / (16 * M)

theorem rationalPositiveColumnWorkingHazard_pos
    {M working : ℚ} (hM : 0 < M) (hworking : 0 < working) :
    0 < rationalPositiveColumnWorkingHazard M working :=
  div_pos hworking (by positivity)

theorem rationalPositiveColumnWorkingHazard_lt_one
    {M working : ℚ} (hM : 0 < M) (hworkingM : working ≤ M) :
    rationalPositiveColumnWorkingHazard M working < 1 := by
  apply (div_lt_one (by positivity : 0 < 16 * M)).mpr
  linarith

/-- The actual finite singleton-column test at the working margin. -/
def RationalQuittingPositiveSingletonColumnAt
    (reward : RationalQuittingReward players) (owner : Fin players) (working : ℚ) : Prop :=
  ∀ who, who ≠ owner →
    reward (quittingSingletonTerminal who) who + working / 4 ≤
      reward (quittingSingletonTerminal owner) who

/-- No cap is supplied: the reward bound and actual positive column derive
the exact stationary inactive inequalities at the unchanged working rate. -/
theorem rationalPositiveColumnWorkingHazard_inactive
    (reward : RationalQuittingReward players) (owner : Fin players)
    {M working : ℚ} (hM : 0 < M) (hworking : 0 < working)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hcolumn : RationalQuittingPositiveSingletonColumnAt reward owner working)
    {who : Fin players} (hne : who ≠ owner) :
    (1 - rationalPositiveColumnWorkingHazard M working) *
        reward (quittingSingletonTerminal who) who +
      rationalPositiveColumnWorkingHazard M working * reward ⟨{owner, who}, by simp⟩ who ≤
        reward (quittingSingletonTerminal owner) who := by
  have hsolo := (abs_le.mp (hreward (quittingSingletonTerminal who) who)).1
  have hjoin := (abs_le.mp (hreward ⟨{owner, who}, by simp⟩ who)).2
  have hh := rationalPositiveColumnWorkingHazard_pos hM hworking
  have hscaled := mul_le_mul_of_nonneg_left
    (show reward ⟨{owner, who}, by simp⟩ who -
      reward (quittingSingletonTerminal who) who ≤ 2 * M by linarith) hh.le
  have hproduct : rationalPositiveColumnWorkingHazard M working * (2 * M) =
      working / 8 := by
    unfold rationalPositiveColumnWorkingHazard
    field_simp [ne_of_gt hM]
    ring
  have hsource := hcolumn who hne
  nlinarith

/-- The literal rational word uses the same working rate at EVERY date. -/
def rationalPositiveColumnWorkingWord
    (owner : Fin players) (M working : ℚ)
    (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    List (RationalQuittingRoot players) :=
  rationalSoloExitWord owner M hM (rationalPositiveColumnWorkingHazard M working)
    (rationalPositiveColumnWorkingHazard_pos hM hworking)
    (rationalPositiveColumnWorkingHazard_lt_one hM hworkingM) accuracy haccuracy

/-- The exact unchanged working rate has the same logarithmic date bound. -/
theorem rationalPositiveColumnWorkingWord_length_le_log
    (owner : Fin players) (M working : ℚ)
    (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    ((rationalPositiveColumnWorkingWord owner M working hM hworking hworkingM
        accuracy haccuracy).length : ℝ) ≤
      1 + Real.log (1 / (rationalSoloExitTolerance players M accuracy : ℝ)) /
        (-Real.log (1 - (rationalPositiveColumnWorkingHazard M working : ℝ))) :=
  rationalSoloExitWord_length_le_log owner M hM _ _ _ accuracy haccuracy

noncomputable section

/-- Delivery to the actual owner-singleton target by the SAME working-rate
word; this conclusion does not impose any outsider sign. -/
theorem rationalPositiveColumnWorkingWord_delivery_le
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M working : ℚ) (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) (who : Fin players) :
    let word := rationalPositiveColumnWorkingWord
      owner M working hM hworking hworkingM accuracy haccuracy
    |quittingTerminalPayoff (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (word.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who -
      (reward (quittingSingletonTerminal owner) who : ℝ)| ≤ (accuracy : ℝ) / 2 :=
  rationalSoloExitWord_delivery_le reward owner M hM hreward _ _ _ accuracy haccuracy who

/-- The SAME working-rate row is exact terminal Nash before truncation. -/
theorem rationalPositiveColumnWorking_stationary_exact
    (reward : RationalQuittingReward players) (owner : Fin players)
    {M working : ℚ} (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingPositiveSingletonColumnAt reward owner working) :
    (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) 0
      (quittingStationaryProfile (rationalQuittingRewardToReal reward)
        (rationalQuittingSoloRoot owner
          (rationalPositiveColumnWorkingHazard M working)).toPMF) := by
  have hh := rationalPositiveColumnWorkingHazard_pos hM hworking
  have hh1 := rationalPositiveColumnWorkingHazard_lt_one hM hworkingM
  rw [rationalQuittingSoloRoot_toPMF_eq owner ⟨hh.le, hh1.le⟩]
  apply isεAsymptoticNash_soloStationary_exact
  · rw [quittingHazardCoin_true_toReal]
    exact_mod_cast hh
  · change (0 : ℝ) ≤ (reward (quittingSingletonTerminal owner) owner : ℝ)
    exact_mod_cast howner
  · intro who hne
    rw [quittingHazardCoin_false_toReal, quittingHazardCoin_true_toReal]
    change (1 - (rationalPositiveColumnWorkingHazard M working : ℝ)) *
        (reward (quittingSingletonTerminal who) who : ℝ) +
      (rationalPositiveColumnWorkingHazard M working : ℝ) *
        (reward ⟨{owner, who}, by simp⟩ who : ℝ) ≤
      (reward (quittingSingletonTerminal owner) who : ℝ)
    exact_mod_cast rationalPositiveColumnWorkingHazard_inactive
      reward owner hM hworking hreward hcolumn hne

/-- Sharp debt at the original final accuracy; the working rate does not
shrink again during the truncation. All complete behavioral replies remain. -/
theorem rationalPositiveColumnWorkingWord_debtSum_le
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M working : ℚ) (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingPositiveSingletonColumnAt reward owner working)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := rationalPositiveColumnWorkingWord
      owner M working hM hworking hworkingM accuracy haccuracy
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (word.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)))) ≤
      (accuracy : ℝ) / 2 := by
  dsimp only [rationalPositiveColumnWorkingWord]
  apply rationalSoloExitWord_debtSum_le
  · exact hreward
  · exact howner
  · intro who hne
    have hsource := hcolumn who hne
    linarith
  · intro who hne
    exact rationalPositiveColumnWorkingHazard_inactive
      reward owner hM hworking hreward hcolumn hne

/-- Actual independent rational date/Never laws of the unchanged working-rate
exit, with full terminal Nash error at most half the final requested accuracy. -/
theorem rationalPositiveColumnWorkingWord_finiteLaws
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M working : ℚ) (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingPositiveSingletonColumnAt reward owner working)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := rationalPositiveColumnWorkingWord
      owner M working hM hworking hworkingM accuracy haccuracy
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) =
        quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
            (word.map RationalQuittingRoot.toPMF)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) ((accuracy : ℝ) / 2)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) := by
  dsimp only
  let word := rationalPositiveColumnWorkingWord
    owner M working hM hworking hworkingM accuracy haccuracy
  obtain ⟨mixed, hmass, hsemantic⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  have hsame := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word
  have hequal := hsemantic.trans hsame.symm
  refine ⟨mixed, hmass, hequal, ?_⟩
  apply isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
  rw [hequal]
  exact rationalPositiveColumnWorkingWord_debtSum_le
    reward owner M working hM hworking hworkingM hreward howner hcolumn accuracy haccuracy

end

end GameTheory
