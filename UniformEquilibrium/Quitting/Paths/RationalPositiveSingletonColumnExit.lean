import MathUE.RationalPowerCutoffLogBound
import UniformEquilibrium.Quitting.Paths.SoloStationaryFiniteExit
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Root.RationalFiniteSourceCapThresholdScan
import UniformEquilibrium.Quitting.Root.RationalFiniteWordSearch

/-! # Executable positive-singleton-column exit

A strict singleton column and a nonnegative selected-owner singleton internally
produce a positive rational exact stationary Nash rate. The finite exit is a
literal repetition of that row followed by Never, with actual full caps.
No signs on other owners, selected root, strategic cap or search-success input
are required. Rational computations do not evaluate the logarithmic bound.
-/

namespace GameTheory

variable {players : ℕ}

/-- The raw finite column test; no strategic object is supplied. -/
def RationalQuittingStrictSingletonColumn
    (reward : RationalQuittingReward players) (owner : Fin players) : Prop :=
  ∀ who, who ≠ owner →
    reward (quittingSingletonTerminal who) who <
      reward (quittingSingletonTerminal owner) who

/-- A safe rate from one actual outsider singleton difference. -/
def rationalPositiveSingletonColumnCandidate
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (who : Fin players) : ℚ :=
  if who = owner then 1 / 2 else
    min (1 / 2)
      ((reward (quittingSingletonTerminal owner) who -
          reward (quittingSingletonTerminal who) who) /
        (2 * (reward (quittingSingletonTerminal owner) who -
          reward (quittingSingletonTerminal who) who + 2 * M)))

/-- The finite rational minimum, with the owner providing the nonempty scan
and the one-player boundary. -/
def rationalPositiveSingletonColumnHazard
    (reward : RationalQuittingReward players) (owner : Fin players) (M : ℚ) : ℚ :=
  Finset.univ.inf' ⟨owner, Finset.mem_univ owner⟩
    (rationalPositiveSingletonColumnCandidate reward owner M)

theorem rationalPositiveSingletonColumnHazard_pos
    (reward : RationalQuittingReward players) (owner : Fin players)
    {M : ℚ} (hM : 0 < M)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner) :
    0 < rationalPositiveSingletonColumnHazard reward owner M := by
  apply (Finset.lt_inf'_iff _).mpr
  intro who _
  unfold rationalPositiveSingletonColumnCandidate
  split_ifs with hwho
  · norm_num
  · have hgap := sub_pos.mpr (hcolumn who hwho)
    exact lt_min (by norm_num) (div_pos hgap (by positivity))

theorem rationalPositiveSingletonColumnHazard_le_half
    (reward : RationalQuittingReward players) (owner : Fin players) (M : ℚ) :
    rationalPositiveSingletonColumnHazard reward owner M ≤ 1 / 2 := by
  have hle := Finset.inf'_le
    (rationalPositiveSingletonColumnCandidate reward owner M) (Finset.mem_univ owner)
  simpa [rationalPositiveSingletonColumnHazard,
    rationalPositiveSingletonColumnCandidate] using hle

/-- The computed rate satisfies every actual inactive inequality. -/
theorem rationalPositiveSingletonColumnHazard_inactive
    (reward : RationalQuittingReward players) (owner : Fin players)
    {M : ℚ} (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    {who : Fin players} (hne : who ≠ owner) :
    (1 - rationalPositiveSingletonColumnHazard reward owner M) *
        reward (quittingSingletonTerminal who) who +
      rationalPositiveSingletonColumnHazard reward owner M *
        reward ⟨{owner, who}, by simp⟩ who ≤
      reward (quittingSingletonTerminal owner) who := by
  let h := rationalPositiveSingletonColumnHazard reward owner M
  let gap := reward (quittingSingletonTerminal owner) who -
    reward (quittingSingletonTerminal who) who
  have hgap : 0 < gap := sub_pos.mpr (hcolumn who hne)
  have hh : 0 < h := rationalPositiveSingletonColumnHazard_pos reward owner hM hcolumn
  have hle := Finset.inf'_le
    (rationalPositiveSingletonColumnCandidate reward owner M) (Finset.mem_univ who)
  have hquotient : h ≤ gap / (2 * (gap + 2 * M)) := by
    exact hle.trans (by
      simp only [rationalPositiveSingletonColumnCandidate, ite_eq_right hne]
      exact min_le_right _ _)
  have hproduct := (le_div_iff₀ (by positivity : 0 < 2 * (gap + 2 * M))).mp hquotient
  have hsolo := (abs_le.mp (hreward (quittingSingletonTerminal who) who)).1
  have hjoin := (abs_le.mp (hreward ⟨{owner, who}, by simp⟩ who)).2
  have hscaled := mul_le_mul_of_nonneg_left
    (show reward ⟨{owner, who}, by simp⟩ who -
      reward (quittingSingletonTerminal who) who ≤ 2 * M by linarith) hh.le
  dsimp only [gap, h] at hproduct hh hscaled ⊢
  nlinarith [mul_nonneg hh.le hgap.le]

/-- The same internally computed rational row is exact terminal Nash. -/
theorem rationalPositiveSingletonColumn_stationary_exact
    (reward : RationalQuittingReward players) (owner : Fin players)
    {M : ℚ} (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner) :
    (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) 0
      (quittingStationaryProfile (rationalQuittingRewardToReal reward)
        (rationalQuittingSoloRoot owner
          (rationalPositiveSingletonColumnHazard reward owner M)).toPMF) := by
  have hh := rationalPositiveSingletonColumnHazard_pos reward owner hM hcolumn
  have hh1 : rationalPositiveSingletonColumnHazard reward owner M ≤ 1 :=
    (rationalPositiveSingletonColumnHazard_le_half reward owner M).trans (by norm_num)
  rw [rationalQuittingSoloRoot_toPMF_eq owner ⟨hh.le, hh1⟩]
  apply isεAsymptoticNash_soloStationary_exact
  · rw [quittingHazardCoin_true_toReal]
    exact_mod_cast hh
  · change (0 : ℝ) ≤ (reward (quittingSingletonTerminal owner) owner : ℝ)
    exact_mod_cast howner
  · intro who hne
    rw [quittingHazardCoin_false_toReal, quittingHazardCoin_true_toReal]
    change (1 - (rationalPositiveSingletonColumnHazard reward owner M : ℝ)) *
        (reward (quittingSingletonTerminal who) who : ℝ) +
      (rationalPositiveSingletonColumnHazard reward owner M : ℝ) *
        (reward ⟨{owner, who}, by simp⟩ who : ℝ) ≤
      (reward (quittingSingletonTerminal owner) who : ℝ)
    exact_mod_cast rationalPositiveSingletonColumnHazard_inactive
      reward owner hM hreward hcolumn hne

private theorem player_count_pos (owner : Fin players) : 0 < (players : ℚ) := by
  exact_mod_cast (Nat.zero_lt_of_lt owner.isLt)

/-- The requested accuracy fixes a rational survival tolerance, allowing
arbitrarily large accuracies without any extra smallness premise. -/
def rationalSoloExitTolerance (players : ℕ) (M accuracy : ℚ) : ℚ :=
  min 1 (accuracy / (2 * players * M))

theorem rationalSoloExitTolerance_pos (owner : Fin players)
    {M accuracy : ℚ} (hM : 0 < M) (haccuracy : 0 < accuracy) :
    0 < rationalSoloExitTolerance players M accuracy := by
  have hn := player_count_pos owner
  exact lt_min zero_lt_one (div_pos haccuracy (by positivity))

/-- Common executable truncation for an actual positive rational solo rate. -/
def rationalSoloExitWord (owner : Fin players) (M : ℚ) (hM : 0 < M)
    (hazard : ℚ) (hhazard0 : 0 < hazard) (hhazard1 : hazard < 1)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    List (RationalQuittingRoot players) :=
  List.replicate
    (Math.rationalPowerCutoff (1 - hazard)
      (rationalSoloExitTolerance players M accuracy)
      (by linarith) (by linarith)
      (rationalSoloExitTolerance_pos owner hM haccuracy))
    (rationalQuittingSoloRoot owner hazard)

/-- The common cutoff retains the exact logarithmic calendar bound. -/
theorem rationalSoloExitWord_length_le_log
    (owner : Fin players) (M : ℚ) (hM : 0 < M)
    (hazard : ℚ) (hhazard0 : 0 < hazard) (hhazard1 : hazard < 1)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    ((rationalSoloExitWord owner M hM hazard hhazard0 hhazard1
        accuracy haccuracy).length : ℝ) ≤
      1 + Real.log (1 / (rationalSoloExitTolerance players M accuracy : ℝ)) /
        (-Real.log (1 - (hazard : ℝ))) := by
  have hρ : 0 < 1 - hazard := by linarith
  have hρ1 : 1 - hazard < 1 := by linarith
  have ht := rationalSoloExitTolerance_pos owner hM haccuracy
  have ht1 : rationalSoloExitTolerance players M accuracy ≤ 1 := min_le_left _ _
  simpa only [rationalSoloExitWord, List.length_replicate, Rat.cast_sub, Rat.cast_one] using
    Math.rationalPowerCutoff_le_log_bound hρ hρ1 ht ht1

/-- The computed cutoff charges the complete surviving mass at the final
accuracy. This arithmetic is shared by debt and payoff delivery. -/
theorem rationalSoloExitWord_tailCharge_le
    (owner : Fin players) (M : ℚ) (hM : 0 < M)
    (hazard : ℚ) (hhazard0 : 0 < hazard) (hhazard1 : hazard < 1)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    players * M * (1 - hazard) ^
        (rationalSoloExitWord owner M hM hazard hhazard0 hhazard1
          accuracy haccuracy).length ≤ accuracy / 2 := by
  let tolerance := rationalSoloExitTolerance players M accuracy
  have hn := player_count_pos owner
  have hcut := Math.rationalPowerCutoff_spec (1 - hazard) tolerance
    (by linarith) (by linarith) (rationalSoloExitTolerance_pos owner hM haccuracy)
  have hratio : tolerance ≤ accuracy / (2 * players * M) := min_le_right _ _
  have hproduct := (le_div_iff₀
    (show 0 < (2 : ℚ) * players * M by positivity)).mp hratio
  have hscaled := mul_le_mul_of_nonneg_left hcut
    (show 0 ≤ (players : ℚ) * M by positivity)
  simp only [rationalSoloExitWord, List.length_replicate]
  nlinarith

/-- Actual rational rows, followed by Always Continue. No selected real
strategy or strategic cap occurs in the executable data. -/
def rationalPositiveSingletonColumnWord
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    List (RationalQuittingRoot players) :=
  rationalSoloExitWord owner M hM
    (rationalPositiveSingletonColumnHazard reward owner M)
    (rationalPositiveSingletonColumnHazard_pos reward owner hM hcolumn)
    (lt_of_le_of_lt (rationalPositiveSingletonColumnHazard_le_half reward owner M)
      (by norm_num)) accuracy haccuracy

/-- The returned calendar satisfies the canonical logarithmic cutoff bound. -/
theorem rationalPositiveSingletonColumnWord_length_le_log
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    ((rationalPositiveSingletonColumnWord reward owner M hM hcolumn
        accuracy haccuracy).length : ℝ) ≤
      1 + Real.log (1 / (rationalSoloExitTolerance players M accuracy : ℝ)) /
        (-Real.log (1 - (rationalPositiveSingletonColumnHazard reward owner M : ℝ))) := by
  exact rationalSoloExitWord_length_le_log owner M hM _ _ _ accuracy haccuracy

noncomputable section

/-- A certified one-row scalar inequality produces an actual finite-word
debt guarantee; no cap is an input. This is shared by both source rate choices. -/
theorem rationalSoloExitWord_debtSum_le
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hazard : ℚ) (hhazard0 : 0 < hazard) (hhazard1 : hazard < 1)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who ≤
        reward (quittingSingletonTerminal owner) who)
    (hinactive : ∀ who, who ≠ owner →
      (1 - hazard) * reward (quittingSingletonTerminal who) who +
        hazard * reward ⟨{owner, who}, by simp⟩ who ≤
          reward (quittingSingletonTerminal owner) who)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := rationalSoloExitWord owner M hM hazard hhazard0 hhazard1 accuracy haccuracy
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (word.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)))) ≤
      (accuracy : ℝ) / 2 := by
  let tolerance := rationalSoloExitTolerance players M accuracy
  let steps := Math.rationalPowerCutoff (1 - hazard) tolerance
    (by linarith) (by linarith) (rationalSoloExitTolerance_pos owner hM haccuracy)
  have hhazardReal0 : (0 : ℝ) ≤ hazard := by exact_mod_cast hhazard0.le
  have hhazardReal1 : (hazard : ℝ) ≤ 1 := by exact_mod_cast hhazard1.le
  have hrealBound : ∀ terminal who,
      |rationalQuittingRewardToReal reward terminal who| ≤ (M : ℝ) := by
    intro terminal who
    change |(reward terminal who : ℝ)| ≤ (M : ℝ)
    exact_mod_cast hreward terminal who
  have hownerReal : 0 ≤ rationalQuittingRewardToReal reward
      (quittingSingletonTerminal owner) owner := by
    change (0 : ℝ) ≤ (reward (quittingSingletonTerminal owner) owner : ℝ)
    exact_mod_cast howner
  have hcolumnReal : ∀ who, who ≠ owner →
      rationalQuittingRewardToReal reward (quittingSingletonTerminal who) who ≤
        rationalQuittingRewardToReal reward (quittingSingletonTerminal owner) who := by
    intro who hne
    change (reward (quittingSingletonTerminal who) who : ℝ) ≤
      (reward (quittingSingletonTerminal owner) who : ℝ)
    exact_mod_cast hunpreempted who hne
  have hinactiveReal : ∀ who, who ≠ owner →
      (1 - (hazard : ℝ)) *
          rationalQuittingRewardToReal reward (quittingSingletonTerminal who) who +
        (hazard : ℝ) * quittingSingletonCollisionReward
          (rationalQuittingRewardToReal reward) owner who ≤
        rationalQuittingRewardToReal reward (quittingSingletonTerminal owner) who := by
    intro who hne
    change (1 - (hazard : ℝ)) * (reward (quittingSingletonTerminal who) who : ℝ) +
      (hazard : ℝ) * (reward ⟨{owner, who}, by simp⟩ who : ℝ) ≤
        (reward (quittingSingletonTerminal owner) who : ℝ)
    exact_mod_cast hinactive who hne
  have hsum := quittingTerminalSemanticDebtSum_replicate_solo_never_sharp_le
    (rationalQuittingRewardToReal reward) owner hrealBound
    hhazardReal0 hhazardReal1
    hownerReal hcolumnReal hinactiveReal steps
  have htail : (players : ℝ) * (M : ℝ) * (1 - (hazard : ℝ)) ^ steps ≤
      (accuracy : ℝ) / 2 := by
    have htailRational := rationalSoloExitWord_tailCharge_le
      owner M hM hazard hhazard0 hhazard1 accuracy haccuracy
    simp only [rationalSoloExitWord, List.length_replicate] at htailRational
    exact_mod_cast htailRational
  dsimp only
  unfold rationalSoloExitWord
  rw [List.map_replicate,
    rationalQuittingSoloRoot_toPMF_eq owner ⟨hhazard0.le, hhazard1.le⟩]
  simp only [Fintype.card_fin] at hsum
  exact hsum.trans htail

/-- Every coordinate of the same computed profile delivers the literal
owner-singleton payoff within half the requested accuracy. No signs are needed. -/
theorem rationalSoloExitWord_delivery_le
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hazard : ℚ) (hhazard0 : 0 < hazard) (hhazard1 : hazard < 1)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) (who : Fin players) :
    let word := rationalSoloExitWord owner M hM hazard hhazard0 hhazard1 accuracy haccuracy
    |quittingTerminalPayoff (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (word.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who -
      (reward (quittingSingletonTerminal owner) who : ℝ)| ≤ (accuracy : ℝ) / 2 := by
  let word := rationalSoloExitWord owner M hM hazard hhazard0 hhazard1 accuracy haccuracy
  have hh0 : (0 : ℝ) ≤ hazard := by exact_mod_cast hhazard0.le
  have hh1 : (hazard : ℝ) ≤ 1 := by exact_mod_cast hhazard1.le
  have hz : 0 ≤ (1 - (hazard : ℝ)) ^ word.length :=
    pow_nonneg (sub_nonneg.mpr hh1) _
  have hn : (1 : ℝ) ≤ players := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.zero_lt_of_lt owner.isLt))
  have hMr : 0 ≤ (M : ℝ) := by exact_mod_cast hM.le
  have hbound : |(reward (quittingSingletonTerminal owner) who : ℝ)| ≤ (M : ℝ) := by
    exact_mod_cast hreward (quittingSingletonTerminal owner) who
  have htail :
      (players : ℝ) * (M : ℝ) * (1 - (hazard : ℝ)) ^ word.length ≤
        (accuracy : ℝ) / 2 := by
    exact_mod_cast rationalSoloExitWord_tailCharge_le
      owner M hM hazard hhazard0 hhazard1 accuracy haccuracy
  have hpayoff : quittingTerminalPayoff (rationalQuittingRewardToReal reward)
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        (word.map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who =
      (1 - (1 - (hazard : ℝ)) ^ word.length) *
        (reward (quittingSingletonTerminal owner) who : ℝ) := by
    dsimp only [word, rationalSoloExitWord]
    rw [List.map_replicate,
      rationalQuittingSoloRoot_toPMF_eq owner ⟨hhazard0.le, hhazard1.le⟩]
    simp only [List.length_replicate]
    exact quittingTerminalPayoff_replicate_solo_never_eq _ owner who hh0 hh1 _
  dsimp only
  rw [hpayoff]
  rw [show (1 - (1 - (hazard : ℝ)) ^ word.length) *
          (reward (quittingSingletonTerminal owner) who : ℝ) -
        (reward (quittingSingletonTerminal owner) who : ℝ) =
        -((1 - (hazard : ℝ)) ^ word.length *
          (reward (quittingSingletonTerminal owner) who : ℝ)) by ring,
    abs_neg, abs_mul, abs_of_nonneg hz]
  have hscaled := mul_le_mul_of_nonneg_left hbound hz
  have hcount := mul_le_mul_of_nonneg_right hn (mul_nonneg hMr hz)
  nlinarith

/-- This is the actual profile of the computed word, not a separately selected root. -/
def rationalPositiveSingletonColumnProfile
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :=
  quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
    ((rationalPositiveSingletonColumnWord reward owner M hM hcolumn
      accuracy haccuracy).map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))

/-- Payoff delivery to the actual stationary singleton target, at the
requested accuracy, is retained by the same computed finite word. -/
theorem rationalPositiveSingletonColumnProfile_delivery_le
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) (who : Fin players) :
    |quittingTerminalPayoff (rationalQuittingRewardToReal reward)
        (rationalPositiveSingletonColumnProfile
          reward owner M hM hcolumn accuracy haccuracy) who -
      (reward (quittingSingletonTerminal owner) who : ℝ)| ≤ (accuracy : ℝ) / 2 :=
  rationalSoloExitWord_delivery_le reward owner M hM hreward _ _ _ accuracy haccuracy who

/-- Sharp actual payoff and cap identities for the computed finite exit. -/
theorem rationalPositiveSingletonColumnProfile_payoff_and_cap
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := rationalPositiveSingletonColumnWord reward owner M hM hcolumn accuracy haccuracy
    let profile := rationalPositiveSingletonColumnProfile
      reward owner M hM hcolumn accuracy haccuracy
    let z := (1 - (rationalPositiveSingletonColumnHazard reward owner M : ℝ)) ^ word.length
    (∀ who, quittingTerminalPayoff (rationalQuittingRewardToReal reward) profile who =
      (1 - z) * (reward (quittingSingletonTerminal owner) who : ℝ)) ∧
    quittingContinuationBestResponseValue (rationalQuittingRewardToReal reward) profile owner =
      (reward (quittingSingletonTerminal owner) owner : ℝ) ∧
    (∀ who, quittingContinuationBestResponseValue
      (rationalQuittingRewardToReal reward) profile who ≤
      max (reward (quittingSingletonTerminal owner) who : ℝ)
        ((1 - z) * (reward (quittingSingletonTerminal owner) who : ℝ))) := by
  have hh := rationalPositiveSingletonColumnHazard_pos reward owner hM hcolumn
  have hh1 : rationalPositiveSingletonColumnHazard reward owner M ≤ 1 :=
    (rationalPositiveSingletonColumnHazard_le_half reward owner M).trans (by norm_num)
  dsimp only
  unfold rationalPositiveSingletonColumnProfile rationalPositiveSingletonColumnWord
    rationalSoloExitWord
  rw [List.map_replicate, rationalQuittingSoloRoot_toPMF_eq owner ⟨hh.le, hh1⟩]
  simp only [List.length_replicate]
  apply quittingTerminalSemanticPair_replicate_solo_never_sharp
  · change (0 : ℝ) ≤ (reward (quittingSingletonTerminal owner) owner : ℝ)
    exact_mod_cast howner
  · intro who hne
    change (reward (quittingSingletonTerminal who) who : ℝ) ≤
      (reward (quittingSingletonTerminal owner) who : ℝ)
    exact_mod_cast (hcolumn who hne).le
  · intro who hne
    change (1 - (rationalPositiveSingletonColumnHazard reward owner M : ℝ)) *
        (reward (quittingSingletonTerminal who) who : ℝ) +
      (rationalPositiveSingletonColumnHazard reward owner M : ℝ) *
        (reward ⟨{owner, who}, by simp⟩ who : ℝ) ≤
      (reward (quittingSingletonTerminal owner) who : ℝ)
    exact_mod_cast rationalPositiveSingletonColumnHazard_inactive
      reward owner hM hreward hcolumn hne

/-- The actual full behavioral debt is at most half the requested accuracy.
Never and all late replies are included by the full semantic cap. -/
theorem rationalPositiveSingletonColumnProfile_debtSum_le
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (rationalPositiveSingletonColumnProfile
          reward owner M hM hcolumn accuracy haccuracy)) ≤ (accuracy : ℝ) / 2 := by
  dsimp only [rationalPositiveSingletonColumnProfile, rationalPositiveSingletonColumnWord]
  apply rationalSoloExitWord_debtSum_le
  · exact hreward
  · exact howner
  · intro who hne
    exact (hcolumn who hne).le
  · intro who hne
    exact rationalPositiveSingletonColumnHazard_inactive
      reward owner hM hreward hcolumn hne

/-- The computed literal profile has full terminal Nash error below the request. -/
theorem rationalPositiveSingletonColumnProfile_nash
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (rationalQuittingRewardToReal reward))
      ((accuracy : ℝ) / 2)
      (rationalPositiveSingletonColumnProfile
        reward owner M hM hcolumn accuracy haccuracy) :=
  isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le _ _
    (rationalPositiveSingletonColumnProfile_debtSum_le
      reward owner M hM hreward howner hcolumn accuracy haccuracy)

/-- Exact independent finite date/Never laws of this computed word retain
the actual unrestricted semantic pair and total-debt guarantee. -/
theorem rationalPositiveSingletonColumnWord_finiteLaws
    (reward : RationalQuittingReward players) (owner : Fin players)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := rationalPositiveSingletonColumnWord reward owner M hM hcolumn accuracy haccuracy
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) =
        quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (rationalPositiveSingletonColumnProfile
            reward owner M hM hcolumn accuracy haccuracy) ∧
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
            word.length mixed)) ≤ (accuracy : ℝ) / 2 := by
  dsimp only
  let word := rationalPositiveSingletonColumnWord reward owner M hM hcolumn accuracy haccuracy
  obtain ⟨mixed, hmass, hsemantic⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  have hsame := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word
  have hequal := hsemantic.trans hsame.symm
  refine ⟨mixed, hmass, hequal, ?_⟩
  rw [hequal]
  exact rationalPositiveSingletonColumnProfile_debtSum_le
    reward owner M hM hreward howner hcolumn accuracy haccuracy

end

end GameTheory
