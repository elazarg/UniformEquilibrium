/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.StationaryOrSmallHazard
import UniformEquilibrium.Quitting.Terminal.TerminalAffineNashTransfer
import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Classification.OnePlayer.StationaryBranch

/-!
# Positive scaling and player transport of stationary-or-small-hazard equilibria

Coordinate scaling preserves zero Never payoff and the actual selected roots.
Player reindexing pulls those same stationary roots and date-indexed roots
back along an equivalence. No additive terminal translation is used.

All reward signs are covered at at most two players. At three players the
producer requires every own-singleton reward to be strictly positive.
-/

noncomputable section

namespace GameTheory.QuittingThreePlayerStrategyClass

open StochasticGame Filter QuittingTwoPlayerExistence

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Increasing the requested error preserves both strategy classes. -/
theorem StationaryOrSmallHazardTerminalEquilibrium.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε η : ℝ}
    (h : StationaryOrSmallHazardTerminalEquilibrium reward ε) (hle : ε ≤ η) :
    StationaryOrSmallHazardTerminalEquilibrium reward η := by
  rcases h with ⟨root, hnash⟩ | ⟨roots, hhazard, hnash⟩
  · exact Or.inl ⟨root, hnash.mono hle⟩
  · exact Or.inr ⟨roots, fun time who => (hhazard time who).trans hle, hnash.mono hle⟩

/-- Zero-shift playerwise scaling preserves the actual root or root sequence.
The hazard bound is transported by the independent accuracy inequality. -/
theorem StationaryOrSmallHazardTerminalEquilibrium.playerwiseScale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (scale : Payoff ι)
    {ε η : ℝ} (hscale : ∀ who, 0 ≤ scale who)
    (hsource : StationaryOrSmallHazardTerminalEquilibrium reward ε)
    (haccuracy : ε ≤ η) (herror : ∀ who, scale who * ε ≤ η) :
    StationaryOrSmallHazardTerminalEquilibrium
      (quittingPlayerwiseAffineReward reward scale 0) η := by
  rcases hsource with ⟨root, hnash⟩ | ⟨roots, hhazard, hnash⟩
  · exact Or.inl ⟨root, isεAsymptoticNash_playerwiseScale reward scale
      (quittingStationaryProfile reward root) hscale hnash herror⟩
  · exact Or.inr ⟨roots, fun time who => (hhazard time who).trans haccuracy,
      isεAsymptoticNash_playerwiseScale reward scale
        (quittingRootSequenceProfile reward roots 0) hscale hnash herror⟩

/-- Player pullback retains the stationary root or literal root sequence;
each date/player Quit hazard is unchanged at its corresponding coordinate. -/
theorem of_reindex (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hsource : StationaryOrSmallHazardTerminalEquilibrium
      (quittingRewardReindex e reward) ε) :
    StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  rcases hsource with ⟨root, hnash⟩ | ⟨roots, hhazard, hnash⟩
  · exact Or.inl ⟨fun who => root (e who), isεAsymptoticNash_quittingProfilePullback e reward
      (quittingStationaryProfile (quittingRewardReindex e reward) root) hnash⟩
  · exact Or.inr ⟨fun time who => roots time (e who), fun time who => hhazard time (e who),
      isεAsymptoticNash_quittingProfilePullback e reward
        (quittingRootSequenceProfile (quittingRewardReindex e reward) roots 0) hnash⟩

/-- Positive own-singletons are normalized by multiplication alone, keeping
Never payoff zero. The normalized producer's actual roots are retained. -/
theorem of_positiveSoloThreePlayer
    (reward : QuittingReward3)
    (hpositive : ∀ who, 0 < reward (quittingSingletonTerminal who) who)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  let scale : Payoff (Fin 3) := fun who => reward (quittingSingletonTerminal who) who
  let normalized := quittingPlayerwiseAffineReward reward (fun who => 1 / scale who) 0
  have hnormalized : ∀ who, normalized (quittingSingletonTerminal who) who = 1 := by
    intro who
    simp [normalized, quittingPlayerwiseAffineReward, scale, div_eq_mul_inv,
      (hpositive who).ne']
  let M := quittingRewardBound reward
  let δ := ε / (M + 1)
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hden : 0 < M + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hidentity : (M + 1) * δ = ε := by
    dsimp only [δ]
    field_simp [hden.ne']
  have hδle : δ ≤ ε := by nlinarith [mul_nonneg hM hδ.le]
  have herror : ∀ who, scale who * δ ≤ ε := by
    intro who
    have hbound : scale who ≤ M :=
      (abs_le.mp (abs_reward_le_quittingRewardBound reward
        (quittingSingletonTerminal who) who)).2
    have hscaled := mul_le_mul_of_nonneg_right hbound hδ.le
    nlinarith
  have hsource := of_normalizedThreePlayer normalized hnormalized hδ
  have hscaled := hsource.playerwiseScale normalized scale
    (fun who => (hpositive who).le) hδle herror
  have hreward : quittingPlayerwiseAffineReward normalized scale 0 = reward := by
    funext terminal who
    change scale who * ((1 / scale who) * reward terminal who + 0) + 0 = reward terminal who
    have hne : scale who ≠ 0 := (hpositive who).ne'
    simp only [add_zero, one_div]
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [hreward] at hscaled
  exact hscaled

/-- The unrestricted two-player producer transports its actual stationary
root to every finite player type of cardinality two. -/
theorem exists_stationaryTerminalNash_of_card_eq_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι = 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward root) := by
  let e : ι ≃ Bool := (Fintype.equivFinOfCardEq hcard).trans finTwoEquiv
  obtain ⟨root, hnash⟩ :=
    quittingGame_exists_stationary_terminalApproximateEquilibrium_twoPlayer
      (quittingRewardReindex e reward) ε hε
  exact ⟨fun who => root (e who), isεAsymptoticNash_quittingProfilePullback e reward
    (quittingStationaryProfile (quittingRewardReindex e reward) root) hnash⟩

/-- Every table on at most two players has an actual stationary terminal
approximate equilibrium; zero and one players use existing trivial branches. -/
theorem exists_stationaryTerminalNash_of_card_le_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι ≤ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward root) := by
  interval_cases hcase : Fintype.card ι
  · let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcase
    exact ⟨fun who => isEmptyElim who, fun who => isEmptyElim who⟩
  · let : Unique ι := (Fintype.card_eq_one_iff_nonempty_unique.mp hcase).some
    exact quittingStationaryεEquilibriumExistence_onePlayer reward ε hε
  · exact exists_stationaryTerminalNash_of_card_eq_two reward hcase hε

/-- The positive-own-singleton three-player producer transports along an
enumeration without changing its strategy class or Quit hazards. -/
theorem of_positiveSolo_of_card_eq_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι = 3)
    (hpositive : ∀ who, 0 < reward (quittingSingletonTerminal who) who)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  let e : ι ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  apply of_reindex e reward
  apply of_positiveSoloThreePlayer (quittingRewardReindex e reward) _ hε
  intro who
  have hsingleton : (quittingCoalitionEquiv e).symm (quittingSingletonTerminal who) =
      quittingSingletonTerminal (e.symm who) := by
    apply Subtype.ext
    simp [quittingCoalitionEquiv, quittingSingletonTerminal]
  change 0 < reward ((quittingCoalitionEquiv e).symm (quittingSingletonTerminal who))
    (e.symm who)
  rw [hsingleton]
  exact hpositive (e.symm who)

/-- All reward signs are retained for zero, one, and two players. Only the
three-player branch requires strictly positive own-singleton rewards. -/
theorem of_card_le_three_of_positiveSolo_when_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι ≤ 3)
    (hpositive : Fintype.card ι = 3 →
      ∀ who, 0 < reward (quittingSingletonTerminal who) who)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  by_cases hthree : Fintype.card ι = 3
  · exact of_positiveSolo_of_card_eq_three reward hthree (hpositive hthree) hε
  · have htwo : Fintype.card ι ≤ 2 := by omega
    exact Or.inl (exists_stationaryTerminalNash_of_card_le_two reward htwo hε)

/-- The positive-own-singleton source discussion holds for every finite
player type with at most three players, including the smaller cardinalities. -/
theorem of_card_le_three_of_positiveSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι ≤ 3)
    (hpositive : ∀ who, 0 < reward (quittingSingletonTerminal who) who)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε :=
  of_card_le_three_of_positiveSolo_when_three reward hcard (fun _ => hpositive) hε

end GameTheory.QuittingThreePlayerStrategyClass
