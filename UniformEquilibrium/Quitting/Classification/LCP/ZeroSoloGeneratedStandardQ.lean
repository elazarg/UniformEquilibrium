/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveAbsorptionStationarySplice
import UniformEquilibrium.Quitting.Classification.LCP.StationaryExistence
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# Zero solo, generated stationary prefixes, or the standard-Q side

The elementary solo-payoff fork turns the production stationary-existence
gate into a three-way conclusion.  Outside the zero-solo branch, one player
has a strictly positive solo payoff.  Any stationary behavioral equilibrium
whose error is below that payoff must absorb: a nonabsorbing product root is
the all-Continue root, against which immediate solo Quit is profitable.

Thus the stationary side of
`hasQuittingStationaryApproximateEquilibria_or_standardQMatrixSide` supplies
the cofinal positive-absorption family consumed by the stationary-prefix
splice theorem.  The result makes no assertion on the standard-Q side.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Every finite quitting reward table is either zero-solo or has a strictly
positive solo payoff.  The statement is valid on an empty player type: the
zero-solo disjunct is then vacuous. -/
theorem isQuittingZeroSolo_or_exists_positiveSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsQuittingZeroSolo reward ∨
      ∃ who : ι, 0 < reward (quittingSingletonTerminal who) who := by
  by_cases hzero : IsQuittingZeroSolo reward
  · exact Or.inl hzero
  · right
    unfold IsQuittingZeroSolo at hzero
    push Not at hzero
    exact hzero

/-- Below a fixed positive solo payoff, a stationary behavioral approximate
equilibrium must have positive one-stage absorption. -/
theorem quittingRootAbsorptionMass_pos_of_stationaryNash_lt_positiveSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {error : ℝ} (herror : 0 ≤ error) (root : ι → PMF Bool)
    (hnash : IsεQuittingStationaryNash reward error root)
    (who : ι) (hsolo : error < reward (quittingSingletonTerminal who) who) :
    0 < quittingRootAbsorptionMass root := by
  by_contra hnot
  have habsorptionZero : quittingRootAbsorptionMass root = 0 :=
    le_antisymm (le_of_not_gt hnot) (quittingRootAbsorptionMass_nonneg root)
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at habsorptionZero
    linarith
  have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) := by
    funext player
    exact eq_pure_false_of_quittingStationaryContinueMass_eq_one
      hcontinue player
  have hprofile : quittingStationaryProfile reward root =
      quittingAlwaysContinueProfile reward := by
    subst root
    rfl
  have hnashContinue :
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) error
        (quittingAlwaysContinueProfile reward) := by
    rw [← hprofile]
    exact hnash
  have hsoloLe :=
    (isεAsymptoticNash_quittingAlwaysContinue_iff reward herror).mp
      hnashContinue who
  linarith

/-- A stationary approximate-equilibrium family on a non-zero-solo table is
cofinally positive absorbing. -/
theorem hasArbitrarilyAccuratePositiveAbsorptionStationaryEquilibria_of_not_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hstationary : HasQuittingStationaryApproximateEquilibria reward)
    (hnotZero : ¬IsQuittingZeroSolo reward) :
    HasArbitrarilyAccuratePositiveAbsorptionStationaryEquilibria reward := by
  obtain ⟨who, hsolo⟩ :=
    (isQuittingZeroSolo_or_exists_positiveSolo reward).resolve_left hnotZero
  intro upper hupper
  let error := min (upper / 2)
    (reward (quittingSingletonTerminal who) who / 2)
  have herror : 0 < error := by
    exact lt_min (by linarith) (by linarith)
  obtain ⟨root, hnash⟩ := hstationary error herror
  have herrorUpper : error < upper :=
    (min_le_left _ _).trans_lt (by linarith)
  have herrorSolo : error < reward (quittingSingletonTerminal who) who :=
    (min_le_right _ _).trans_lt (by linarith)
  exact ⟨error, root, herror, herrorUpper, hnash,
    quittingRootAbsorptionMass_pos_of_stationaryNash_lt_positiveSolo
      reward herror.le root hnash who herrorSolo⟩

/-- Stationary approximability is already enough for the elementary residual
fork: either every own singleton reward is nonpositive, or the positive-solo
argument generates punished stationary prefixes. -/
theorem isQuittingZeroSolo_or_stationarilyGenerated_of_stationaryApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hstationary : HasQuittingStationaryApproximateEquilibria reward) :
    IsQuittingZeroSolo reward ∨
      QuittingStationarilyGeneratedApproximateEquilibria reward := by
  by_cases hzero : IsQuittingZeroSolo reward
  · exact Or.inl hzero
  · exact Or.inr
      (quittingStationarilyGeneratedApproximateEquilibria_of_positiveAbsorptionStationary
        reward
        (hasArbitrarilyAccuratePositiveAbsorptionStationaryEquilibria_of_not_zeroSolo
          reward hstationary hzero))

namespace QuittingLCPClassification

/-- **Stationary-prefix/standard-Q dichotomy off zero solo.** -/
theorem stationarilyGenerated_or_standardQMatrixSide_of_not_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnotZero : ¬IsQuittingZeroSolo reward) :
    QuittingStationarilyGeneratedApproximateEquilibria reward ∨
      StandardQMatrixSide reward := by
  rcases hasQuittingStationaryApproximateEquilibria_or_standardQMatrixSide
      reward with hstationary | hstandard
  · exact Or.inl
      (quittingStationarilyGeneratedApproximateEquilibria_of_positiveAbsorptionStationary
        reward
        (hasArbitrarilyAccuratePositiveAbsorptionStationaryEquilibria_of_not_zeroSolo
          reward hstationary hnotZero))
  · exact Or.inr hstandard

/-- **Zero solo / stationarily generated / standard-Q trichotomy.**  This is
an exhaustive classification of the conclusions supplied by the production
stationary LCP gate and the positive-absorption splice.  It does not solve or
classify the standard-Q side. -/
theorem zeroSolo_or_stationarilyGenerated_or_standardQMatrixSide
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsQuittingZeroSolo reward ∨
      QuittingStationarilyGeneratedApproximateEquilibria reward ∨
      StandardQMatrixSide reward := by
  by_cases hzero : IsQuittingZeroSolo reward
  · exact Or.inl hzero
  · exact Or.inr
      (stationarilyGenerated_or_standardQMatrixSide_of_not_zeroSolo
        reward hzero)

/-- Excluding the stationary-prefix residual leaves either the nonpositive
solo class or the standard-Q side. -/
theorem zeroSolo_or_standardQMatrixSide_of_not_stationarilyGenerated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnotGenerated :
      ¬QuittingStationarilyGeneratedApproximateEquilibria reward) :
    IsQuittingZeroSolo reward ∨ StandardQMatrixSide reward := by
  rcases zeroSolo_or_stationarilyGenerated_or_standardQMatrixSide reward with
    hzero | hgenerated | hstandard
  · exact Or.inl hzero
  · exact absurd hgenerated hnotGenerated
  · exact Or.inr hstandard

/-- Off the nonpositive-solo class, failure of the stationary-prefix residual
forces the production standard-Q side. -/
theorem standardQMatrixSide_of_not_zeroSolo_of_not_stationarilyGenerated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnotZero : ¬IsQuittingZeroSolo reward)
    (hnotGenerated :
      ¬QuittingStationarilyGeneratedApproximateEquilibria reward) :
    StandardQMatrixSide reward := by
  exact
    (zeroSolo_or_standardQMatrixSide_of_not_stationarilyGenerated
      reward hnotGenerated).resolve_left hnotZero

end QuittingLCPClassification
end GameTheory
