/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.FinFourHopfConcreteChambers
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Forced pair defects of the sharp table, and the zero-solo screen of a ray

Two independent facts about
`GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel` and its
relation to the zero-minimum maximal-ray regressions.

The first is a screen exclusion.  Every
`GameTheory.FinFourMaximalRayZeroMinimumRegressions.Regression` carries a
vanishing solo reward at each player, and by
`GameTheory.isQuittingSureExitSet_empty_iff` that is exactly the empty
coalition passing the sure-exit test.  A regression table therefore always has
a pure coalition screen, so no table free of such screens can carry one.  On
the sharp table the solo rewards are `0`, `0`, `0` and the singleton level, so
a regression forces that level to vanish.

The second is the forced pure pair.  The sharp table carries the same
`GameTheory.FinFourMaximalRayZeroMinimumRegressions.LocalForcedPairFragment`
as the rational and full-binding completions, with packet owner three, marked
owner zero and payer one, at every real `R` and every real singleton level.
Its coordinate defect vector at the pure pair `{0, 3}` is `(0, 1, 1/100, 1)`,
against `(0, 1/100, 1/100, 1)` for both older completions: the marked owner is
slack in all three, but the two nonmembers carry distinct positive defects only
for the sharp table.
-/

noncomputable section

namespace GameTheory

namespace FinFourHopfConcreteChambers

open QuittingSureSetOwnerRepair

open FinFourMaximalRayZeroMinimumRegressions
  (Regression LocalForcedPairFragment rationalReward rationalScale
    rationalLocalForcedPairFragment fullBindingReward
    fullBindingLocalForcedPairFragment)

/-! ## The zero-solo screen carried by every ray regression -/

/-- **A ray regression always has a pure coalition screen.**  Its vanishing
solo rewards are exactly the empty coalition's sure-exit conditions, so the
all-continue profile is an exact terminal Nash profile of the table. -/
theorem isQuittingSureExitSet_empty_of_regression
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) :
    IsQuittingSureExitSet reward (∅ : Finset Player) := by
  rw [isQuittingSureExitSet_empty_iff]
  intro who
  rw [show quittingSoloReward reward who who =
    reward (quittingSingletonTerminal who) who from rfl, regression.zero_solo who]

/-- **Screen freeness excludes a ray regression.**  No table whose coalitions
are all refuted as sure exit sets carries a zero-minimum ray regression. -/
theorem not_forall_not_isQuittingSureExitSet_of_regression
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) :
    ¬ ∀ S : Finset Player, ¬ IsQuittingSureExitSet reward S :=
  fun hscreenFree ↦
    hscreenFree ∅ (isQuittingSureExitSet_empty_of_regression regression)

/-- **A ray regression pins the sharp table's singleton level to zero.**
Player three's solo exit pays that level, and a regression requires it to
vanish. -/
theorem singletonLevel_eq_zero_of_regression_sharpReward
    (R singletonLevel : ℝ)
    (regression : Regression (sharpReward R singletonLevel)) :
    singletonLevel = 0 := by
  have hthree := regression.zero_solo 3
  norm_num +decide [quittingSingletonTerminal, sharpReward,
    sharpSpectatorPassive, indicator] at hthree
  exact hthree

/-- **No ray regression at a positive singleton level.**  The sharp table
carries a zero-minimum ray regression at no positive singleton level and at no
real `R`. -/
theorem not_nonempty_regression_sharpReward (R singletonLevel : ℝ)
    (hlevel : 0 < singletonLevel) :
    ¬ Nonempty (Regression (sharpReward R singletonLevel)) := by
  rintro ⟨regression⟩
  exact absurd
    (singletonLevel_eq_zero_of_regression_sharpReward R singletonLevel regression)
    hlevel.ne'

/-! ## The forced pure pair of the sharp table -/

/-- **The sharp table's forced paid pair.**  Player three quits alone, player
zero joins it at a strict gain, and player one strictly gains again by joining
the resulting pair, while player zero's own defect at that pair vanishes.  All
three signs are rational constants, so no hypothesis on either parameter is
needed. -/
def sharpLocalForcedPairFragment (R singletonLevel : ℝ) :
    LocalForcedPairFragment (sharpReward R singletonLevel) where
  continuation := quittingAlwaysContinueProfile _
  singletonOwner := 3
  markedOwner := 0
  payer := 1
  packetOwner := 3
  singletonOwner_eq_packetOwner := rfl
  packetOwner_ne_markedOwner := by decide
  payer_ne_markedOwner := by decide
  payer_ne_packetOwner := by decide
  singletonProfile := quittingRootThenContinuationProfile _
    (quittingPureSetRoot {3}) (quittingAlwaysContinueProfile _)
  pairProfile := quittingRootThenContinuationProfile _
    (quittingPureSetRoot {0, 3}) (quittingAlwaysContinueProfile _)
  singletonProfile_eq := rfl
  pairProfile_eq := rfl
  marked_gain := by
    norm_num +decide [sharpReward, sharpActivePassive, sharpActiveGain,
      quittingSingletonTerminal, indicator, sharpScale]
  marked_pair_debt_eq_zero := by
    rw [quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      _ {0, 3} (by decide)]
    norm_num +decide [quittingTerminalSemanticDebt, quittingSetReward,
      sharpReward, sharpActivePassive, sharpActiveGain, indicator, sharpScale]
  payer_gain := by
    norm_num +decide [sharpReward, sharpActivePassive, sharpActiveGain,
      indicator, sharpScale]

/-- Coordinate defect vector of a forced pure pair, read at its own semantic
pair. -/
def forcedPairDebt
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (fragment : LocalForcedPairFragment reward) : Player → ℝ :=
  fun who ↦ quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward fragment.pairProfile) who

/-- **The sharp table's pair defect vector.**  At the pure pair `{0, 3}` the
marked owner is slack, the two nonmembers carry `1` and `1/100`, and the packet
owner carries `1`.  Every entry is a rational constant. -/
theorem forcedPairDebt_sharpLocalForcedPairFragment (R singletonLevel : ℝ) :
    forcedPairDebt (sharpLocalForcedPairFragment R singletonLevel) =
      ![0, 1, 1 / 100, 1] := by
  unfold forcedPairDebt
  rw [(sharpLocalForcedPairFragment R singletonLevel).pair_debt_eq]
  funext who
  fin_cases who <;>
    norm_num +decide [LocalForcedPairFragment.pairTerminal,
      sharpLocalForcedPairFragment, quittingSetReward, sharpReward,
      sharpActivePassive, sharpActiveGain, sharpSpectatorPassive, indicator,
      sharpScale, sharpLoss]

/-- **The two nonmembers carry distinct positive defects.**  The marked owner's
defect vanishes, and the two players outside the pure pair `{0, 3}` both gain
strictly by joining it, by different amounts. -/
theorem forcedPairDebt_sharp_zero_and_distinct_pos (R singletonLevel : ℝ) :
    forcedPairDebt (sharpLocalForcedPairFragment R singletonLevel) 0 = 0 ∧
      0 < forcedPairDebt (sharpLocalForcedPairFragment R singletonLevel) 1 ∧
        0 < forcedPairDebt (sharpLocalForcedPairFragment R singletonLevel) 2 ∧
          forcedPairDebt (sharpLocalForcedPairFragment R singletonLevel) 1 ≠
            forcedPairDebt (sharpLocalForcedPairFragment R singletonLevel) 2 := by
  rw [forcedPairDebt_sharpLocalForcedPairFragment]
  simp

/-! ## The older completions, for contrast -/

/-- **The rational completion's pair defect vector.**  Its two nonmembers carry
the same defect. -/
theorem forcedPairDebt_rationalLocalForcedPairFragment :
    forcedPairDebt rationalLocalForcedPairFragment = ![0, 1 / 100, 1 / 100, 1] := by
  unfold forcedPairDebt
  rw [rationalLocalForcedPairFragment.pair_debt_eq]
  funext who
  fin_cases who <;>
    norm_num +decide [LocalForcedPairFragment.pairTerminal,
      rationalLocalForcedPairFragment, quittingSetReward, rationalReward,
      FinFourMaximalRayZeroMinimumRegressions.rationalSpectatorReward,
      FinFourMaximalRayZeroMinimumRegressions.activeBaseReward,
      FinFourMaximalRayZeroMinimumRegressions.passive,
      FinFourMaximalRayZeroMinimumRegressions.interaction, rationalScale]

/-- **The full-binding completion's pair defect vector.**  Its two nonmembers
carry the same defect, at every spectator parameter. -/
theorem forcedPairDebt_fullBindingLocalForcedPairFragment (R : ℝ) :
    forcedPairDebt (fullBindingLocalForcedPairFragment R) =
      ![0, 1 / 100, 1 / 100, 1] := by
  unfold forcedPairDebt
  rw [(fullBindingLocalForcedPairFragment R).pair_debt_eq]
  funext who
  fin_cases who <;>
    norm_num +decide [LocalForcedPairFragment.pairTerminal,
      fullBindingLocalForcedPairFragment, quittingSetReward, fullBindingReward,
      FinFourMaximalRayZeroMinimumRegressions.fullBindingSpectatorReward,
      FinFourMaximalRayZeroMinimumRegressions.fullBindingSpectatorCoefficient,
      rationalReward, FinFourMaximalRayZeroMinimumRegressions.activeBaseReward,
      FinFourMaximalRayZeroMinimumRegressions.passive,
      FinFourMaximalRayZeroMinimumRegressions.interaction, rationalScale]
  have hcoefficient : ![R, -R - 1, 0, 0] (3 : Player) = 0 := by simp
  rw [hcoefficient, max_eq_right (by linarith)]
  ring

/-- **The older completions do not separate their two nonmembers.**  Both carry
equal pair defects there, so the distinct-defect property of
`forcedPairDebt_sharp_zero_and_distinct_pos` fails for them. -/
theorem forcedPairDebt_older_completions_not_distinct (R : ℝ) :
    forcedPairDebt rationalLocalForcedPairFragment 1 =
        forcedPairDebt rationalLocalForcedPairFragment 2 ∧
      forcedPairDebt (fullBindingLocalForcedPairFragment R) 1 =
        forcedPairDebt (fullBindingLocalForcedPairFragment R) 2 := by
  rw [forcedPairDebt_rationalLocalForcedPairFragment,
    forcedPairDebt_fullBindingLocalForcedPairFragment]
  simp

end FinFourHopfConcreteChambers

end GameTheory
