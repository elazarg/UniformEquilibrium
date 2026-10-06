import UniformEquilibrium.Quitting.Examples.BoxedNashChargeTripleFixture
import UniformEquilibrium.Quitting.Examples.BoxedNashChargeFullCoreFixture
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-! # Literal forced-Quit floor and pure-coalition exclusions

These finite tests use the actual two boxed-charge reward tables. The product
laws used to refute a universal weighted floor need not be Nash. Pure-coalition
exclusion is the original terminal behavioral Nash statement, including Never.
No nonexistence of a uniform payoff or selected chronology is inferred.
-/

noncomputable section

namespace GameTheory.BoxedNashChargeFloorAndPureExclusions

open QuittingSureSetOwnerRepair

private theorem weighted_singleton_quit_eq
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (weights : Payoff (Fin 4)) (quitter : Fin 4) :
    (∑ player, weights player *
      (quittingRootQuitPayoff reward 0 (quittingPureSetRoot {quitter}) player -
        reward (quittingSingletonTerminal player) player)) =
      ∑ player, weights player *
        (quittingSetReward reward (insert player {quitter}) player -
          reward (quittingSingletonTerminal player) player) := by
  simp only [quittingRootQuitPayoff_pureSetRoot_eq_insert]

/-- Every nonnegative universal forced-Quit floor weight is zero. -/
theorem triple_universal_forcedQuit_floor_weights_eq_zero
    (weights : Payoff (Fin 4)) (hnonnegative : ∀ player, 0 ≤ weights player)
    (hfloor : ∀ root : Fin 4 → PMF Bool,
      0 ≤ ∑ player, weights player *
        (quittingRootQuitPayoff BoxedNashChargeTripleFixture.reward 0 root player -
          BoxedNashChargeTripleFixture.reward (quittingSingletonTerminal player) player)) :
    weights = 0 := by
  have hzero := hfloor (quittingPureSetRoot {0})
  have hone := hfloor (quittingPureSetRoot {1})
  have htwo := hfloor (quittingPureSetRoot {2})
  rw [weighted_singleton_quit_eq] at hzero hone htwo
  norm_num +decide [Fin.sum_univ_succ, quittingSetReward, BoxedNashChargeTripleFixture.reward,
    Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal] at hzero hone htwo
  have h0 := hnonnegative 0
  have h1 := hnonnegative 1
  have h2 := hnonnegative 2
  have h3 := hnonnegative 3
  funext player
  fin_cases player
  · change weights 0 = 0
    linarith
  · change weights 1 = 0
    linarith
  · change weights 2 = 0
    linarith
  · change weights 3 = 0
    linarith

theorem full_universal_forcedQuit_floor_weights_eq_zero
    (weights : Payoff (Fin 4)) (hnonnegative : ∀ player, 0 ≤ weights player)
    (hfloor : ∀ root : Fin 4 → PMF Bool,
      0 ≤ ∑ player, weights player *
        (quittingRootQuitPayoff BoxedNashChargeFullCoreFixture.reward 0 root player -
          BoxedNashChargeFullCoreFixture.reward (quittingSingletonTerminal player) player)) :
    weights = 0 := by
  have hzero := hfloor (quittingPureSetRoot {0})
  have hone := hfloor (quittingPureSetRoot {1})
  have htwo := hfloor (quittingPureSetRoot {2})
  have hthree := hfloor (quittingPureSetRoot {3})
  rw [weighted_singleton_quit_eq] at hzero hone htwo hthree
  norm_num +decide [Fin.sum_univ_succ, quittingSetReward, BoxedNashChargeFullCoreFixture.reward,
    Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal]
    at hzero hone htwo hthree
  have h0 := hnonnegative 0
  have h1 := hnonnegative 1
  have h2 := hnonnegative 2
  have h3 := hnonnegative 3
  funext player
  fin_cases player
  · change weights 0 = 0
    linarith
  · change weights 1 = 0
    linarith
  · change weights 2 = 0
    linarith
  · change weights 3 = 0
    linarith

private def tripleTogglePlayer (active : Finset (Fin 4)) : Fin 4 :=
  match Math.FiniteCoalition.binaryCode active with
  | 1 => 2
  | 3 => 1
  | 4 => 1
  | 6 => 2
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 13 => 3
  | 14 => 3
  | 15 => 3
  | _ => 0

private theorem triple_toggle_profit (active : Finset (Fin 4)) :
    let player := tripleTogglePlayer active
    quittingSetReward BoxedNashChargeTripleFixture.reward active player <
      quittingSetReward BoxedNashChargeTripleFixture.reward
        (if player ∈ active then active.erase player else insert player active) player := by
  fin_cases active <;>
    norm_num +decide [tripleTogglePlayer, quittingSetReward,
      BoxedNashChargeTripleFixture.reward, Math.FiniteCoalition.binaryCode_finFour]

theorem triple_not_sureExitSet (active : Finset (Fin 4)) :
    ¬IsQuittingSureExitSet BoxedNashChargeTripleFixture.reward active := by
  apply not_isQuittingSureExitSet_of_strict_toggle
  have hprofit := triple_toggle_profit active
  by_cases hmember : tripleTogglePlayer active ∈ active
  · left
    exact ⟨tripleTogglePlayer active, hmember, by simpa only [ite_eq_left hmember] using hprofit⟩
  · right
    exact ⟨tripleTogglePlayer active, hmember, by simpa only [ite_eq_right hmember] using hprofit⟩

theorem full_not_sureExitSet (active : Finset (Fin 4)) :
    ¬IsQuittingSureExitSet BoxedNashChargeFullCoreFixture.reward active := by
  fin_cases active <;>
    norm_num +decide [IsQuittingSureExitSet, Fin.forall_fin_succ, quittingSetReward,
      BoxedNashChargeFullCoreFixture.reward, Math.FiniteCoalition.binaryCode_finFour]

theorem triple_not_pure_terminalNash (active : Finset (Fin 4)) :
    ¬(quittingGame BoxedNashChargeTripleFixture.reward).IsεAsymptoticNash
      (quittingTerminalPayoff BoxedNashChargeTripleFixture.reward) 0
      (quittingStationaryProfile BoxedNashChargeTripleFixture.reward
        (quittingPureSetRoot active)) := by
  rw [isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet]
  exact triple_not_sureExitSet active

theorem full_not_pure_terminalNash (active : Finset (Fin 4)) :
    ¬(quittingGame BoxedNashChargeFullCoreFixture.reward).IsεAsymptoticNash
      (quittingTerminalPayoff BoxedNashChargeFullCoreFixture.reward) 0
      (quittingStationaryProfile BoxedNashChargeFullCoreFixture.reward
        (quittingPureSetRoot active)) := by
  rw [isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet]
  exact full_not_sureExitSet active

end GameTheory.BoxedNashChargeFloorAndPureExclusions
