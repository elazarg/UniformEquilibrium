import UniformEquilibrium.Quitting.Examples.CrossedMatchingFixture
import UniformEquilibrium.Quitting.Classification.QuittingPremiumCore
import UniformEquilibrium.Quitting.Root.PureSetNashSureExit

/-! # Premium core and pure-coalition exclusions of the crossed-matching fixture

The only premium traps are the two scheduled pairs and the full player set.
Every pure stationary coalition profile, including all Never, admits a profitable
membership toggle. These finite exclusions do not exclude a uniform payoff.
-/

noncomputable section

namespace GameTheory.CrossedMatchingFixture

open QuittingSureSetOwnerRepair

/-- A participant has a positive own premium exactly at its scheduled pair. -/
theorem participant_positive_premium_iff (coalition : Finset (Fin 4)) (player : Fin 4) :
    (player ∈ coalition ∧ HasPositiveOwnQuittingPremium reward player coalition) ↔
      (coalition = {0, 2} ∧ (player = 0 ∨ player = 2)) ∨
        (coalition = {1, 3} ∧ (player = 1 ∨ player = 3)) := by
  by_cases hnonempty : coalition.Nonempty
  · have hpositive : HasPositiveOwnQuittingPremium reward player coalition ↔
        reward (quittingSingletonTerminal player) player <
          reward ⟨coalition, hnonempty⟩ player := by
      constructor
      · rintro ⟨_, hlt⟩
        exact hlt
      · intro hlt
        exact ⟨hnonempty, hlt⟩
    rw [hpositive]
    fin_cases coalition <;> fin_cases player <;>
      norm_num +decide [reward, Math.FiniteCoalition.binaryCode_finFour,
        quittingSingletonTerminal] at *
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    subst coalition
    simp only [Finset.notMem_empty, false_and, false_iff]
    fin_cases player <;> decide

/-- The census includes the empty set, which is not a trap. -/
theorem premium_trap_iff (active : Finset (Fin 4)) :
    IsQuittingPremiumTrap reward active ↔
      active = {0, 2} ∨ active = {1, 3} ∨ active = Finset.univ := by
  unfold IsQuittingPremiumTrap MathUE.IsFiniteCoalitionPremiumTrap
  simp_rw [participant_positive_premium_iff]
  fin_cases active <;> decide

theorem premium_core_eq_univ : quittingPremiumCore reward = Finset.univ := by
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  exact MathUE.IsFiniteCoalitionPremiumTrap.subset_core
    ((premium_trap_iff Finset.univ).mpr (Or.inr (Or.inr rfl)))

theorem premium_core_card : (quittingPremiumCore reward).card = 4 := by
  rw [premium_core_eq_univ]
  decide

theorem premium_core_not_card_le_two : ¬(quittingPremiumCore reward).card ≤ 2 := by
  rw [premium_core_card]
  decide

theorem premium_core_not_card_le_three : ¬(quittingPremiumCore reward).card ≤ 3 := by
  rw [premium_core_card]
  decide

/-- A concrete deviator for each pure coalition, including the empty one. -/
def pureCoalitionTogglePlayer (active : Finset (Fin 4)) : Fin 4 :=
  match Math.FiniteCoalition.binaryCode active with
  | 1 => 2
  | 2 => 3
  | 4 => 0
  | 5 => 1
  | 6 => 1
  | 8 => 1
  | 10 => 2
  | 11 => 1
  | 12 => 2
  | 14 => 1
  | _ => 0

theorem pure_coalition_toggle_profit (active : Finset (Fin 4)) :
    let player := pureCoalitionTogglePlayer active
    quittingSetReward reward active player <
      quittingSetReward reward
        (if player ∈ active then active.erase player else insert player active) player := by
  fin_cases active <;>
    norm_num +decide [pureCoalitionTogglePlayer, quittingSetReward, reward,
      Math.FiniteCoalition.binaryCode_finFour]

theorem not_sureExitSet (active : Finset (Fin 4)) :
    ¬IsQuittingSureExitSet reward active := by
  apply not_isQuittingSureExitSet_of_strict_toggle
  have hprofit := pure_coalition_toggle_profit active
  by_cases hmember : pureCoalitionTogglePlayer active ∈ active
  · left
    exact ⟨pureCoalitionTogglePlayer active, hmember,
      by simpa only [ite_eq_left hmember] using hprofit⟩
  · right
    exact ⟨pureCoalitionTogglePlayer active, hmember,
      by simpa only [ite_eq_right hmember] using hprofit⟩

/-- Actual terminal behavioral Nash fails for every pure stationary coalition. -/
theorem not_pure_coalition_terminalNash (active : Finset (Fin 4)) :
    ¬(quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward (quittingPureSetRoot active)) := by
  rw [isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet]
  exact not_sureExitSet active

theorem not_allNever_terminalNash :
    ¬(quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingAlwaysContinueProfile reward) := by
  simpa only [quittingStationaryProfile_pureSetRoot_empty] using
    not_pure_coalition_terminalNash ∅

end GameTheory.CrossedMatchingFixture
