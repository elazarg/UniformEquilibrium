import UniformEquilibrium.Quitting.Cycles.BelowSingletonJointPhaseSource
import MathUE.Finset.CoalitionBinaryCode
import MathUE.Finset.FinFourNonemptyCoalitions
import Mathlib.Tactic.NormNum

/-! # The literal two-phase fixture below its singleton levels

The complete fifteen-row table has selected survival probability `2 / 3`.
Its actual phase values and one fixed terminal and finite-horizon profile are
derived from the raw table. Full-coordinate persistence, quantitative horizon
rates and the fixture's source-separation claims are separate results.
-/

noncomputable section

namespace GameTheory.BelowSingletonJointPhaseFixture

open PairedCycle Math.CrossedMatching Math.PairedAffine

private abbrev coalitionCode := @Math.FiniteCoalition.binaryCode 4

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.val with
    | 1 => ![1, 4, 0, 0]
    | 2 => ![4, 1, 0, 0]
    | 3 => ![1 / 2, 1 / 2, 0, 0]
    | 4 => ![0, 0, 1, 4]
    | 5 => ![-1 / 10, -119 / 60, -1 / 10, -119 / 60]
    | 6 => ![0, 1 / 2, 1 / 2, 0]
    | 7 => ![100, -3, 100, 0]
    | 8 => ![0, 0, 4, 1]
    | 9 => ![1 / 2, 0, 0, 1 / 2]
    | 10 => ![-119 / 60, -1 / 10, -119 / 60, -1 / 10]
    | 11 => ![-3, 100, 0, 100]
    | 12 => ![0, 0, 1 / 2, 1 / 2]
    | 13 => ![100, 0, 100, -3]
    | 14 => ![0, 100, -3, 100]
    | 15 => ![-101, -102, -103, -104]
    | _ => 0

theorem reward_rows (row : Fin 15) :
    reward (Math.Finset.finFourCoalitionRowEquiv row) =
      (![![1, 4, 0, 0], ![4, 1, 0, 0], ![1 / 2, 1 / 2, 0, 0],
        ![0, 0, 1, 4], ![-1 / 10, -119 / 60, -1 / 10, -119 / 60],
        ![0, 1 / 2, 1 / 2, 0], ![100, -3, 100, 0], ![0, 0, 4, 1],
        ![1 / 2, 0, 0, 1 / 2], ![-119 / 60, -1 / 10, -119 / 60, -1 / 10],
        ![-3, 100, 0, 100], ![0, 0, 1 / 2, 1 / 2], ![100, 0, 100, -3],
        ![0, 100, -3, 100], ![-101, -102, -103, -104]]
        : Fin 15 → Payoff (Fin 4)) row := by
  fin_cases row <;>
    norm_num +decide [reward, coalitionCode, Math.FiniteCoalition.binaryCode_finFour,
      Math.Finset.finFourCoalitionRowEquiv, Math.Finset.finFourCoalitionOfRow]

@[simp] theorem singleton_eq (player : Fin 4) : singleton reward player = 1 := by
  fin_cases player <;>
    norm_num +decide [PairedCycle.singleton, reward, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal]

theorem rawFamily : BelowSingleton.RawFamily reward (fun _ => 1) 3 (-11 / 10) (-179 / 60) := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro player
    fin_cases player <;>
      norm_num +decide [reward, PairedCycle.singleton, coalitionCode,
        Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal,
        favorite, scheduled, other]

theorem selected_mem : (2 / 3 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1 := by norm_num

theorem selected_root :
    Math.PairedBelowSingleton.polynomial 3 (-11 / 10) (-179 / 60) (2 / 3) = 0 := by
  norm_num [Math.PairedBelowSingleton.polynomial, Math.cubicAnchor]

def phaseValues : Fin 2 → Payoff (Fin 4) :=
  ![![19 / 30, 19 / 20, 19 / 30, 19 / 20],
    ![19 / 20, 19 / 30, 19 / 20, 19 / 30]]

theorem phaseValue_eq (phase : Fin 2) :
    twoPairPhaseValue reward fin4Schedule (fun _ => 1 - (2 / 3 : ℝ)) phase =
      phaseValues phase := by
  funext player
  unfold twoPairPhaseValue
  rw [BelowSingleton.activeValue_eq rawFamily, BelowSingleton.postValue_eq rawFamily,
    singleton_eq]
  have hfirst : fin4Schedule.phase 1 = 1 := fin4Schedule.phase_first 1
  have hsecond : fin4Schedule.phase 2 = 0 := fin4Schedule.phase_second 0
  have hthird : fin4Schedule.phase 3 = 1 := fin4Schedule.phase_second 1
  fin_cases phase <;> fin_cases player <;>
    norm_num [phaseValues, hfirst, hsecond, hthird]

theorem phaseValues_lt_singleton (phase : Fin 2) (player : Fin 4) :
    phaseValues phase player < singleton reward player := by
  rw [← phaseValue_eq]
  exact BelowSingleton.phaseValue_lt_singleton rawFamily selected_mem phase player

theorem activeValue_eq (player : Fin 4) :
    twoPairActiveValue reward fin4Schedule (fun _ => 1 - (2 / 3 : ℝ)) player =
      19 / 30 := by
  rw [BelowSingleton.activeValue_eq rawFamily, singleton_eq]
  norm_num

theorem postValue_eq (player : Fin 4) :
    twoPairPostValue reward fin4Schedule (fun _ => 1 - (2 / 3 : ℝ)) player =
      19 / 20 := by
  rw [BelowSingleton.postValue_eq rawFamily, singleton_eq]
  norm_num

theorem active_endpoints (player : Fin 4) :
    quittingRootQuitPayoff reward
        (phaseValues (finRotate 2 (fin4Schedule.phase player)))
        (cycle fin4Schedule (fun _ => 1 - (2 / 3 : ℝ))
          (properUnitBounds _ (fun _ => ⟨by norm_num, by norm_num⟩))
          (fin4Schedule.phase player)) player = 19 / 30 ∧
    quittingRootContinuePayoff reward
        (phaseValues (finRotate 2 (fin4Schedule.phase player)))
        (cycle fin4Schedule (fun _ => 1 - (2 / 3 : ℝ))
          (properUnitBounds _ (fun _ => ⟨by norm_num, by norm_num⟩))
          (fin4Schedule.phase player)) player = 19 / 30 := by
  rw [← phaseValue_eq]
  obtain ⟨hquit, hcontinue⟩ := twoPair_active_endpoints reward fin4Schedule
    (fun _ => 1 - (2 / 3 : ℝ)) (fun _ => ⟨by norm_num, by norm_num⟩) player
  exact ⟨hquit.trans (activeValue_eq player), hcontinue.trans (activeValue_eq player)⟩

theorem passive_continue_eq (player : Fin 4) :
    quittingRootContinuePayoff reward (phaseValues (fin4Schedule.phase player))
        (cycle fin4Schedule (fun _ => 1 - (2 / 3 : ℝ))
          (properUnitBounds _ (fun _ => ⟨by norm_num, by norm_num⟩))
          (finRotate 2 (fin4Schedule.phase player))) player = 19 / 20 := by
  rw [← phaseValue_eq]
  exact (BelowSingleton.passive_continue rawFamily selected_mem selected_root player).trans
    (postValue_eq player)

theorem passive_quit_eq (player : Fin 4) :
    quittingRootQuitPayoff reward (phaseValues (fin4Schedule.phase player))
        (cycle fin4Schedule (fun _ => 1 - (2 / 3 : ℝ))
          (properUnitBounds _ (fun _ => ⟨by norm_num, by norm_num⟩))
          (finRotate 2 (fin4Schedule.phase player))) player = 1 / 3 := by
  rw [fin4Schedule_passive_root]
  have hne : favorite player ≠ other player := by fin_cases player <;> decide
  rw [rootQuit_eq_bellman reward _ hne, quittingHazardCoin_true_toReal]
  fin_cases player <;>
    norm_num +decide [bellman, contribution, reward, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, favorite, other]

theorem passive_gap_eq (player : Fin 4) :
    twoPairPostValue reward fin4Schedule (fun _ => 1 - (2 / 3 : ℝ)) player -
      quittingRootQuitPayoff reward (phaseValues (fin4Schedule.phase player))
        (cycle fin4Schedule (fun _ => 1 - (2 / 3 : ℝ))
          (properUnitBounds _ (fun _ => ⟨by norm_num, by norm_num⟩))
          (finRotate 2 (fin4Schedule.phase player))) player = 37 / 60 := by
  rw [postValue_eq, passive_quit_eq]
  norm_num

theorem caps_strict (player : Fin 4) :
    reward ⟨{player, favorite player}, by simp⟩ player < 13 / 15 ∧
    reward ⟨{player, other player}, by simp⟩ player < 13 / 15 ∧
    reward ⟨{player, favorite player, other player}, by simp⟩ player < 13 / 15 := by
  fin_cases player <;>
    norm_num +decide [reward, coalitionCode, Math.FiniteCoalition.binaryCode_finFour,
      favorite, other]

def profile : (quittingGame reward).BehaviorProfile :=
  BelowSingleton.profile reward (2 / 3) selected_mem

/-- The displayed rational profile is terminal Nash and works at every accuracy. -/
theorem exact_terminal_and_fixedProfile :
    quittingTerminalPayoff reward profile = phaseValues 0 ∧
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile ∧
    (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ,
      ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon ε profile ∧
          ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon profile player -
            phaseValues 0 player| ≤ ε) ∧
    (quittingGame reward).IsUniformEquilibriumPayoff none (phaseValues 0) := by
  have hresult := twoPair_exact_terminal_and_fixedProfile reward fin4Schedule
    (fun _ => 1 - (2 / 3 : ℝ))
    (fun _ => ⟨by norm_num, by norm_num⟩)
    (BelowSingleton.passive_continue rawFamily selected_mem selected_root)
    (fun player => (BelowSingleton.passive_quit_lt rawFamily selected_mem player).le) 0
  simpa only [profile, BelowSingleton.profile, phaseValue_eq] using hresult

theorem isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none (phaseValues 0) :=
  exact_terminal_and_fixedProfile.2.2.2

end GameTheory.BelowSingletonJointPhaseFixture
