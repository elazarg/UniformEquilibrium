import UniformEquilibrium.Quitting.Cycles.CrossedMatchingPhaseSource
import MathUE.Finset.CoalitionBinaryCode
import MathUE.Finset.FinFourNonemptyCoalitions
import Mathlib.Tactic.NormNum

/-! # The literal asymmetric crossed-matching table

This fixture uses all sixty printed reward coordinates. Matrix, child-debt,
response-quotient and stationary-support separations are separate obligations.
-/

noncomputable section

namespace GameTheory.CrossedMatchingFixture

open PairedCycle Math.CrossedMatching

private abbrev coalitionCode := @Math.FiniteCoalition.binaryCode 4

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.val with
    | 1 => ![1, 61 / 8, 0, 0]
    | 2 => ![289 / 40, 1, 0, 0]
    | 3 => ![-1, -1, 0, 0]
    | 4 => ![0, 0, 1, 61 / 8]
    | 5 => ![177 / 32, 0, 177 / 32, 0]
    | 6 => ![0, -1, -1, 0]
    | 7 => ![-10, 1 / 2, -10, 0]
    | 8 => ![0, 0, 61 / 8, 1]
    | 9 => ![-1, 0, 0, -1]
    | 10 => ![2, 113 / 14, 0, 113 / 14]
    | 11 => ![1 / 2, -10, 0, -10]
    | 12 => ![0, 0, -1, -1]
    | 13 => ![-10, 0, -10, 1 / 2]
    | 14 => ![0, -10, 1 / 2, -10]
    | 15 => ![-11, -12, -13, -14]
    | _ => 0

theorem reward_rows (row : Fin 15) :
    reward (Math.Finset.finFourCoalitionRowEquiv row) =
      (![![1, 61 / 8, 0, 0], ![289 / 40, 1, 0, 0], ![-1, -1, 0, 0],
        ![0, 0, 1, 61 / 8], ![177 / 32, 0, 177 / 32, 0], ![0, -1, -1, 0],
        ![-10, 1 / 2, -10, 0], ![0, 0, 61 / 8, 1], ![-1, 0, 0, -1],
        ![2, 113 / 14, 0, 113 / 14], ![1 / 2, -10, 0, -10], ![0, 0, -1, -1],
        ![-10, 0, -10, 1 / 2], ![0, -10, 1 / 2, -10], ![-11, -12, -13, -14]]
        : Fin 15 → Payoff (Fin 4)) row := by
  fin_cases row <;>
    norm_num +decide [reward, coalitionCode, Math.FiniteCoalition.binaryCode_finFour,
      Math.Finset.finFourCoalitionRowEquiv, Math.Finset.finFourCoalitionOfRow]

theorem rawSource : CrossedMatching.RawSource reward := by
  constructor <;> intro player <;> fin_cases player <;>
    norm_num +decide [reward, PairedCycle.singleton, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal,
      favorite, scheduled, other]

def odds : Fin 4 → ℝ := ![1 / 4, 1 / 5, 1 / 4, 1 / 5]

theorem odds_positive (player : Fin 4) : 0 < odds player := by
  fin_cases player <;> norm_num [odds]

theorem passive_equations (player : Fin 4) :
    passiveEquation (quittingProjectiveLCPMatrix reward) (TwoPairOdds.premium reward)
      (TwoPairOdds.passive reward) odds player = 0 := by
  fin_cases player <;>
    norm_num +decide [passiveEquation, TwoPairOdds.premium, TwoPairOdds.passive,
      quittingProjectiveLCPMatrix, quittingProjectiveSingletonTerminal,
      reward, PairedCycle.singleton, odds, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour,
      quittingSingletonTerminal, favorite, scheduled, other]

def phaseValues : Fin 2 → Payoff (Fin 4) :=
  ![![61 / 32, 183 / 70, 61 / 32, 183 / 70],
    ![305 / 128, 61 / 28, 305 / 128, 61 / 28]]

theorem activeValue_eq (player : Fin 4) :
    twoPairActiveValue reward fin4Schedule (TwoPairOdds.hazard odds) player =
      (![61 / 32, 61 / 28, 61 / 32, 61 / 28] : Fin 4 → ℝ) player := by
  rw [TwoPairOdds.activeValue_eq]
  fin_cases player <;>
    norm_num +decide [TwoPairOdds.premium, TwoPairOdds.hazard, reward, PairedCycle.singleton, odds,
      coalitionCode, Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal,
      scheduled]

theorem postValue_eq (player : Fin 4) :
    twoPairPostValue reward fin4Schedule (TwoPairOdds.hazard odds) player =
      (![305 / 128, 183 / 70, 305 / 128, 183 / 70] : Fin 4 → ℝ) player := by
  rw [TwoPairOdds.postValue_eq reward odds_positive, TwoPairOdds.matrix_entry]
  fin_cases player <;>
    norm_num +decide [TwoPairOdds.premium, reward, PairedCycle.singleton, odds, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal, scheduled]

theorem phaseValue_eq (phase : Fin 2) :
    twoPairPhaseValue reward fin4Schedule (TwoPairOdds.hazard odds) phase =
      phaseValues phase := by
  funext player
  unfold twoPairPhaseValue
  rw [activeValue_eq, postValue_eq]
  have hfirst : fin4Schedule.phase 1 = 1 := fin4Schedule.phase_first 1
  have hsecond : fin4Schedule.phase 2 = 0 := fin4Schedule.phase_second 0
  have hthird : fin4Schedule.phase 3 = 1 := fin4Schedule.phase_second 1
  fin_cases phase <;> fin_cases player <;>
    norm_num [phaseValues, hfirst, hsecond, hthird]

theorem active_endpoints (player : Fin 4) :
    quittingRootQuitPayoff reward
        (phaseValues (finRotate 2 (fin4Schedule.phase player)))
        (cycle fin4Schedule (TwoPairOdds.hazard odds)
          (properUnitBounds _ (TwoPairOdds.hazard_proper odds_positive))
          (fin4Schedule.phase player)) player =
      (![61 / 32, 61 / 28, 61 / 32, 61 / 28] : Fin 4 → ℝ) player ∧
    quittingRootContinuePayoff reward
        (phaseValues (finRotate 2 (fin4Schedule.phase player)))
        (cycle fin4Schedule (TwoPairOdds.hazard odds)
          (properUnitBounds _ (TwoPairOdds.hazard_proper odds_positive))
          (fin4Schedule.phase player)) player =
      (![61 / 32, 61 / 28, 61 / 32, 61 / 28] : Fin 4 → ℝ) player := by
  simpa only [phaseValue_eq, activeValue_eq] using
    twoPair_active_endpoints reward fin4Schedule (TwoPairOdds.hazard odds)
      (TwoPairOdds.hazard_proper odds_positive) player

theorem passive_continue_eq (player : Fin 4) :
    quittingRootContinuePayoff reward (phaseValues (fin4Schedule.phase player))
        (cycle fin4Schedule (TwoPairOdds.hazard odds)
          (properUnitBounds _ (TwoPairOdds.hazard_proper odds_positive))
          (finRotate 2 (fin4Schedule.phase player))) player =
      (![305 / 128, 183 / 70, 305 / 128, 183 / 70] : Fin 4 → ℝ) player := by
  rw [← phaseValue_eq]
  exact (TwoPairOdds.passive_continue reward odds_positive passive_equations player).trans
    (postValue_eq player)

theorem passive_quit_eq (player : Fin 4) :
    quittingRootQuitPayoff reward (phaseValues (fin4Schedule.phase player))
        (cycle fin4Schedule (TwoPairOdds.hazard odds)
          (properUnitBounds _ (TwoPairOdds.hazard_proper odds_positive))
          (finRotate 2 (fin4Schedule.phase player))) player =
      (![31 / 72, 17 / 50, 31 / 72, 17 / 50] : Fin 4 → ℝ) player := by
  rw [fin4Schedule_passive_root]
  have hne : favorite player ≠ other player := by fin_cases player <;> decide
  rw [rootQuit_eq_bellman reward _ hne, quittingHazardCoin_true_toReal]
  fin_cases player <;>
    norm_num +decide [Math.PairedAffine.bellman, Math.PairedAffine.contribution,
      TwoPairOdds.hazard, odds, reward, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, favorite, other]

def profile (initial : Fin 2) : (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward
    (cycle fin4Schedule (TwoPairOdds.hazard odds)
      (properUnitBounds _ (TwoPairOdds.hazard_proper odds_positive))) initial

/-- One literal rational profile supplies every accuracy at sufficiently long horizons. -/
theorem exact_terminal_and_fixedProfile (initial : Fin 2) :
    quittingTerminalPayoff reward (profile initial) = phaseValues initial ∧
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (profile initial) ∧
    (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
      (quittingGame reward).IsεHorizonNash none horizon ε (profile initial) ∧
        ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon
          (profile initial) player - phaseValues initial player| ≤ ε) ∧
    (quittingGame reward).IsUniformEquilibriumPayoff none (phaseValues initial) := by
  have hresult := twoPair_exact_terminal_and_fixedProfile reward fin4Schedule
    (TwoPairOdds.hazard odds) (TwoPairOdds.hazard_proper odds_positive)
    (TwoPairOdds.passive_continue reward odds_positive passive_equations)
    (CrossedMatching.passive_quit rawSource odds_positive) initial
  simpa only [profile, phaseValue_eq] using hresult

theorem isUniformEquilibriumPayoff (initial : Fin 2) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (phaseValues initial) :=
  (exact_terminal_and_fixedProfile initial).2.2.2

abbrev RewardTable := {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)

/-- Strict inequalities on the actual sixty reward coordinates; no odds are inputs. -/
def strictRegion : Set RewardTable := {nearby | ∀ player,
  PairedCycle.singleton nearby player <
    nearby (quittingSingletonTerminal (favorite player)) player ∧
  nearby (quittingSingletonTerminal (scheduled player)) player <
    PairedCycle.singleton nearby player ∧
  nearby (quittingSingletonTerminal (other player)) player < PairedCycle.singleton nearby player ∧
  nearby (quittingSingletonTerminal (scheduled player)) player <
    nearby ⟨{player, scheduled player}, by simp⟩ player ∧
  nearby ⟨{player, favorite player}, by simp⟩ player < PairedCycle.singleton nearby player ∧
  nearby ⟨{player, other player}, by simp⟩ player < PairedCycle.singleton nearby player ∧
  nearby ⟨{player, favorite player, other player}, by simp⟩ player <
    PairedCycle.singleton nearby player}

private theorem continuous_entry (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (player : Fin 4) : Continuous (fun nearby : RewardTable => nearby terminal player) :=
  (continuous_apply player).comp (continuous_apply terminal)

theorem isOpen_strictRegion : IsOpen strictRegion := by
  unfold strictRegion
  simp only [Set.ofPred_forall, Set.ofPred_and]
  apply isOpen_iInter_of_finite
  intro player
  have hsolo : Continuous (fun nearby : RewardTable => PairedCycle.singleton nearby player) :=
    continuous_entry (quittingSingletonTerminal player) player
  exact (isOpen_lt hsolo (continuous_entry _ _)).inter
    ((isOpen_lt (continuous_entry _ _) hsolo).inter
      ((isOpen_lt (continuous_entry _ _) hsolo).inter
        ((isOpen_lt (continuous_entry _ _) (continuous_entry _ _)).inter
          ((isOpen_lt (continuous_entry _ _) hsolo).inter
            ((isOpen_lt (continuous_entry _ _) hsolo).inter
              (isOpen_lt (continuous_entry _ _) hsolo))))))

theorem mem_strictRegion : reward ∈ strictRegion := by
  intro player
  fin_cases player <;>
    norm_num +decide [reward, PairedCycle.singleton, coalitionCode,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal,
      favorite, scheduled, other]

theorem rawSource_of_mem_strictRegion {nearby : RewardTable} (hnearby : nearby ∈ strictRegion) :
    CrossedMatching.RawSource nearby := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun player => (hnearby player).1
  · exact fun player => (hnearby player).2.1
  · exact fun player => (hnearby player).2.2.1
  · exact fun player => (hnearby player).2.2.2.1
  · exact fun player => (hnearby player).2.2.2.2.1.le
  · exact fun player => (hnearby player).2.2.2.2.2.1.le
  · exact fun player => (hnearby player).2.2.2.2.2.2.le

/-- Every game in this open full-coordinate neighborhood has its own fixed UE target. -/
theorem exists_open_reward_neighborhood : ∃ neighborhood : Set RewardTable,
    IsOpen neighborhood ∧ reward ∈ neighborhood ∧
      ∀ nearby ∈ neighborhood, ∃ target : Payoff (Fin 4),
        (quittingGame nearby).IsUniformEquilibriumPayoff none target := by
  refine ⟨strictRegion, isOpen_strictRegion, mem_strictRegion, ?_⟩
  intro nearby hnearby
  exact CrossedMatching.exists_uniformEquilibriumPayoff (rawSource_of_mem_strictRegion hnearby)

end GameTheory.CrossedMatchingFixture
