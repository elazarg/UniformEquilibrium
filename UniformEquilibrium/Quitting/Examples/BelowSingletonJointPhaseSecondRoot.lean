import UniformEquilibrium.Quitting.Examples.BelowSingletonJointPhaseFixture
import UniformEquilibrium.Quitting.Cycles.TwoPairOddsValues
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import MathUE.RationalizedQuadraticBracketRoot

/-! # A second indifference root with an actual profitable Quit deviation

The twelve passive joining entries of the literal fixture are changed to
`13 / 15`. Its small scalar root satisfies the actual passive Continue
equations and therefore realizes the computed terminal values. At that root,
date-zero Quit is strictly profitable against the same fixed opponents.
This excludes the displayed profile, not uniform equilibrium in the game.
-/

noncomputable section

namespace GameTheory.BelowSingletonJointPhaseSecondRoot

open PairedCycle Math.CrossedMatching Math.PairedAffine

private abbrev coalitionCode := @Math.FiniteCoalition.binaryCode 4

def reward : TwoPairOdds.Reward :=
  fun terminal => match coalitionCode terminal.val with
    | 3 => ![13 / 15, 13 / 15, 0, 0]
    | 6 => ![0, 13 / 15, 13 / 15, 0]
    | 7 => ![100, 13 / 15, 100, 0]
    | 9 => ![13 / 15, 0, 0, 13 / 15]
    | 11 => ![13 / 15, 100, 0, 100]
    | 12 => ![0, 0, 13 / 15, 13 / 15]
    | 13 => ![100, 0, 100, 13 / 15]
    | 14 => ![0, 100, 13 / 15, 100]
    | _ => BelowSingletonJointPhaseFixture.reward terminal

@[simp] theorem singleton_eq (player : Fin 4) : singleton reward player = 1 := by
  fin_cases player <;>
    norm_num +decide [PairedCycle.singleton, reward, coalitionCode,
      BelowSingletonJointPhaseFixture.reward, Math.FiniteCoalition.binaryCode_finFour,
      quittingSingletonTerminal]

theorem reward_data (player : Fin 4) :
    quittingProjectiveLCPMatrix reward player (favorite player) = 3 ∧
    quittingProjectiveLCPMatrix reward player (scheduled player) = -1 ∧
    quittingProjectiveLCPMatrix reward player (other player) = -1 ∧
    TwoPairOdds.premium reward player = -11 / 10 ∧
    TwoPairOdds.passive reward player = -179 / 60 := by
  fin_cases player <;>
    norm_num +decide [quittingProjectiveLCPMatrix, TwoPairOdds.premium, TwoPairOdds.passive,
      PairedCycle.singleton, reward, coalitionCode, BelowSingletonJointPhaseFixture.reward,
      Math.FiniteCoalition.binaryCode_finFour, quittingSingletonTerminal,
      favorite, scheduled, other]

theorem passive_caps_eq (player : Fin 4) :
    reward ⟨{player, favorite player}, by simp⟩ player = 13 / 15 ∧
    reward ⟨{player, other player}, by simp⟩ player = 13 / 15 ∧
    reward ⟨{player, favorite player, other player}, by simp⟩ player = 13 / 15 := by
  fin_cases player <;>
    norm_num +decide [reward, coalitionCode, BelowSingletonJointPhaseFixture.reward,
      Math.FiniteCoalition.binaryCode_finFour, favorite, other]

def smallRoot : ℝ := Math.rationalizedQuadraticRoot (-22) 85 (-3)

theorem smallRoot_mem : smallRoot ∈ Set.Ioo (0 : ℝ) (1 / 20) := by
  have hspec := Math.rationalizedQuadraticRoot_spec
    (leading := (-22 : ℝ)) (linear := 85) (constant := -3) (cap := 1 / 20)
    (by norm_num) (by norm_num) (by norm_num [Math.quadraticBracketValue])
  exact hspec.2.2.1

theorem smallRoot_quadratic : 22 * smallRoot ^ 2 - 85 * smallRoot + 3 = 0 := by
  have hspec := Math.rationalizedQuadraticRoot_spec
    (leading := (-22 : ℝ)) (linear := 85) (constant := -3) (cap := 1 / 20)
    (by norm_num) (by norm_num) (by norm_num [Math.quadraticBracketValue])
  have hzero := hspec.2.2.2.1
  change -22 * smallRoot ^ 2 + 85 * smallRoot + -3 = 0 at hzero
  linarith

theorem smallRoot_formula : smallRoot = 6 / (85 + Real.sqrt 6961) := by
  norm_num [smallRoot, Math.rationalizedQuadraticRoot, discrim]

theorem polynomial_factor (t : ℝ) :
    Math.PairedBelowSingleton.polynomial 3 (-11 / 10) (-179 / 60) t =
      -(3 * t - 2) * (22 * t ^ 2 - 85 * t + 3) / 60 := by
  unfold Math.PairedBelowSingleton.polynomial Math.cubicAnchor
  ring

theorem smallRoot_polynomial :
    Math.PairedBelowSingleton.polynomial 3 (-11 / 10) (-179 / 60) smallRoot = 0 := by
  rw [polynomial_factor, smallRoot_quadratic]
  ring

def odds (t : ℝ) : Fin 4 → ℝ := fun _ => (1 - t) / t

theorem odds_pos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : ∀ player, 0 < odds t player :=
  fun _ => div_pos (sub_pos.mpr ht.2) ht.1

theorem hazard_eq {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    TwoPairOdds.hazard (odds t) = fun _ => 1 - t := by
  funext player
  unfold TwoPairOdds.hazard odds
  have hden : 1 + (1 - t) / t = 1 / t := by
    field_simp [ne_of_gt ht.1]
    ring
  rw [hden]
  field_simp [ne_of_gt ht.1]

theorem passiveEquation_eq {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (player : Fin 4) :
    passiveEquation (quittingProjectiveLCPMatrix reward) (TwoPairOdds.premium reward)
        (TwoPairOdds.passive reward) (odds t) player =
      -(1 - t) * Math.PairedBelowSingleton.polynomial 3 (-11 / 10) (-179 / 60) t / t ^ 3 := by
  obtain ⟨hf, ha, ho, hp, hk⟩ := reward_data player
  unfold passiveEquation
  rw [hf, ha, ho, hp, hk]
  unfold odds Math.PairedBelowSingleton.polynomial Math.cubicAnchor
  have htne := ne_of_gt ht.1
  have hdenom : 1 + (1 - t) / t ≠ 0 := by
    have : 0 < 1 + (1 - t) / t := by
      linarith [div_pos (sub_pos.mpr ht.2) ht.1]
    exact ne_of_gt this
  field_simp [htne, hdenom]
  ring

theorem passive_continue {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hroot : Math.PairedBelowSingleton.polynomial 3 (-11 / 10) (-179 / 60) t = 0)
    (player : Fin 4) :
    quittingRootContinuePayoff reward
      (twoPairPhaseValue reward fin4Schedule (TwoPairOdds.hazard (odds t))
        (fin4Schedule.phase player))
      (cycle fin4Schedule (TwoPairOdds.hazard (odds t))
        (properUnitBounds _ (TwoPairOdds.hazard_proper (odds_pos ht)))
        (finRotate 2 (fin4Schedule.phase player))) player =
      twoPairPostValue reward fin4Schedule (TwoPairOdds.hazard (odds t)) player := by
  apply TwoPairOdds.passive_continue reward (odds_pos ht)
  intro who
  rw [passiveEquation_eq ht, hroot]
  ring

theorem postValue_eq {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (player : Fin 4) :
    twoPairPostValue reward fin4Schedule (TwoPairOdds.hazard (odds t)) player =
      11 / 10 - 1 / (10 * t) := by
  rw [TwoPairOdds.postValue_eq reward (odds_pos ht), singleton_eq,
    (reward_data player).2.1, (reward_data player).2.2.2.1]
  unfold odds
  field_simp [ne_of_gt ht.1]
  ring

theorem passive_quit_eq {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (player : Fin 4) :
    quittingRootQuitPayoff reward
      (twoPairPhaseValue reward fin4Schedule (TwoPairOdds.hazard (odds t))
        (fin4Schedule.phase player))
      (cycle fin4Schedule (TwoPairOdds.hazard (odds t))
        (properUnitBounds _ (TwoPairOdds.hazard_proper (odds_pos ht)))
        (finRotate 2 (fin4Schedule.phase player))) player =
      t ^ 2 + (1 - t ^ 2) * (13 / 15) := by
  rw [fin4Schedule_passive_root]
  have hne : favorite player ≠ other player := by fin_cases player <;> decide
  rw [rootQuit_eq_bellman reward _ hne, quittingHazardCoin_true_toReal,
    quittingHazardCoin_true_toReal]
  have hq : ∀ who, TwoPairOdds.hazard (odds t) who = 1 - t := congrFun (hazard_eq ht)
  rw [hq, hq]
  obtain ⟨hf, ho, hj⟩ := passive_caps_eq player
  have hs : reward (quittingSingletonTerminal player) player = 1 := singleton_eq player
  unfold bellman contribution
  rw [hf, ho, hj, hs]
  ring

def smallOdds : Fin 4 → ℝ := odds smallRoot

theorem smallRoot_unit : smallRoot ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨smallRoot_mem.1, smallRoot_mem.2.trans (by norm_num)⟩

def profile (initial : Fin 2) : (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward
    (cycle fin4Schedule (TwoPairOdds.hazard smallOdds)
      (properUnitBounds _ (TwoPairOdds.hazard_proper (odds_pos smallRoot_unit)))) initial

theorem terminalPayoff_eq (initial : Fin 2) :
    quittingTerminalPayoff reward (profile initial) =
      twoPairPhaseValue reward fin4Schedule (TwoPairOdds.hazard smallOdds) initial := by
  exact twoPair_terminalPayoff_eq reward fin4Schedule _
    (TwoPairOdds.hazard_proper (odds_pos smallRoot_unit))
    (passive_continue smallRoot_unit smallRoot_polynomial) initial

theorem terminal_passive_eq (player : Fin 4) :
    quittingTerminalPayoff reward (profile (finRotate 2 (fin4Schedule.phase player))) player =
      11 / 10 - 1 / (10 * smallRoot) := by
  rw [terminalPayoff_eq, twoPairPhaseValue_post]
  exact postValue_eq smallRoot_unit player

theorem quitNow_payoff_eq (player : Fin 4) :
    quittingTerminalPayoff reward
      (Function.update (profile (finRotate 2 (fin4Schedule.phase player))) player
        (quittingPureTimeBehaviorStrategy reward player (some 0))) player =
      smallRoot ^ 2 + (1 - smallRoot ^ 2) * (13 / 15) := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold profile
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile,
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
    ← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward _ player
      (twoPairPhaseValue reward fin4Schedule (TwoPairOdds.hazard smallOdds)
        (fin4Schedule.phase player)), quittingCyclicRootSequence_zero]
  exact passive_quit_eq smallRoot_unit player

theorem passive_value_lt : 11 / 10 - 1 / (10 * smallRoot) < -9 / 10 := by
  have ht := smallRoot_mem
  have hden : 0 < 10 * smallRoot := mul_pos (by norm_num) ht.1
  have hrecip : 2 < 1 / (10 * smallRoot) := by
    apply (lt_div_iff₀ hden).mpr
    linarith [ht.2]
  linarith

theorem quitNow_value_gt :
    13 / 15 < smallRoot ^ 2 + (1 - smallRoot ^ 2) * (13 / 15) := by
  nlinarith [sq_pos_of_pos smallRoot_mem.1]

/-- The actual date-zero deviation is profitable against the displayed opponents. -/
theorem quitNow_gain_pos (player : Fin 4) :
    0 < quittingTerminalPayoff reward
      (Function.update (profile (finRotate 2 (fin4Schedule.phase player))) player
        (quittingPureTimeBehaviorStrategy reward player (some 0))) player -
      quittingTerminalPayoff reward
        (profile (finRotate 2 (fin4Schedule.phase player))) player := by
  rw [quitNow_payoff_eq, terminal_passive_eq]
  linarith [passive_value_lt, quitNow_value_gt]

theorem not_terminalNash_passive_initial (player : Fin 4) :
    ¬ (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (profile (finRotate 2 (fin4Schedule.phase player))) := by
  intro hnash
  have hcap := hnash player (quittingPureTimeBehaviorStrategy reward player (some 0))
  have hgain := quitNow_gain_pos player
  simp only [add_zero] at hcap
  linarith

/-- Both initial phases of the small-root profile fail actual terminal Nash. -/
theorem not_terminalNash (initial : Fin 2) :
    ¬ (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (profile initial) := by
  fin_cases initial
  · change ¬ (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (profile 0)
    have hphase : fin4Schedule.phase 1 = 1 := fin4Schedule.phase_first 1
    simpa only [hphase, show finRotate 2 (1 : Fin 2) = 0 from rfl] using
      not_terminalNash_passive_initial 1
  · change ¬ (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (profile 1)
    simpa only [fin4Schedule_phase_zero, show finRotate 2 (0 : Fin 2) = 1 from rfl] using
      not_terminalNash_passive_initial 0

def selectedOdds : Fin 4 → ℝ := odds (2 / 3)

theorem selected_unit : (2 / 3 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num

theorem selected_polynomial :
    Math.PairedBelowSingleton.polynomial 3 (-11 / 10) (-179 / 60) (2 / 3) = 0 := by
  rw [polynomial_factor]
  norm_num

theorem selected_postValue_eq (player : Fin 4) :
    twoPairPostValue reward fin4Schedule (TwoPairOdds.hazard selectedOdds) player =
      19 / 20 := by
  exact (postValue_eq selected_unit player).trans (by norm_num)

theorem selected_activeValue_eq (player : Fin 4) :
    twoPairActiveValue reward fin4Schedule (TwoPairOdds.hazard selectedOdds) player =
      19 / 30 := by
  rw [TwoPairOdds.activeValue_eq, singleton_eq, (reward_data player).2.2.2.1]
  unfold selectedOdds
  rw [hazard_eq selected_unit]
  norm_num

theorem selected_passive_quit_eq (player : Fin 4) :
    quittingRootQuitPayoff reward
      (twoPairPhaseValue reward fin4Schedule (TwoPairOdds.hazard selectedOdds)
        (fin4Schedule.phase player))
      (cycle fin4Schedule (TwoPairOdds.hazard selectedOdds)
        (properUnitBounds _ (TwoPairOdds.hazard_proper (odds_pos selected_unit)))
        (finRotate 2 (fin4Schedule.phase player))) player = 25 / 27 := by
  exact (passive_quit_eq selected_unit player).trans (by norm_num)

theorem selected_passive_gap_eq (player : Fin 4) :
    twoPairPostValue reward fin4Schedule (TwoPairOdds.hazard selectedOdds) player -
      quittingRootQuitPayoff reward
        (twoPairPhaseValue reward fin4Schedule (TwoPairOdds.hazard selectedOdds)
          (fin4Schedule.phase player))
        (cycle fin4Schedule (TwoPairOdds.hazard selectedOdds)
          (properUnitBounds _ (TwoPairOdds.hazard_proper (odds_pos selected_unit)))
          (finRotate 2 (fin4Schedule.phase player))) player = 13 / 540 := by
  rw [selected_postValue_eq, selected_passive_quit_eq]
  norm_num

theorem selected_phaseValue_eq (initial : Fin 2) :
    twoPairPhaseValue reward fin4Schedule (TwoPairOdds.hazard selectedOdds) initial =
      BelowSingletonJointPhaseFixture.phaseValues initial := by
  funext player
  unfold twoPairPhaseValue
  rw [selected_activeValue_eq, selected_postValue_eq]
  have hfirst : fin4Schedule.phase 1 = 1 := fin4Schedule.phase_first 1
  have hsecond : fin4Schedule.phase 2 = 0 := fin4Schedule.phase_second 0
  have hthird : fin4Schedule.phase 3 = 1 := fin4Schedule.phase_second 1
  fin_cases initial <;> fin_cases player <;>
    norm_num [BelowSingletonJointPhaseFixture.phaseValues, hfirst, hsecond, hthird]

def selectedProfile (initial : Fin 2) : (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward
    (cycle fin4Schedule (TwoPairOdds.hazard selectedOdds)
      (properUnitBounds _ (TwoPairOdds.hazard_proper (odds_pos selected_unit)))) initial

/-- The modified table still has its valid upper-root exact fixed profile. -/
theorem selected_exact_terminal_and_fixedProfile (initial : Fin 2) :
    quittingTerminalPayoff reward (selectedProfile initial) =
      BelowSingletonJointPhaseFixture.phaseValues initial ∧
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (selectedProfile initial) ∧
    (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ,
      ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon ε (selectedProfile initial) ∧
          ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon
              (selectedProfile initial) player -
            BelowSingletonJointPhaseFixture.phaseValues initial player| ≤ ε) ∧
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (BelowSingletonJointPhaseFixture.phaseValues initial) := by
  have hquit (player : Fin 4) :
      quittingRootQuitPayoff reward
        (twoPairPhaseValue reward fin4Schedule (TwoPairOdds.hazard selectedOdds)
          (fin4Schedule.phase player))
        (cycle fin4Schedule (TwoPairOdds.hazard selectedOdds)
          (properUnitBounds _ (TwoPairOdds.hazard_proper (odds_pos selected_unit)))
          (finRotate 2 (fin4Schedule.phase player))) player ≤
        twoPairPostValue reward fin4Schedule (TwoPairOdds.hazard selectedOdds) player := by
    rw [selected_passive_quit_eq, selected_postValue_eq]
    norm_num
  have hresult := twoPair_exact_terminal_and_fixedProfile reward fin4Schedule
    (TwoPairOdds.hazard selectedOdds) (TwoPairOdds.hazard_proper (odds_pos selected_unit))
    (passive_continue selected_unit selected_polynomial) hquit initial
  simpa only [selectedProfile, selected_phaseValue_eq] using hresult

end GameTheory.BelowSingletonJointPhaseSecondRoot
