import UniformEquilibrium.Diagnostics.Quitting.PivotRepairRationalFixture
import MathUE.ProbabilityMassFunction.IndicatorExpectation

/-! # A positive lower bound for the rational pivot-repair example

The bound holds for every feasible repair mass against the fixed actual opponent laws.
-/

noncomputable section

namespace GameTheory.PivotRepairRationalLowerBound

open Math.LinearProgramming
open _root_.Math.Probability
open PivotRepairRationalFixture

/-- Deterministic laws in which exactly the displayed coalition quits at one date. -/
def pureCoalitionLaws (coalition : Finset (Fin 4)) (time : ℕ) :
    Fin 4 → PMF (Option ℕ) :=
  fun player ↦ PMF.pure (if player ∈ coalition then some time else none)

private theorem pureCoalitionPayoff_eq_reward (coalition : Finset (Fin 4))
    (hne : coalition.Nonempty) (time : ℕ) (observer : Fin 4) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (pureCoalitionLaws coalition time)) observer =
      reward ⟨coalition, hne⟩ observer := by
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  unfold quittingIndependentTerminalOutcomeLaw pureCoalitionLaws
  rw [Math.PMFProduct.pmfPi_pure, PMF.pure_map, expect_pure,
    quittingFirstStoppingOutcome_one_date coalition hne time]
  rfl

/-- Player 1's deterministic branch payoffs at the opponent date. -/
theorem playerOne_at_branch_payoffs (time : ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (pureCoalitionLaws {0} time)) 1 = 7 ∧
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (pureCoalitionLaws {0, 1} time)) 1 = 8 ∧
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (pureCoalitionLaws {0, 2} time)) 1 = 7 ∧
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (pureCoalitionLaws {0, 1, 2} time)) 1 = 6 := by
  constructor
  · rw [pureCoalitionPayoff_eq_reward {0} (by simp)]
    norm_num [reward, Fin.ext_iff]
  constructor
  · rw [pureCoalitionPayoff_eq_reward {0, 1} (by simp)]
    norm_num [reward, Fin.ext_iff]
  constructor
  · rw [pureCoalitionPayoff_eq_reward {0, 2} (by simp)]
    norm_num [reward, Fin.ext_iff]
  · rw [pureCoalitionPayoff_eq_reward {0, 1, 2} (by simp)]
    norm_num [reward, Fin.ext_iff]

/-- Player 1's deterministic first-opponent branch payoffs. -/
theorem playerOne_opponent_branch_payoffs (time : ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (pureCoalitionLaws {1} time)) 1 = 0 ∧
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (pureCoalitionLaws {2} time)) 1 = 7 ∧
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (pureCoalitionLaws {1, 2} time)) 1 = 5 := by
  constructor
  · rw [pureCoalitionPayoff_eq_reward {1} (by simp)]
    norm_num [reward, Fin.ext_iff]
  constructor
  · rw [pureCoalitionPayoff_eq_reward {2} (by simp)]
    norm_num [reward, Fin.ext_iff]
  · rw [pureCoalitionPayoff_eq_reward {1, 2} (by simp)]
    norm_num [reward, Fin.ext_iff]

private def pivotTwoTimes (pivotChoice : Option ℕ) (twoTime : Option ℕ) :
    Fin 4 → Option ℕ
  | 0 => pivotChoice
  | 2 => twoTime
  | _ => none

private theorem playerOne_pivot_two_pure_payoff (pivotChoice : Option ℕ)
    (twoTime : Option ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (fun player ↦ PMF.pure (pivotTwoTimes pivotChoice twoTime player))) 1 =
      if pivotChoice = none ∧ twoTime = none then 0 else 7 := by
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  unfold quittingIndependentTerminalOutcomeLaw
  rw [Math.PMFProduct.pmfPi_pure, PMF.pure_map, expect_pure]
  rcases pivotChoice with _ | pivotTime
  · rcases twoTime with _ | twoTime
    · rw [show pivotTwoTimes none none = fun _ : Fin 4 ↦ none by
          funext player
          fin_cases player <;> rfl]
      simp [quittingTerminalOutcomeReward]
    · rw [show pivotTwoTimes none (some twoTime) = fun player ↦
          if player ∈ ({2} : Finset (Fin 4)) then some twoTime else none by
        funext player
        fin_cases player <;> rfl,
        quittingFirstStoppingOutcome_one_date {2} (by simp)]
      norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]
      simp
  · rcases twoTime with _ | twoTime
    · rw [show pivotTwoTimes (some pivotTime) none = fun player ↦
          if player ∈ ({0} : Finset (Fin 4)) then some pivotTime else none by
        funext player
        fin_cases player <;> rfl,
        quittingFirstStoppingOutcome_one_date {0} (by simp)]
      norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]
      simp
    · by_cases hpivot : pivotTime < twoTime
      · have hout : quittingFirstStoppingOutcome
            (pivotTwoTimes (some pivotTime) (some twoTime)) =
          some ⟨{0}, by simp⟩ := by
          calc
            quittingFirstStoppingOutcome
                (pivotTwoTimes (some pivotTime) (some twoTime)) =
                quittingFirstStoppingOutcome
                  (pivotTwoTimes (some pivotTime) none) := by
              apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
                (hidden := 2) (blocker := 0)
              · intro other hother
                fin_cases other <;> simp_all [pivotTwoTimes]
              · simpa [pivotTwoTimes, quittingStoppingTimeValue] using hpivot
              · simp [pivotTwoTimes, quittingStoppingTimeValue]
            _ = some ⟨{0}, by simp⟩ := by
              rw [show pivotTwoTimes (some pivotTime) none = fun player ↦
                    if player ∈ ({0} : Finset (Fin 4)) then some pivotTime else none by
                  funext player
                  fin_cases player <;> rfl,
                quittingFirstStoppingOutcome_one_date {0} (by simp)]
        rw [hout]
        norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]
        simp
      · by_cases htwo : twoTime < pivotTime
        · have hout : quittingFirstStoppingOutcome
              (pivotTwoTimes (some pivotTime) (some twoTime)) =
            some ⟨{2}, by simp⟩ := by
            calc
              quittingFirstStoppingOutcome
                  (pivotTwoTimes (some pivotTime) (some twoTime)) =
                  quittingFirstStoppingOutcome (pivotTwoTimes none (some twoTime)) := by
                apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
                  (hidden := 0) (blocker := 2)
                · intro other hother
                  fin_cases other <;> simp_all [pivotTwoTimes]
                · simpa [pivotTwoTimes, quittingStoppingTimeValue] using htwo
                · simp [pivotTwoTimes, quittingStoppingTimeValue]
              _ = some ⟨{2}, by simp⟩ := by
                rw [show pivotTwoTimes none (some twoTime) = fun player ↦
                      if player ∈ ({2} : Finset (Fin 4)) then some twoTime else none by
                    funext player
                    fin_cases player <;> rfl,
                  quittingFirstStoppingOutcome_one_date {2} (by simp)]
          rw [hout]
          norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]
          simp
        · have heq : pivotTime = twoTime := by omega
          subst twoTime
          rw [show pivotTwoTimes (some pivotTime) (some pivotTime) = fun player ↦
              if player ∈ ({0, 2} : Finset (Fin 4)) then some pivotTime else none by
            funext player
            fin_cases player <;> rfl,
            quittingFirstStoppingOutcome_one_date {0, 2} (by simp)]
          norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]
          simp

private def pivotTwoBase (N : ℕ) : Fin 4 → PMF (Option ℕ) :=
  Function.update (fun _ ↦ PMF.pure none) 2
    (quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num))

private theorem playerOne_given_pivot_choice (N : ℕ) (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (pivotTwoBase N) 0 (PMF.pure choice))) 1 =
      if choice = none then 1 else 7 := by
  unfold pivotTwoBase
  rw [show Function.update
        (Function.update (fun _ : Fin 4 ↦ PMF.pure none) 2
          (quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num))) 0
        (PMF.pure choice) = Function.update
          (Function.update (fun _ : Fin 4 ↦ PMF.pure none) 0 (PMF.pure choice)) 2
          (quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num)) by
      exact (Function.update_comm (by decide : (0 : Fin 4) ≠ 2) _ _ _).symm]
  rw [quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
    expect_quitOrNever]
  have hnone : Function.update
      (Function.update (fun _ : Fin 4 ↦ PMF.pure none) 0 (PMF.pure choice)) 2
        (PMF.pure none) = fun player ↦ PMF.pure (pivotTwoTimes choice none player) := by
    funext player
    fin_cases player <;> rfl
  have hsome : Function.update
      (Function.update (fun _ : Fin 4 ↦ PMF.pure none) 0 (PMF.pure choice)) 2
        (PMF.pure (some (N - 1))) =
      fun player ↦ PMF.pure (pivotTwoTimes choice (some (N - 1)) player) := by
    funext player
    fin_cases player <;> rfl
  rw [hnone, hsome, playerOne_pivot_two_pure_payoff,
    playerOne_pivot_two_pure_payoff]
  rcases choice with _ | time
  · norm_num
    exact Option.some_ne_none _
  · simp
    ring

/-- Against an arbitrary pivot law, player 1's actual Never response pays
`7 - 6ν`, where `ν` is the pivot law's Never mass. -/
theorem playerOne_never_response_payoff (N : ℕ) (hN : 1 ≤ N)
    (law : PMF (Option ℕ)) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update (opponents N hN) 0 law) 1
            (PMF.pure none))) 1 =
      7 - 6 * (law none).toReal := by
  rw [show Function.update (Function.update (opponents N hN) 0 law) 1
        (PMF.pure none) = Function.update (pivotTwoBase N) 0 law by
    funext player
    fin_cases player <;> simp [opponents, pivotTwoBase]]
  rw [quittingTerminalPayoff_stoppingLawProfile_update_eq_expect]
  have hpointwise : (fun choice ↦ quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update (pivotTwoBase N) 0 (PMF.pure choice))) 1) =
      fun choice ↦ if choice = none then 1 else 7 := by
    funext choice
    exact playerOne_given_pivot_choice N choice
  rw [hpointwise]
  let singleton := fun choice : Option ℕ ↦ if choice = none then (1 : ℝ) else 0
  let complement := fun choice : Option ℕ ↦ if choice = none then (0 : ℝ) else 1
  have hsingleton : ∀ choice, |singleton choice| ≤ 1 := by
    intro choice
    simp only [singleton]
    split <;> norm_num
  have hcomplement : ∀ choice, |7 * complement choice| ≤ 7 := by
    intro choice
    simp only [complement]
    split <;> norm_num
  have hadd := expect_add_of_summable law singleton (7 * complement ·)
    (expect_summable_of_bounded law singleton hsingleton)
    (expect_summable_of_bounded law (7 * complement ·) hcomplement)
  rw [show (fun choice : Option ℕ ↦ if choice = none then (1 : ℝ) else 7) =
      fun choice ↦ singleton choice + 7 * complement choice by
    funext choice
    split <;> simp_all [singleton, complement]]
  rw [hadd, expect_const_mul, expect_singletonIndicator,
    expect_complementSingletonIndicator]
  ring

private theorem allNever_playerOne_payoff :
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward neverLaws) 1 = 0 := by
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  unfold quittingIndependentTerminalOutcomeLaw neverLaws
  rw [Math.PMFProduct.pmfPi_pure, PMF.pure_map, expect_pure]
  simp [quittingTerminalOutcomeReward]

/-- Player 1's actual payoff when the pivot quits at the opponent date. -/
theorem playerOnePayoff_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff (some (N - 1)) 1 = 363 / 49 := by
  rw [observerPayoff_conditioned N hN (some (N - 1)) 1]
  rcases playerOne_at_branch_payoffs (N - 1) with ⟨h0, h01, h02, h012⟩
  have hb0 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update neverLaws 0 (PMF.pure (some (N - 1))))) 1 = 7 := by
    rw [show Function.update neverLaws 0 (PMF.pure (some (N - 1))) =
        pureCoalitionLaws {0} (N - 1) by
      funext player
      fin_cases player <;> rfl, h0]
  have hb01 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update
        (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
          (PMF.pure (some (N - 1))))) 1 = 8 := by
    rw [show Function.update
        (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
          (PMF.pure (some (N - 1))) = pureCoalitionLaws {0, 1} (N - 1) by
      funext player
      fin_cases player <;> rfl, h01]
  have hb02 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update
        (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 2
          (PMF.pure (some (N - 1))))) 1 = 7 := by
    rw [show Function.update
        (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 2
          (PMF.pure (some (N - 1))) = pureCoalitionLaws {0, 2} (N - 1) by
      funext player
      fin_cases player <;> rfl, h02]
  have hb012 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update
        (Function.update
          (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
            (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))))) 1 = 6 := by
    rw [show Function.update
        (Function.update
          (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
            (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))) =
          pureCoalitionLaws {0, 1, 2} (N - 1) by
      funext player
      fin_cases player <;> rfl, h012]
  rw [hb0, hb01, hb02, hb012]
  norm_num

/-- Player 1's actual payoff when the pivot chooses Never. -/
theorem playerOnePayoff_never (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff none 1 = 41 / 49 := by
  rw [observerPayoff_conditioned N hN none 1]
  rcases playerOne_opponent_branch_payoffs (N - 1) with ⟨h1, h2, h12⟩
  have hbase : Function.update neverLaws 0 (PMF.pure none) = neverLaws := by
      funext player
      fin_cases player <;> rfl
  have hb1 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update neverLaws 0 (PMF.pure none)) 1
        (PMF.pure (some (N - 1))))) 1 = 0 := by
    rw [show Function.update
        (Function.update neverLaws 0 (PMF.pure none)) 1
          (PMF.pure (some (N - 1))) = pureCoalitionLaws {1} (N - 1) by
      funext player
      fin_cases player <;> rfl, h1]
  have hb2 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update neverLaws 0 (PMF.pure none)) 2
        (PMF.pure (some (N - 1))))) 1 = 7 := by
    rw [show Function.update
        (Function.update neverLaws 0 (PMF.pure none)) 2
          (PMF.pure (some (N - 1))) = pureCoalitionLaws {2} (N - 1) by
      funext player
      fin_cases player <;> rfl, h2]
  have hb12 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure none)) 1
          (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))))) 1 = 5 := by
    rw [show Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure none)) 1
          (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))) =
          pureCoalitionLaws {1, 2} (N - 1) by
      funext player
      fin_cases player <;> rfl, h12]
  rw [hbase] at hb1 hb2 hb12
  rw [hbase, allNever_playerOne_payoff, hb1, hb2, hb12]
  norm_num

/-- Player 1's actual payoff at every finite pivot date after the opponent date. -/
theorem playerOnePayoff_after (N : ℕ) (hN : 1 ≤ N) {time : ℕ}
    (htime : N ≤ time) :
    (input N hN).purePivotPayoff (some time) 1 = 167 / 49 := by
  unfold QuittingPivotRepairLPInput.purePivotPayoff
  change quittingTerminalPayoff reward (quittingStoppingLawProfile reward
    (Function.update (opponents N hN) 0 (PMF.pure (some time)))) 1 = _
  rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
    reward (opponents N hN) 0 1 N]
  · change (input N hN).purePivotPayoff none 1 + _ = _
    rw [playerOnePayoff_never]
    have hproduct : (∏ j ∈ Finset.univ.erase (0 : Fin 4),
        ((opponents N hN j) none).toReal) = 18 / 49 := by
      have hall : (∏ j, ((opponents N hN j) none).toReal) = 18 / 49 := by
        rw [Fin.prod_univ_four, opponents_one_never, opponents_two_never]
        simp [opponents]
        norm_num
      have hzero : ((opponents N hN 0) none).toReal = 1 := by simp [opponents]
      calc
        (∏ j ∈ Finset.univ.erase (0 : Fin 4),
            ((opponents N hN j) none).toReal) =
            ∏ j, ((opponents N hN j) none).toReal := by
          simpa [hzero] using Finset.prod_erase_mul Finset.univ
            (fun j ↦ ((opponents N hN j) none).toReal)
            (Finset.mem_univ (0 : Fin 4))
        _ = 18 / 49 := hall
    rw [hproduct]
    simp [quittingSingletonTerminal, reward, Fin.ext_iff]
    norm_num
  · exact (input N hN).opponents_finite
  · exact htime

private def beforeThreeTimes (N time : ℕ) (first second : Bool) : Fin 4 → Option ℕ
  | 0 => some time
  | 1 => if first then some (N - 1) else none
  | 2 => if second then some (N - 1) else none
  | _ => none

private theorem firstStoppingOutcome_beforeThreeTimes (N time : ℕ)
    (htime : time < N - 1) (first second : Bool) :
    quittingFirstStoppingOutcome (beforeThreeTimes N time first second) =
      some ⟨{0}, by simp⟩ := by
  let withoutFirst := beforeThreeTimes N time false second
  let pivotOnly := beforeThreeTimes N time false false
  have hfirst : quittingFirstStoppingOutcome (beforeThreeTimes N time first second) =
      quittingFirstStoppingOutcome withoutFirst := by
    cases first
    · rfl
    · apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
        (hidden := 1) (blocker := 0)
      · intro other hother
        fin_cases other <;> simp_all [beforeThreeTimes, withoutFirst]
      · simp [beforeThreeTimes, quittingStoppingTimeValue]
        exact_mod_cast htime
      · simp [beforeThreeTimes, withoutFirst, quittingStoppingTimeValue]
  have hsecond : quittingFirstStoppingOutcome withoutFirst =
      quittingFirstStoppingOutcome pivotOnly := by
    cases second
    · rfl
    · apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
        (hidden := 2) (blocker := 0)
      · intro other hother
        fin_cases other <;> simp_all [beforeThreeTimes, withoutFirst, pivotOnly]
      · simp [beforeThreeTimes, withoutFirst, quittingStoppingTimeValue]
        exact_mod_cast htime
      · simp [beforeThreeTimes, pivotOnly, quittingStoppingTimeValue]
  rw [hfirst, hsecond]
  change quittingFirstStoppingOutcome
      (fun player ↦ if player ∈ ({0} : Finset (Fin 4)) then some time else none) = _
  exact quittingFirstStoppingOutcome_one_date {0} (by simp) time

private theorem playerOne_before_branch_payoff (N time : ℕ)
    (htime : time < N - 1) (first second : Bool) :
    quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (fun player ↦ PMF.pure (beforeThreeTimes N time first second player))) 1 = 7 := by
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  unfold quittingIndependentTerminalOutcomeLaw
  rw [Math.PMFProduct.pmfPi_pure, PMF.pure_map, expect_pure,
    firstStoppingOutcome_beforeThreeTimes N time htime first second]
  norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]

/-- Player 1's actual payoff is `7` when the pivot quits before the opponent date. -/
theorem playerOnePayoff_before (N : ℕ) (hN : 1 ≤ N) {time : ℕ}
    (htime : time < N - 1) :
    (input N hN).purePivotPayoff (some time) 1 = 7 := by
  rw [observerPayoff_conditioned N hN (some time) 1]
  have hbranch (first second : Bool) :
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (Function.update
          (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
            (PMF.pure (if first then some (N - 1) else none))) 2
          (PMF.pure (if second then some (N - 1) else none)))) 1 = 7 := by
    rw [show Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
          (PMF.pure (if first then some (N - 1) else none))) 2
        (PMF.pure (if second then some (N - 1) else none)) =
        fun player ↦ PMF.pure (beforeThreeTimes N time first second player) by
      funext player
      fin_cases player <;> cases first <;> cases second <;> rfl]
    exact playerOne_before_branch_payoff N time htime first second
  have h00 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update neverLaws 0 (PMF.pure (some time)))) 1 = 7 := by
    rw [show Function.update neverLaws 0 (PMF.pure (some time)) =
        Function.update
          (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
            (PMF.pure none)) 2 (PMF.pure none) by
      funext player
      fin_cases player <;> rfl]
    exact hbranch false false
  have h10 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
        (PMF.pure (some (N - 1))))) 1 = 7 := by
    rw [show Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
        (PMF.pure (some (N - 1))) = Function.update
          (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
            (PMF.pure (some (N - 1)))) 2 (PMF.pure none) by
      funext player
      fin_cases player <;> rfl]
    exact hbranch true false
  have h01 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 2
        (PMF.pure (some (N - 1))))) 1 = 7 := by
    rw [show Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 2
        (PMF.pure (some (N - 1))) = Function.update
          (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
            (PMF.pure none)) 2 (PMF.pure (some (N - 1))) by
      funext player
      fin_cases player <;> rfl]
    exact hbranch false true
  have h11 : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
          (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))))) 1 = 7 := by
    simpa using hbranch true true
  rw [h00, h10, h01, h11]
  norm_num

def tauIndex (N : ℕ) (hN : 1 ≤ N) : Fin N := ⟨N - 1, by omega⟩

def beforeMass {N : ℕ} (hN : 1 ≤ N) (mass : PivotRepairMass N) : ℝ :=
  ∑ time ∈ Finset.univ.erase (tauIndex N hN), pivotRepairHead mass time

def atMass {N : ℕ} (hN : 1 ≤ N) (mass : PivotRepairMass N) : ℝ :=
  pivotRepairHead mass (tauIndex N hN)

theorem headMass_eq_beforeMass_add_atMass {N : ℕ} (hN : 1 ≤ N)
    (mass : PivotRepairMass N) :
    (∑ time, pivotRepairHead mass time) = beforeMass hN mass + atMass hN mass := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (tauIndex N hN))]
  rfl

theorem aggregate_sum_eq_one {N : ℕ} (hN : 1 ≤ N)
    {mass : PivotRepairMass N} (hfeasible : IsPivotRepairMassFeasible mass) :
    beforeMass hN mass + atMass hN mass + pivotRepairLate mass +
        pivotRepairNever mass = 1 := by
  rw [← headMass_eq_beforeMass_add_atMass]
  exact hfeasible.2.2.2.1

theorem beforeMass_nonneg {N : ℕ} (hN : 1 ≤ N)
    {mass : PivotRepairMass N} (hfeasible : IsPivotRepairMassFeasible mass) :
    0 ≤ beforeMass hN mass := by
  apply Finset.sum_nonneg
  intro time _
  exact hfeasible.1 time

theorem atMass_nonneg {N : ℕ} (hN : 1 ≤ N)
    {mass : PivotRepairMass N} (hfeasible : IsPivotRepairMassFeasible mass) :
    0 ≤ atMass hN mass := hfeasible.1 _

private theorem headPayoffSum_pivot {N : ℕ} (hN : 1 ≤ N)
    (mass : PivotRepairMass N) :
    (∑ time, pivotRepairHead mass time *
      (input N hN).purePivotPayoff (some time.1) 0) =
      beforeMass hN mass + (217 / 49) * atMass hN mass := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (tauIndex N hN))]
  congr 1
  · apply Finset.sum_congr rfl
    intro time htime
    have hne : time ≠ tauIndex N hN := (Finset.mem_erase.mp htime).1
    have hbefore : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun heq ↦ hne (Fin.ext heq))
    rw [pivotPayoff_before N hN hbefore]
    ring
  · rw [show (tauIndex N hN).1 = N - 1 by rfl, pivotPayoff_at]
    simp [atMass]
    ring

private theorem headPayoffSum_playerOne {N : ℕ} (hN : 1 ≤ N)
    (mass : PivotRepairMass N) :
    (∑ time, pivotRepairHead mass time *
      (input N hN).purePivotPayoff (some time.1) 1) =
      7 * beforeMass hN mass + (363 / 49) * atMass hN mass := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (tauIndex N hN))]
  congr 1
  · unfold beforeMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro time htime
    have hne : time ≠ tauIndex N hN := (Finset.mem_erase.mp htime).1
    have hbefore : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun heq ↦ hne (Fin.ext heq))
    rw [playerOnePayoff_before N hN hbefore]
    ring
  · rw [show (tauIndex N hN).1 = N - 1 by rfl, playerOnePayoff_at]
    simp [atMass]
    ring

/-- Player 1's prescribed LP payoff has the packet's four-mass formula. -/
theorem playerOne_prescribedPayoff_formula {N : ℕ} (hN : 1 ≤ N)
    (mass : PivotRepairMass N) :
    (input N hN).prescribedPayoff mass 1 =
      7 * beforeMass hN mass +
        (363 * atMass hN mass + 167 * pivotRepairLate mass +
          41 * pivotRepairNever mass) / 49 := by
  unfold QuittingPivotRepairLPInput.prescribedPayoff
  change (∑ time : Fin N, pivotRepairHead mass time *
        (input N hN).purePivotPayoff (some time.1) 1) +
      pivotRepairLate mass * (input N hN).purePivotPayoff (some N) 1 +
      pivotRepairNever mass * (input N hN).purePivotPayoff none 1 = _
  rw [headPayoffSum_playerOne, playerOnePayoff_after N hN (show N ≤ N by omega),
    playerOnePayoff_never]
  ring

/-- The LP's actual player-1 Never endpoint is `7 - 6ν`. -/
theorem playerOne_neverEndpoint_formula {N : ℕ} (hN : 1 ≤ N)
    (mass : PivotRepairMass N) (hfeasible : IsPivotRepairMassFeasible mass) :
    (input N hN).responderNeverEndpoint mass 1 =
      7 - 6 * pivotRepairNever mass := by
  have hne : (1 : Fin 4) ≠ (input N hN).pivot := by
    change (1 : Fin 4) ≠ 0
    decide
  rw [← (input N hN).provisional_neverResponse_eq mass hfeasible 1 hne]
  change quittingTerminalPayoff reward (quittingStoppingLawProfile reward
    (Function.update
      (Function.update (opponents N hN) 0
        (pivotRepairProvisionalStoppingLaw mass hfeasible)) 1 (PMF.pure none))) 1 = _
  rw [playerOne_never_response_payoff]
  rw [pivotRepairProvisionalStoppingLaw_none_toReal]

/-- Player 1's Never-response gain has the packet's four-mass formula. -/
theorem playerOne_neverGain_formula {N : ℕ} (hN : 1 ≤ N)
    (mass : PivotRepairMass N) (hfeasible : IsPivotRepairMassFeasible mass) :
    (input N hN).responderNeverEndpoint mass 1 -
        (input N hN).prescribedPayoff mass 1 =
      (-20 * atMass hN mass + 176 * pivotRepairLate mass +
        8 * pivotRepairNever mass) / 49 := by
  rw [playerOne_neverEndpoint_formula hN mass hfeasible,
    playerOne_prescribedPayoff_formula]
  have hsum := aggregate_sum_eq_one hN hfeasible
  linarith

/-- The pivot's actual LP debt has the packet's four-mass formula. -/
theorem pivotDebt_formula {N : ℕ} (hN : 1 ≤ N) (mass : PivotRepairMass N)
    (hfeasible : IsPivotRepairMassFeasible mass) :
    (input N hN).pivotCap - (input N hN).prescribedPayoff mass 0 =
      (186 * beforeMass hN mass + 18 * atMass hN mass +
        18 * pivotRepairNever mass) / 49 := by
  rw [pivotCap]
  unfold QuittingPivotRepairLPInput.prescribedPayoff
  change 235 / 49 -
      ((∑ time : Fin N, pivotRepairHead mass time *
          (input N hN).purePivotPayoff (some time.1) 0) +
        pivotRepairLate mass * (input N hN).purePivotPayoff (some N) 0 +
        pivotRepairNever mass * (input N hN).purePivotPayoff none 0) = _
  rw [headPayoffSum_pivot, pivotPayoff_after N hN (show N ≤ N by omega),
    pivotPayoff_never]
  have hsum := aggregate_sum_eq_one hN hfeasible
  linarith

private theorem weighted_certificate_identity (u v w n : ℝ)
    (hsum : u + v + w + n = 1) :
    (98 * ((186 * u + 18 * v + 18 * n) / 49) +
        9 * ((-20 * v + 176 * w + 8 * n) / 49)) / 107 =
      (1584 + 16644 * u + 252 * n) / 5243 := by
  rw [show (5243 : ℝ) = 49 * 107 by norm_num]
  field_simp
  linarith

private theorem weighted_certificate_lower_bound (u v w n : ℝ)
    (hsum : u + v + w + n = 1) (hu : 0 ≤ u) (hn : 0 ≤ n) :
    1584 / 5243 ≤
      (98 * ((186 * u + 18 * v + 18 * n) / 49) +
        9 * ((-20 * v + 176 * w + 8 * n) / 49)) / 107 := by
  rw [weighted_certificate_identity u v w n hsum]
  norm_num
  linarith

/-- Every feasible repair mass has objective at least the packet's
`1584/5243` certificate value. -/
theorem objective_ge_1584_div_5243 {N : ℕ} (hN : 1 ≤ N)
    (mass : PivotRepairMass N) (hfeasible : IsPivotRepairMassFeasible mass) :
    1584 / 5243 ≤ (input N hN).objective mass := by
  let pivotIndex : (input N hN).ConstraintIndex := Sum.inr (Sum.inl ())
  have hpivot : (input N hN).pivotCap - (input N hN).prescribedPayoff mass 0 ≤
      (input N hN).objective mass := by
    have h := Finset.le_sup'
      (f := (input N hN).constraintGain mass) (Finset.mem_univ pivotIndex)
    change (input N hN).pivotCap - (input N hN).prescribedPayoff mass 0 ≤
      (input N hN).objective mass at h
    exact h
  have hne : (1 : Fin 4) ≠ (input N hN).pivot := by
    change (1 : Fin 4) ≠ 0
    decide
  let responder : (input N hN).Nonpivot := ⟨1, hne⟩
  let neverIndex : (input N hN).ConstraintIndex :=
    Sum.inr (Sum.inr (responder, Sum.inr (0 : Fin 3)))
  have hone : (input N hN).responderNeverEndpoint mass 1 -
        (input N hN).prescribedPayoff mass 1 ≤ (input N hN).objective mass := by
    have h := Finset.le_sup'
      (f := (input N hN).constraintGain mass) (Finset.mem_univ neverIndex)
    change (input N hN).responderNeverEndpoint mass 1 -
      (input N hN).prescribedPayoff mass 1 ≤ (input N hN).objective mass at h
    exact h
  rw [pivotDebt_formula hN mass hfeasible] at hpivot
  rw [playerOne_neverGain_formula hN mass hfeasible] at hone
  have hcertificate := weighted_certificate_lower_bound
    (beforeMass hN mass) (atMass hN mass) (pivotRepairLate mass)
      (pivotRepairNever mass) (aggregate_sum_eq_one hN hfeasible)
      (beforeMass_nonneg hN hfeasible) hfeasible.2.2.1
  nlinarith

end GameTheory.PivotRepairRationalLowerBound
