import UniformEquilibrium.Diagnostics.Quitting.PureTimeCapAttainment
import UniformEquilibrium.Quitting.ControllerTester.RenewableBarrierSaturation

/-! # Concrete two-clock renewable-barrier regression -/

noncomputable section

namespace GameTheory.RenewableTwoClockRegression

open GameTheory

abbrev Player := Fin 4

/-- The reviewed four-player reward table.  Every coalition involving either
sentinel player `2` or `3` has the zero payoff vector. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if 2 ∈ terminal.1 ∨ 3 ∈ terminal.1 then 0
    else if terminal.1 = {0} then if who = 0 then 1 else 0
    else if terminal.1 = {1} then
      if who = 0 then 1 else if who = 1 then -1 else 0
    else if terminal.1 = {0, 1} then if who = 1 then 1 else 0
    else 0

/-- State `A=(2,2,1,1)` at the fixed sentinel horizon `H=1`. -/
def clocksA : QuittingPureTimeProfile Player := ![some 2, some 2, some 1, some 1]

/-- State `B=(0,2,1,1)`. -/
def clocksB : QuittingPureTimeProfile Player := ![some 0, some 2, some 1, some 1]

/-- State `C=(0,0,1,1)`. -/
def clocksC : QuittingPureTimeProfile Player := ![some 0, some 0, some 1, some 1]

/-- State `D=(2,0,1,1)`. -/
def clocksD : QuittingPureTimeProfile Player := ![some 2, some 0, some 1, some 1]

def profile (clocks : QuittingPureTimeProfile Player) :
    (quittingGame reward).BehaviorProfile :=
  quittingPureTimeProfileBehavior reward clocks

@[simp] theorem reward_of_sentinel_mem
    (terminal : {S : Finset Player // S.Nonempty}) (who : Player)
    (h : 2 ∈ terminal.1 ∨ 3 ∈ terminal.1) :
    reward terminal who = 0 := by
  simp [reward, h]

private theorem payoff_eq_reward_at_first
    (clocks : QuittingPureTimeProfile Player) (deadline : ℕ)
    (hbefore : ∀ time < deadline, quittingPureTimeCoalitionAt clocks time = ∅)
    (hat : (quittingPureTimeCoalitionAt clocks deadline).Nonempty) :
    quittingTerminalPayoff reward (profile clocks) =
      reward ⟨quittingPureTimeCoalitionAt clocks deadline, hat⟩ := by
  exact quittingTerminalPayoff_pureTimeProfileBehavior_eq
    reward clocks deadline hbefore hat

@[simp] theorem coalition_B_zero :
    quittingPureTimeCoalitionAt clocksB 0 = {0} := by
  ext who
  fin_cases who <;> simp [quittingPureTimeCoalitionAt, clocksB]

@[simp] theorem coalition_C_zero :
    quittingPureTimeCoalitionAt clocksC 0 = {0, 1} := by
  ext who
  fin_cases who <;> simp [quittingPureTimeCoalitionAt, clocksC]

@[simp] theorem coalition_D_zero :
    quittingPureTimeCoalitionAt clocksD 0 = {1} := by
  ext who
  fin_cases who <;> simp [quittingPureTimeCoalitionAt, clocksD]

theorem payoff_A :
    quittingTerminalPayoff reward (profile clocksA) = (fun _ => 0) := by
  have hbefore : ∀ time < 1, quittingPureTimeCoalitionAt clocksA time = ∅ := by
    intro time htime
    interval_cases time
    ext who
    fin_cases who <;> simp [quittingPureTimeCoalitionAt, clocksA]
  have hat : (quittingPureTimeCoalitionAt clocksA 1).Nonempty := by
    refine ⟨2, ?_⟩
    simp [quittingPureTimeCoalitionAt, clocksA]
  rw [payoff_eq_reward_at_first clocksA 1 hbefore hat]
  funext who
  apply reward_of_sentinel_mem
  left
  simp [quittingPureTimeCoalitionAt, clocksA]

theorem payoff_B :
    quittingTerminalPayoff reward (profile clocksB) = ![1, 0, 0, 0] := by
  have hat : (quittingPureTimeCoalitionAt clocksB 0).Nonempty := by
    refine ⟨0, ?_⟩
    simp [quittingPureTimeCoalitionAt, clocksB]
  rw [payoff_eq_reward_at_first clocksB 0 (by omega) hat]
  funext who
  fin_cases who <;> simp [reward]

theorem payoff_C :
    quittingTerminalPayoff reward (profile clocksC) = ![0, 1, 0, 0] := by
  have hat : (quittingPureTimeCoalitionAt clocksC 0).Nonempty := by
    refine ⟨0, ?_⟩
    simp [quittingPureTimeCoalitionAt, clocksC]
  rw [payoff_eq_reward_at_first clocksC 0 (by omega) hat]
  have hne : ({0, 1} : Finset Player) ≠ {0} := by decide
  funext who
  fin_cases who <;> simp [reward, hne]

theorem payoff_D :
    quittingTerminalPayoff reward (profile clocksD) = ![1, -1, 0, 0] := by
  have hat : (quittingPureTimeCoalitionAt clocksD 0).Nonempty := by
    refine ⟨1, ?_⟩
    simp [quittingPureTimeCoalitionAt, clocksD]
  rw [payoff_eq_reward_at_first clocksD 0 (by omega) hat]
  funext who
  fin_cases who <;> simp [reward]

private theorem clocksA_before_one (who : Player) :
    ∀ time < 1, quittingPureTimeOpponentCoalitionAt clocksA who time = ∅ := by
  intro time htime
  interval_cases time
  ext other
  fin_cases who <;> fin_cases other <;>
    simp [quittingPureTimeOpponentCoalitionAt, quittingPureTimeCoalitionAt,
      clocksA]

private theorem clocksA_opponents_one_nonempty (who : Player) :
    (quittingPureTimeOpponentCoalitionAt clocksA who 1).Nonempty := by
  fin_cases who
  · exact ⟨2, by simp [quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksA]⟩
  · exact ⟨2, by simp [quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksA]⟩
  · exact ⟨3, by simp [quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksA]⟩
  · exact ⟨2, by simp [quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksA]⟩

theorem cap_A :
    quittingContinuationBestResponseValue reward (profile clocksA) =
      ![1, 0, 0, 0] := by
  funext who
  have hcap := quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
    reward clocksA who 1 (by omega) (clocksA_before_one who)
      (clocksA_opponents_one_nonempty who)
  change quittingContinuationBestResponseValue reward
    (quittingPureTimeProfileBehavior reward clocksA) who = _
  rw [hcap]
  fin_cases who <;>
    simp [reward, quittingSingletonTerminal,
      quittingPureTimeOpponentCoalitionAt, quittingPureTimeCoalitionAt, clocksA]

@[simp] theorem opponents_B_one_zero :
    quittingPureTimeOpponentCoalitionAt clocksB 1 0 = {0} := by
  ext other
  fin_cases other <;> simp [quittingPureTimeOpponentCoalitionAt,
    quittingPureTimeCoalitionAt, clocksB]

theorem cap_B :
    quittingContinuationBestResponseValue reward (profile clocksB) =
      ![1, 1, 0, 0] := by
  unfold profile
  funext who
  fin_cases who
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksB) 0 = 1
    have hbefore : ∀ time < 1,
        quittingPureTimeOpponentCoalitionAt clocksB 0 time = ∅ := by
      intro time htime
      interval_cases time
      ext other
      fin_cases other <;> simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksB]
    have hat : (quittingPureTimeOpponentCoalitionAt clocksB 0 1).Nonempty := by
      exact ⟨2, by simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksB]⟩
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
      reward clocksB 0 1 (by omega) hbefore hat]
    simp [reward, quittingSingletonTerminal, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksB]
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksB) 1 = 1
    have hat : (quittingPureTimeOpponentCoalitionAt clocksB 1 0).Nonempty := by
      exact ⟨0, by simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksB]⟩
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksB 1 hat]
    simp only [opponents_B_one_zero]
    have hinsert : (insert 1 ({0} : Finset Player)) = {0, 1} := by
      ext other
      fin_cases other <;> simp
    have hne : ({0, 1} : Finset Player) ≠ {0} := by decide
    simp [reward, hinsert, hne]
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksB) 2 = 0
    have hat : (quittingPureTimeOpponentCoalitionAt clocksB 2 0).Nonempty := by
      exact ⟨0, by simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksB]⟩
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksB 2 hat]
    simp [reward, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksB]
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksB) 3 = 0
    have hat : (quittingPureTimeOpponentCoalitionAt clocksB 3 0).Nonempty := by
      exact ⟨0, by simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksB]⟩
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksB 3 hat]
    simp [reward, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksB]

private theorem clocksC_opponents_zero_nonempty (who : Player) :
    (quittingPureTimeOpponentCoalitionAt clocksC who 0).Nonempty := by
  fin_cases who
  · exact ⟨1, by simp [quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksC]⟩
  · exact ⟨0, by simp [quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksC]⟩
  · exact ⟨0, by simp [quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksC]⟩
  · exact ⟨0, by simp [quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksC]⟩

theorem cap_C :
    quittingContinuationBestResponseValue reward (profile clocksC) =
      ![1, 1, 0, 0] := by
  unfold profile
  funext who
  fin_cases who
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksC) 0 = 1
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksC 0 (clocksC_opponents_zero_nonempty 0)]
    simp only [quittingPureTimeOpponentCoalitionAt, coalition_C_zero]
    have hne : ({0, 1} : Finset Player) ≠ {0} := by decide
    simp [reward, hne]
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksC) 1 = 1
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksC 1 (clocksC_opponents_zero_nonempty 1)]
    simp only [quittingPureTimeOpponentCoalitionAt, coalition_C_zero]
    have hne : ({0, 1} : Finset Player) ≠ {0} := by decide
    have herase : ({0, 1} : Finset Player).erase 1 = {0} := by decide
    have hinsert : insert 1 ({0} : Finset Player) = {0, 1} := by decide
    simp [reward, hne, herase, hinsert]
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksC) 2 = 0
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksC 2 (clocksC_opponents_zero_nonempty 2)]
    simp [reward, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksC]
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksC) 3 = 0
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksC 3 (clocksC_opponents_zero_nonempty 3)]
    simp [reward, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksC]

theorem cap_D :
    quittingContinuationBestResponseValue reward (profile clocksD) =
      ![1, 0, 0, 0] := by
  unfold profile
  funext who
  fin_cases who
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksD) 0 = 1
    have hat : (quittingPureTimeOpponentCoalitionAt clocksD 0 0).Nonempty := by
      exact ⟨1, by simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksD]⟩
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksD 0 hat]
    simp only [quittingPureTimeOpponentCoalitionAt, coalition_D_zero]
    have hne : ({0, 1} : Finset Player) ≠ {0} := by decide
    simp [reward, hne]
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksD) 1 = 0
    have hbefore : ∀ time < 1,
        quittingPureTimeOpponentCoalitionAt clocksD 1 time = ∅ := by
      intro time htime
      interval_cases time
      ext other
      fin_cases other <;> simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksD]
    have hat : (quittingPureTimeOpponentCoalitionAt clocksD 1 1).Nonempty := by
      exact ⟨2, by simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksD]⟩
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
      reward clocksD 1 1 (by omega) hbefore hat]
    simp [reward, quittingSingletonTerminal, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksD]
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksD) 2 = 0
    have hat : (quittingPureTimeOpponentCoalitionAt clocksD 2 0).Nonempty := by
      exact ⟨1, by simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksD]⟩
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksD 2 hat]
    simp [reward, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksD]
  · change quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward clocksD) 3 = 0
    have hat : (quittingPureTimeOpponentCoalitionAt clocksD 3 0).Nonempty := by
      exact ⟨1, by simp [quittingPureTimeOpponentCoalitionAt,
        quittingPureTimeCoalitionAt, clocksD]⟩
    rw [quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
      reward clocksD 3 hat]
    simp [reward, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt, clocksD]

theorem clocks_B_eq_update_A : clocksB = Function.update clocksA 0 (some 0) := by
  funext who
  fin_cases who <;> simp [clocksA, clocksB]

theorem clocks_C_eq_update_B : clocksC = Function.update clocksB 1 (some 0) := by
  funext who
  fin_cases who <;> simp [clocksB, clocksC]

theorem clocks_D_eq_update_C : clocksD = Function.update clocksC 0 (some 2) := by
  funext who
  fin_cases who <;> simp [clocksC, clocksD]

theorem clocks_A_eq_update_D : clocksA = Function.update clocksD 1 (some 2) := by
  funext who
  fin_cases who <;> simp [clocksA, clocksD]

theorem response_cycle_profiles :
    profile clocksB = Function.update (profile clocksA) 0
        (quittingPureTimeBehaviorStrategy reward 0 (some 0)) ∧
      profile clocksC = Function.update (profile clocksB) 1
        (quittingPureTimeBehaviorStrategy reward 1 (some 0)) ∧
      profile clocksD = Function.update (profile clocksC) 0
        (quittingPureTimeBehaviorStrategy reward 0 (some 2)) ∧
      profile clocksA = Function.update (profile clocksD) 1
        (quittingPureTimeBehaviorStrategy reward 1 (some 2)) := by
  constructor
  · rw [clocks_B_eq_update_A]
    exact quittingPureTimeProfileBehavior_update reward clocksA 0 (some 0)
  constructor
  · rw [clocks_C_eq_update_B]
    exact quittingPureTimeProfileBehavior_update reward clocksB 1 (some 0)
  constructor
  · rw [clocks_D_eq_update_C]
    exact quittingPureTimeProfileBehavior_update reward clocksC 0 (some 2)
  · rw [clocks_A_eq_update_D]
    exact quittingPureTimeProfileBehavior_update reward clocksD 1 (some 2)

theorem response_cycle_exact_caps_and_gains :
    quittingTerminalPayoff reward (profile clocksB) 0 =
        quittingContinuationBestResponseValue reward (profile clocksA) 0 ∧
      quittingTerminalPayoff reward (profile clocksB) 0 -
          quittingTerminalPayoff reward (profile clocksA) 0 = 1 ∧
    quittingTerminalPayoff reward (profile clocksC) 1 =
        quittingContinuationBestResponseValue reward (profile clocksB) 1 ∧
      quittingTerminalPayoff reward (profile clocksC) 1 -
          quittingTerminalPayoff reward (profile clocksB) 1 = 1 ∧
    quittingTerminalPayoff reward (profile clocksD) 0 =
        quittingContinuationBestResponseValue reward (profile clocksC) 0 ∧
      quittingTerminalPayoff reward (profile clocksD) 0 -
          quittingTerminalPayoff reward (profile clocksC) 0 = 1 ∧
    quittingTerminalPayoff reward (profile clocksA) 1 =
        quittingContinuationBestResponseValue reward (profile clocksD) 1 ∧
      quittingTerminalPayoff reward (profile clocksA) 1 -
          quittingTerminalPayoff reward (profile clocksD) 1 = 1 := by
  rw [payoff_A, payoff_B, payoff_C, payoff_D, cap_A, cap_B, cap_C, cap_D]
  norm_num

theorem rawMaximumDebt_A : quittingControllerRawMaximumDebt
    (quittingTerminalSemanticPair reward (profile clocksA)) = 1 := by
  unfold quittingControllerRawMaximumDebt
    QuittingBoundaryHolonomy.finitePlayerMax
  simp only [quittingTerminalSemanticPair, payoff_A, cap_A]
  apply le_antisymm
  · apply Finset.sup'_le
    intro who _
    fin_cases who <;> norm_num
  · exact (by
      have h := Finset.le_sup'
        (fun who : Player => (![1, 0, 0, 0] : Player → ℝ) who)
        (Finset.mem_univ (0 : Player))
      simpa using h)

private theorem finitePlayerMax_eq_one
    (value : Player → ℝ) (hle : ∀ who, value who ≤ 1)
    (witness : Player) (hwitness : value witness = 1) :
    QuittingBoundaryHolonomy.finitePlayerMax value = 1 := by
  unfold QuittingBoundaryHolonomy.finitePlayerMax
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun who _ => hle who
  · exact hwitness ▸ Finset.le_sup' value (Finset.mem_univ witness)

theorem rawMaximumDebt_B : quittingControllerRawMaximumDebt
    (quittingTerminalSemanticPair reward (profile clocksB)) = 1 := by
  unfold quittingControllerRawMaximumDebt
  simp only [quittingTerminalSemanticPair, payoff_B, cap_B]
  apply finitePlayerMax_eq_one (witness := 1)
  · intro who
    fin_cases who <;> norm_num
  · norm_num

theorem rawMaximumDebt_C : quittingControllerRawMaximumDebt
    (quittingTerminalSemanticPair reward (profile clocksC)) = 1 := by
  unfold quittingControllerRawMaximumDebt
  simp only [quittingTerminalSemanticPair, payoff_C, cap_C]
  apply finitePlayerMax_eq_one (witness := 0)
  · intro who
    fin_cases who <;> norm_num
  · norm_num

theorem rawMaximumDebt_D : quittingControllerRawMaximumDebt
    (quittingTerminalSemanticPair reward (profile clocksD)) = 1 := by
  unfold quittingControllerRawMaximumDebt
  simp only [quittingTerminalSemanticPair, payoff_D, cap_D]
  apply finitePlayerMax_eq_one (witness := 1)
  · intro who
    fin_cases who <;> norm_num
  · norm_num

/-- The universal controller prefix in which sentinel player `2` Quits
surely and every other player Continues. -/
def sentinelRoot : Player → PMF Bool := fun who =>
  if who = 2 then PMF.pure true else PMF.pure false

private theorem sentinelPrefix_eq_zero_of_playerTwo_zero
    (pair : QuittingTerminalSemanticPair Player)
    (hpayoff : pair.1 2 = 0) (hcap : pair.2 2 = 0) :
    quittingTerminalSemanticPrefix reward sentinelRoot pair =
      ((fun _ => 0), (fun _ => 0)) := by
  have hroot : sentinelRoot = fun who => PMF.pure (decide (who = 2)) := by
    funext who
    by_cases h : who = 2 <;> simp [sentinelRoot, h]
  rw [hroot]
  have htwoAfterZeroContinues :
      ({x : Player | x ≠ 0 ∧ x = 2} : Finset Player).Nonempty := by
    exact ⟨2, by decide⟩
  have hwith (who : Player) :
      ({x : Player | x = who ∨ x = 2} : Finset Player).Nonempty := by
    exact ⟨2, by simp⟩
  have hwithout (who : Player) (hne : who ≠ 2) :
      ({x : Player | x ≠ who ∧ x = 2} : Finset Player).Nonempty := by
    refine ⟨2, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hne.symm, trivial⟩
  apply Prod.ext <;> funext who <;> fin_cases who <;>
    simp [quittingTerminalSemanticPrefix, quittingRootSuccessorPayoff,
      quittingRootQuitPayoff, quittingRootContinuePayoff,
      quittingRootExpectedPayoff, quittingRootPayoff, quittingQuitters, reward,
      Math.PMFProduct.pmfPi_pure, Math.Probability.expect_pure,
      Math.PMFProduct.pmfPi_update_pure_family,
      Function.update_apply, htwoAfterZeroContinues, hwith, hwithout,
      hpayoff, hcap]

theorem sentinelPrefix_A_eq_zero :
    quittingTerminalSemanticPrefix reward sentinelRoot
        (quittingTerminalSemanticPair reward (profile clocksA)) =
      ((fun _ => 0), (fun _ => 0)) := by
  apply sentinelPrefix_eq_zero_of_playerTwo_zero
  · change quittingTerminalPayoff reward (profile clocksA) 2 = 0
    exact congrFun payoff_A 2
  · change quittingContinuationBestResponseValue reward (profile clocksA) 2 = 0
    exact congrFun cap_A 2

theorem sentinelPrefix_B_eq_zero :
    quittingTerminalSemanticPrefix reward sentinelRoot
        (quittingTerminalSemanticPair reward (profile clocksB)) =
      ((fun _ => 0), (fun _ => 0)) := by
  apply sentinelPrefix_eq_zero_of_playerTwo_zero
  · change quittingTerminalPayoff reward (profile clocksB) 2 = 0
    exact congrFun payoff_B 2
  · change quittingContinuationBestResponseValue reward (profile clocksB) 2 = 0
    exact congrFun cap_B 2

theorem sentinelPrefix_C_eq_zero :
    quittingTerminalSemanticPrefix reward sentinelRoot
        (quittingTerminalSemanticPair reward (profile clocksC)) =
      ((fun _ => 0), (fun _ => 0)) := by
  apply sentinelPrefix_eq_zero_of_playerTwo_zero
  · change quittingTerminalPayoff reward (profile clocksC) 2 = 0
    exact congrFun payoff_C 2
  · change quittingContinuationBestResponseValue reward (profile clocksC) 2 = 0
    exact congrFun cap_C 2

theorem sentinelPrefix_D_eq_zero :
    quittingTerminalSemanticPrefix reward sentinelRoot
        (quittingTerminalSemanticPair reward (profile clocksD)) =
      ((fun _ => 0), (fun _ => 0)) := by
  apply sentinelPrefix_eq_zero_of_playerTwo_zero
  · change quittingTerminalPayoff reward (profile clocksD) 2 = 0
    exact congrFun payoff_D 2
  · change quittingContinuationBestResponseValue reward (profile clocksD) 2 = 0
    exact congrFun cap_D 2

private theorem wordInf_eq_zero_of_sentinelPrefix
    (pair : QuittingTerminalSemanticPair Player)
    (hprefix : quittingTerminalSemanticPrefix reward sentinelRoot pair =
      ((fun _ => 0), (fun _ => 0))) :
    quittingControllerWordInf reward quittingTerminalSemanticExploitability pair = 0 := by
  apply le_antisymm
  · calc
      quittingControllerWordInf reward quittingTerminalSemanticExploitability pair ≤
          quittingTerminalSemanticExploitability
            (quittingControllerRootListEvalFrom reward
              [quittingSimplexOfRoot sentinelRoot] pair) :=
        quittingControllerWordInf_le_word reward _
          quittingControllerSemanticExploitability_nonneg pair _
      _ = 0 := by
        simp only [quittingControllerRootListEvalFrom_cons,
          quittingControllerRootListEvalFrom_nil,
          quittingRootOfSimplex_simplexOfRoot, hprefix]
        simp [quittingTerminalSemanticExploitability,
          quittingTerminalSemanticDebt,
          QuittingBoundaryHolonomy.finitePlayerMax]
  · exact quittingControllerWordInf_nonneg reward _
      quittingControllerSemanticExploitability_nonneg pair

theorem cycle_source_wordInf_eq_zero :
    (∀ clocks ∈ [clocksA, clocksB, clocksC, clocksD],
      quittingControllerWordInf reward quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward (profile clocks)) = 0) := by
  intro clocks hclocks
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hclocks
  rcases hclocks with rfl | rfl | rfl | rfl
  · exact wordInf_eq_zero_of_sentinelPrefix _ sentinelPrefix_A_eq_zero
  · exact wordInf_eq_zero_of_sentinelPrefix _ sentinelPrefix_B_eq_zero
  · exact wordInf_eq_zero_of_sentinelPrefix _ sentinelPrefix_C_eq_zero
  · exact wordInf_eq_zero_of_sentinelPrefix _ sentinelPrefix_D_eq_zero

private theorem rawWordInf_eq_semanticWordInf_of_mem_carrier
    (pair : QuittingTerminalSemanticPair Player)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingControllerWordInf reward quittingControllerRawMaximumDebt pair =
      quittingControllerWordInf reward quittingTerminalSemanticExploitability pair := by
  unfold quittingControllerWordInf
  congr 1
  funext roots
  exact quittingControllerRawMaximumDebt_eq_semanticExploitability_of_mem_carrier
    reward (quittingControllerRootListEvalFrom_mem_carrier reward roots pair hpair)

theorem cycle_source_rawMaximumDebt_wordInf_eq_zero :
    ∀ clocks ∈ [clocksA, clocksB, clocksC, clocksD],
      quittingControllerWordInf reward quittingControllerRawMaximumDebt
        (quittingTerminalSemanticPair reward (profile clocks)) = 0 := by
  intro clocks hclocks
  have hcarrier : quittingTerminalSemanticPair reward (profile clocks) ∈
      quittingTerminalSemanticCarrier reward :=
    subset_closure (Set.mem_range_self (profile clocks))
  rw [rawWordInf_eq_semanticWordInf_of_mem_carrier _ hcarrier]
  exact cycle_source_wordInf_eq_zero clocks hclocks

/-- Actual behavioral profile obtained by executing the sentinel root before
the first cycle state. -/
def sentinelProfile : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward sentinelRoot (profile clocksA)

theorem sentinelProfile_semanticPair_eq_zero :
    quittingTerminalSemanticPair reward sentinelProfile =
      ((fun _ => 0), (fun _ => 0)) := by
  rw [sentinelProfile, quittingTerminalSemanticPair_rootThenContinuation]
  exact sentinelPrefix_A_eq_zero

theorem sentinelProfile_isZeroAsymptoticNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 sentinelProfile := by
  intro who deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward sentinelProfile who deviation
  have hpayoff : quittingTerminalPayoff reward sentinelProfile who = 0 := by
    exact congrFun (congrArg Prod.fst sentinelProfile_semanticPair_eq_zero) who
  have hcap : quittingContinuationBestResponseValue reward sentinelProfile who = 0 := by
    exact congrFun (congrArg Prod.snd sentinelProfile_semanticPair_eq_zero) who
  rw [hcap] at hdeviation
  rw [hpayoff]
  simpa using hdeviation

theorem sentinelProfile_rawMaximumDebt_eq_zero :
    quittingControllerRawMaximumDebt
      (quittingTerminalSemanticPair reward sentinelProfile) = 0 := by
  rw [sentinelProfile_semanticPair_eq_zero]
  unfold quittingControllerRawMaximumDebt
    QuittingBoundaryHolonomy.finitePlayerMax
  simp

/-- The actual zero-debt sentinel profile attains the global carrier minimum. -/
theorem sentinelProfile_isMinimum_rawMaximumDebt :
    ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      quittingControllerRawMaximumDebt
          (quittingTerminalSemanticPair reward sentinelProfile) ≤
        quittingControllerRawMaximumDebt pair := by
  intro pair hpair
  rw [sentinelProfile_rawMaximumDebt_eq_zero,
    quittingControllerRawMaximumDebt_eq_semanticExploitability_of_mem_carrier
      reward hpair]
  exact quittingControllerSemanticExploitability_nonneg pair

/-- The four actual semantic points of the renewable response cycle. -/
def cycleSeed : Set (QuittingTerminalSemanticPair Player) :=
  {pair | ∃ clocks ∈ [clocksA, clocksB, clocksC, clocksD],
    pair = quittingTerminalSemanticPair reward (profile clocks)}

/-- The universal-prefix hull of the fixed-gap response cycle has an attained
raw-debt floor exactly equal to zero. -/
theorem exists_cycleHull_minimum_rawMaximumDebt_eq_zero :
    ∃ minimum ∈ quittingUniversalPrefixHull reward cycleSeed,
      (∀ pair ∈ quittingUniversalPrefixHull reward cycleSeed,
        quittingControllerRawMaximumDebt minimum ≤
          quittingControllerRawMaximumDebt pair) ∧
      quittingControllerRawMaximumDebt minimum = 0 := by
  have hseedCarrier : cycleSeed ⊆ quittingTerminalSemanticCarrier reward := by
    rintro pair ⟨clocks, _, rfl⟩
    exact subset_closure (Set.mem_range_self (profile clocks))
  have hseedBox : cycleSeed ⊆ quittingTerminalSemanticBox Player
      (quittingRewardBound reward) := fun pair hpair =>
    quittingTerminalSemanticCarrier_mem_box reward pair
      (abs_reward_le_quittingRewardBound reward) (hseedCarrier hpair)
  have hseedNonempty : cycleSeed.Nonempty := by
    refine ⟨quittingTerminalSemanticPair reward (profile clocksA), ?_⟩
    exact ⟨clocksA, by simp, rfl⟩
  obtain ⟨minimum, hminimumMem, hminimum, heq⟩ :=
    exists_minimizer_rawMaximumDebt_universalPrefixHull_eq_sInf_wordInf_of_box
      reward cycleSeed (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward) hseedBox hseedNonempty
  have hrange : Set.range (fun pair : cycleSeed =>
      quittingControllerWordInf reward quittingControllerRawMaximumDebt pair.1) =
      {0} := by
    ext value
    constructor
    · rintro ⟨pair, rfl⟩
      rw [Set.mem_singleton_iff]
      obtain ⟨clocks, hclocks, hpair⟩ := pair.2
      change quittingControllerWordInf reward quittingControllerRawMaximumDebt
        pair.1 = 0
      rw [hpair]
      exact cycle_source_rawMaximumDebt_wordInf_eq_zero clocks hclocks
    · intro hvalue
      rw [Set.mem_singleton_iff] at hvalue
      subst value
      refine ⟨⟨quittingTerminalSemanticPair reward (profile clocksA), ?_⟩, ?_⟩
      · exact ⟨clocksA, by simp, rfl⟩
      · exact cycle_source_rawMaximumDebt_wordInf_eq_zero clocksA (by simp)
  refine ⟨minimum, hminimumMem, hminimum, ?_⟩
  rw [heq, hrange, csInf_singleton]

end GameTheory.RenewableTwoClockRegression
