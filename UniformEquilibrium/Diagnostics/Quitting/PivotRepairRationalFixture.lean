import UniformEquilibrium.Quitting.Terminal.PivotRepairExactObjective

noncomputable section

namespace GameTheory.PivotRepairRationalFixture

open Math.ProbabilityMassFunction
open _root_.Math.Probability

/-- The literal four-player terminal table from the rational repair test. -/
def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who ↦
    let S := terminal.1
    if who = 0 then
      match decide (0 ∈ S), decide (1 ∈ S), decide (2 ∈ S) with
      | false, false, false => 0 | true, false, false => 1
      | false, true, false => 7 | false, false, true => 7
      | true, true, false => 6 | true, false, true => 9
      | false, true, true => 7 | true, true, true => 7
    else if who = 1 then
      match decide (0 ∈ S), decide (1 ∈ S), decide (2 ∈ S) with
      | false, false, false => 0 | true, false, false => 7
      | false, true, false => 0 | false, false, true => 7
      | true, true, false => 8 | true, false, true => 7
      | false, true, true => 5 | true, true, true => 6
    else if who = 2 then
      match decide (0 ∈ S), decide (1 ∈ S), decide (2 ∈ S) with
      | false, false, false => 0 | true, false, false => 7
      | false, true, false => 7 | false, false, true => 0
      | true, true, false => 7 | true, false, true => 5
      | false, true, true => 8 | true, true, true => 6
    else if 3 ∈ S then
      if 0 ∈ S ∨ 1 ∈ S ∨ 2 ∈ S then -1 else 0
    else if 1 ∈ S ∨ 2 ∈ S then 1 else 0

/-- A law with mass `weight` at the displayed date and the rest at Never. -/
def quitOrNever (time : ℕ) (weight : ℝ) (hzero : 0 ≤ weight)
    (hone : weight ≤ 1) : PMF (Option ℕ) :=
  (bernoulliBool weight hzero hone).map (fun selected ↦ if selected then some time else none)

theorem expect_quitOrNever (time : ℕ) (weight : ℝ) (hzero : 0 ≤ weight)
    (hone : weight ≤ 1) (value : Option ℕ → ℝ) :
    expect (quitOrNever time weight hzero hone) value =
      (1 - weight) * value none + weight * value (some time) := by
  unfold quitOrNever
  rw [expect_map, expect_eq_sum, Fintype.sum_bool]
  simp [add_comm]

def opponents (N : ℕ) (_hN : 1 ≤ N) : Fin 4 → PMF (Option ℕ)
  | 1 => quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num)
  | 2 => quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num)
  | _ => PMF.pure none

def input (N : ℕ) (hN : 1 ≤ N) : QuittingPivotRepairLPInput reward where
  opponents := opponents N hN
  pivot := 0
  deadline := N
  deadline_pos := hN
  opponents_finite := by
    intro j hj choice hchoice
    fin_cases j
    · exact (hj rfl).elim
    · change (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num)) choice ≠ 0
        at hchoice
      rcases choice with _ | time
      · exact Or.inl rfl
      · right
        refine ⟨time, ?_, rfl⟩
        have heq : time = N - 1 := by
          by_contra hne
          apply hchoice
          simp [quitOrNever, PMF.map_apply, hne]
        rw [heq]
        omega
    · change (quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num)) choice ≠ 0
        at hchoice
      rcases choice with _ | time
      · exact Or.inl rfl
      · right
        refine ⟨time, ?_, rfl⟩
        have heq : time = N - 1 := by
          by_contra hne
          apply hchoice
          simp [quitOrNever, PMF.map_apply, hne]
        rw [heq]
        omega
    · left
      simpa [opponents, PMF.pure_apply] using hchoice

@[simp] private theorem input_pivot (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).pivot = 0 := rfl

@[simp] private theorem input_opponents (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).opponents = opponents N hN := rfl

@[simp] private theorem input_deadline (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).deadline = N := rfl

@[simp] theorem opponents_one_at (N : ℕ) (hN : 1 ≤ N) :
    ((opponents N hN 1) (some (N - 1))).toReal = 4 / 7 := by
  simp [opponents, quitOrNever, PMF.map_apply]

@[simp] theorem opponents_one_never (N : ℕ) (hN : 1 ≤ N) :
    ((opponents N hN 1) none).toReal = 3 / 7 := by
  simp [opponents, quitOrNever, PMF.map_apply]
  norm_num

@[simp] theorem opponents_two_at (N : ℕ) (hN : 1 ≤ N) :
    ((opponents N hN 2) (some (N - 1))).toReal = 1 / 7 := by
  simp [opponents, quitOrNever, PMF.map_apply]

@[simp] theorem opponents_two_never (N : ℕ) (hN : 1 ≤ N) :
    ((opponents N hN 2) none).toReal = 6 / 7 := by
  simp [opponents, quitOrNever, PMF.map_apply]
  norm_num

/-- The deterministic all-Never stopping-law profile used in the conditioning formula. -/
def neverLaws : Fin 4 → PMF (Option ℕ) := fun _ ↦ PMF.pure none

private theorem pureLawsPayoff (times : Fin 4 → Option ℕ) (who : Fin 4) :
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward (fun player ↦ PMF.pure (times player))) who =
      quittingTerminalOutcomeReward reward (quittingFirstStoppingOutcome times) who := by
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  unfold quittingIndependentTerminalOutcomeLaw
  rw [Math.PMFProduct.pmfPi_pure, PMF.pure_map, expect_pure]

private theorem opponents_as_updates (N : ℕ) (hN : 1 ≤ N) :
    opponents N hN = Function.update
      (Function.update neverLaws 1
        (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num))) 2
      (quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num)) := by
  funext player
  fin_cases player <;> rfl

/-- The payoff of any observer conditions over the two independent opponent atoms. -/
theorem observerPayoff_conditioned (N : ℕ) (hN : 1 ≤ N)
    (choice : Option ℕ) (observer : Fin 4) :
    (input N hN).purePivotPayoff choice observer =
      (6 / 7) * ((3 / 7) *
          quittingTerminalPayoff reward (quittingStoppingLawProfile reward
            (Function.update neverLaws 0 (PMF.pure choice))) observer +
        (4 / 7) * quittingTerminalPayoff reward (quittingStoppingLawProfile reward
          (Function.update (Function.update neverLaws 0 (PMF.pure choice)) 1
            (PMF.pure (some (N - 1))))) observer) +
      (1 / 7) * ((3 / 7) * quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward
            (Function.update (Function.update neverLaws 0 (PMF.pure choice)) 2
              (PMF.pure (some (N - 1))))) observer +
        (4 / 7) * quittingTerminalPayoff reward (quittingStoppingLawProfile reward
            (Function.update
            (Function.update (Function.update neverLaws 0 (PMF.pure choice)) 1
              (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))))) observer) := by
  change quittingTerminalPayoff reward
    (quittingStoppingLawProfile reward
      (Function.update (opponents N hN) 0 (PMF.pure choice))) observer = _
  rw [opponents_as_updates]
  have hmove : Function.update
      (Function.update
        (Function.update neverLaws 1
          (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num))) 2
        (quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num))) 0
      (PMF.pure choice) = Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure choice)) 1
          (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num))) 2
        (quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num)) := by
    funext player
    fin_cases player <;> rfl
  rw [hmove, quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
    expect_quitOrNever]
  congr 1
  · rw [show Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure choice)) 1
          (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num))) 2
          (PMF.pure none) = Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure choice)) 2
          (PMF.pure none)) 1
          (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num)) by
      exact Function.update_comm (by decide : (1 : Fin 4) ≠ 2) _ _ _]
    rw [quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
      expect_quitOrNever]
    norm_num
    congr 1
    · congr 2
      funext player
      fin_cases player <;> rfl

    · congr 2
      funext player
      fin_cases player <;> rfl
  · rw [show Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure choice)) 1
          (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num))) 2
          (PMF.pure (some (N - 1))) = Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure choice)) 2
          (PMF.pure (some (N - 1)))) 1
          (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num)) by
      exact Function.update_comm (by decide : (1 : Fin 4) ≠ 2) _ _ _]
    rw [quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
      expect_quitOrNever]
    norm_num
    congr 1
    · congr 2
      funext player
      fin_cases player <;> rfl
    · congr 2
      funext player
      fin_cases player <;> rfl

private theorem pureCoalitionPayoff (coalition : Finset (Fin 4))
    (hne : coalition.Nonempty) (time : ℕ) :
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward (fun player ↦
        PMF.pure (if player ∈ coalition then some time else none))) 0 =
      reward ⟨coalition, hne⟩ 0 := by
  rw [pureLawsPayoff, quittingFirstStoppingOutcome_one_date coalition hne time]
  rfl

private theorem allNeverPivotPayoff :
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward neverLaws) 0 = 0 := by
  rw [show neverLaws = fun _ : Fin 4 ↦ PMF.pure none by rfl, pureLawsPayoff]
  simp [quittingTerminalOutcomeReward]

private theorem deterministicNeverBranches (N : ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update neverLaws 0 (PMF.pure none))) 0 = 0 ∧
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (Function.update (Function.update neverLaws 0 (PMF.pure none)) 1
          (PMF.pure (some (N - 1))))) 0 = 7 ∧
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (Function.update (Function.update neverLaws 0 (PMF.pure none)) 2
          (PMF.pure (some (N - 1))))) 0 = 7 ∧
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (Function.update
          (Function.update (Function.update neverLaws 0 (PMF.pure none)) 1
            (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))))) 0 = 7 := by
  have h0 : Function.update neverLaws 0 (PMF.pure none) = neverLaws := by
    funext player
    simp [neverLaws, Function.update_apply]
  rw [h0, allNeverPivotPayoff]
  constructor
  · norm_num
  have h1 := pureCoalitionPayoff {1} (by simp) (N - 1)
  have h2 := pureCoalitionPayoff {2} (by simp) (N - 1)
  have h12 := pureCoalitionPayoff {1, 2} (by simp) (N - 1)
  constructor
  · rw [show Function.update neverLaws 1 (PMF.pure (some (N - 1))) =
        fun player ↦ PMF.pure (if player ∈ ({1} : Finset (Fin 4))
          then some (N - 1) else none) by
      funext player
      fin_cases player <;> rfl, h1]
    norm_num [reward, show (2 : Fin 4) ≠ 1 by omega]
  constructor
  · rw [show Function.update neverLaws 2 (PMF.pure (some (N - 1))) =
        fun player ↦ PMF.pure (if player ∈ ({2} : Finset (Fin 4))
          then some (N - 1) else none) by
      funext player
      fin_cases player <;> rfl, h2]
    norm_num [reward, show (0 : Fin 4) ≠ 2 by omega,
      show (1 : Fin 4) ≠ 2 by omega]
  · rw [show Function.update (Function.update neverLaws 1
          (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))) =
        fun player ↦ PMF.pure (if player ∈ ({1, 2} : Finset (Fin 4))
          then some (N - 1) else none) by
      funext player
      fin_cases player <;> rfl, h12]
    norm_num [reward, show (0 : Fin 4) ≠ 2 by omega]

/-- The pivot's actual Never payoff is `217/49`. -/
theorem pivotPayoff_never (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff none 0 = 217 / 49 := by
  rw [observerPayoff_conditioned N hN none 0]
  rcases deterministicNeverBranches N with ⟨h0, h1, h2, h12⟩
  rw [h0, h1, h2, h12]
  norm_num

private theorem opponentNeverProduct (N : ℕ) (hN : 1 ≤ N) :
    (∏ j ∈ Finset.univ.erase (0 : Fin 4),
      ((opponents N hN j) none).toReal) = 18 / 49 := by
  have hall : (∏ j, ((opponents N hN j) none).toReal) = 18 / 49 := by
    rw [Fin.prod_univ_four, opponents_one_never, opponents_two_never]
    simp [opponents]
    norm_num
  have hzero : ((opponents N hN 0) none).toReal = 1 := by simp [opponents]
  calc
    _ = (∏ j ∈ Finset.univ.erase (0 : Fin 4),
        ((opponents N hN j) none).toReal) * ((opponents N hN 0) none).toReal := by
      rw [hzero, mul_one]
    _ = ∏ j, ((opponents N hN j) none).toReal :=
      Finset.prod_erase_mul Finset.univ
        (fun j : Fin 4 ↦ ((opponents N hN j) none).toReal) (Finset.mem_univ 0)
    _ = 18 / 49 := hall

/-- Every finite pivot time after the common opponent date pays `235/49`. -/
theorem pivotPayoff_after (N : ℕ) (hN : 1 ≤ N) {time : ℕ}
    (htime : N ≤ time) :
    (input N hN).purePivotPayoff (some time) 0 = 235 / 49 := by
  change quittingTerminalPayoff reward
    (quittingStoppingLawProfile reward
      (Function.update (opponents N hN) 0 (PMF.pure (some time)))) 0 = _
  rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_eq_never_add
    reward (opponents N hN) 0 N]
  · change (input N hN).purePivotPayoff none 0 + _ = _
    rw [pivotPayoff_never]
    rw [opponentNeverProduct]
    norm_num [reward, quittingSingletonTerminal,
      show (2 : Fin 4) ≠ 0 by omega]
  · exact (input N hN).opponents_finite
  · exact htime

private theorem deterministicAtBranches (N : ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update neverLaws 0 (PMF.pure (some (N - 1))))) 0 = 1 ∧
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (Function.update (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
          (PMF.pure (some (N - 1))))) 0 = 6 ∧
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (Function.update (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 2
          (PMF.pure (some (N - 1))))) 0 = 9 ∧
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (Function.update
          (Function.update (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
            (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))))) 0 = 7 := by
  have branch (coalition : Finset (Fin 4)) (hne : coalition.Nonempty)
      (laws : Fin 4 → PMF (Option ℕ))
      (hlaws : laws = fun player ↦ PMF.pure
        (if player ∈ coalition then some (N - 1) else none)) :
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward laws) 0 =
        reward ⟨coalition, hne⟩ 0 := by
    rw [hlaws]
    exact pureCoalitionPayoff coalition hne (N - 1)
  have hb0 := branch {0} (by simp)
    (Function.update neverLaws 0 (PMF.pure (some (N - 1))))
    (by funext player; fin_cases player <;> rfl)
  have hb1 := branch {0, 1} (by simp)
    (Function.update (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
      (PMF.pure (some (N - 1))))
    (by funext player; fin_cases player <;> rfl)
  have hb2 := branch {0, 2} (by simp)
    (Function.update (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 2
      (PMF.pure (some (N - 1))))
    (by funext player; fin_cases player <;> rfl)
  have hb12 := branch {0, 1, 2} (by simp)
    (Function.update
      (Function.update (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
        (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))))
    (by funext player; fin_cases player <;> rfl)
  norm_num [reward, show (2 : Fin 4) ≠ 0 by omega,
    show (2 : Fin 4) ≠ 1 by omega, show (1 : Fin 4) ≠ 2 by omega] at hb0 hb1 hb2 hb12
  exact ⟨hb0, hb1, hb2, hb12⟩

/-- The pivot's actual payoff at the common opponent date is `217/49`. -/
theorem pivotPayoff_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff (some (N - 1)) 0 = 217 / 49 := by
  rw [observerPayoff_conditioned N hN (some (N - 1)) 0]
  rcases deterministicAtBranches N with ⟨h0, h1, h2, h12⟩
  rw [h0, h1, h2, h12]
  norm_num

private def beforeTimes (N time : ℕ) (first second : Bool) : Fin 4 → Option ℕ
  | 0 => some time
  | 1 => if first then some (N - 1) else none
  | 2 => if second then some (N - 1) else none
  | _ => none

private theorem firstStoppingOutcome_beforeTimes (N time : ℕ)
    (htime : time < N - 1) (first second : Bool) :
    quittingFirstStoppingOutcome (beforeTimes N time first second) =
      some ⟨{0}, by simp⟩ := by
  let withoutFirst := beforeTimes N time false second
  let pivotOnly := beforeTimes N time false false
  have hfirst : quittingFirstStoppingOutcome (beforeTimes N time first second) =
      quittingFirstStoppingOutcome withoutFirst := by
    cases first
    · rfl
    · apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
        (hidden := 1) (blocker := 0)
      · intro other hother
        fin_cases other <;> simp_all [beforeTimes, withoutFirst]
      · simp [beforeTimes, quittingStoppingTimeValue]
        exact_mod_cast htime
      · simp [beforeTimes, withoutFirst, quittingStoppingTimeValue]
  have hsecond : quittingFirstStoppingOutcome withoutFirst =
      quittingFirstStoppingOutcome pivotOnly := by
    cases second
    · rfl
    · apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
        (hidden := 2) (blocker := 0)
      · intro other hother
        fin_cases other <;> simp_all [beforeTimes, withoutFirst, pivotOnly]
      · simp [beforeTimes, withoutFirst, quittingStoppingTimeValue]
        exact_mod_cast htime
      · simp [beforeTimes, pivotOnly, quittingStoppingTimeValue]
  rw [hfirst, hsecond]
  change quittingFirstStoppingOutcome
      (fun player ↦ if player ∈ ({0} : Finset (Fin 4)) then some time else none) = _
  exact quittingFirstStoppingOutcome_one_date {0} (by simp) time

private theorem deterministicBeforePayoff (N time : ℕ) (htime : time < N - 1)
    (first second : Bool) :
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward (fun player ↦
        PMF.pure (beforeTimes N time first second player))) 0 = 1 := by
  rw [pureLawsPayoff, firstStoppingOutcome_beforeTimes N time htime first second]
  norm_num [quittingTerminalOutcomeReward, reward,
    show (2 : Fin 4) ≠ 0 by omega]

/-- Every pivot time strictly before the common opponent date pays `1`. -/
theorem pivotPayoff_before (N : ℕ) (hN : 1 ≤ N) {time : ℕ}
    (htime : time < N - 1) :
    (input N hN).purePivotPayoff (some time) 0 = 1 := by
  rw [observerPayoff_conditioned N hN (some time) 0]
  have hbranch (first second : Bool) :
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (Function.update
          (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
            (PMF.pure (if first then some (N - 1) else none))) 2
          (PMF.pure (if second then some (N - 1) else none)))) 0 = 1 := by
    rw [show Function.update
        (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
          (PMF.pure (if first then some (N - 1) else none))) 2
        (PMF.pure (if second then some (N - 1) else none)) =
        fun player ↦ PMF.pure (beforeTimes N time first second player) by
      funext player
      fin_cases player <;> cases first <;> cases second <;> rfl]
    exact deterministicBeforePayoff N time htime first second
  have h00 := hbranch false false
  have h10 := hbranch true false
  have h01 := hbranch false true
  have h11 := hbranch true true
  simp only [if_true] at h11
  have h00' : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update neverLaws 0 (PMF.pure (some time)))) 0 = 1 := by
    rw [← h00]
    congr 2
    funext player
    fin_cases player <;> rfl
  have h10' : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 1
        (PMF.pure (some (N - 1))))) 0 = 1 := by
    rw [← h10]
    congr 2
    funext player
    fin_cases player <;> rfl
  have h01' : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update neverLaws 0 (PMF.pure (some time))) 2
        (PMF.pure (some (N - 1))))) 0 = 1 := by
    rw [← h01]
    congr 2
    funext player
    fin_cases player <;> rfl
  rw [h00', h10', h01', h11]
  norm_num

private theorem pivotLatePayoff (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).pivotLatePayoff = 235 / 49 := by
  unfold QuittingPivotRepairLPInput.pivotLatePayoff
  rw [show (input N hN).pivotNeverPayoff = 217 / 49 by
    exact pivotPayoff_never N hN]
  simp only [input_pivot, input_opponents]
  rw [opponentNeverProduct]
  norm_num [input, reward, quittingSingletonTerminal,
    show (2 : Fin 4) ≠ 0 by omega]

/-- The pivot's actual finite LP cap is `235/49`. -/
theorem pivotCap (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).pivotCap = 235 / 49 := by
  unfold QuittingPivotRepairLPInput.pivotCap
  apply le_antisymm
  · apply Finset.sup'_le
    intro candidate _
    rcases candidate with time | endpoint
    · simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue]
      simp only [input_pivot]
      by_cases hbefore : time.1 < N - 1
      · rw [show (input N hN).purePivotPayoff (some time.1) 0 = 1 by
          exact pivotPayoff_before N hN hbefore]
        norm_num
      · have hlt : time.1 < N := by simpa only [input_deadline] using time.isLt
        have heq : time.1 = N - 1 := by omega
        rw [heq, pivotPayoff_at]
        norm_num
    · cases endpoint
      · simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue,
          QuittingPivotRepairLPInput.pivotNeverPayoff]
        simp only [input_pivot]
        rw [pivotPayoff_never]
        norm_num
      · simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue]
        rw [pivotLatePayoff]
  · have hle := Finset.le_sup' (f := (input N hN).pivotCapCandidateValue)
      (show (Sum.inr true : Fin N ⊕ Bool) ∈ Finset.univ by exact Finset.mem_univ _)
    have hcand : (input N hN).pivotCapCandidateValue (Sum.inr true) = 235 / 49 := by
      simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue]
      exact pivotLatePayoff N hN
    exact hcand ▸ hle


end GameTheory.PivotRepairRationalFixture
