import MathUE.FiniteBooleanEndpointOrbit
import MathUE.FinitePivotOrbit
import UniformEquilibrium.Diagnostics.Quitting.PureTimeInheritedResponseAlphabet
import UniformEquilibrium.Diagnostics.Quitting.PureTimeMinimumDescent
import UniformEquilibrium.Quitting.Paths.BehaviorSupportedPureTimeReplacement

/-!
# Selected exact responses on an inherited pure-clock alphabet

An opaque deterministic choice selects a debt-maximizing mover and one exact
cap-attaining inherited clock.  Every conclusion is independent of how ties
are resolved.  The resulting orbit is a horizontal response construction,
not a chronology within one play of the quitting game.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Pure-clock profiles whose clocks belong to one fixed inherited alphabet. -/
abbrev QuittingPureTimeInheritedState
    (initial : QuittingPureTimeProfile ι) :=
  ι → {clock // clock ∈ quittingPureTimeInheritedResponseAlphabet initial}

/-- Exact size of the inherited finite state space. -/
theorem card_quittingPureTimeInheritedState
    (initial : QuittingPureTimeProfile ι) :
    Fintype.card (QuittingPureTimeInheritedState initial) =
      (quittingPureTimeInheritedResponseAlphabet initial).card ^
        Fintype.card ι := by
  simp [QuittingPureTimeInheritedState]

/-- The inherited response state space has the expected alphabet-power bound. -/
theorem card_quittingPureTimeInheritedState_le
    (initial : QuittingPureTimeProfile ι) :
    Fintype.card (QuittingPureTimeInheritedState initial) ≤
      (Fintype.card ι + 2) ^ Fintype.card ι := by
  rw [card_quittingPureTimeInheritedState]
  exact Nat.pow_le_pow_left
    (card_quittingPureTimeInheritedResponseAlphabet_le initial)
    (Fintype.card ι)

/-- For four players the inherited response state space has at most
`6^4 = 1296` states. -/
theorem card_quittingPureTimeInheritedState_le_1296_finFour
    (initial : QuittingPureTimeProfile (Fin 4)) :
    Fintype.card (QuittingPureTimeInheritedState initial) ≤ 1296 := by
  exact (card_quittingPureTimeInheritedState_le initial).trans (by norm_num)

/-- Forget the proof that every clock belongs to the inherited alphabet. -/
def QuittingPureTimeInheritedState.toProfile
    {initial : QuittingPureTimeProfile ι}
    (state : QuittingPureTimeInheritedState initial) :
    QuittingPureTimeProfile ι :=
  fun who => state who

/-- The initial profile, viewed as a state in its inherited alphabet. -/
def quittingPureTimeInitialInheritedState
    (initial : QuittingPureTimeProfile ι) :
    QuittingPureTimeInheritedState initial :=
  fun who => ⟨initial who,
    quittingPureTime_mem_inheritedResponseAlphabet initial who⟩

omit [DecidableEq ι] in
@[simp] theorem quittingPureTimeInitialInheritedState_toProfile
    (initial : QuittingPureTimeProfile ι) :
    (quittingPureTimeInitialInheritedState initial).toProfile = initial := by
  rfl

@[simp] theorem quittingPureTimeInheritedState_toProfile_update
    {initial : QuittingPureTimeProfile ι}
    (source : QuittingPureTimeInheritedState initial) (who : ι)
    (response : {clock // clock ∈
      quittingPureTimeInheritedResponseAlphabet initial}) :
    QuittingPureTimeInheritedState.toProfile
        (Function.update source who response) =
      Function.update source.toProfile who response := by
  funext other
  change ↑(Function.update source who response other) =
    Function.update source.toProfile who (response : Option ℕ) other
  by_cases heq : other = who
  · subst other
    simp
  · rw [Function.update_of_ne heq, Function.update_of_ne heq]
    rfl

/-- One exact response by a debt-maximizing player inside the inherited clock
alphabet.  This is a horizontal response edge, not a temporal game-history
transition. -/
structure QuittingPureTimeMaxDebtExactResponseStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι)
    (source : QuittingPureTimeInheritedState initial) where
  mover : ι
  response : {clock // clock ∈
    quittingPureTimeInheritedResponseAlphabet initial}
  target : QuittingPureTimeInheritedState initial
  target_eq : target = Function.update source mover response
  mover_maximal : ∀ other,
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward source.toProfile)) other ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward source.toProfile)) mover
  cap_attained :
    quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward target.toProfile) mover =
      quittingContinuationBestResponseValue reward
        (quittingPureTimeProfileBehavior reward source.toProfile) mover

namespace QuittingPureTimeMaxDebtExactResponseStep

/-- The target is the literal pure-clock profile update displayed by the step. -/
theorem target_profile_eq_update
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι}
    {source : QuittingPureTimeInheritedState initial}
    (step : QuittingPureTimeMaxDebtExactResponseStep reward initial source) :
    step.target.toProfile =
      Function.update source.toProfile step.mover step.response := by
  rw [step.target_eq, quittingPureTimeInheritedState_toProfile_update]

/-- Exact cap attainment resets the mover's literal terminal debt to zero. -/
theorem target_mover_debt_eq_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι}
    {source : QuittingPureTimeInheritedState initial}
    (step : QuittingPureTimeMaxDebtExactResponseStep reward initial source) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward step.target.toProfile))
        step.mover = 0 := by
  have hcap :
      quittingContinuationBestResponseValue reward
          (quittingPureTimeProfileBehavior reward step.target.toProfile)
          step.mover =
        quittingContinuationBestResponseValue reward
          (quittingPureTimeProfileBehavior reward source.toProfile)
          step.mover := by
    rw [step.target_profile_eq_update,
      quittingPureTimeProfileBehavior_update,
      quittingContinuationBestResponseValue_update_self]
  change quittingContinuationBestResponseValue reward
        (quittingPureTimeProfileBehavior reward step.target.toProfile)
        step.mover -
      quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward step.target.toProfile)
        step.mover = 0
  rw [hcap, step.cap_attained]
  exact sub_self _

/-- The mover's payoff gain is exactly its source terminal debt. -/
theorem mover_payoff_gain_eq_source_debt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι}
    {source : QuittingPureTimeInheritedState initial}
    (step : QuittingPureTimeMaxDebtExactResponseStep reward initial source) :
    quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward step.target.toProfile)
          step.mover -
        quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward source.toProfile) step.mover =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward source.toProfile)) step.mover := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  rw [step.cap_attained]

/-- The total source debt is at most the number of players times the selected
mover's maximal debt. -/
theorem source_debtSum_le_card_mul_mover_debt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι}
    {source : QuittingPureTimeInheritedState initial}
    (step : QuittingPureTimeMaxDebtExactResponseStep reward initial source) :
    quittingPureTimeTerminalSemanticDebtSum reward source.toProfile ≤
      (Fintype.card ι : ℝ) *
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward source.toProfile))
          step.mover := by
  have hsum := (Finset.univ : Finset ι).sum_le_card_nsmul
    (fun who => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingPureTimeProfileBehavior reward source.toProfile)) who)
    (quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingPureTimeProfileBehavior reward source.toProfile)) step.mover)
    (fun who _ => step.mover_maximal who)
  simpa only [quittingPureTimeTerminalSemanticDebtSum,
    quittingTerminalSemanticDebtSum, Finset.card_univ, nsmul_eq_mul] using hsum

/-- A global positive total-debt floor gives the selected mover its average
share of that floor. -/
theorem minimumDebt_div_card_le_source_mover_debt
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι}
    {source : QuittingPureTimeInheritedState initial}
    (step : QuittingPureTimeMaxDebtExactResponseStep reward initial source)
    (minimumDebt : ℝ)
    (hlower : ∀ times : QuittingPureTimeProfile ι,
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times) :
    minimumDebt / Fintype.card ι ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward source.toProfile))
        step.mover := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  apply (div_le_iff₀ hcard).2
  have hlowerSource := hlower source.toProfile
  have hsum := step.source_debtSum_le_card_mul_mover_debt
  nlinarith

end QuittingPureTimeMaxDebtExactResponseStep

/-- Every inherited-alphabet state admits a maximal-debt exact response step
that remains in the same finite state space. -/
theorem exists_quittingPureTimeMaxDebtExactResponseStep
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι)
    (source : QuittingPureTimeInheritedState initial) :
    Nonempty (QuittingPureTimeMaxDebtExactResponseStep reward initial source) := by
  let debt : ι → ℝ := fun who =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingPureTimeProfileBehavior reward source.toProfile)) who
  obtain ⟨mover, _, hmover⟩ := Finset.exists_max_image
    (Finset.univ : Finset ι) debt Finset.univ_nonempty
  obtain ⟨response, hresponse, hcap⟩ :=
    exists_quittingPureTime_capAttainer_mem_inheritedResponseAlphabet
      reward initial source.toProfile mover (fun other => (source other).2)
  let response' : {clock // clock ∈
      quittingPureTimeInheritedResponseAlphabet initial} :=
    ⟨response, hresponse⟩
  let target : QuittingPureTimeInheritedState initial :=
    Function.update source mover response'
  refine ⟨{
    mover := mover
    response := response'
    target := target
    target_eq := rfl
    mover_maximal := ?_
    cap_attained := ?_
  }⟩
  · intro other
    exact hmover other (Finset.mem_univ other)
  · dsimp only [target]
    rw [quittingPureTimeInheritedState_toProfile_update]
    exact hcap

/-- A deterministic choice of maximal-debt exact response. -/
noncomputable def quittingPureTimeSelectedMaxDebtExactResponseStep
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι)
    (source : QuittingPureTimeInheritedState initial) :
    QuittingPureTimeMaxDebtExactResponseStep reward initial source :=
  Classical.choice
    (exists_quittingPureTimeMaxDebtExactResponseStep reward initial source)

/-- Deterministic successor obtained by the selected exact response. -/
noncomputable def quittingPureTimeSelectedExactResponseSuccessor
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) :
    QuittingPureTimeInheritedState initial →
      QuittingPureTimeInheritedState initial :=
  fun source =>
    (quittingPureTimeSelectedMaxDebtExactResponseStep
      reward initial source).target

/-- The deterministic horizontal orbit of selected maximal-debt exact
responses inside the inherited clock alphabet. -/
noncomputable def quittingPureTimeSelectedExactResponseOrbit
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) :
    ℕ → QuittingPureTimeInheritedState initial :=
  Math.finitePivotOrbit
    (quittingPureTimeSelectedExactResponseSuccessor reward initial)
    (quittingPureTimeInitialInheritedState initial)

@[simp] theorem quittingPureTimeSelectedExactResponseOrbit_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) :
    quittingPureTimeSelectedExactResponseOrbit reward initial 0 =
      quittingPureTimeInitialInheritedState initial := by
  rfl

@[simp] theorem quittingPureTimeSelectedExactResponseOrbit_succ
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (time : ℕ) :
    quittingPureTimeSelectedExactResponseOrbit reward initial (time + 1) =
      quittingPureTimeSelectedExactResponseSuccessor reward initial
        (quittingPureTimeSelectedExactResponseOrbit reward initial time) := by
  rfl

/-- Every displayed pure-clock profile on the selected response orbit is a
literal finite unilateral-replacement descendant of the initial profile. -/
theorem isQuittingPureTimeReplacementAncestry_selectedExactResponseOrbit
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (time : ℕ) :
    IsQuittingPureTimeReplacementAncestry initial
      (quittingPureTimeSelectedExactResponseOrbit reward initial time).toProfile := by
  induction time with
  | zero =>
      rw [quittingPureTimeSelectedExactResponseOrbit_zero,
        quittingPureTimeInitialInheritedState_toProfile]
      exact Relation.ReflTransGen.refl
  | succ time ih =>
      let step := quittingPureTimeSelectedMaxDebtExactResponseStep reward initial
        (quittingPureTimeSelectedExactResponseOrbit reward initial time)
      have hstep : IsQuittingPureTimeReplacementAncestry
          (quittingPureTimeSelectedExactResponseOrbit reward initial time).toProfile
          step.target.toProfile := by
        rw [step.target_profile_eq_update]
        exact isQuittingPureTimeReplacementAncestry_update _ step.mover step.response
      have htarget : step.target =
          quittingPureTimeSelectedExactResponseOrbit reward initial (time + 1) := by
        rfl
      rw [htarget] at hstep
      exact ih.trans hstep

/-- Every behavioral profile displayed by the selected pure-clock response
orbit is a literal finite complete-strategy-replacement descendant of the
behavioral interpretation of the initial profile. -/
theorem isQuittingBehaviorReplacementAncestry_selectedExactResponseOrbit
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (time : ℕ) :
    IsQuittingBehaviorReplacementAncestry
      (quittingPureTimeProfileBehavior reward initial)
      (quittingPureTimeProfileBehavior reward
        (quittingPureTimeSelectedExactResponseOrbit reward initial time).toProfile) :=
  isQuittingBehaviorReplacementAncestry_pureTimeProfileBehavior
    (isQuittingPureTimeReplacementAncestry_selectedExactResponseOrbit
      reward initial time)

/-- The selected horizontal response orbit repeats within the cardinality of
its inherited finite state space. -/
theorem exists_boundedRepeat_quittingPureTimeSelectedExactResponseOrbit
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) :
    Nonempty (MathUE.FiniteBooleanEndpointOrbit.BoundedRepeat
      (quittingPureTimeSelectedExactResponseOrbit reward initial)) :=
  MathUE.FiniteBooleanEndpointOrbit.exists_boundedRepeat _

/-- For four players the inherited-state orbit repeats no later than time
`1296 = 6^4`. -/
theorem exists_quittingPureTimeSelectedExactResponseOrbit_repeat_finFour
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (initial : QuittingPureTimeProfile (Fin 4)) :
    ∃ first second : ℕ,
      first < second ∧
      quittingPureTimeSelectedExactResponseOrbit reward initial first =
        quittingPureTimeSelectedExactResponseOrbit reward initial second ∧
      second ≤ 1296 := by
  obtain ⟨bounded⟩ :=
    exists_boundedRepeat_quittingPureTimeSelectedExactResponseOrbit
      reward initial
  refine ⟨bounded.first, bounded.second, bounded.first_lt_second,
    bounded.closes_at, ?_⟩
  exact bounded.second_le_card.trans
    (card_quittingPureTimeInheritedState_le_1296_finFour initial)

/-- The selected exact-response edge leaving one orbit state. -/
noncomputable def quittingPureTimeSelectedExactResponseOrbitStep
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (time : ℕ) :=
  quittingPureTimeSelectedMaxDebtExactResponseStep reward initial
    (quittingPureTimeSelectedExactResponseOrbit reward initial time)

/-- The selected edge's target is literally the next orbit state. -/
theorem quittingPureTimeSelectedExactResponseOrbitStep_target_eq
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (time : ℕ) :
    (quittingPureTimeSelectedExactResponseOrbitStep reward initial time).target =
      quittingPureTimeSelectedExactResponseOrbit reward initial (time + 1) := by
  rfl

/-- Every orbit edge resets the selected mover's target debt to zero. -/
theorem quittingPureTimeSelectedExactResponseOrbitStep_target_mover_debt_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (time : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward
            (quittingPureTimeSelectedExactResponseOrbit reward initial
              (time + 1)).toProfile))
        (quittingPureTimeSelectedExactResponseOrbitStep
          reward initial time).mover = 0 := by
  rw [← quittingPureTimeSelectedExactResponseOrbitStep_target_eq]
  exact (quittingPureTimeSelectedExactResponseOrbitStep
    reward initial time).target_mover_debt_eq_zero

/-- Under a global pure-profile total-debt floor, every selected orbit edge
gains at least the average floor. -/
theorem quittingPureTimeSelectedExactResponseOrbitStep_gain_ge_averageDebt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (minimumDebt : ℝ)
    (hlower : ∀ times : QuittingPureTimeProfile ι,
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times)
    (time : ℕ) :
    minimumDebt / Fintype.card ι ≤
      quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (quittingPureTimeSelectedExactResponseOrbit reward initial
              (time + 1)).toProfile)
          (quittingPureTimeSelectedExactResponseOrbitStep
            reward initial time).mover -
        quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (quittingPureTimeSelectedExactResponseOrbit reward initial
              time).toProfile)
          (quittingPureTimeSelectedExactResponseOrbitStep
            reward initial time).mover := by
  rw [← quittingPureTimeSelectedExactResponseOrbitStep_target_eq,
    (quittingPureTimeSelectedExactResponseOrbitStep
      reward initial time).mover_payoff_gain_eq_source_debt]
  exact (quittingPureTimeSelectedExactResponseOrbitStep
    reward initial time).minimumDebt_div_card_le_source_mover_debt
      minimumDebt hlower

/-- A selected exact-response edge cannot be a self-loop under a positive
global debt floor. -/
theorem quittingPureTimeSelectedExactResponseOrbitStep_target_ne_source
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (minimumDebt : ℝ)
    (hpositive : 0 < minimumDebt)
    (hlower : ∀ times : QuittingPureTimeProfile ι,
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times)
    (time : ℕ) :
    (quittingPureTimeSelectedExactResponseOrbitStep
      reward initial time).target ≠
      quittingPureTimeSelectedExactResponseOrbit reward initial time := by
  let step := quittingPureTimeSelectedExactResponseOrbitStep
    reward initial time
  have hfloor := step.minimumDebt_div_card_le_source_mover_debt
    minimumDebt hlower
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  intro heq
  have hreset := step.target_mover_debt_eq_zero
  rw [heq] at hreset
  have hminimumAverage : 0 < minimumDebt / Fintype.card ι :=
    div_pos hpositive hcard
  linarith

/-- A bounded nontrivial closed segment of the selected horizontal exact-
response orbit. -/
structure QuittingPureTimeExactResponseCycle
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) where
  start : ℕ
  period : ℕ
  two_le_period : 2 ≤ period
  end_le_stateCard : start + period ≤
    Fintype.card (QuittingPureTimeInheritedState initial)
  closes : quittingPureTimeSelectedExactResponseOrbit reward initial
      (start + period) =
    quittingPureTimeSelectedExactResponseOrbit reward initial start

/-- A positive global pure-profile debt floor forces a bounded nontrivial
literal response cycle from every initial pure-clock profile. -/
theorem exists_quittingPureTimeExactResponseCycle
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (minimumDebt : ℝ)
    (hpositive : 0 < minimumDebt)
    (hlower : ∀ times : QuittingPureTimeProfile ι,
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times) :
    Nonempty (QuittingPureTimeExactResponseCycle reward initial) := by
  obtain ⟨bounded⟩ :=
    exists_boundedRepeat_quittingPureTimeSelectedExactResponseOrbit
      reward initial
  let period := bounded.second - bounded.first
  have hperiodPositive : 0 < period := by
    dsimp only [period]
    have hlt := bounded.first_lt_second
    omega
  have hend : bounded.first + period = bounded.second := by
    dsimp only [period]
    omega
  have hcloses : quittingPureTimeSelectedExactResponseOrbit reward initial
        (bounded.first + period) =
      quittingPureTimeSelectedExactResponseOrbit reward initial bounded.first := by
    rw [hend]
    exact bounded.closes_at.symm
  refine ⟨{
    start := bounded.first
    period := period
    two_le_period := ?_
    end_le_stateCard := by rw [hend]; exact bounded.second_le_card
    closes := hcloses
  }⟩
  by_contra hnot
  have hperiodOne : period = 1 := by omega
  have hfixed :
      (quittingPureTimeSelectedExactResponseOrbitStep reward initial
        bounded.first).target =
        quittingPureTimeSelectedExactResponseOrbit reward initial bounded.first := by
    rw [quittingPureTimeSelectedExactResponseOrbitStep_target_eq]
    have hnextEnd : bounded.first + 1 = bounded.second := by omega
    rw [hnextEnd]
    exact bounded.closes_at.symm
  exact quittingPureTimeSelectedExactResponseOrbitStep_target_ne_source
    reward initial minimumDebt hpositive hlower bounded.first hfixed

/-- For four players the positive-floor response cycle closes by time 1296,
and its nontrivial period is also at most 1296. -/
theorem exists_quittingPureTimeExactResponseCycle_finFour
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (initial : QuittingPureTimeProfile (Fin 4)) (minimumDebt : ℝ)
    (hpositive : 0 < minimumDebt)
    (hlower : ∀ times : QuittingPureTimeProfile (Fin 4),
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times) :
    ∃ cycle : QuittingPureTimeExactResponseCycle reward initial,
      cycle.start + cycle.period ≤ 1296 ∧ cycle.period ≤ 1296 := by
  obtain ⟨cycle⟩ := exists_quittingPureTimeExactResponseCycle
    reward initial minimumDebt hpositive hlower
  refine ⟨cycle, ?_, ?_⟩
  · exact cycle.end_le_stateCard.trans
      (card_quittingPureTimeInheritedState_le_1296_finFour initial)
  · exact (Nat.le_add_left cycle.period cycle.start).trans (by
      exact cycle.end_le_stateCard.trans
        (card_quittingPureTimeInheritedState_le_1296_finFour initial))

end GameTheory
