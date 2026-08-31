import MathUE.FiniteResponseCycleLedger
import UniformEquilibrium.Diagnostics.Quitting.PureTimeExactResponseMinimumAlternative

/-!
# Exact externality ledger for a four-player pure-clock response cycle

A literal horizontal response cycle has exact cross-cap cancellation.  Its
mover gains force a nonmover prescribed-payoff fall and a nonmover debt rise.
No temporal Nash--Bellman return or uniform equilibrium is constructed.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingPureTimeOffMinimumExactResponseCycle

/-- State at one offset of the closed response segment. -/
def state
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) :
    QuittingPureTimeInheritedState initial :=
  quittingPureTimeSelectedExactResponseOrbit reward initial
    (cycle.start + offset)

/-- Literal behavior profile at one offset of the response cycle. -/
def profile
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingPureTimeProfileBehavior reward (cycle.state offset).toProfile

/-- Selected exact-response step leaving one cycle offset. -/
noncomputable def step
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) :=
  quittingPureTimeSelectedExactResponseOrbitStep reward initial
    (cycle.start + offset)

/-- Mover on one edge of the response cycle. -/
noncomputable def mover
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) : ι :=
  (cycle.step offset).mover

/-- Prescribed terminal payoff along the response cycle. -/
def payoff
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) (who : ι) : ℝ :=
  quittingTerminalPayoff reward (cycle.profile offset) who

/-- Full behavioral cap along the response cycle. -/
def cap
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) (who : ι) : ℝ :=
  quittingContinuationBestResponseValue reward (cycle.profile offset) who

/-- Literal payoff gain of the mover on one response-cycle edge. -/
noncomputable def gain
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) : ℝ :=
  cycle.payoff (offset + 1) (cycle.mover offset) -
    cycle.payoff offset (cycle.mover offset)

/-- The selected edge's target is the next displayed cycle state. -/
theorem step_target_eq_state_succ
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) :
    (cycle.step offset).target = cycle.state (offset + 1) := by
  unfold step state
  rw [quittingPureTimeSelectedExactResponseOrbitStep_target_eq]
  simp only [Nat.add_assoc]

/-- The displayed response cycle closes literally as behavior profiles. -/
theorem profile_period_eq_zero
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) :
    cycle.profile cycle.period = cycle.profile 0 := by
  unfold profile state
  simpa using congrArg
    (fun state : QuittingPureTimeInheritedState initial =>
      quittingPureTimeProfileBehavior reward state.toProfile)
    cycle.closes

/-- The mover's behavioral cap is invariant on its own exact-response edge. -/
theorem cap_succ_mover_eq
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) :
    cycle.cap (offset + 1) (cycle.mover offset) =
      cycle.cap offset (cycle.mover offset) := by
  unfold cap profile mover
  rw [← cycle.step_target_eq_state_succ,
    (cycle.step offset).target_profile_eq_update,
    quittingPureTimeProfileBehavior_update,
    quittingContinuationBestResponseValue_update_self]
  rfl

/-- The exact cycle ledger: aggregate nonmover cap displacement cancels;
nonmover payoff change equals minus the mover's accumulated gain; and
nonmover debt change equals that accumulated gain. -/
theorem externality_ledger
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (observer : ι) :
    (∑ offset ∈ (Finset.range cycle.period).filter
        (fun offset => cycle.mover offset ≠ observer),
      (cycle.cap (offset + 1) observer - cycle.cap offset observer)) = 0 ∧
      (∑ offset ∈ (Finset.range cycle.period).filter
          (fun offset => cycle.mover offset ≠ observer),
        (cycle.payoff (offset + 1) observer -
          cycle.payoff offset observer)) =
        -(∑ offset ∈ (Finset.range cycle.period).filter
          (fun offset => cycle.mover offset = observer), cycle.gain offset) ∧
      (∑ offset ∈ (Finset.range cycle.period).filter
          (fun offset => cycle.mover offset ≠ observer),
        ((cycle.cap (offset + 1) observer -
            cycle.payoff (offset + 1) observer) -
          (cycle.cap offset observer - cycle.payoff offset observer))) =
        ∑ offset ∈ (Finset.range cycle.period).filter
          (fun offset => cycle.mover offset = observer), cycle.gain offset := by
  apply MathUE.FiniteResponseCycleLedger.closed_mover_externality_ledger
  · funext who
    simpa only [payoff] using congrArg
      (fun profile => quittingTerminalPayoff reward profile who)
      cycle.profile_period_eq_zero
  · funext who
    unfold cap
    rw [cycle.profile_period_eq_zero]
  · intro offset _
    exact cycle.cap_succ_mover_eq offset
  · intro offset _
    rfl

/-- Every displayed cycle edge gains at least the average global debt floor. -/
theorem averageDebt_le_gain
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt)
    (hlower : ∀ times : QuittingPureTimeProfile ι,
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times)
    (offset : ℕ) :
    minimumDebt / Fintype.card ι ≤ cycle.gain offset := by
  simp only [gain, payoff, profile, mover, step, state]
  exact
    quittingPureTimeSelectedExactResponseOrbitStep_gain_ge_averageDebt
      reward initial minimumDebt hlower (cycle.start + offset)

/-- In a four-player positive-debt response cycle, some nonmover loses at
least one twelfth of the debt floor in prescribed payoff, and some (possibly
different) nonmover gains at least one twelfth in terminal debt. -/
theorem exists_nonmover_payoffFall_and_debtRise_ge_twelfth_finFour
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {initial : QuittingPureTimeProfile (Fin 4)} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt)
    (hlower : ∀ times : QuittingPureTimeProfile (Fin 4),
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times) :
    (∃ offset < cycle.period, ∃ observer,
      observer ≠ cycle.mover offset ∧
      minimumDebt / 12 ≤
        cycle.payoff offset observer - cycle.payoff (offset + 1) observer) ∧
      ∃ offset < cycle.period, ∃ observer,
        observer ≠ cycle.mover offset ∧
        minimumDebt / 12 ≤
          (cycle.cap (offset + 1) observer -
              cycle.payoff (offset + 1) observer) -
            (cycle.cap offset observer - cycle.payoff offset observer) := by
  let indexSet : Finset (Sigma fun _ : Fin 4 => ℕ) :=
    Finset.univ.sigma fun observer =>
      (Finset.range cycle.period).filter
        (fun offset => cycle.mover offset ≠ observer)
  let payoffFall : (Sigma fun _ : Fin 4 => ℕ) → ℝ := fun index =>
    cycle.payoff index.2 index.1 - cycle.payoff (index.2 + 1) index.1
  let debtRise : (Sigma fun _ : Fin 4 => ℕ) → ℝ := fun index =>
    (cycle.cap (index.2 + 1) index.1 -
        cycle.payoff (index.2 + 1) index.1) -
      (cycle.cap index.2 index.1 - cycle.payoff index.2 index.1)
  have hindexNonempty : indexSet.Nonempty := by
    let moved := cycle.mover 0
    let observer : Fin 4 := if moved = 0 then 1 else 0
    have hobserver : observer ≠ moved := by
      dsimp only [observer]
      split_ifs with heq
      · intro hone
        have : (1 : Fin 4) = 0 := hone.trans heq
        norm_num at this
      · simpa only [ne_eq, eq_comm] using heq
    refine ⟨⟨observer, 0⟩, ?_⟩
    simp only [indexSet, Finset.mem_sigma, Finset.mem_univ, true_and,
      Finset.mem_filter, Finset.mem_range]
    exact ⟨cycle.period_pos, by simpa only [moved] using hobserver.symm⟩
  have hindexCard : indexSet.card = 3 * cycle.period := by
    dsimp only [indexSet]
    rw [Finset.card_sigma]
    calc
      (∑ observer ∈ (Finset.univ : Finset (Fin 4)),
          ((Finset.range cycle.period).filter
            (fun offset => cycle.mover offset ≠ observer)).card) =
          ∑ observer ∈ (Finset.univ : Finset (Fin 4)),
            ∑ offset ∈ Finset.range cycle.period,
              if cycle.mover offset ≠ observer then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro observer _
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ offset ∈ Finset.range cycle.period,
          ∑ observer ∈ (Finset.univ : Finset (Fin 4)),
            if cycle.mover offset ≠ observer then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ _offset ∈ Finset.range cycle.period, 3 := by
        apply Finset.sum_congr rfl
        intro offset _
        rw [← Finset.sum_filter]
        rw [show (Finset.univ : Finset (Fin 4)).filter
            (fun observer => cycle.mover offset ≠ observer) =
            Finset.univ.erase (cycle.mover offset) by
          ext observer
          simp [ne_comm]]
        simp
      _ = 3 * cycle.period := by simp [mul_comm]
  have hpayoffFallSum :
      (∑ index ∈ indexSet, payoffFall index) =
        ∑ offset ∈ Finset.range cycle.period, cycle.gain offset := by
    rw [show (∑ index ∈ indexSet, payoffFall index) =
        ∑ observer ∈ (Finset.univ : Finset (Fin 4)),
          ∑ offset ∈ (Finset.range cycle.period).filter
            (fun offset => cycle.mover offset ≠ observer),
            payoffFall ⟨observer, offset⟩ by
      exact Finset.sum_sigma _ _ payoffFall]
    calc
      (∑ observer ∈ (Finset.univ : Finset (Fin 4)),
          ∑ offset ∈ (Finset.range cycle.period).filter
            (fun offset => cycle.mover offset ≠ observer),
            payoffFall ⟨observer, offset⟩) =
          ∑ observer ∈ (Finset.univ : Finset (Fin 4)),
            ∑ offset ∈ (Finset.range cycle.period).filter
              (fun offset => cycle.mover offset = observer),
              cycle.gain offset := by
        apply Finset.sum_congr rfl
        intro observer _
        have hledger := (cycle.externality_ledger observer).2.1
        dsimp only [payoffFall]
        calc
          (∑ offset ∈ (Finset.range cycle.period).filter
              (fun offset => cycle.mover offset ≠ observer),
              (cycle.payoff offset observer -
                cycle.payoff (offset + 1) observer)) =
              -(∑ offset ∈ (Finset.range cycle.period).filter
                (fun offset => cycle.mover offset ≠ observer),
                (cycle.payoff (offset + 1) observer -
                  cycle.payoff offset observer)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro offset _
            ring
          _ = _ := by rw [hledger]; ring
      _ = ∑ offset ∈ Finset.range cycle.period, cycle.gain offset := by
        simp_rw [Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro offset _
        simp
  have hdebtRiseSum :
      (∑ index ∈ indexSet, debtRise index) =
        ∑ offset ∈ Finset.range cycle.period, cycle.gain offset := by
    rw [show (∑ index ∈ indexSet, debtRise index) =
        ∑ observer ∈ (Finset.univ : Finset (Fin 4)),
          ∑ offset ∈ (Finset.range cycle.period).filter
            (fun offset => cycle.mover offset ≠ observer),
            debtRise ⟨observer, offset⟩ by
      exact Finset.sum_sigma _ _ debtRise]
    calc
      (∑ observer ∈ (Finset.univ : Finset (Fin 4)),
          ∑ offset ∈ (Finset.range cycle.period).filter
            (fun offset => cycle.mover offset ≠ observer),
            debtRise ⟨observer, offset⟩) =
          ∑ observer ∈ (Finset.univ : Finset (Fin 4)),
            ∑ offset ∈ (Finset.range cycle.period).filter
              (fun offset => cycle.mover offset = observer),
              cycle.gain offset := by
        apply Finset.sum_congr rfl
        intro observer _
        exact (cycle.externality_ledger observer).2.2
      _ = ∑ offset ∈ Finset.range cycle.period, cycle.gain offset := by
        simp_rw [Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro offset _
        simp
  have hgainSum : (cycle.period : ℝ) * (minimumDebt / 4) ≤
      ∑ offset ∈ Finset.range cycle.period, cycle.gain offset := by
    calc
      (cycle.period : ℝ) * (minimumDebt / 4) =
          ∑ _offset ∈ Finset.range cycle.period, minimumDebt / 4 := by
        simp [nsmul_eq_mul]
      _ ≤ ∑ offset ∈ Finset.range cycle.period, cycle.gain offset := by
        exact Finset.sum_le_sum fun offset _ => by
          simpa using cycle.averageDebt_le_gain hlower offset
  have hcardThreshold : (indexSet.card : ℝ) * (minimumDebt / 12) ≤
      ∑ index ∈ indexSet, payoffFall index := by
    rw [hpayoffFallSum]
    rw [hindexCard]
    norm_num
    nlinarith
  have hcardThresholdDebt : (indexSet.card : ℝ) * (minimumDebt / 12) ≤
      ∑ index ∈ indexSet, debtRise index := by
    rw [hdebtRiseSum]
    rw [hindexCard]
    norm_num
    nlinarith
  obtain ⟨payoffIndex, hpayoffIndex, hpayoffFall⟩ :=
    MathUE.FiniteResponseCycleLedger.exists_mem_value_ge_of_card_mul_le_sum
      indexSet hindexNonempty payoffFall (minimumDebt / 12) hcardThreshold
  obtain ⟨debtIndex, hdebtIndex, hdebtRise⟩ :=
    MathUE.FiniteResponseCycleLedger.exists_mem_value_ge_of_card_mul_le_sum
      indexSet hindexNonempty debtRise (minimumDebt / 12) hcardThresholdDebt
  have hpayoffMem := Finset.mem_sigma.mp hpayoffIndex
  have hdebtMem := Finset.mem_sigma.mp hdebtIndex
  constructor
  · refine ⟨payoffIndex.2,
      Finset.mem_range.mp (Finset.mem_filter.mp hpayoffMem.2).1,
      payoffIndex.1, ?_, hpayoffFall⟩
    exact (Finset.mem_filter.mp hpayoffMem.2).2.symm
  · refine ⟨debtIndex.2,
      Finset.mem_range.mp (Finset.mem_filter.mp hdebtMem.2).1,
      debtIndex.1, ?_, hdebtRise⟩
    exact (Finset.mem_filter.mp hdebtMem.2).2.symm

end QuittingPureTimeOffMinimumExactResponseCycle

end GameTheory
