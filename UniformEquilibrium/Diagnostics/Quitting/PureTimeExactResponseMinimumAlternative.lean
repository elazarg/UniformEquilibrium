import UniformEquilibrium.Diagnostics.Quitting.PureTimeSelectedExactResponseOrbit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement

/-!
# Minimum entrance or an off-minimum pure-clock response cycle

The selected horizontal response orbit either first reaches the minimum-debt
face or contains a bounded closed segment entirely above it.  Every edge has
a fresh paid first-disagreement row.  This does not make the response orbit a
temporal Nash--Bellman path.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every selected exact-response edge with a positive debt floor has a fresh
pure-time first-disagreement row carrying the average debt gain. -/
theorem exists_paidFirstDisagreementRow_selectedExactResponseOrbitStep
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (minimumDebt : ℝ)
    (hpositive : 0 < minimumDebt)
    (hlower : ∀ times : QuittingPureTimeProfile ι,
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times)
    (time : ℕ) :
    ∃ row : QuittingPaidFirstDisagreementRow reward
        (quittingPureTimeProfileBehavior reward
          (quittingPureTimeSelectedExactResponseOrbit reward initial
            time).toProfile)
        (quittingPureTimeSelectedExactResponseOrbitStep
          reward initial time).mover
        (minimumDebt / Fintype.card ι),
      row.sourceWitness =
          (quittingPureTimeSelectedExactResponseOrbit reward initial
            time).toProfile
            (quittingPureTimeSelectedExactResponseOrbitStep
              reward initial time).mover ∧
        row.receivingWitness =
          (quittingPureTimeSelectedExactResponseOrbitStep
            reward initial time).response := by
  let source := quittingPureTimeSelectedExactResponseOrbit reward initial time
  let step := quittingPureTimeSelectedExactResponseOrbitStep
    reward initial time
  let profile := quittingPureTimeProfileBehavior reward source.toProfile
  have hsourcePayoff :
      quittingPureTimeDeviationPayoff reward profile step.mover
          (source.toProfile step.mover) =
        quittingTerminalPayoff reward profile step.mover := by
    unfold quittingPureTimeDeviationPayoff
    rw [← quittingPureTimeProfileBehavior_update]
    rw [Function.update_eq_self]
  have hresponsePayoff :
      quittingPureTimeDeviationPayoff reward profile step.mover step.response =
        quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward step.target.toProfile)
          step.mover := by
    unfold quittingPureTimeDeviationPayoff
    rw [step.target_profile_eq_update,
      quittingPureTimeProfileBehavior_update]
  have hgain : minimumDebt / Fintype.card ι ≤
      quittingPureTimeDeviationPayoff reward profile step.mover step.response -
        quittingPureTimeDeviationPayoff reward profile step.mover
          (source.toProfile step.mover) := by
    rw [hresponsePayoff, hsourcePayoff]
    exact quittingPureTimeSelectedExactResponseOrbitStep_gain_ge_averageDebt
      reward initial minimumDebt hlower time
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  have hgainPositive : 0 < minimumDebt / Fintype.card ι :=
    div_pos hpositive hcard
  simpa only [source, step, profile] using
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
      reward profile step.mover (source.toProfile step.mover) step.response
        (minimumDebt / Fintype.card ι) hgainPositive hgain

/-- A first visit to the minimum-debt face along the selected horizontal
response orbit. -/
structure QuittingPureTimeMinimumDebtEntrance
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (minimumDebt : ℝ) where
  time : ℕ
  time_pos : 0 < time
  time_le_stateCard : time ≤
    Fintype.card (QuittingPureTimeInheritedState initial)
  at_minimum : quittingPureTimeTerminalSemanticDebtSum reward
      (quittingPureTimeSelectedExactResponseOrbit reward initial time).toProfile =
    minimumDebt
  strict_before : ∀ earlier < time,
    minimumDebt < quittingPureTimeTerminalSemanticDebtSum reward
      (quittingPureTimeSelectedExactResponseOrbit reward initial earlier).toProfile
  target_mover_debt_eq_zero : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingPureTimeProfileBehavior reward
          (quittingPureTimeSelectedExactResponseOrbit reward initial time).toProfile))
      (quittingPureTimeSelectedExactResponseOrbitStep reward initial
        (time - 1)).mover = 0

namespace QuittingPureTimeMinimumDebtEntrance

/-- The edge entering the first minimum state starts strictly off minimum. -/
theorem before_minimum
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (entrance : QuittingPureTimeMinimumDebtEntrance
      reward initial minimumDebt) :
    minimumDebt < quittingPureTimeTerminalSemanticDebtSum reward
      (quittingPureTimeSelectedExactResponseOrbit reward initial
        (entrance.time - 1)).toProfile := by
  have hpos : 0 < entrance.time := entrance.time_pos
  exact entrance.strict_before _ (by omega)

end QuittingPureTimeMinimumDebtEntrance

/-- A positive closed segment of the selected response orbit which stays
strictly above the minimum-debt face. -/
structure QuittingPureTimeOffMinimumExactResponseCycle
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (minimumDebt : ℝ) where
  start : ℕ
  period : ℕ
  two_le_period : 2 ≤ period
  end_le_stateCard : start + period ≤
    Fintype.card (QuittingPureTimeInheritedState initial)
  closes : quittingPureTimeSelectedExactResponseOrbit reward initial
      (start + period) =
    quittingPureTimeSelectedExactResponseOrbit reward initial start
  offMinimum_through_stateCard : ∀ time ≤
      Fintype.card (QuittingPureTimeInheritedState initial),
    minimumDebt < quittingPureTimeTerminalSemanticDebtSum reward
      (quittingPureTimeSelectedExactResponseOrbit reward initial time).toProfile

namespace QuittingPureTimeOffMinimumExactResponseCycle

/-- The nontrivial cycle has positive period. -/
theorem period_pos
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) :
    0 < cycle.period := by
  have htwo : 2 ≤ cycle.period := cycle.two_le_period
  omega

/-- Every orbit state through the closing endpoint stays strictly above the
minimum-debt face. -/
theorem offMinimum_before_end
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (time : ℕ)
    (htime : time ≤ cycle.start + cycle.period) :
    minimumDebt < quittingPureTimeTerminalSemanticDebtSum reward
      (quittingPureTimeSelectedExactResponseOrbit reward initial time).toProfile := by
  exact cycle.offMinimum_through_stateCard time
    (htime.trans cycle.end_le_stateCard)

/-- Every displayed state of the literal cycle is strictly above the
minimum-debt face. -/
theorem offMinimum
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {initial : QuittingPureTimeProfile ι} {minimumDebt : ℝ}
    (cycle : QuittingPureTimeOffMinimumExactResponseCycle
      reward initial minimumDebt) (offset : ℕ) (hoffset : offset ≤ cycle.period) :
    minimumDebt < quittingPureTimeTerminalSemanticDebtSum reward
      (quittingPureTimeSelectedExactResponseOrbit reward initial
        (cycle.start + offset)).toProfile := by
  exact cycle.offMinimum_before_end _ (Nat.add_le_add_left hoffset cycle.start)

end QuittingPureTimeOffMinimumExactResponseCycle

/-- Starting strictly above a global pure-profile debt floor, the selected
exact-response orbit either first reaches the floor or closes a positive
cycle entirely above it. -/
theorem exists_minimumDebtEntrance_or_offMinimumExactResponseCycle
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (minimumDebt : ℝ)
    (hpositive : 0 < minimumDebt)
    (hlower : ∀ times : QuittingPureTimeProfile ι,
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times)
    (hoffInitial : minimumDebt <
      quittingPureTimeTerminalSemanticDebtSum reward initial) :
    Nonempty (QuittingPureTimeMinimumDebtEntrance reward initial minimumDebt) ∨
      Nonempty (QuittingPureTimeOffMinimumExactResponseCycle
        reward initial minimumDebt) := by
  let orbit := quittingPureTimeSelectedExactResponseOrbit reward initial
  let atMinimum : QuittingPureTimeInheritedState initial → Prop := fun state =>
    quittingPureTimeTerminalSemanticDebtSum reward state.toProfile = minimumDebt
  rcases Math.exists_output_or_repeated_finitePivotOrbit
      (quittingPureTimeSelectedExactResponseSuccessor reward initial)
      atMinimum (quittingPureTimeInitialInheritedState initial) with
    hhit | hrepeat
  · obtain ⟨boundedTime, hboundedHit⟩ := hhit
    have hexists : ∃ time : ℕ,
        quittingPureTimeTerminalSemanticDebtSum reward
            (orbit time).toProfile = minimumDebt := by
      exact ⟨boundedTime, hboundedHit⟩
    let entrance := Nat.find hexists
    have hentrance := Nat.find_spec hexists
    have hentrancePos : 0 < entrance := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have hinitial : quittingPureTimeTerminalSemanticDebtSum reward initial =
          minimumDebt := by
        simpa only [entrance, hzero, orbit,
          quittingPureTimeSelectedExactResponseOrbit_zero,
          quittingPureTimeInitialInheritedState_toProfile] using hentrance
      linarith
    have hentranceLe : entrance ≤ boundedTime :=
      Nat.find_min' hexists hboundedHit
    refine Or.inl ⟨{
      time := entrance
      time_pos := hentrancePos
      time_le_stateCard := ?_
      at_minimum := hentrance
      strict_before := ?_
      target_mover_debt_eq_zero := ?_
    }⟩
    · exact hentranceLe.trans (by omega)
    · intro earlier hearlier
      have hne : quittingPureTimeTerminalSemanticDebtSum reward
          (orbit earlier).toProfile ≠ minimumDebt :=
        Nat.find_min hexists hearlier
      exact lt_of_le_of_ne (hlower (orbit earlier).toProfile) (Ne.symm hne)
    · have hsucc : entrance - 1 + 1 = entrance := by omega
      simpa only [orbit, hsucc] using
        quittingPureTimeSelectedExactResponseOrbitStep_target_mover_debt_eq_zero
          reward initial (entrance - 1)
  · obtain ⟨first, second, hfirstSecond, hclose, hnoMinimum⟩ := hrepeat
    let period := (second : ℕ) - (first : ℕ)
    have hperiodPos : 0 < period := by
      dsimp only [period]
      omega
    have hend : (first : ℕ) + period = second := by
      dsimp only [period]
      omega
    refine Or.inr ⟨{
      start := first
      period := period
      two_le_period := ?_
      end_le_stateCard := by omega
      closes := ?_
      offMinimum_through_stateCard := ?_
    }⟩
    · by_contra hnot
      have hperiodOne : period = 1 := by omega
      have hfixed :
          (quittingPureTimeSelectedExactResponseOrbitStep
            reward initial first).target =
            quittingPureTimeSelectedExactResponseOrbit reward initial first := by
        rw [quittingPureTimeSelectedExactResponseOrbitStep_target_eq]
        have hnextEnd : (first : ℕ) + 1 = (second : ℕ) := by omega
        rw [hnextEnd]
        exact hclose.symm
      exact quittingPureTimeSelectedExactResponseOrbitStep_target_ne_source
        reward initial minimumDebt hpositive hlower first hfixed
    · rw [hend]
      exact hclose.symm
    · intro time htime
      let time : Fin (Fintype.card
          (QuittingPureTimeInheritedState initial) + 1) :=
        ⟨time, by omega⟩
      have hne : quittingPureTimeTerminalSemanticDebtSum reward
          (orbit time).toProfile ≠ minimumDebt := hnoMinimum time
      exact lt_of_le_of_ne (hlower (orbit time).toProfile) (Ne.symm hne)

/-- A first minimum entrance and an orbit which stays off minimum through the
finite state bound cannot coexist. -/
theorem not_both_minimumDebtEntrance_and_offMinimumExactResponseCycle
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (minimumDebt : ℝ) :
    ¬(Nonempty (QuittingPureTimeMinimumDebtEntrance
        reward initial minimumDebt) ∧
      Nonempty (QuittingPureTimeOffMinimumExactResponseCycle
        reward initial minimumDebt)) := by
  rintro ⟨⟨entrance⟩, ⟨cycle⟩⟩
  have hstrict := cycle.offMinimum_through_stateCard
    entrance.time entrance.time_le_stateCard
  rw [entrance.at_minimum] at hstrict
  exact (lt_irrefl minimumDebt) hstrict

/-- Starting strictly above a positive global debt floor, exactly one of a
first minimum entrance and an entirely off-minimum pre-repeat cycle exists. -/
theorem exists_minimumDebtEntrance_xor_offMinimumExactResponseCycle
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial : QuittingPureTimeProfile ι) (minimumDebt : ℝ)
    (hpositive : 0 < minimumDebt)
    (hlower : ∀ times : QuittingPureTimeProfile ι,
      minimumDebt ≤ quittingPureTimeTerminalSemanticDebtSum reward times)
    (hoffInitial : minimumDebt <
      quittingPureTimeTerminalSemanticDebtSum reward initial) :
    Xor (Nonempty (QuittingPureTimeMinimumDebtEntrance
        reward initial minimumDebt))
      (Nonempty (QuittingPureTimeOffMinimumExactResponseCycle
        reward initial minimumDebt)) := by
  rw [xor_def]
  rcases exists_minimumDebtEntrance_or_offMinimumExactResponseCycle
      reward initial minimumDebt hpositive hlower hoffInitial with
    hentrance | hcycle
  · exact Or.inl ⟨hentrance, fun hcycle =>
      not_both_minimumDebtEntrance_and_offMinimumExactResponseCycle
        reward initial minimumDebt ⟨hentrance, hcycle⟩⟩
  · exact Or.inr ⟨hcycle, fun hentrance =>
      not_both_minimumDebtEntrance_and_offMinimumExactResponseCycle
        reward initial minimumDebt ⟨hentrance, hcycle⟩⟩

end GameTheory
