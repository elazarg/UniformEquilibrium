/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicBlockerBarrier
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicBlockerResetAdapter
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticBoundedSelfReset
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticReachedRowDebtLocalization

/-!
# Bounded self-reset localization of a quitting counterexample

The terminal exploitability gap of a quitting counterexample is a uniform
coordinate-debt floor on every actual behavioral profile.  Applying bounded
pure-time self-reset to an arbitrary sequence of starting profiles produces,
after one finite-label extraction, a fixed final pure-time player and a fixed
nonempty terminal coalition of uniformly positive mass.

If the final player belongs to that coalition, the sign-free reached-row debt
inequality gives one fixed other player's legal actual-row gain along a strict
subsequence.  If the final player is absent, the terminal mass lies entirely
on the finite pre-stop clock and the atomic-blocker theorem gives a forced-owner
wall on every row of that clock.

This construction uses neither a stopping-law frontier nor a reward sign.  It
retains the bounded executable self-reset chain from every supplied starting
profile.
-/

noncomputable section

namespace GameTheory

open Filter Finset Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Canonical vanishing error used by the counterexample self-reset sequence. -/
def quittingCounterexampleSelfResetAccuracy
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) (rank : ℕ) : ℝ :=
  (regime.terminalGap / 2) * (1 / (rank + 1 : ℝ))

theorem quittingCounterexampleSelfResetAccuracy_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) (rank : ℕ) :
    0 < quittingCounterexampleSelfResetAccuracy regime rank := by
  unfold quittingCounterexampleSelfResetAccuracy
  exact mul_pos (half_pos regime.terminalGap_pos)
    (one_div_pos.mpr (by positivity))

theorem quittingCounterexampleSelfResetAccuracy_lt_terminalGap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) (rank : ℕ) :
    quittingCounterexampleSelfResetAccuracy regime rank < regime.terminalGap := by
  have hinv : (1 / (rank + 1 : ℝ)) ≤ 1 := by
    have hrank : (0 : ℝ) ≤ rank := by positivity
    simpa only [one_div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (by linarith : (1 : ℝ) ≤ rank + 1)
  have hhalf : regime.terminalGap / 2 < regime.terminalGap := by
    linarith [regime.terminalGap_pos]
  calc
    quittingCounterexampleSelfResetAccuracy regime rank ≤
        regime.terminalGap / 2 := by
      unfold quittingCounterexampleSelfResetAccuracy
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hinv (half_pos regime.terminalGap_pos).le
    _ < regime.terminalGap := hhalf

theorem tendsto_quittingCounterexampleSelfResetAccuracy_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    Tendsto (quittingCounterexampleSelfResetAccuracy regime) atTop (nhds 0) := by
  have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  change Tendsto (fun rank : ℕ =>
    (regime.terminalGap / 2) * (1 / (rank + 1 : ℝ))) atTop (nhds 0)
  simpa only [one_div, mul_zero] using
    hzero.const_mul (regime.terminalGap / 2)

/-- The counterexample terminal gap is the generic uniform coordinate-debt
floor required by bounded self-reset. -/
theorem QuittingCounterexampleRegime.hasUniformTerminalDebtFloor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    HasQuittingUniformTerminalDebtFloor reward regime.terminalGap := by
  intro profile
  exact regime.exists_terminalGap_le_terminalSemanticDebt reward profile

/-- Optimal uniform mass floor obtained by pigeonholing among nonempty
terminal coalitions after the final finite pure-time reset. -/
def quittingBoundedSelfResetTerminalMassFloor (ι : Type) [Fintype ι] : ℝ :=
  1 / (Fintype.card {S : Finset ι // S.Nonempty} : ℝ)

omit [DecidableEq ι] in
theorem quittingBoundedSelfResetTerminalMassFloor_pos
    (who : ι) :
    0 < quittingBoundedSelfResetTerminalMassFloor ι := by
  unfold quittingBoundedSelfResetTerminalMassFloor
  have hnonempty : Nonempty {S : Finset ι // S.Nonempty} :=
    ⟨⟨{who}, Finset.singleton_nonempty who⟩⟩
  letI := hnonempty
  positivity

/-- A fixed-label subsequence of bounded self-reset endpoints.  Every endpoint
retains its complete executable chain from the corresponding supplied start,
has the same final pure-time player and terminal coalition, and carries the
sharp finite-simplex terminal mass floor. -/
structure QuittingBoundedSelfResetTerminalSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    (starts : ℕ → (quittingGame reward).BehaviorProfile) where
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  length : ℕ → ℕ
  profile : ℕ → (quittingGame reward).BehaviorProfile
  observer : ι
  stop : ℕ → ℕ
  terminal : {S : Finset ι // S.Nonempty}
  chain : ∀ rank,
    QuittingPureTimeSelfResetChain reward regime.terminalGap
      (quittingCounterexampleSelfResetAccuracy regime (subseq rank))
      (starts (subseq rank)) (length rank) (profile rank) observer (stop rank)
  length_le : ∀ rank, length rank ≤ Fintype.card ι + 1
  terminal_mass_lower : ∀ rank,
    quittingBoundedSelfResetTerminalMassFloor ι ≤
      quittingTerminalOutcomeMass reward (profile rank) (some terminal)

namespace QuittingBoundedSelfResetTerminalSequence

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}
variable {starts : ℕ → (quittingGame reward).BehaviorProfile}

/-- The final observer literally uses the displayed finite pure-time strategy
at every endpoint. -/
theorem observer_strategy
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts)
    (rank : ℕ) :
    sequence.profile rank sequence.observer =
      quittingPureTimeBehaviorStrategy reward sequence.observer
        (some (sequence.stop rank)) :=
  (sequence.chain rank).final_player_strategy

/-- The final observer's initial semantic debt converges to zero. -/
theorem observer_debt_tendsto_zero
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts) :
    Tendsto (fun rank => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sequence.profile rank))
        sequence.observer) atTop (nhds 0) := by
  apply squeeze_zero'
  · apply Eventually.of_forall
    intro rank
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingTerminalSemanticPair_mem_carrier reward _) sequence.observer
  · apply Eventually.of_forall
    intro rank
    exact (sequence.chain rank).final_debt_le_error
  · exact (tendsto_quittingCounterexampleSelfResetAccuracy_zero regime).comp
      sequence.subseq_strictMono.tendsto_atTop

/-- Every current suffix semantic pair remains above the counterexample's
terminal gap in total debt. -/
theorem terminalGap_le_suffix_debtSum
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts)
    (rank stage : ℕ) :
    regime.terminalGap ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (sequence.profile rank)
          stage)) := by
  let suffix := quittingAllContinueProfileSpine reward
    (sequence.profile rank) stage
  obtain ⟨who, hwho⟩ :=
    regime.exists_terminalGap_le_terminalSemanticDebt reward suffix
  calc
    regime.terminalGap ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward suffix) who := hwho
    _ ≤ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward suffix) := by
      unfold quittingTerminalSemanticDebtSum
      exact Finset.single_le_sum
        (fun other _ => quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward (quittingTerminalSemanticPair_mem_carrier reward suffix) other)
        (Finset.mem_univ who)

end QuittingBoundedSelfResetTerminalSequence

/-- Every sequence of starting profiles admits a fixed-label bounded
self-reset terminal sequence. -/
theorem QuittingCounterexampleRegime.exists_boundedSelfResetTerminalSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    (starts : ℕ → (quittingGame reward).BehaviorProfile) :
    Nonempty (QuittingBoundedSelfResetTerminalSequence regime starts) := by
  letI : Nonempty ι := regime.nonempty_players
  have hexit : ∀ rank, ∃ (length : ℕ)
      (profile : (quittingGame reward).BehaviorProfile)
      (observer : ι) (stop : ℕ),
      QuittingPureTimeSelfResetChain reward regime.terminalGap
          (quittingCounterexampleSelfResetAccuracy regime rank)
          (starts rank) length profile observer stop ∧
        length ≤ Fintype.card ι + 1 := by
    intro rank
    exact exists_bounded_quittingPureTimeSelfResetChain reward
      regime.terminalGap (quittingCounterexampleSelfResetAccuracy regime rank)
      regime.hasUniformTerminalDebtFloor
      (quittingCounterexampleSelfResetAccuracy_pos regime rank)
      (quittingCounterexampleSelfResetAccuracy_lt_terminalGap regime rank)
      (starts rank)
  choose length profile observer stop chain hlength using hexit
  have hterminal : ∀ rank, ∃ terminal : {S : Finset ι // S.Nonempty},
      quittingBoundedSelfResetTerminalMassFloor ι ≤
        quittingTerminalOutcomeMass reward (profile rank) (some terminal) := by
    intro rank
    exact exists_terminal_mass_ge_inv_card_of_pureTimePlayer reward
      (profile rank) (observer rank) (stop rank)
      ((chain rank).final_player_strategy)
  choose terminal hmass using hterminal
  let label : ℕ → ι × {S : Finset ι // S.Nonempty} := fun rank =>
    (observer rank, terminal rank)
  have hfrequent : ∃ᶠ rank in atTop,
      ∃ fixed ∈ (Finset.univ : Finset (ι × {S : Finset ι // S.Nonempty})),
        label rank = fixed := by
    exact Frequently.of_forall fun rank =>
      ⟨label rank, Finset.mem_univ _, rfl⟩
  rw [Finset.frequently_exists] at hfrequent
  obtain ⟨fixed, _hfixed, hfixedFrequent⟩ := hfrequent
  obtain ⟨subseq, hsubseq, hlabel⟩ :=
    extraction_of_frequently_atTop hfixedFrequent
  refine ⟨{
    subseq := subseq
    subseq_strictMono := hsubseq
    length := fun rank => length (subseq rank)
    profile := fun rank => profile (subseq rank)
    observer := fixed.1
    stop := fun rank => stop (subseq rank)
    terminal := fixed.2
    chain := ?_
    length_le := ?_
    terminal_mass_lower := ?_
  }⟩
  · intro rank
    have hfixedEq := hlabel rank
    have hobserver : observer (subseq rank) = fixed.1 :=
      congr_arg Prod.fst hfixedEq
    simpa only [hobserver] using chain (subseq rank)
  · intro rank
    exact hlength (subseq rank)
  · intro rank
    have hfixedEq := hlabel rank
    have hterminalEq : terminal (subseq rank) = fixed.2 :=
      congr_arg Prod.snd hfixedEq
    simpa only [hterminalEq] using hmass (subseq rank)

/-! ## Sign-free reached-row endpoint -/

/-- Quantitative target-row output of a bounded self-reset terminal sequence.
It retains a further strict subsequence and the exact canonical legal gain
floor. -/
structure QuittingBoundedSelfResetTargetRowLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts) where
  observer_mem : sequence.observer ∈ sequence.terminal.val
  other : ι
  other_ne : other ≠ sequence.observer
  gainSubseq : ℕ → ℕ
  gainSubseq_strictMono : StrictMono gainSubseq
  gain_lower : ∀ rank,
    quittingBoundedSelfResetTerminalMassFloor ι * regime.terminalGap /
          (2 * ((Finset.univ.erase sequence.observer).card : ℝ)) ≤
      quittingTerminalPayoff reward
          (Function.update (sequence.profile (gainSubseq rank)) other
            (quittingStagePureEndpointBehaviorDeviation reward
              (sequence.profile (gainSubseq rank)) other
              (sequence.stop (gainSubseq rank))
              (quittingRootBestEndpointAction reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward
                    (sequence.profile (gainSubseq rank))
                    (sequence.stop (gainSubseq rank) + 1))).1
                (quittingProfileLiveRoot reward
                  (sequence.profile (gainSubseq rank))
                  (sequence.stop (gainSubseq rank))) other))) other -
        quittingTerminalPayoff reward
          (sequence.profile (gainSubseq rank)) other

theorem QuittingBoundedSelfResetTerminalSequence.targetRowLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts)
    (hmem : sequence.observer ∈ sequence.terminal.val) :
    Nonempty (QuittingBoundedSelfResetTargetRowLocalization sequence) := by
  let reachFloor := quittingBoundedSelfResetTerminalMassFloor ι
  have hreachFloor : 0 < reachFloor :=
    quittingBoundedSelfResetTerminalMassFloor_pos sequence.observer
  have hstageMass : ∀ rank, reachFloor ≤
      quittingStageCoalitionMass reward (sequence.profile rank)
        (sequence.stop rank) sequence.terminal := by
    intro rank
    obtain ⟨predecessor, hprofile⟩ :=
      (sequence.chain rank).exists_final_predecessor
    rw [hprofile]
    rw [← quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward predecessor sequence.observer (sequence.stop rank)
      sequence.terminal hmem]
    simpa only [hprofile] using sequence.terminal_mass_lower rank
  have hreach : ∀ rank, reachFloor ≤
      quittingLiveMass reward (sequence.profile rank) (sequence.stop rank) := by
    intro rank
    exact (hstageMass rank).trans
      (quittingStageCoalitionMass_le_liveMass reward (sequence.profile rank)
        (sequence.stop rank) sequence.terminal)
  have hsure : ∀ rank,
      quittingProfileLiveRoot reward (sequence.profile rank)
          (sequence.stop rank) sequence.observer = PMF.pure true := by
    intro rank
    obtain ⟨predecessor, hprofile⟩ :=
      (sequence.chain rank).exists_final_predecessor
    rw [hprofile, quittingProfileLiveRoot_update_pureTime_self,
      quittingPureTimeHazard_some_self]
  obtain ⟨other, gainSubseq, hother, hgainSubseq, hgain⟩ :=
    exists_fixed_other_reachedRowGain_subsequence reward regime.terminalGap
      regime.terminalGap_pos sequence.profile sequence.stop sequence.observer
      reachFloor (fun rank => sequence.terminalGap_le_suffix_debtSum rank _)
      hreachFloor hreach hsure sequence.observer_debt_tendsto_zero
  exact ⟨{
    observer_mem := hmem
    other := other
    other_ne := hother
    gainSubseq := gainSubseq
    gainSubseq_strictMono := hgainSubseq
    gain_lower := hgain
  }⟩

/-! ## Finite-clock observer-absent endpoint -/

/-- A fixed member of the terminal coalition selected at the self-reset
endpoint. -/
def quittingBoundedSelfResetObserverAbsentOwner
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts) : ι :=
  sequence.terminal.property.choose

theorem quittingBoundedSelfResetObserverAbsentOwner_mem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts) :
    quittingBoundedSelfResetObserverAbsentOwner sequence ∈
      sequence.terminal.val :=
  sequence.terminal.property.choose_spec

/-- Literal one-row profile obtained by forcing the selected terminal owner
to Quit at an actual pre-observer-stop row. -/
def quittingBoundedSelfResetForcedOwnerProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts)
    (rank time : ℕ) : (quittingGame reward).BehaviorProfile :=
  let owner := quittingBoundedSelfResetObserverAbsentOwner sequence
  Function.update (sequence.profile rank) owner
    (quittingStagePureEndpointBehaviorDeviation reward
      (sequence.profile rank) owner time true)

/-- The counterexample atomic barrier at one forced-owner row of a bounded
self-reset endpoint. -/
def quittingBoundedSelfResetRowBarrier
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts)
    (rank time : ℕ) : ℝ :=
  let owner := quittingBoundedSelfResetObserverAbsentOwner sequence
  let root := Function.update
    (quittingProfileLiveRoot reward (sequence.profile rank) time)
    owner (PMF.pure true)
  max (quittingForcedOwnerOutsiderDefect reward root owner)
    (max 0 (-quittingAtomicBlockerBalance reward root owner))

/-- The one-row forced profile has exactly the corresponding forced product
root. -/
theorem quittingProfileLiveRoot_boundedSelfResetForcedOwnerProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts)
    (rank time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingBoundedSelfResetForcedOwnerProfile sequence rank time) time =
      Function.update
        (quittingProfileLiveRoot reward (sequence.profile rank) time)
        (quittingBoundedSelfResetObserverAbsentOwner sequence)
        (PMF.pure true) := by
  funext player
  unfold quittingBoundedSelfResetForcedOwnerProfile quittingProfileLiveRoot
  by_cases hplayer :
      player = quittingBoundedSelfResetObserverAbsentOwner sequence
  · subst player
    simp [quittingStagePureEndpointBehaviorDeviation,
      quittingStageDeviationHazard_self]
  · simp [Function.update, hplayer]

/-- Forcing a member of the selected terminal coalition to Quit cannot
decrease that coalition's stage cylinder. -/
theorem quittingBoundedSelfReset_stageMass_le_forcedOwnerCylinder
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts)
    (rank time : ℕ) :
    quittingStageCoalitionMass reward (sequence.profile rank) time
        sequence.terminal ≤
      quittingLiveMass reward (sequence.profile rank) time *
        quittingRootCoalitionMass
          (Function.update
            (quittingProfileLiveRoot reward (sequence.profile rank) time)
            (quittingBoundedSelfResetObserverAbsentOwner sequence)
            (PMF.pure true)) sequence.terminal.val := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  apply mul_le_mul_of_nonneg_left
  · simpa [quittingPureEndpointRoutedCoalition,
      quittingBoundedSelfResetObserverAbsentOwner_mem sequence] using
      quittingRootCoalitionMass_le_pureEndpointRouted
        (quittingProfileLiveRoot reward (sequence.profile rank) time)
        sequence.terminal.val
        (quittingBoundedSelfResetObserverAbsentOwner sequence) true
  · exact quittingLiveMass_nonneg reward (sequence.profile rank) time

/-- Quantitative finite-clock forced-owner wall produced when the final
pure-time observer is absent from the selected terminal coalition. -/
structure QuittingBoundedSelfResetObserverAbsentWall
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts) where
  observer_not_mem : sequence.observer ∉ sequence.terminal.val
  owner_ne_observer :
    quittingBoundedSelfResetObserverAbsentOwner sequence ≠ sequence.observer
  terminal_mass_eq_clock : ∀ rank,
    quittingTerminalOutcomeMass reward (sequence.profile rank)
        (some sequence.terminal) =
      ∑ time ∈ Finset.range (sequence.stop rank),
        quittingStageCoalitionMass reward (sequence.profile rank) time
          sequence.terminal
  row_wall : ∀ rank time, time < sequence.stop rank →
    let owner := quittingBoundedSelfResetObserverAbsentOwner sequence
    let actualRoot := quittingProfileLiveRoot reward (sequence.profile rank) time
    let forcedRoot := Function.update actualRoot owner (PMF.pure true)
    let forcedProfile :=
      quittingBoundedSelfResetForcedOwnerProfile sequence rank time
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward (sequence.profile rank) (time + 1))
    let mass := quittingStageCoalitionMass reward (sequence.profile rank) time
      sequence.terminal
    actualRoot sequence.observer = PMF.pure false ∧
      quittingProfileLiveRoot reward forcedProfile time = forcedRoot ∧
      mass ≤ quittingLiveMass reward (sequence.profile rank) time *
        quittingRootCoalitionMass forcedRoot sequence.terminal.val ∧
      regime.terminalGap ≤
        quittingBoundedSelfResetRowBarrier sequence rank time ∧
      mass * regime.terminalGap ≤
        mass * quittingBoundedSelfResetRowBarrier sequence rank time ∧
      ((∃ who, who ≠ owner ∧
          regime.terminalGap ≤
            quittingRootCoordinateNashDefect reward tail.1 forcedRoot who ∧
          mass * regime.terminalGap ≤ mass *
            quittingRootCoordinateNashDefect reward tail.1 forcedRoot who) ∨
        (regime.terminalGap ≤
            max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) ∧
          mass * regime.terminalGap ≤
            mass * max 0
              (-quittingAtomicBlockerBalance reward forcedRoot owner)))

theorem QuittingBoundedSelfResetTerminalSequence.observerAbsentWall
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {starts : ℕ → (quittingGame reward).BehaviorProfile}
    (sequence : QuittingBoundedSelfResetTerminalSequence regime starts)
    (habsent : sequence.observer ∉ sequence.terminal.val) :
    Nonempty (QuittingBoundedSelfResetObserverAbsentWall sequence) := by
  let owner := quittingBoundedSelfResetObserverAbsentOwner sequence
  have hownerMem : owner ∈ sequence.terminal.val :=
    quittingBoundedSelfResetObserverAbsentOwner_mem sequence
  have hownerNe : owner ≠ sequence.observer := by
    intro heq
    exact habsent (heq ▸ hownerMem)
  refine ⟨{
    observer_not_mem := habsent
    owner_ne_observer := hownerNe
    terminal_mass_eq_clock := ?_
    row_wall := ?_
  }⟩
  · intro rank
    obtain ⟨predecessor, hprofile⟩ :=
      (sequence.chain rank).exists_final_predecessor
    rw [hprofile]
    exact quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
      reward predecessor sequence.observer (sequence.stop rank)
        sequence.terminal habsent
  · intro rank time htime
    let actualRoot :=
      quittingProfileLiveRoot reward (sequence.profile rank) time
    let forcedRoot := Function.update actualRoot owner (PMF.pure true)
    let forcedProfile :=
      quittingBoundedSelfResetForcedOwnerProfile sequence rank time
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward (sequence.profile rank) (time + 1))
    let mass := quittingStageCoalitionMass reward (sequence.profile rank) time
      sequence.terminal
    have hobserver : actualRoot sequence.observer = PMF.pure false := by
      obtain ⟨predecessor, hprofile⟩ :=
        (sequence.chain rank).exists_final_predecessor
      dsimp only [actualRoot]
      rw [hprofile]
      exact quittingProfileLiveRoot_update_pureTime_some_eq_pureContinue_of_lt
        reward predecessor sequence.observer htime
    have hforcedProfile : quittingProfileLiveRoot reward forcedProfile time =
        forcedRoot := by
      simpa only [forcedProfile, forcedRoot, actualRoot, owner] using
        quittingProfileLiveRoot_boundedSelfResetForcedOwnerProfile
          sequence rank time
    have hmass : mass ≤ quittingLiveMass reward (sequence.profile rank) time *
        quittingRootCoalitionMass forcedRoot sequence.terminal.val := by
      simpa only [mass, forcedRoot, actualRoot, owner] using
        quittingBoundedSelfReset_stageMass_le_forcedOwnerCylinder
          sequence rank time
    have hownerForced : forcedRoot owner = PMF.pure true := by
      simp [forcedRoot]
    have hbarrier : regime.terminalGap ≤
        quittingBoundedSelfResetRowBarrier sequence rank time := by
      simpa only [quittingBoundedSelfResetRowBarrier, forcedRoot, actualRoot,
        owner] using regime.terminalGap_le_atomicBlockerBarrier hownerForced
    have hmassNonneg : 0 ≤ mass :=
      quittingStageCoalitionMass_nonneg reward (sequence.profile rank) time
        sequence.terminal
    have hweightedBarrier : mass * regime.terminalGap ≤
        mass * quittingBoundedSelfResetRowBarrier sequence rank time :=
      mul_le_mul_of_nonneg_left hbarrier hmassNonneg
    have halternative :
        (∃ who, who ≠ owner ∧
            regime.terminalGap ≤
              quittingRootCoordinateNashDefect reward tail.1 forcedRoot who ∧
            mass * regime.terminalGap ≤ mass *
              quittingRootCoordinateNashDefect reward tail.1 forcedRoot who) ∨
          (regime.terminalGap ≤
              max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) ∧
            mass * regime.terminalGap ≤
              mass * max 0
                (-quittingAtomicBlockerBalance reward forcedRoot owner)) := by
      have hraw : regime.terminalGap ≤
          max (quittingForcedOwnerOutsiderDefect reward forcedRoot owner)
            (max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner)) := by
        simpa only [quittingBoundedSelfResetRowBarrier, forcedRoot, actualRoot,
          owner] using hbarrier
      rcases le_max_iff.mp hraw with hdefect | hrefusal
      · left
        obtain ⟨who, hwho, hcoordinate⟩ :=
          exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
            reward tail.1 forcedRoot owner hownerForced
              regime.terminalGap_pos hdefect
        exact ⟨who, hwho, hcoordinate,
          mul_le_mul_of_nonneg_left hcoordinate hmassNonneg⟩
      · exact Or.inr ⟨hrefusal,
          mul_le_mul_of_nonneg_left hrefusal hmassNonneg⟩
    exact ⟨hobserver, hforcedProfile, hmass, hbarrier, hweightedBarrier,
      halternative⟩

end GameTheory
