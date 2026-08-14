/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOffDiagonalAtomSequenceDispatch
import Research.Quitting.TerminalLawTwoOutcomePassport

/-!
# Fixed two-outcome passports on the off-diagonal stopping-law frontier

The production positive-slope decoder retains one positive signed atom.  Its
proof actually starts from a positive *total payoff comparison*.  Applying
the independent-coupling identity before atom selection retains a stronger
passport: one outcome has positive mass in the better endpoint law, one
strictly lower-reward outcome has positive mass in the source law, and the
same pair persists along a subsequence.

When both outcomes absorb, their ordered membership signatures have at most
four fibers.  This is a genuine four-role localization of the terminal-law
witness.  It is not yet a four-player reduction: profiles, payoff coordinates
and conditional laws need not be constant inside a fiber.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One rank of the off-diagonal decoder with the stronger two-outcome
passport retained in either branch. -/
def HasQuittingStoppingLawVanishingDebtPassportAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge error : ℝ) : Prop :=
  (∃ high low : QuittingTerminalOutcome ι,
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
        quittingTerminalCrossLawAtom reward profile
          (Function.update profile mover target) observer high low) ∨
  ∃ quitTime : Option ℕ, ∃ high low : QuittingTerminalOutcome ι,
    charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
        quittingTerminalCrossLawAtom reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          (Function.update (Function.update profile mover (profile mover)) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          observer high low ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))) observer ≤
      error

/-- The coordinate positive-slope proof with its full two-law payoff passport
retained. -/
theorem exists_prescribedPassport_or_pureTimePassport_with_debtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda charge error : ℝ) (hlambda0 : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hcharge : 0 < charge)
    (herror : 0 < error) (herrorLe : error ≤ charge / 8)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0.le hlambda1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    HasQuittingStoppingLawVanishingDebtPassportAlternative reward profile mover
      observer target charge error := by
  let endpoint := Function.update profile mover target
  let mixed := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (profile mover) target lambda hlambda0.le hlambda1)
  let sourcePair := quittingTerminalSemanticPair reward profile
  let endpointPair := quittingTerminalSemanticPair reward endpoint
  let mixedPair := quittingTerminalSemanticPair reward mixed
  have hchord := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target lambda hlambda0.le
      hlambda1
  rw [Function.update_eq_self] at hchord
  change quittingTerminalSemanticDebt mixedPair observer ≤
      (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
        lambda * quittingTerminalSemanticDebt endpointPair observer at hchord
  have hendpointSlope : charge ≤
      quittingTerminalSemanticDebt endpointPair observer -
        quittingTerminalSemanticDebt sourcePair observer := by
    change lambda * charge ≤
      quittingTerminalSemanticDebt mixedPair observer -
        quittingTerminalSemanticDebt sourcePair observer at hslope
    have hscaled : lambda * charge ≤ lambda *
        (quittingTerminalSemanticDebt endpointPair observer -
          quittingTerminalSemanticDebt sourcePair observer) := by
      nlinarith
    nlinarith
  let sourceCap := quittingContinuationBestResponseValue reward profile observer
  let endpointCap := quittingContinuationBestResponseValue reward endpoint observer
  let sourcePayoff := quittingTerminalPayoff reward profile observer
  let endpointPayoff := quittingTerminalPayoff reward endpoint observer
  have hsplit : charge ≤
      (endpointCap - sourceCap) + (sourcePayoff - endpointPayoff) := by
    dsimp only [sourcePair, endpointPair, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair] at hendpointSlope
    dsimp only [sourceCap, endpointCap, sourcePayoff, endpointPayoff]
    linarith
  by_cases hpayoff : charge / 2 ≤ sourcePayoff - endpointPayoff
  · left
    obtain ⟨high, low, hatom, _hhigh, _hlow, _hrewardOrder⟩ :=
      exists_positive_terminalCrossLawPassport reward profile endpoint observer
        (charge / 2) (by positivity) hpayoff
    exact ⟨high, low, by simpa only [endpoint] using hatom⟩
  · right
    have hcap : charge / 2 < endpointCap - sourceCap := by linarith
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingContinuation_deviation_ge_sub reward endpoint observer
        (half_pos herror)
    obtain ⟨quitTime, hquitTime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        reward endpoint observer deviation (half_pos herror)
    let pureDeviation :=
      quittingPureTimeBehaviorStrategy reward observer quitTime
    have hsourceBound :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile observer pureDeviation
    have hpureEndpoint : endpointCap - error ≤
        quittingTerminalPayoff reward
          (Function.update endpoint observer pureDeviation) observer := by
      dsimp only [pureDeviation]
      linarith
    have hrectangle : charge / 4 ≤
        quittingTerminalPayoff reward
            (Function.update endpoint observer pureDeviation) observer -
          quittingTerminalPayoff reward
            (Function.update profile observer pureDeviation) observer := by
      dsimp only [sourceCap] at hcap hsourceBound
      linarith
    obtain ⟨high, low, hatom, _hhigh, _hlow, _hrewardOrder⟩ :=
      exists_positive_terminalCrossLawPassport reward
        (Function.update endpoint observer pureDeviation)
        (Function.update profile observer pureDeviation) observer
        (charge / 4) (by positivity) hrectangle
    have hdebt : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update endpoint observer pureDeviation)) observer ≤ error := by
      unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
      change quittingContinuationBestResponseValue reward
          (Function.update endpoint observer pureDeviation) observer -
        quittingTerminalPayoff reward
          (Function.update endpoint observer pureDeviation) observer ≤ error
      rw [quittingContinuationBestResponseValue_update_self]
      dsimp only [endpointCap] at hpureEndpoint
      linarith
    refine ⟨quitTime, high, low, ?_, ?_⟩
    · simpa only [endpoint, pureDeviation, Function.update_eq_self] using hatom
    · simpa only [endpoint, pureDeviation] using hdebt

/-- The strengthened alternative holds eventually on the fixed tangent
column, with the same vanishing error schedule as the production decoder. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_fixedVanishingDebtPassportAlternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    ∃ (mover : {who // who ∈ frontier.active}) (observer : ι) (charge : ℝ),
      observer ≠ mover.1 ∧ 0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawVanishingDebtPassportAlternative reward
          (frontier.profiles (frontier.subseq rank)) mover.1 observer
          (frontier.bestResponse mover (frontier.subseq rank)) charge
          (quittingStoppingLawAtomDecoderError charge rank) := by
  classical
  have hactiveNonempty : frontier.active.Nonempty := by
    by_contra hempty
    have hactiveEmpty : frontier.active = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hdebtZero : ∀ who,
        quittingTerminalSemanticDebt frontier.base who = 0 := by
      intro who
      have hnotPositive :
          ¬0 < quittingTerminalSemanticDebt frontier.base who := by
        intro hpositive
        have hmem := (frontier.active_iff who).2 hpositive
        rw [hactiveEmpty] at hmem
        simp at hmem
      exact le_antisymm (le_of_not_gt hnotPositive)
        (quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward frontier.base_mem who)
    have hbasePositive := frontier.base_positive
    unfold quittingTerminalSemanticDebtSum at hbasePositive
    simp only [hdebtZero, Finset.sum_const_zero] at hbasePositive
    exact (lt_irrefl 0) hbasePositive
  obtain ⟨mover, hmover⟩ := hactiveNonempty
  let activeMover : {who // who ∈ frontier.active} := ⟨mover, hmover⟩
  obtain ⟨observer, hobserverNe, hpositive⟩ :=
    frontier.exists_positiveOffDiagonal hmover
  let charge := frontier.tangent activeMover observer / 2
  have hcharge : 0 < charge := div_pos hpositive (by norm_num)
  have hchargeLt : charge < frontier.tangent activeMover observer := by
    dsimp only [charge, activeMover]
    linarith
  have heventuallySlope : ∀ᶠ rank in atTop,
      charge ≤ quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover
        (frontier.bestResponse activeMover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) observer :=
    (frontier.tangent_tendsto activeMover observer).eventually
      (Ioi_mem_nhds hchargeLt) |>.mono fun _ hlt ↦ hlt.le
  refine ⟨activeMover, observer, charge, hobserverNe, hcharge, ?_⟩
  filter_upwards [heventuallySlope] with rank hslopeNormalized
  have hlambda := frontier.lambda_pos (frontier.subseq rank)
  have hslope : frontier.lambda (frontier.subseq rank) * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update
              (frontier.profiles (frontier.subseq rank)) mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (frontier.profiles (frontier.subseq rank) mover)
                (frontier.bestResponse activeMover (frontier.subseq rank))
                (frontier.lambda (frontier.subseq rank)) hlambda.le
                (frontier.lambda_le_one (frontier.subseq rank))))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) observer := by
    unfold quittingStoppingLawNormalizedDebtDirection
      quittingTerminalSemanticDebtChange quittingStoppingLawResetProfile
      at hslopeNormalized
    have hscaled := (le_div_iff₀ hlambda).mp hslopeNormalized
    nlinarith
  exact exists_prescribedPassport_or_pureTimePassport_with_debtBound
    reward (frontier.profiles (frontier.subseq rank)) mover observer
      (frontier.bestResponse activeMover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank)) charge
      (quittingStoppingLawAtomDecoderError charge rank) hlambda
      (frontier.lambda_le_one (frontier.subseq rank)) hcharge
      (quittingStoppingLawAtomDecoderError_pos hcharge rank)
      (quittingStoppingLawAtomDecoderError_le hcharge rank)
      hslope

/-! ## A fixed ordered passport along a strict subsequence -/

/-- Prescribed-law branch with one fixed high/low outcome passport. -/
structure QuittingStoppingLawPrescribedPassportSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) where
  mover : {who // who ∈ frontier.active}
  observer : ι
  charge : ℝ
  observer_ne_mover : observer ≠ mover.1
  charge_pos : 0 < charge
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  high : QuittingTerminalOutcome ι
  low : QuittingTerminalOutcome ι
  atom_bound : ∀ n,
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
        quittingTerminalCrossLawAtom reward
          (frontier.profiles (frontier.subseq (rank n)))
          (Function.update (frontier.profiles (frontier.subseq (rank n)))
            mover.1 (frontier.bestResponse mover
              (frontier.subseq (rank n)))) observer high low

/-- Pure-time rectangle branch with one fixed high/low outcome passport and
vanishing observer debt at its high-law endpoint. -/
structure QuittingStoppingLawVanishingDebtPassportSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) where
  mover : {who // who ∈ frontier.active}
  observer : ι
  charge : ℝ
  observer_ne_mover : observer ≠ mover.1
  charge_pos : 0 < charge
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  quitTime : ℕ → Option ℕ
  high : QuittingTerminalOutcome ι
  low : QuittingTerminalOutcome ι
  atom_bound : ∀ n,
    charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
        quittingTerminalCrossLawAtom reward
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (rank n))) mover.1
              (frontier.bestResponse mover (frontier.subseq (rank n))))
            observer
            (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (rank n))) mover.1
              (frontier.profiles (frontier.subseq (rank n)) mover.1))
            observer
            (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
          observer high low
  observer_debt_tendsto_zero : Tendsto (fun n ↦
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update
          (Function.update
            (frontier.profiles (frontier.subseq (rank n))) mover.1
            (frontier.bestResponse mover (frontier.subseq (rank n))))
          observer
          (quittingPureTimeBehaviorStrategy reward observer (quitTime n))))
      observer) atTop (nhds 0)

namespace QuittingCounterexampleStoppingLawFrontier

/-- **Fixed two-outcome passport extraction.**  The ordered high/low pair is
constant along a strict subsequence in either branch. -/
theorem exists_prescribedPassportSequence_or_vanishingDebtPassportSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawPrescribedPassportSequence frontier) ∨
      Nonempty (QuittingStoppingLawVanishingDebtPassportSequence frontier) := by
  classical
  obtain ⟨mover, observer, charge, hobserverNe, hcharge, halternative⟩ :=
    frontier.exists_fixedVanishingDebtPassportAlternative
  let Prescribed : ℕ → Prop := fun rank ↦
    ∃ high low : QuittingTerminalOutcome ι,
      charge / 2 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
          quittingTerminalCrossLawAtom reward
            (frontier.profiles (frontier.subseq rank))
            (Function.update (frontier.profiles (frontier.subseq rank)) mover.1
              (frontier.bestResponse mover (frontier.subseq rank)))
            observer high low
  let Rectangle : ℕ → Prop := fun rank ↦
    ∃ quitTime : Option ℕ, ∃ high low : QuittingTerminalOutcome ι,
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
          quittingTerminalCrossLawAtom reward
            (Function.update
              (Function.update (frontier.profiles (frontier.subseq rank))
                mover.1 (frontier.bestResponse mover (frontier.subseq rank)))
              observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime))
            (Function.update
              (Function.update (frontier.profiles (frontier.subseq rank))
                mover.1 (frontier.profiles (frontier.subseq rank) mover.1))
              observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime))
            observer high low ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update
              (Function.update (frontier.profiles (frontier.subseq rank))
                mover.1 (frontier.bestResponse mover (frontier.subseq rank)))
              observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime)))
          observer ≤ quittingStoppingLawAtomDecoderError charge rank
  have hlocal : ∀ᶠ rank in atTop, Prescribed rank ∨ Rectangle rank := by
    simpa only [Prescribed, Rectangle,
      HasQuittingStoppingLawVanishingDebtPassportAlternative] using halternative
  by_cases hprescribed : ∃ᶠ rank in atTop, Prescribed rank
  · obtain ⟨rawRank, hrawRank, hatom⟩ :=
      extraction_of_frequently_atTop hprescribed
    choose highAt lowAt hpassportAt using hatom
    let pairAt : ℕ →
        QuittingTerminalOutcome ι × QuittingTerminalOutcome ι :=
      fun n => (highAt n, lowAt n)
    letI : TopologicalSpace
        (QuittingTerminalOutcome ι × QuittingTerminalOutcome ι) := ⊥
    letI : DiscreteTopology
        (QuittingTerminalOutcome ι × QuittingTerminalOutcome ι) :=
      discreteTopology_bot _
    obtain ⟨pair, pairSubseq, hpairSubseq, hpairTendsto⟩ :=
      CompactSpace.tendsto_subseq pairAt
    have hpairEventually : ∀ᶠ n in atTop, pairAt (pairSubseq n) = pair := by
      have hsingleton : ({pair} : Set
          (QuittingTerminalOutcome ι × QuittingTerminalOutcome ι)) ∈
          nhds pair := by
        have hopen : IsOpen ({pair} : Set
            (QuittingTerminalOutcome ι × QuittingTerminalOutcome ι)) :=
          discreteTopology_iff_isOpen_singleton.mp inferInstance pair
        exact hopen.mem_nhds rfl
      exact hpairTendsto.eventually hsingleton
    obtain ⟨labelStart, hlabelStart⟩ :=
      eventually_atTop.1 hpairEventually
    let rank : ℕ → ℕ := fun n ↦ rawRank (pairSubseq (n + labelStart))
    have hrank : StrictMono rank := by
      intro first second hlt
      exact hrawRank (hpairSubseq (Nat.add_lt_add_right hlt labelStart))
    have hfixed : ∀ n,
        pairAt (pairSubseq (n + labelStart)) = pair := by
      intro n
      exact hlabelStart (n + labelStart) (Nat.le_add_left labelStart n)
    refine Or.inl ⟨⟨mover, observer, charge, hobserverNe, hcharge,
      rank, hrank, pair.1, pair.2, ?_⟩⟩
    intro n
    have h := hpassportAt (pairSubseq (n + labelStart))
    have heq := hfixed n
    change (highAt (pairSubseq (n + labelStart)),
      lowAt (pairSubseq (n + labelStart))) = pair at heq
    have hhigh : highAt (pairSubseq (n + labelStart)) = pair.1 := by
      simpa using congrArg Prod.fst heq
    have hlow : lowAt (pairSubseq (n + labelStart)) = pair.2 := by
      simpa using congrArg Prod.snd heq
    rw [hhigh, hlow] at h
    simpa only [rank] using h
  · have hnotPrescribed : ∀ᶠ rank in atTop, ¬Prescribed rank :=
      Filter.not_frequently.mp hprescribed
    have hrectangle : ∀ᶠ rank in atTop, Rectangle rank := by
      filter_upwards [hlocal, hnotPrescribed] with rank hbranch hnot
      exact hbranch.resolve_left hnot
    obtain ⟨start, hstart⟩ := eventually_atTop.1 hrectangle
    have hchoice : ∀ n, Rectangle (n + start) := by
      intro n
      exact hstart (n + start) (Nat.le_add_left start n)
    choose quitTimeAt highAt lowAt hatomAt hdebtAt using hchoice
    let pairAt : ℕ →
        QuittingTerminalOutcome ι × QuittingTerminalOutcome ι :=
      fun n => (highAt n, lowAt n)
    letI : TopologicalSpace
        (QuittingTerminalOutcome ι × QuittingTerminalOutcome ι) := ⊥
    letI : DiscreteTopology
        (QuittingTerminalOutcome ι × QuittingTerminalOutcome ι) :=
      discreteTopology_bot _
    obtain ⟨pair, pairSubseq, hpairSubseq, hpairTendsto⟩ :=
      CompactSpace.tendsto_subseq pairAt
    have hpairEventually : ∀ᶠ n in atTop, pairAt (pairSubseq n) = pair := by
      have hsingleton : ({pair} : Set
          (QuittingTerminalOutcome ι × QuittingTerminalOutcome ι)) ∈
          nhds pair := by
        have hopen : IsOpen ({pair} : Set
            (QuittingTerminalOutcome ι × QuittingTerminalOutcome ι)) :=
          discreteTopology_iff_isOpen_singleton.mp inferInstance pair
        exact hopen.mem_nhds rfl
      exact hpairTendsto.eventually hsingleton
    obtain ⟨labelStart, hlabelStart⟩ :=
      eventually_atTop.1 hpairEventually
    let rank : ℕ → ℕ := fun n ↦ pairSubseq (n + labelStart) + start
    let quitTime : ℕ → Option ℕ := fun n ↦
      quitTimeAt (pairSubseq (n + labelStart))
    have hrank : StrictMono rank := by
      intro first second hlt
      exact Nat.add_lt_add_right
        (hpairSubseq (Nat.add_lt_add_right hlt labelStart)) start
    have hfixed : ∀ n,
        pairAt (pairSubseq (n + labelStart)) = pair := by
      intro n
      exact hlabelStart (n + labelStart) (Nat.le_add_left labelStart n)
    have hatom : ∀ n,
        charge / 4 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
            quittingTerminalCrossLawAtom reward
              (Function.update
                (Function.update
                  (frontier.profiles (frontier.subseq (rank n))) mover.1
                  (frontier.bestResponse mover (frontier.subseq (rank n))))
                observer
                (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
              (Function.update
                (Function.update
                  (frontier.profiles (frontier.subseq (rank n))) mover.1
                  (frontier.profiles (frontier.subseq (rank n)) mover.1))
                observer
                (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
              observer pair.1 pair.2 := by
      intro n
      have h := hatomAt (pairSubseq (n + labelStart))
      have heq := hfixed n
      change (highAt (pairSubseq (n + labelStart)),
        lowAt (pairSubseq (n + labelStart))) = pair at heq
      have hhigh : highAt (pairSubseq (n + labelStart)) = pair.1 := by
        simpa using congrArg Prod.fst heq
      have hlow : lowAt (pairSubseq (n + labelStart)) = pair.2 := by
        simpa using congrArg Prod.snd heq
      rw [hhigh, hlow] at h
      simpa only [rank, quitTime] using h
    have herror : Tendsto
        (fun n ↦ quittingStoppingLawAtomDecoderError charge (rank n))
        atTop (nhds 0) :=
      (tendsto_quittingStoppingLawAtomDecoderError charge).comp
        hrank.tendsto_atTop
    have hdebt : Tendsto (fun n ↦
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update
              (Function.update
                (frontier.profiles (frontier.subseq (rank n))) mover.1
                (frontier.bestResponse mover (frontier.subseq (rank n))))
              observer
              (quittingPureTimeBehaviorStrategy reward observer (quitTime n))))
          observer) atTop (nhds 0) := by
      apply squeeze_zero
      · intro n
        exact quittingTerminalDeviationDebt_nonneg reward _ observer
      · intro n
        simpa only [rank, quitTime] using
          hdebtAt (pairSubseq (n + labelStart))
      · exact herror
    exact Or.inr ⟨⟨mover, observer, charge, hobserverNe, hcharge,
      rank, hrank, quitTime, pair.1, pair.2, hatom, hdebt⟩⟩

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
