/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.Atom.ExactPrefixChronology
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.AtomSequenceDispatch
import Research.Quitting.CounterfactualAtomMinimumResetSquare

/-!
# Endpoint-debt provenance on the exact-prefix atom chronology

The fixed atom and rectangle decoders were obtained from a positive
normalized stopping-law debt direction, but their public packets discarded
that inequality.  This module retains it through the same fixed player
labels, the same literal suffix profiles, and arbitrarily long exact Nash
prefix stacks.

The full mover-reset endpoint then raises the observer's semantic debt by the
same fixed charge.  In the rectangle branch, the selected observer response
has vanishing debt at the common double-reset endpoint.  Global minimum
provenance therefore gives a literal square alternative: either the first
reset endpoint has a fixed total-debt excursion, or the observer reset sends
a fixed amount of debt to another named player.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact-prefix chronology retaining the normalized slope, its correctly
scaled mixed-edge inequality, the full-endpoint debt rise, and the stronger
vanishing-debt atom decoder. -/
structure QuittingStoppingLawAtomEndpointRiseChronology
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) where
  chronology : QuittingStoppingLawAtomExactPrefixChronology frontier
  normalizedSlope_eventually : ∀ᶠ rank in atTop,
    chronology.charge ≤ quittingStoppingLawNormalizedDebtDirection reward
      (frontier.profiles (frontier.subseq rank)) chronology.mover.1
      (frontier.bestResponse chronology.mover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank))
      (frontier.lambda_pos (frontier.subseq rank)).le
      (frontier.lambda_le_one (frontier.subseq rank)) chronology.observer
  mixedSlope_eventually : ∀ᶠ rank in atTop,
    frontier.lambda (frontier.subseq rank) * chronology.charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (frontier.profiles (frontier.subseq rank))
              chronology.mover.1
              (quittingStoppingLawMixtureBehaviorStrategy reward
                chronology.mover.1
                (frontier.profiles (frontier.subseq rank)
                  chronology.mover.1)
                (frontier.bestResponse chronology.mover
                  (frontier.subseq rank))
                (frontier.lambda (frontier.subseq rank))
                (frontier.lambda_pos (frontier.subseq rank)).le
                (frontier.lambda_le_one (frontier.subseq rank)))))
          chronology.observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) chronology.observer
  endpointDebtRise_eventually : ∀ᶠ rank in atTop,
    chronology.charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (frontier.profiles (frontier.subseq rank))
              chronology.mover.1
              (frontier.bestResponse chronology.mover
                (frontier.subseq rank)))) chronology.observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) chronology.observer
  vanishingAtom_eventually : ∀ᶠ rank in atTop,
    HasQuittingStoppingLawVanishingDebtAtomAlternative reward
      (frontier.profiles (frontier.subseq rank)) chronology.mover.1
      chronology.observer
      (frontier.bestResponse chronology.mover (frontier.subseq rank))
      chronology.charge
      (quittingStoppingLawAtomDecoderError chronology.charge rank)

/-- The actual fixed tangent column admits the enriched chronology.  The
factor `lambda` appears only on the mixed edge; convexity removes it when
passing to the full endpoint. -/
theorem QuittingCounterexampleStoppingLawFrontier.nonempty_atomEndpointRiseChronology
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawAtomEndpointRiseChronology frontier) := by
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
  have hnormalized : ∀ᶠ rank in atTop,
      charge ≤ quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover
        (frontier.bestResponse activeMover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) observer :=
    (frontier.tangent_tendsto activeMover observer).eventually
      (Ioi_mem_nhds hchargeLt) |>.mono fun _ hlt => hlt.le
  have hmixed : ∀ᶠ rank in atTop,
      frontier.lambda (frontier.subseq rank) * charge ≤
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update (frontier.profiles (frontier.subseq rank)) mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover
                  (frontier.profiles (frontier.subseq rank) mover)
                  (frontier.bestResponse activeMover (frontier.subseq rank))
                  (frontier.lambda (frontier.subseq rank))
                  (frontier.lambda_pos (frontier.subseq rank)).le
                  (frontier.lambda_le_one (frontier.subseq rank))))) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (frontier.profiles (frontier.subseq rank))) observer := by
    filter_upwards [hnormalized] with rank hslopeNormalized
    have hlambda := frontier.lambda_pos (frontier.subseq rank)
    unfold quittingStoppingLawNormalizedDebtDirection
      quittingTerminalSemanticDebtChange quittingStoppingLawResetProfile
      at hslopeNormalized
    have hscaled := (le_div_iff₀ hlambda).mp hslopeNormalized
    nlinarith
  have hendpoint : ∀ᶠ rank in atTop,
      charge ≤
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update (frontier.profiles (frontier.subseq rank)) mover
                (frontier.bestResponse activeMover (frontier.subseq rank))))
            observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (frontier.profiles (frontier.subseq rank))) observer := by
    filter_upwards [hmixed] with rank hslope
    exact stoppingLawSlope_le_fullEndpoint_observerDebtChange
      reward (frontier.profiles (frontier.subseq rank)) mover observer
      (frontier.bestResponse activeMover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank)) charge
      (frontier.lambda_pos (frontier.subseq rank))
      (frontier.lambda_le_one (frontier.subseq rank))
      hslope
  have hvanishing : ∀ᶠ rank in atTop,
      HasQuittingStoppingLawVanishingDebtAtomAlternative reward
        (frontier.profiles (frontier.subseq rank)) mover observer
        (frontier.bestResponse activeMover (frontier.subseq rank)) charge
        (quittingStoppingLawAtomDecoderError charge rank) := by
    filter_upwards [hmixed] with rank hslope
    exact exists_prescribedAtom_or_pureTimeRectangleAtom_with_debtBound
      reward (frontier.profiles (frontier.subseq rank)) mover observer
      (frontier.bestResponse activeMover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank)) charge
      (quittingStoppingLawAtomDecoderError charge rank)
      (frontier.lambda_pos (frontier.subseq rank))
      (frontier.lambda_le_one (frontier.subseq rank)) hcharge
      (quittingStoppingLawAtomDecoderError_pos hcharge rank)
      (quittingStoppingLawAtomDecoderError_le hcharge.le rank) hslope
  have hatom : ∀ᶠ rank in atTop,
      HasQuittingStoppingLawDebtSlopeAtomAlternative reward
        (frontier.profiles (frontier.subseq rank)) mover observer
        (frontier.bestResponse activeMover (frontier.subseq rank)) charge :=
    hvanishing.mono fun _ h =>
      hasDebtSlopeAtomAlternative_of_hasVanishingDebtAtomAlternative
        reward _ mover observer _ charge _ h
  obtain ⟨chronology, hmoverEq, hobserverEq, hchargeEq⟩ :=
    nonempty_atomExactPrefixChronology_of_fixedAlternative frontier activeMover
      observer charge hobserverNe hcharge hatom
  refine ⟨{
    chronology := chronology
    normalizedSlope_eventually := ?_
    mixedSlope_eventually := ?_
    endpointDebtRise_eventually := ?_
    vanishingAtom_eventually := ?_ }⟩
  · rw [hmoverEq, hobserverEq, hchargeEq]
    simpa only [activeMover] using hnormalized
  · rw [hmoverEq, hobserverEq, hchargeEq]
    simpa only [activeMover] using hmixed
  · rw [hmoverEq, hobserverEq, hchargeEq]
    simpa only [activeMover] using hendpoint
  · rw [hmoverEq, hobserverEq, hchargeEq]
    simpa only [activeMover] using hvanishing

/-! ## Fixed-label exact-prefix extraction -/

/-- Fixed prescribed atom labels with the complete exact-prefix and endpoint
debt-rise provenance retained. -/
structure QuittingStoppingLawPrescribedAtomEndpointRiseSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawAtomEndpointRiseChronology frontier) where
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  terminal : {S : Finset ι // S.Nonempty}
  atom_bound : ∀ n,
    packet.chronology.charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (frontier.profiles (frontier.subseq (rank n)))
          (Function.update (frontier.profiles (frontier.subseq (rank n)))
            packet.chronology.mover.1
            (frontier.bestResponse packet.chronology.mover
              (frontier.subseq (rank n))))
          packet.chronology.observer (some terminal)
  mixedSlope : ∀ n,
    frontier.lambda (frontier.subseq (rank n)) *
        packet.chronology.charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (frontier.profiles (frontier.subseq (rank n)))
              packet.chronology.mover.1
              (quittingStoppingLawMixtureBehaviorStrategy reward
                packet.chronology.mover.1
                (frontier.profiles (frontier.subseq (rank n))
                  packet.chronology.mover.1)
                (frontier.bestResponse packet.chronology.mover
                  (frontier.subseq (rank n)))
                (frontier.lambda (frontier.subseq (rank n)))
                (frontier.lambda_pos (frontier.subseq (rank n))).le
                (frontier.lambda_le_one (frontier.subseq (rank n))))))
          packet.chronology.observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq (rank n))))
          packet.chronology.observer
  endpointDebtRise : ∀ n,
    packet.chronology.charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (frontier.profiles (frontier.subseq (rank n)))
              packet.chronology.mover.1
              (frontier.bestResponse packet.chronology.mover
                (frontier.subseq (rank n))))) packet.chronology.observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq (rank n))))
          packet.chronology.observer

/-- Fixed rectangle labels and responses with exact-prefix, endpoint-rise,
and vanishing observer-debt provenance. -/
structure QuittingStoppingLawRectangleEndpointRiseSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawAtomEndpointRiseChronology frontier) where
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  quitTime : ℕ → Option ℕ
  terminal : {S : Finset ι // S.Nonempty}
  atom_bound : ∀ n,
    packet.chronology.charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (rank n)))
              packet.chronology.mover.1
              (frontier.bestResponse packet.chronology.mover
                (frontier.subseq (rank n))))
            packet.chronology.observer
            (quittingPureTimeBehaviorStrategy reward
              packet.chronology.observer (quitTime n)))
          (Function.update
            (frontier.profiles (frontier.subseq (rank n)))
            packet.chronology.observer
            (quittingPureTimeBehaviorStrategy reward
              packet.chronology.observer (quitTime n)))
          packet.chronology.observer (some terminal)
  observer_debt_bound : ∀ n,
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update
            (Function.update
              (frontier.profiles (frontier.subseq (rank n)))
              packet.chronology.mover.1
              (frontier.bestResponse packet.chronology.mover
                (frontier.subseq (rank n))))
            packet.chronology.observer
            (quittingPureTimeBehaviorStrategy reward
              packet.chronology.observer (quitTime n))))
        packet.chronology.observer ≤
      quittingStoppingLawAtomDecoderError packet.chronology.charge (rank n)
  mixedSlope : ∀ n,
    frontier.lambda (frontier.subseq (rank n)) *
        packet.chronology.charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (frontier.profiles (frontier.subseq (rank n)))
              packet.chronology.mover.1
              (quittingStoppingLawMixtureBehaviorStrategy reward
                packet.chronology.mover.1
                (frontier.profiles (frontier.subseq (rank n))
                  packet.chronology.mover.1)
                (frontier.bestResponse packet.chronology.mover
                  (frontier.subseq (rank n)))
                (frontier.lambda (frontier.subseq (rank n)))
                (frontier.lambda_pos (frontier.subseq (rank n))).le
                (frontier.lambda_le_one (frontier.subseq (rank n))))))
          packet.chronology.observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq (rank n))))
          packet.chronology.observer
  endpointDebtRise : ∀ n,
    packet.chronology.charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (frontier.profiles (frontier.subseq (rank n)))
              packet.chronology.mover.1
              (frontier.bestResponse packet.chronology.mover
                (frontier.subseq (rank n))))) packet.chronology.observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq (rank n))))
          packet.chronology.observer
  observer_debt_tendsto_zero : Tendsto (fun n =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update
          (Function.update
            (frontier.profiles (frontier.subseq (rank n)))
            packet.chronology.mover.1
            (frontier.bestResponse packet.chronology.mover
              (frontier.subseq (rank n))))
          packet.chronology.observer
          (quittingPureTimeBehaviorStrategy reward
            packet.chronology.observer (quitTime n))))
      packet.chronology.observer) atTop (nhds 0)

/-- Every fixed-label subsequence retains the exact Nash stacks chosen in the
enriched chronology. -/
theorem QuittingStoppingLawRectangleEndpointRiseSequence.exactStack
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet)
    (n : ℕ) :
    IsQuittingLiteralExactRootStack reward
      (packet.chronology.roots (sequence.rank n))
      (frontier.profiles (frontier.subseq (sequence.rank n))) :=
  packet.chronology.exact_stack (sequence.rank n)

/-- Along the fixed-label rectangle subsequence, the complete exact-prefix
profiles still converge in total debt to the global minimum fiber. -/
theorem QuittingStoppingLawRectangleEndpointRiseSequence.prefixDebt_tendsto_minimum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet) :
    Tendsto (fun n => quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward
          (packet.chronology.roots (sequence.rank n))
          (frontier.profiles (frontier.subseq (sequence.rank n))))))
      atTop (nhds (quittingTerminalSemanticDebtSum frontier.base)) :=
  packet.chronology.prefixDebt_tendsto_minimum.comp
    sequence.rank_strictMono.tendsto_atTop

/-- Fixed-label extraction from the enriched exact-prefix chronology. -/
theorem QuittingStoppingLawAtomEndpointRiseChronology.exists_prescribed_or_rectangleSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawAtomEndpointRiseChronology frontier) :
    Nonempty (QuittingStoppingLawPrescribedAtomEndpointRiseSequence packet) ∨
      Nonempty (QuittingStoppingLawRectangleEndpointRiseSequence packet) := by
  classical
  let mover := packet.chronology.mover
  let observer := packet.chronology.observer
  let charge := packet.chronology.charge
  let Prescribed : ℕ → Prop := fun rank =>
    ∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 2 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (frontier.profiles (frontier.subseq rank))
            (Function.update (frontier.profiles (frontier.subseq rank))
              mover.1 (frontier.bestResponse mover (frontier.subseq rank)))
            observer (some terminal)
  let Rectangle : ℕ → Prop := fun rank =>
    ∃ quitTime : Option ℕ, ∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
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
            observer (some terminal) ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update
              (Function.update (frontier.profiles (frontier.subseq rank))
                mover.1 (frontier.bestResponse mover (frontier.subseq rank)))
              observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime)))
          observer ≤ quittingStoppingLawAtomDecoderError charge rank
  let Slope : ℕ → Prop := fun rank =>
    frontier.lambda (frontier.subseq rank) * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (frontier.profiles (frontier.subseq rank)) mover.1
              (quittingStoppingLawMixtureBehaviorStrategy reward mover.1
                (frontier.profiles (frontier.subseq rank) mover.1)
                (frontier.bestResponse mover (frontier.subseq rank))
                (frontier.lambda (frontier.subseq rank))
                (frontier.lambda_pos (frontier.subseq rank)).le
                (frontier.lambda_le_one (frontier.subseq rank))))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) observer
  let Rise : ℕ → Prop := fun rank => charge ≤
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (frontier.profiles (frontier.subseq rank)) mover.1
            (frontier.bestResponse mover (frontier.subseq rank)))) observer -
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (frontier.profiles (frontier.subseq rank))) observer
  have hlocal : ∀ᶠ rank in atTop, Prescribed rank ∨ Rectangle rank := by
    simpa only [Prescribed, Rectangle, mover, observer, charge,
      HasQuittingStoppingLawVanishingDebtAtomAlternative] using
      packet.vanishingAtom_eventually
  have hslope : ∀ᶠ rank in atTop, Slope rank := by
    simpa only [Slope, mover, observer, charge] using
      packet.mixedSlope_eventually
  have hrise : ∀ᶠ rank in atTop, Rise rank := by
    simpa only [Rise, mover, observer, charge] using
      packet.endpointDebtRise_eventually
  let PrescribedGood : ℕ → Prop := fun rank =>
    Prescribed rank ∧ Slope rank ∧ Rise rank
  let RectangleGood : ℕ → Prop := fun rank =>
    Rectangle rank ∧ Slope rank ∧ Rise rank
  have hgood : ∀ᶠ rank in atTop,
      PrescribedGood rank ∨ RectangleGood rank := by
    filter_upwards [hlocal, hslope, hrise] with rank hbranch hs hr
    exact hbranch.elim (fun hp => Or.inl ⟨hp, hs, hr⟩)
      (fun hq => Or.inr ⟨hq, hs, hr⟩)
  by_cases hprescribed : ∃ᶠ rank in atTop, PrescribedGood rank
  · obtain ⟨rank, hrank, hgoodAt⟩ :=
      extraction_of_frequently_atTop hprescribed
    choose terminalAt hterminalAt using fun n => (hgoodAt n).1
    letI : TopologicalSpace {S : Finset ι // S.Nonempty} := ⊥
    letI : DiscreteTopology {S : Finset ι // S.Nonempty} :=
      discreteTopology_bot _
    obtain ⟨terminal, terminalSubseq, hterminalSubseq,
      hterminalTendsto⟩ := CompactSpace.tendsto_subseq terminalAt
    have hterminalEventually : ∀ᶠ n in atTop,
        terminalAt (terminalSubseq n) = terminal := by
      have hsingleton : ({terminal} : Set {S : Finset ι // S.Nonempty}) ∈
          nhds terminal := by
        have hopen : IsOpen ({terminal} :
            Set {S : Finset ι // S.Nonempty}) :=
          discreteTopology_iff_isOpen_singleton.mp inferInstance terminal
        exact hopen.mem_nhds rfl
      exact hterminalTendsto.eventually hsingleton
    obtain ⟨labelStart, hlabelStart⟩ :=
      eventually_atTop.1 hterminalEventually
    let fixedRank : ℕ → ℕ := fun n => rank (terminalSubseq (n + labelStart))
    have hfixedRank : StrictMono fixedRank := by
      intro first second hlt
      exact hrank (hterminalSubseq (Nat.add_lt_add_right hlt labelStart))
    have hfixedAtom : ∀ n, charge / 2 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (frontier.profiles (frontier.subseq (fixedRank n)))
            (Function.update
              (frontier.profiles (frontier.subseq (fixedRank n))) mover.1
              (frontier.bestResponse mover (frontier.subseq (fixedRank n))))
            observer (some terminal) := by
      intro n
      have h := hterminalAt (terminalSubseq (n + labelStart))
      rw [hlabelStart (n + labelStart) (Nat.le_add_left labelStart n)] at h
      simpa only [fixedRank] using h
    have hfixedSlope : ∀ n, Slope (fixedRank n) := fun n =>
      (hgoodAt (terminalSubseq (n + labelStart))).2.1
    have hfixedRise : ∀ n, Rise (fixedRank n) := fun n =>
      (hgoodAt (terminalSubseq (n + labelStart))).2.2
    exact Or.inl ⟨⟨fixedRank, hfixedRank, terminal,
      by simpa only [mover, observer, charge] using hfixedAtom,
      by simpa only [Slope, mover, observer, charge] using hfixedSlope,
      by simpa only [Rise, mover, observer, charge] using hfixedRise⟩⟩
  · have hnotPrescribed : ∀ᶠ rank in atTop, ¬PrescribedGood rank :=
      Filter.not_frequently.mp hprescribed
    have hrectangle : ∀ᶠ rank in atTop, RectangleGood rank := by
      filter_upwards [hgood, hnotPrescribed] with rank hbranch hnot
      exact hbranch.resolve_left hnot
    obtain ⟨start, hstart⟩ := eventually_atTop.1 hrectangle
    have hchoice : ∀ n, RectangleGood (n + start) := fun n =>
      hstart (n + start) (Nat.le_add_left start n)
    choose quitTimeAt terminalAt hatomAt hdebtAt using
      fun n => (hchoice n).1
    letI : TopologicalSpace {S : Finset ι // S.Nonempty} := ⊥
    letI : DiscreteTopology {S : Finset ι // S.Nonempty} :=
      discreteTopology_bot _
    obtain ⟨terminal, terminalSubseq, hterminalSubseq,
      hterminalTendsto⟩ := CompactSpace.tendsto_subseq terminalAt
    have hterminalEventually : ∀ᶠ n in atTop,
        terminalAt (terminalSubseq n) = terminal := by
      have hsingleton : ({terminal} : Set {S : Finset ι // S.Nonempty}) ∈
          nhds terminal := by
        have hopen : IsOpen ({terminal} :
            Set {S : Finset ι // S.Nonempty}) :=
          discreteTopology_iff_isOpen_singleton.mp inferInstance terminal
        exact hopen.mem_nhds rfl
      exact hterminalTendsto.eventually hsingleton
    obtain ⟨labelStart, hlabelStart⟩ :=
      eventually_atTop.1 hterminalEventually
    let rank : ℕ → ℕ := fun n => terminalSubseq (n + labelStart) + start
    let quitTime : ℕ → Option ℕ := fun n =>
      quitTimeAt (terminalSubseq (n + labelStart))
    have hrank : StrictMono rank := by
      intro first second hlt
      exact Nat.add_lt_add_right
        (hterminalSubseq (Nat.add_lt_add_right hlt labelStart)) start
    have hterminalEq : ∀ n,
        terminalAt (terminalSubseq (n + labelStart)) = terminal := fun n =>
      hlabelStart (n + labelStart) (Nat.le_add_left labelStart n)
    have hatom : ∀ n, charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update
              (Function.update
                (frontier.profiles (frontier.subseq (rank n))) mover.1
                (frontier.bestResponse mover (frontier.subseq (rank n))))
              observer
              (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
            (Function.update (frontier.profiles (frontier.subseq (rank n)))
              observer
              (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
            observer (some terminal) := by
      intro n
      have h := hatomAt (terminalSubseq (n + labelStart))
      rw [hterminalEq n] at h
      simpa only [rank, quitTime, Function.update_eq_self] using h
    have hdebt : ∀ n,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update
                (Function.update
                  (frontier.profiles (frontier.subseq (rank n))) mover.1
                  (frontier.bestResponse mover (frontier.subseq (rank n))))
                observer
                (quittingPureTimeBehaviorStrategy reward observer (quitTime n))))
            observer ≤ quittingStoppingLawAtomDecoderError charge (rank n) := by
      intro n
      simpa only [rank, quitTime] using
        hdebtAt (terminalSubseq (n + labelStart))
    have hfixedSlope : ∀ n, Slope (rank n) := fun n =>
      (hchoice (terminalSubseq (n + labelStart))).2.1
    have hfixedRise : ∀ n, Rise (rank n) := fun n =>
      (hchoice (terminalSubseq (n + labelStart))).2.2
    have herror : Tendsto
        (fun n => quittingStoppingLawAtomDecoderError charge (rank n))
        atTop (nhds 0) :=
      (tendsto_quittingStoppingLawAtomDecoderError charge).comp
        hrank.tendsto_atTop
    have hdebtZero : Tendsto (fun n =>
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
      · exact hdebt
      · exact herror
    exact Or.inr ⟨⟨rank, hrank, quitTime, terminal,
      by simpa only [mover, observer, charge] using hatom,
      by simpa only [mover, observer, charge] using hdebt,
      by simpa only [Slope, mover, observer, charge] using hfixedSlope,
      by simpa only [Rise, mover, observer, charge] using hfixedRise,
      by simpa only [mover, observer] using hdebtZero⟩⟩

/-! ## Global-minimum square dispatch -/

/-- The rectangle branch cannot remain a two-coordinate debt transfer near
the global floor.  At every fixed-label rank, either the first reset endpoint
has a fixed excess or the literal observer-response edge transfers a fixed
amount to another named player. -/
theorem QuittingStoppingLawRectangleEndpointRiseSequence.excess_or_secondTransfer
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet)
    (n : ℕ) :
    let profile := frontier.profiles (frontier.subseq (sequence.rank n))
    let first := Function.update profile packet.chronology.mover.1
      (frontier.bestResponse packet.chronology.mover
        (frontier.subseq (sequence.rank n)))
    let both := Function.update first packet.chronology.observer
      (quittingPureTimeBehaviorStrategy reward packet.chronology.observer
        (sequence.quitTime n))
    packet.chronology.charge / 2 ≤
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward first) -
          quittingTerminalSemanticDebtSum frontier.base ∨
      ∃ recipient ∈ Finset.univ.erase packet.chronology.observer,
        packet.chronology.charge / 4 /
            ((Finset.univ.erase packet.chronology.observer).card : ℝ) <
          quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward first)
            (quittingTerminalSemanticPair reward both) recipient := by
  dsimp only
  let profile := frontier.profiles (frontier.subseq (sequence.rank n))
  let moverTarget := frontier.bestResponse packet.chronology.mover
    (frontier.subseq (sequence.rank n))
  let observerResponse := quittingPureTimeBehaviorStrategy reward
    packet.chronology.observer (sequence.quitTime n)
  have hsquare :=
    positiveMinimum_counterfactualResetSquare_excess_or_secondTransfer
      reward frontier.base profile packet.chronology.mover.1
      packet.chronology.observer packet.chronology.observer_ne_mover.symm
      moverTarget observerResponse
      (frontier.lambda (frontier.subseq (sequence.rank n)))
      packet.chronology.charge
      (quittingStoppingLawAtomDecoderError packet.chronology.charge
        (sequence.rank n))
      (frontier.lambda_pos (frontier.subseq (sequence.rank n)))
      (frontier.lambda_le_one (frontier.subseq (sequence.rank n)))
      packet.chronology.charge_pos
      (by
        have h := quittingStoppingLawAtomDecoderError_le
          packet.chronology.charge_pos.le (sequence.rank n)
        linarith [packet.chronology.charge_pos])
      frontier.base_minimum
      (by simpa only [profile, moverTarget] using sequence.mixedSlope n)
      (by simpa only [profile, moverTarget, observerResponse] using
        sequence.observer_debt_bound n)
  exact hsquare.2

/-- If the first mover-reset endpoints approach the minimum fiber, the
square dispatch eventually leaves only a uniformly positive second transfer.
-/
theorem
    QuittingStoppingLawRectangleEndpointRiseSequence.eventually_secondTransfer_of_firstNearMinimum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet)
    (hnear : Tendsto (fun n =>
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update
              (frontier.profiles (frontier.subseq (sequence.rank n)))
              packet.chronology.mover.1
              (frontier.bestResponse packet.chronology.mover
                (frontier.subseq (sequence.rank n))))) -
        quittingTerminalSemanticDebtSum frontier.base) atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      ∃ recipient ∈ Finset.univ.erase packet.chronology.observer,
        packet.chronology.charge / 4 /
            ((Finset.univ.erase packet.chronology.observer).card : ℝ) <
          let profile := frontier.profiles
            (frontier.subseq (sequence.rank n))
          let first := Function.update profile packet.chronology.mover.1
            (frontier.bestResponse packet.chronology.mover
              (frontier.subseq (sequence.rank n)))
          let both := Function.update first packet.chronology.observer
            (quittingPureTimeBehaviorStrategy reward
              packet.chronology.observer (sequence.quitTime n))
          quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward first)
            (quittingTerminalSemanticPair reward both) recipient := by
  have hsmall : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update
              (frontier.profiles (frontier.subseq (sequence.rank n)))
              packet.chronology.mover.1
              (frontier.bestResponse packet.chronology.mover
                (frontier.subseq (sequence.rank n))))) -
        quittingTerminalSemanticDebtSum frontier.base <
          packet.chronology.charge / 2 :=
    hnear.eventually (Iio_mem_nhds
      (div_pos packet.chronology.charge_pos (by norm_num)))
  filter_upwards [hsmall] with n hn
  rcases sequence.excess_or_secondTransfer n with hexcess | htransfer
  · linarith
  · exact htransfer

namespace QuittingStoppingLawRectangleEndpointRiseSequence

/-- If the common double-reset endpoints approach the minimum fiber, every
late square gives either a fixed literal total-debt descent on the observer
edge or the same uniformly positive second-transfer certificate. -/
theorem eventually_descent_or_secondTransfer_of_bothNearMinimum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet)
    (hnear : Tendsto (fun n =>
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update
              (Function.update
                (frontier.profiles (frontier.subseq (sequence.rank n)))
                packet.chronology.mover.1
                (frontier.bestResponse packet.chronology.mover
                  (frontier.subseq (sequence.rank n))))
              packet.chronology.observer
              (quittingPureTimeBehaviorStrategy reward
                packet.chronology.observer (sequence.quitTime n)))) -
        quittingTerminalSemanticDebtSum frontier.base) atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      let profile := frontier.profiles (frontier.subseq (sequence.rank n))
      let first := Function.update profile packet.chronology.mover.1
        (frontier.bestResponse packet.chronology.mover
          (frontier.subseq (sequence.rank n)))
      let both := Function.update first packet.chronology.observer
        (quittingPureTimeBehaviorStrategy reward packet.chronology.observer
          (sequence.quitTime n))
      packet.chronology.charge / 4 ≤
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward first) -
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward both) ∨
        ∃ recipient ∈ Finset.univ.erase packet.chronology.observer,
          packet.chronology.charge / 4 /
              ((Finset.univ.erase packet.chronology.observer).card : ℝ) <
            quittingTerminalSemanticDebtChange
              (quittingTerminalSemanticPair reward first)
              (quittingTerminalSemanticPair reward both) recipient := by
  have hsmall : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update
              (Function.update
                (frontier.profiles (frontier.subseq (sequence.rank n)))
                packet.chronology.mover.1
                (frontier.bestResponse packet.chronology.mover
                  (frontier.subseq (sequence.rank n))))
              packet.chronology.observer
              (quittingPureTimeBehaviorStrategy reward
                packet.chronology.observer (sequence.quitTime n)))) -
        quittingTerminalSemanticDebtSum frontier.base <
          packet.chronology.charge / 4 :=
    hnear.eventually (Iio_mem_nhds
      (div_pos packet.chronology.charge_pos (by norm_num)))
  filter_upwards [hsmall] with n hn
  rcases sequence.excess_or_secondTransfer n with hexcess | htransfer
  · exact Or.inl (by linarith)
  · exact Or.inr htransfer

end QuittingStoppingLawRectangleEndpointRiseSequence

namespace QuittingCounterexampleStoppingLawFrontier

/-- Regime-facing enriched dispatch.  The prescribed branch retains the
endpoint debt-rise passport; the rectangle branch additionally carries the
literal reset-square alternative at every fixed-label rank. -/
theorem exists_prescribedEndpointRise_or_rectangleSquareDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    (∃ packet : QuittingStoppingLawAtomEndpointRiseChronology frontier,
        Nonempty
          (QuittingStoppingLawPrescribedAtomEndpointRiseSequence packet)) ∨
      ∃ packet : QuittingStoppingLawAtomEndpointRiseChronology frontier,
        ∃ sequence : QuittingStoppingLawRectangleEndpointRiseSequence packet,
          ∀ n,
            let profile := frontier.profiles
              (frontier.subseq (sequence.rank n))
            let first := Function.update profile packet.chronology.mover.1
              (frontier.bestResponse packet.chronology.mover
                (frontier.subseq (sequence.rank n)))
            let both := Function.update first packet.chronology.observer
              (quittingPureTimeBehaviorStrategy reward
                packet.chronology.observer (sequence.quitTime n))
            packet.chronology.charge / 2 ≤
                quittingTerminalSemanticDebtSum
                    (quittingTerminalSemanticPair reward first) -
                  quittingTerminalSemanticDebtSum frontier.base ∨
              ∃ recipient ∈ Finset.univ.erase packet.chronology.observer,
                packet.chronology.charge / 4 /
                    ((Finset.univ.erase
                      packet.chronology.observer).card : ℝ) <
                  quittingTerminalSemanticDebtChange
                    (quittingTerminalSemanticPair reward first)
                    (quittingTerminalSemanticPair reward both) recipient := by
  obtain ⟨packet⟩ := frontier.nonempty_atomEndpointRiseChronology
  rcases packet.exists_prescribed_or_rectangleSequence with hprescribed |
      hrectangle
  · exact Or.inl ⟨packet, hprescribed⟩
  · obtain ⟨sequence⟩ := hrectangle
    exact Or.inr ⟨packet, sequence, sequence.excess_or_secondTransfer⟩

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
