/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.AtomSequenceDispatch
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingPayoff

/-!
# Self-oriented pure-time atom sequence

The off-diagonal stopping-law decoder can expose a prescribed-payoff atom when
one player's reset lowers another player's payoff.  That branch is avoidable.
Choose instead one positive-debt owner, purify both a near-worst source and a
near-best target to deterministic Quit times, and compare the owner's own
payoff.  Own-strategy updates leave the owner's best-response cap unchanged,
so the target-minus-source payoff gain is the source debt up to vanishing
error.  A fixed absorbing terminal atom therefore survives along a strict
subsequence while the target owner's debt tends to zero.

Both endpoints use pure times.  Hence the sign and owner-membership of the
fixed terminal feed literal pure-time versions of the three existing
consumers: the owner-absent forced-row wall, the negative source-row atomic
dispatch, or the positive reached-row localization.  No prescribed comparison
leaf remains.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Pure-time source and target selection -/

/-- Some deterministic Quit time or `Never` has payoff no larger than a
behavioral strategy's payoff up to any positive error. -/
private theorem exists_quittingPureTimeBehaviorStrategy_terminalPayoff_le_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (strategy : (quittingGame reward).BehaviorStrategy who)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ quitTime : Option ℕ,
      quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) who ≤
        quittingTerminalPayoff reward
            (Function.update profile who strategy) who + ε := by
  let source := quittingTerminalPayoff reward
    (Function.update profile who strategy) who
  let value : Option ℕ → ℝ := fun quitTime =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime)) who
  have hmixture : source =
      expect (quittingBehaviorStoppingLaw reward strategy) value := by
    simpa only [source, value] using
      quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
        reward profile who strategy
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  have hmono :
      expect (quittingBehaviorStoppingLaw reward strategy)
          (fun _ : Option ℕ => source + ε) ≤
        expect (quittingBehaviorStoppingLaw reward strategy) value := by
    apply FinDist.expect_mono
    intro quitTime _
    exact (hnone quitTime).le
  rw [expect_const, ← hmixture] at hmono
  linarith

/-- Pure Quit times and `Never` approach the full behavioral best-response
cap from below. -/
private theorem exists_quittingPureTimeBehaviorStrategy_cap_ge_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ quitTime : Option ℕ,
      quittingContinuationBestResponseValue reward profile who - ε ≤
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) who := by
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub
      reward profile who (half_pos hε)
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward profile who deviation (half_pos hε)
  refine ⟨quitTime, ?_⟩
  linarith

/-- Two pure times expose the owner's debt as a target-minus-source payoff
gain, and the near-best target has small owner debt. -/
private theorem exists_quittingPureTimePair_gain_and_targetDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ sourceTime targetTime : Option ℕ,
      quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) who - 2 * ε ≤
        quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who targetTime)) who -
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who sourceTime)) who ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who targetTime))) who ≤
        ε := by
  obtain ⟨sourceTime, hsource⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_le_add
      reward profile who (profile who) hε
  rw [Function.update_eq_self] at hsource
  obtain ⟨targetTime, htarget⟩ :=
    exists_quittingPureTimeBehaviorStrategy_cap_ge_sub
      reward profile who hε
  have htargetDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who targetTime))) who ≤ ε := by
    change quittingContinuationBestResponseValue reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who targetTime)) who -
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who targetTime)) who ≤ ε
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  refine ⟨sourceTime, targetTime, ?_, htargetDebt⟩
  change quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who - 2 * ε ≤
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who targetTime)) who -
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who sourceTime)) who
  linarith

/-- Update one player by a deterministic Quit time or by `Never`. -/
def quittingPureTimeUpdatedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (quitTime : Option ℕ) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile who
    (quittingPureTimeBehaviorStrategy reward who quitTime)

/-! ## Self-oriented fixed-label atom sequence -/

/-- A fixed self-oriented terminal atom between two pure-time owner endpoints.
The target endpoint is an asymptotic owner best response. -/
structure QuittingStoppingLawSelfOrientedAtomSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) where
  owner : {who // who ∈ frontier.active}
  charge : ℝ
  charge_pos : 0 < charge
  rank : ℕ → ℕ
  rank_strictMono : StrictMono rank
  sourceQuitTime : ℕ → Option ℕ
  targetQuitTime : ℕ → Option ℕ
  terminal : {S : Finset ι // S.Nonempty}
  atom_bound : ∀ n,
    charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (quittingPureTimeUpdatedProfile reward
            (frontier.profiles (frontier.subseq (rank n))) owner.1
            (targetQuitTime n))
          (quittingPureTimeUpdatedProfile reward
            (frontier.profiles (frontier.subseq (rank n))) owner.1
            (sourceQuitTime n))
          owner.1 (some terminal)
  target_debt_tendsto_zero : Tendsto (fun n =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingPureTimeUpdatedProfile reward
          (frontier.profiles (frontier.subseq (rank n))) owner.1
          (targetQuitTime n))) owner.1) atTop (nhds 0)

/-- The source pure-time endpoint. -/
def quittingStoppingLawSelfOrientedSourceProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingPureTimeUpdatedProfile reward
    (frontier.profiles (frontier.subseq (packet.rank n))) packet.owner.1
    (packet.sourceQuitTime n)

/-- The target pure-time endpoint. -/
def quittingStoppingLawSelfOrientedTargetProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingPureTimeUpdatedProfile reward
    (frontier.profiles (frontier.subseq (packet.rank n))) packet.owner.1
    (packet.targetQuitTime n)

namespace QuittingCounterexampleStoppingLawFrontier

/-- Every stopping-law frontier has a self-oriented fixed-terminal atom
sequence.  The construction uses no off-diagonal recipient. -/
theorem nonempty_selfOrientedAtomSequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawSelfOrientedAtomSequence frontier) := by
  classical
  have hactiveNonempty : frontier.active.Nonempty := by
    by_contra hempty
    have hactiveEmpty : frontier.active = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hdebtZero : ∀ who,
        quittingTerminalSemanticDebt frontier.base who = 0 := by
      intro who
      have hnotPositive :
          ¬ 0 < quittingTerminalSemanticDebt frontier.base who := by
        intro hpositive
        have hmem := (frontier.active_iff who).2 hpositive
        rw [hactiveEmpty] at hmem
        simp at hmem
      exact le_antisymm (le_of_not_gt hnotPositive)
        (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
          frontier.base_mem who)
    have hbasePositive := frontier.base_positive
    unfold quittingTerminalSemanticDebtSum at hbasePositive
    simp only [hdebtZero, Finset.sum_const_zero] at hbasePositive
    exact (lt_irrefl 0) hbasePositive
  obtain ⟨owner, howner⟩ := hactiveNonempty
  let activeOwner : {who // who ∈ frontier.active} := ⟨owner, howner⟩
  let charge := quittingTerminalSemanticDebt frontier.base owner
  have hcharge : 0 < charge := by
    exact (frontier.active_iff owner).1 howner
  have hprofilesSubseq : Tendsto (fun rank =>
      quittingTerminalSemanticPair reward
        (frontier.profiles (frontier.subseq rank)))
      atTop (nhds frontier.base) :=
    frontier.profiles_tendsto.comp frontier.subseq_strictMono.tendsto_atTop
  have hdebtTendsto : Tendsto (fun rank =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (frontier.profiles (frontier.subseq rank))) owner)
      atTop (nhds charge) := by
    simpa only [charge] using
      (continuous_quittingTerminalSemanticDebt owner).tendsto frontier.base |>.comp
        hprofilesSubseq
  have heventuallyDebt : ∀ᶠ rank in atTop,
      charge / 2 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (frontier.profiles (frontier.subseq rank))) owner :=
    hdebtTendsto.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨start, hstart⟩ := eventually_atTop.1 heventuallyDebt
  let rawRank : ℕ → ℕ := fun n => n + start
  have hrawRank : StrictMono rawRank := by
    intro first second hlt
    exact Nat.add_lt_add_right hlt start
  have hsourceDebt : ∀ n,
      charge / 2 ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (frontier.profiles (frontier.subseq (rawRank n)))) owner := by
    intro n
    exact (hstart (rawRank n) (Nat.le_add_left start n)).le
  let error : ℕ → ℝ := quittingStoppingLawAtomDecoderError charge
  have hendpointChoice : ∀ n,
      ∃ sourceTime targetTime : Option ℕ,
        charge / 4 ≤
          quittingTerminalPayoff reward
              (quittingPureTimeUpdatedProfile reward
                (frontier.profiles (frontier.subseq (rawRank n))) owner
                targetTime) owner -
            quittingTerminalPayoff reward
              (quittingPureTimeUpdatedProfile reward
                (frontier.profiles (frontier.subseq (rawRank n))) owner
                sourceTime) owner ∧
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingPureTimeUpdatedProfile reward
              (frontier.profiles (frontier.subseq (rawRank n))) owner
              targetTime)) owner ≤ error n := by
    intro n
    have herrorPos : 0 < error n :=
      quittingStoppingLawAtomDecoderError_pos hcharge n
    obtain ⟨sourceTime, targetTime, hgain, htargetDebt⟩ :=
      exists_quittingPureTimePair_gain_and_targetDebt reward
        (frontier.profiles (frontier.subseq (rawRank n))) owner herrorPos
    have herrorLe : error n ≤ charge / 8 :=
      quittingStoppingLawAtomDecoderError_le hcharge.le n
    refine ⟨sourceTime, targetTime, ?_, htargetDebt⟩
    linarith [hsourceDebt n, hgain, herrorLe]
  choose sourceTimeAt targetTimeAt hgainAt hdebtAt using hendpointChoice
  have hterminalChoice : ∀ n,
      ∃ terminal : {S : Finset ι // S.Nonempty},
        charge / 4 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward
              (quittingPureTimeUpdatedProfile reward
                (frontier.profiles (frontier.subseq (rawRank n))) owner
                (targetTimeAt n))
              (quittingPureTimeUpdatedProfile reward
                (frontier.profiles (frontier.subseq (rawRank n))) owner
                (sourceTimeAt n))
              owner (some terminal) := by
    intro n
    exact exists_absorbingTerminalPayoffDifferenceAtom reward
      (quittingPureTimeUpdatedProfile reward
        (frontier.profiles (frontier.subseq (rawRank n))) owner
        (targetTimeAt n))
      (quittingPureTimeUpdatedProfile reward
        (frontier.profiles (frontier.subseq (rawRank n))) owner
        (sourceTimeAt n))
      owner (charge / 4) (by positivity) (hgainAt n)
  choose terminalAt hatomAt using hterminalChoice
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
    have hmem := hterminalTendsto.eventually hsingleton
    filter_upwards [hmem] with n hn
    exact hn
  obtain ⟨labelStart, hlabelStart⟩ :=
    eventually_atTop.1 hterminalEventually
  let selected : ℕ → ℕ := fun n => terminalSubseq (n + labelStart)
  have hselected : StrictMono selected := by
    intro first second hlt
    exact hterminalSubseq (Nat.add_lt_add_right hlt labelStart)
  let rank : ℕ → ℕ := fun n => rawRank (selected n)
  let sourceQuitTime : ℕ → Option ℕ := fun n => sourceTimeAt (selected n)
  let targetQuitTime : ℕ → Option ℕ := fun n => targetTimeAt (selected n)
  have hrank : StrictMono rank := hrawRank.comp hselected
  have hatom : ∀ n,
      charge / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (quittingPureTimeUpdatedProfile reward
              (frontier.profiles (frontier.subseq (rank n))) owner
              (targetQuitTime n))
            (quittingPureTimeUpdatedProfile reward
              (frontier.profiles (frontier.subseq (rank n))) owner
              (sourceQuitTime n))
            owner (some terminal) := by
    intro n
    have h := hatomAt (selected n)
    rw [hlabelStart (n + labelStart)
      (Nat.le_add_left labelStart n)] at h
    simpa only [rank, selected, rawRank, sourceQuitTime, targetQuitTime] using h
  have herror : Tendsto (fun n => error (selected n)) atTop (nhds 0) :=
    (tendsto_quittingStoppingLawAtomDecoderError charge).comp
      hselected.tendsto_atTop
  have htargetDebt : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeUpdatedProfile reward
            (frontier.profiles (frontier.subseq (rank n))) owner
            (targetQuitTime n))) owner) atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact quittingTerminalDeviationDebt_nonneg reward _ owner
    · intro n
      simpa only [rank, selected, rawRank, targetQuitTime, error] using
        hdebtAt (selected n)
    · simpa only [error] using herror
  exact ⟨⟨activeOwner, charge, hcharge, rank, hrank, sourceQuitTime,
    targetQuitTime, terminal, hatom, htargetDebt⟩⟩

end QuittingCounterexampleStoppingLawFrontier

/-! ## Signed mass carried by the self-oriented atom -/

/-- The fixed terminal reward coordinate selected by a positive atom is
nonzero. -/
theorem QuittingStoppingLawSelfOrientedAtomSequence.reward_ne_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier) :
    reward packet.terminal packet.owner.1 ≠ 0 := by
  intro hzero
  have hatom := packet.atom_bound 0
  unfold quittingTerminalPayoffDifferenceAtom at hatom
  simp only [quittingTerminalOutcomeReward] at hatom
  rw [hzero, mul_zero, mul_zero] at hatom
  linarith [packet.charge_pos]

/-- The canonical reward bound is positive on a self-oriented atom packet. -/
theorem QuittingStoppingLawSelfOrientedAtomSequence.rewardBound_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier) :
    0 < quittingRewardBound reward := by
  have hbound := abs_reward_le_quittingRewardBound reward packet.terminal
    packet.owner.1
  exact (abs_pos.mpr packet.reward_ne_zero).trans_le hbound

/-- Uniform terminal-mass scale supplied by the self-oriented atom. -/
def quittingStoppingLawSelfOrientedMassLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier) : ℝ :=
  (packet.charge / 4) /
    ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
      quittingRewardBound reward)

/-- The mass scale is strictly positive. -/
theorem QuittingStoppingLawSelfOrientedAtomSequence.massLower_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier) :
    0 < quittingStoppingLawSelfOrientedMassLower packet := by
  unfold quittingStoppingLawSelfOrientedMassLower
  exact div_pos (div_pos packet.charge_pos (by norm_num))
    (mul_pos (by positivity) packet.rewardBound_pos)

/-- Positive owner reward stores the atom's mass at the pure-time target. -/
theorem QuittingStoppingLawSelfOrientedAtomSequence.positiveTarget_massLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (hrewardPositive : 0 < reward packet.terminal packet.owner.1) (n : ℕ) :
    quittingStoppingLawSelfOrientedMassLower packet ≤
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawSelfOrientedTargetProfile packet n)
        (some packet.terminal) := by
  classical
  let card : ℝ := Fintype.card (QuittingTerminalOutcome ι)
  let M := quittingRewardBound reward
  let targetMass := quittingTerminalOutcomeMass reward
    (quittingStoppingLawSelfOrientedTargetProfile packet n)
    (some packet.terminal)
  let sourceMass := quittingTerminalOutcomeMass reward
    (quittingStoppingLawSelfOrientedSourceProfile packet n)
    (some packet.terminal)
  have hcard : 0 < card := by
    dsimp only [card]
    exact_mod_cast Fintype.card_pos
  have hrewardLe : reward packet.terminal packet.owner.1 ≤ M := by
    exact (le_abs_self _).trans
      (abs_reward_le_quittingRewardBound reward packet.terminal packet.owner.1)
  have hMpos : 0 < M := hrewardPositive.trans_le hrewardLe
  have htargetNonneg : 0 ≤ targetMass :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward
      (quittingStoppingLawSelfOrientedTargetProfile packet n)).1
        (some packet.terminal)
  have hsourceNonneg : 0 ≤ sourceMass :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward
      (quittingStoppingLawSelfOrientedSourceProfile packet n)).1
        (some packet.terminal)
  have hbound := packet.atom_bound n
  change packet.charge / 4 ≤ card *
      ((targetMass - sourceMass) * reward packet.terminal packet.owner.1)
    at hbound
  have hdiffRewardLe :
      (targetMass - sourceMass) * reward packet.terminal packet.owner.1 ≤
        targetMass * M := by
    have hdiffLe : targetMass - sourceMass ≤ targetMass := by linarith
    have hleft := mul_le_mul_of_nonneg_right hdiffLe hrewardPositive.le
    have hright := mul_le_mul_of_nonneg_left hrewardLe htargetNonneg
    exact hleft.trans hright
  have htotal : packet.charge / 4 ≤ card * (targetMass * M) :=
    hbound.trans (mul_le_mul_of_nonneg_left hdiffRewardLe hcard.le)
  unfold quittingStoppingLawSelfOrientedMassLower
  apply (div_le_iff₀ (mul_pos hcard hMpos)).2
  change packet.charge / 4 ≤ targetMass * (card * M)
  calc
    packet.charge / 4 ≤ card * (targetMass * M) := htotal
    _ = targetMass * (card * M) := by ring

/-- Negative owner reward stores the atom's mass at the pure-time source. -/
theorem QuittingStoppingLawSelfOrientedAtomSequence.negativeSource_massLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawSelfOrientedAtomSequence frontier)
    (hrewardNegative : reward packet.terminal packet.owner.1 < 0) (n : ℕ) :
    quittingStoppingLawSelfOrientedMassLower packet ≤
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawSelfOrientedSourceProfile packet n)
        (some packet.terminal) := by
  classical
  let card : ℝ := Fintype.card (QuittingTerminalOutcome ι)
  let M := quittingRewardBound reward
  let targetMass := quittingTerminalOutcomeMass reward
    (quittingStoppingLawSelfOrientedTargetProfile packet n)
    (some packet.terminal)
  let sourceMass := quittingTerminalOutcomeMass reward
    (quittingStoppingLawSelfOrientedSourceProfile packet n)
    (some packet.terminal)
  have hcard : 0 < card := by
    dsimp only [card]
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := packet.rewardBound_pos
  have htargetNonneg : 0 ≤ targetMass :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward
      (quittingStoppingLawSelfOrientedTargetProfile packet n)).1
        (some packet.terminal)
  have hsourceNonneg : 0 ≤ sourceMass :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward
      (quittingStoppingLawSelfOrientedSourceProfile packet n)).1
        (some packet.terminal)
  have hnegativeBound : -reward packet.terminal packet.owner.1 ≤ M := by
    rw [← abs_of_neg hrewardNegative]
    exact abs_reward_le_quittingRewardBound reward packet.terminal
      packet.owner.1
  have hbound := packet.atom_bound n
  change packet.charge / 4 ≤ card *
      ((targetMass - sourceMass) * reward packet.terminal packet.owner.1)
    at hbound
  have hproductLe :
      (targetMass - sourceMass) * reward packet.terminal packet.owner.1 ≤
        sourceMass * M := by
    calc
      (targetMass - sourceMass) * reward packet.terminal packet.owner.1 =
          (sourceMass - targetMass) *
            (-reward packet.terminal packet.owner.1) := by ring
      _ ≤ sourceMass * (-reward packet.terminal packet.owner.1) := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (neg_nonneg.mpr hrewardNegative.le)
      _ ≤ sourceMass * M := by
        exact mul_le_mul_of_nonneg_left hnegativeBound hsourceNonneg
  have htotal : packet.charge / 4 ≤ card * (sourceMass * M) :=
    hbound.trans (mul_le_mul_of_nonneg_left hproductLe hcard.le)
  unfold quittingStoppingLawSelfOrientedMassLower
  apply (div_le_iff₀ (mul_pos hcard hMpos)).2
  change packet.charge / 4 ≤ sourceMass * (card * M)
  calc
    packet.charge / 4 ≤ card * (sourceMass * M) := htotal
    _ = sourceMass * (card * M) := by ring


end GameTheory
