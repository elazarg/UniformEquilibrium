/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.SlopeFrontier
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.LiteralRootStackSurvival
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack

/-!
# Exact-prefix chronology ending at the stopping-law atom suffix

The independently optimized exact-dynamic-debt tail need not be identified
with the minimum terminal-semantic point in order to state-match the literal
off-diagonal atom.  There is a more direct, game-specific construction.

Every literal profile in the common-base tangent sequence admits an exact
finite Nash-root stack of any prescribed depth.  Choosing depth `rank + 1`
gives arbitrarily long executable chronologies ending at the *same literal
suffix* on which the stopping-law atom alternative is evaluated.  Exact Nash
prefixing can only decrease every debt coordinate, while global minimality of
the frontier base bounds the prefixed profile from below.  Since the terminal
suffix debt tends to the minimum, the total debt of the entire prefixed
chronology is squeezed back to the same minimum.

This is not a return theorem for the canonical exact-`D` tail, and it does not
make the atom occur at a bounded distance along one infinite profile.  It does
avoid equating the two independently selected objectives before feeding a
literal atom into a finite state-matched consumer.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open Math.SurvivalWeightedObstruction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A fixed atom column together with arbitrarily long literal exact-Nash
prefix stacks ending at the atom-producing continuation profiles. -/
structure QuittingStoppingLawAtomExactPrefixChronology
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) where
  mover : {who // who ∈ frontier.active}
  observer : ι
  charge : ℝ
  observer_ne_mover : observer ≠ mover.1
  charge_pos : 0 < charge
  roots : ℕ → List (ι → PMF Bool)
  roots_length : ∀ rank, (roots rank).length = rank + 1
  exact_stack : ∀ rank,
    IsQuittingLiteralExactRootStack reward (roots rank)
      (frontier.profiles (frontier.subseq rank))
  atom_eventually : ∀ᶠ rank in atTop,
    HasQuittingStoppingLawDebtSlopeAtomAlternative reward
      (frontier.profiles (frontier.subseq rank)) mover.1 observer
      (frontier.bestResponse mover (frontier.subseq rank)) charge
  prefixDebt_tendsto_minimum :
    Tendsto (fun rank => quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward (roots rank)
          (frontier.profiles (frontier.subseq rank)))))
      atTop (nhds (quittingTerminalSemanticDebtSum frontier.base))
  totalDebtLoss_tendsto_zero :
    Tendsto (fun rank =>
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward (roots rank)
              (frontier.profiles (frontier.subseq rank)))))
      atTop (nhds 0)

namespace QuittingCounterexampleStoppingLawFrontier

/-- Build an exact-prefix chronology from a supplied fixed atom column.  This
is the mover- and observer-preserving form of the chronology constructor. -/
theorem nonempty_atomExactPrefixChronology_of_fixedAlternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (observer : ι) (charge : ℝ)
    (hobserver : observer ≠ mover.1) (hcharge : 0 < charge)
    (hatom : ∀ᶠ rank in atTop,
      HasQuittingStoppingLawDebtSlopeAtomAlternative reward
        (frontier.profiles (frontier.subseq rank)) mover.1 observer
        (frontier.bestResponse mover (frontier.subseq rank)) charge) :
    ∃ chronology : QuittingStoppingLawAtomExactPrefixChronology frontier,
      chronology.mover = mover ∧ chronology.observer = observer ∧
        chronology.charge = charge := by
  classical
  have hstackChoice : ∀ rank : ℕ,
      ∃ roots : List (ι → PMF Bool),
        roots.length = rank + 1 ∧
          IsQuittingLiteralExactRootStack reward roots
            (frontier.profiles (frontier.subseq rank)) := by
    intro rank
    exact exists_quittingLiteralExactRootStack reward
      (frontier.profiles (frontier.subseq rank)) (rank + 1)
  choose roots hrootsLength hrootsExact using hstackChoice
  have htailPair : Tendsto (fun rank =>
      quittingTerminalSemanticPair reward
        (frontier.profiles (frontier.subseq rank))) atTop
      (nhds frontier.base) :=
    frontier.profiles_tendsto.comp frontier.subseq_strictMono.tendsto_atTop
  have htailDebt : Tendsto (fun rank =>
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (frontier.profiles (frontier.subseq rank)))) atTop
      (nhds (quittingTerminalSemanticDebtSum frontier.base)) :=
    continuous_quittingTerminalSemanticDebtSum.tendsto frontier.base |>.comp
      htailPair
  let prefixDebt : ℕ → ℝ := fun rank =>
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward (roots rank)
          (frontier.profiles (frontier.subseq rank))))
  let tailDebt : ℕ → ℝ := fun rank =>
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (frontier.profiles (frontier.subseq rank)))
  have hlower : ∀ rank,
      quittingTerminalSemanticDebtSum frontier.base ≤ prefixDebt rank := by
    intro rank
    apply frontier.base_minimum
    exact quittingTerminalSemanticPair_mem_carrier reward _
  have hupper : ∀ rank, prefixDebt rank ≤ tailDebt rank := by
    intro rank
    simpa only [prefixDebt, tailDebt, quittingTerminalSemanticDebtSum,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDeviationDebt] using
      (sum_quittingTerminalDeviationDebt_literalRootStack_le_terminal
        reward (roots rank) (frontier.profiles (frontier.subseq rank))
        (hrootsExact rank))
  have hgap : Tendsto (fun rank =>
      tailDebt rank - quittingTerminalSemanticDebtSum frontier.base)
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _ : ℕ => quittingTerminalSemanticDebtSum frontier.base)
        atTop (nhds (quittingTerminalSemanticDebtSum frontier.base)) :=
      tendsto_const_nhds
    simpa only [tailDebt, sub_self] using htailDebt.sub hconst
  have hprefixGap : Tendsto (fun rank =>
      prefixDebt rank - quittingTerminalSemanticDebtSum frontier.base)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro rank
      exact sub_nonneg.mpr (hlower rank)
    · intro rank
      exact sub_le_sub_right (hupper rank) _
    · exact hgap
  have hprefixDebt : Tendsto prefixDebt atTop
      (nhds (quittingTerminalSemanticDebtSum frontier.base)) := by
    have hadd := hprefixGap.add_const
      (quittingTerminalSemanticDebtSum frontier.base)
    simpa only [prefixDebt, sub_add_cancel, zero_add] using hadd
  have hloss : Tendsto (fun rank => tailDebt rank - prefixDebt rank)
      atTop (nhds 0) := by
    simpa only [sub_self] using htailDebt.sub hprefixDebt
  let chronology : QuittingStoppingLawAtomExactPrefixChronology frontier := {
    mover := mover
    observer := observer
    charge := charge
    observer_ne_mover := hobserver
    charge_pos := hcharge
    roots := roots
    roots_length := hrootsLength
    exact_stack := hrootsExact
    atom_eventually := hatom
    prefixDebt_tendsto_minimum := hprefixDebt
    totalDebtLoss_tendsto_zero := hloss }
  exact ⟨chronology, rfl, rfl, rfl⟩

/-- **Literal atom-to-chronology adapter.**

The stopping-law atom suffix can be placed after an exact state-matched
Nash-root word whose length tends to infinity.  The complete prefixed
profiles remain asymptotically on the minimum-total-debt stratum.

The result preserves the actual atom-producing suffix and replacement
strategy.  It does not pass to an infinite-path limit, where the terminal
atom could escape to infinity. -/
theorem nonempty_atomExactPrefixChronology
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawAtomExactPrefixChronology frontier) := by
  obtain ⟨mover, observer, charge, hobserver, hcharge, hatom⟩ :=
    frontier.exists_fixedAtomAlternative
  obtain ⟨chronology, _hmover, _hobserver, _hcharge⟩ :=
    frontier.nonempty_atomExactPrefixChronology_of_fixedAlternative mover
      observer charge hobserver hcharge hatom
  exact ⟨chronology⟩

end QuittingCounterexampleStoppingLawFrontier

namespace QuittingStoppingLawAtomExactPrefixChronology

/-- Near-minimality forces the entire finite exact stack to preserve the
opponent-deleted survival clock of every positive-debt player. -/
theorem opponentSurvival_tendsto_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (chronology : QuittingStoppingLawAtomExactPrefixChronology frontier)
    {who : ι} (hwho : who ∈ frontier.active) :
    Tendsto (fun rank =>
      quittingLiteralRootStackOpponentSurvival (chronology.roots rank) who)
      atTop (nhds 1) := by
  let minimumDebt := quittingTerminalSemanticDebt frontier.base who
  let terminalDebt : ℕ → ℝ := fun rank =>
    quittingTerminalDeviationDebt reward
      (frontier.profiles (frontier.subseq rank)) who
  let prefixDebt : ℕ → ℝ := fun rank =>
    quittingTerminalDeviationDebt reward
      (quittingLiteralRootStackProfile reward (chronology.roots rank)
        (frontier.profiles (frontier.subseq rank))) who
  let totalLoss : ℕ → ℝ := fun rank =>
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (frontier.profiles (frontier.subseq rank))) -
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward (chronology.roots rank)
            (frontier.profiles (frontier.subseq rank))))
  let lower := minimumDebt / 2
  have hminimum : 0 < minimumDebt := (frontier.active_iff who).1 hwho
  have hlower : 0 < lower := div_pos hminimum (by norm_num)
  have htailPair : Tendsto (fun rank =>
      quittingTerminalSemanticPair reward
        (frontier.profiles (frontier.subseq rank))) atTop
      (nhds frontier.base) :=
    frontier.profiles_tendsto.comp frontier.subseq_strictMono.tendsto_atTop
  have hterminalDebt : Tendsto terminalDebt atTop (nhds minimumDebt) := by
    have hcoordinate :=
      (continuous_quittingTerminalSemanticDebt who).tendsto frontier.base |>.comp
        htailPair
    change Tendsto (fun rank => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (frontier.profiles (frontier.subseq rank))) who) atTop
      (nhds (quittingTerminalSemanticDebt frontier.base who)) at hcoordinate
    simpa only [terminalDebt, minimumDebt, quittingTerminalDeviationDebt,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair] using hcoordinate
  have heventuallyLower : ∀ᶠ rank in atTop, lower ≤ terminalDebt rank :=
    hterminalDebt.eventually (Ioi_mem_nhds (show lower < minimumDebt by
      dsimp only [lower]
      linarith)) |>.mono fun _ hlt => hlt.le
  have hcoordinateDrop : ∀ rank,
      terminalDebt rank - prefixDebt rank ≤ totalLoss rank := by
    intro rank
    have hnonneg : ∀ other ∈ (Finset.univ : Finset ι),
        0 ≤ quittingTerminalDeviationDebt reward
              (frontier.profiles (frontier.subseq rank)) other -
            quittingTerminalDeviationDebt reward
              (quittingLiteralRootStackProfile reward (chronology.roots rank)
                (frontier.profiles (frontier.subseq rank))) other := by
      intro other _
      exact sub_nonneg.mpr
        (quittingTerminalDeviationDebt_literalRootStack_le_terminal
          reward (chronology.roots rank)
          (frontier.profiles (frontier.subseq rank)) other
          (chronology.exact_stack rank))
    calc
      terminalDebt rank - prefixDebt rank ≤
          ∑ other, (quittingTerminalDeviationDebt reward
                (frontier.profiles (frontier.subseq rank)) other -
              quittingTerminalDeviationDebt reward
                (quittingLiteralRootStackProfile reward (chronology.roots rank)
                  (frontier.profiles (frontier.subseq rank))) other) := by
        exact Finset.single_le_sum hnonneg (Finset.mem_univ who)
      _ = totalLoss rank := by
        dsimp only [totalLoss, terminalDebt, prefixDebt,
          quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt,
          quittingTerminalSemanticPair, quittingTerminalDeviationDebt]
        rw [Finset.sum_sub_distrib]
  have hblockAct : ∀ rank, prefixDebt rank =
      (quittingLiteralTerminalDebtAggregateBlock reward
        (chronology.roots rank)
        (frontier.profiles (frontier.subseq rank)) who).act ()
          (terminalDebt rank) := by
    intro rank
    simpa only [prefixDebt, terminalDebt] using
      (quittingTerminalDeviationDebt_literalRootStack_eq_blockAct
        reward (chronology.roots rank)
        (frontier.profiles (frontier.subseq rank)) who
        (chronology.exact_stack rank))
  have hsurvivalBound : ∀ᶠ rank in atTop,
      1 - quittingLiteralRootStackOpponentSurvival
          (chronology.roots rank) who ≤ totalLoss rank / lower := by
    filter_upwards [heventuallyLower] with rank hrank
    let block := quittingLiteralTerminalDebtAggregateBlock reward
      (chronology.roots rank)
      (frontier.profiles (frontier.subseq rank)) who
    have hkilled : (1 - block.survival) * lower ≤ totalLoss rank :=
      Block.killed_mul_lowerDebt_le_of_debt_sub_act_le
        (block := block) (channel := ()) (debt := terminalDebt rank)
        (lower := lower) (error := totalLoss rank) hrank hlower.le (by
          rw [← hblockAct rank]
          exact hcoordinateDrop rank)
    rw [quittingLiteralTerminalDebtAggregateBlock_survival_eq] at hkilled
    exact (le_div_iff₀ hlower).2 (by simpa [mul_comm] using hkilled)
  have htotalLoss : Tendsto totalLoss atTop (nhds 0) := by
    simpa only [totalLoss] using chronology.totalDebtLoss_tendsto_zero
  have hupper : Tendsto (fun rank => totalLoss rank / lower)
      atTop (nhds 0) := by
    simpa using htotalLoss.div_const lower
  have hsurvivalGap : Tendsto (fun rank =>
      1 - quittingLiteralRootStackOpponentSurvival
        (chronology.roots rank) who) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun rank => sub_nonneg.mpr
        (quittingLiteralRootStackOpponentSurvival_le_one
          (chronology.roots rank) who)
    · exact hsurvivalBound
    · exact hupper
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hrecover := hone.sub hsurvivalGap
  simpa only [sub_sub_cancel, sub_zero] using hrecover

/-- **Two active debts retain the literal atom suffix.**

If the minimum stratum has two distinct positive-debt players, full joint
survival through the arbitrarily long exact prefix stacks tends to one.  Thus
the atom-producing terminal suffix is not merely a formal endpoint: its law
is reached with asymptotically undiminished probability.

The only branch not covered is `frontier.active.card = 1`, where the unique
debtor's own hazards are invisible to its opponent-deleted debt clock. -/
theorem jointSurvival_tendsto_one_of_twoActive
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (chronology : QuittingStoppingLawAtomExactPrefixChronology frontier)
    {first second : ι} (hfirst : first ∈ frontier.active)
    (hsecond : second ∈ frontier.active) (hne : first ≠ second) :
    Tendsto (fun rank =>
      quittingLiteralRootStackJointSurvival (chronology.roots rank))
      atTop (nhds 1) := by
  have hfirstSurvival := chronology.opponentSurvival_tendsto_one hfirst
  have hsecondSurvival := chronology.opponentSurvival_tendsto_one hsecond
  have hproduct : Tendsto (fun rank =>
      quittingLiteralRootStackOpponentSurvival
          (chronology.roots rank) first *
        quittingLiteralRootStackOpponentSurvival
          (chronology.roots rank) second) atTop (nhds 1) := by
    simpa using hfirstSurvival.mul hsecondSurvival
  have hlower : ∀ rank,
      quittingLiteralRootStackOpponentSurvival
          (chronology.roots rank) first *
          quittingLiteralRootStackOpponentSurvival
            (chronology.roots rank) second ≤
        quittingLiteralRootStackJointSurvival (chronology.roots rank) :=
    fun rank => mul_opponentSurvival_le_jointSurvival_of_ne
      (chronology.roots rank) hne
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hproduct
    tendsto_const_nhds hlower (fun rank =>
      quittingLiteralRootStackJointSurvival_le_one
        (chronology.roots rank))

/-- Every player distinct from one positive-debt owner has own-survival
tending to one through the exact prefix stacks.  In the singleton-active
branch this says that only the unique active owner can preempt access to the
terminal atom suffix. -/
theorem ownSurvival_tendsto_one_of_active_ne
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (chronology : QuittingStoppingLawAtomExactPrefixChronology frontier)
    {owner other : ι} (howner : owner ∈ frontier.active)
    (hne : other ≠ owner) :
    Tendsto (fun rank =>
      quittingLiteralRootStackOwnSurvival (chronology.roots rank) other)
      atTop (nhds 1) := by
  have hlower := chronology.opponentSurvival_tendsto_one howner
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower
    tendsto_const_nhds
    (fun rank =>
      quittingLiteralRootStackOpponentSurvival_le_ownSurvival_of_ne
        (chronology.roots rank) hne)
    (fun rank => quittingLiteralRootStackOwnSurvival_le_one
      (chronology.roots rank) other)

/-- **Exhaustive access dichotomy for the exact-prefix atom chronology.**

Either the positive minimum has one active debtor, in which case all other
players' own survival through the full stack tends to one and only that owner
can hide the atom by preemption, or two active debtors force full joint
survival to one and the literal atom suffix remains asymptotically reached.
-/
theorem singletonActive_or_jointSurvival_tendsto_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (chronology : QuittingStoppingLawAtomExactPrefixChronology frontier) :
    (∃ owner : ι,
      frontier.active = {owner} ∧
        ∀ other, other ≠ owner →
          Tendsto (fun rank =>
            quittingLiteralRootStackOwnSurvival
              (chronology.roots rank) other) atTop (nhds 1)) ∨
      ∃ first ∈ frontier.active, ∃ second ∈ frontier.active,
        first ≠ second ∧
          Tendsto (fun rank =>
            quittingLiteralRootStackJointSurvival (chronology.roots rank))
            atTop (nhds 1) := by
  classical
  by_cases hcard : frontier.active.card ≤ 1
  · left
    have hnonempty : frontier.active.Nonempty :=
      ⟨chronology.mover.1, chronology.mover.2⟩
    have hcardPos : 0 < frontier.active.card := Finset.card_pos.mpr hnonempty
    have hcardOne : frontier.active.card = 1 := by omega
    obtain ⟨owner, hactive⟩ := Finset.card_eq_one.mp hcardOne
    refine ⟨owner, hactive, ?_⟩
    intro other hne
    apply chronology.ownSurvival_tendsto_one_of_active_ne
      (owner := owner)
    · rw [hactive]
      simp
    · exact hne
  · right
    have hcardTwo : 1 < frontier.active.card := Nat.lt_of_not_ge hcard
    obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
      Finset.one_lt_card.mp hcardTwo
    exact ⟨first, hfirst, second, hsecond, hne,
      chronology.jointSurvival_tendsto_one_of_twoActive
        hfirst hsecond hne⟩

end QuittingStoppingLawAtomExactPrefixChronology

end GameTheory
