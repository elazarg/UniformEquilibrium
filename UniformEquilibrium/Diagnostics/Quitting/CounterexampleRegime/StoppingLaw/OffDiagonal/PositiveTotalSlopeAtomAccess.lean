/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.Atom.ContinuePrefixAccess
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.PositiveTotalSlopeEndpoint

/-!
# Source-relative positive-slope amplification with mover-preserving atom access

The full-reset endpoint theorem already retains a supplied positive-slope mover,
its complete unilateral replacement, and a fixed positive off-diagonal atom
alternative.  The atom chronology places that same literal atom suffix after
arbitrarily long exact Nash-root stacks.

This module joins those two interfaces without changing the mover or the
frontier rank.

* Every strict lower bound on the total tangent slope is eventually a lower
  bound on the full endpoint's total-debt excursion from the actual source,
  not only from the limiting minimum.
* The supplied mover has a fixed positive literal full-reset payoff gain.
* One exact-prefix chronology ending at the same rank's atom source can be
  selected while retaining that mover.
* After forcing the mover to Continue through the prefix, the atom remains
  visible with fixed positive charge.

The resulting passport is source- and rank-matched.  It is not a
punishment-floor capacity rebase: neither the full endpoint nor the atom source
is identified with the target of the near-maximal admissible incoming path.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open Math.SurvivalWeightedObstruction
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleStoppingLawFrontier

/-- **Source-relative scale-free endpoint amplification.**

Every threshold strictly below the limiting total tangent slope is eventually
realized as total-debt growth from the actual source profile to the literal
full reset endpoint at the same frontier rank. -/
theorem eventually_fullReset_sourceRelative_totalDebtChange_of_lt_positiveTotalSlope
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (eta : ℝ)
    (heta : eta < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤ quittingTerminalSemanticDebtSum
          (frontier.fullResetPair mover rank) -
        quittingTerminalSemanticDebtSum (frontier.sourcePair rank) := by
  have hsumTendsto : Tendsto (fun rank ↦ ∑ observer,
      quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) observer)
      atTop (nhds (∑ observer, frontier.tangent mover observer)) :=
    tendsto_finsetSum Finset.univ fun observer _ ↦
      frontier.tangent_tendsto mover observer
  filter_upwards [hsumTendsto.eventually (Ioi_mem_nhds heta)] with rank hrank
  exact hrank.le.trans
    (frontier.sum_normalizedDebtDirection_le_fullReset_totalDebtChange
      mover rank)

/-- The literal full-reset deviation by any supplied active mover eventually
has a fixed source-unit gain. -/
theorem eventually_baseDebt_quarter_le_fullResetPrescribedGain
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebt frontier.base mover.1 / 4 ≤
        frontier.fullResetPrescribedGain mover rank := by
  have hgain : Tendsto (fun rank ↦ frontier.fullResetPrescribedGain mover rank)
      atTop (nhds (-frontier.tangent mover mover.1)) := by
    have htangent := (frontier.tangent_tendsto mover mover.1).neg
    change Tendsto (fun rank ↦
      -quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) mover.1)
      atTop (nhds (-frontier.tangent mover mover.1)) at htangent
    apply htangent.congr'
    exact Eventually.of_forall fun rank ↦
      (frontier.fullResetPrescribedGain_eq_neg_normalizedDebtDirection
        mover rank).symm
  have hthreshold : quittingTerminalSemanticDebt frontier.base mover.1 / 4 <
      -frontier.tangent mover mover.1 := by
    have hdiagonal := frontier.tangent_diagonal mover
    linarith
  exact (hgain.eventually (Ioi_mem_nhds hthreshold)).mono fun _ h ↦ h.le

/-- Build the exact-prefix atom chronology while preserving a supplied active
mover and the fixed atom column selected for that mover. -/
theorem exists_atomExactPrefixChronology_of_mover
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    ∃ chronology : QuittingStoppingLawAtomExactPrefixChronology frontier,
      chronology.mover = mover := by
  classical
  obtain ⟨observer, charge, hobserver, _hpositive, _hchargeEq,
      hcharge, hatom⟩ := frontier.exists_fixedAtomAlternative_of_mover mover
  have hstackChoice : ∀ rank : ℕ,
      ∃ roots : List (ι → PMF Bool),
        roots.length = rank + 1 ∧
          IsQuittingLiteralExactRootStack reward roots
            (frontier.profiles (frontier.subseq rank)) := by
    intro rank
    exact exists_quittingLiteralExactRootStack reward
      (frontier.profiles (frontier.subseq rank)) (rank + 1)
  choose roots hrootsLength hrootsExact using hstackChoice
  have htailPair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward
        (frontier.profiles (frontier.subseq rank))) atTop
      (nhds frontier.base) :=
    frontier.profiles_tendsto.comp frontier.subseq_strictMono.tendsto_atTop
  have htailDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (frontier.profiles (frontier.subseq rank)))) atTop
      (nhds (quittingTerminalSemanticDebtSum frontier.base)) :=
    continuous_quittingTerminalSemanticDebtSum.tendsto frontier.base |>.comp
      htailPair
  let prefixDebt : ℕ → ℝ := fun rank ↦
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward (roots rank)
          (frontier.profiles (frontier.subseq rank))))
  let tailDebt : ℕ → ℝ := fun rank ↦
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
  have hgap : Tendsto (fun rank ↦
      tailDebt rank - quittingTerminalSemanticDebtSum frontier.base)
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _ : ℕ ↦ quittingTerminalSemanticDebtSum frontier.base)
        atTop (nhds (quittingTerminalSemanticDebtSum frontier.base)) :=
      tendsto_const_nhds
    simpa only [tailDebt, sub_self] using htailDebt.sub hconst
  have hprefixGap : Tendsto (fun rank ↦
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
  have hloss : Tendsto (fun rank ↦ tailDebt rank - prefixDebt rank)
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
  exact ⟨chronology, rfl⟩

/-- One positive-slope mover together with its compact full-endpoint cluster
and an exact-prefix atom chronology using that same mover. -/
structure PositiveTotalSlopeEndpointAtomPassport
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) where
  mover : {who // who ∈ frontier.active}
  totalSlope_pos : 0 < ∑ observer, frontier.tangent mover observer
  endpoint : PositiveTotalSlopeEndpointCluster frontier mover
  chronology : QuittingStoppingLawAtomExactPrefixChronology frontier
  chronology_mover : chronology.mover = mover

/-- Positive total slope yields a mover-preserving endpoint/atom passport. -/
theorem nonempty_positiveTotalSlopeEndpointAtomPassport
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hpositive : ∃ mover,
      0 < ∑ observer, frontier.tangent mover observer) :
    Nonempty (PositiveTotalSlopeEndpointAtomPassport frontier) := by
  obtain ⟨mover, hslope⟩ := hpositive
  obtain ⟨endpoint⟩ :=
    frontier.exists_positiveTotalSlopeEndpointCluster mover hslope
  obtain ⟨chronology, hmover⟩ :=
    frontier.exists_atomExactPrefixChronology_of_mover mover
  exact ⟨{
    mover := mover
    totalSlope_pos := hslope
    endpoint := endpoint
    chronology := chronology
    chronology_mover := hmover }⟩

end QuittingCounterexampleStoppingLawFrontier

namespace PositiveTotalSlopeEndpointAtomPassport

/-- **Same-rank endpoint/atom access.**

At every threshold below the positive total slope, all sufficiently late
frontier ranks simultaneously retain:

* the scale-free total-debt excursion from that rank's actual source to its
  literal full reset endpoint;
* the supplied mover's fixed positive legal full-reset gain; and
* a positive atom alternative at the front of an exact state-matched Nash-root
  stack after one Continue-through deviation by that same mover.

The conjunction uses one actual source rank and one mover throughout. -/
theorem eventually_sourceExcursion_gain_and_continuePrefixAtom
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (passport : PositiveTotalSlopeEndpointAtomPassport frontier)
    (eta : ℝ) (heta : eta <
      ∑ observer, frontier.tangent passport.mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤ quittingTerminalSemanticDebtSum
          (frontier.fullResetPair passport.mover rank) -
        quittingTerminalSemanticDebtSum (frontier.sourcePair rank) ∧
      quittingTerminalSemanticDebt frontier.base passport.mover.1 / 4 ≤
        frontier.fullResetPrescribedGain passport.mover rank ∧
      HasQuittingContinuePrefixDebtSlopeAtomAlternative reward
        (passport.chronology.roots rank)
        (frontier.profiles (frontier.subseq rank)) passport.mover.1
        passport.chronology.observer
        (frontier.bestResponse passport.mover (frontier.subseq rank))
        (passport.chronology.charge / 2) := by
  have hatom := passport.chronology.continuePrefix_atomAlternative_eventually
  rw [passport.chronology_mover] at hatom
  filter_upwards [
    frontier.eventually_fullReset_sourceRelative_totalDebtChange_of_lt_positiveTotalSlope
      passport.mover eta heta,
    frontier.eventually_baseDebt_quarter_le_fullResetPrescribedGain
      passport.mover,
    hatom] with rank hexcursion hgain hatomRank
  exact ⟨hexcursion, hgain, hatomRank⟩

end PositiveTotalSlopeEndpointAtomPassport

end GameTheory
