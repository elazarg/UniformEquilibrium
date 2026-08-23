/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.Atom.ContinuePrefixAccess
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.PositiveTotalSlopeEndpoint

/-!
# Mover-preserving atom access for a positive total slope

A positive-total-slope mover has two source-matched finite-rank consequences.
Its literal full reset makes a scale-free total-debt excursion and a fixed
legal mover gain.  A positive off-diagonal recipient of that same mover also
has a common-response atom alternative with vanishing endpoint debt.

The atom source can be placed after arbitrarily long exact Nash-root stacks
without changing the mover, observer, charge, or frontier rank.  This is a
finite passport joining data at one literal source.  The full reset endpoint
is counterfactual: it is not asserted to be a reached continuation of one
infinite chronology, and no return or contradiction is claimed.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleStoppingLawFrontier

/-- A positive-total-slope mover, its compact full-reset endpoint cluster,
and a strong vanishing-debt atom chronology using that same mover and one
fixed off-diagonal observer. -/
structure PositiveTotalSlopeEndpointAtomPassport
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) where
  mover : {who // who ∈ frontier.active}
  totalSlope_pos : 0 < ∑ observer, frontier.tangent mover observer
  endpoint : PositiveTotalSlopeEndpointCluster frontier mover
  observer : ι
  charge : ℝ
  observer_ne_mover : observer ≠ mover.1
  observer_tangent_lower :
    ((∑ who, frontier.tangent mover who) +
        quittingTerminalSemanticDebt frontier.base mover.1) /
        ((Finset.univ.erase mover.1).card : ℝ) ≤
      frontier.tangent mover observer
  charge_eq : charge = 7 * frontier.tangent mover observer / 16
  charge_pos : 0 < charge
  vanishingAtom_eventually : ∀ᶠ rank in atTop,
    HasQuittingStoppingLawVanishingDebtAtomAlternative reward
      (frontier.profiles (frontier.subseq rank)) mover.1 observer
      (frontier.bestResponse mover (frontier.subseq rank)) charge
      (quittingStoppingLawAtomDecoderError charge rank)
  chronology : QuittingStoppingLawAtomExactPrefixChronology frontier
  chronology_mover : chronology.mover = mover
  chronology_observer : chronology.observer = observer
  chronology_charge : chronology.charge = charge

/-- Positive total slope yields the mover-preserving endpoint and atom
passport.  The atom-interface charge is `7/16` of the selected positive
off-diagonal tangent entry. -/
theorem nonempty_positiveTotalSlopeEndpointAtomPassport
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hpositive : ∃ mover,
      0 < ∑ observer, frontier.tangent mover observer) :
    Nonempty (PositiveTotalSlopeEndpointAtomPassport frontier) := by
  obtain ⟨mover, hslope⟩ := hpositive
  obtain ⟨endpoint⟩ :=
    frontier.exists_positiveTotalSlopeEndpointCluster mover hslope
  obtain ⟨observer, charge, hobserver, hobserverLower, hchargeEq, hcharge,
      hvanishing⟩ :=
    frontier.exists_quantitativeStrongVanishingDebtAtomAlternative_of_mover mover
  have hatom : ∀ᶠ rank in atTop,
      HasQuittingStoppingLawDebtSlopeAtomAlternative reward
        (frontier.profiles (frontier.subseq rank)) mover.1 observer
        (frontier.bestResponse mover (frontier.subseq rank)) charge :=
    hvanishing.mono fun _ h =>
      hasDebtSlopeAtomAlternative_of_hasVanishingDebtAtomAlternative
        reward _ mover.1 observer _ charge _ h
  obtain ⟨chronology, hmover, hobserverEq, hchargeChronology⟩ :=
    frontier.nonempty_atomExactPrefixChronology_of_fixedAlternative mover
      observer charge hobserver hcharge hatom
  exact ⟨{
    mover := mover
    totalSlope_pos := hslope
    endpoint := endpoint
    observer := observer
    charge := charge
    observer_ne_mover := hobserver
    observer_tangent_lower := hobserverLower
    charge_eq := hchargeEq
    charge_pos := hcharge
    vanishingAtom_eventually := hvanishing
    chronology := chronology
    chronology_mover := hmover
    chronology_observer := hobserverEq
    chronology_charge := hchargeChronology }⟩

end QuittingCounterexampleStoppingLawFrontier

namespace QuittingCounterexampleStoppingLawFrontier.PositiveTotalSlopeEndpointAtomPassport

/-- At every threshold below the positive total slope, sufficiently late
ranks simultaneously retain the literal source-relative endpoint excursion,
the mover's legal full-reset gain, the strong common-response atom, and its
Continue-prefix access through the exact stack at that same rank. -/
theorem eventually_sourceExcursion_gain_and_atomAccess
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (passport : frontier.PositiveTotalSlopeEndpointAtomPassport)
    (eta : ℝ) (heta : eta <
      ∑ observer, frontier.tangent passport.mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤ quittingTerminalSemanticDebtSum
          (frontier.fullResetPair passport.mover rank) -
        quittingTerminalSemanticDebtSum (frontier.sourcePair rank) ∧
      quittingTerminalSemanticDebt frontier.base passport.mover.1 / 4 ≤
        frontier.fullResetPrescribedGain passport.mover rank ∧
      HasQuittingStoppingLawVanishingDebtAtomAlternative reward
        (frontier.profiles (frontier.subseq rank)) passport.mover.1
        passport.observer
        (frontier.bestResponse passport.mover (frontier.subseq rank))
        passport.charge
        (quittingStoppingLawAtomDecoderError passport.charge rank) ∧
      HasQuittingContinuePrefixDebtSlopeAtomAlternative reward
        (passport.chronology.roots rank)
        (frontier.profiles (frontier.subseq rank)) passport.mover.1
        passport.observer
        (frontier.bestResponse passport.mover (frontier.subseq rank))
        (passport.charge / 2) := by
  have hatom := passport.chronology.continuePrefix_atomAlternative_eventually
  rw [passport.chronology_mover, passport.chronology_observer,
    passport.chronology_charge] at hatom
  filter_upwards [
    frontier.eventually_fullReset_sourceRelative_totalDebtChange_of_lt_totalSlope
      passport.mover eta heta,
    frontier.eventually_baseDebt_quarter_le_fullResetPrescribedGain
      passport.mover,
    passport.vanishingAtom_eventually,
    hatom] with rank hexcursion hgain hvanishing hatomRank
  exact ⟨hexcursion, hgain, hvanishing, hatomRank⟩

end QuittingCounterexampleStoppingLawFrontier.PositiveTotalSlopeEndpointAtomPassport

end GameTheory
