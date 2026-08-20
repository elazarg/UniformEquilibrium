/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CertifiedForcedOwnerEndpointFlip
import Research.Quitting.MinimumExactNashOneActive

/-!
# Forced-owner endpoint flips on the positive minimum stratum

The signed source-transport residual has one sharp global fence.  At a
positive minimum terminal-semantic pair, an exact Nash root has at most one
positive quitting hazard.  If a positive terminal cylinder contains the
forced owner, that unique possible quitter is already the owner.  Every
distinct outsider is therefore literally pure Continue.

Consequently a strictly negative outsider endpoint gain on the
owner-forced-Continue face can only be the pure-Quit endpoint.  The
pure-Continue endpoint is the outsider's prescribed marginal and has gain
zero.  Thus a certified endpoint flip returned to an exact positive-minimum
Nash row has only the Quit-selected, singleton-support orientation.

This does not return the current observer-absent carrier rows to the minimum
stratum.  It identifies exactly what such a law-preserving return would buy:
the Continue-selected half of the signed residual disappears, and the other
half lands on a literal one-active boundary.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive coalition cylinder through `owner` uses the sole available
positive-hazard slot of an exact Nash root on the positive minimum stratum.
Every distinct outsider is pure Continue. -/
theorem minimumExactNash_positiveCoalition_outsider_isPureContinue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (howner : owner ∈ terminal.val)
    (hne : who ≠ owner)
    (hmass : 0 < quittingRootCoalitionMass root terminal.val) :
    root who = PMF.pure false := by
  have hcard := minimumTerminalSemantic_exactNash_hasSupportCardAtMost_one
    pair root hpair hminimum hpositive hnash
  have hownerQuit : 0 < (root owner true).toReal :=
    hmass.trans_le
      (quittingRootCoalitionMass_le_quitProbability_of_mem
        root terminal.val owner howner)
  have hownerSupport : owner ∈ quittingPositiveHazardSupport root := by
    simp [quittingPositiveHazardSupport, hazardOfRoot, hownerQuit]
  have hwhoNotSupport : who ∉ quittingPositiveHazardSupport root := by
    intro hwhoSupport
    have hpairSubset : ({owner, who} : Finset ι) ⊆
        quittingPositiveHazardSupport root := by
      intro player hplayer
      simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
      rcases hplayer with rfl | rfl
      · exact hownerSupport
      · exact hwhoSupport
    have htwo : 2 ≤ (quittingPositiveHazardSupport root).card := by
      have hcardPair := Finset.card_le_card hpairSubset
      simpa [hne, hne.symm] using hcardPair
    unfold HasQuittingSupportCardAtMost at hcard
    omega
  exact quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport
    root hwhoNotSupport

/-- The same hypotheses force the entire positive root coalition to be the
owner singleton.  Thus a law-preserving causal return would send every
nonsingleton charged atom directly to contradiction. -/
theorem minimumExactNash_positiveCoalition_eq_ownerSingleton
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val)
    (hmass : 0 < quittingRootCoalitionMass root terminal.val) :
    terminal.val = {owner} := by
  ext player
  constructor
  · intro hplayer
    by_contra hne
    have hne' : player ≠ owner := by simpa using hne
    have hpure := minimumExactNash_positiveCoalition_outsider_isPureContinue
      pair root hpair hminimum hpositive hnash terminal owner player
        howner hne' hmass
    have hle := quittingRootCoalitionMass_le_quitProbability_of_mem
      root terminal.val player hplayer
    rw [hpure] at hle
    simp at hle
    linarith
  · intro hplayer
    have heq : player = owner := by simpa using hplayer
    subst player
    exact howner

/-- On such a returned minimum row, a negative pure endpoint at the
owner-Continue face must be Quit.  Continue is already the outsider's
prescribed action and has exactly zero deviation gain. -/
theorem minimumExactNash_continueFaceLoss_forces_quitAction
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner who : ι) (howner : owner ∈ terminal.val)
    (hne : who ≠ owner)
    (hmass : 0 < quittingRootCoalitionMass root terminal.val)
    (action : Bool)
    (hloss : quittingRootDeviationGain reward pair.1
      (Function.update root owner (PMF.pure false)) who
        (PMF.pure action) < 0) :
    action = true := by
  have hwho := minimumExactNash_positiveCoalition_outsider_isPureContinue
    pair root hpair hminimum hpositive hnash terminal owner who
      howner hne hmass
  cases action with
  | false =>
      exfalso
      let forcedRoot := Function.update root owner (PMF.pure false)
      have hforcedWho : forcedRoot who = PMF.pure false := by
        dsimp only [forcedRoot]
        rw [Function.update_of_ne hne, hwho]
      have hupdate : Function.update forcedRoot who (PMF.pure false) =
          forcedRoot := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp [hforcedWho]
        · simp [hplayer]
      unfold quittingRootDeviationGain at hloss
      change quittingRootExpectedPayoff reward pair.1
          (Function.update forcedRoot who (PMF.pure false)) who -
        quittingRootSuccessorPayoff reward pair.1 forcedRoot who < 0 at hloss
      rw [hupdate] at hloss
      unfold quittingRootSuccessorPayoff at hloss
      linarith
  | true => rfl

end GameTheory
