/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CausalTailEscapeMaxAbsorptionCore
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashNearMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumLawFiniteAtom
import Research.Quitting.UniqueAllContinueCapStackNoGo

/-!
# Minimum-law causal suffix dispatch and inert cap stacks

This module consumes a same-point positive causal suffix atom through the
maximal-cap dispatch. It retains either a one-step positive punishment charge
or an arbitrarily deep literal all-Continue, zero-charge, law-invariant stack.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-! ## Same-point causal-atom consumption -/

/-- The strategic output obtained by applying the first maximal-cap prefix to
one actual positive row selected from a causal suffix-atom packet.

The retained exact cap stack is longer than any requested depth.  The
positive-charge arm is a one-step exact punishment-floor prefix.  It does not
assert that the resulting behavioral profile is globally cap--Nash or uniform.
In the other arm the same retained stack is literally all-Continue, has zero
charge, and fixes the full semantic pair and terminal law. -/
structure QuittingMinimumLawCausalSuffixMaximalCapDispatch
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (requestedDepth : ℕ) where
  chronologyIndex : ℕ
  profile : (quittingGame reward).BehaviorProfile
  stage : ℕ
  roots : List (iota → PMF Bool)
  roots_length : roots.length = chronologyIndex + 1
  requestedDepth_lt_roots_length : requestedDepth < roots.length
  rootStack : IsQuittingCapNashRootStack reward roots profile
  pointAtom_pos : 0 < point.2 (some atom.terminal)
  sourceAtom_pos :
    0 < quittingStageCoalitionMass reward profile stage atom.terminal
  shiftedSourceAtom_pos :
    0 < quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward roots profile)
      (chronologyIndex + 1 + stage) atom.terminal
  oneStepCharge_retainingAtom_or_uniqueAllContinue :
    (0 < (quittingMaximalCapPrefixPunishmentFloorPrefix
          reward profile 1).charge ∧
        0 < quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward profile 1)
          (1 + stage) atom.terminal) ∨
      ((∀ candidate : iota → PMF Bool,
        IsεQuittingRootNash reward
            (quittingTerminalSemanticPair reward profile).2 0 candidate →
          candidate = (quittingAllContinueRoot : iota → PMF Bool)) ∧
        roots = List.replicate roots.length
          (quittingAllContinueRoot : iota → PMF Bool) ∧
        quittingCapNashStackAbsorptionSum roots = 0 ∧
        quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots profile) =
          quittingTerminalSemanticPair reward profile ∧
        quittingTerminalOutcomeMass reward
            (quittingLiteralRootStackProfile reward roots profile) =
          quittingTerminalOutcomeMass reward profile)

/-- A causal suffix-atom packet has an actual literal positive row at which
the first maximal exact cap root either gives positive punishment-prefix
charge while retaining that same row, or the exact cap--Nash correspondence
is the singleton all-Continue root.

The selected coalition is exactly the finite atom of `point`; neither the
terminal law nor the behavioral cap is reprojected.  The selected source stack
can be required to exceed any prescribed finite depth. -/
theorem QuittingMinimumLawCausalSuffixAtom.nonempty_maximalCapDispatch
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (requestedDepth : ℕ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum point.1) :
    Nonempty
      (QuittingMinimumLawCausalSuffixMaximalCapDispatch
        reward point atom requestedDepth) := by
  obtain ⟨profiles, _cutoff, mark, roots, _hprofiles, hlength,
      hstack, _hdebt, heventual⟩ := atom.chronology
  rw [eventually_atTop] at heventual
  obtain ⟨first, hfirst⟩ := heventual
  let index := max first requestedDepth
  have hrow := hfirst index (le_max_left first requestedDepth)
  let profile := profiles index
  let stage := mark index
  let selectedRoots := roots index
  have hselectedLength : selectedRoots.length = index + 1 := by
    simpa only [selectedRoots] using hlength index
  have hdepth : requestedDepth < selectedRoots.length := by
    rw [hselectedLength]
    dsimp only [index]
    omega
  have hselectedStack :
      IsQuittingCapNashRootStack reward selectedRoots profile := by
    simpa only [selectedRoots, profile] using hstack index
  have hsourceAtom : 0 <
      quittingStageCoalitionMass reward profile stage atom.terminal := by
    simpa only [profile, stage] using hrow.2.2.1
  have hshiftedAtom : 0 < quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward selectedRoots profile)
      (index + 1 + stage) atom.terminal := by
    simpa only [selectedRoots, profile, stage] using hrow.2.2.2
  have hdispatch :=
    maximalCapPrefix_positivePunishmentCharge_retainingAtom_or_uniqueAllContinue
      reward point.1 profile stage atom.terminal hminimum hminimumPositive
        hsourceAtom
  have hstrongDispatch :
      (0 < (quittingMaximalCapPrefixPunishmentFloorPrefix
            reward profile 1).charge ∧
          0 < quittingStageCoalitionMass reward
            (quittingMaximalCapPrefixProfile reward profile 1)
            (1 + stage) atom.terminal) ∨
        ((∀ candidate : iota → PMF Bool,
            IsεQuittingRootNash reward
                (quittingTerminalSemanticPair reward profile).2 0 candidate →
              candidate = (quittingAllContinueRoot : iota → PMF Bool)) ∧
          selectedRoots = List.replicate selectedRoots.length
            (quittingAllContinueRoot : iota → PMF Bool) ∧
          quittingCapNashStackAbsorptionSum selectedRoots = 0 ∧
          quittingTerminalSemanticPair reward
              (quittingLiteralRootStackProfile reward selectedRoots profile) =
            quittingTerminalSemanticPair reward profile ∧
          quittingTerminalOutcomeMass reward
              (quittingLiteralRootStackProfile reward selectedRoots profile) =
            quittingTerminalOutcomeMass reward profile) := by
    rcases hdispatch with hpositive | hunique
    · exact Or.inl hpositive
    · right
      have hstackData :=
        capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
          reward profile selectedRoots hunique hselectedStack
      have hcharge :=
        capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap
          reward profile selectedRoots hunique hselectedStack
      have hlaw :=
        capNashRootStack_terminalOutcomeMass_eq_of_unique_terminalCap
          reward profile selectedRoots hunique hselectedStack
      exact ⟨hunique, hstackData.1, hcharge, hstackData.2, hlaw⟩
  exact ⟨{
    chronologyIndex := index
    profile := profile
    stage := stage
    roots := selectedRoots
    roots_length := hselectedLength
    requestedDepth_lt_roots_length := hdepth
    rootStack := hselectedStack
    pointAtom_pos := atom.terminalMass_pos
    sourceAtom_pos := hsourceAtom
    shiftedSourceAtom_pos := hshiftedAtom
    oneStepCharge_retainingAtom_or_uniqueAllContinue := hstrongDispatch }⟩

/-- In a punishment-normal quitting game with no uniform-equilibrium payoff,
every supplied globally minimizing joint-law point has one same-point finite
atom whose actual causal rows satisfy the maximal-cap dispatch beyond every
prescribed finite depth.

This is a local exact-prefix alternative.  Its positive-charge branch is not
a global cap--Nash or uniform-equilibrium conclusion. -/
theorem exists_minimumLawCausalSuffixMaximalCapDispatch_of_punishmentNormal_of_not_uniform
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (hno : ¬∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (point : QuittingTerminalSemanticLawPoint iota)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ atom : QuittingMinimumLawCausalSuffixAtom reward point,
      ∀ requestedDepth,
        Nonempty
          (QuittingMinimumLawCausalSuffixMaximalCapDispatch
            reward point atom requestedDepth) := by
  obtain ⟨atom⟩ :=
    nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff
      reward hno hnormal point hpoint hminimum
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr
      hno
  have hcarrier := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hminimumValue : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward :=
    (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      point.1 hcarrier hminimum).symm
  have hminimumPositive : 0 <
      quittingTerminalSemanticDebtSum point.1 := by
    rw [hminimumValue]
    exact hinf
  exact ⟨atom, fun requestedDepth ↦ atom.nonempty_maximalCapDispatch
    reward point requestedDepth hminimum hminimumPositive⟩

/-! ## Eventual minimum-cap freeze -/

/-- An arbitrarily deep exact source stack selected from a causal atom packet
after the near-minimum cap-freezing radius has been entered.

Every stored equality concerns the same literal suffix profile, exact root
word, and finite atom.  The stack is inert; this structure does not assert
that an inert stack yields a uniform-equilibrium payoff or a contradiction. -/
structure QuittingMinimumLawCausalSuffixInertCapStack
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (requestedDepth : ℕ) where
  chronologyIndex : ℕ
  profile : (quittingGame reward).BehaviorProfile
  stage : ℕ
  roots : List (iota → PMF Bool)
  roots_length : roots.length = chronologyIndex + 1
  requestedDepth_lt_roots_length : requestedDepth < roots.length
  rootStack : IsQuittingCapNashRootStack reward roots profile
  pointAtom_pos : 0 < point.2 (some atom.terminal)
  sourceAtom_pos :
    0 < quittingStageCoalitionMass reward profile stage atom.terminal
  shiftedSourceAtom_pos :
    0 < quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward roots profile)
      (chronologyIndex + 1 + stage) atom.terminal
  cap_uniqueAllContinue : ∀ candidate : iota → PMF Bool,
    IsεQuittingRootNash reward
        (quittingTerminalSemanticPair reward profile).2 0 candidate →
      candidate = (quittingAllContinueRoot : iota → PMF Bool)
  roots_eq_replicate_allContinue :
    roots = List.replicate roots.length
      (quittingAllContinueRoot : iota → PMF Bool)
  absorptionSum_eq_zero : quittingCapNashStackAbsorptionSum roots = 0
  semanticPair_eq :
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots profile) =
      quittingTerminalSemanticPair reward profile
  terminalOutcomeMass_eq :
    quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward roots profile) =
      quittingTerminalOutcomeMass reward profile

/-- Near-minimum cap freezing consumes the positive-charge arm of the causal
packet dispatch.  Beyond every prescribed finite depth, one of the packet's
actual source-matched exact stacks is literally replicated all-Continue,
zero-charge, and invariant in both semantic and complete terminal-law
coordinates, while retaining the same positive finite atom. -/
theorem QuittingMinimumLawCausalSuffixAtom.nonempty_inertCapStack
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (requestedDepth : ℕ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum point.1) :
    Nonempty
      (QuittingMinimumLawCausalSuffixInertCapStack
        reward point atom requestedDepth) := by
  obtain ⟨epsilon, hepsilon, hfreeze⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum point.1)
        hminimumPositive hminimum
  obtain ⟨profiles, _cutoff, mark, roots, hprofiles, hlength,
      hstack, _hdebt, hatomEventually⟩ := atom.chronology
  have hpairTendsto : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds point.1) :=
    continuous_fst.continuousAt.tendsto.comp hprofiles
  have hdebtTendsto : Tendsto
      (fun n ↦ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n)))
      atTop (nhds (quittingTerminalSemanticDebtSum point.1)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hpairTendsto
  have hnearEventually : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) <
        quittingTerminalSemanticDebtSum point.1 + epsilon :=
    (tendsto_order.1 hdebtTendsto).2
      (quittingTerminalSemanticDebtSum point.1 + epsilon) (by linarith)
  have hdataEventually := hatomEventually.and hnearEventually
  rw [eventually_atTop] at hdataEventually
  obtain ⟨first, hfirst⟩ := hdataEventually
  let index := max first requestedDepth
  have hdata := hfirst index (le_max_left first requestedDepth)
  let profile := profiles index
  let stage := mark index
  let selectedRoots := roots index
  have hselectedLength : selectedRoots.length = index + 1 := by
    simpa only [selectedRoots] using hlength index
  have hdepth : requestedDepth < selectedRoots.length := by
    rw [hselectedLength]
    dsimp only [index]
    omega
  have hselectedStack :
      IsQuittingCapNashRootStack reward selectedRoots profile := by
    simpa only [selectedRoots, profile] using hstack index
  have hsourceAtom : 0 <
      quittingStageCoalitionMass reward profile stage atom.terminal := by
    simpa only [profile, stage] using hdata.1.2.2.1
  have hshiftedAtom : 0 < quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward selectedRoots profile)
      (index + 1 + stage) atom.terminal := by
    simpa only [selectedRoots, profile, stage] using hdata.1.2.2.2
  have hprofileMem : quittingTerminalSemanticPair reward profile ∈
      quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward profile
  have hunique : ∀ candidate : iota → PMF Bool,
      IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward profile).2 0 candidate →
        candidate = (quittingAllContinueRoot : iota → PMF Bool) := by
    exact hfreeze (quittingTerminalSemanticPair reward profile) hprofileMem
      (by simpa only [profile] using hdata.2.le)
  have hstackData :=
    capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
      reward profile selectedRoots hunique hselectedStack
  have hcharge :=
    capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap
      reward profile selectedRoots hunique hselectedStack
  have hlaw :=
    capNashRootStack_terminalOutcomeMass_eq_of_unique_terminalCap
      reward profile selectedRoots hunique hselectedStack
  exact ⟨{
    chronologyIndex := index
    profile := profile
    stage := stage
    roots := selectedRoots
    roots_length := hselectedLength
    requestedDepth_lt_roots_length := hdepth
    rootStack := hselectedStack
    pointAtom_pos := atom.terminalMass_pos
    sourceAtom_pos := hsourceAtom
    shiftedSourceAtom_pos := hshiftedAtom
    cap_uniqueAllContinue := hunique
    roots_eq_replicate_allContinue := hstackData.1
    absorptionSum_eq_zero := hcharge
    semanticPair_eq := hstackData.2
    terminalOutcomeMass_eq := hlaw }⟩

/-- Punishment-normality and failure of uniform-payoff existence select one
finite atom at every supplied minimum joint-law point.  The checked positive
infimum equivalence then makes that same atom admit arbitrarily deep literal
inert source stacks.

The conclusion is an inert-stack boundary, not a uniform-payoff or
contradiction theorem. -/
theorem exists_minimumLawCausalSuffixInertCapStack_of_punishmentNormal_of_not_uniform
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (hno : ¬∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (point : QuittingTerminalSemanticLawPoint iota)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ atom : QuittingMinimumLawCausalSuffixAtom reward point,
      ∀ requestedDepth,
        Nonempty
          (QuittingMinimumLawCausalSuffixInertCapStack
            reward point atom requestedDepth) := by
  obtain ⟨atom⟩ :=
    nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff
      reward hno hnormal point hpoint hminimum
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr
      hno
  have hcarrier := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hminimumValue : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward :=
    (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      point.1 hcarrier hminimum).symm
  have hminimumPositive : 0 <
      quittingTerminalSemanticDebtSum point.1 := by
    rw [hminimumValue]
    exact hinf
  exact ⟨atom, fun requestedDepth ↦ atom.nonempty_inertCapStack
    reward point requestedDepth hminimum hminimumPositive⟩


end GameTheory
