/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.ControllerTester.ControllerValue

/-!
# Closed invariant barrier duality for the controller--tester value

This module gives the target-free controller value its exact closed
forward-invariant-set dual. A certificate lives inside the compact reward box,
contains the all-Continue Never boundary, is invariant under every product
root prefix, and carries a maximum all-behavior cap-debt floor.

The canonical terminal-semantic carrier is a certificate at the exact value.
Every other certificate contains that carrier, so it cannot certify a larger
floor. A positive floor yields an executable behavioral deviation at every
strictly smaller margin; no best-response supremum is assumed attained.
-/

noncomputable section

namespace GameTheory

open Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A closed forward-invariant maximum-debt barrier inside the canonical
compact reward box. -/
structure QuittingControllerClosedInvariantBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (floor : ℝ) where
  barrier : Set (QuittingTerminalSemanticPair ι)
  subset_rewardBox :
    barrier ⊆ quittingTerminalSemanticBox ι (quittingRewardBound reward)
  isClosed : IsClosed barrier
  neverBoundary_mem : quittingNeverBoundarySemanticPair reward ∈ barrier
  prefix_mem : ∀ pair ∈ barrier, ∀ root : ι → PMF Bool,
    quittingTerminalSemanticPrefix reward root pair ∈ barrier
  maximumDebt_floor : ∀ pair ∈ barrier,
    floor ≤ quittingControllerRawMaximumDebt pair

/-- Every finite word evaluated from the Never boundary belongs to a closed
invariant barrier. -/
theorem QuittingControllerClosedInvariantBarrier.finitePrefix_mem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {floor : ℝ}
    (certificate : QuittingControllerClosedInvariantBarrier reward floor)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingFinitePrefixSemanticEval reward roots cutoff
        (quittingNeverBoundarySemanticPair reward) ∈
      certificate.barrier := by
  induction cutoff generalizing roots with
  | zero =>
      simpa [quittingFinitePrefixSemanticEval] using
        certificate.neverBoundary_mem
  | succ cutoff ih =>
      simp only [quittingFinitePrefixSemanticEval]
      exact certificate.prefix_mem _
        (ih (fun time => roots (time + 1))) (roots 0)

/-- Every closed invariant barrier contains the entire compact executable
terminal-semantic carrier. -/
theorem QuittingControllerClosedInvariantBarrier.carrier_subset
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {floor : ℝ}
    (certificate : QuittingControllerClosedInvariantBarrier reward floor) :
    quittingTerminalSemanticCarrier reward ⊆ certificate.barrier := by
  rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
  apply closure_minimal _ certificate.isClosed
  rintro pair ⟨roots, cutoff, rfl⟩
  exact certificate.finitePrefix_mem roots cutoff

/-- The terminal-semantic carrier is the canonical closed invariant barrier
at the exact target-free controller--tester value. -/
def quittingControllerCanonicalBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingControllerClosedInvariantBarrier reward
      (quittingControllerTesterValue reward) where
  barrier := quittingTerminalSemanticCarrier reward
  subset_rewardBox := fun pair hpair =>
    quittingTerminalSemanticCarrier_mem_box reward pair
      (abs_reward_le_quittingRewardBound reward) hpair
  isClosed := isClosed_closure
  neverBoundary_mem := by
    rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
    exact subset_closure ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩
  prefix_mem := fun pair hpair root =>
    quittingTerminalSemanticPrefix_mem_carrier reward root pair hpair
  maximumDebt_floor := fun pair hpair =>
    (quittingControllerTesterValue_eq_minimum_rawMaximumDebt reward).2.2 pair hpair

/-- Exact closed-invariant-set dual: a floor is certifiable precisely when it
does not exceed the compact target-free controller--tester value. -/
theorem nonempty_closedInvariantBarrier_iff_le_controllerTesterValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (floor : ℝ) :
    Nonempty (QuittingControllerClosedInvariantBarrier reward floor) ↔
      floor ≤ quittingControllerTesterValue reward := by
  constructor
  · rintro ⟨certificate⟩
    exact (certificate.maximumDebt_floor
      (quittingControllerTesterMinimizer reward)
      (certificate.carrier_subset
        (quittingControllerTesterMinimizer_mem reward))).trans_eq
          (quittingControllerTesterValue_eq_max_debt reward).symm
  · intro hfloor
    let canonical := quittingControllerCanonicalBarrier reward
    exact ⟨{
      barrier := canonical.barrier
      subset_rewardBox := canonical.subset_rewardBox
      isClosed := canonical.isClosed
      neverBoundary_mem := canonical.neverBoundary_mem
      prefix_mem := canonical.prefix_mem
      maximumDebt_floor := fun pair hpair =>
        hfloor.trans (canonical.maximumDebt_floor pair hpair) }⟩

/-- Literal maximum form of the closed invariant-set dual: the canonical
carrier attains the value and every other certified floor is below it. -/
theorem quittingControllerTesterValue_isGreatest_closedInvariantBarrierFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Nonempty (QuittingControllerClosedInvariantBarrier reward
        (quittingControllerTesterValue reward)) ∧
      ∀ floor,
        Nonempty (QuittingControllerClosedInvariantBarrier reward floor) →
          floor ≤ quittingControllerTesterValue reward := by
  constructor
  · exact ⟨quittingControllerCanonicalBarrier reward⟩
  · intro floor hfloor
    exact (nonempty_closedInvariantBarrier_iff_le_controllerTesterValue
      reward floor).1 hfloor

/-- A positive closed-invariant floor supplies an actual unrestricted
behavioral deviation at every strictly smaller positive margin. Attainment at
the certified floor itself is not asserted. -/
theorem QuittingControllerClosedInvariantBarrier.exists_behavioralDeviation_gain_ge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {floor margin : ℝ}
    (certificate : QuittingControllerClosedInvariantBarrier reward floor)
    (_hmarginPos : 0 < margin) (hmargin : margin < floor)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ who : ι, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward profile who + margin ≤
        quittingTerminalPayoff reward
          (Function.update profile who deviation) who := by
  let pair := quittingTerminalSemanticPair reward profile
  have hpairCarrier : pair ∈ quittingTerminalSemanticCarrier reward :=
    subset_closure ⟨profile, rfl⟩
  have hfloor : floor ≤ quittingControllerRawMaximumDebt pair :=
    certificate.maximumDebt_floor pair
      (certificate.carrier_subset hpairCarrier)
  obtain ⟨who, _hwhoMem, hwho⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty
    (fun player => pair.2 player - pair.1 player)
  have hdebt : floor ≤ quittingTerminalSemanticDebt pair who := by
    unfold quittingControllerRawMaximumDebt
      QuittingBoundaryHolonomy.finitePlayerMax at hfloor
    rw [hwho] at hfloor
    simpa [quittingTerminalSemanticDebt] using hfloor
  let slack := quittingTerminalSemanticDebt pair who - margin
  have hslack : 0 < slack := by
    dsimp only [slack]
    linarith
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward profile who hslack
  refine ⟨who, deviation, ?_⟩
  change floor ≤ quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who at hdebt
  dsimp only [slack, pair, quittingTerminalSemanticDebt,
    quittingTerminalSemanticPair] at hdeviation
  linarith

/-- A positive closed invariant barrier is therefore a literal all-behavior
terminal exploitability obstruction, without a maximizing-deviation axiom. -/
theorem QuittingControllerClosedInvariantBarrier.positiveFloor_forces_gap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {floor : ℝ}
    (certificate : QuittingControllerClosedInvariantBarrier reward floor)
    (_hfloor : 0 < floor) :
    ∀ margin, 0 < margin → margin < floor →
      ∀ profile : (quittingGame reward).BehaviorProfile,
        ∃ who : ι, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
          quittingTerminalPayoff reward profile who + margin ≤
            quittingTerminalPayoff reward
              (Function.update profile who deviation) who := by
  intro margin hmarginPos hmargin profile
  exact certificate.exists_behavioralDeviation_gain_ge
    hmarginPos hmargin profile

end GameTheory
