/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.ProductRootLawSupport

/-!
# Zero-singleton behavioral-law product base

These declarations expose the product-base and exact-realization consequences
of a joint terminal semantic/law carrier point. They do not assert a descent
theorem.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A point of the joint carrier has one sequence converging simultaneously
in its semantic-pair and complete-law coordinates. -/
theorem exists_behaviorProfile_sequence_joint_tendsto_of_mem_terminalSemanticLawCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      Tendsto (fun n =>
        (quittingTerminalSemanticPair reward (profiles n),
          quittingTerminalOutcomeMass reward (profiles n)))
        atTop (nhds point) := by
  rw [quittingTerminalSemanticLawCarrier, mem_closure_iff_seq_limit] at hpoint
  obtain ⟨points, hpoints, hpointsTendsto⟩ := hpoint
  choose profiles hprofiles using hpoints
  refine ⟨profiles, ?_⟩
  simpa only [hprofiles] using hpointsTendsto

/-- Zero Never and singleton mass at a joint carrier point give one exact
product-law root with two distinct sure quitters.  Every supported coalition
of that law literally contains the fixed sure pair. -/
theorem exists_twoSureProductRoot_realizing_law_of_mem_terminalSemanticLawCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hNever : point.2 none = 0)
    (hSingleton : ∀ who,
      point.2 (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι) :
    ∃ (root : ι → PMF Bool) (first second : ι),
      first ≠ second ∧
        (root first true).toReal = 1 ∧
        (root second true).toReal = 1 ∧
        (∀ outcome, quittingTerminalOutcomeMass reward
          (quittingOneDateThenNeverProfile reward root) outcome =
            point.2 outcome) ∧
        ∀ terminal : {S : Finset ι // S.Nonempty},
          point.2 (some terminal) ≠ 0 →
            first ∈ terminal.val ∧ second ∈ terminal.val := by
  classical
  obtain ⟨profiles, hjoint⟩ :=
    exists_behaviorProfile_sequence_joint_tendsto_of_mem_terminalSemanticLawCarrier
      reward point hpoint
  have hlaw (outcome : QuittingTerminalOutcome ι) :
      Tendsto (fun n => quittingTerminalOutcomeMass reward (profiles n) outcome)
        atTop (nhds (point.2 outcome)) :=
    (((continuous_apply outcome).comp continuous_snd).tendsto point).comp hjoint
  obtain ⟨rates, first, second, hne, hfirst, hsecond, hrates0, hrates1,
      hcoalition⟩ :=
    zeroSingletonProductBase_zeroNever_zeroSingleton_law_productBase
      reward profiles point.2 hlaw hNever hSingleton hcard
  let root : ι → PMF Bool := fun who =>
    quittingHazardCoin (rates who) (hrates0 who) (hrates1 who)
  have hrootRate (who : ι) : (root who true).toReal = rates who := by
    simp only [root]
    exact quittingHazardCoin_true_toReal
      (rates who) (hrates0 who) (hrates1 who)
  have hsureFirst : (root first true).toReal = 1 := by
    rw [hrootRate, hfirst]
  have hsureSecond : (root second true).toReal = 1 := by
    rw [hrootRate, hsecond]
  have hlawRoot : ∀ outcome, quittingTerminalOutcomeMass reward
      (quittingOneDateThenNeverProfile reward root) outcome =
        point.2 outcome := by
    intro outcome
    cases outcome with
    | none =>
        rw [productRoot_terminalOutcomeMass_oneDateThenNever_none
          reward root hsureFirst, hNever]
    | some terminal =>
        rw [productRoot_terminalOutcomeMass_oneDateThenNever_some
          reward root hsureFirst terminal,
          zeroSingletonProductBase_coalitionMass_eq_boxCoalition]
        have hrateFunction : (fun who => (root who true).toReal) = rates :=
          funext hrootRate
        rw [hrateFunction]
        exact (hcoalition terminal).symm
  refine ⟨root, first, second, hne, hsureFirst, hsureSecond, hlawRoot, ?_⟩
  intro terminal hsupported
  exact terminalLaw_supportedCoalition_contains_twoSureQuitters
    reward point.2 root hsureFirst hsureSecond hlawRoot terminal hsupported

/-- Under strict singleton margins, one fixed two-sure root realizes the
carrier point both as root-then-Never and as stationary repetition. -/
theorem exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hNever : point.2 none = 0)
    (hSingleton : ∀ who,
      point.2 (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι)
    (hstrict : ∀ who,
      reward (quittingSingletonTerminal who) who < point.1.2 who) :
    ∃ (root : ι → PMF Bool) (first second : ι),
      first ≠ second ∧
        (root first true).toReal = 1 ∧
        (root second true).toReal = 1 ∧
        quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root) = point.1 ∧
        quittingTerminalOutcomeMass reward
          (quittingOneDateThenNeverProfile reward root) = point.2 ∧
        quittingTerminalSemanticPair reward
          (quittingStationaryProfile reward root) = point.1 ∧
        quittingTerminalOutcomeMass reward
          (quittingStationaryProfile reward root) = point.2 := by
  obtain ⟨profiles, hjoint⟩ :=
    exists_behaviorProfile_sequence_joint_tendsto_of_mem_terminalSemanticLawCarrier
      reward point hpoint
  have hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds point.1) := (continuous_fst.tendsto point).comp hjoint
  have hlaw (outcome : QuittingTerminalOutcome ι) : Tendsto
      (fun n => quittingTerminalOutcomeMass reward (profiles n) outcome)
      atTop (nhds (point.2 outcome)) :=
    (((continuous_apply outcome).comp continuous_snd).tendsto point).comp hjoint
  obtain ⟨bound, -, hreward⟩ := exists_quittingRewardBound reward
  obtain ⟨root, first, second, hne, hfirst, hsecond, hpair, hlawRoot⟩ :=
    exists_twoSureProductRootThenNever_realizing_semantics_of_strictSingletonMargin
      reward profiles point.2 hlaw hNever hSingleton hcard hreward point.1
        hsemantic hstrict
  have hstationaryPair :=
    quittingTerminalSemanticPair_stationary_eq_oneDateThenNever_of_twoSureQuitters
      reward root hne hfirst hsecond
  have hstationaryLaw :=
    quittingTerminalOutcomeMass_stationary_eq_oneDateThenNever_of_sureQuitter
      reward root hfirst
  exact ⟨root, first, second, hne, hfirst, hsecond, hpair, funext hlawRoot,
    hstationaryPair.trans hpair, hstationaryLaw.trans (funext hlawRoot)⟩

/-- Under nonstrict singleton margins, one all-Continue row followed by the
same two-sure product root realizes the joint carrier point exactly. -/
theorem exists_twoSurePaddedProductRoot_realizing_jointCarrierPoint_of_margin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hNever : point.2 none = 0)
    (hSingleton : ∀ who,
      point.2 (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι)
    (hmargin : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ point.1.2 who) :
    ∃ (root : ι → PMF Bool) (first second : ι),
      first ≠ second ∧
        (root first true).toReal = 1 ∧
        (root second true).toReal = 1 ∧
        quittingTerminalSemanticPair reward
          (oneDateProductPaddedOneDateProfile reward 1 root) = point.1 ∧
        quittingTerminalOutcomeMass reward
          (oneDateProductPaddedOneDateProfile reward 1 root) = point.2 := by
  obtain ⟨profiles, hjoint⟩ :=
    exists_behaviorProfile_sequence_joint_tendsto_of_mem_terminalSemanticLawCarrier
      reward point hpoint
  have hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds point.1) := (continuous_fst.tendsto point).comp hjoint
  have hlaw (outcome : QuittingTerminalOutcome ι) : Tendsto
      (fun n => quittingTerminalOutcomeMass reward (profiles n) outcome)
      atTop (nhds (point.2 outcome)) :=
    (((continuous_apply outcome).comp continuous_snd).tendsto point).comp hjoint
  obtain ⟨bound, -, hreward⟩ := exists_quittingRewardBound reward
  obtain ⟨root, first, second, hne, hfirst, hsecond, hpair, hlawRoot⟩ :=
    exists_twoSurePaddedProductRoot_realizing_semantics_of_singletonMargin
      reward profiles point.2 hlaw hNever hSingleton hcard hreward point.1
        hsemantic hmargin
  exact ⟨root, first, second, hne, hfirst, hsecond, hpair, funext hlawRoot⟩

end GameTheory
