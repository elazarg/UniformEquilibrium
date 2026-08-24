/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidResetPayoffAlignment

/-!
# Endpoint edges at a pair-base paid reset payoff

The returned fixed-law reset face and its literal stationary paid target have
the same prescribed payoff `U`.  If `U` dominates the behavioral punishment
floor, finite one-stage Nash existence at tail `U` produces an exact
floor-admissible predecessor edge.  Its charge is positive unless its root is
literally all-Continue.

The all-Continue alternative is exact: it occurs precisely when every
singleton quitting reward is at most `U`.  A paid first-disagreement row does
not contradict this condition: it compares pure-time deviations against the
stationary source, not a singleton Quit against the continuation `U`, and it
may also be paid by a later or Never witness.

For the unconditional four-player pair-base construction, floor domination
is already known on both complementary induced-Nash coordinates.  Thus the
only additional alternative is a strict punishment-floor violation localized
to one of the two forced-Quit base players.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- One exact floor-admissible predecessor at the displayed tail payoff,
with the exhaustive positive-charge/all-Continue alternative. -/
structure QuittingPunishmentFloorEndpointEdgeAt
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tailPayoff : Payoff iota) where
  edge : QuittingPunishmentFloorAdmissibleEdge reward
  tail_payoff : edge.tail.1.1.1 = tailPayoff
  positive_or_allContinue :
    0 < edge.toBoxEdge.absorptionCharge ∨
      (edge.toBoxEdge.root =
          (quittingAllContinueRoot : iota → PMF Bool) ∧
        edge.toBoxEdge.absorptionCharge = 0 ∧
        edge.current.1.1.1 = tailPayoff ∧
        ∀ who, reward (quittingSingletonTerminal who) who ≤
          tailPayoff who)

/-- Every bounded payoff above the punishment floor has an exact endpoint
edge.  Zero absorption forces the root to be literally all-Continue, makes
the edge a payoff self-loop, and is equivalent to singleton domination at
the displayed tail. -/
theorem nonempty_quittingPunishmentFloorEndpointEdgeAt
    (tailPayoff : Payoff iota)
    (hbound : ∀ who, |tailPayoff who| ≤ quittingRewardBound reward)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ tailPayoff who) :
    Nonempty (QuittingPunishmentFloorEndpointEdgeAt reward tailPayoff) := by
  let tailPoint : QuittingNashBellmanPoint iota :=
    (tailPayoff, quittingAllContinueSimplexRoot)
  have htailMem : tailPoint ∈
      quittingNashBellmanBox (quittingRewardBound reward) := by
    constructor
    · intro who
      exact (abs_le.mp (hbound who)).1
    · intro who
      exact (abs_le.mp (hbound who)).2
  let tailBox : QuittingPunishmentFloorBoxState reward :=
    ⟨tailPoint, htailMem⟩
  let tail : QuittingPunishmentFloorAdmissibleState reward :=
    ⟨tailBox, hfloor⟩
  obtain ⟨currentPoint, hcurrentMem, hexact⟩ :=
    exists_quittingNashBellmanPredecessor reward
      (abs_reward_le_quittingRewardBound reward) tailPoint htailMem
  let current : QuittingPunishmentFloorBoxState reward :=
    ⟨currentPoint, hcurrentMem⟩
  let edge : QuittingPunishmentFloorAdmissibleEdge reward :=
    QuittingPunishmentFloorAdmissibleEdge.ofExactEdge tail current hexact
  have htailPayoff : edge.tail.1.1.1 = tailPayoff := rfl
  refine ⟨{
    edge := edge
    tail_payoff := htailPayoff
    positive_or_allContinue := ?_ }⟩
  by_cases hpositive : 0 < edge.toBoxEdge.absorptionCharge
  · exact Or.inl hpositive
  · right
    have hzero : edge.toBoxEdge.absorptionCharge = 0 := by
      exact le_antisymm (le_of_not_gt hpositive)
        edge.toBoxEdge.absorptionCharge_nonneg
    have hcontinue : quittingStationaryContinueMass edge.toBoxEdge.root = 1 := by
      unfold QuittingPunishmentFloorBoxEdge.absorptionCharge at hzero
      unfold quittingRootAbsorptionMass at hzero
      linarith
    have hroot : edge.toBoxEdge.root =
        (quittingAllContinueRoot : iota → PMF Bool) := by
      funext who
      simpa only [quittingAllContinueRoot] using
        eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who
    have hcurrent : edge.current.1.1.1 = tailPayoff := by
      rw [edge.exactEdge.1]
      change quittingRootSuccessorPayoff reward edge.tail.1.1.1
          edge.toBoxEdge.root = tailPayoff
      rw [hroot, quittingRootSuccessorPayoff_allContinueRoot_eq]
      exact htailPayoff
    have hsingleton : ∀ who,
        reward (quittingSingletonTerminal who) who ≤ tailPayoff who := by
      have hnash : IsεQuittingRootNash reward tailPayoff 0
          (quittingAllContinueRoot : iota → PMF Bool) := by
        have hendpoint : IsεQuittingRootEndpointNash reward
            edge.tail.1.1.1 0 edge.toBoxEdge.root := edge.exactEdge.2
        rw [hroot, htailPayoff] at hendpoint
        exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          reward tailPayoff quittingAllContinueRoot).mp hendpoint
      exact (isZeroQuittingRootNash_allContinue_iff_singleton_le
        reward tailPayoff).mp hnash
    exact ⟨hroot, hzero, hcurrent, hsingleton⟩

/-- Failure of singleton domination removes the zero-charge arm from any
endpoint-edge packet. -/
theorem QuittingPunishmentFloorEndpointEdgeAt.positiveCharge_of_not_singleton_le
    {tailPayoff : Payoff iota}
    (endpoint : QuittingPunishmentFloorEndpointEdgeAt reward tailPayoff)
    (hnot : ¬ ∀ who,
      reward (quittingSingletonTerminal who) who ≤ tailPayoff who) :
    0 < endpoint.edge.toBoxEdge.absorptionCharge := by
  rcases endpoint.positive_or_allContinue with hpositive | hstall
  · exact hpositive
  · exact False.elim (hnot hstall.2.2.2)

/-- The zero-charge all-Continue endpoint is available exactly under
singleton domination.  This theorem constructs the literal payoff self-loop
in the reverse direction, rather than relying on an arbitrary Nash selection.
-/
theorem exists_allContinue_quittingPunishmentFloorEndpointEdgeAt_iff
    (tailPayoff : Payoff iota)
    (hbound : ∀ who, |tailPayoff who| ≤ quittingRewardBound reward)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ tailPayoff who) :
    (∃ endpoint : QuittingPunishmentFloorEndpointEdgeAt reward tailPayoff,
      endpoint.edge.toBoxEdge.root =
        (quittingAllContinueRoot : iota → PMF Bool)) ↔
      ∀ who, reward (quittingSingletonTerminal who) who ≤
        tailPayoff who := by
  constructor
  · rintro ⟨endpoint, hroot⟩
    have hendpoint : IsεQuittingRootEndpointNash reward
        endpoint.edge.tail.1.1.1 0 endpoint.edge.toBoxEdge.root :=
      endpoint.edge.exactEdge.2
    rw [hroot, endpoint.tail_payoff] at hendpoint
    have hnash : IsεQuittingRootNash reward tailPayoff 0
        (quittingAllContinueRoot : iota → PMF Bool) :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward tailPayoff quittingAllContinueRoot).mp hendpoint
    exact (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward tailPayoff).mp hnash
  · intro hsingleton
    let point : QuittingNashBellmanPoint iota :=
      (tailPayoff, quittingAllContinueSimplexRoot)
    have hpointMem : point ∈
        quittingNashBellmanBox (quittingRewardBound reward) := by
      constructor
      · intro who
        exact (abs_le.mp (hbound who)).1
      · intro who
        exact (abs_le.mp (hbound who)).2
    let box : QuittingPunishmentFloorBoxState reward := ⟨point, hpointMem⟩
    let state : QuittingPunishmentFloorAdmissibleState reward :=
      ⟨box, hfloor⟩
    let edge : QuittingPunishmentFloorAdmissibleEdge reward := {
      tail := state
      current := state
      exactEdge := by
        constructor
        · change tailPayoff = quittingRootSuccessorPayoff reward tailPayoff
              (quittingRootOfSimplex quittingAllContinueSimplexRoot)
          rw [quittingRootOfSimplex_allContinueSimplexRoot,
            quittingRootSuccessorPayoff_allContinueRoot_eq]
        · rw [quittingRootOfSimplex_allContinueSimplexRoot]
          exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
            reward tailPayoff quittingAllContinueRoot).mpr
              ((isZeroQuittingRootNash_allContinue_iff_singleton_le
                reward tailPayoff).mpr hsingleton) }
    have hroot : edge.toBoxEdge.root =
        (quittingAllContinueRoot : iota → PMF Bool) := by
      exact quittingRootOfSimplex_allContinueSimplexRoot
    have hzero : edge.toBoxEdge.absorptionCharge = 0 := by
      unfold QuittingPunishmentFloorBoxEdge.absorptionCharge
      rw [hroot]
      simp [quittingRootAbsorptionMass, quittingStationaryContinueMass,
        quittingAllContinueAction, quittingAllContinueRoot]
    let endpoint : QuittingPunishmentFloorEndpointEdgeAt reward tailPayoff := {
      edge := edge
      tail_payoff := rfl
      positive_or_allContinue := Or.inr
        ⟨hroot, hzero, rfl, hsingleton⟩ }
    exact ⟨endpoint, hroot⟩

/-- Source-facing four-player boundary retaining the stationary paid target,
fixed-law reset dispatch, exact payoff alignment, and its endpoint edge.  The
only possible failure of floor admissibility is localized to the forced-Quit
pair base. -/
structure FinFourPairBasePaidResetEndpointBoundary
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (owner baseFirst baseSecond : Fin 4) where
  target : FinFourPairBasePaidResetTarget reward witness owner
    baseFirst baseSecond
  returned : QuittingTerminalSemanticPair (Fin 4)
  dispatch : QuittingFixedLawResetDispatch (reward := reward)
    minimum target.semanticPair target.mass owner baseFirst returned
  payoff_aligned : returned.1 = target.semanticPair.1
  paid_row : Nonempty (QuittingPaidFirstDisagreementRow reward target.profile
    target.localization.debtor witness.terminalGap)
  floor_violation_or_endpoint :
    (∃ who ∈ ({baseFirst, baseSecond} : Finset (Fin 4)),
      target.semanticPair.1 who < quittingPunishmentValue reward who) ∨
    Nonempty (QuittingPunishmentFloorEndpointEdgeAt reward
      target.semanticPair.1)

namespace FinFourPairBasePaidResetEndpointBoundary

/-- Even while the target retains its full-gap paid row, its literal
all-Continue zero-charge endpoint is governed exactly by singleton
domination.  The paid-row field supplies no contradiction to this condition.
-/
theorem exists_allContinueEndpoint_iff_singleton_le_of_floor
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimum : QuittingTerminalSemanticPair (Fin 4)}
    {owner baseFirst baseSecond : Fin 4}
    (boundary : FinFourPairBasePaidResetEndpointBoundary reward witness
      minimum owner baseFirst baseSecond)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      boundary.target.semanticPair.1 who) :
    (∃ endpoint : QuittingPunishmentFloorEndpointEdgeAt reward
        boundary.target.semanticPair.1,
      endpoint.edge.toBoxEdge.root =
        (quittingAllContinueRoot : Fin 4 → PMF Bool)) ↔
      ∀ who, reward (quittingSingletonTerminal who) who ≤
        boundary.target.semanticPair.1 who := by
  apply exists_allContinue_quittingPunishmentFloorEndpointEdgeAt_iff
  · intro who
    change |quittingTerminalPayoff reward boundary.target.profile who| ≤
      quittingRewardBound reward
    exact abs_quittingTerminalPayoff_le reward boundary.target.profile who
      (abs_reward_le_quittingRewardBound reward)
  · exact hfloor

end FinFourPairBasePaidResetEndpointBoundary

/-- The pair-base paid reset target either has a punishment-floor violation
at one of its two forced-Quit coordinates, or its payoff is the tail of an
exact admissible edge.  In the latter branch the edge has positive absorption
unless singleton domination makes it the literal all-Continue zero-charge
self-loop. -/
theorem QuittingTerminalExploitabilityWitness.nonempty_finFour_pairBasePaidResetEndpointBoundary
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (owner baseFirst baseSecond : Fin 4)
    (hownerFirst : owner ≠ baseFirst)
    (hownerSecond : owner ≠ baseSecond)
    (hbase : baseFirst ≠ baseSecond) :
    Nonempty (FinFourPairBasePaidResetEndpointBoundary reward witness minimum
      owner baseFirst baseSecond) := by
  obtain ⟨target, returned, dispatch⟩ :=
    witness.exists_finFour_pairBasePaidResetDispatch minimum hminimumMem
      hminimum hminimumPositive owner baseFirst baseSecond hownerFirst
        hownerSecond hbase
  have haligned : returned.1 = target.semanticPair.1 :=
    dispatch.prescribed_eq_target target.target_joint
  have hboundary :
      (∃ who ∈ ({baseFirst, baseSecond} : Finset (Fin 4)),
        target.semanticPair.1 who < quittingPunishmentValue reward who) ∨
      Nonempty (QuittingPunishmentFloorEndpointEdgeAt reward
        target.semanticPair.1) := by
    by_cases hfloor : ∀ who,
        quittingPunishmentValue reward who ≤ target.semanticPair.1 who
    · right
      apply nonempty_quittingPunishmentFloorEndpointEdgeAt
        target.semanticPair.1
      · intro who
        change |quittingTerminalPayoff reward target.profile who| ≤
          quittingRewardBound reward
        exact abs_quittingTerminalPayoff_le reward target.profile who
          (abs_reward_le_quittingRewardBound reward)
      · exact hfloor
    · left
      obtain ⟨who, hwho⟩ := not_forall.mp hfloor
      have hwho : target.semanticPair.1 who <
          quittingPunishmentValue reward who := lt_of_not_ge hwho
      refine ⟨who, ?_, hwho⟩
      by_contra hnot
      have hfree : who ∈ finFourPairBaseComplement
          ({baseFirst, baseSecond} : Finset (Fin 4)) := by
        simp [finFourPairBaseComplement, hnot]
      exact (not_lt_of_ge (target.localization.free_solved who hfree).2) hwho
  exact ⟨{
    target := target
    returned := returned
    dispatch := dispatch
    payoff_aligned := haligned
    paid_row := target.paid_row
    floor_violation_or_endpoint := hboundary }⟩

end GameTheory
