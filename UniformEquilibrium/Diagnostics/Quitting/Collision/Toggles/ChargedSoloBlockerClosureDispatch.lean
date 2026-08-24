/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.ChargedSoloBlockerGateRepayment
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBaseStationaryTwoDebtorHandoff
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidResetAlignment
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PrescribedOwnerStationaryHandoff
import UniformEquilibrium.Diagnostics.Quitting.PaidFirstDisagreementPayoffNearReturn
import
  UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourPrescribedOwnerResetAlignment
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourSoloWallDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFixedLawMinimumTargetStall

/-!
# Closure dispatch for a charged solo blocker gate

This file composes the source-native charged-blocker gate with the literal
four-player solo-wall dispatch.  A positive pair premium now produces either
an outsider join at the full terminal gap or an actual stationary two-debtor
handoff.  The other arm remains the checked one-coordinate exact repayment.

Two source-matching facts delimit the remaining closure problem.  First, the
gate's displayed exact solo root preserves total debt at its actual carrier
source, so it cannot itself be used as a strict debt-descent edge.  Second, a
pair-base target co-realizes a paid row, a zero-debt reset owner, and unit
incidence on one actual profile and law.  Its fixed-law dispatch starts at the
global minimum, but its dynamic edge prefixes the separately selected reset
face `returned`, not the paid target.  No equality or chronological connector
between those two points is asserted.

No arm below constructs payoff near-return.  In particular, the paid row in
the stationary two-debtor handoff does not by itself satisfy the frontier and
source-alignment quantifiers of
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer`.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open QuittingSureSetOwnerRepair

namespace FinFourChargedSoloBlockerGate

/-- The repayment arm, named so that downstream dispatches can retain all of
its source, root, label, and coordinate provenance without abbreviation. -/
def HasEveryExactRepayment
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker)
    (gap : ℝ) : Prop :=
  ∀ orbit : QuittingPunishmentFloorInfiniteOrbit reward,
    orbit.value 0 = finFourSoloBlockerTail reward gate.source.1 owner blocker
        (gate.hazard true).toReal →
    orbit.roots 0 = gate.root →
    orbit.value 1 blocker =
        (1 - (gate.hazard true).toReal) *
            quittingSoloReward reward blocker blocker +
          (gate.hazard true).toReal *
            quittingSingletonCollisionReward reward owner blocker ∧
      ∃ limit : Payoff (Fin 4),
        (∀ who, Tendsto (fun time ↦ orbit.value time who) atTop
          (nhds (limit who))) ∧
        charge / 8 * gap / 2 ≤ limit blocker - orbit.value 1 blocker ∧
        ∃ time, 1 ≤ time ∧
          charge / 8 * gap / 4 ≤
            orbit.value time blocker - orbit.value 1 blocker

/-- The actual exact root stored by the gate is debt-neutral at the gate's
actual carrier source.  Thus that row cannot supply the strict carrier debt
decrease required by the well-founded branch. -/
theorem sourcePrefix_debtSum_eq
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward gate.root gate.source) =
      quittingTerminalSemanticDebtSum gate.source := by
  have hnash : IsεQuittingRootNash reward gate.source.1 0
      (quittingSoloStationaryRoot owner gate.hazard) := by
    rw [← gate.root_eq_solo]
    exact gate.exact_root
  rw [gate.root_eq_solo]
  exact quittingTerminalSemanticDebtSum_prefix_solo_eq_of_uniqueDebtor
    reward gate.source owner gate.hazard gate.source_mem hnash
      gate.owner_tail_eq_solo gate.other_debt

/-- Equivalently, the gate records zero semantic-debt drop at its literal
source/root pair. -/
theorem source_debtDrop_eq_zero
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker) :
    quittingTerminalSemanticDebtDrop reward gate.source gate.root = 0 := by
  unfold quittingTerminalSemanticDebtDrop
  rw [gate.sourcePrefix_debtSum_eq]
  exact sub_self _

/-- **Premium consumption at the actual charged gate.**  The premium arm of
the source-native repayment theorem feeds the solo-wall dispatch.  Therefore
the complete unconditional output is a full-gap outsider join, an actual
stationary two-debtor handoff, or the original one-coordinate exact
repayment arm. -/
theorem pairJoin_or_stationaryTwoDebtorHandoff_or_everyExactRepayment
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker)
    (hcharge : 0 < charge) :
    ∃ gap : ℝ, 0 < gap ∧
      ((∃ joiner ∉ ({owner, blocker} : Finset (Fin 4)),
          quittingSetReward reward {owner, blocker} joiner +
              witness.terminalGap ≤
            quittingSetReward reward
              (insert joiner {owner, blocker}) joiner) ∨
        (∃ joiner fourth,
          Nonempty (FinFourLeaveJoinStationaryTwoDebtorHandoff reward
            witness (finFourOffMinimumRewardBound reward) owner blocker
              joiner fourth)) ∨
        gate.HasEveryExactRepayment gap) := by
  obtain ⟨gap, hgap, hsplit⟩ :=
    gate.pairPremium_or_every_exactRepayment hcharge
  refine ⟨gap, hgap, ?_⟩
  rcases hsplit with hpremium | hrepayment
  · have hpremiumPos : 0 <
        quittingSingletonCollisionReward reward owner blocker -
          quittingSoloReward reward owner blocker := by
      exact (half_pos hgap).trans_le hpremium
    have hpremiumSet : quittingSetReward reward {owner} blocker <
        quittingSetReward reward {owner, blocker} blocker := by
      rw [quittingSetReward_singleton_eq_soloReward,
        quittingSetReward_pair_right]
      linarith
    have hnormal : IsQuittingNormalPlayer reward blocker := by
      obtain ⟨minimum, _hminimumMem, _hminimum, _hminimumPos,
          _hnash, _hfixed, hseparated⟩ :=
        exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff
          reward witness.not_exists_uniformEquilibriumPayoff
      unfold IsQuittingNormalPlayer quittingSoloSelfPayoff
      convert (hseparated blocker).1 using 1
      congr 1
    rcases pairPremium_pairJoin_or_leaveJoinStationaryTwoDebtorHandoff
        witness (finFourOffMinimumRewardBound reward)
          (finFourOffMinimumRewardBound_pos reward).le
          (abs_reward_le_finFourOffMinimumRewardBound reward)
          owner blocker gate.owner_ne_blocker hnormal hpremiumSet with
      hjoin | hhandoff
    · exact Or.inl hjoin
    · exact Or.inr (Or.inl hhandoff)
  · exact Or.inr (Or.inr hrepayment)

private theorem exists_finFour_label_outside_triple
    (first second third : Fin 4)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ∃ fourth, fourth ∉ ({first, second, third} : Finset (Fin 4)) := by
  have hcard : ({first, second, third} : Finset (Fin 4)).card <
      (Finset.univ : Finset (Fin 4)).card := by
    simp [hfirstSecond, hfirstThird, hsecondThird]
  obtain ⟨fourth, _, hfourth⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨fourth, hfourth⟩

/-- A full-gap outsider join has an actual stationary consumer on the same
gate pair: the complementary induced binary game retains quantitative
off-pair absorption, a heavy collision atom, base-localized debt, and a paid
row. -/
theorem pairBaseHandoff_or_leaveJoinHandoff_or_everyExactRepayment
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker)
    (hcharge : 0 < charge) :
    ∃ gap : ℝ, 0 < gap ∧
      ((∃ joiner fourth,
          Nonempty (FinFourPairBaseStationaryTwoDebtorHandoff reward
            witness (finFourOffMinimumRewardBound reward) owner blocker
              joiner fourth)) ∨
        (∃ joiner fourth,
          Nonempty (FinFourLeaveJoinStationaryTwoDebtorHandoff reward
            witness (finFourOffMinimumRewardBound reward) owner blocker
              joiner fourth)) ∨
        gate.HasEveryExactRepayment gap) := by
  obtain ⟨gap, hgap, hjoin | hleave | hrepayment⟩ :=
    gate.pairJoin_or_stationaryTwoDebtorHandoff_or_everyExactRepayment hcharge
  · refine ⟨gap, hgap, Or.inl ?_⟩
    obtain ⟨joiner, hjoiner, hjoin⟩ := hjoin
    have hjoinerNe : joiner ≠ owner ∧ joiner ≠ blocker := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hjoiner
    obtain ⟨fourth, hfourth⟩ := exists_finFour_label_outside_triple
      owner blocker joiner gate.owner_ne_blocker hjoinerNe.1.symm
        hjoinerNe.2.symm
    have hfourthNe : fourth ≠ owner ∧ fourth ≠ blocker ∧
        fourth ≠ joiner := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hfourth
    refine ⟨joiner, fourth, ?_⟩
    exact nonempty_finFourPairBaseStationaryTwoDebtorHandoff
      witness (finFourOffMinimumRewardBound reward)
        (finFourOffMinimumRewardBound_pos reward).le
        (abs_reward_le_finFourOffMinimumRewardBound reward)
        owner blocker joiner fourth gate.owner_ne_blocker
          hjoinerNe.1.symm hfourthNe.1.symm hjoinerNe.2.symm
            hfourthNe.2.1.symm hfourthNe.2.2.symm (by
              have hset : insert joiner {owner, blocker} =
                  ({owner, blocker, joiner} : Finset (Fin 4)) := by
                ext who
                simp only [Finset.mem_insert, Finset.mem_singleton]
                aesop
              rw [hset] at hjoin
              exact hjoin)
  · exact ⟨gap, hgap, Or.inr (Or.inl hleave)⟩
  · exact ⟨gap, hgap, Or.inr (Or.inr hrepayment)⟩

end FinFourChargedSoloBlockerGate

/-! ## Same-profile paid reset target at the minimum source -/

/-- The paid/reset target is co-realized, but the fixed-law dispatch prefixes
its separate reset-face return.  The last field records the exact debt
boundary: either the paid target lies strictly above the minimum, or the
returned reset face is forced to stall at all-Continue. -/
structure FinFourChargedGatePaidResetBoundary
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (_gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker) where
  minimum : QuittingTerminalSemanticPair (Fin 4)
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  minimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate
  minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum
  secondBase : Fin 4
  target : FinFourPairBasePaidResetTarget reward witness owner blocker
    secondBase
  returned : QuittingTerminalSemanticPair (Fin 4)
  dispatch : QuittingFixedLawResetDispatch (reward := reward)
    minimum target.semanticPair target.mass owner blocker returned
  target_excess_or_returned_stall :
    quittingTerminalSemanticDebtSum minimum <
        quittingTerminalSemanticDebtSum target.semanticPair ∨
      (IsεQuittingRootNash reward returned.2 0
          (quittingAllContinueRoot : Fin 4 → PMF Bool) ∧
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot
          returned = returned)

private theorem exists_finFour_label_outside_pair
    (first second : Fin 4) (hne : first ≠ second) :
    ∃ third, third ∉ ({first, second} : Finset (Fin 4)) := by
  have hcard : ({first, second} : Finset (Fin 4)).card <
      (Finset.univ : Finset (Fin 4)).card := by
    simp [hne]
  obtain ⟨third, _, hthird⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨third, hthird⟩

/-- Every charged gate label pair admits an independently selected but
same-profile paid/reset target from the actual global minimum.  The paid row
belongs to `target.profile`; the dynamic branch of `dispatch` acts on
`returned`, and this theorem does not identify them. -/
theorem FinFourChargedSoloBlockerGate.nonempty_paidResetBoundary
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker) :
    Nonempty (FinFourChargedGatePaidResetBoundary witness gate) := by
  obtain ⟨minimum, hminimumMem, hminimum, hminimumPos, _hnash,
      _hfixed, _hseparated⟩ :=
    exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff
      reward witness.not_exists_uniformEquilibriumPayoff
  obtain ⟨secondBase, hsecondBase⟩ :=
    exists_finFour_label_outside_pair owner blocker gate.owner_ne_blocker
  have hsecondNe : secondBase ≠ owner ∧ secondBase ≠ blocker := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      hsecondBase
  obtain ⟨target, returned, hdispatch⟩ :=
    witness.exists_finFour_pairBasePaidResetDispatch
      minimum hminimumMem hminimum hminimumPos owner blocker secondBase
        gate.owner_ne_blocker hsecondNe.1.symm hsecondNe.2.symm
  have hboundary :
      quittingTerminalSemanticDebtSum minimum <
          quittingTerminalSemanticDebtSum target.semanticPair ∨
        (IsεQuittingRootNash reward returned.2 0
            (quittingAllContinueRoot : Fin 4 → PMF Bool) ∧
          quittingTerminalSemanticPrefix reward quittingAllContinueRoot
            returned = returned) := by
    by_cases htarget : quittingTerminalSemanticDebtSum target.semanticPair ≤
        quittingTerminalSemanticDebtSum minimum
    · exact Or.inr
        (hdispatch.allContinue_of_target_debt_le_source hminimum htarget)
    · exact Or.inl (lt_of_not_ge htarget)
  exact ⟨{
    minimum := minimum
    minimum_mem := hminimumMem
    minimum_le := hminimum
    minimum_pos := hminimumPos
    secondBase := secondBase
    target := target
    returned := returned
    dispatch := hdispatch
    target_excess_or_returned_stall := hboundary
  }⟩

namespace FinFourChargedSoloBlockerGate

/-- The two strongest checked outputs coexist: the charged premium/repayment
dispatch and a same-profile paid/reset target from the global minimum.  This
does not turn the target's paid row into a paid row at the returned reset face
and therefore is not yet the payoff-near-return consumer. -/
theorem stationaryHandoff_or_exactRepayment_and_paidResetBoundary
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (gate : FinFourChargedSoloBlockerGate reward witness minimumDebt charge
      owner blocker)
    (hcharge : 0 < charge) :
    ∃ gap : ℝ, 0 < gap ∧
      (((∃ joiner fourth,
          Nonempty (FinFourPairBaseStationaryTwoDebtorHandoff reward
            witness (finFourOffMinimumRewardBound reward) owner blocker
              joiner fourth)) ∨
        (∃ joiner fourth,
          Nonempty (FinFourLeaveJoinStationaryTwoDebtorHandoff reward
            witness (finFourOffMinimumRewardBound reward) owner blocker
              joiner fourth)) ∨
        gate.HasEveryExactRepayment gap) ∧
      Nonempty (FinFourChargedGatePaidResetBoundary witness gate)) := by
  obtain ⟨gap, hgap, hterminal⟩ :=
    gate.pairBaseHandoff_or_leaveJoinHandoff_or_everyExactRepayment hcharge
  exact ⟨gap, hgap, hterminal, gate.nonempty_paidResetBoundary⟩

end FinFourChargedSoloBlockerGate

/-! ## The precise minimum-fiber source match -/

/-- Both same-owner handoffs that become available once the charged gate's
actual source is proved to lie on its recorded minimum fiber.  The reset
target and the singleton-base stationary point are deliberately separate
fields. -/
structure FinFourChargedGateSourceMatchedOwnerHandoffs
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {pairs : ℕ → QuittingTerminalSemanticPair (Fin 4)}
    {roots : ℕ → Fin 4 → PMF Bool}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (limit : FinFourChargedSoloBlockerGateLimit reward witness pairs roots
      minimumDebt charge owner blocker) where
  resetTarget : QuittingTerminalSemanticPair (Fin 4)
  resetMass : QuittingTerminalOutcome (Fin 4) → ℝ
  resetReturned : QuittingTerminalSemanticPair (Fin 4)
  reset_joint : (resetTarget, resetMass) ∈
    quittingTerminalSemanticLawCarrier reward
  reset_owner_debt : quittingTerminalSemanticDebt resetTarget owner = 0
  reset_firstBase_incidence :
    quittingTerminalOpponentIncidenceMass owner
      (finFourPrescribedResetFirstBase owner) resetMass = 1
  reset_dispatch : QuittingFixedLawResetDispatch (reward := reward)
    limit.gate.source resetTarget resetMass owner
      (finFourPrescribedResetFirstBase owner) resetReturned
  stationaryDelta : ℝ
  stationaryDelta_pos : 0 < stationaryDelta
  stationaryPoint : mixedPolytope
    (quittingBinaryForm (Finset.univ.erase owner)).sig
  stationaryPoint_mem : stationaryPoint ∈
    quittingPersistentBaseNashSet reward {owner} (Finset.univ.erase owner)
  stationaryHandoff : Nonempty (QuittingSingletonBaseStationaryHandoff
    reward owner (Finset.univ.erase owner) stationaryPoint
      stationaryDelta witness.terminalGap)

/-- The missing reverse inequality is sufficient for literal source matching.
It makes the gate source another global minimum, hence its unique owner debt
is positive and the prescribed-owner reset theorem applies.  Independently,
compact stationary re-selection supplies the singleton-base handoff at that
same owner label. -/
theorem FinFourChargedSoloBlockerGateLimit.nonempty_sourceMatchedOwnerHandoffs_of_debtSum_le
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {pairs : ℕ → QuittingTerminalSemanticPair (Fin 4)}
    {roots : ℕ → Fin 4 → PMF Bool}
    {minimumDebt charge : ℝ} {owner blocker : Fin 4}
    (limit : FinFourChargedSoloBlockerGateLimit reward witness pairs roots
      minimumDebt charge owner blocker)
    (hsourceLe : quittingTerminalSemanticDebtSum limit.gate.source ≤
      minimumDebt) :
    Nonempty (FinFourChargedGateSourceMatchedOwnerHandoffs witness limit) := by
  have hsourceMinimum : ∀ candidate ∈
      quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum limit.gate.source ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    calc
      quittingTerminalSemanticDebtSum limit.gate.source ≤
          minimumDebt := hsourceLe
      _ = quittingTerminalSemanticDebtSum limit.minimum :=
        limit.minimumDebt_eq
      _ ≤ quittingTerminalSemanticDebtSum candidate :=
        limit.minimum_le candidate hcandidate
  have hsourcePos : 0 <
      quittingTerminalSemanticDebtSum limit.gate.source := by
    calc
      0 < quittingTerminalSemanticDebtSum limit.minimum := limit.minimum_pos
      _ = minimumDebt := limit.minimumDebt_eq.symm
      _ ≤ quittingTerminalSemanticDebtSum limit.gate.source :=
        limit.gate.minimumDebt_le
  have hownerPos : 0 <
      quittingTerminalSemanticDebt limit.gate.source owner := by
    rw [limit.gate.owner_debt_eq_sum]
    exact hsourcePos
  obtain ⟨resetPoint, hresetPointMem, hreset⟩ :=
    witness.exists_finFour_prescribedOwner_resetDispatch
      limit.gate.source owner limit.gate.source_mem hsourceMinimum hownerPos
  dsimp only at hreset
  rcases hreset with
    ⟨hresetJoint, hresetDebt, hresetIncidence, resetReturned,
      hresetDispatch⟩
  obtain ⟨delta, hdelta, _hall, stationaryPoint, hstationaryPoint,
      hstationaryHandoff⟩ :=
    witness.exists_prescribedOwner_stationaryHandoff owner
  let resetRoot := quittingPersistentBaseRoot
    (finFourPrescribedResetBase owner)
    (finFourPrescribedResetFree owner) resetPoint
  let resetProfile := quittingStationaryProfile reward resetRoot
  let resetTarget := quittingTerminalSemanticPair reward resetProfile
  let resetMass := quittingTerminalOutcomeMass reward resetProfile
  exact ⟨{
    resetTarget := resetTarget
    resetMass := resetMass
    resetReturned := resetReturned
    reset_joint := hresetJoint
    reset_owner_debt := hresetDebt
    reset_firstBase_incidence := hresetIncidence
    reset_dispatch := hresetDispatch
    stationaryDelta := delta
    stationaryDelta_pos := hdelta
    stationaryPoint := stationaryPoint
    stationaryPoint_mem := hstationaryPoint
    stationaryHandoff := hstationaryHandoff
  }⟩

end GameTheory
