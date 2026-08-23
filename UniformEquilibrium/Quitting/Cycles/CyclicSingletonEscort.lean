/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate
import MathUE.FiniteSerialRelation

/-!
# Escort edges forced by balanced singleton cycles

A change from one positive-hazard singleton owner to the next forces two
opposite weak signs in the normalized singleton matrix.  This is the local,
zero-deletion-free core of the escort-cycle obstruction.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {L : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A directed escort edge from `owner` to `nextOwner`: the first owner weakly
prefers its own solo payoff to the next owner's singleton outcome, while the
next owner weakly prefers the first owner's singleton outcome to its own solo
payoff. -/
def IsQuittingSingletonEscortEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner nextOwner : ι) : Prop :=
  owner ≠ nextOwner ∧
    quittingSingletonMatrix reward owner nextOwner ≤ 0 ∧
    0 ≤ quittingSingletonMatrix reward nextOwner owner

/-- A positive-period closed walk in the singleton escort digraph. -/
abbrev QuittingSingletonEscortCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  Math.FiniteSerialRelation.PeriodicCycle
    (IsQuittingSingletonEscortEdge reward)

namespace QuittingSingletonEscortCycle

omit [Fintype ι] [DecidableEq ι] in
/-- Escort edges are irreflexive, so every escort cycle visits at least two
vertices. -/
theorem two_le_period (cycle : QuittingSingletonEscortCycle reward) :
    2 ≤ cycle.period := by
  apply cycle.two_le_period_of_irreflexive
  intro owner hedge
  exact hedge.1 rfl

end QuittingSingletonEscortCycle

omit [Fintype ι] [DecidableEq ι] in
private theorem coarse_next_eq_solo
    (certificate : BalancedSingletonCycleCertificate (L := L) reward)
    (phase : Fin L) :
    certificate.coarse (finRotate L phase) (certificate.owner phase) =
      quittingSoloReward reward (certificate.owner phase) (certificate.owner phase) := by
  have harc := congrFun (certificate.arc phase) (certificate.owner phase)
  have hactive := certificate.active phase
  simp only [quittingSingletonArcPayoff] at harc
  nlinarith [certificate.hazard_lt_one phase]

omit [Fintype ι] [DecidableEq ι] in
/-- Two positive-hazard phases separated by a zero-hazard stretch force an
escort edge as soon as the stretch is supplied through its exact coarse-value
bridge.  Iterating zero-hazard arc equations provides this bridge. -/
theorem BalancedSingletonCycleCertificate.escortEdge_of_coarse_bridge
    (certificate : BalancedSingletonCycleCertificate (L := L) reward)
    (phase nextPhase : Fin L)
    (hchange : certificate.owner phase ≠ certificate.owner nextPhase)
    (hcurrent : 0 < certificate.hazard phase)
    (hnext : 0 < certificate.hazard nextPhase)
    (hbridge : certificate.coarse (finRotate L phase) =
      certificate.coarse nextPhase) :
    IsQuittingSingletonEscortEdge reward (certificate.owner phase)
      (certificate.owner nextPhase) := by
  let afterNext := finRotate L nextPhase
  have hnextTie : certificate.coarse nextPhase (certificate.owner phase) =
      quittingSoloReward reward (certificate.owner phase) (certificate.owner phase) := by
    rw [← hbridge]
    exact coarse_next_eq_solo certificate phase
  have harcNext := congrFun (certificate.arc nextPhase) (certificate.owner phase)
  have hafterFloor := certificate.soloFloor afterNext (certificate.owner phase)
  have hnextMatrix : quittingSingletonMatrix reward (certificate.owner phase)
      (certificate.owner nextPhase) ≤ 0 := by
    simp only [quittingSingletonArcPayoff] at harcNext
    unfold quittingSingletonMatrix
    simp only [quittingSoloReward] at hnextTie hafterFloor harcNext
    have hsurvival : 0 ≤ 1 - certificate.hazard nextPhase := by
      linarith [certificate.hazard_lt_one nextPhase]
    have hcontinuation : 0 ≤ (1 - certificate.hazard nextPhase) *
        (certificate.coarse afterNext (certificate.owner phase) -
          reward ⟨{certificate.owner phase}, by simp⟩ (certificate.owner phase)) :=
      mul_nonneg hsurvival (sub_nonneg.mpr hafterFloor)
    have hendpoint : certificate.hazard nextPhase *
        (reward ⟨{certificate.owner nextPhase}, by simp⟩ (certificate.owner phase) -
          reward ⟨{certificate.owner phase}, by simp⟩ (certificate.owner phase)) ≤ 0 := by
      nlinarith only [harcNext, hnextTie, hcontinuation]
    rw [mul_comm] at hendpoint
    exact nonpos_of_mul_nonpos_left hendpoint hnext
  have harcCurrent := congrFun (certificate.arc phase) (certificate.owner nextPhase)
  have hcurrentFloor := certificate.soloFloor phase (certificate.owner nextPhase)
  have hnextActive := certificate.active nextPhase
  have hbridgeAt := congrFun hbridge (certificate.owner nextPhase)
  have hreverseMatrix : 0 ≤ quittingSingletonMatrix reward
      (certificate.owner nextPhase) (certificate.owner phase) := by
    simp only [quittingSingletonArcPayoff] at harcCurrent
    unfold quittingSingletonMatrix
    simp only [quittingSoloReward] at hcurrentFloor hnextActive harcCurrent hbridgeAt
    have hsurvival : 0 ≤ 1 - certificate.hazard phase := by
      linarith [certificate.hazard_lt_one phase]
    have hcoarseDiff : 0 ≤
        certificate.coarse phase (certificate.owner nextPhase) -
          certificate.coarse (finRotate L phase) (certificate.owner nextPhase) := by
      rw [hbridgeAt, hnextActive]
      exact sub_nonneg.mpr hcurrentFloor
    have hidentity :
        certificate.coarse phase (certificate.owner nextPhase) -
            certificate.coarse (finRotate L phase) (certificate.owner nextPhase) =
          certificate.hazard phase *
            (reward ⟨{certificate.owner phase}, by simp⟩
                (certificate.owner nextPhase) -
              certificate.coarse (finRotate L phase) (certificate.owner nextPhase)) := by
      rw [harcCurrent]
      ring
    rw [hidentity, hbridgeAt, hnextActive] at hcoarseDiff
    have hendpoint := hcoarseDiff
    rw [mul_comm] at hendpoint
    exact nonneg_of_mul_nonneg_left hendpoint hcurrent
  exact ⟨hchange, hnextMatrix, hreverseMatrix⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Every adjacent change between positive-hazard owners in a balanced
singleton cycle is an escort edge in the normalized singleton matrix. -/
theorem BalancedSingletonCycleCertificate.escortEdge_of_owner_change
    (certificate : BalancedSingletonCycleCertificate (L := L) reward)
    (phase : Fin L)
    (hchange : certificate.owner phase ≠
      certificate.owner (finRotate L phase))
    (hcurrent : 0 < certificate.hazard phase)
    (hnext : 0 < certificate.hazard (finRotate L phase)) :
    IsQuittingSingletonEscortEdge reward (certificate.owner phase)
      (certificate.owner (finRotate L phase)) := by
  exact certificate.escortEdge_of_coarse_bridge phase (finRotate L phase)
    hchange hcurrent hnext rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Opponent divergence ensures that the owner word of every balanced
singleton certificate contains at least two distinct players. -/
theorem BalancedSingletonCycleCertificate.exists_distinct_owner
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) :
    ∃ first second : Fin L, certificate.owner first ≠ certificate.owner second := by
  obtain ⟨second, hne, _⟩ := certificate.opponentDivergence
    (certificate.owner certificate.initial)
  exact ⟨certificate.initial, second, hne⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem BalancedSingletonCycleCertificate.coarse_eq_iterate_of_hazard_zero
    (certificate : BalancedSingletonCycleCertificate (L := L) reward)
    (phase : Fin L) (steps : ℕ)
    (hzero : ∀ offset < steps,
      certificate.hazard ((finRotate L)^[offset] phase) = 0) :
    certificate.coarse phase =
      certificate.coarse ((finRotate L)^[steps] phase) := by
  induction steps generalizing phase with
  | zero => rfl
  | succ steps ih =>
      have hhead := certificate.arc phase
      have hheadZero : certificate.hazard phase = 0 := by
        simpa using hzero 0 (by omega)
      rw [hheadZero] at hhead
      have hhead' : certificate.coarse phase =
          certificate.coarse (finRotate L phase) := by
        funext who
        have := congrFun hhead who
        simpa [quittingSingletonArcPayoff] using this
      rw [hhead']
      rw [Function.iterate_succ_apply]
      apply ih (finRotate L phase)
      intro offset hoffset
      rw [← Function.iterate_succ_apply]
      exact hzero (offset + 1) (by omega)

/-- Owners which occur at a phase carrying strictly positive hazard. -/
def BalancedSingletonCycleCertificate.PositiveOwner
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) :=
  {owner : ι // ∃ phase, 0 < certificate.hazard phase ∧
    certificate.owner phase = owner}

omit [Fintype ι] [DecidableEq ι] in
private theorem BalancedSingletonCycleCertificate.positiveOwner_nonempty
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) :
    Nonempty certificate.PositiveOwner := by
  obtain ⟨phase, _, hpositive⟩ :=
    certificate.opponentDivergence (certificate.owner certificate.initial)
  exact ⟨⟨certificate.owner phase, phase, hpositive, rfl⟩⟩

omit [Fintype ι] in
private theorem BalancedSingletonCycleCertificate.positiveOwner_has_escort
    (certificate : BalancedSingletonCycleCertificate (L := L) reward)
    (source : certificate.PositiveOwner) :
    ∃ target : certificate.PositiveOwner,
      IsQuittingSingletonEscortEdge reward source.val target.val := by
  obtain ⟨sourcePhase, hsourcePositive, hsourceOwner⟩ := source.property
  obtain ⟨targetPhase, htargetDifferent, htargetPositive⟩ :=
    certificate.opponentDivergence source.val
  obtain ⟨targetDistance, htargetDistanceLt, htargetReach⟩ :=
    Math.exists_iterate_finRotate_eq sourcePhase targetPhase
  have hexists : ∃ distance : ℕ,
      0 < distance ∧ distance < L ∧
        0 < certificate.hazard ((finRotate L)^[distance] sourcePhase) ∧
        certificate.owner ((finRotate L)^[distance] sourcePhase) ≠ source.val := by
    refine ⟨targetDistance, ?_, htargetDistanceLt, ?_, ?_⟩
    · by_contra hnot
      have : targetDistance = 0 := Nat.eq_zero_of_not_pos hnot
      subst targetDistance
      simp only [Function.iterate_zero, id_eq] at htargetReach
      apply htargetDifferent
      rw [← htargetReach, hsourceOwner]
    · simpa [htargetReach] using htargetPositive
    · simpa [htargetReach] using htargetDifferent.symm
  let nextDistance := Nat.find hexists
  have hnext := Nat.find_spec hexists
  let positiveBefore := (Finset.range nextDistance).filter fun distance ↦
    0 < certificate.hazard ((finRotate L)^[distance] sourcePhase)
  have hpositiveBefore : positiveBefore.Nonempty := by
    refine ⟨0, ?_⟩
    have hnextPositive : 0 < nextDistance := hnext.1
    simp [positiveBefore, hnextPositive, hsourcePositive]
  let lastDistance := positiveBefore.max' hpositiveBefore
  have hlastMem : lastDistance ∈ positiveBefore :=
    Finset.max'_mem positiveBefore hpositiveBefore
  have hlastLt : lastDistance < nextDistance :=
    (Finset.mem_filter.mp hlastMem).1 |> Finset.mem_range.mp
  have hlastPositive :
      0 < certificate.hazard ((finRotate L)^[lastDistance] sourcePhase) :=
    (Finset.mem_filter.mp hlastMem).2
  have hbeforeSameOwner (distance : ℕ) (hdistance : distance < nextDistance)
      (hpositive : 0 < certificate.hazard
        ((finRotate L)^[distance] sourcePhase)) :
      certificate.owner ((finRotate L)^[distance] sourcePhase) = source.val := by
    by_contra hdifferent
    have hwitness : 0 < distance ∧ distance < L ∧
        0 < certificate.hazard ((finRotate L)^[distance] sourcePhase) ∧
        certificate.owner ((finRotate L)^[distance] sourcePhase) ≠ source.val := by
      refine ⟨?_, lt_trans hdistance hnext.2.1, hpositive, hdifferent⟩
      by_contra hnot
      have : distance = 0 := Nat.eq_zero_of_not_pos hnot
      subst distance
      exact hdifferent (by simpa using hsourceOwner)
    have hminimal := Nat.find_min' hexists hwitness
    omega
  have hlastOwner :
      certificate.owner ((finRotate L)^[lastDistance] sourcePhase) = source.val :=
    hbeforeSameOwner lastDistance hlastLt hlastPositive
  have hzeroBetween (offset : ℕ)
      (hoffset : offset < nextDistance - (lastDistance + 1)) :
      certificate.hazard
          ((finRotate L)^[offset]
            ((finRotate L)^[lastDistance + 1] sourcePhase)) = 0 := by
    rw [← Function.iterate_add_apply]
    have hindexLt : lastDistance + 1 + offset < nextDistance := by omega
    by_contra hne
    have hpos : 0 < certificate.hazard
        ((finRotate L)^[lastDistance + 1 + offset] sourcePhase) := by
      have := certificate.hazard_nonneg
        ((finRotate L)^[lastDistance + 1 + offset] sourcePhase)
      exact lt_of_le_of_ne this (by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Ne.symm hne)
    have hmem : lastDistance + 1 + offset ∈ positiveBefore := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hindexLt, hpos⟩
    have hle := Finset.le_max' positiveBefore _ hmem
    omega
  let lastPhase := (finRotate L)^[lastDistance] sourcePhase
  let nextPhase := (finRotate L)^[nextDistance] sourcePhase
  have hrotateLast : finRotate L lastPhase =
      (finRotate L)^[lastDistance + 1] sourcePhase := by
    simp only [lastPhase, Function.iterate_succ_apply']
  have hnextFromLast :
      (finRotate L)^[nextDistance - (lastDistance + 1)]
          ((finRotate L)^[lastDistance + 1] sourcePhase) = nextPhase := by
    rw [← Function.iterate_add_apply]
    simp only [nextPhase]
    congr 2
    omega
  have hbridge : certificate.coarse (finRotate L lastPhase) =
      certificate.coarse nextPhase := by
    rw [hrotateLast]
    rw [certificate.coarse_eq_iterate_of_hazard_zero _ _ hzeroBetween]
    rw [hnextFromLast]
  let target : certificate.PositiveOwner :=
    ⟨certificate.owner nextPhase, nextPhase, hnext.2.2.1, rfl⟩
  refine ⟨target, ?_⟩
  have hlastPhaseOwner : certificate.owner lastPhase = source.val := by
    exact hlastOwner
  have hchange : certificate.owner lastPhase ≠ certificate.owner nextPhase := by
    rw [hlastPhaseOwner]
    exact hnext.2.2.2.symm
  have hedge := certificate.escortEdge_of_coarse_bridge lastPhase nextPhase hchange
    hlastPositive hnext.2.2.1 hbridge
  rw [hlastPhaseOwner] at hedge
  exact hedge

/-- **Escort-cycle necessity.**  Every balanced singleton certificate forces
a closed directed walk in the raw singleton escort digraph.  The walk has
period at least two, hence visits at least two vertices.  Zero-hazard phases
and consecutive repetitions of one owner are removed internally by selecting
the last positive phase before each owner change. -/
theorem BalancedSingletonCycleCertificate.exists_escortCycle
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) :
    ∃ cycle : QuittingSingletonEscortCycle reward, 2 ≤ cycle.period := by
  let R : certificate.PositiveOwner → certificate.PositiveOwner → Prop :=
    fun source target ↦ IsQuittingSingletonEscortEdge reward source.val target.val
  letI : Nonempty certificate.PositiveOwner := certificate.positiveOwner_nonempty
  letI : Finite certificate.PositiveOwner :=
    Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨subtypeCycle⟩ :=
    Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial R
      certificate.positiveOwner_has_escort
  let cycle : QuittingSingletonEscortCycle reward :=
    subtypeCycle.map Subtype.val (fun hedge ↦ hedge)
  exact ⟨cycle, cycle.two_le_period⟩

end GameTheory
