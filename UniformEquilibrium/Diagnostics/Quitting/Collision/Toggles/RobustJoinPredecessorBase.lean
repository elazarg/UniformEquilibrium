/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.FiniteSerialRelation
import GameTheory.Math.DAG
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseArbitraryCompletionEscape

/-!
# Robust-join predecessor bases

A player `enforcer` robustly joins `joiner` when, in every terminal
background avoiding both players, adding `joiner` in the presence of
`enforcer` weakly improves `joiner`'s reward.  A finite base with an incoming
robust edge at every vertex is therefore complement-uniformly leave-safe.
The existing persistent-base compiler then supplies an exact stationary
terminal Nash profile against unrestricted behavioral deviations and a
uniform-equilibrium payoff.

The cycle layer uses `Math.FiniteSerialRelation.PeriodicCycle` as a supplied
finite-cycle representation.  The no-uniform-payoff consequences below state
both absence of such cycles and the exact predecessor-free-vertex property
for every nonempty induced finite subgraph.  No converse characterization of
all leave-safe bases is asserted.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.FiniteSerialRelation
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Adding `joiner` in the presence of `enforcer` never hurts `joiner`,
uniformly over backgrounds containing neither player.  Distinctness is part
of the relation. -/
def QuittingRobustJoin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (enforcer joiner : ι) : Prop :=
  enforcer ≠ joiner ∧
    ∀ background,
      background ⊆ (Finset.univ.erase enforcer).erase joiner →
        quittingSetReward reward (insert enforcer background) joiner ≤
          quittingSetReward reward
            (insert joiner (insert enforcer background)) joiner

/-- A base of at least two players in which every vertex has a robust
predecessor inside the base. -/
def QuittingRobustPredecessorBase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) : Prop :=
  2 ≤ base.card ∧
    ∀ joiner ∈ base,
      ∃ enforcer ∈ base, QuittingRobustJoin reward enforcer joiner

namespace QuittingRobustPredecessorBase

/-- A robust-predecessor base satisfies the literal complement-uniform leave
condition consumed by the persistent-base arbitrary-completion compiler. -/
theorem complementLeaveSafe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι)
    (hbase : QuittingRobustPredecessorBase reward base) :
    QuittingPersistentBaseComplementLeaveSafe reward base := by
  intro joiner hjoiner completion hcompletion
  obtain ⟨enforcer, henforcer, hrobust⟩ := hbase.2 joiner hjoiner
  let background := (base.erase enforcer).erase joiner ∪ completion
  have henforcerNe : enforcer ≠ joiner := hrobust.1
  have hbackground :
      background ⊆ (Finset.univ.erase enforcer).erase joiner := by
    intro player hplayer
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
      Finset.mem_univ player⟩⟩
    · rcases Finset.mem_union.mp hplayer with hplayer | hplayer
      · exact (Finset.mem_erase.mp hplayer).1
      · intro heq
        subst player
        exact (Finset.mem_sdiff.mp (hcompletion hplayer)).2 hjoiner
    · rcases Finset.mem_union.mp hplayer with hplayer | hplayer
      · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hplayer).2).1
      · intro heq
        subst player
        exact (Finset.mem_sdiff.mp (hcompletion hplayer)).2 henforcer
  have hcomparison := hrobust.2 background hbackground
  have hwithoutJoiner :
      insert enforcer background = base.erase joiner ∪ completion := by
    ext player
    constructor
    · intro hplayer
      rcases Finset.mem_insert.mp hplayer with rfl | hplayer
      · exact Finset.mem_union_left completion
          (Finset.mem_erase.mpr ⟨henforcerNe, henforcer⟩)
      · rcases Finset.mem_union.mp hplayer with hplayer | hplayer
        · exact Finset.mem_union_left completion
            (Finset.mem_erase.mpr
              ⟨(Finset.mem_erase.mp hplayer).1,
                (Finset.mem_erase.mp
                  (Finset.mem_erase.mp hplayer).2).2⟩)
        · exact Finset.mem_union_right (base.erase joiner) hplayer
    · intro hplayer
      rcases Finset.mem_union.mp hplayer with hplayer | hplayer
      · by_cases heq : player = enforcer
        · exact Finset.mem_insert.mpr (Or.inl heq)
        · exact Finset.mem_insert.mpr (Or.inr
            (Finset.mem_union_left completion
              (Finset.mem_erase.mpr
                ⟨(Finset.mem_erase.mp hplayer).1,
                  Finset.mem_erase.mpr
                    ⟨heq, (Finset.mem_erase.mp hplayer).2⟩⟩)))
      · exact Finset.mem_insert.mpr (Or.inr
          (Finset.mem_union_right _ hplayer))
  have hwithJoiner :
      insert joiner (base.erase joiner ∪ completion) =
        base ∪ completion := by
    ext player
    constructor
    · intro hplayer
      rcases Finset.mem_insert.mp hplayer with rfl | hplayer
      · exact Finset.mem_union_left completion hjoiner
      · rcases Finset.mem_union.mp hplayer with hplayer | hplayer
        · exact Finset.mem_union_left completion
            (Finset.mem_of_mem_erase hplayer)
        · exact Finset.mem_union_right base hplayer
    · intro hplayer
      rcases Finset.mem_union.mp hplayer with hplayer | hplayer
      · by_cases heq : player = joiner
        · exact Finset.mem_insert.mpr (Or.inl heq)
        · exact Finset.mem_insert.mpr (Or.inr
            (Finset.mem_union_left completion
              (Finset.mem_erase.mpr ⟨heq, hplayer⟩)))
      · exact Finset.mem_insert.mpr (Or.inr
          (Finset.mem_union_right _ hplayer))
  rw [hwithoutJoiner, hwithJoiner] at hcomparison
  exact hcomparison

end QuittingRobustPredecessorBase

/-- A robust-predecessor base compiles to one exact stationary terminal Nash
profile against every behavioral deviation, whose payoff is a uniform-
equilibrium payoff. -/
theorem exists_exactTerminalNash_and_uniformPayoff_of_robustPredecessorBase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι)
    (hbase : QuittingRobustPredecessorBase reward base) :
    ∃ point ∈ quittingPersistentBaseNashSet reward base
        (Finset.univ \ base),
      let root := quittingPersistentBaseRoot base
        (Finset.univ \ base) point
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0
          (quittingStationaryProfile reward root) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) := by
  exact exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe
    reward base hbase.1 (hbase.complementLeaveSafe reward base)

/-! ## Supplied robust cycles -/

/-- The vertex set visited during one displayed period of a supplied robust
join cycle.  Repeated vertices are harmless; irreflexivity forces at least two
distinct vertices in the range. -/
def quittingRobustJoinCycleBase
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (cycle : PeriodicCycle (QuittingRobustJoin reward)) : Finset ι :=
  (Finset.range cycle.period).image cycle.vertex

/-- The one-period vertex range of a robust-join cycle is a literal robust-
predecessor base. -/
theorem quittingRobustJoinCycle_robustPredecessorBase
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (cycle : PeriodicCycle (QuittingRobustJoin reward)) :
    QuittingRobustPredecessorBase reward
      (quittingRobustJoinCycleBase cycle) := by
  have hirreflexive : ∀ player, ¬QuittingRobustJoin reward player player := by
    intro player hjoin
    exact hjoin.1 rfl
  have hperiod := cycle.two_le_period_of_irreflexive hirreflexive
  have hzeroMem : cycle.vertex 0 ∈ quittingRobustJoinCycleBase cycle := by
    apply Finset.mem_image.mpr
    exact ⟨0, Finset.mem_range.mpr (lt_of_lt_of_le Nat.zero_lt_two hperiod), rfl⟩
  have honeMem : cycle.vertex 1 ∈ quittingRobustJoinCycleBase cycle := by
    apply Finset.mem_image.mpr
    exact ⟨1, Finset.mem_range.mpr (lt_of_lt_of_le Nat.one_lt_two hperiod), rfl⟩
  have hzeroNeOne : cycle.vertex 0 ≠ cycle.vertex 1 := (cycle.edge 0).1
  constructor
  · rw [show 2 ≤ (quittingRobustJoinCycleBase cycle).card ↔
        1 < (quittingRobustJoinCycleBase cycle).card by omega,
      Finset.one_lt_card]
    exact ⟨cycle.vertex 0, hzeroMem, cycle.vertex 1, honeMem, hzeroNeOne⟩
  · intro joiner hjoiner
    obtain ⟨time, htime, rfl⟩ := Finset.mem_image.mp hjoiner
    have htimeLt : time < cycle.period := Finset.mem_range.mp htime
    by_cases htimeZero : time = 0
    · subst time
      let previous := cycle.period - 1
      have hpreviousLt : previous < cycle.period := by
        dsimp only [previous]
        omega
      have hpreviousMem :
          cycle.vertex previous ∈ quittingRobustJoinCycleBase cycle := by
        apply Finset.mem_image.mpr
        exact ⟨previous, Finset.mem_range.mpr hpreviousLt, rfl⟩
      refine ⟨cycle.vertex previous, hpreviousMem, ?_⟩
      have hedge := cycle.edge previous
      have hpreviousSucc : previous + 1 = cycle.period := by
        dsimp only [previous]
        omega
      rw [hpreviousSucc] at hedge
      have hclose : cycle.vertex cycle.period = cycle.vertex 0 := by
        simpa using cycle.vertex_periodic 0
      simpa [hclose] using hedge
    · let previous := time - 1
      have hpreviousLt : previous < cycle.period := by
        dsimp only [previous]
        omega
      have hpreviousMem :
          cycle.vertex previous ∈ quittingRobustJoinCycleBase cycle := by
        apply Finset.mem_image.mpr
        exact ⟨previous, Finset.mem_range.mpr hpreviousLt, rfl⟩
      refine ⟨cycle.vertex previous, hpreviousMem, ?_⟩
      have hedge := cycle.edge previous
      have hpreviousSucc : previous + 1 = time := by
        dsimp only [previous]
        omega
      simpa [hpreviousSucc] using hedge

/-- A supplied robust-join cycle compiles to one exact stationary terminal
Nash profile against unrestricted behavioral deviations and a uniform-
equilibrium payoff. -/
theorem exists_exactTerminalNash_and_uniformPayoff_of_robustJoinCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : PeriodicCycle (QuittingRobustJoin reward)) :
    ∃ point ∈ quittingPersistentBaseNashSet reward
        (quittingRobustJoinCycleBase cycle)
        (Finset.univ \ quittingRobustJoinCycleBase cycle),
      let root := quittingPersistentBaseRoot
        (quittingRobustJoinCycleBase cycle)
        (Finset.univ \ quittingRobustJoinCycleBase cycle) point
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0
          (quittingStationaryProfile reward root) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) := by
  exact exists_exactTerminalNash_and_uniformPayoff_of_robustPredecessorBase
    reward (quittingRobustJoinCycleBase cycle)
      (quittingRobustJoinCycle_robustPredecessorBase cycle)

/-! ## Counterexample-side graph consequences -/

/-- The finite predecessor set of a vertex in the robust-join graph. -/
noncomputable def quittingRobustJoinPredecessors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (joiner : ι) : Finset ι :=
  by
    classical
    exact Finset.univ.filter fun enforcer =>
      QuittingRobustJoin reward enforcer joiner

@[simp] theorem mem_quittingRobustJoinPredecessors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (enforcer joiner : ι) :
    enforcer ∈ quittingRobustJoinPredecessors reward joiner ↔
      QuittingRobustJoin reward enforcer joiner := by
  simp [quittingRobustJoinPredecessors]

/-- If no uniform-equilibrium payoff exists, every nonempty induced robust-
join subgraph has a vertex with no robust predecessor inside that subgraph. -/
theorem exists_robustJoin_predecessorFree_vertex_of_no_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (vertices : Finset ι) (hvertices : vertices.Nonempty) :
    ∃ joiner ∈ vertices,
      ∀ enforcer ∈ vertices,
        ¬QuittingRobustJoin reward enforcer joiner := by
  by_contra hsource
  have hpredecessor : ∀ joiner ∈ vertices,
      ∃ enforcer ∈ vertices,
        QuittingRobustJoin reward enforcer joiner := by
    intro joiner hjoiner
    by_contra hnone
    apply hsource
    exact ⟨joiner, hjoiner, fun enforcer henforcer hjoin =>
      hnone ⟨enforcer, henforcer, hjoin⟩⟩
  obtain ⟨joiner, hjoiner⟩ := hvertices
  obtain ⟨enforcer, henforcer, hrobust⟩ :=
    hpredecessor joiner hjoiner
  have hcard : 2 ≤ vertices.card := by
    rw [show 2 ≤ vertices.card ↔ 1 < vertices.card by omega,
      Finset.one_lt_card]
    exact ⟨enforcer, henforcer, joiner, hjoiner, hrobust.1⟩
  have hbase : QuittingRobustPredecessorBase reward vertices :=
    ⟨hcard, hpredecessor⟩
  obtain ⟨point, hpoint, _hnash, huniform⟩ :=
    exists_exactTerminalNash_and_uniformPayoff_of_robustPredecessorBase
      reward vertices hbase
  exact hno ⟨fun player => quittingTerminalPayoff reward
    (quittingStationaryProfile reward
      (quittingPersistentBaseRoot vertices
        (Finset.univ \ vertices) point)) player, huniform⟩

/-- The robust-join relation of a finite quitting game without a uniform-
equilibrium payoff is acyclic in the standard directed-relation sense: no
nonempty transitive path returns to its starting vertex. -/
theorem quittingRobustJoin_acyclic_of_no_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    GameTheory.Math.DAG.Acyclic (QuittingRobustJoin reward) := by
  classical
  have hwellFounded : WellFounded (QuittingRobustJoin reward) := by
    rw [WellFounded.wellFounded_iff_has_min]
    intro vertices hvertices
    let support := Finset.univ.filter fun player => player ∈ vertices
    have hsupport : support.Nonempty := by
      obtain ⟨player, hplayer⟩ := hvertices
      exact ⟨player, by simp [support]; exact hplayer⟩
    obtain ⟨joiner, hjoiner, hminimal⟩ :=
      exists_robustJoin_predecessorFree_vertex_of_no_uniformPayoff
        reward hno support hsupport
    refine ⟨joiner, ?_, ?_⟩
    · simpa [support] using hjoiner
    · intro enforcer henforcer hrobust
      apply hminimal enforcer
      · simp [support]
        exact henforcer
      · exact hrobust
  have hirreflexive : Std.Irrefl
      (Relation.TransGen (QuittingRobustJoin reward)) :=
    hwellFounded.transGen.irrefl
  exact hirreflexive.irrefl

/-- The standard finite-DAG API turns the checked robust-join acyclicity into
a topological order listing every robust predecessor before its joiner. -/
theorem nonempty_robustJoinTopologicalOrder_of_no_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    Nonempty
      (GameTheory.Math.DAG.TopologicalOrder
        (quittingRobustJoinPredecessors reward)) := by
  apply GameTheory.Math.DAG.topologicalOrder_of_acyclic
  simpa only [mem_quittingRobustJoinPredecessors] using
    quittingRobustJoin_acyclic_of_no_uniformPayoff reward hno

/-- Equivalently, no periodic robust-join cycle can exist in a game without
a uniform-equilibrium payoff. -/
theorem not_nonempty_robustJoinPeriodicCycle_of_no_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ¬Nonempty (PeriodicCycle (QuittingRobustJoin reward)) := by
  rintro ⟨cycle⟩
  obtain ⟨point, hpoint, _hnash, huniform⟩ :=
    exists_exactTerminalNash_and_uniformPayoff_of_robustJoinCycle
      reward cycle
  exact hno ⟨fun player => quittingTerminalPayoff reward
    (quittingStationaryProfile reward
      (quittingPersistentBaseRoot
        (quittingRobustJoinCycleBase cycle)
        (Finset.univ \ quittingRobustJoinCycleBase cycle) point)) player,
    huniform⟩

end GameTheory
