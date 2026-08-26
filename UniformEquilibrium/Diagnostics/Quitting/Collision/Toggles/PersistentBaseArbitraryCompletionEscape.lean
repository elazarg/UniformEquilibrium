/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseNashSemanticAdapter
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity

/-!
# Arbitrary completion of a persistent quitting base

Suppose at least two players form a persistent base and each base player weakly prefers every
terminal coalition containing the whole base to the coalition obtained by deleting that player.
The remaining players may have arbitrary terminal rewards.  A mixed Nash equilibrium of their
induced finite Boolean game then extends to an exact stationary terminal Nash profile and an
all-behavior uniform equilibrium.

This is an adapter to the persistent-base compiler.  It does not assert that every quitting game
has such a base, and it makes no singleton-base claim.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every base player weakly prefers staying in the base, uniformly over all choices made by the
players outside the base. -/
def QuittingPersistentBaseComplementLeaveSafe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (base : Finset ι) : Prop :=
  ∀ who ∈ base, ∀ completion ⊆ Finset.univ \ base,
    quittingSetReward reward (base.erase who ∪ completion) who ≤
      quittingSetReward reward (base ∪ completion) who

/-- On the base coordinates, terminal reward is the literal indicator of coalition membership.
No restriction is imposed on coordinates outside the base. -/
def QuittingPersistentBaseMembershipReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (base : Finset ι) : Prop :=
  ∀ terminal who, who ∈ base →
    reward terminal who = if who ∈ terminal.1 then 1 else 0

/-- Literal membership coordinates give the sharp `0 < 1` leave comparison for every
complementary completion. -/
theorem quittingPersistentBaseMembershipReward_stay_eq_one_leave_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) (hbase : 2 ≤ base.card)
    (hmembership : QuittingPersistentBaseMembershipReward reward base)
    (who : ι) (hwho : who ∈ base)
    (completion : Finset ι) (hcompletion : completion ⊆ Finset.univ \ base) :
    quittingSetReward reward (base ∪ completion) who = 1 ∧
      quittingSetReward reward (base.erase who ∪ completion) who = 0 := by
  have hbaseNonempty : base.Nonempty := ⟨who, hwho⟩
  have heraseNonempty : (base.erase who).Nonempty := by
    have hnontrivial : base.Nontrivial :=
      Finset.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le Nat.one_lt_two hbase)
    exact hnontrivial.erase_nonempty
  have hstayNonempty : (base ∪ completion).Nonempty :=
    hbaseNonempty.mono Finset.subset_union_left
  have hleaveNonempty : (base.erase who ∪ completion).Nonempty :=
    heraseNonempty.mono Finset.subset_union_left
  have hnotCompletion : who ∉ completion := by
    intro hwhoCompletion
    exact (Finset.mem_sdiff.mp (hcompletion hwhoCompletion)).2 hwho
  constructor
  · rw [quittingSetReward_of_nonempty reward hstayNonempty,
      hmembership _ who hwho]
    simp [hwho]
  · rw [quittingSetReward_of_nonempty reward hleaveNonempty,
      hmembership _ who hwho]
    simp [hnotCompletion]

/-- Membership coordinates on a base of size at least two imply the complement-uniform leave
condition. -/
theorem QuittingPersistentBaseMembershipReward.complementLeaveSafe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) (hbase : 2 ≤ base.card)
    (hmembership : QuittingPersistentBaseMembershipReward reward base) :
    QuittingPersistentBaseComplementLeaveSafe reward base := by
  intro who hwho completion hcompletion
  obtain ⟨hstay, hleave⟩ :=
    quittingPersistentBaseMembershipReward_stay_eq_one_leave_eq_zero
      reward base hbase hmembership who hwho completion hcompletion
  rw [hstay, hleave]
  norm_num

/-- A sure-quitting persistent base kills any opponent-coalition atom that omits one of its
members. -/
theorem quittingOpponentCoalitionMass_persistentBaseRoot_eq_zero_of_not_subset
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (who : ι) (coalition : Finset ι)
    (homits : ¬base.erase who ⊆ coalition) :
    quittingOpponentCoalitionMass
        (quittingPersistentBaseRoot base free point) who coalition = 0 := by
  obtain ⟨other, hother, hmissing⟩ := Finset.not_subset.mp homits
  have hotherBase : other ∈ base := Finset.mem_of_mem_erase hother
  have hotherNe : other ≠ who := Finset.ne_of_mem_erase hother
  have hotherComplement : other ∈ Finset.univ.erase who \ coalition := by
    simp [hotherNe, hmissing]
  unfold quittingOpponentCoalitionMass
  rw [Finset.prod_eq_zero hotherComplement (by
    rw [quittingPersistentBaseRoot_apply_of_mem_base base free point hotherBase]
    simp)]
  simp

/-- The complement-quantified leave condition supplies every persistent player's endpoint sign
at every arbitrary induced-game mixed point. -/
theorem quittingPersistentBaseRoot_endpointDifference_nonneg_of_complementLeaveSafe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι)
    (hbase : 2 ≤ base.card)
    (hsafe : QuittingPersistentBaseComplementLeaveSafe reward base)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (who : ι) (hwho : who ∈ base) :
    0 ≤ quittingRootEndpointDifference reward 0
      (quittingPersistentBaseRoot base free point) who := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  apply Finset.sum_nonneg
  intro coalition hcoalition
  rw [Finset.mem_powerset] at hcoalition
  by_cases hcontains : base.erase who ⊆ coalition
  · have heraseNonempty : (base.erase who).Nonempty := by
      have hnontrivial : base.Nontrivial :=
        Finset.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le Nat.one_lt_two hbase)
      exact hnontrivial.erase_nonempty
    have hcoalitionNonempty : coalition.Nonempty := heraseNonempty.mono hcontains
    let completion := coalition \ base
    have hcompletion : completion ⊆ Finset.univ \ base := by
      intro player hplayer
      simp only [completion, Finset.mem_sdiff] at hplayer ⊢
      exact ⟨Finset.mem_univ player, hplayer.2⟩
    have hcoalitionEq : coalition = base.erase who ∪ completion := by
      ext player
      constructor
      · intro hplayer
        by_cases hplayerBase : player ∈ base
        · have hplayerNe : player ≠ who := by
            intro heq
            subst player
            exact (Finset.mem_erase.mp (hcoalition hplayer)).1 rfl
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hplayerNe, hplayerBase⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hplayer, hplayerBase⟩)
      · intro hplayer
        rcases Finset.mem_union.mp hplayer with hplayerErase | hplayerCompletion
        · exact hcontains hplayerErase
        · exact (Finset.mem_sdiff.mp hplayerCompletion).1
    have hinsertEq : insert who coalition = base ∪ completion := by
      ext player
      constructor
      · intro hplayer
        rcases Finset.mem_insert.mp hplayer with rfl | hplayerCoalition
        · exact Finset.mem_union_left _ hwho
        · rw [hcoalitionEq] at hplayerCoalition
          rcases Finset.mem_union.mp hplayerCoalition with hplayerErase | hplayerCompletion
          · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase hplayerErase)
          · exact Finset.mem_union_right _ hplayerCompletion
      · intro hplayer
        rcases Finset.mem_union.mp hplayer with hplayerBase | hplayerCompletion
        · by_cases heq : player = who
          · exact Finset.mem_insert.mpr (Or.inl heq)
          · exact Finset.mem_insert.mpr (Or.inr
              (hcontains (Finset.mem_erase.mpr ⟨heq, hplayerBase⟩)))
        · exact Finset.mem_insert.mpr (Or.inr ((hcoalitionEq.symm ▸
            Finset.mem_union_right (base.erase who) hplayerCompletion)))
    have hleave := hsafe who hwho completion hcompletion
    rw [← hcoalitionEq, ← hinsertEq] at hleave
    rw [quittingEndpointInsertionToggle_of_nonempty
      reward 0 who coalition hcoalitionNonempty]
    have htoggle :
        0 ≤ reward ⟨insert who coalition, Finset.insert_nonempty who coalition⟩ who -
          reward ⟨coalition, hcoalitionNonempty⟩ who := by
      rw [sub_nonneg]
      rw [quittingSetReward_of_nonempty reward hcoalitionNonempty] at hleave
      simpa using hleave
    exact mul_nonneg
      (quittingOpponentCoalitionMass_nonneg
        (quittingPersistentBaseRoot base free point) who coalition)
      htoggle
  · rw [quittingOpponentCoalitionMass_persistentBaseRoot_eq_zero_of_not_subset
      base free point who coalition hcontains]
    simp

/-- The complement construction has no outsider coordinates. -/
theorem persistentBase_union_complement_eq_univ (base : Finset ι) :
    base ∪ (Finset.univ \ base) = Finset.univ := by
  ext player
  simp

/-- An induced Nash point exists and extends to the all-behavior persistent-base certificate.
The free-player rewards are unrestricted. -/
theorem exists_quittingPersistentBaseCertificate_of_complementLeaveSafe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) (hbase : 2 ≤ base.card)
    (hsafe : QuittingPersistentBaseComplementLeaveSafe reward base) :
    ∃ point ∈ quittingPersistentBaseNashSet reward base (Finset.univ \ base),
      Nonempty (QuittingPersistentBaseCertificate reward base (Finset.univ \ base)
        (quittingPersistentBaseRoot base (Finset.univ \ base) point)) := by
  obtain ⟨point, hpoint⟩ :=
    quittingPersistentBaseNashSet_nonempty reward base (Finset.univ \ base)
  refine ⟨point, hpoint, ?_⟩
  have hdisjoint : Disjoint base (Finset.univ \ base) := by
    rw [Finset.disjoint_left]
    intro player hplayerBase hplayerFree
    exact (Finset.mem_sdiff.mp hplayerFree).2 hplayerBase
  apply nonempty_quittingPersistentBaseCertificate_of_inducedNash
    reward base (Finset.univ \ base) hdisjoint hbase point hpoint
  · intro who hwho
    exact quittingPersistentBaseRoot_endpointDifference_nonneg_of_complementLeaveSafe
      reward base (Finset.univ \ base) hbase hsafe point who hwho
  · intro who houtside
    exfalso
    apply houtside
    rw [persistentBase_union_complement_eq_univ]
    exact Finset.mem_univ who

/-- A persistent-base certificate gives exact stationary terminal Nash against the full behavioral
deviation class. -/
theorem QuittingPersistentBaseCertificate.isZeroAsymptoticNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {base free : Finset ι} {root : ι → PMF Bool}
    (certificate : QuittingPersistentBaseCertificate reward base free root) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 (quittingStationaryProfile reward root) := by
  let value : Payoff ι := fun player =>
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) player
  apply isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    reward root value
  · rw [certificate.continueMass_eq_zero]
    norm_num
  · funext who
    exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who
  · exact certificate.endpointNash
  · intro who
    rw [certificate.opponents_continueMass_eq_zero who]
    norm_num

/-- **Arbitrary-completion escape.**  A complement-uniform persistent-base leave inequality
produces one stationary profile that is exact terminal Nash against unrestricted behavioral
deviations and whose terminal payoff is a uniform-equilibrium payoff. -/
theorem exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) (hbase : 2 ≤ base.card)
    (hsafe : QuittingPersistentBaseComplementLeaveSafe reward base) :
    ∃ point ∈ quittingPersistentBaseNashSet reward base (Finset.univ \ base),
      let root := quittingPersistentBaseRoot base (Finset.univ \ base) point
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0 (quittingStationaryProfile reward root) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) := by
  obtain ⟨point, hpoint, ⟨certificate⟩⟩ :=
    exists_quittingPersistentBaseCertificate_of_complementLeaveSafe
      reward base hbase hsafe
  exact ⟨point, hpoint, certificate.isZeroAsymptoticNash,
    certificate.isUniformEquilibriumPayoff⟩

/-- Literal membership payoffs on a base of size at least two have an exact stationary terminal
Nash completion for arbitrary rewards on every complementary coordinate. -/
theorem exists_exactTerminalNash_and_uniformPayoff_of_persistentBaseMembershipReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) (hbase : 2 ≤ base.card)
    (hmembership : QuittingPersistentBaseMembershipReward reward base) :
    ∃ point ∈ quittingPersistentBaseNashSet reward base (Finset.univ \ base),
      let root := quittingPersistentBaseRoot base (Finset.univ \ base) point
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0 (quittingStationaryProfile reward root) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) := by
  exact exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe
    reward base hbase (hmembership.complementLeaveSafe reward base hbase)

end GameTheory
