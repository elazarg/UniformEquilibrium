/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PunishmentNormalAtomicCollisionHandoff
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.RobustJoinPredecessorBase
import UniformEquilibrium.Quitting.RewardBound

/-!
# Strict background reversal on selected collision cycles

A positive selected join edge cannot remain weakly favorable on every
background around a whole supplied cycle in a quitting game with no uniform-
equilibrium payoff: otherwise the cycle is a robust-join cycle and the
persistent-base compiler applies.  This implication is valid for every
finite player type.

For four players, the maintained hard residual supplies a fixed-point-free
positive collision map.  Consequently a literal reward table on which every
positive singleton join remains weakly favorable on every disjoint
background has a uniform-equilibrium payoff.  The Fin4 statement has no
supplied coordinate bound, residual, selector, or cycle hypothesis.
-/

noncomputable section

namespace GameTheory

open Math.FiniteSerialRelation
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every distinct strictly favorable singleton join remains weakly
favorable after adding any background which contains neither endpoint. -/
def QuittingNoStrictBackgroundReversal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ enforcer joiner, enforcer ≠ joiner →
    quittingSetReward reward {enforcer} joiner <
        quittingSetReward reward {enforcer, joiner} joiner →
      ∀ background,
        background ⊆ (Finset.univ.erase enforcer).erase joiner →
          quittingSetReward reward (insert enforcer background) joiner ≤
            quittingSetReward reward
              (insert joiner (insert enforcer background)) joiner

/-- On any supplied positive selected cycle in an arbitrary finite quitting
game without a uniform-equilibrium payoff, some selected edge reverses
strictly on a nonempty background. -/
theorem selectedCycle_has_strictBackgroundReversal_of_no_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (selected : ι → ι → Prop)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (cycle : PeriodicCycle selected)
    (hpositive : ∀ {enforcer joiner}, selected enforcer joiner →
      quittingSetReward reward {enforcer} joiner + gamma ≤
        quittingSetReward reward {enforcer, joiner} joiner)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ time background,
      selected (cycle.vertex time) (cycle.vertex (time + 1)) ∧
        cycle.vertex time ≠ cycle.vertex (time + 1) ∧
        background.Nonempty ∧
        background ⊆
          (Finset.univ.erase (cycle.vertex time)).erase
            (cycle.vertex (time + 1)) ∧
        quittingSetReward reward
            (insert (cycle.vertex (time + 1))
              (insert (cycle.vertex time) background))
            (cycle.vertex (time + 1)) <
          quittingSetReward reward
            (insert (cycle.vertex time) background)
            (cycle.vertex (time + 1)) := by
  have hcycleNe : ∀ time,
      cycle.vertex time ≠ cycle.vertex (time + 1) := by
    intro time heq
    have hgap := hpositive (cycle.edge time)
    have hsame :
        quittingSetReward reward {cycle.vertex time} (cycle.vertex time) +
            gamma ≤
          quittingSetReward reward {cycle.vertex time} (cycle.vertex time) := by
      simpa [heq] using hgap
    linarith
  by_contra hreverse
  let robustCycle : PeriodicCycle (QuittingRobustJoin reward) := {
    period := cycle.period
    period_pos := cycle.period_pos
    vertex := cycle.vertex
    vertex_periodic := cycle.vertex_periodic
    edge := by
      intro time
      have hselected := cycle.edge time
      have hgap := hpositive hselected
      constructor
      · exact hcycleNe time
      · intro background hbackground
        by_contra hweak
        have hstrict :
            quittingSetReward reward
                (insert (cycle.vertex (time + 1))
                  (insert (cycle.vertex time) background))
                (cycle.vertex (time + 1)) <
              quittingSetReward reward
                (insert (cycle.vertex time) background)
                (cycle.vertex (time + 1)) := lt_of_not_ge hweak
        by_cases hnonempty : background.Nonempty
        · exact hreverse ⟨time, background, hselected, hcycleNe time,
            hnonempty, hbackground, hstrict⟩
        · have hempty : background = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
          subst background
          have hgap' :
              quittingSetReward reward {cycle.vertex time}
                    (cycle.vertex (time + 1)) + gamma ≤
                quittingSetReward reward
                    {cycle.vertex (time + 1), cycle.vertex time}
                    (cycle.vertex (time + 1)) := by
            simpa only [Finset.insert_empty, Finset.pair_comm] using hgap
          have hstrict' :
              quittingSetReward reward
                    {cycle.vertex (time + 1), cycle.vertex time}
                    (cycle.vertex (time + 1)) <
                quittingSetReward reward {cycle.vertex time}
                    (cycle.vertex (time + 1)) := by
            simpa only [Finset.insert_empty] using hstrict
          linarith }
  obtain ⟨point, hpoint, _hnash, huniform⟩ :=
    exists_exactTerminalNash_and_uniformPayoff_of_robustJoinCycle
      reward robustCycle
  exact hnot ⟨_, huniform⟩

/-- A four-player table with no strict background reversal has a literal
uniform-equilibrium payoff.  The canonical reward bound and the hard
residual collision selector are internal to the proof. -/
theorem finFour_exists_uniformPayoff_of_noStrictBackgroundReversal
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnoReversal : QuittingNoStrictBackgroundReversal reward) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hnot
  obtain ⟨residual⟩ :=
    nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
      reward (abs_reward_le_quittingRewardBound reward) hnot
  obtain ⟨next, _hnextNe, hnextGap⟩ :=
    residual.exists_fixedPointFree_terminalGap_collisionMap
  let selected : Fin 4 → Fin 4 → Prop :=
    fun enforcer joiner ↦ next enforcer = joiner
  have hserial : ∀ enforcer, ∃ joiner, selected enforcer joiner :=
    fun enforcer ↦ ⟨next enforcer, rfl⟩
  obtain ⟨cycle⟩ :=
    nonempty_periodicCycle_of_serial selected hserial
  have hpositive : ∀ {enforcer joiner}, selected enforcer joiner →
      quittingSetReward reward {enforcer} joiner +
          residual.witness.terminalGap ≤
        quittingSetReward reward {enforcer, joiner} joiner := by
    intro enforcer joiner hedge
    change next enforcer = joiner at hedge
    subst joiner
    exact hnextGap enforcer
  obtain ⟨time, background, hedge, hedgesNe, hbackgroundNonempty,
      hbackground, hreverse⟩ :=
    selectedCycle_has_strictBackgroundReversal_of_no_uniformPayoff
      reward selected residual.witness.terminalGap
      residual.witness.terminalGap_pos cycle hpositive hnot
  have hsingletonPositive :
      quittingSetReward reward {cycle.vertex time}
          (cycle.vertex (time + 1)) <
        quittingSetReward reward
          {cycle.vertex time, cycle.vertex (time + 1)}
          (cycle.vertex (time + 1)) := by
    have hgap := hpositive hedge
    linarith [residual.witness.terminalGap_pos]
  have hweak := hnoReversal (cycle.vertex time)
    (cycle.vertex (time + 1)) hedgesNe hsingletonPositive
    background hbackground
  exact (not_lt_of_ge hweak) hreverse

end GameTheory
