/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicBlockProfile
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile

/-!
# A period-three schedule with unequal visit multiplicities

The block interface indexes phases by `Fin (m + 1)` and carries a separate
hazard vector at each phase, so a player may be scheduled at several phases,
with a different probability at each, while another player is never scheduled
at all.  This file exhibits such a schedule on a three-player table.

The table pays player `0` the value `1` whenever the realized quitter set is
`{0}` or `{1}`, and pays `0` on every other coalition and to every other
player.  The schedule has period three: player `0` quits with probability
`1/2` at phase zero and `1/4` at phase two, player `1` quits with probability
`1/3` at phase one, and player `2` never quits.  The visit multiplicities are
`2`, `1` and `0`, and the two visits of player `0` carry different
probabilities.

The displayed value is the constant vector `(1, 0, 0)`.  Player `0` is exactly
indifferent at both of its phases because its solo row already pays `1`;
player `1` is indifferent because everything it can reach pays it `0`; and
player `2` never gains by joining.

This is a bounded checked instance recording that the interface accepts
schedules whose phases are not a common tile.  It proves nothing about any
other table.
-/

noncomputable section

namespace GameTheory
namespace BlockPeriodicMultiVisit

open Math.PMFProduct

/-- The three players. -/
abbrev Player := Fin 3

/-! ## The table -/

/-- The table paying player `0` the value `1` on the two coalitions `{0}` and
`{1}`, and `0` everywhere else. -/
def multiVisitReward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S who => if who = 0 ∧ (S.1 = {0} ∨ S.1 = {1}) then 1 else 0

theorem multiVisitReward_singleton_zero (who : Player) :
    multiVisitReward (quittingSingletonTerminal 0) who = if who = 0 then 1 else 0 := by
  rw [multiVisitReward]
  by_cases hwho : who = 0
  · rw [if_pos ⟨hwho, Or.inl rfl⟩, if_pos hwho]
  · rw [if_neg (fun hcontra ↦ hwho hcontra.1), if_neg hwho]

theorem multiVisitReward_singleton_one (who : Player) :
    multiVisitReward (quittingSingletonTerminal 1) who = if who = 0 then 1 else 0 := by
  rw [multiVisitReward]
  by_cases hwho : who = 0
  · rw [if_pos ⟨hwho, Or.inr rfl⟩, if_pos hwho]
  · rw [if_neg (fun hcontra ↦ hwho hcontra.1), if_neg hwho]

theorem multiVisitReward_singleton_two (who : Player) :
    multiVisitReward (quittingSingletonTerminal 2) who = 0 := by
  rw [multiVisitReward]
  refine if_neg ?_
  revert who
  decide

/-- Every two-element coalition pays each of its members zero. -/
theorem multiVisitReward_pair {owner who : Player} (hne : owner ≠ who) :
    multiVisitReward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who = 0 := by
  rw [multiVisitReward]
  refine if_neg ?_
  revert hne
  revert owner who
  decide

theorem one_le_multiVisitRewardBound :
    (1 : ℝ) ≤ quittingRewardBound multiVisitReward := by
  have hentry := abs_reward_le_quittingRewardBound multiVisitReward
    (quittingSingletonTerminal 0) 0
  rw [multiVisitReward_singleton_zero, if_pos rfl] at hentry
  simpa using hentry

/-! ## The schedule -/

/-- The player scheduled at each phase: player `0` twice, player `1` once. -/
def multiVisitOwner : Fin 3 → Player := ![0, 1, 0]

/-- The quit probability at each phase; the two visits of player `0` differ. -/
def multiVisitRate : Fin 3 → ℝ := ![1 / 2, 1 / 3, 1 / 4]

theorem multiVisitRate_nonneg (k : Fin 3) : 0 ≤ multiVisitRate k := by
  fin_cases k <;> norm_num [multiVisitRate]

theorem multiVisitRate_le_one (k : Fin 3) : multiVisitRate k ≤ 1 := by
  fin_cases k <;> norm_num [multiVisitRate]

/-- The hazard schedule: the scheduled player carries the phase's rate and
everybody else carries zero. -/
def multiVisitHazard : Fin 3 → Player → ℝ :=
  fun k who ↦ if who = multiVisitOwner k then multiVisitRate k else 0

theorem multiVisitHazard_nonneg : ∀ k who, 0 ≤ multiVisitHazard k who := by
  intro k who
  rw [multiVisitHazard]
  by_cases hwho : who = multiVisitOwner k
  · rw [if_pos hwho]
    exact multiVisitRate_nonneg k
  · rw [if_neg hwho]

theorem multiVisitHazard_le_one : ∀ k who, multiVisitHazard k who ≤ 1 := by
  intro k who
  rw [multiVisitHazard]
  by_cases hwho : who = multiVisitOwner k
  · rw [if_pos hwho]
    exact multiVisitRate_le_one k
  · rw [if_neg hwho]
    norm_num

/-- Each phase of the schedule is the single-quitter row of its scheduled
player. -/
theorem quittingBlockCycle_multiVisitHazard (k : Fin 3) :
    quittingBlockCycle multiVisitHazard multiVisitHazard_nonneg
        multiVisitHazard_le_one k =
      quittingSoloMixedRoot (multiVisitOwner k)
        (quittingHazardCoin (multiVisitRate k) (multiVisitRate_nonneg k)
          (multiVisitRate_le_one k)) := by
  funext who
  by_cases hwho : who = multiVisitOwner k
  · rw [hwho, quittingSoloMixedRoot_self]
    exact quittingHazardCoin_congr (multiVisitHazard_nonneg k (multiVisitOwner k))
      (multiVisitHazard_le_one k (multiVisitOwner k)) (multiVisitRate_nonneg k)
      (multiVisitRate_le_one k)
      (by rw [quittingHazardCoin_true_toReal, quittingHazardCoin_true_toReal,
            multiVisitHazard, if_pos rfl])
  · rw [quittingSoloMixedRoot_of_ne hwho]
    exact quittingHazardCoin_eq_pure_false_of_quitMass_zero (multiVisitHazard_nonneg k who)
      (multiVisitHazard_le_one k who)
      (by rw [quittingHazardCoin_true_toReal, multiVisitHazard, if_neg hwho])

/-! ## The displayed value -/

/-- The displayed value, constant across the phases. -/
def multiVisitValue : Fin 4 → Payoff Player := fun _ ↦ ![1, 0, 0]

theorem abs_multiVisitValue_le (stage : Fin 4) (who : Player) :
    |multiVisitValue stage who| ≤ quittingRewardBound multiVisitReward := by
  have hbound := one_le_multiVisitRewardBound
  fin_cases who <;> simp [multiVisitValue] <;> linarith

/-! ## The certificate -/

theorem multiVisit_isQuittingBlockCertificate :
    IsQuittingBlockCertificate multiVisitReward multiVisitHazard multiVisitValue := by
  refine isQuittingBlockCertificate_of_root multiVisitHazard_nonneg
    multiVisitHazard_le_one abs_multiVisitValue_le rfl ?_ ?_ ?_ ?_
  · intro k
    funext who
    rw [quittingBlockCycle_multiVisitHazard, quittingRootSuccessorPayoff_soloMixedRoot,
      quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
    fin_cases k <;> fin_cases who <;>
      simp [multiVisitValue, multiVisitOwner, multiVisitRate,
        multiVisitReward_singleton_zero, multiVisitReward_singleton_one]
  · intro k
    rw [quittingBlockCycle_multiVisitHazard]
    refine isZeroQuittingRootEndpointNash_soloMixedRoot multiVisitReward _ _ _ ?_ ?_
    · fin_cases k <;>
        simp [multiVisitValue, multiVisitOwner, multiVisitReward_singleton_zero,
          multiVisitReward_singleton_one]
    · intro who hne
      rw [multiVisitReward_pair (Ne.symm hne), quittingHazardCoin_true_toReal,
        quittingHazardCoin_false_toReal]
      fin_cases k <;> fin_cases who <;>
        simp_all [multiVisitValue, multiVisitOwner, multiVisitRate,
          multiVisitReward_singleton_zero, multiVisitReward_singleton_one,
          multiVisitReward_singleton_two]
  · refine ⟨0, continueMass_lt_one_of_pos (multiVisitHazard_nonneg 0)
      (multiVisitHazard_le_one 0) (i₀ := 0) ?_⟩
    show (0 : ℝ) < multiVisitHazard 0 0
    norm_num [multiVisitHazard, multiVisitOwner, multiVisitRate]
  · intro who
    fin_cases who <;>
      simp [multiVisitReward_singleton_zero, multiVisitReward_singleton_one,
        multiVisitReward_singleton_two]

/-! ## The payoff -/

/-- **The multi-visit schedule delivers the payoff `(1, 0, 0)`.**  Player `0`
is scheduled at two of the three phases with different probabilities, player
`1` at one, and player `2` at none. -/
theorem multiVisit_isUniformEquilibriumPayoff :
    (quittingGame multiVisitReward).IsUniformEquilibriumPayoff none
      (multiVisitValue 0) :=
  isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
    multiVisit_isQuittingBlockCertificate

/-- The table carries no counterexample regime. -/
theorem multiVisit_isEmpty_counterexampleRegime :
    IsEmpty (QuittingCounterexampleRegime multiVisitReward) :=
  isEmpty_counterexampleRegime_of_isQuittingBlockCertificate
    multiVisit_isQuittingBlockCertificate

end BlockPeriodicMultiVisit
end GameTheory
