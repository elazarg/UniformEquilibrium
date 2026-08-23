/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate

/-!
# A cyclic tail producer for balanced singleton certificates

This module isolates the finite algebra needed to produce a balanced
one-owner-per-phase singleton cycle.  A nonnegative cyclic tail solving the
normalized singleton recurrence is compiled into the semantic certificate;
the existing balanced-cycle compiler then handles arbitrary nonsingleton
rewards and unrestricted behavioral deviations.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {n : ℕ} [NeZero n]
variable {reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n)}

/-- Finite cyclic algebra sufficient for an equal-hazard balanced singleton
cycle.  `tail (phase - who)` is the normalized continuation surplus of player
`who` at `phase`. -/
structure CyclicSingletonTailData
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n)) where
  survival : ℝ
  tail : Fin n → ℝ
  survival_pos : 0 < survival
  survival_lt_one : survival < 1
  tail_zero : tail 0 = 0
  tail_nonneg : ∀ offset, 0 ≤ tail offset
  recurrence : ∀ phase who,
    tail (phase - who) = quittingSingletonMatrix reward who phase +
      survival * tail (finRotate n phase - who)

namespace CyclicSingletonTailData

/-- Continuation values induced by cyclic tail data. -/
def coarse (data : CyclicSingletonTailData reward) (phase : Fin n) : Payoff (Fin n) :=
  fun who => quittingSoloReward reward who who +
    (1 - data.survival) * data.tail (phase - who)

/-- A cyclic tail phase gives a player exactly their solo level precisely when
the corresponding normalized tail vanishes. -/
theorem coarse_eq_solo_iff_tail_eq_zero
    (data : CyclicSingletonTailData reward) (phase who : Fin n) :
    data.coarse phase who = quittingSoloReward reward who who ↔
      data.tail (phase - who) = 0 := by
  unfold coarse
  constructor
  · intro heq
    have hmul : (1 - data.survival) * data.tail (phase - who) = 0 := by
      linarith
    exact (mul_eq_zero.mp hmul).resolve_left (by
      linarith [data.survival_lt_one])
  · intro hzero
    rw [hzero, mul_zero, add_zero]

/-- Cyclic tail data produce a balanced singleton-cycle certificate. -/
def certificate (data : CyclicSingletonTailData reward) (hn : 2 ≤ n) :
    BalancedSingletonCycleCertificate (L := n) reward where
  owner := id
  hazard := fun _ => 1 - data.survival
  coarse := data.coarse
  initial := 0
  hazard_nonneg := by
    intro phase
    linarith [data.survival_lt_one]
  hazard_lt_one := by
    intro phase
    linarith [data.survival_pos]
  arc := by
    intro phase
    funext who
    simp only [coarse, id_eq, quittingSingletonArcPayoff]
    rw [data.recurrence phase who]
    unfold quittingSingletonMatrix
    simp only [quittingSoloReward]
    ring
  active := by
    intro phase
    simp [coarse, data.tail_zero]
  soloFloor := by
    intro phase who
    simp only [coarse]
    exact le_add_of_nonneg_right <| mul_nonneg
      (by linarith [data.survival_lt_one]) (data.tail_nonneg (phase - who))
  opponentDivergence := by
    intro who
    refine ⟨finRotate n who, ?_, by linarith [data.survival_lt_one]⟩
    simp only [id_eq]
    intro heq
    have hval := congrArg Fin.val heq
    rw [Math.val_finRotate] at hval
    have hwho : who.val + 1 < n := by
      by_contra hnot
      have heqLast : who.val + 1 = n := by omega
      simp [heqLast] at hval
      have hwhoZero : who.val = 0 := by
        simpa using congrArg Fin.val hval
      omega
    rw [Nat.mod_eq_of_lt hwho] at hval
    have := who.isLt
    omega

@[simp] theorem certificate_coarse (data : CyclicSingletonTailData reward) (hn : 2 ≤ n) :
    (data.certificate hn).coarse = data.coarse := rfl

/-- Direct game-semantic consumer for cyclic tail data. -/
theorem isUniformEquilibriumPayoff
    (data : CyclicSingletonTailData reward) (hn : 2 ≤ n) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (data.coarse 0) := by
  change (quittingGame reward).IsUniformEquilibriumPayoff none
    (data.coarse (data.certificate hn).initial)
  exact (data.certificate hn).isUniformEquilibriumPayoff

end CyclicSingletonTailData
end GameTheory
