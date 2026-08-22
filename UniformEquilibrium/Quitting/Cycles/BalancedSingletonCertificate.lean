/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.SingletonArcCycle

/-!
# Balanced cyclic singleton certificates

This module gives a named certificate interface for the one-owner-at-a-time
cyclic compiler.  The `arc` equation is the balanced Bellman equation: the
coarse value at a phase is the singleton endpoint/interpolation between its
owner's solo payoff and the next phase's value.  `active` and `soloFloor` are
the exact owner and passive-player inequalities needed by that equation.

The bounded interface exposes the collision cap explicitly.  The
reader-facing interface derives it from the finite reward table, so no reward
for a nonsingleton coalition is discarded or identified with a singleton
reward.

The `opponentDivergence` field records the terminal semantic seam which cannot
be inferred from a cyclic Bellman equation.  Every player must face a
strictly positive hazard from a different owner at some phase.  It implies the
strict deleted-opponent product required by the terminal compiler.  In
particular, a one-phase cycle with one owner is rejected for the owner unless
an additional opponent hazard is supplied.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {L : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A balanced cyclic singleton certificate for a quitting game.

The certificate contains all data needed by the mesh compiler.  The phase
hazard is a probability, so `hazard_nonneg` and `hazard_lt_one` are explicit.
The `opponentDivergence` clause is the exact sufficient condition for every
deviating player's deleted-opponent survival product to be below one.
-/
structure BalancedSingletonCycleCertificateWithBounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  owner : Fin L → ι
  hazard : Fin L → ℝ
  coarse : Fin L → Payoff ι
  initial : Fin L
  aStar : ℝ
  collisionBound : ℝ
  hazard_nonneg : ∀ phase, 0 ≤ hazard phase
  hazard_lt_one : ∀ phase, hazard phase < 1
  intensity_bound : ∀ phase, quittingMeshIntensity (hazard phase) ≤ aStar
  collision_bound : 0 ≤ collisionBound
  arc : ∀ phase, coarse phase = quittingSingletonArcPayoff (hazard phase)
    (quittingSoloReward reward (owner phase))
    (coarse (finRotate L phase))
  active : ∀ phase,
    coarse phase (owner phase) = quittingSoloReward reward (owner phase) (owner phase)
  soloFloor : ∀ phase who,
    quittingSoloReward reward who who ≤ coarse phase who
  collision : ∀ phase other, other ≠ owner phase →
    max (quittingSingletonCollisionReward reward (owner phase) other -
      quittingSoloReward reward other other) 0 ≤ collisionBound
  opponentDivergence : ∀ who, ∃ phase, who ≠ owner phase ∧ 0 < hazard phase

/-! The reader-facing certificate omits all auxiliary caps. -/

/-- A balanced cyclic singleton certificate whose finite caps are inferred. -/
structure BalancedSingletonCycleCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  owner : Fin L → ι
  hazard : Fin L → ℝ
  coarse : Fin L → Payoff ι
  initial : Fin L
  hazard_nonneg : ∀ phase, 0 ≤ hazard phase
  hazard_lt_one : ∀ phase, hazard phase < 1
  arc : ∀ phase, coarse phase = quittingSingletonArcPayoff (hazard phase)
    (quittingSoloReward reward (owner phase))
    (coarse (finRotate L phase))
  active : ∀ phase,
    coarse phase (owner phase) = quittingSoloReward reward (owner phase) (owner phase)
  soloFloor : ∀ phase who,
    quittingSoloReward reward who who ≤ coarse phase who
  opponentDivergence : ∀ who, ∃ phase, who ≠ owner phase ∧ 0 < hazard phase

def balancedSingletonCycleIntensityCap
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) : ℝ :=
  ∑ phase, quittingMeshIntensity (certificate.hazard phase)

def balancedSingletonCycleCollisionCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  2 * quittingRewardBound reward

omit [Fintype ι] [DecidableEq ι] in
theorem balancedSingletonCycleIntensityCap_nonneg
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) :
    0 ≤ balancedSingletonCycleIntensityCap certificate := by
  unfold balancedSingletonCycleIntensityCap
  exact Finset.sum_nonneg fun phase _ => quittingMeshIntensity_nonneg
    (certificate.hazard_nonneg phase) (certificate.hazard_lt_one phase).le

omit [Fintype ι] [DecidableEq ι] in
theorem balancedSingletonCycleIntensityCap_bound
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) (phase : Fin L) :
    quittingMeshIntensity (certificate.hazard phase) ≤
      balancedSingletonCycleIntensityCap certificate := by
  unfold balancedSingletonCycleIntensityCap
  exact Finset.single_le_sum
    (fun other _ => quittingMeshIntensity_nonneg
      (certificate.hazard_nonneg other) (certificate.hazard_lt_one other).le)
    (Finset.mem_univ phase)

omit [DecidableEq ι] in
theorem balancedSingletonCycleCollisionCap_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ balancedSingletonCycleCollisionCap reward := by
  unfold balancedSingletonCycleCollisionCap
  exact mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)

theorem balancedSingletonCycle_collision_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner other : ι) (_hne : other ≠ owner) :
    max (quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other) 0 ≤
      balancedSingletonCycleCollisionCap reward := by
  have hcollision := abs_reward_le_quittingRewardBound reward
    ⟨{owner, other}, by simp⟩ other
  have hsolo := abs_reward_le_quittingRewardBound reward
    ⟨{other}, by simp⟩ other
  have hdiff : quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other ≤
      2 * quittingRewardBound reward := by
    unfold quittingSingletonCollisionReward quittingSoloReward at *
    rw [abs_le] at hcollision hsolo
    linarith
  exact max_le hdiff (balancedSingletonCycleCollisionCap_nonneg reward)

def BalancedSingletonCycleCertificate.toWithBounds
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) :
    BalancedSingletonCycleCertificateWithBounds (L := L) reward :=
  { owner := certificate.owner
    hazard := certificate.hazard
    coarse := certificate.coarse
    initial := certificate.initial
    aStar := balancedSingletonCycleIntensityCap certificate
    collisionBound := balancedSingletonCycleCollisionCap reward
    hazard_nonneg := certificate.hazard_nonneg
    hazard_lt_one := certificate.hazard_lt_one
    intensity_bound := balancedSingletonCycleIntensityCap_bound certificate
    collision_bound := balancedSingletonCycleCollisionCap_nonneg reward
    arc := certificate.arc
    active := certificate.active
    soloFloor := certificate.soloFloor
    collision := fun phase other hne =>
      balancedSingletonCycle_collision_bound reward
        (certificate.owner phase) other hne
    opponentDivergence := certificate.opponentDivergence }

omit [Fintype ι] in
private theorem prod_if_owner_one_sub_hazard_lt_one
    (owner : Fin L → ι) (hazard : Fin L → ℝ)
    (hazard_nonneg : ∀ phase, 0 ≤ hazard phase)
    (hazard_lt_one : ∀ phase, hazard phase < 1)
    (who : ι) (hdivergence : ∃ phase, who ≠ owner phase ∧ 0 < hazard phase) :
    (∏ phase : Fin L,
      if who = owner phase then 1 else 1 - hazard phase) < 1 := by
  obtain ⟨phase, hne, hpositive⟩ := hdivergence
  have hfactor_nonneg : ∀ phase,
      0 ≤ (if who = owner phase then 1 else 1 - hazard phase) := by
    intro phase
    by_cases howner : who = owner phase
    · simp [howner]
    · simp only [howner, ↓reduceIte]
      linarith [hazard_lt_one phase]
  have hfactor_le : ∀ phase,
      (if who = owner phase then 1 else 1 - hazard phase) ≤ 1 := by
    intro phase
    by_cases howner : who = owner phase
    · simp [howner]
    · simp only [howner, ↓reduceIte]
      linarith [hazard_nonneg phase]
  have hfactor_lt :
      (if who = owner phase then 1 else 1 - hazard phase) < 1 := by
    simp only [hne, ↓reduceIte]
    linarith
  have hsplit := Finset.mul_prod_erase Finset.univ
    (fun phase : Fin L => if who = owner phase then 1 else 1 - hazard phase)
    (Finset.mem_univ phase)
  have herase :
      (∏ other ∈ Finset.univ.erase phase,
        if who = owner other then 1 else 1 - hazard other) ≤ 1 :=
    Finset.prod_le_one
      (fun other _ => hfactor_nonneg other)
      (fun other _ => hfactor_le other)
  calc
    (∏ phase : Fin L,
        if who = owner phase then 1 else 1 - hazard phase) =
        (if who = owner phase then 1 else 1 - hazard phase) *
          ∏ other ∈ Finset.univ.erase phase,
            if who = owner other then 1 else 1 - hazard other := hsplit.symm
    _ ≤ (if who = owner phase then 1 else 1 - hazard phase) * 1 :=
      mul_le_mul_of_nonneg_left herase (hfactor_nonneg phase)
    _ = (if who = owner phase then 1 else 1 - hazard phase) := mul_one _
    _ < 1 := hfactor_lt

omit [Fintype ι] in
private theorem BalancedSingletonCycleCertificateWithBounds.opponent_contracts
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (certificate : BalancedSingletonCycleCertificateWithBounds (L := L) reward)
    (who : ι) :
    (∏ phase : Fin L,
      if who = certificate.owner phase then 1 else
        1 - certificate.hazard phase) < 1 := by
  have hprod := prod_if_owner_one_sub_hazard_lt_one
    certificate.owner certificate.hazard certificate.hazard_nonneg
    certificate.hazard_lt_one who (certificate.opponentDivergence who)
  exact hprod

omit [Fintype ι] in
/-- The exact deleted-opponent product supplied by a balanced certificate. -/
theorem BalancedSingletonCycleCertificateWithBounds.opponent_product_lt_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (certificate : BalancedSingletonCycleCertificateWithBounds (L := L) reward)
    (who : ι) :
    (∏ phase : Fin L,
      if who = certificate.owner phase then 1 else
        1 - certificate.hazard phase) < 1 :=
  certificate.opponent_contracts who

/-- A balanced cyclic singleton certificate yields a uniform-equilibrium
payoff at its selected initial phase.

All terminal rewards, including arbitrary nonsingleton coalition rewards, are
handled by the explicit `collision_bound` and `collision` fields.  The only
semantic terminality premise is `opponentDivergence`, used to obtain strict
deleted-opponent contraction for every player.
-/
theorem BalancedSingletonCycleCertificateWithBounds.isUniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (certificate : BalancedSingletonCycleCertificateWithBounds (L := L) reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (certificate.coarse certificate.initial) := by
  apply singletonArcCycle_isUniformEquilibriumPayoff
    reward certificate.owner certificate.hazard certificate.coarse
    certificate.initial certificate.hazard_nonneg certificate.hazard_lt_one
    certificate.intensity_bound certificate.collision_bound certificate.arc
    certificate.active certificate.soloFloor certificate.collision
  intro who
  exact certificate.opponent_product_lt_one who

/-- The lean certificate also exposes the exact deleted-opponent product. -/
theorem BalancedSingletonCycleCertificate.opponent_product_lt_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) (who : ι) :
    (∏ phase : Fin L,
      if who = certificate.owner phase then 1 else
        1 - certificate.hazard phase) < 1 :=
  certificate.toWithBounds.opponent_product_lt_one who

/-- The reader-facing balanced singleton compiler.  All finite mesh and
collision caps are derived internally from the supplied finite data and
`quittingRewardBound`; arbitrary nonsingleton rewards remain covered by the
derived collision estimate. -/
theorem BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (certificate : BalancedSingletonCycleCertificate (L := L) reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (certificate.coarse certificate.initial) :=
  certificate.toWithBounds.isUniformEquilibriumPayoff

end GameTheory
