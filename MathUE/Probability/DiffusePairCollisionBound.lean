/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.DiscreteHazardStopping

/-!
# Uniform collision bounds for discrete hazards

Two independent public-time hazards `p` and `q` stop simultaneously at date
`t` with live probability

```text
jointSurvival(t) * p(t) * q(t).
```

If the first hazard has mesh at most `m`, the total simultaneous-stop mass up
to *any* cutoff is at most

```text
m * (1 - jointSurvival(cutoff)) <= m.
```

The estimate is uniform over the second hazard.  Thus no behavioral stopping
law can extract a macroscopic simultaneous-quitting interaction from a clock
whose maximal one-date hazard tends to zero.

This is probability geometry only.  A quitting-game deletion theorem must
still show that every payoff channel involving the prospective deleted player
reduces to such a collision term, while its solo channel is tight or otherwise
priced.
-/

noncomputable section

namespace Math
namespace Probability
namespace DiffusePairCollision

open DiscreteHazard

/-- The union hazard of two independent stop decisions. -/
def pairHazard (first second : ScalarHazard) : ScalarHazard where
  stop time := first.stop time + second.stop time -
    first.stop time * second.stop time
  stop_nonneg time := by
    have hp0 := first.stop_nonneg time
    have hp1 := first.stop_le_one time
    have hq0 := second.stop_nonneg time
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hq0]
  stop_le_one time := by
    have hp0 := first.stop_nonneg time
    have hp1 := first.stop_le_one time
    have hq0 := second.stop_nonneg time
    have hq1 := second.stop_le_one time
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1)
      (sub_nonneg.mpr hq1)]

/-- Probability that both hazards first stop simultaneously at one displayed
date, with joint survival before that date. -/
def collisionMassAt
    (first second : ScalarHazard) (time : ℕ) : ℝ :=
  (pairHazard first second).survival 0 time *
    first.stop time * second.stop time

/-- Total simultaneous-stop mass before a finite cutoff. -/
def collisionMass
    (first second : ScalarHazard) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff, collisionMassAt first second time

theorem pairHazard_stop_eq_one_sub_continueProduct
    (first second : ScalarHazard) (time : ℕ) :
    (pairHazard first second).stop time =
      1 - (1 - first.stop time) * (1 - second.stop time) := by
  simp only [pairHazard]
  ring

theorem collisionMassAt_nonneg
    (first second : ScalarHazard) (time : ℕ) :
    0 ≤ collisionMassAt first second time := by
  exact mul_nonneg
    (mul_nonneg ((pairHazard first second).survival_nonneg 0 time)
      (first.stop_nonneg time))
    (second.stop_nonneg time)

theorem collisionMass_nonneg
    (first second : ScalarHazard) (cutoff : ℕ) :
    0 ≤ collisionMass first second cutoff :=
  Finset.sum_nonneg fun time _ => collisionMassAt_nonneg first second time

/-- One-date collision is bounded by mesh times one-date union stopping. -/
theorem stop_mul_stop_le_mesh_mul_pairStop
    (first second : ScalarHazard) (mesh : ℝ) (time : ℕ)
    (hmesh : first.stop time ≤ mesh) :
    first.stop time * second.stop time ≤
      mesh * (pairHazard first second).stop time := by
  have hp0 := first.stop_nonneg time
  have hq0 := second.stop_nonneg time
  have hq1 := second.stop_le_one time
  have hmesh0 : 0 ≤ mesh := hp0.trans hmesh
  have hpq : first.stop time * second.stop time ≤
      mesh * second.stop time :=
    mul_le_mul_of_nonneg_right hmesh hq0
  have hqle : second.stop time ≤ (pairHazard first second).stop time := by
    dsimp only [pairHazard]
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hq1)]
  exact hpq.trans (mul_le_mul_of_nonneg_left hqle hmesh0)

/-- **Uniform finite collision bound.**  The bound is independent of the
second hazard and loses only the probability that the pair has stopped by the
cutoff. -/
theorem collisionMass_le_mesh_mul_one_sub_survival
    (first second : ScalarHazard) (mesh : ℝ) (cutoff : ℕ)
    (hmesh : ∀ time < cutoff, first.stop time ≤ mesh) :
    collisionMass first second cutoff ≤
      mesh * (1 - (pairHazard first second).survival 0 cutoff) := by
  calc
    collisionMass first second cutoff =
        ∑ time ∈ Finset.range cutoff,
          (pairHazard first second).survival 0 time *
            (first.stop time * second.stop time) := by
      simp only [collisionMass, collisionMassAt]
      apply Finset.sum_congr rfl
      intro time _
      ring
    _ ≤ ∑ time ∈ Finset.range cutoff,
        (pairHazard first second).survival 0 time *
          (mesh * (pairHazard first second).stop time) := by
      apply Finset.sum_le_sum
      intro time htime
      exact mul_le_mul_of_nonneg_left
        (stop_mul_stop_le_mesh_mul_pairStop first second mesh time
          (hmesh time (Finset.mem_range.mp htime)))
        ((pairHazard first second).survival_nonneg 0 time)
    _ = mesh * ∑ time ∈ Finset.range cutoff,
        (pairHazard first second).stopMass time := by
      simp only [ScalarHazard.stopMass]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro time _
      ring
    _ = mesh * (1 -
        (pairHazard first second).survival 0 cutoff) := by
      rw [(pairHazard first second).sum_stopMass]

/-- The simpler mesh bound. -/
theorem collisionMass_le_mesh
    (first second : ScalarHazard) (mesh : ℝ) (cutoff : ℕ)
    (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ time < cutoff, first.stop time ≤ mesh) :
    collisionMass first second cutoff ≤ mesh := by
  have hbound := collisionMass_le_mesh_mul_one_sub_survival
    first second mesh cutoff hmesh
  have hsurvival0 : 0 ≤ (pairHazard first second).survival 0 cutoff :=
    (pairHazard first second).survival_nonneg 0 cutoff
  nlinarith

/-- The full infinite-horizon collision law is summable under a global mesh
bound.  No completeness assumption is imposed on either stopping law. -/
theorem summable_collisionMassAt_of_mesh
    (first second : ScalarHazard) (mesh : ℝ)
    (hmesh : ∀ time, first.stop time ≤ mesh) :
    Summable (collisionMassAt first second) := by
  have hmesh0 : 0 ≤ mesh :=
    (first.stop_nonneg 0).trans (hmesh 0)
  apply summable_of_sum_range_le
  · exact collisionMassAt_nonneg first second
  · intro cutoff
    exact collisionMass_le_mesh first second mesh cutoff hmesh0
      (fun time _ => hmesh time)

/-- **Uniform infinite collision bound.**  Even over the complete horizon,
an arbitrary second behavioral stopping law has simultaneous-stop mass at
most the first clock's mesh. -/
theorem tsum_collisionMassAt_le_mesh
    (first second : ScalarHazard) (mesh : ℝ)
    (hmesh : ∀ time, first.stop time ≤ mesh) :
    (∑' time, collisionMassAt first second time) ≤ mesh := by
  apply Real.tsum_le_of_sum_range_le
  · exact collisionMassAt_nonneg first second
  · intro cutoff
    have hmesh0 : 0 ≤ mesh :=
      (first.stop_nonneg 0).trans (hmesh 0)
    exact collisionMass_le_mesh first second mesh cutoff hmesh0
      (fun time _ => hmesh time)

/-- Boolean-behavior adapter for the finite uniform collision bound. -/
theorem boolean_collisionMass_le_mesh
    (first second : BooleanHazard) (mesh : ℝ) (cutoff : ℕ)
    (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ time < cutoff, stopProbability first time ≤ mesh) :
    collisionMass first.toScalar second.toScalar cutoff ≤ mesh :=
  collisionMass_le_mesh first.toScalar second.toScalar mesh cutoff hmesh0 hmesh

/-- Boolean-behavior adapter for the complete-horizon bound. -/
theorem boolean_tsum_collisionMassAt_le_mesh
    (first second : BooleanHazard) (mesh : ℝ)
    (hmesh : ∀ time, stopProbability first time ≤ mesh) :
    (∑' time, collisionMassAt first.toScalar second.toScalar time) ≤ mesh :=
  tsum_collisionMassAt_le_mesh first.toScalar second.toScalar mesh hmesh

/-- Weighted payoff form: a uniformly bounded collision payoff is at most
`bound * mesh` in absolute expected contribution. -/
theorem abs_collisionPayoff_le_bound_mul_mesh
    (first second : ScalarHazard) (mesh bound payoff : ℝ) (cutoff : ℕ)
    (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ time < cutoff, first.stop time ≤ mesh)
    (hpayoff : |payoff| ≤ bound) :
    |collisionMass first second cutoff * payoff| ≤ bound * mesh := by
  rw [abs_mul]
  have hcollision0 := collisionMass_nonneg first second cutoff
  have hbound0 : 0 ≤ bound := (abs_nonneg payoff).trans hpayoff
  rw [abs_of_nonneg hcollision0]
  calc
    collisionMass first second cutoff * |payoff| ≤
        collisionMass first second cutoff * bound :=
      mul_le_mul_of_nonneg_left hpayoff hcollision0
    _ ≤ mesh * bound :=
      mul_le_mul_of_nonneg_right
        (collisionMass_le_mesh first second mesh cutoff hmesh0 hmesh) hbound0
    _ = bound * mesh := by ring

end DiffusePairCollision
end Probability
end Math
