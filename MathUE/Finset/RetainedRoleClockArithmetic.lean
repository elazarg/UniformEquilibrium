/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.GroupAction.CyclicKofNArithmetic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Arithmetic of retained-role clocks

An `m`-edge chain names its `m+1` vertices and one additional incidence
label, hence at most `m+2` roles. This module counts finite clocks of such
packets independently of any game semantics.

Uniform player load gives `N*r ≤ (m+2)*L`. If every packet is saturated,
the usual balanced-incidence equation also yields the reduced-denominator
law `N / gcd(m+2,N) ∣ L`.
-/

namespace Math

namespace RetainedRoleClockArithmetic

open CyclicKofNArithmetic
open scoped BigOperators

noncomputable section

variable {Player Phase : Type*} [DecidableEq Player]

/-- The roles named by an `m`-edge chain: its `m+1` vertices and one
additional incidence label. -/
def resetChainRoleSupport (edges : ℕ)
    (vertex : Fin (edges + 1) → Player) (incidenceLabel : Player) : Finset Player :=
  insert incidenceLabel (Finset.univ.image vertex)

/-- An `m`-edge chain plus one incidence label names at most `m+2` roles. -/
theorem resetChainRoleSupport_card_le (edges : ℕ)
    (vertex : Fin (edges + 1) → Player) (incidenceLabel : Player) :
    (resetChainRoleSupport edges vertex incidenceLabel).card ≤ edges + 2 := by
  have himage : (Finset.univ.image vertex).card ≤ edges + 1 := by
    calc
      (Finset.univ.image vertex).card ≤
          (Finset.univ : Finset (Fin (edges + 1))).card := Finset.card_image_le
      _ = edges + 1 := by simp
  calc
    (resetChainRoleSupport edges vertex incidenceLabel).card ≤
        (Finset.univ.image vertex).card + 1 :=
      Finset.card_insert_le incidenceLabel (Finset.univ.image vertex)
    _ ≤ (edges + 1) + 1 := Nat.add_le_add_right himage 1
    _ = edges + 2 := by simp [Nat.add_assoc]

/-- A finite clock of local retained-role packets. -/
def retainedRoleClock (edges : ℕ)
    (vertex : Phase → Fin (edges + 1) → Player)
    (incidenceLabel : Phase → Player) : Phase → Finset Player :=
  fun phase => resetChainRoleSupport edges (vertex phase) (incidenceLabel phase)

/-- Every packet in the clock has at most `m+2` roles. -/
theorem retainedRoleClock_phaseLoad_le
    (edges : ℕ) (vertex : Phase → Fin (edges + 1) → Player)
    (incidenceLabel : Phase → Player) (phase : Phase) :
    phaseLoad (retainedRoleClock edges vertex incidenceLabel) phase ≤ edges + 2 := by
  exact resetChainRoleSupport_card_le edges (vertex phase) (incidenceLabel phase)

variable [Fintype Player] [Fintype Phase]

/-- Uniform player load and the local `m+2` role cap imply
`N*r ≤ (m+2)*L`. -/
theorem population_mul_playerLoad_le_roleCap_mul_clockCard
    (edges : ℕ) (vertex : Phase → Fin (edges + 1) → Player)
    (incidenceLabel : Phase → Player) (r : ℕ)
    (hload : ∀ player,
      playerLoad (retainedRoleClock edges vertex incidenceLabel) player = r) :
    Fintype.card Player * r ≤ (edges + 2) * Fintype.card Phase := by
  let roles := retainedRoleClock edges vertex incidenceLabel
  calc
    Fintype.card Player * r = ∑ _player : Player, r := by simp
    _ = ∑ player, playerLoad roles player := by
      apply Finset.sum_congr rfl
      intro player _
      exact (hload player).symm
    _ = ∑ phase, phaseLoad roles phase :=
      (sum_phaseLoad_eq_sum_playerLoad roles).symm
    _ ≤ ∑ _phase : Phase, (edges + 2) := by
      refine Finset.sum_le_sum (s := Finset.univ) ?_
      intro phase _
      exact retainedRoleClock_phaseLoad_le edges vertex incidenceLabel phase
    _ = (edges + 2) * Fintype.card Phase := by simp [mul_comm]

omit [Fintype Player] in
/-- Saturated retained-role clocks are balanced `(m+2)/N` schedules. -/
theorem retainedRoleClock_isBalanced_of_saturated
    (edges : ℕ) (vertex : Phase → Fin (edges + 1) → Player)
    (incidenceLabel : Phase → Player) (r : ℕ)
    (hsaturated : ∀ phase,
      (retainedRoleClock edges vertex incidenceLabel phase).card = edges + 2)
    (hload : ∀ player,
      playerLoad (retainedRoleClock edges vertex incidenceLabel) player = r) :
    IsBalanced (retainedRoleClock edges vertex incidenceLabel) (edges + 2) r := by
  exact ⟨hsaturated, hload⟩

/-- A saturated balanced clock of `m`-edge packets has phase count divisible
by the reduced denominator of `(m+2)/N`. -/
theorem reducedPopulation_dvd_retainedRoleClockCard
    (edges : ℕ) (vertex : Phase → Fin (edges + 1) → Player)
    (incidenceLabel : Phase → Player) (r : ℕ)
    (hPlayer : 0 < Fintype.card Player)
    (hsaturated : ∀ phase,
      (retainedRoleClock edges vertex incidenceLabel phase).card = edges + 2)
    (hload : ∀ player,
      playerLoad (retainedRoleClock edges vertex incidenceLabel) player = r) :
    Fintype.card Player / (edges + 2).gcd (Fintype.card Player) ∣
      Fintype.card Phase := by
  exact (retainedRoleClock_isBalanced_of_saturated
    edges vertex incidenceLabel r hsaturated hload).reducedPopulation_dvd_card hPlayer

/-- In the coprime case a nonempty retained-role clock needs at least one
full population cycle. -/
theorem population_le_retainedRoleClockCard_of_coprime
    (edges : ℕ) (vertex : Phase → Fin (edges + 1) → Player)
    (incidenceLabel : Phase → Player) (r : ℕ)
    (hPhase : 0 < Fintype.card Phase)
    (hcoprime : Nat.Coprime (edges + 2) (Fintype.card Player))
    (hsaturated : ∀ phase,
      (retainedRoleClock edges vertex incidenceLabel phase).card = edges + 2)
    (hload : ∀ player,
      playerLoad (retainedRoleClock edges vertex incidenceLabel) player = r) :
    Fintype.card Player ≤ Fintype.card Phase := by
  exact IsBalanced.population_le_card_phase_of_coprime hPhase hcoprime
    (retainedRoleClock_isBalanced_of_saturated
      edges vertex incidenceLabel r hsaturated hload)

end

end RetainedRoleClockArithmetic

end Math
