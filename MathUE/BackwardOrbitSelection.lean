/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Backward orbits through a finite absorbing range

A self-map whose image lies in a finite set admits a periodic backward orbit:
a sequence in which every term is the image of its successor.  A forward
orbit must revisit a value, and reading the revealed cycle backwards,
repeated, is such a sequence.

This is the combinatorial substitute for a fixed-point theorem in
discretized backward-induction constructions: a backward orbit of the
one-step selection map is exactly an infinite self-consistent plan.  The
sibling `Math.finitePivotOrbit` alternative concerns forward orbits on a
finite label type; here the ambient type may be infinite, and only the
image is finite.
-/

namespace Math

/-- **Periodic backward orbit extraction.**  A self-map whose image lies in a
finite set admits a periodic sequence in which every term is the image of its
successor. -/
theorem exists_periodic_backward_orbit {β : Type*} (f : β → β) (start : β)
    {range : Set β} (hfinite : range.Finite) (hmem : ∀ b, f b ∈ range) :
    ∃ (period : ℕ) (chain : ℕ → β), 0 < period ∧
      (∀ n, chain (n + period) = chain n) ∧
      ∀ n, chain n = f (chain (n + 1)) := by
  classical
  have hsucc : ∀ j, f^[j + 1] start = f (f^[j] start) := fun j =>
    Function.iterate_succ_apply' f j start
  have hmapsTo : Set.MapsTo (fun j => f^[j] start) Set.univ
      (insert start range) := by
    intro j _
    cases j with
    | zero => exact Set.mem_insert start range
    | succ j =>
        show f^[j + 1] start ∈ insert start range
        rw [hsucc j]
        exact Set.mem_insert_of_mem start (hmem (f^[j] start))
  obtain ⟨x, -, y, -, hxy, heq⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmapsTo
      (hfinite.insert start)
  have hpair : ∃ low high : ℕ, low < high ∧ f^[low] start = f^[high] start := by
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact ⟨x, y, hlt, heq⟩
    · exact ⟨y, x, hlt, heq.symm⟩
  obtain ⟨low, high, hlt, hcycle⟩ := hpair
  set period := high - low with hperiod
  have hperiod1 : 1 ≤ period := by omega
  let chain : ℕ → β := fun n =>
    f^[low + (period - 1) - n % period] start
  refine ⟨period, chain, hperiod1, ?_, fun n => ?_⟩
  · intro n
    simp [chain]
  show f^[low + (period - 1) - n % period] start =
    f (f^[low + (period - 1) - (n + 1) % period] start)
  rw [← hsucc (low + (period - 1) - (n + 1) % period)]
  have hppos : 0 < period := hperiod1
  obtain ⟨residue, hresidue⟩ : ∃ residue, n % period = residue :=
    ⟨n % period, rfl⟩
  have hresidueLt : residue < period := hresidue ▸ Nat.mod_lt n hppos
  rw [hresidue]
  by_cases hlast : residue = period - 1
  · have hnext : (n + 1) % period = 0 := by
      rcases Nat.lt_or_ge 1 period with hbig | hsmall
      · rw [Nat.add_mod, hresidue, hlast, Nat.mod_eq_of_lt hbig,
          show period - 1 + 1 = period from by omega, Nat.mod_self]
      · have hone : period = 1 := by omega
        rw [hone, Nat.mod_one]
    rw [hnext, hlast]
    have hindexLeft : low + (period - 1) - (period - 1) = low := by omega
    have hindexRight : low + (period - 1) - 0 + 1 = high := by omega
    rw [hindexLeft, hindexRight]
    exact hcycle
  · have hstep : residue + 1 < period := by omega
    have hbig : 1 < period := by omega
    have hnext : (n + 1) % period = residue + 1 := by
      rw [Nat.add_mod, hresidue, Nat.mod_eq_of_lt hbig,
        Nat.mod_eq_of_lt hstep]
    rw [hnext]
    have hindex : low + (period - 1) - (residue + 1) + 1 =
        low + (period - 1) - residue := by omega
    rw [hindex]

/-- **Backward orbit extraction.**  A self-map whose image lies in a finite
set admits a sequence in which every term is the image of its successor. -/
theorem exists_backward_orbit {β : Type*} (f : β → β) (start : β)
    {range : Set β} (hfinite : range.Finite) (hmem : ∀ b, f b ∈ range) :
    ∃ chain : ℕ → β, ∀ n, chain n = f (chain (n + 1)) := by
  obtain ⟨_period, chain, _hperiod, _hperiodic, hchain⟩ :=
    exists_periodic_backward_orbit f start hfinite hmem
  exact ⟨chain, hchain⟩

end Math
