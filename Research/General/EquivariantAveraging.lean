/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Finite-group Reynolds averaging

This file proves two representation-theoretic building blocks:

* averaging an orbit over a finite group produces an invariant vector;
* an equivariant rational-linear map commutes with that average.

It does not assert that averaging equilibrium strategies preserves Nash
equilibrium; the theorem applies to linear state, payoff, occupation, and dual
certificate spaces.
-/

namespace Math
namespace EquivariantAveraging

open scoped BigOperators

section Reynolds

variable (G V : Type*)
variable [Fintype G]
variable [AddCommMonoid V] [Module ℚ V] [SMul G V]

noncomputable def reynolds (v : V) : V :=
  ((Fintype.card G : ℚ)⁻¹) • ∑ g : G, g • v

end Reynolds

section Invariant

variable (G V : Type*)
variable [Fintype G]
variable [AddCommMonoid V] [Module ℚ V]
variable [Group G] [DistribMulAction G V] [SMulCommClass G ℚ V]

theorem reynolds_invariant (h : G) (v : V) :
    h • reynolds G V v = reynolds G V v := by
  unfold reynolds
  rw [smul_comm h ((Fintype.card G : ℚ)⁻¹)]
  congr 1
  rw [Finset.smul_sum]
  simpa only [Equiv.coe_mulLeft, smul_smul] using
    (Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => g • v))

end Invariant

section EquivariantMap

variable {G V W : Type*}
variable [Fintype G]
variable [AddCommMonoid V] [Module ℚ V] [SMul G V]
variable [AddCommMonoid W] [Module ℚ W] [SMul G W]

theorem equivariant_map_reynolds
    (L : V →ₗ[ℚ] W)
    (equivariant : ∀ g : G, ∀ v : V, L (g • v) = g • L v)
    (v : V) :
    L (reynolds G V v) = reynolds G W (L v) := by
  unfold reynolds
  rw [LinearMap.map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact equivariant g v

end EquivariantMap

end EquivariantAveraging
end Math
