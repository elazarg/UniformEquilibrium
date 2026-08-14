import Mathlib

/-!
# E21: finite-group Reynolds averaging

This standalone file proves two representation-theoretic building blocks:

* averaging an orbit over a finite group produces an invariant vector;
* an equivariant rational-linear map commutes with that average.

It does not assert that averaging equilibrium strategies preserves Nash
equilibrium; the theorem applies to linear state, payoff, occupation, and dual
certificate spaces.
-/

namespace Experiments.EquivariantAveraging

open scoped BigOperators

variable (G V : Type*)
variable [Fintype G] [Group G]
variable [AddCommGroup V] [Module ℚ V]
variable [DistribMulAction G V] [SMulCommClass G ℚ V]

noncomputable def reynolds (v : V) : V :=
  ((Fintype.card G : ℚ)⁻¹) • ∑ g : G, g • v

theorem reynolds_invariant (h : G) (v : V) :
    h • reynolds G V v = reynolds G V v := by
  unfold reynolds
  rw [smul_comm h ((Fintype.card G : ℚ)⁻¹)]
  congr 1
  rw [Finset.smul_sum]
  simpa only [Equiv.coe_mulLeft, smul_smul] using
    (Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => g • v))

variable {G V}
variable {W : Type*}
variable [AddCommGroup W] [Module ℚ W]
variable [DistribMulAction G W] [SMulCommClass G ℚ W]

omit [SMulCommClass G ℚ V] [SMulCommClass G ℚ W] in
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

end Experiments.EquivariantAveraging
