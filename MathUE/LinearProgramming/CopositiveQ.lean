/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import FixedPointTheorems.brouwer
import MathUE.LinearProgramming.Tournament

/-!
# Copositive plus `R₀` implies standard `Q`

This file develops the textbook nonhomogeneous linear complementarity problem
`LCP(M, q)`: find `z ≥ 0` with residual `w = q + Mz ≥ 0` and `z i * w i = 0`
at every coordinate.  The matrix convention is the repository's row
convention, `(Mz) i = ∑ j, z j * M i j`.

The headline result is that a copositive `R₀` matrix is a `Q`-matrix.  Nothing
here is game-semantic.  The game-facing `Q`-matrix predicates in the
production quitting lane spell out the same three conditions in the same row
convention, so the bridge to them is a field-by-field conversion; it is not
built here, because this lane may not depend on the game-semantic modules.

## Main definitions

* `lcpResidual` — the residual `w = q + Mz`
* `IsStandardLCPSolution`, `StandardLCPSolvable`, `IsStandardQ`
* `IsCopositive` — `⟨z, Mz⟩ ≥ 0` for every nonnegative `z`
* `IsR0Matrix` — `LCP(M, 0)` has only the zero solution

## Main results

* `isR0Matrix_iff_not_singletonLCPFeasible` — `R₀` is exactly the negation of
  the homogeneous simplex branch already used in `SingletonLCP.lean`
* `exists_simplex_variationalInequality` — Hartman–Stampacchia on the standard
  simplex, via `brouwer_fixed_point` and the Nash excess map
* `exists_truncated_variationalInequality` — the same on the truncation
  `K r = {z ≥ 0 : ∑ z ≤ r}`
* `copositive_isR0Matrix_isStandardQ` — the headline implication
* `isStandardQ_tournamentSkewMatrix` — the tournament corollary, combining the
  headline implication with the quadratic-form and no-sink results of
  `Tournament.lean`

## Topological input

The only topological ingredients are `brouwer_fixed_point` (from the pinned
`fixed-point-theorems` package) and the extreme value theorem on the compact
standard simplex.  Everything else is finite-dimensional linear algebra with
explicit perturbations.
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι]

/-! ## The standard linear complementarity problem -/

/-- The standard LCP residual `w = q + Mz`, in the repository's row convention
`(Mz) i = ∑ j, z j * M i j`. -/
def lcpResidual (M : ι → ι → ℝ) (q z : ι → ℝ) (i : ι) : ℝ :=
  q i + ∑ j, z j * M i j

/-- `z` solves the standard linear complementarity problem `LCP(M, q)`. -/
structure IsStandardLCPSolution (M : ι → ι → ℝ) (q z : ι → ℝ) : Prop where
  /-- The weight vector is nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ z i
  /-- The residual `q + Mz` is nonnegative. -/
  residual_nonneg : ∀ i, 0 ≤ lcpResidual M q z i
  /-- Weight and residual are complementary at every coordinate. -/
  complementary : ∀ i, z i * lcpResidual M q z i = 0

/-- The standard LCP is solvable for this right-hand side. -/
def StandardLCPSolvable (M : ι → ι → ℝ) (q : ι → ℝ) : Prop :=
  ∃ z : ι → ℝ, IsStandardLCPSolution M q z

/-- Textbook `Q`: the standard LCP is solvable for every right-hand side. -/
def IsStandardQ (M : ι → ι → ℝ) : Prop :=
  ∀ q : ι → ℝ, StandardLCPSolvable M q

/-- Copositivity on the nonnegative orthant: `⟨z, Mz⟩ ≥ 0` whenever `z ≥ 0`. -/
def IsCopositive (M : ι → ι → ℝ) : Prop :=
  ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) → 0 ≤ ∑ i, z i * ∑ j, z j * M i j

/-- The `R₀` property: the homogeneous problem `LCP(M, 0)` has only the zero
solution. -/
def IsR0Matrix (M : ι → ι → ℝ) : Prop :=
  ∀ z : ι → ℝ, IsStandardLCPSolution M 0 z → ∀ i, z i = 0

/-- Unfolding lemma for the residual. -/
@[simp] theorem lcpResidual_def (M : ι → ι → ℝ) (q z : ι → ℝ) (i : ι) :
    lcpResidual M q z i = q i + ∑ j, z j * M i j := rfl

/-- The homogeneous residual is the plain matrix action. -/
theorem lcpResidual_zero (M : ι → ι → ℝ) (z : ι → ℝ) (i : ι) :
    lcpResidual M 0 z i = ∑ j, z j * M i j := by
  simp [lcpResidual]

/-! ## `R₀` is the negation of the homogeneous simplex branch -/

/-- The normalized singleton residual is the plain matrix action at the
underlying weight vector. -/
theorem singletonLCPResidual_eq (M : ι → ι → ℝ) (lam : stdSimplex ℝ ι) (i : ι) :
    singletonLCPResidual M lam i = ∑ j, lam.val j * M i j := rfl

/-- **`R₀` versus the homogeneous simplex branch.** A nonzero nonnegative
solution of `LCP(M, 0)` rescales to a simplex point and conversely, so the
normalized singleton LCP of `SingletonLCP.lean` is feasible exactly when `M`
fails `R₀`. -/
theorem isR0Matrix_iff_not_singletonLCPFeasible (M : ι → ι → ℝ) :
    IsR0Matrix M ↔ ¬SingletonLCPFeasible M := by
  classical
  constructor
  · rintro hR0 ⟨lam, hnn, hcomp⟩
    have hsol : IsStandardLCPSolution M 0 lam.val := by
      refine ⟨lam.property.1, fun i => ?_, fun i => ?_⟩
      · rw [lcpResidual_zero, ← singletonLCPResidual_eq]
        exact hnn i
      · rw [lcpResidual_zero, ← singletonLCPResidual_eq]
        exact hcomp i
    have hzero : ∀ i, lam.val i = 0 := hR0 lam.val hsol
    have hone := lam.property.2
    simp [hzero] at hone
  · intro hno z hsol i
    by_contra hi
    have hpos : 0 < z i := lt_of_le_of_ne (hsol.weight_nonneg i) (Ne.symm hi)
    have hsum_pos : 0 < ∑ j, z j :=
      Finset.sum_pos' (fun j _ => hsol.weight_nonneg j) ⟨i, Finset.mem_univ i, hpos⟩
    have hmem : (fun j => z j / ∑ k, z k) ∈ stdSimplex ℝ ι :=
      ⟨fun j => div_nonneg (hsol.weight_nonneg j) hsum_pos.le,
        by rw [← Finset.sum_div]; exact div_self hsum_pos.ne'⟩
    set lam : stdSimplex ℝ ι := ⟨_, hmem⟩ with hlam
    have hres : ∀ j, singletonLCPResidual M lam j = (∑ k, z k * M j k) / ∑ k, z k := by
      intro j
      rw [singletonLCPResidual_eq]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by rw [hlam]; ring
    refine hno ⟨lam, fun j => ?_, fun j => ?_⟩
    · rw [hres j]
      have hnn := hsol.residual_nonneg j
      rw [lcpResidual_zero] at hnn
      exact div_nonneg hnn hsum_pos.le
    · rw [hres j]
      have hc := hsol.complementary j
      rw [lcpResidual_zero] at hc
      have hval : lam.val j = z j / ∑ k, z k := rfl
      rw [hval, div_mul_div_comm, hc]
      simp

/-! ## Hartman–Stampacchia on the standard simplex

The variational inequality on the standard simplex is produced by Brouwer's
fixed-point theorem applied to the Nash excess map.  For a continuous field
`G` the inequality `⟨G u, v - u⟩ ≥ 0` for all simplex points `v` is equivalent
to the coordinatewise form `⟨G u, u⟩ ≤ G u k`, which is what we prove. -/

section SimplexVI

variable {κ : Type*} [Fintype κ]

/-- The Nash excess at coordinate `k`: the amount by which coordinate `k`
improves on the current weighted average of the field `G`. -/
private def viExcess (G : (κ → ℝ) → κ → ℝ) (u : κ → ℝ) (k : κ) : ℝ :=
  max 0 ((∑ l, u l * G u l) - G u k)

private theorem viExcess_nonneg (G : (κ → ℝ) → κ → ℝ) (u : κ → ℝ) (k : κ) :
    0 ≤ viExcess G u k := le_max_left _ _

private theorem viExcess_sum_nonneg (G : (κ → ℝ) → κ → ℝ) (u : κ → ℝ) :
    0 ≤ ∑ l, viExcess G u l :=
  Finset.sum_nonneg fun l _ => viExcess_nonneg G u l

/-- The Nash excess map: add the excess to each coordinate and renormalize. -/
private def nashExcessMap (G : (κ → ℝ) → κ → ℝ) (u : κ → ℝ) : κ → ℝ :=
  fun k => (u k + viExcess G u k) / (1 + ∑ l, viExcess G u l)

private theorem continuous_viAverage {G : (κ → ℝ) → κ → ℝ} (hG : Continuous G) :
    Continuous fun u : κ → ℝ => ∑ l, u l * G u l :=
  continuous_finsetSum _ fun l _ => (continuous_apply l).mul ((continuous_apply l).comp hG)

private theorem continuous_viExcess {G : (κ → ℝ) → κ → ℝ} (hG : Continuous G) (k : κ) :
    Continuous fun u : κ → ℝ => viExcess G u k :=
  continuous_const.max ((continuous_viAverage hG).sub ((continuous_apply k).comp hG))

private theorem continuous_nashExcessMap {G : (κ → ℝ) → κ → ℝ} (hG : Continuous G) :
    Continuous (nashExcessMap G) := by
  refine continuous_pi fun k => ?_
  refine Continuous.div ((continuous_apply k).add (continuous_viExcess hG k))
    (continuous_const.add (continuous_finsetSum _ fun l _ => continuous_viExcess hG l))
    fun u => ?_
  have h := viExcess_sum_nonneg G u
  intro hzero
  linarith

private theorem nashExcessMap_mem {G : (κ → ℝ) → κ → ℝ} {u : κ → ℝ}
    (hu : u ∈ stdSimplex ℝ κ) : nashExcessMap G u ∈ stdSimplex ℝ κ := by
  have hC := viExcess_sum_nonneg G u
  have hden : (0 : ℝ) < 1 + ∑ l, viExcess G u l := by linarith
  refine ⟨fun k => div_nonneg (by linarith [hu.1 k, viExcess_nonneg G u k]) hden.le, ?_⟩
  have hsplit : (∑ k, nashExcessMap G u k) =
      (∑ k, (u k + viExcess G u k)) / (1 + ∑ l, viExcess G u l) :=
    (Finset.sum_div _ _ _).symm
  rw [hsplit, Finset.sum_add_distrib, hu.2]
  exact div_self hden.ne'

/-- **Hartman–Stampacchia on the standard simplex.** For a continuous field
`G` there is a simplex point `u` at which no coordinate direction improves:
the weighted average `⟨G u, u⟩` is a lower bound for every coordinate of
`G u`.  Equivalently `⟨G u, v - u⟩ ≥ 0` for every simplex point `v`
(`simplex_variationalInequality_of_le`).

The sole topological ingredient is `brouwer_fixed_point`. -/
theorem exists_simplex_variationalInequality [Nonempty κ]
    (G : (κ → ℝ) → κ → ℝ) (hG : Continuous G) :
    ∃ u ∈ stdSimplex ℝ κ, ∀ k, (∑ l, u l * G u l) ≤ G u k := by
  classical
  set Δ : Set (κ → ℝ) := stdSimplex ℝ κ with hΔ
  have hcvx : Convex ℝ Δ := convex_stdSimplex ℝ _
  have hcpt : IsCompact Δ := isCompact_stdSimplex ℝ _
  have hne : Δ.Nonempty := by
    obtain ⟨k₀⟩ := ‹Nonempty κ›
    exact ⟨fun k => if k = k₀ then 1 else 0,
      fun k => by by_cases h : k = k₀ <;> simp [h], by simp⟩
  let Φ : Δ → Δ := fun u => ⟨nashExcessMap G u.1, nashExcessMap_mem u.2⟩
  have hΦ : Continuous Φ :=
    continuous_induced_rng.2 ((continuous_nashExcessMap hG).comp continuous_subtype_val)
  obtain ⟨u, hufix⟩ := brouwer_fixed_point Δ hcvx hcpt hne ⟨Φ, hΦ⟩
  have hmem : u.1 ∈ stdSimplex ℝ κ := u.2
  have heq : nashExcessMap G u.1 = u.1 := congrArg Subtype.val hufix
  set C : ℝ := ∑ l, viExcess G u.1 l with hCdef
  have hCnn : 0 ≤ C := viExcess_sum_nonneg G u.1
  have hden : (0 : ℝ) < 1 + C := by linarith
  -- The fixed-point equation reads `excess k = u k * C` coordinatewise.
  have hbal : ∀ k, viExcess G u.1 k = u.1 k * C := by
    intro k
    have hk : (u.1 k + viExcess G u.1 k) / (1 + C) = u.1 k := congrFun heq k
    field_simp at hk
    linarith [hk]
  -- The total excess must vanish.
  have hC0 : C = 0 := by
    by_contra hne0
    have hCpos : 0 < C := lt_of_le_of_ne hCnn (Ne.symm hne0)
    obtain ⟨k₀, hk₀⟩ : ∃ k, 0 < u.1 k := by
      by_contra hnone
      have hzero : ∀ k, u.1 k = 0 := fun k =>
        le_antisymm (le_of_not_gt fun h => hnone ⟨k, h⟩) (hmem.1 k)
      have := hmem.2
      simp [hzero] at this
    have hstrict : ∀ k, 0 < u.1 k → G u.1 k < ∑ l, u.1 l * G u.1 l := by
      intro k hk
      have hex : 0 < viExcess G u.1 k := by
        rw [hbal k]; exact mul_pos hk hCpos
      have := (lt_max_iff.mp hex)
      rcases this with h | h
      · exact absurd h (lt_irrefl 0)
      · linarith
    have hlt : (∑ k, u.1 k * G u.1 k) < ∑ k, u.1 k * (∑ l, u.1 l * G u.1 l) := by
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨k₀, Finset.mem_univ k₀, ?_⟩
      · rcases eq_or_lt_of_le (hmem.1 k) with h | h
        · simp [← h]
        · exact le_of_lt (mul_lt_mul_of_pos_left (hstrict k h) h)
      · exact mul_lt_mul_of_pos_left (hstrict k₀ hk₀) hk₀
    rw [← Finset.sum_mul, hmem.2, one_mul] at hlt
    exact absurd hlt (lt_irrefl _)
  refine ⟨u.1, hmem, fun k => ?_⟩
  have hzero : max 0 ((∑ l, u.1 l * G u.1 l) - G u.1 k) = 0 := by
    change viExcess G u.1 k = 0
    rw [hbal k, hC0, mul_zero]
  have hle := max_eq_left_iff.mp hzero
  linarith

/-- The coordinatewise form of the variational inequality implies the pairing
form against every simplex point. -/
theorem simplex_variationalInequality_of_le {G : (κ → ℝ) → κ → ℝ} {u : κ → ℝ}
    (h : ∀ k, (∑ l, u l * G u l) ≤ G u k) {v : κ → ℝ} (hv : v ∈ stdSimplex ℝ κ) :
    (∑ l, u l * G u l) ≤ ∑ k, v k * G u k := by
  have hge : (∑ k, v k * (∑ l, u l * G u l)) ≤ ∑ k, v k * G u k :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (hv.1 k)
  rwa [← Finset.sum_mul, hv.2, one_mul] at hge

end SimplexVI

/-! ## The truncated variational inequality

`K r = {z : z ≥ 0, ∑ z ≤ r}` is the image of the standard simplex over
`Option ι` under `u ↦ r · (u ∘ some)`, the extra coordinate carrying the slack
in the budget constraint.  Transporting the simplex inequality along that
affine bijection gives the variational inequality on `K r` for the affine
field `z ↦ q + Mz`. -/

section Truncation

/-- The affine field `q + Mz` transported to the simplex over `Option ι`; the
slack coordinate carries the value zero. -/
private def truncField (M : ι → ι → ℝ) (q : ι → ℝ) (r : ℝ) (v : Option ι → ℝ) :
    Option ι → ℝ
  | none => 0
  | some i => lcpResidual M q (fun j => r * v (some j)) i

/-- The point of the simplex over `Option ι` corresponding to `y ∈ K r`. -/
private def truncSimplexPoint (r : ℝ) (y : ι → ℝ) : Option ι → ℝ
  | none => (r - ∑ i, y i) / r
  | some i => y i / r

private theorem continuous_truncField (M : ι → ι → ℝ) (q : ι → ℝ) (r : ℝ) :
    Continuous (truncField M q r) := by
  refine continuous_pi fun k => ?_
  cases k with
  | none => exact continuous_const
  | some i =>
      show Continuous fun v : Option ι → ℝ => q i + ∑ j, (r * v (some j)) * M i j
      refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
      have h1 : Continuous fun v : Option ι → ℝ => v (some j) := continuous_apply (some j)
      have h2 : Continuous fun v : Option ι → ℝ => r * v (some j) := h1.const_mul r
      exact h2.mul_const (M i j)

/-- **The truncated variational inequality.** For every budget `r > 0` there
is a point of `K r = {z ≥ 0 : ∑ z ≤ r}` at which the affine field `q + Mz`
points outward: moving to any other point of `K r` cannot decrease the
pairing.  This is Hartman–Stampacchia for `K r`, obtained from
`exists_simplex_variationalInequality` through the affine bijection with the
standard simplex over `Option ι`. -/
theorem exists_truncated_variationalInequality (M : ι → ι → ℝ) (q : ι → ℝ) {r : ℝ}
    (hr : 0 < r) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ r ∧
      ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → (∑ i, y i) ≤ r →
        0 ≤ ∑ i, (y i - z i) * lcpResidual M q z i := by
  classical
  obtain ⟨u, hu, hvi⟩ :=
    exists_simplex_variationalInequality (κ := Option ι) (truncField M q r)
      (continuous_truncField M q r)
  have hrne : r ≠ 0 := hr.ne'
  set z : ι → ℝ := fun i => r * u (some i) with hz
  have hres : ∀ i, truncField M q r u (some i) = lcpResidual M q z i := fun _ => rfl
  have hnone : truncField M q r u none = (0 : ℝ) := rfl
  have haverage : (∑ l, u l * truncField M q r u l) = ∑ i, u (some i) * lcpResidual M q z i := by
    rw [Fintype.sum_option]
    simp only [hres, hnone, mul_zero, zero_add]
  have htotal : u none + ∑ i, u (some i) = 1 := by
    have h := hu.2
    rwa [Fintype.sum_option] at h
  refine ⟨z, fun i => mul_nonneg hr.le (hu.1 _), ?_, ?_⟩
  · have hle : (∑ i, u (some i)) ≤ 1 := by linarith [hu.1 none]
    calc (∑ i, z i) = r * ∑ i, u (some i) := by rw [hz, Finset.mul_sum]
      _ ≤ r * 1 := by exact mul_le_mul_of_nonneg_left hle hr.le
      _ = r := mul_one r
  · intro y hy hybudget
    have hvmem : truncSimplexPoint r y ∈ stdSimplex ℝ (Option ι) := by
      constructor
      · intro k
        cases k with
        | none => exact div_nonneg (by linarith) hr.le
        | some i => exact div_nonneg (hy i) hr.le
      · rw [Fintype.sum_option]
        show (r - ∑ i, y i) / r + ∑ i, y i / r = 1
        rw [← Finset.sum_div]
        field_simp
        ring
    have hpair := simplex_variationalInequality_of_le hvi hvmem
    rw [haverage, Fintype.sum_option] at hpair
    have hpnone : truncSimplexPoint r y none = (r - ∑ i, y i) / r := rfl
    have hpsome : ∀ i, truncSimplexPoint r y (some i) = y i / r := fun _ => rfl
    simp only [hres, hnone, hpnone, hpsome, mul_zero, zero_add] at hpair
    have hscaled := mul_le_mul_of_nonneg_left hpair hr.le
    have hleft : r * ∑ i, u (some i) * lcpResidual M q z i =
        ∑ i, z i * lcpResidual M q z i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hz]; ring
    have hright : r * ∑ i, y i / r * lcpResidual M q z i =
        ∑ i, y i * lcpResidual M q z i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    rw [hleft, hright] at hscaled
    have hsplit : (∑ i, (y i - z i) * lcpResidual M q z i) =
        (∑ i, y i * lcpResidual M q z i) - ∑ i, z i * lcpResidual M q z i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    linarith

end Truncation

/-! ## The interior case: a variational-inequality point with budget slack -/

/-- **The interior case.** A truncated variational-inequality point that does
not exhaust the budget solves `LCP(M, q)`.  Both perturbations stay inside
`K r`: increasing one coordinate by the remaining slack, and deleting one
coordinate. -/
theorem isStandardLCPSolution_of_truncated_of_lt (M : ι → ι → ℝ) (q : ι → ℝ) {r : ℝ}
    {z : ι → ℝ} (hznn : ∀ i, 0 ≤ z i) (hlt : (∑ i, z i) < r)
    (hvi : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → (∑ i, y i) ≤ r →
      0 ≤ ∑ i, (y i - z i) * lcpResidual M q z i) :
    IsStandardLCPSolution M q z := by
  classical
  have hslack : 0 < r - ∑ i, z i := by linarith
  have hres : ∀ i, 0 ≤ lcpResidual M q z i := by
    intro i
    set c : ℝ := r - ∑ k, z k with hc
    have hynn : ∀ j, 0 ≤ z j + if j = i then c else 0 := by
      intro j
      by_cases h : j = i
      · rw [if_pos h]; linarith [hznn j, hslack]
      · rw [if_neg h]; linarith [hznn j]
    have hy := hvi (fun j => z j + if j = i then c else 0) hynn
      (by rw [Finset.sum_add_distrib]; simp [hc])
    have hsimp : (∑ j, ((z j + if j = i then c else 0) - z j) * lcpResidual M q z j) =
        c * lcpResidual M q z i := by
      refine (Finset.sum_eq_single i ?_ ?_).trans (by simp)
      · intro j _ hj; simp [hj]
      · intro hj; exact absurd (Finset.mem_univ i) hj
    rw [hsimp] at hy
    exact nonneg_of_mul_nonneg_right hy hslack
  refine ⟨hznn, hres, fun i => ?_⟩
  have hynn : ∀ j, 0 ≤ z j - if j = i then z i else 0 := by
    intro j
    by_cases h : j = i
    · rw [if_pos h, h]; linarith
    · rw [if_neg h]; linarith [hznn j]
  have hy := hvi (fun j => z j - if j = i then z i else 0) hynn
    (by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      linarith [hznn i])
  have hsimp : (∑ j, ((z j - if j = i then z i else 0) - z j) * lcpResidual M q z j) =
      -(z i * lcpResidual M q z i) := by
    refine (Finset.sum_eq_single i ?_ ?_).trans (by simp)
    · intro j _ hj; simp [hj]
    · intro hj; exact absurd (Finset.mem_univ i) hj
  rw [hsimp] at hy
  have hle : z i * lcpResidual M q z i ≤ 0 := by linarith
  exact le_antisymm hle (mul_nonneg (hznn i) (hres i))

/-! ## The boundary case: normalized approximate homogeneous solutions -/

/-- How far a nonnegative vector is from solving the homogeneous problem
`LCP(M, 0)`: the excess of the quadratic form over zero plus the total
negative part of the matrix action. -/
def homogeneousViolation (M : ι → ι → ℝ) (p : ι → ℝ) : ℝ :=
  max 0 (∑ i, p i * ∑ j, p j * M i j) + ∑ i, max 0 (-(∑ j, p j * M i j))

theorem homogeneousViolation_nonneg (M : ι → ι → ℝ) (p : ι → ℝ) :
    0 ≤ homogeneousViolation M p :=
  add_nonneg (le_max_left _ _) (Finset.sum_nonneg fun _ _ => le_max_left _ _)

theorem continuous_homogeneousViolation (M : ι → ι → ℝ) :
    Continuous (homogeneousViolation M) := by
  have hrow : ∀ i : ι, Continuous fun p : ι → ℝ => ∑ j, p j * M i j := by
    intro i
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun p : ι → ℝ => p j := continuous_apply j
    exact h1.mul_const (M i j)
  refine Continuous.add ?_ (continuous_finsetSum _ fun i _ => ?_)
  · exact continuous_const.max
      (continuous_finsetSum _ fun i _ => (continuous_apply i).mul (hrow i))
  · exact continuous_const.max (hrow i).neg

/-- A simplex point of zero homogeneous violation is a witness for the
homogeneous simplex branch. -/
theorem singletonLCPFeasible_of_violation_nonpos (M : ι → ι → ℝ) {p : ι → ℝ}
    (hp : p ∈ stdSimplex ℝ ι) (hviol : homogeneousViolation M p ≤ 0) :
    SingletonLCPFeasible M := by
  classical
  have hsplit : max 0 (∑ i, p i * ∑ j, p j * M i j) = 0 ∧
      (∑ i, max 0 (-(∑ j, p j * M i j))) = 0 := by
    have h1 : (0 : ℝ) ≤ max 0 (∑ i, p i * ∑ j, p j * M i j) := le_max_left _ _
    have h2 : (0 : ℝ) ≤ ∑ i, max 0 (-(∑ j, p j * M i j)) :=
      Finset.sum_nonneg fun _ _ => le_max_left _ _
    have hsum := hviol
    rw [homogeneousViolation] at hsum
    exact ⟨le_antisymm (by linarith) h1, le_antisymm (by linarith) h2⟩
  have hrow : ∀ i, 0 ≤ ∑ j, p j * M i j := by
    intro i
    have hterm : max 0 (-(∑ j, p j * M i j)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => le_max_left _ _)).mp hsplit.2 i
        (Finset.mem_univ i)
    have := max_eq_left_iff.mp hterm
    linarith
  have hquad_le : (∑ i, p i * ∑ j, p j * M i j) ≤ 0 := max_eq_left_iff.mp hsplit.1
  have hquad_ge : 0 ≤ ∑ i, p i * ∑ j, p j * M i j :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (hrow i)
  have hquad : (∑ i, p i * ∑ j, p j * M i j) = 0 := le_antisymm hquad_le hquad_ge
  refine ⟨⟨p, hp⟩, fun i => hrow i, fun i => ?_⟩
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hp.1 i) (hrow i))).mp hquad i (Finset.mem_univ i)

/-- **Compactness limit.** If the homogeneous violation can be made
arbitrarily small on the standard simplex then it is actually attained at
zero, so the homogeneous simplex branch is nonempty.  The extreme value
theorem on the compact simplex is the only topological input. -/
theorem singletonLCPFeasible_of_approximate (M : ι → ι → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ p ∈ stdSimplex ℝ ι, homogeneousViolation M p ≤ ε) :
    SingletonLCPFeasible M := by
  classical
  obtain ⟨p₁, hp₁, _⟩ := h 1 one_pos
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_stdSimplex ℝ (ι := ι)).exists_isMinOn ⟨p₁, hp₁⟩
      (continuous_homogeneousViolation M).continuousOn
  refine singletonLCPFeasible_of_violation_nonpos M hp ?_
  by_contra hpos
  push Not at hpos
  obtain ⟨p', hp', hle⟩ := h (homogeneousViolation M p / 2) (by linarith)
  have := hmin hp'
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- **The boundary case.** A truncated variational-inequality point that
exhausts the budget normalizes to a simplex point whose homogeneous violation
is `O(1/r)`.  Copositivity enters only through the lower bound on the pairing
`⟨z, q + Mz⟩`. -/
theorem homogeneousViolation_normalized_le_of_bound (M : ι → ι → ℝ) (q : ι → ℝ)
    (hcop : IsCopositive M) {r Bq : ℝ} (hr : 0 < r) (hBq_nonneg : 0 ≤ Bq)
    (hq_le : ∀ i, |q i| ≤ Bq) {z : ι → ℝ} (hznn : ∀ i, 0 ≤ z i)
    (hsum : (∑ i, z i) = r)
    (hvi : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → (∑ i, y i) ≤ r →
      0 ≤ ∑ i, (y i - z i) * lcpResidual M q z i) :
    homogeneousViolation M (fun i => z i / r) ≤
      (2 * (Fintype.card ι : ℝ) + 1) * Bq / r := by
  classical
  -- The pairing `⟨z, q + Mz⟩` and its two bounds.
  have hpair_eq : (∑ i, z i * lcpResidual M q z i) =
      (∑ i, z i * q i) + ∑ i, z i * ∑ j, z j * M i j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [lcpResidual_def]; ring
  have hquad_nonneg : 0 ≤ ∑ i, z i * ∑ j, z j * M i j := hcop z hznn
  have hzq_ge : -(r * Bq) ≤ ∑ i, z i * q i := by
    have hterm : ∀ i, -(z i * Bq) ≤ z i * q i := by
      intro i
      have h1 : -(z i * |q i|) ≤ z i * q i := by
        nlinarith [neg_abs_le (q i), hznn i]
      have h2 : z i * |q i| ≤ z i * Bq :=
        mul_le_mul_of_nonneg_left (hq_le i) (hznn i)
      linarith
    have hsum_le : (∑ i, -(z i * Bq)) ≤ ∑ i, z i * q i :=
      Finset.sum_le_sum fun i _ => hterm i
    have hconst : (∑ i, -(z i * Bq)) = -(r * Bq) := by
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hsum]
    linarith [hsum_le, hconst.symm.le, hconst.le]
  have hpair_le : (∑ i, z i * lcpResidual M q z i) ≤ 0 := by
    have h := hvi (fun _ => 0) (fun _ => le_refl 0) (by simp; linarith)
    have hsimp : (∑ i, ((0 : ℝ) - z i) * lcpResidual M q z i) =
        -∑ i, z i * lcpResidual M q z i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsimp] at h
    linarith
  have hpair_ge : -(r * Bq) ≤ ∑ i, z i * lcpResidual M q z i := by
    rw [hpair_eq]; linarith
  have hquad_le : (∑ i, z i * ∑ j, z j * M i j) ≤ r * Bq := by
    rw [hpair_eq] at hpair_le; linarith
  -- Every residual coordinate is bounded below, by testing against `r • eⱼ`.
  have hres_ge : ∀ j, -Bq ≤ lcpResidual M q z j := by
    intro j
    have hynn : ∀ k, 0 ≤ if k = j then r else (0 : ℝ) := by
      intro k
      by_cases hk : k = j
      · rw [if_pos hk]; exact hr.le
      · rw [if_neg hk]
    have h := hvi (fun k => if k = j then r else 0) hynn (by simp)
    have hsplit : (∑ k, ((if k = j then r else 0) - z k) * lcpResidual M q z k) =
        (∑ k, (if k = j then r else 0) * lcpResidual M q z k) -
          ∑ k, z k * lcpResidual M q z k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hsingle : (∑ k, (if k = j then r else 0) * lcpResidual M q z k) =
        r * lcpResidual M q z j := by
      refine (Finset.sum_eq_single j ?_ ?_).trans (by simp)
      · intro k _ hk; rw [if_neg hk]; ring
      · intro hk; exact absurd (Finset.mem_univ j) hk
    rw [hsplit, hsingle] at h
    have hrj : -(r * Bq) ≤ r * lcpResidual M q z j := by linarith
    nlinarith [hrj, hr]
  -- Normalize and bound the two pieces of the violation.
  set p : ι → ℝ := fun i => z i / r with hp
  have hrow : ∀ i, (∑ j, p j * M i j) = (∑ j, z j * M i j) / r := by
    intro i
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by rw [hp]; ring
  have hquadp : (∑ i, p i * ∑ j, p j * M i j) =
      (∑ i, z i * ∑ j, z j * M i j) / (r * r) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrow i, hp]
    field_simp
  have hquadp_le : (∑ i, p i * ∑ j, p j * M i j) ≤ Bq / r := by
    have hrr : (0 : ℝ) < r * r := by positivity
    rw [hquadp, div_le_iff₀ hrr]
    have hclear : Bq / r * (r * r) = Bq * r := by field_simp
    rw [hclear]
    nlinarith [hquad_le]
  have hrowp_ge : ∀ i, -(2 * Bq / r) ≤ ∑ j, p j * M i j := by
    intro i
    have hzM : -(2 * Bq) ≤ ∑ j, z j * M i j := by
      have h := hres_ge i
      rw [lcpResidual_def] at h
      nlinarith [hq_le i, le_abs_self (q i), neg_abs_le (q i)]
    have hdiv : (-(2 * Bq)) / r ≤ (∑ j, z j * M i j) / r := by gcongr
    rw [hrow i, ← neg_div]
    exact hdiv
  -- Assemble.
  have hpiece1 : max 0 (∑ i, p i * ∑ j, p j * M i j) ≤ Bq / r :=
    max_le (by positivity) hquadp_le
  have hpiece2 : (∑ i, max 0 (-(∑ j, p j * M i j))) ≤
      (Fintype.card ι : ℝ) * (2 * Bq / r) := by
    have hbound : ∀ i, max 0 (-(∑ j, p j * M i j)) ≤ 2 * Bq / r := by
      intro i
      exact max_le (by positivity) (by linarith [hrowp_ge i])
    calc (∑ i, max 0 (-(∑ j, p j * M i j))) ≤ ∑ _i : ι, (2 * Bq / r) :=
          Finset.sum_le_sum fun i _ => hbound i
      _ = (Fintype.card ι : ℝ) * (2 * Bq / r) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [homogeneousViolation]
  have hfinal : Bq / r + (Fintype.card ι : ℝ) * (2 * Bq / r) =
      (2 * (Fintype.card ι : ℝ) + 1) * Bq / r := by
    field_simp
    ring
  linarith [hpiece1, hpiece2, hfinal.symm.le, hfinal.le]

/-- The `‖q‖₁` reading of the boundary bound: the total `∑ i, |q i|` bounds
every coordinate. -/
theorem homogeneousViolation_normalized_le (M : ι → ι → ℝ) (q : ι → ℝ)
    (hcop : IsCopositive M) {r : ℝ} (hr : 0 < r) {z : ι → ℝ} (hznn : ∀ i, 0 ≤ z i)
    (hsum : (∑ i, z i) = r)
    (hvi : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → (∑ i, y i) ≤ r →
      0 ≤ ∑ i, (y i - z i) * lcpResidual M q z i) :
    homogeneousViolation M (fun i => z i / r) ≤
      (2 * (Fintype.card ι : ℝ) + 1) * (∑ i, |q i|) / r :=
  homogeneousViolation_normalized_le_of_bound M q hcop hr
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (fun i => Finset.single_le_sum (f := fun i => |q i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i))
    hznn hsum hvi

/-! ## The headline theorem -/

/-- **Copositive plus `R₀` implies standard `Q`.** For every right-hand side
`q`, the truncated variational inequality on `K r` either has budget slack —
and then already solves `LCP(M, q)` — or exhausts the budget, in which case
the normalized point has homogeneous violation `O(1/r)`.  Letting `r` grow,
the extreme value theorem produces an exact nonzero homogeneous solution,
contradicting `R₀`.  Copositivity is used only for the lower bound on the
pairing `⟨z, q + Mz⟩`. -/
theorem standardLCPSolvable_of_copositive_of_isR0Matrix (M : ι → ι → ℝ)
    (hcop : IsCopositive M) (hR0 : IsR0Matrix M) (q : ι → ℝ) :
    StandardLCPSolvable M q := by
  classical
  by_contra hno
  refine (isR0Matrix_iff_not_singletonLCPFeasible M).mp hR0 ?_
  refine singletonLCPFeasible_of_approximate M fun ε hε => ?_
  set Bq : ℝ := ∑ i, |q i| with hBq
  have hBq_nonneg : 0 ≤ Bq := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set D : ℝ := (2 * (Fintype.card ι : ℝ) + 1) * Bq with hD
  have hD_nonneg : 0 ≤ D := by
    have : (0 : ℝ) ≤ 2 * (Fintype.card ι : ℝ) + 1 := by positivity
    exact mul_nonneg this hBq_nonneg
  set r : ℝ := (D + 1) / ε with hrdef
  have hr : 0 < r := by rw [hrdef]; positivity
  obtain ⟨z, hznn, hzle, hvi⟩ := exists_truncated_variationalInequality M q hr
  have hsum : (∑ i, z i) = r := by
    rcases lt_or_eq_of_le hzle with hlt | heq
    · exact absurd ⟨z, isStandardLCPSolution_of_truncated_of_lt M q hznn hlt hvi⟩ hno
    · exact heq
  have hmem : (fun i => z i / r) ∈ stdSimplex ℝ ι :=
    ⟨fun i => div_nonneg (hznn i) hr.le, by rw [← Finset.sum_div, hsum]; exact div_self hr.ne'⟩
  refine ⟨fun i => z i / r, hmem, ?_⟩
  have hbound := homogeneousViolation_normalized_le M q hcop hr hznn hsum hvi
  have hDr : D / r ≤ ε := by
    rw [hrdef, div_div_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < D + 1)]
    nlinarith [hD_nonneg, hε]
  calc homogeneousViolation M (fun i => z i / r) ≤ D / r := by rw [hD]; exact hbound
    _ ≤ ε := hDr

/-- **Copositive plus `R₀` implies standard `Q`**, in `Q`-matrix form. -/
theorem copositive_isR0Matrix_isStandardQ (M : ι → ι → ℝ)
    (hcop : IsCopositive M) (hR0 : IsR0Matrix M) : IsStandardQ M :=
  fun q => standardLCPSolvable_of_copositive_of_isR0Matrix M hcop hR0 q

/-! ## The tournament corollary -/

/-- **Skew-dominant tournament matrices are standard `Q`.** For `t > 1` the
tournament quadratic form is nonnegative on the orthant, and an exact outgoing
edge at every vertex rules out the homogeneous simplex branch, which is
exactly `R₀`. -/
theorem isStandardQ_tournamentSkewMatrix (t : ℝ) (A : ι → ι → ℝ)
    (hA : IsFractionalTournament A) (hunit : FractionalTournamentHasUnitOutneighbor A)
    (ht : 1 < t) : IsStandardQ (tournamentSkewMatrix t A) := by
  refine copositive_isR0Matrix_isStandardQ _ (fun z hz => ?_) ?_
  · exact tournamentSkewMatrix_quadratic_nonneg t A hA ht.le z hz
  · exact (isR0Matrix_iff_not_singletonLCPFeasible _).mpr
      (not_singletonLCPFeasible_tournamentSkewMatrix t A hA hunit ht)

end Math.LinearProgramming
