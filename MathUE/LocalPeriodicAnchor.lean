/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-!
# Finite normalized-hazard seam limits

This file isolates the finite-dimensional core of a periodic anchor
obstruction.  A fixed finite matrix is tested against normalized cumulative
hazards.  Compactness supplies the simplex limit; a signed seam and a
vanishing first-order error then force that limit into the matrix kernel.

The first-order error is deliberately an explicit interface.  In a quitting
game it is the place where the Bellman operator, the vanishing row mesh, and
the anchored payoff annotations must be connected by a separate calculation.
-/

namespace MathUE.LocalPeriodicAnchor

noncomputable section

open Filter
open scoped BigOperators Topology

variable {I : Type*} [Fintype I] [DecidableEq I]

def totalHazard (period : ℕ → ℕ) (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (h : ℕ) : ℝ :=
  ∑ phase, ∑ player, q h phase player

def cumulativeHazard (period : ℕ → ℕ) (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (h : ℕ) (player : I) : ℝ :=
  ∑ phase, q h phase player

def normalizedHazard (period : ℕ → ℕ) (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (h : ℕ) (player : I) : ℝ :=
  cumulativeHazard period q h player / totalHazard period q h

def signedSeam (period : ℕ → ℕ) (p : (h : ℕ) → Fin (period h) → I → ℝ)
    (h : ℕ) (player : I) : ℝ :=
  ∑ phase, p h phase player

def matrixApply (matrix : I → I → ℝ) (vector : I → ℝ) (player : I) : ℝ :=
  ∑ other, matrix player other * vector other

omit [Fintype I] [DecidableEq I] in
theorem cumulativeHazard_nonneg
    (period : ℕ → ℕ) (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (hq : ∀ h phase player, 0 ≤ q h phase player) :
    ∀ h player, 0 ≤ cumulativeHazard period q h player := by
  intro h player
  exact Finset.sum_nonneg fun phase _ => hq h phase player

omit [DecidableEq I] in
theorem cumulativeHazard_sum_eq_totalHazard
    (period : ℕ → ℕ) (q : (h : ℕ) → Fin (period h) → I → ℝ) (h : ℕ) :
    ∑ player, cumulativeHazard period q h player = totalHazard period q h := by
  unfold cumulativeHazard totalHazard
  rw [Finset.sum_comm]

omit [DecidableEq I] in
theorem normalizedHazard_nonneg
    (period : ℕ → ℕ) (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (hq : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h) :
    ∀ h player, 0 ≤ normalizedHazard period q h player := by
  intro h player
  exact div_nonneg (cumulativeHazard_nonneg period q hq h player)
    (le_of_lt (hpositive h))

omit [DecidableEq I] in
theorem normalizedHazard_sum_eq_one
    (period : ℕ → ℕ) (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (hpositive : ∀ h, 0 < totalHazard period q h) :
    ∀ h, ∑ player, normalizedHazard period q h player = 1 := by
  intro h
  unfold normalizedHazard
  rw [← Finset.sum_div, cumulativeHazard_sum_eq_totalHazard]
  exact div_self (ne_of_gt (hpositive h))

theorem normalizedHazard_le_one
    (period : ℕ → ℕ) (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (hq : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h) :
    ∀ h player, normalizedHazard period q h player ≤ 1 := by
  intro h player
  have hnonneg : ∀ other, 0 ≤ normalizedHazard period q h other :=
    normalizedHazard_nonneg period q hq hpositive h
  have hrest : 0 ≤ ∑ other ∈ (Finset.univ.erase player),
      normalizedHazard period q h other := by
    exact Finset.sum_nonneg fun other _ => hnonneg other
  have hsplit : normalizedHazard period q h player +
      ∑ other ∈ (Finset.univ.erase player), normalizedHazard period q h other = 1 := by
    calc
      normalizedHazard period q h player +
          ∑ other ∈ (Finset.univ.erase player), normalizedHazard period q h other =
        ∑ other, normalizedHazard period q h other :=
          Finset.add_sum_erase (Finset.univ : Finset I)
            (normalizedHazard period q h) (by simp)
      _ = 1 := normalizedHazard_sum_eq_one period q hpositive h
  linarith

theorem exists_normalizedHazard_subsequence_kernel
    [Nonempty I]
    (period : ℕ → ℕ)
    (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (p : (h : ℕ) → Fin (period h) → I → ℝ)
    (matrix : I → I → ℝ)
    (hQ : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h)
    (hseam : ∀ player, Tendsto
      (fun h => signedSeam period p h player / totalHazard period q h)
      atTop (nhds 0))
    (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hlinear : ∀ h player,
      |signedSeam period p h player / totalHazard period q h -
        matrixApply matrix (normalizedHazard period q h) player| ≤ error h) :
    ∃ limit : I → ℝ, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
      (∀ player, 0 ≤ limit player) ∧
      (∑ player, limit player = 1) ∧
      (∀ player, matrixApply matrix limit player = 0) ∧
      Tendsto (normalizedHazard period q ∘ subsequence) atTop (nhds limit) := by
  let weights : ℕ → I → ℝ := normalizedHazard period q
  let box : Set (I → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)
  have hweights_box : ∀ h, weights h ∈ box := by
    intro h
    rw [Set.mem_pi]
    intro player _
    exact ⟨normalizedHazard_nonneg period q hQ hpositive h player,
      normalizedHazard_le_one period q hQ hpositive h player⟩
  have hbox_compact : IsCompact box := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨limit, hlimit_box, subsequence, hsubsequence, hconverges⟩ :=
    hbox_compact.tendsto_subseq hweights_box
  have hcoordinate : ∀ player, Tendsto
      (fun n => weights (subsequence n) player) atTop (nhds (limit player)) := by
    intro player
    exact (continuous_apply player).tendsto (limit) |>.comp hconverges
  have hlimit_nonneg : ∀ player, 0 ≤ limit player := by
    intro player
    exact (Set.mem_pi.mp hlimit_box player (by simp)).1
  have hweights_sum : ∀ h, ∑ player, weights h player = 1 := by
    intro h
    exact normalizedHazard_sum_eq_one period q hpositive h
  have hlimit_sum : ∑ player, limit player = 1 := by
    have hsum_tendsto : Tendsto
        (fun n => ∑ player, weights (subsequence n) player) atTop
        (nhds (∑ player, limit player)) := by
      apply tendsto_finsetSum
      intro player _
      exact hcoordinate player
    have hsum_const : (fun n => ∑ player, weights (subsequence n) player) =
        (fun _ => (1 : ℝ)) := by
      funext n
      exact hweights_sum (subsequence n)
    rw [hsum_const] at hsum_tendsto
    exact tendsto_nhds_unique hsum_tendsto tendsto_const_nhds
  have hmatrix_tendsto : ∀ player, Tendsto
      (fun h => matrixApply matrix (weights h) player) atTop (nhds 0) := by
    intro player
    have habs : Tendsto
        (fun h => |signedSeam period p h player / totalHazard period q h -
          matrixApply matrix (weights h) player|) atTop (nhds 0) := by
      apply squeeze_zero (fun h => abs_nonneg _)
      · intro h
        exact hlinear h player
      · exact herror
    have hdiff : Tendsto
        (fun h => signedSeam period p h player / totalHazard period q h -
          matrixApply matrix (weights h) player) atTop (nhds 0) := by
      apply (tendsto_zero_iff_norm_tendsto_zero).2
      simpa only [Real.norm_eq_abs] using habs
    have hsub := hseam player |>.sub hdiff
    have heq : (fun h => signedSeam period p h player / totalHazard period q h -
        (signedSeam period p h player / totalHazard period q h -
          matrixApply matrix (weights h) player)) =
        (fun h => matrixApply matrix (weights h) player) := by
      funext h
      ring
    rw [heq] at hsub
    simpa using hsub
  have hmatrix_limit : ∀ player, Tendsto
      (fun n => matrixApply matrix (weights (subsequence n)) player) atTop
      (nhds (matrixApply matrix limit player)) := by
    intro player
    unfold matrixApply
    apply tendsto_finsetSum
    intro other _
    exact (hcoordinate other).const_mul (matrix player other)
  have hkernel : ∀ player, matrixApply matrix limit player = 0 := by
    intro player
    have hzero := hmatrix_tendsto player |>.comp hsubsequence.tendsto_atTop
    exact tendsto_nhds_unique (hmatrix_limit player) hzero
  exact ⟨limit, subsequence, hsubsequence, hlimit_nonneg, hlimit_sum, hkernel,
    hconverges⟩

theorem exists_normalizedHazard_subsequence_kernel_of_norm_seam
    [Nonempty I]
    (period : ℕ → ℕ)
    (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (p : (h : ℕ) → Fin (period h) → I → ℝ)
    (matrix : I → I → ℝ)
    (hQ : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h)
    (hseam : Tendsto
      (fun h => ‖(fun player : I =>
        signedSeam period p h player / totalHazard period q h)‖)
      atTop (nhds 0))
    (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hlinear : ∀ h,
      ‖(fun player : I => signedSeam period p h player / totalHazard period q h -
        matrixApply matrix (normalizedHazard period q h) player)‖ ≤ error h) :
    ∃ limit : I → ℝ, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
      (∀ player, 0 ≤ limit player) ∧
      (∑ player, limit player = 1) ∧
      (∀ player, matrixApply matrix limit player = 0) ∧
      Tendsto (normalizedHazard period q ∘ subsequence) atTop (nhds limit) := by
  have hseam_coordinate : ∀ player, Tendsto
      (fun h => signedSeam period p h player / totalHazard period q h)
      atTop (nhds 0) := by
    intro player
    have hbound : ∀ h, |signedSeam period p h player /
        totalHazard period q h| ≤
        ‖(fun other : I => signedSeam period p h other /
          totalHazard period q h)‖ := by
      intro h
      let vector : I → ℝ := fun other => signedSeam period p h other /
        totalHazard period q h
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm vector player)
    have habs : Tendsto
        (fun h => |signedSeam period p h player /
          totalHazard period q h|) atTop (nhds 0) :=
      squeeze_zero (fun h => abs_nonneg _) hbound hseam
    exact (tendsto_zero_iff_norm_tendsto_zero).2 (by
      simpa only [Real.norm_eq_abs] using habs)
  have hlinear_coordinate : ∀ h player,
      |signedSeam period p h player / totalHazard period q h -
        matrixApply matrix (normalizedHazard period q h) player| ≤ error h := by
    intro h player
    let vector : I → ℝ := fun other => signedSeam period p h other /
      totalHazard period q h - matrixApply matrix (normalizedHazard period q h) other
    have hv := (norm_le_pi_norm vector player).trans (hlinear h)
    simpa only [Real.norm_eq_abs] using
      hv
  exact exists_normalizedHazard_subsequence_kernel period q p matrix hQ hpositive
    hseam_coordinate error herror hlinear_coordinate

theorem exists_normalizedHazard_subsequence_kernel_of_eventually_norm_seam
    [Nonempty I]
    (period : ℕ → ℕ)
    (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (p : (h : ℕ) → Fin (period h) → I → ℝ)
    (matrix : I → I → ℝ)
    (hQ : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h)
    (hseam : Tendsto
      (fun h => ‖(fun player : I =>
        signedSeam period p h player / totalHazard period q h)‖)
      atTop (nhds 0))
    (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hlinear : ∀ᶠ h in atTop, ‖(fun player : I =>
      signedSeam period p h player / totalHazard period q h -
        matrixApply matrix (normalizedHazard period q h) player)‖ ≤ error h) :
    ∃ limit : I → ℝ, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
      (∀ player, 0 ≤ limit player) ∧
      (∑ player, limit player = 1) ∧
      (∀ player, matrixApply matrix limit player = 0) ∧
      Tendsto (normalizedHazard period q ∘ subsequence) atTop (nhds limit) := by
  obtain ⟨start, hstart⟩ := eventually_atTop.1 hlinear
  let shiftedPeriod : ℕ → ℕ := fun h => period (h + start)
  let shiftedQ : (h : ℕ) → Fin (shiftedPeriod h) → I → ℝ :=
    fun h phase player => q (h + start) phase player
  let shiftedP : (h : ℕ) → Fin (shiftedPeriod h) → I → ℝ :=
    fun h phase player => p (h + start) phase player
  have hQ' : ∀ h phase player, 0 ≤ shiftedQ h phase player := by
    intro h phase player
    exact hQ (h + start) phase player
  have hpositive' : ∀ h, 0 < totalHazard shiftedPeriod shiftedQ h := by
    intro h
    exact hpositive (h + start)
  have hseam' : Tendsto
      (fun h => ‖(fun player : I =>
        signedSeam shiftedPeriod shiftedP h player /
          totalHazard shiftedPeriod shiftedQ h)‖)
      atTop (nhds 0) := by
    change Tendsto (fun h => ‖(fun player : I =>
      signedSeam period p (h + start) player /
        totalHazard period q (h + start))‖) atTop (nhds 0)
    simpa [Function.comp_def] using hseam.comp (tendsto_add_atTop_nat start)
  have hlinear' : ∀ h, ‖(fun player : I =>
      signedSeam shiftedPeriod shiftedP h player /
        totalHazard shiftedPeriod shiftedQ h -
        matrixApply matrix (normalizedHazard shiftedPeriod shiftedQ h) player)‖ ≤
      error (h + start) := by
    intro h
    exact hstart (h + start) (by omega)
  obtain ⟨limit, subsequence, hsubsequence, hnonneg, hsum, hkernel, hconverges⟩ :=
    exists_normalizedHazard_subsequence_kernel_of_norm_seam shiftedPeriod shiftedQ
      shiftedP matrix hQ' hpositive' hseam' (fun h => error (h + start))
      (herror.comp (tendsto_add_atTop_nat start)) hlinear'
  refine ⟨limit, fun h => subsequence h + start, ?_, hnonneg, hsum, hkernel, ?_⟩
  · intro a b hab
    exact Nat.add_lt_add_right (hsubsequence hab) start
  · change Tendsto (fun h =>
      normalizedHazard period q (subsequence h + start)) atTop (nhds limit) at hconverges
    exact hconverges

theorem exists_normalizedHazard_subsequence_kernel_of_eventually_additive_norm_seam
    [Nonempty I]
    (period : ℕ → ℕ)
    (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (p : (h : ℕ) → Fin (period h) → I → ℝ)
    (matrix : I → I → ℝ)
    (hQ : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h)
    (hseam : Tendsto
      (fun h => ‖(fun player : I =>
        signedSeam period p h player / totalHazard period q h)‖)
      atTop (nhds 0))
    (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hlinear : ∀ᶠ h in atTop, ‖(fun player : I =>
      signedSeam period p h player / totalHazard period q h +
        matrixApply matrix (normalizedHazard period q h) player)‖ ≤ error h) :
    ∃ limit : I → ℝ, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
      (∀ player, 0 ≤ limit player) ∧
      (∑ player, limit player = 1) ∧
      (∀ player, matrixApply matrix limit player = 0) ∧
      Tendsto (normalizedHazard period q ∘ subsequence) atTop (nhds limit) := by
  let negMatrix : I → I → ℝ := fun player other => -matrix player other
  have hlinear' : ∀ᶠ h in atTop, ‖(fun player : I =>
      signedSeam period p h player / totalHazard period q h -
        matrixApply negMatrix (normalizedHazard period q h) player)‖ ≤ error h := by
    filter_upwards [hlinear] with h hh
    simpa [negMatrix, matrixApply, Finset.sum_neg_distrib] using hh
  obtain ⟨limit, subsequence, hsubsequence, hnonneg, hsum, hkernel, hconverges⟩ :=
    exists_normalizedHazard_subsequence_kernel_of_eventually_norm_seam period q p
      negMatrix hQ hpositive hseam error herror hlinear'
  refine ⟨limit, subsequence, hsubsequence, hnonneg, hsum, ?_, hconverges⟩
  intro player
  have hk := hkernel player
  simpa [negMatrix, matrixApply, Finset.sum_neg_distrib] using hk

theorem exists_normalizedHazard_subsequence_kernel_of_additive_linearization
    [Nonempty I]
    (period : ℕ → ℕ)
    (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (p : (h : ℕ) → Fin (period h) → I → ℝ)
    (matrix : I → I → ℝ)
    (hQ : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h)
    (hseam : ∀ player, Tendsto
      (fun h => signedSeam period p h player / totalHazard period q h)
      atTop (nhds 0))
    (error : ℕ → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (hlinear : ∀ h player,
      |signedSeam period p h player / totalHazard period q h +
        matrixApply matrix (normalizedHazard period q h) player| ≤ error h) :
    ∃ limit : I → ℝ, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
      (∀ player, 0 ≤ limit player) ∧
      (∑ player, limit player = 1) ∧
      (∀ player, matrixApply matrix limit player = 0) ∧
      Tendsto (normalizedHazard period q ∘ subsequence) atTop (nhds limit) := by
  let negP : (h : ℕ) → Fin (period h) → I → ℝ := fun h phase player =>
    -p h phase player
  have hseam_neg : ∀ player, Tendsto
      (fun h => signedSeam period negP h player / totalHazard period q h)
      atTop (nhds 0) := by
    intro player
    have hneg := (hseam player).neg
    simpa only [signedSeam, negP, Finset.sum_neg_distrib, neg_div, neg_zero] using hneg
  have hlinear_neg : ∀ h player,
      |signedSeam period negP h player / totalHazard period q h -
        matrixApply matrix (normalizedHazard period q h) player| ≤ error h := by
    intro h player
    have hbound := hlinear h player
    rw [show signedSeam period negP h player /
        totalHazard period q h - matrixApply matrix
          (normalizedHazard period q h) player =
        -(signedSeam period p h player / totalHazard period q h +
          matrixApply matrix (normalizedHazard period q h) player) by
      simp only [signedSeam, negP, Finset.sum_neg_distrib, neg_div]
      ring]
    rw [abs_neg]
    exact hbound
  exact exists_normalizedHazard_subsequence_kernel period q negP matrix hQ hpositive
    hseam_neg error herror hlinear_neg

theorem exists_normalizedHazard_subsequence_kernel_of_vanishing_mesh_anchor
    [Nonempty I]
    (period : ℕ → ℕ)
    (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (p : (h : ℕ) → Fin (period h) → I → ℝ)
    (matrix : I → I → ℝ)
    (mesh anchorError : ℕ → ℝ) (constant : ℝ)
    (hQ : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hanchor : Tendsto anchorError atTop (nhds 0))
    (hseam : ∀ player, Tendsto
      (fun h => signedSeam period p h player / totalHazard period q h)
      atTop (nhds 0))
    (hlinear : ∀ h player,
      |signedSeam period p h player / totalHazard period q h -
        matrixApply matrix (normalizedHazard period q h) player| ≤
          constant * (mesh h + anchorError h)) :
    ∃ limit : I → ℝ, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
      (∀ player, 0 ≤ limit player) ∧
      (∑ player, limit player = 1) ∧
      (∀ player, matrixApply matrix limit player = 0) ∧
      Tendsto (normalizedHazard period q ∘ subsequence) atTop (nhds limit) := by
  have herror : Tendsto (fun h => constant * (mesh h + anchorError h))
      atTop (nhds 0) := by
    simpa using (hmesh.add hanchor).const_mul constant
  exact exists_normalizedHazard_subsequence_kernel period q p matrix hQ hpositive hseam
    (fun h => constant * (mesh h + anchorError h)) herror hlinear

theorem exists_normalizedHazard_subsequence_kernel_of_vanishing_mesh_anchor_norm
    [Nonempty I]
    (period : ℕ → ℕ)
    (q : (h : ℕ) → Fin (period h) → I → ℝ)
    (p : (h : ℕ) → Fin (period h) → I → ℝ)
    (matrix : I → I → ℝ)
    (mesh anchorError : ℕ → ℝ) (constant : ℝ)
    (hQ : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hanchor : Tendsto anchorError atTop (nhds 0))
    (hseam : Tendsto
      (fun h => ‖(fun player : I =>
        signedSeam period p h player / totalHazard period q h)‖)
      atTop (nhds 0))
    (hlinear : ∀ h,
      ‖(fun player : I => signedSeam period p h player /
        totalHazard period q h -
        matrixApply matrix (normalizedHazard period q h) player)‖ ≤
        constant * (mesh h + anchorError h)) :
    ∃ limit : I → ℝ, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
      (∀ player, 0 ≤ limit player) ∧
      (∑ player, limit player = 1) ∧
      (∀ player, matrixApply matrix limit player = 0) ∧
      Tendsto (normalizedHazard period q ∘ subsequence) atTop (nhds limit) := by
  have herror : Tendsto (fun h => constant * (mesh h + anchorError h))
      atTop (nhds 0) := by
    simpa using (hmesh.add hanchor).const_mul constant
  exact exists_normalizedHazard_subsequence_kernel_of_norm_seam period q p matrix hQ
    hpositive hseam (fun h => constant * (mesh h + anchorError h)) herror hlinear

end

end MathUE.LocalPeriodicAnchor
