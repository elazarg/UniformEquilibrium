import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Caristi's fixed-point theorem

A lower-semicontinuous potential on a complete metric space has a fixed point
for every self-map whose displacement is paid for by the potential decrease.
-/

namespace MathUE

open Filter Set
open scoped Topology

noncomputable section

/-- **Caristi's fixed-point theorem.** If `φ` is lower semicontinuous and
bounded below, and `dist x (f x) ≤ φ x - φ (f x)`, then `f` has a fixed
point. -/
theorem exists_fixedPoint_of_caristi
    {X : Type*} [MetricSpace X] [Nonempty X] [CompleteSpace X]
    (f : X → X) (φ : X → ℝ) (hφ : LowerSemicontinuous φ)
    (hbound : BddBelow (Set.range φ))
    (hcaristi : ∀ x, dist x (f x) ≤ φ x - φ (f x)) :
    ∃ x, f x = x := by
  let R (x y : X) : Prop := dist x y ≤ φ x - φ y
  have hR_refl (x : X) : R x x := by
    simp [R]
  have hR_trans {x y z : X} (hxy : R x y) (hyz : R y z) : R x z := by
    dsimp [R] at hxy hyz ⊢
    calc
      dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ ≤ (φ x - φ y) + (φ y - φ z) := add_le_add hxy hyz
      _ = φ x - φ z := by ring
  have hR_phi {x y : X} (hxy : R x y) : φ y ≤ φ x := by
    dsimp [R] at hxy
    linarith [show 0 ≤ dist x y from dist_nonneg]
  have hstep (n : ℕ) (x : X) : ∃ y, R x y ∧
      φ y < sInf (φ '' {z | R x z}) + (n + 1 : ℝ)⁻¹ := by
    have himage_nonempty : (φ '' {z | R x z}).Nonempty :=
      ⟨φ x, ⟨x, hR_refl x, rfl⟩⟩
    have himage_bdd : BddBelow (φ '' {z | R x z}) :=
      hbound.mono (Set.image_subset_range φ _)
    have hpos : 0 < (n + 1 : ℝ)⁻¹ := inv_pos.mpr (by positivity)
    obtain ⟨value, hvalue, hvalue_lt⟩ := exists_lt_of_csInf_lt himage_nonempty
      (lt_add_of_pos_right _ hpos)
    obtain ⟨y, hyR, rfl⟩ := hvalue
    exact ⟨y, hyR, hvalue_lt⟩
  let next (n : ℕ) (x : X) : X := Classical.choose (hstep n x)
  have next_R (n : ℕ) (x : X) : R x (next n x) :=
    (Classical.choose_spec (hstep n x)).1
  have next_approx (n : ℕ) (x : X) :
      φ (next n x) < sInf (φ '' {z | R x z}) + (n + 1 : ℝ)⁻¹ :=
    (Classical.choose_spec (hstep n x)).2
  let x' : ℕ → X :=
    Nat.rec (Classical.arbitrary X) (fun n current => next n current)
  have x'_succ (n : ℕ) : x' (n + 1) = next n (x' n) := by
    simp [x']
  have hR_succ (n : ℕ) : R (x' n) (x' (n + 1)) := by
    rw [x'_succ]
    exact next_R n (x' n)
  have hR_le {n m : ℕ} (hnm : n ≤ m) : R (x' n) (x' m) := by
    induction m, hnm using Nat.le_induction with
    | base => exact hR_refl _
    | succ m hnm ih => exact hR_trans ih (hR_succ m)
  have hanti : Antitone (φ ∘ x') := by
    intro n m hnm
    exact hR_phi (hR_le hnm)
  have hbdd : BddBelow (Set.range (φ ∘ x')) := by
    exact hbound.mono (Set.range_comp_subset_range x' φ)
  let L := sInf (Set.range (φ ∘ x'))
  have htendsto : Tendsto (φ ∘ x') atTop (nhds L) :=
    tendsto_atTop_ciInf hanti hbdd
  have hdiff : Tendsto (fun n => φ (x' n) - L) atTop (nhds 0) := by
    simpa only [Function.comp_apply, sub_self] using htendsto.sub_const L
  have hcauchy : CauchySeq x' := by
    apply cauchySeq_of_le_tendsto_0' (fun n => φ (x' n) - L)
    · intro n m hnm
      have hrel := hR_le hnm
      dsimp [R] at hrel
      have hLm : L ≤ φ (x' m) := csInf_le hbdd ⟨m, rfl⟩
      linarith
    · exact hdiff
  obtain ⟨limit, hlimit⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hφlimit : φ limit ≤ L := by
    by_contra hnot
    have hLlt : L < φ limit := lt_of_not_ge hnot
    let middle := (L + φ limit) / 2
    have hmiddleLimit : middle < φ limit := by
      dsimp [middle]
      linarith
    have heventLower : ∀ᶠ n in atTop, middle < φ (x' n) :=
      hlimit.eventually (hφ.lowerSemicontinuousAt limit middle hmiddleLimit)
    have heventUpper : ∀ᶠ n in atTop, φ (x' n) < middle := by
      have hLmiddle : L < middle := by
        dsimp [middle]
        linarith
      exact htendsto.eventually (gt_mem_nhds hLmiddle)
    obtain ⟨n, hlowerMiddle, hupperMiddle⟩ :=
      (heventLower.and heventUpper).exists
    exact (not_lt_of_ge (le_of_lt hlowerMiddle)) hupperMiddle
  have hR_limit (n : ℕ) : R (x' n) limit := by
    have hdist_tendsto : Tendsto (fun m => dist (x' n) (x' m)) atTop
        (nhds (dist (x' n) limit)) := tendsto_const_nhds.dist hlimit
    have hrhs_tendsto : Tendsto (fun m => φ (x' n) - φ (x' m)) atTop
        (nhds (φ (x' n) - L)) := tendsto_const_nhds.sub htendsto
    have hsub_tendsto : Tendsto
        (fun m => dist (x' n) (x' m) - (φ (x' n) - φ (x' m))) atTop
        (nhds (dist (x' n) limit - (φ (x' n) - L))) :=
      hdist_tendsto.sub hrhs_tendsto
    have hsub_nonpos : dist (x' n) limit - (φ (x' n) - L) ≤ 0 := by
      apply le_of_tendsto hsub_tendsto
      exact Filter.eventually_atTop.2 ⟨n, fun m hnm => by
        linarith [hR_le hnm]⟩
    dsimp [R]
    linarith
  have hinv_tendsto :
      Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))
  have hshift_tendsto :
      Tendsto (fun n => φ (x' (n + 1))) atTop (nhds L) := by
    simpa [Function.comp_def, Nat.add_comm] using
      htendsto.comp (tendsto_add_atTop_nat 1)
  have hL_ge_limit : L ≤ φ limit := by
    have herror_tendsto : Tendsto
        (fun n => φ (x' (n + 1)) - (φ limit + (n + 1 : ℝ)⁻¹)) atTop
        (nhds (L - φ limit)) := by
      simpa only [add_zero] using
        hshift_tendsto.sub (tendsto_const_nhds.add hinv_tendsto)
    have hnonpos : L - φ limit ≤ 0 := by
      apply le_of_tendsto' herror_tendsto
      intro n
      have hnext := next_approx n (x' n)
      rw [← x'_succ n] at hnext
      have hinf_le : sInf (φ '' {z | R (x' n) z}) ≤ φ limit := by
        apply csInf_le
        · exact hbound.mono (Set.image_subset_range φ _)
        · exact ⟨limit, hR_limit n, rfl⟩
      linarith
    linarith
  have hφlimit_eq : φ limit = L := le_antisymm hφlimit hL_ge_limit
  have hmaximal {y : X} (hly : R limit y) : y = limit := by
    have hRny (n : ℕ) : R (x' n) y := hR_trans (hR_limit n) hly
    have herror_tendsto : Tendsto
        (fun n => φ (x' (n + 1)) - (φ y + (n + 1 : ℝ)⁻¹)) atTop
        (nhds (L - φ y)) := by
      simpa only [add_zero] using
        hshift_tendsto.sub (tendsto_const_nhds.add hinv_tendsto)
    have hLy : L ≤ φ y := by
      have hnonpos : L - φ y ≤ 0 := by
        apply le_of_tendsto' herror_tendsto
        intro n
        have hnext := next_approx n (x' n)
        rw [← x'_succ n] at hnext
        have hinf_le : sInf (φ '' {z | R (x' n) z}) ≤ φ y := by
          apply csInf_le
          · exact hbound.mono (Set.image_subset_range φ _)
          · exact ⟨y, hRny n, rfl⟩
        linarith
      linarith
    have hdist : dist limit y ≤ 0 := by
      dsimp [R] at hly
      rw [hφlimit_eq] at hly
      linarith
    exact (dist_eq_zero.mp (le_antisymm hdist dist_nonneg)).symm
  refine ⟨limit, ?_⟩
  exact hmaximal (hcaristi limit)

end

end MathUE
