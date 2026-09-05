import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Order.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Monotone nonexpansive interval iteration -/

open Filter Function Set
open scoped Topology

namespace Math

theorem monotone_iterate_zero_of_zero_le
    {Φ : ℝ → ℝ} (hmono : Monotone Φ) (hzero : 0 ≤ Φ 0) :
    Monotone (fun n : ℕ => Φ^[n] 0) :=
  hmono.monotone_iterate_of_le_map hzero

theorem antitone_iterate_zero_of_le_zero
    {Φ : ℝ → ℝ} (hmono : Monotone Φ) (hzero : Φ 0 ≤ 0) :
    Antitone (fun n : ℕ => Φ^[n] 0) :=
  hmono.antitone_iterate_of_map_le hzero

/-- Iteration from zero converges inside every preserved symmetric compact
interval, in either monotonicity direction, and its limit is fixed. -/
theorem exists_fixedPoint_tendsto_iterate_zero_of_monotone_nonexpansive
    (Φ : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hmono : Monotone Φ) (hlip : LipschitzWith 1 Φ)
    (hmap : MapsTo Φ (Icc (-M) M) (Icc (-M) M)) :
    ∃ ℓ ∈ Icc (-M) M,
      Tendsto (fun n : ℕ => Φ^[n] 0) atTop (𝓝 ℓ) ∧ Φ ℓ = ℓ := by
  have horbit : ∀ n : ℕ, Φ^[n] 0 ∈ Icc (-M) M := by
    intro n
    induction n with
    | zero => exact ⟨neg_nonpos.mpr hM, hM⟩
    | succ n ih =>
        rw [iterate_succ_apply']
        exact hmap ih
  by_cases hzero : 0 ≤ Φ 0
  · have hseq := monotone_iterate_zero_of_zero_le hmono hzero
    have hbdd : BddAbove (range fun n : ℕ => Φ^[n] 0) := by
      exact ⟨M, by rintro _ ⟨n, rfl⟩; exact (horbit n).2⟩
    let ℓ := ⨆ n : ℕ, Φ^[n] 0
    have htendsto : Tendsto (fun n : ℕ => Φ^[n] 0) atTop (𝓝 ℓ) :=
      tendsto_atTop_ciSup hseq hbdd
    have hℓmem : ℓ ∈ Icc (-M) M := by
      constructor
      · exact ge_of_tendsto' htendsto fun n => (horbit n).1
      · exact le_of_tendsto' htendsto fun n => (horbit n).2
    refine ⟨ℓ, hℓmem, htendsto, ?_⟩
    have hshift : Tendsto (fun n : ℕ => Φ^[n + 1] 0) atTop (𝓝 ℓ) :=
      htendsto.comp (tendsto_add_atTop_nat 1)
    have himage : Tendsto (fun n : ℕ => Φ (Φ^[n] 0)) atTop (𝓝 (Φ ℓ)) :=
      hlip.continuous.continuousAt.tendsto.comp htendsto
    exact tendsto_nhds_unique himage (by simpa [iterate_succ_apply'] using hshift)
  · have hzero' : Φ 0 ≤ 0 := le_of_not_ge hzero
    have hseq := antitone_iterate_zero_of_le_zero hmono hzero'
    have hbdd : BddBelow (range fun n : ℕ => Φ^[n] 0) := by
      exact ⟨-M, by rintro _ ⟨n, rfl⟩; exact (horbit n).1⟩
    let ℓ := ⨅ n : ℕ, Φ^[n] 0
    have htendsto : Tendsto (fun n : ℕ => Φ^[n] 0) atTop (𝓝 ℓ) :=
      tendsto_atTop_ciInf hseq hbdd
    have hℓmem : ℓ ∈ Icc (-M) M := by
      constructor
      · exact ge_of_tendsto' htendsto fun n => (horbit n).1
      · exact le_of_tendsto' htendsto fun n => (horbit n).2
    refine ⟨ℓ, hℓmem, htendsto, ?_⟩
    have hshift : Tendsto (fun n : ℕ => Φ^[n + 1] 0) atTop (𝓝 ℓ) :=
      htendsto.comp (tendsto_add_atTop_nat 1)
    have himage : Tendsto (fun n : ℕ => Φ (Φ^[n] 0)) atTop (𝓝 (Φ ℓ)) :=
      hlip.continuous.continuousAt.tendsto.comp htendsto
    exact tendsto_nhds_unique himage (by simpa [iterate_succ_apply'] using hshift)

theorem map_le_of_fixedPoint_lt_of_nonexpansive
    {Φ : ℝ → ℝ} {ℓ x : ℝ} (hlip : LipschitzWith 1 Φ)
    (hfixed : Φ ℓ = ℓ) (hlt : ℓ < x) : Φ x ≤ x := by
  have hdist := hlip.dist_le_mul ℓ x
  rw [Real.dist_eq, Real.dist_eq, hfixed] at hdist
  have hright : |ℓ - x| = x - ℓ := by
    rw [abs_of_neg (sub_neg.mpr hlt)]
    ring
  have hleft : Φ x - ℓ ≤ |ℓ - Φ x| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  rw [hright] at hdist
  norm_num at hdist
  linarith

theorem not_fixedPoint_lt_zero_above_iterateLimit
    {Φ : ℝ → ℝ} {ℓ x : ℝ} (hmono : Monotone Φ)
    (htendsto : Tendsto (fun n : ℕ => Φ^[n] 0) atTop (𝓝 ℓ))
    (hlt : ℓ < x) (hxneg : x < 0) : Φ x ≠ x := by
  intro hfixed
  have hxle : ∀ n : ℕ, x ≤ Φ^[n] 0 := by
    intro n
    have hiterate := hmono.iterate n hxneg.le
    have hfixedIterate : Φ^[n] x = x := Function.IsFixedPt.iterate hfixed n
    simpa [hfixedIterate] using hiterate
  have : x ≤ ℓ := ge_of_tendsto' htendsto hxle
  exact (not_le_of_gt hlt) this

end Math
