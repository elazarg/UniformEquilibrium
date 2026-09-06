import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Instances.Real.Lemmas
import MathUE.AffineRecurrenceFiniteUnroll

/-! # Infinite unrolling of a summable scalar affine recurrence -/

noncomputable section
namespace Math

open Filter Finset
open scoped Topology

/-- The tail product is the infimum of its finite chronological products. -/
def affineProductTail (a : ℕ → ℝ) (start : ℕ) : ℝ :=
  sInf (Set.range fun horizon => ∏ offset ∈ range horizon, a (start + offset))

/-- Finite tail products converge to their literal infimum when all factors
lie in the unit interval. -/
theorem tendsto_affineProductTail
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (start : ℕ) :
    Tendsto (fun horizon => ∏ offset ∈ range horizon, a (start + offset))
      atTop (nhds (affineProductTail a start)) := by
  have hanti : Antitone (fun horizon =>
      ∏ offset ∈ range horizon, a (start + offset)) := by
    apply antitone_nat_of_succ_le
    intro horizon
    rw [prod_range_succ]
    have hprod : 0 ≤ ∏ offset ∈ range horizon,
        a (start + offset) := prod_nonneg fun offset _ => ha0 _
    exact mul_le_of_le_one_right hprod (ha1 (start + horizon))
  simpa [affineProductTail, sInf_range] using
    tendsto_atTop_ciInf hanti
      ⟨0, fun value hvalue => by
        obtain ⟨horizon, rfl⟩ := hvalue
        exact prod_nonneg fun offset _ => ha0 _⟩

/-- The finite weighted charge sums converge to the series weighted by the
corresponding infinite tail products. -/
theorem tendsto_affineWeightedChargeSum
    (a b : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (hb : Summable fun n => |b n|) :
    Tendsto (fun horizon => ∑ k ∈ range horizon,
        (∏ i ∈ Ico (k + 1) horizon, a i) * b k) atTop
      (nhds (∑' k, affineProductTail a (k + 1) * b k)) := by
  let finiteWeight : ℕ → ℕ → ℝ := fun horizon k =>
    if k < horizon then (∏ i ∈ Ico (k + 1) horizon, a i) * b k else 0
  have hpoint : ∀ k, Tendsto (fun horizon => finiteWeight horizon k) atTop
      (nhds (affineProductTail a (k + 1) * b k)) := by
    intro k
    have hprod := (tendsto_affineProductTail a ha0 ha1 (k + 1)).mul_const (b k)
    have hprod' := hprod.comp (Filter.tendsto_sub_atTop_nat (k + 1))
    apply Tendsto.congr' _ hprod'
    filter_upwards [eventually_ge_atTop (k + 1)] with horizon hhorizon
    have hk : k < horizon := by omega
    dsimp only [finiteWeight]
    rw [if_pos hk, prod_Ico_eq_prod_range]
    rfl
  have hbound : ∀ horizon k, ‖finiteWeight horizon k‖ ≤ |b k| := by
    intro horizon k
    by_cases hk : k < horizon
    · dsimp only [finiteWeight]
      rw [if_pos hk, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (prod_nonneg fun i _ => ha0 _)]
      have hp : (∏ i ∈ Ico (k + 1) horizon, a i) ≤ 1 :=
        prod_le_one (fun i _ => ha0 i) (fun i _ => ha1 i)
      exact mul_le_of_le_one_left (abs_nonneg (b k)) hp
    · simp only [finiteWeight, if_neg hk, norm_zero, abs_nonneg]
  have htendsto := tendsto_tsum_of_dominated_convergence hb hpoint
    (Eventually.of_forall hbound)
  convert htendsto using 1
  funext horizon
  rw [tsum_eq_sum' (s := range horizon)]
  · apply sum_congr rfl
    intro k hk
    simp only [finiteWeight, mem_range.mp hk, if_true]
  · intro k hk
    by_contra hnot
    have hnotLt : ¬ k < horizon := fun hlt => hnot (mem_range.mpr hlt)
    have hzero : finiteWeight horizon k = 0 := by
      simp only [finiteWeight, if_neg hnotLt]
    exact hk hzero

/-- A convergent affine recurrence equals its initial infinite product term
plus the absolutely convergent series of tail-product-weighted charges. -/
theorem affineRecurrence_limit_eq_productTail_add_tsum
    (x a b : ℕ → ℝ) (limit : ℝ)
    (hstep : ∀ n, x (n + 1) = a n * x n + b n)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (hb : Summable fun n => |b n|)
    (hx : Tendsto x atTop (nhds limit)) :
    limit = affineProductTail a 0 * x 0 +
      ∑' n, affineProductTail a (n + 1) * b n := by
  have hunroll : ∀ n, x n =
      (∏ i ∈ Ico 0 n, a i) * x 0 +
        ∑ k ∈ Ico 0 n, (∏ i ∈ Ico (k + 1) n, a i) * b k :=
    fun n => affineRecurrence_eq_prod_add_sum_prod x a b 0
      (fun n _ => hstep n) n.zero_le
  have hproduct := (tendsto_affineProductTail a ha0 ha1 0).mul_const (x 0)
  have hsum := tendsto_affineWeightedChargeSum a b ha0 ha1 hb
  have hright := hproduct.add hsum
  have heq : x = fun n =>
      (∏ i ∈ range n, a i) * x 0 +
        ∑ k ∈ range n, (∏ i ∈ Ico (k + 1) n, a i) * b k := by
    funext n
    simpa using hunroll n
  rw [heq] at hx
  exact tendsto_nhds_unique hx (by simpa only [zero_add] using hright)

end Math
