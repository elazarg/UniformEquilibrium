import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Banach limits on bounded real sequences

This file records the algebraic and convexity properties of an abstract Banach
limit. The functional is total, but its axioms are required only on bounded
sequences.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace MathUE

/-- A real sequence is bounded in absolute value. -/
def IsBoundedSequence (sequence : ℕ → ℝ) : Prop :=
  ∃ bound : ℝ, ∀ n, |sequence n| ≤ bound

namespace IsBoundedSequence

theorem const (c : ℝ) : IsBoundedSequence (fun _ : ℕ ↦ c) := by
  exact ⟨|c|, fun _ ↦ le_rfl⟩

theorem add {f g : ℕ → ℝ}
    (hf : IsBoundedSequence f) (hg : IsBoundedSequence g) :
    IsBoundedSequence (fun n ↦ f n + g n) := by
  obtain ⟨boundF, hboundF⟩ := hf
  obtain ⟨boundG, hboundG⟩ := hg
  refine ⟨boundF + boundG, fun n ↦ ?_⟩
  exact (abs_add_le (f n) (g n)).trans (add_le_add (hboundF n) (hboundG n))

theorem neg {f : ℕ → ℝ} (hf : IsBoundedSequence f) :
    IsBoundedSequence (fun n ↦ -f n) := by
  obtain ⟨bound, hbound⟩ := hf
  exact ⟨bound, fun n ↦ by simpa using hbound n⟩

theorem sub {f g : ℕ → ℝ}
    (hf : IsBoundedSequence f) (hg : IsBoundedSequence g) :
    IsBoundedSequence (fun n ↦ f n - g n) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem smul (c : ℝ) {f : ℕ → ℝ} (hf : IsBoundedSequence f) :
    IsBoundedSequence (fun n ↦ c * f n) := by
  obtain ⟨bound, hbound⟩ := hf
  refine ⟨|c| * bound, fun n ↦ ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hbound n) (abs_nonneg c)

theorem finset_sum {K : Type} {s : Finset K} {f : K → ℕ → ℝ}
    (hf : ∀ k ∈ s, IsBoundedSequence (f k)) :
    IsBoundedSequence (fun n ↦ ∑ k ∈ s, f k n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | @insert k s hk ih =>
      simp only [Finset.sum_insert hk]
      exact (hf k (Finset.mem_insert_self k s)).add
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

theorem of_tendsto {f : ℕ → ℝ} {x : ℝ}
    (hf : Tendsto f atTop (nhds x)) : IsBoundedSequence f := by
  have hrange : Bornology.IsBounded (Set.range f) :=
    Metric.isBounded_range_of_tendsto f hf
  obtain ⟨bound, hbound⟩ :=
    (Metric.isBounded_iff_subset_closedBall 0).mp hrange
  refine ⟨bound, fun n ↦ ?_⟩
  simpa [Real.dist_eq] using hbound ⟨n, rfl⟩

end IsBoundedSequence

/-- A positive, normalized, shift-invariant extension of the ordinary limit
from convergent sequences to bounded real sequences. -/
structure BanachLimit where
  eval : (ℕ → ℝ) → ℝ
  map_add : ∀ f g, IsBoundedSequence f → IsBoundedSequence g →
    eval (fun n ↦ f n + g n) = eval f + eval g
  map_smul : ∀ c f, IsBoundedSequence f →
    eval (fun n ↦ c * f n) = c * eval f
  positive : ∀ f, IsBoundedSequence f → (∀ n, 0 ≤ f n) → 0 ≤ eval f
  constant : ∀ c, eval (fun _ ↦ c) = c
  shift : ∀ f, IsBoundedSequence f → eval (fun n ↦ f (n + 1)) = eval f
  agreesWithLimit : ∀ f x, IsBoundedSequence f →
    Tendsto f atTop (nhds x) → eval f = x

namespace BanachLimit

@[simp] theorem eval_zero (L : BanachLimit) :
    L.eval (fun _ : ℕ ↦ 0) = 0 :=
  L.constant 0

theorem eval_neg (L : BanachLimit) {f : ℕ → ℝ}
    (hf : IsBoundedSequence f) : L.eval (fun n ↦ -f n) = -L.eval f := by
  simpa using L.map_smul (-1) f hf

theorem eval_sub (L : BanachLimit) {f g : ℕ → ℝ}
    (hf : IsBoundedSequence f) (hg : IsBoundedSequence g) :
    L.eval (fun n ↦ f n - g n) = L.eval f - L.eval g := by
  rw [show (fun n ↦ f n - g n) = fun n ↦ f n + -g n by
    funext n
    ring]
  rw [L.map_add f (fun n ↦ -g n) hf hg.neg, L.eval_neg hg]
  ring

theorem eval_mono (L : BanachLimit) {f g : ℕ → ℝ}
    (hf : IsBoundedSequence f) (hg : IsBoundedSequence g)
    (hle : ∀ n, f n ≤ g n) : L.eval f ≤ L.eval g := by
  have hpositive := L.positive (fun n ↦ g n - f n) (hg.sub hf)
    (fun n ↦ sub_nonneg.mpr (hle n))
  rw [L.eval_sub hg hf] at hpositive
  linarith

/-- A Banach limit is at most `c` when the bounded sequence is eventually
below `c + ε` for every positive `ε`. -/
theorem eval_le_of_eventually_le_add (L : BanachLimit) {f : ℕ → ℝ}
    (hf : IsBoundedSequence f) {c : ℝ}
    (hupper : ∀ ε, 0 < ε → ∀ᶠ n in atTop, f n ≤ c + ε) :
    L.eval f ≤ c := by
  let envelope : ℕ → ℝ := fun n ↦ max (f n) c
  have henvelope : Tendsto envelope atTop (nhds c) := by
    apply tendsto_order.2
    constructor
    · intro lower hlower
      filter_upwards [] with n
      exact hlower.trans_le (le_max_right (f n) c)
    · intro upper hupperc
      let ε := (upper - c) / 2
      have hε : 0 < ε := by dsimp only [ε]; linarith
      filter_upwards [hupper ε hε] with n hn
      apply max_lt
      · exact hn.trans_lt (by dsimp only [ε]; linarith)
      · exact hupperc
  have hboundedEnvelope : IsBoundedSequence envelope :=
    IsBoundedSequence.of_tendsto henvelope
  calc
    L.eval f ≤ L.eval envelope :=
      L.eval_mono hf hboundedEnvelope (fun n ↦ le_max_left _ _)
    _ = c := L.agreesWithLimit envelope c hboundedEnvelope henvelope

theorem eval_finset_sum (L : BanachLimit) {K : Type} (s : Finset K)
    (f : K → ℕ → ℝ) (hbounded : ∀ k ∈ s, IsBoundedSequence (f k)) :
    L.eval (fun n ↦ ∑ k ∈ s, f k n) = ∑ k ∈ s, L.eval (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      simp only [Finset.sum_insert hk]
      rw [L.map_add (f k) (fun n ↦ ∑ j ∈ s, f j n)
        (hbounded k (Finset.mem_insert_self k s))
        (IsBoundedSequence.finset_sum fun j hj ↦
          hbounded j (Finset.mem_insert_of_mem hj))]
      rw [ih fun j hj ↦ hbounded j (Finset.mem_insert_of_mem hj)]

/-- Coordinatewise evaluation by a Banach limit. -/
def evalPi {I : Type} (L : BanachLimit) (sequence : ℕ → I → ℝ) : I → ℝ :=
  fun i ↦ L.eval (fun n ↦ sequence n i)

/-- Coordinatewise Banach evaluation agrees with an ordinary limit. -/
theorem evalPi_eq_of_tendsto {I : Type} (L : BanachLimit)
    {sequence : ℕ → I → ℝ} {x : I → ℝ}
    (hsequence : Tendsto sequence atTop (nhds x)) :
    L.evalPi sequence = x := by
  funext i
  apply L.agreesWithLimit
  · exact IsBoundedSequence.of_tendsto (hsequence.apply_nhds i)
  · exact hsequence.apply_nhds i

/-- Coordinatewise Banach evaluation preserves a finite convex hull. -/
theorem evalPi_mem_convexHull_range {K I : Type} [Fintype K]
    [DecidableEq K] [Nonempty K] (L : BanachLimit) (point : K → I → ℝ)
    (sequence : ℕ → I → ℝ)
    (hsequence : ∀ n, sequence n ∈ convexHull ℝ (Set.range point)) :
    L.evalPi sequence ∈ convexHull ℝ (Set.range point) := by
  classical
  have hexists (n : ℕ) :
      ∃ weight : K → ℝ, (∀ k, 0 ≤ weight k) ∧
        ∑ k, weight k = 1 ∧ ∑ k, weight k • point k = sequence n := by
    rw [convexHull_range_eq_exists_affineCombination] at hsequence
    rcases hsequence n with ⟨support, weight₀, hweight₀0, hweight₀sum, hweighted⟩
    let weight : K → ℝ := fun k ↦ if k ∈ support then weight₀ k else 0
    refine ⟨weight, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k ∈ support
      · simpa [weight, hk] using hweight₀0 k hk
      · simp [weight, hk]
    · simpa [weight] using hweight₀sum
    · rw [← hweighted,
        support.affineCombination_eq_linear_combination point weight₀ hweight₀sum]
      simp [weight]
  choose weight hweight0 hweightSum hweighted using hexists
  have hweightLeOne (n : ℕ) (k : K) : weight n k ≤ 1 := by
    rw [← hweightSum n]
    exact Finset.single_le_sum (fun j _hj ↦ hweight0 n j) (Finset.mem_univ k)
  have hweightBounded (k : K) :
      IsBoundedSequence (fun n ↦ weight n k) := by
    refine ⟨1, fun n ↦ ?_⟩
    rw [abs_of_nonneg (hweight0 n k)]
    exact hweightLeOne n k
  let limitWeight : K → ℝ := fun k ↦ L.eval (fun n ↦ weight n k)
  have hlimitWeight0 (k : K) : 0 ≤ limitWeight k := by
    exact L.positive (fun n ↦ weight n k) (hweightBounded k)
      (fun n ↦ hweight0 n k)
  have hlimitWeightSum : ∑ k, limitWeight k = 1 := by
    calc
      ∑ k, limitWeight k = L.eval (fun n ↦ ∑ k, weight n k) := by
        rw [L.eval_finset_sum Finset.univ (fun k n ↦ weight n k)
          (fun k _hk ↦ hweightBounded k)]
      _ = L.eval (fun _ : ℕ ↦ 1) := by
        congr 1
        funext n
        exact hweightSum n
      _ = 1 := L.constant 1
  apply mem_convexHull_of_exists_fintype (s := Set.range point)
    limitWeight point hlimitWeight0 hlimitWeightSum (fun k ↦ ⟨k, rfl⟩)
  funext i
  unfold evalPi
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ k, limitWeight k * point k i) = L.eval (fun n ↦ sequence n i)
  have hscalar (k : K) :
      limitWeight k * point k i =
        L.eval (fun n ↦ weight n k * point k i) := by
    calc
      limitWeight k * point k i = point k i * L.eval (fun n ↦ weight n k) := by
        rw [mul_comm]
      _ = L.eval (fun n ↦ point k i * weight n k) :=
        (L.map_smul (point k i) (fun n ↦ weight n k) (hweightBounded k)).symm
      _ = L.eval (fun n ↦ weight n k * point k i) := by
        congr 1
        funext n
        rw [mul_comm]
  simp_rw [hscalar]
  calc
    ∑ k, L.eval (fun n ↦ weight n k * point k i) =
        L.eval (fun n ↦ ∑ k, weight n k * point k i) := by
      symm
      simpa only [Finset.sum_const_zero, Finset.sum_filter] using
        L.eval_finset_sum Finset.univ
          (fun k n ↦ weight n k * point k i)
          (fun k _hk ↦ by
            simpa only [mul_comm] using
              (hweightBounded k).smul (point k i))
    _ = L.eval (fun n ↦ sequence n i) := by
      congr 1
      funext n
      have hn := congrFun (hweighted n) i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hn

end BanachLimit

end MathUE
