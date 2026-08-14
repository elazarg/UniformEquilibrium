import Mathlib

/-!
# Potentials as collateral: minimum escrow equals maximal prefix drawdown

This is the pathwise algebra behind `ideas/wild/DynamicSignalProcessing.md` §10
("Potentials as collateral"), upgrading the exhaustive finite check `E12`
(`experiments/collateral_account.py`) to a proved statement.

For a real increment stream `d : ℕ → ℝ` and horizon `N`, `drawdown d N` is the
maximal prefix loss `sup_{n ≤ N} (-(prefixSum d n))`.  The main identity is a
pathwise collateral principle:

* `drawdown d N` is exactly the least initial balance `e` for which every
  prefix balance `e + prefixSum d n` (`n ≤ N`) stays nonnegative
  (`add_prefixSum_nonneg`, `drawdown_le_of_feasible`, `drawdown_eq_sInf`).
* When the increments are the differences of a potential,
  `d i = Φ (i + 1) - Φ i`, the required escrow is bounded by the potential's
  oscillation on `range (N + 1)` (`drawdown_le_oscillation`), and this bound
  is attained whenever `Φ` is antitone on that range
  (`drawdown_eq_oscillation_of_antitone`).

**Nonclaims.**  Everything here is pathwise, deterministic algebra: the
escrow keeps *every* prefix of *this one* increment path solvent.  Nothing
here is a probabilistic or expected-drift statement; turning an
expected-drift potential into a solvency guarantee needs probabilistic
collateral, default, or high-probability rules (E12's own stated
limitation).  There is no game content: `d` and `Φ` are bare real sequences,
not payoffs, strategies, or equilibrium objects.
-/

noncomputable section

namespace Experiments.EscrowDrawdown

open scoped BigOperators

/-- The prefix sum of the increment stream `d` up to (excluding) index `n`. -/
def prefixSum (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, d i

/-- The maximal prefix drawdown of `d` over the horizon `[0, N]`: the largest
loss `-(prefixSum d n)` witnessed by any prefix `n ≤ N`.  Since `n = 0`
contributes `-(prefixSum d 0) = 0`, this is automatically nonnegative. -/
def drawdown (d : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun n => -(prefixSum d n))

@[simp]
theorem prefixSum_zero (d : ℕ → ℝ) : prefixSum d 0 = 0 := by
  simp [prefixSum]

theorem prefixSum_succ (d : ℕ → ℝ) (n : ℕ) :
    prefixSum d (n + 1) = prefixSum d n + d n := by
  simp [prefixSum, Finset.sum_range_succ]

/-- The drawdown is always nonnegative: the empty prefix `n = 0` never loses
money, so it alone forces `drawdown d N ≥ 0`. -/
theorem drawdown_nonneg (d : ℕ → ℝ) (N : ℕ) : 0 ≤ drawdown d N := by
  have h0 : (0 : ℝ) = -(prefixSum d 0) := by simp
  rw [h0]
  exact Finset.le_sup' (fun n => -(prefixSum d n))
    (Finset.mem_range.mpr (Nat.succ_pos N))

/-- Feasibility: starting from escrow `drawdown d N`, every prefix balance up
to the horizon stays nonnegative. -/
theorem add_prefixSum_nonneg (d : ℕ → ℝ) (N : ℕ) {n : ℕ} (hn : n ≤ N) :
    0 ≤ drawdown d N + prefixSum d n := by
  have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  have hle : -(prefixSum d n) ≤ drawdown d N :=
    Finset.le_sup' (fun m => -(prefixSum d m)) hmem
  linarith

/-- Minimality: any escrow `e` that keeps every prefix balance nonnegative
must be at least the drawdown. -/
theorem drawdown_le_of_feasible (d : ℕ → ℝ) (N : ℕ) (e : ℝ)
    (he : ∀ n ≤ N, 0 ≤ e + prefixSum d n) :
    drawdown d N ≤ e := by
  apply Finset.sup'_le
  intro n hn
  have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have := he n hn'
  linarith

/-- Characterization: the drawdown is exactly the infimum of feasible
escrows, i.e. the least nonnegative initial balance keeping every prefix up
to `N` solvent. -/
theorem drawdown_eq_sInf (d : ℕ → ℝ) (N : ℕ) :
    drawdown d N = sInf {e : ℝ | 0 ≤ e ∧ ∀ n ≤ N, 0 ≤ e + prefixSum d n} := by
  apply le_antisymm
  · apply le_csInf
    · exact ⟨drawdown d N, drawdown_nonneg d N, fun n hn => add_prefixSum_nonneg d N hn⟩
    · rintro e ⟨-, he⟩
      exact drawdown_le_of_feasible d N e he
  · apply csInf_le
    · exact ⟨0, fun e he => he.1⟩
    · exact ⟨drawdown_nonneg d N, fun n hn => add_prefixSum_nonneg d N hn⟩

/-- If `d` telescopes a potential `Φ`, its prefix sum is the potential's net
change from time `0`. -/
theorem prefixSum_eq_sub (d Φ : ℕ → ℝ) (hd : ∀ i, d i = Φ (i + 1) - Φ i) (n : ℕ) :
    prefixSum d n = Φ n - Φ 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [prefixSum_succ, ih, hd n]; ring

/-- First half of the oscillation bound: the escrow needed never exceeds the
potential's drop from its starting value to its lowest value on the horizon. -/
theorem drawdown_le_sub_inf' (d Φ : ℕ → ℝ) (N : ℕ) (hd : ∀ i, d i = Φ (i + 1) - Φ i) :
    drawdown d N ≤ Φ 0 - (Finset.range (N + 1)).inf' Finset.nonempty_range_add_one Φ := by
  apply Finset.sup'_le
  intro n hn
  rw [prefixSum_eq_sub d Φ hd n]
  have hinf : (Finset.range (N + 1)).inf' Finset.nonempty_range_add_one Φ ≤ Φ n :=
    Finset.inf'_le Φ hn
  linarith

/-- Potential-oscillation bound: if the increments are potential
differences, the drawdown (hence the minimum escrow) is bounded by the
potential's oscillation over the horizon. -/
theorem drawdown_le_oscillation (d Φ : ℕ → ℝ) (N : ℕ) (hd : ∀ i, d i = Φ (i + 1) - Φ i) :
    drawdown d N ≤
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one Φ -
        (Finset.range (N + 1)).inf' Finset.nonempty_range_add_one Φ := by
  have h1 := drawdown_le_sub_inf' d Φ N hd
  have h2 : Φ 0 ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one Φ :=
    Finset.le_sup' Φ (Finset.mem_range.mpr (Nat.succ_pos N))
  linarith

/-- Sharpness witness: when `Φ` is antitone on `[0, N]`, the oscillation
bound of `drawdown_le_oscillation` is attained exactly.  A decreasing
potential (e.g. a linear one, matching the sharp numeric example in E12) has
no slack: the worst prefix is the last one, and the drawdown equals the
full drop `Φ 0 - Φ N`, which is the potential's oscillation on the range. -/
theorem drawdown_eq_oscillation_of_antitone (d Φ : ℕ → ℝ) (N : ℕ)
    (hd : ∀ i, d i = Φ (i + 1) - Φ i) (hΦ : AntitoneOn Φ (Set.Iic N)) :
    drawdown d N =
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one Φ -
        (Finset.range (N + 1)).inf' Finset.nonempty_range_add_one Φ := by
  have hsup : (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one Φ = Φ 0 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro n hn
      have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      exact hΦ (Set.mem_Iic.mpr (Nat.zero_le N)) (Set.mem_Iic.mpr hn') (Nat.zero_le n)
    · exact Finset.le_sup' Φ (Finset.mem_range.mpr (Nat.succ_pos N))
  have hinf : (Finset.range (N + 1)).inf' Finset.nonempty_range_add_one Φ = Φ N := by
    apply le_antisymm
    · exact Finset.inf'_le Φ (Finset.mem_range.mpr (Nat.lt_succ_self N))
    · apply Finset.le_inf'
      intro n hn
      have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      exact hΦ (Set.mem_Iic.mpr hn') (Set.mem_Iic.mpr le_rfl) hn'
  rw [hsup, hinf]
  apply le_antisymm
  · apply Finset.sup'_le
    intro n hn
    have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [prefixSum_eq_sub d Φ hd n]
    have : Φ N ≤ Φ n := hΦ (Set.mem_Iic.mpr hn') (Set.mem_Iic.mpr le_rfl) hn'
    linarith
  · have hmem : N ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_self N)
    have hle : -(prefixSum d N) ≤ drawdown d N :=
      Finset.le_sup' (fun m => -(prefixSum d m)) hmem
    rw [prefixSum_eq_sub d Φ hd N] at hle
    linarith

end Experiments.EscrowDrawdown
