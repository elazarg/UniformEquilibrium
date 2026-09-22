import MathUE.LinearProgramming.ThreeCycleInverseFormulas
import MathUE.Probability.OneSidedDebtShadowing
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Rigidity of normalized absorbing singleton paths

These are game-independent recurrences, not supplied periodic certificates.
Only positive-hazard rows have an active-coordinate equality. Zero-hazard
gaps are unrestricted, and finite owner blocks are conclusions. The
identification with actual stopping-law continuation values is a separate
game-semantic adapter.
-/

noncomputable section

open Filter
open scoped Topology

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι]

/-- An exact nonnegative singleton recurrence on a weighted probability simplex,
with vanishing survival on every tail. No owner changes or vertex visits
are supplied as fields. -/
structure NormalizedSingletonPath (T : Matrix ι ι ℝ)
    (weight : ι → ℝ) where
  owner : ℕ → ι
  hazard : ℕ → ℝ
  value : ℕ → ι → ℝ
  weight_pos : ∀ i, 0 < weight i
  hazard_nonneg : ∀ time, 0 ≤ hazard time
  hazard_lt_one : ∀ time, hazard time < 1
  value_nonneg : ∀ time i, 0 ≤ value time i
  normalized : ∀ time, ∑ i, weight i * value time i = 1
  step : ∀ time i, value time i = hazard time * T i (owner time) +
    (1 - hazard time) * value (time + 1) i
  active_zero : ∀ time, 0 < hazard time → value time (owner time) = 0
  absorbs : ∀ start,
    Tendsto (survivalProduct (fun time => 1 - hazard time) start) atTop (nhds 0)

namespace NormalizedSingletonPath

variable {T : Matrix ι ι ℝ} {weight : ι → ℝ}

/-- Normalization bounds each nonnegative coordinate independently of time. -/
theorem value_le (path : NormalizedSingletonPath T weight) (time : ℕ) (i : ι) :
    path.value time i ≤ 1 / weight i := by
  classical
  have hterm : weight i * path.value time i ≤ 1 := by
    rw [← path.normalized time]
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg (path.weight_pos j).le (path.value_nonneg time j))
      (Finset.mem_univ i)
  apply (le_div_iff₀ (path.weight_pos i)).mpr
  simpa only [mul_comm] using hterm

/-- A zero-hazard row leaves every continuation coordinate unchanged. -/
theorem value_eq_next_of_hazard_zero (path : NormalizedSingletonPath T weight)
    (time : ℕ) (hzero : path.hazard time = 0) :
    path.value time = path.value (time + 1) := by
  funext i
  simpa only [hzero, zero_mul, sub_zero, one_mul, zero_add] using path.step time i

/-- A column with a negative coordinate cannot be the only positive-hazard
owner on any tail. Absorption removes the bounded residual continuation. -/
theorem exists_active_owner_ne (path : NormalizedSingletonPath T weight)
    (start : ℕ) (owner : ι) (hnegative : ∃ i, T i owner < 0) :
    ∃ time, start ≤ time ∧ 0 < path.hazard time ∧ path.owner time ≠ owner := by
  by_contra hnone
  have hmono : ∀ time, start ≤ time → 0 < path.hazard time → path.owner time = owner := by
    intro time htime hpositive
    by_contra hne
    exact hnone ⟨time, htime, hpositive, hne⟩
  obtain ⟨i, hi⟩ := hnegative
  let difference : ℕ → ℝ := fun time => path.value time i - T i owner
  have hrec : ∀ offset,
      difference (start + offset) = 0 +
        (1 - path.hazard (start + offset)) * difference (start + offset + 1) := by
    intro offset
    have hstep := path.step (start + offset) i
    by_cases hzero : path.hazard (start + offset) = 0
    · simp only [hzero, zero_mul, sub_zero, one_mul, zero_add] at hstep ⊢
      dsimp only [difference]
      rw [hstep]
    · have hpositive : 0 < path.hazard (start + offset) :=
        lt_of_le_of_ne (path.hazard_nonneg _) (Ne.symm hzero)
      rw [hmono (start + offset) (by omega) hpositive] at hstep
      dsimp only [difference]
      linarith
  have hfinite (length : ℕ) :
      difference start = survivalProduct (fun time => 1 - path.hazard time) start length *
        difference (start + length) := by
    have h := backwardRecursion_eq_weighted_sum_add_terminal
      (fun offset => difference (start + offset)) (fun _ => 0)
      (fun offset => 1 - path.hazard (start + offset)) 0 length
      (fun offset => by simpa only [Nat.add_assoc] using hrec offset)
    simpa only [survivalProduct, Nat.zero_add, Nat.add_zero, mul_zero,
      Finset.sum_const_zero, zero_add] using h
  have hbound : ∃ bound : ℝ, ∀ time, |difference time| ≤ bound := by
    refine ⟨1 / weight i + |T i owner|, fun time => ?_⟩
    calc
      |difference time| ≤ |path.value time i| + |T i owner| := by
        simpa [difference] using abs_sub_le (path.value time i) 0 (T i owner)
      _ ≤ 1 / weight i + |T i owner| := by
        rw [abs_of_nonneg (path.value_nonneg time i)]
        linarith [path.value_le time i]
  have hlimit := tendsto_survivalProduct_mul_bounded_zero
    (fun time => 1 - path.hazard time) difference start (path.absorbs start) hbound
  have hconstant : Tendsto (fun _ : ℕ => difference start) atTop (nhds 0) :=
    hlimit.congr' (Eventually.of_forall fun length => (hfinite length).symm)
  have hzero : difference start = 0 := tendsto_nhds_unique tendsto_const_nhds hconstant
  dsimp only [difference] at hzero
  linarith [path.value_nonneg start i]

/-- Along a same-owner positive block, the old active coordinate stays zero,
including across arbitrary zero-hazard gaps. -/
theorem value_owner_eq_zero_through_block (path : NormalizedSingletonPath T weight)
    (hdiag : ∀ i, T i i = 0) (start finish : ℕ) (hstart : start ≤ finish)
    (hactive : 0 < path.hazard start)
    (hblock : ∀ time, start ≤ time → time < finish →
      0 < path.hazard time → path.owner time = path.owner start) :
    path.value finish (path.owner start) = 0 := by
  have hprop : ∀ time, start ≤ time → time ≤ finish →
      path.value time (path.owner start) = 0 := by
    intro time htime
    induction time, htime using Nat.le_induction with
    | base => intro _; exact path.active_zero start hactive
    | succ time htime ih =>
        intro hfinish
        have hprevious := ih (by omega)
        have hstep := path.step time (path.owner start)
        have hcharge : path.hazard time * T (path.owner start) (path.owner time) = 0 := by
          by_cases hzero : path.hazard time = 0
          · rw [hzero, zero_mul]
          · rw [hblock time htime (by omega)
              (lt_of_le_of_ne (path.hazard_nonneg _) (Ne.symm hzero)), hdiag, mul_zero]
        rw [hprevious, hcharge, zero_add] at hstep
        exact (mul_eq_zero.mp hstep.symm).resolve_left
          (sub_pos.mpr (path.hazard_lt_one time)).ne'
  exact hprop finish hstart le_rfl

/-- Every positive owner block has a first different positive owner at a
finite date. At that boundary both owner coordinates are zero. -/
theorem exists_first_owner_change (path : NormalizedSingletonPath T weight)
    (hdiag : ∀ i, T i i = 0) (hnegative : ∀ owner, ∃ i, T i owner < 0)
    (start : ℕ) (hactive : 0 < path.hazard start) :
    ∃ finish, start < finish ∧ 0 < path.hazard finish ∧
      path.owner finish ≠ path.owner start ∧
      (∀ time, start ≤ time → time < finish →
        0 < path.hazard time → path.owner time = path.owner start) ∧
      path.value finish (path.owner start) = 0 ∧
      path.value finish (path.owner finish) = 0 := by
  classical
  have hexists := path.exists_active_owner_ne start (path.owner start) (hnegative _)
  let finish := Nat.find hexists
  have hfinish := Nat.find_spec hexists
  change start ≤ finish ∧ 0 < path.hazard finish ∧
    path.owner finish ≠ path.owner start at hfinish
  have hlt : start < finish := by
    refine lt_of_le_of_ne hfinish.1 ?_
    intro heq
    exact hfinish.2.2 (congrArg path.owner heq.symm)
  have hblock : ∀ time, start ≤ time → time < finish →
      0 < path.hazard time → path.owner time = path.owner start := by
    intro time htime hbefore hpositive
    by_contra hne
    exact Nat.find_min hexists hbefore ⟨htime, hpositive, hne⟩
  exact ⟨finish, hlt, hfinish.2.1, hfinish.2.2, hblock,
    path.value_owner_eq_zero_through_block hdiag start finish hfinish.1 hactive hblock,
    path.active_zero finish hfinish.2.1⟩

end NormalizedSingletonPath

namespace ThreeCycleInverseFormulas

/-- A nonpositive off-diagonal entry points to the forward cyclic successor. -/
theorem next_eq_finRotate_of_entry_nonpos
    {a b c d e f : ℝ} (hb : 0 < b) (hc : 0 < c) (hf : 0 < f)
    (owner next : Fin 3) (hne : next ≠ owner)
    (hentry : directedCycleMatrix a b c d e f owner next ≤ 0) :
    next = finRotate 3 owner := by
  fin_cases owner <;> fin_cases next
  all_goals
    first
    | rfl
    | exact (hne rfl).elim
    | exact (not_le_of_gt hb hentry).elim
    | exact (not_le_of_gt hc hentry).elim
    | exact (not_le_of_gt hf hentry).elim

/-- The first different positive owner is forced to be the cyclic successor;
the switching boundary has the two corresponding zero coordinates. -/
theorem exists_first_cyclic_owner_change
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) {weight : Fin 3 → ℝ}
    (path : NormalizedSingletonPath (directedCycleMatrix a b c d e f) weight)
    (start : ℕ) (hactive : 0 < path.hazard start) :
    ∃ finish, start < finish ∧ 0 < path.hazard finish ∧
      path.owner finish = finRotate 3 (path.owner start) ∧
      (∀ time, start ≤ time → time < finish →
        0 < path.hazard time → path.owner time = path.owner start) ∧
      path.value finish (path.owner start) = 0 ∧
      path.value finish (path.owner finish) = 0 := by
  have hdiag : ∀ i, directedCycleMatrix a b c d e f i i = 0 := by
    intro i
    fin_cases i <;> norm_num [directedCycleMatrix]
  have hnegative : ∀ owner, ∃ i, directedCycleMatrix a b c d e f i owner < 0 := by
    intro owner
    fin_cases owner
    · exact ⟨2, by simpa [directedCycleMatrix] using neg_neg_of_pos he⟩
    · exact ⟨0, by simpa [directedCycleMatrix] using neg_neg_of_pos ha⟩
    · exact ⟨1, by simpa [directedCycleMatrix] using neg_neg_of_pos hd⟩
  obtain ⟨finish, hlt, hpositive, hne, hblock, hzero, hnewzero⟩ :=
    path.exists_first_owner_change hdiag hnegative start hactive
  have hentry : directedCycleMatrix a b c d e f (path.owner start)
      (path.owner finish) ≤ 0 := by
    have hstep := path.step finish (path.owner start)
    rw [hzero] at hstep
    have htail := mul_nonneg (sub_pos.mpr (path.hazard_lt_one finish)).le
      (path.value_nonneg (finish + 1) (path.owner start))
    exact nonpos_of_mul_nonpos_right (by linarith) hpositive
  exact ⟨finish, hlt, hpositive,
    next_eq_finRotate_of_entry_nonpos hb hc hf _ _ hne hentry, hblock, hzero, hnewzero⟩

end ThreeCycleInverseFormulas
end Math.LinearProgramming
