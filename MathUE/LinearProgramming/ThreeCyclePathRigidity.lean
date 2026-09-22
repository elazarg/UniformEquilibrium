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

/-- If all other coordinates vanish, normalization identifies the remaining
coordinate with its weighted probability-simplex vertex. -/
theorem value_eq_single_of_zero_off [DecidableEq ι]
    (path : NormalizedSingletonPath T weight) (time : ℕ) (j : ι)
    (hzero : ∀ i, i ≠ j → path.value time i = 0) :
    path.value time = Pi.single j (1 / weight j) := by
  have hsum : (∑ i, weight i * path.value time i) =
      weight j * path.value time j := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      rw [hzero i hij, mul_zero]
    · simp
  have hj : path.value time j = 1 / weight j := by
    apply (eq_div_iff (path.weight_pos j).ne').mpr
    rw [mul_comm, ← hsum, path.normalized]
  ext i
  by_cases hij : i = j
  · subst i
    simpa using hj
  · simp [hij, hzero i hij]

/-- A zero-hazard row leaves every continuation coordinate unchanged. -/
theorem value_eq_next_of_hazard_zero (path : NormalizedSingletonPath T weight)
    (time : ℕ) (hzero : path.hazard time = 0) :
    path.value time = path.value (time + 1) := by
  funext i
  simpa only [hzero, zero_mul, sub_zero, one_mul, zero_add] using path.step time i

/-- A finite window with one positive-hazard owner merges into one affine
step. Zero-hazard rows and the zero-length window need no special premises. -/
theorem value_eq_survival_affine_of_same_owner
    (path : NormalizedSingletonPath T weight) (start length : ℕ) (owner : ι)
    (hblock : ∀ offset, offset < length →
      0 < path.hazard (start + offset) → path.owner (start + offset) = owner)
    (i : ι) :
    path.value start i =
      (1 - survivalProduct (fun time => 1 - path.hazard time) start length) * T i owner +
      survivalProduct (fun time => 1 - path.hazard time) start length *
        path.value (start + length) i := by
  have hunroll := backwardRecursion_eq_weighted_sum_add_terminal
    (fun time => path.value time i)
    (fun time => path.hazard time * T i (path.owner time))
    (fun time => 1 - path.hazard time) start length (fun time => path.step time i)
  have hforcing :
      (∑ offset ∈ Finset.range length,
        survivalProduct (fun time => 1 - path.hazard time) start offset *
          (path.hazard (start + offset) * T i (path.owner (start + offset)))) =
      (∑ offset ∈ Finset.range length,
        survivalProduct (fun time => 1 - path.hazard time) start offset *
          path.hazard (start + offset)) * T i owner := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro offset hoffset
    by_cases hzero : path.hazard (start + offset) = 0
    · simp only [hzero, zero_mul, mul_zero]
    · rw [hblock offset (Finset.mem_range.mp hoffset)
        (lt_of_le_of_ne (path.hazard_nonneg _) (Ne.symm hzero))]
      ring
  have hmass :
      (∑ offset ∈ Finset.range length,
        survivalProduct (fun time => 1 - path.hazard time) start offset *
          path.hazard (start + offset)) =
        1 - survivalProduct (fun time => 1 - path.hazard time) start length := by
    simpa only [sub_sub_cancel] using
      sum_survivalProduct_mul_one_sub (fun time => 1 - path.hazard time) start length
  rw [hforcing, hmass] at hunroll
  exact hunroll

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
  have hbound : ∃ bound : ℝ, ∀ time, |difference time| ≤ bound := by
    refine ⟨1 / weight i + |T i owner|, fun time => ?_⟩
    calc
      |difference time| ≤ |path.value time i| + |T i owner| := by
        simpa [difference] using abs_sub_le (path.value time i) 0 (T i owner)
      _ ≤ 1 / weight i + |T i owner| := by
        rw [abs_of_nonneg (path.value_nonneg time i)]
        linarith [path.value_le time i]
  have habs := abs_prescribedError_le_of_suffixDiscrepancy
    (fun offset => difference (start + offset)) (fun _ => 0)
    (fun offset => 1 - path.hazard (start + offset)) 0
    (fun offset => (sub_pos.mpr (path.hazard_lt_one _)).le)
    (fun offset => by linarith [path.hazard_nonneg (start + offset)])
    (fun offset => by simpa only [zero_add, sub_zero, Nat.add_assoc] using hrec offset)
    (by intro first length; simp)
    (fun first => by
      have hshift :
          Math.survivalProduct (fun offset => 1 - path.hazard (start + offset)) first =
            Math.survivalProduct (fun time => 1 - path.hazard time) (start + first) := by
        funext length
        unfold Math.survivalProduct
        apply Finset.prod_congr rfl
        intro offset _
        rw [Nat.add_assoc]
      rw [hshift]
      exact path.absorbs (start + first))
    ⟨hbound.choose, fun offset => hbound.choose_spec (start + offset)⟩ 0
  have hzero : difference start = 0 :=
    abs_eq_zero.mp (le_antisymm (by simpa only [Nat.add_zero] using habs) (abs_nonneg _))
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

private theorem successor_entry_pos
    {a b c d e f : ℝ} (hb : 0 < b) (hc : 0 < c) (hf : 0 < f)
    (owner : Fin 3) :
    0 < directedCycleMatrix a b c d e f (finRotate 3 owner) owner := by
  fin_cases owner
  · exact hc
  · exact hf
  · exact hb

private theorem survivalFraction_successor_balance
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f) (owner : Fin 3) :
    (1 - survivalFraction a b c d e f owner) *
      (directedCycleMatrix a b c d e f (finRotate 3 owner) owner *
        columnWeight a b c d e f (finRotate 3 owner)) = 1 := by
  have hfractions := fractions_pos_lt_one_add_eq_one ha hb hc hd he hf hgap owner
  have hcomplement : 1 - survivalFraction a b c d e f owner =
      absorptionFraction a b c d e f owner := by linarith [hfractions.2.2.2.2]
  have habsorption : absorptionFraction a b c d e f owner =
      1 / (directedCycleMatrix a b c d e f (finRotate 3 owner) owner *
        columnWeight a b c d e f (finRotate 3 owner)) := by
    fin_cases owner <;> rfl
  rw [hcomplement, habsorption]
  exact one_div_mul_cancel (mul_pos (successor_entry_pos hb hc hf owner)
    (columnWeight_pos ha hb hc hd he hf hgap _)).ne'

/-- A same-owner finite window ending with zero successor coordinate has
at least the algebraic full-block survival. Its initial point may be anywhere
on the normalized simplex; no entry vertex or positive initial hazard is
assumed. -/
theorem survivalFraction_le_window_survival
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (path : NormalizedSingletonPath (directedCycleMatrix a b c d e f)
      (columnWeight a b c d e f))
    (start length : ℕ) (owner : Fin 3)
    (hblock : ∀ offset, offset < length →
      0 < path.hazard (start + offset) → path.owner (start + offset) = owner)
    (hexit : path.value (start + length) (finRotate 3 owner) = 0) :
    survivalFraction a b c d e f owner ≤
      survivalProduct (fun time => 1 - path.hazard time) start length := by
  let next := finRotate 3 owner
  let entry := directedCycleMatrix a b c d e f next owner
  let weight := columnWeight a b c d e f next
  let survival := survivalProduct (fun time => 1 - path.hazard time) start length
  have hweight : 0 < weight := path.weight_pos next
  have hden : 0 < entry * weight := mul_pos (successor_entry_pos hb hc hf owner) hweight
  have harc := path.value_eq_survival_affine_of_same_owner start length owner hblock next
  rw [hexit, mul_zero, add_zero] at harc
  have harcWeighted : (1 - survival) * (entry * weight) =
      path.value start next * weight := by
    change path.value start next = (1 - survival) * entry at harc
    rw [harc]
    ring
  have hbound : path.value start next * weight ≤ 1 :=
    (le_div_iff₀ hweight).mp (path.value_le start next)
  have hbalance := survivalFraction_successor_balance ha hb hc hd he hf hgap owner
  change (1 - survivalFraction a b c d e f owner) * (entry * weight) = 1 at hbalance
  have hcompare : (1 - survival) * (entry * weight) ≤
      (1 - survivalFraction a b c d e f owner) * (entry * weight) := by
    rw [harcWeighted, hbalance]
    exact hbound
  have h := (mul_le_mul_iff_of_pos_right hden).mp hcompare
  change survivalFraction a b c d e f owner ≤ survival
  linarith

/-- When that window starts at the full successor-coordinate value, its
survival is exactly the algebraic block fraction. In the forced-cycle
application, the two endpoint conditions come from adjacent owner changes. -/
theorem window_survival_eq_survivalFraction
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (path : NormalizedSingletonPath (directedCycleMatrix a b c d e f)
      (columnWeight a b c d e f))
    (start length : ℕ) (owner : Fin 3)
    (hblock : ∀ offset, offset < length →
      0 < path.hazard (start + offset) → path.owner (start + offset) = owner)
    (hentry : path.value start (finRotate 3 owner) =
      1 / columnWeight a b c d e f (finRotate 3 owner))
    (hexit : path.value (start + length) (finRotate 3 owner) = 0) :
    survivalProduct (fun time => 1 - path.hazard time) start length =
      survivalFraction a b c d e f owner := by
  let next := finRotate 3 owner
  let entry := directedCycleMatrix a b c d e f next owner
  let weight := columnWeight a b c d e f next
  let survival := survivalProduct (fun time => 1 - path.hazard time) start length
  have hweight : 0 < weight := path.weight_pos next
  have hden : 0 < entry * weight := mul_pos (successor_entry_pos hb hc hf owner) hweight
  have harc := path.value_eq_survival_affine_of_same_owner start length owner hblock next
  rw [hexit, mul_zero, add_zero, hentry] at harc
  have harcWeighted : (1 - survival) * (entry * weight) = 1 := by
    calc
      (1 - survival) * (entry * weight) =
          ((1 - survival) * entry) * weight := by ring
      _ = (1 / weight) * weight := by rw [← harc]
      _ = 1 := one_div_mul_cancel hweight.ne'
  have hbalance := survivalFraction_successor_balance ha hb hc hd he hf hgap owner
  change (1 - survivalFraction a b c d e f owner) * (entry * weight) = 1 at hbalance
  have h := mul_right_cancel₀ hden.ne' (harcWeighted.trans hbalance.symm)
  change survival = survivalFraction a b c d e f owner
  linarith

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

private theorem exists_vertex_at_three_changes
    {T : Matrix (Fin 3) (Fin 3) ℝ} {weight : Fin 3 → ℝ}
    (path : NormalizedSingletonPath T weight) (first second third fourth : ℕ)
    (hsecondOwner : path.owner second = finRotate 3 (path.owner first))
    (hthirdOwner : path.owner third = finRotate 3 (path.owner second))
    (hfourthOwner : path.owner fourth = finRotate 3 (path.owner third))
    (hzeroFirst : path.value second (path.owner first) = 0)
    (hzeroSecond : path.value second (path.owner second) = 0)
    (hzeroSecond' : path.value third (path.owner second) = 0)
    (hzeroThird : path.value third (path.owner third) = 0)
    (hzeroThird' : path.value fourth (path.owner third) = 0)
    (hzeroFourth : path.value fourth (path.owner fourth) = 0) (j : Fin 3) :
    ∃ time, (time = second ∨ time = third ∨ time = fourth) ∧
      path.value time = Pi.single j (1 / weight j) := by
  have hvertex (time : ℕ) (old next : Fin 3)
      (hne : old ≠ next) (hjOld : j ≠ old) (hjNext : j ≠ next)
      (hold : path.value time old = 0) (hnext : path.value time next = 0) :
      path.value time = Pi.single j (1 / weight j) := by
    apply path.value_eq_single_of_zero_off
    intro i hij
    have hthree : ∀ x y z k : Fin 3,
        x ≠ y → z ≠ x → z ≠ y → k ≠ z → k = x ∨ k = y := by decide
    rcases hthree old next j i hne hjOld hjNext hij with hi | hi
    · simpa only [hi] using hold
    · simpa only [hi] using hnext
  have hrotateNe : ∀ i : Fin 3, i ≠ finRotate 3 i := by decide
  have hcover :
      (j ≠ path.owner first ∧ j ≠ path.owner second) ∨
      (j ≠ path.owner second ∧ j ≠ path.owner third) ∨
      (j ≠ path.owner third ∧ j ≠ path.owner fourth) := by
    rw [hfourthOwner, hthirdOwner, hsecondOwner]
    have hfinite : ∀ i k : Fin 3,
        (k ≠ i ∧ k ≠ finRotate 3 i) ∨
        (k ≠ finRotate 3 i ∧ k ≠ finRotate 3 (finRotate 3 i)) ∨
        (k ≠ finRotate 3 (finRotate 3 i) ∧
          k ≠ finRotate 3 (finRotate 3 (finRotate 3 i))) := by decide
    exact hfinite (path.owner first) j
  rcases hcover with hj | hj | hj
  · refine ⟨second, Or.inl rfl, hvertex second _ _ ?_ hj.1 hj.2 hzeroFirst hzeroSecond⟩
    rw [hsecondOwner]
    exact hrotateNe _
  · refine ⟨third, Or.inr (Or.inl rfl),
      hvertex third _ _ ?_ hj.1 hj.2 hzeroSecond' hzeroThird⟩
    rw [hthirdOwner]
    exact hrotateNe _
  · refine ⟨fourth, Or.inr (Or.inr rfl),
      hvertex fourth _ _ ?_ hj.1 hj.2 hzeroThird' hzeroFourth⟩
    rw [hfourthOwner]
    exact hrotateNe _

/-- Every tail visits every weighted probability-simplex vertex. The three
finite owner changes are derived from absorption, not supplied as data. -/
theorem exists_vertex_after
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) {weight : Fin 3 → ℝ}
    (path : NormalizedSingletonPath (directedCycleMatrix a b c d e f) weight)
    (start : ℕ) (j : Fin 3) :
    ∃ time, start ≤ time ∧ path.value time = Pi.single j (1 / weight j) := by
  obtain ⟨first, hstart, hactive, _hne⟩ :=
    path.exists_active_owner_ne start 0
      ⟨2, by simpa [directedCycleMatrix] using neg_neg_of_pos he⟩
  obtain ⟨second, hfirst, hsecondActive, hsecondOwner, _, hzeroFirst, hzeroSecond⟩ :=
    exists_first_cyclic_owner_change ha hb hc hd he hf path first hactive
  obtain ⟨third, hsecond, hthirdActive, hthirdOwner, _, hzeroSecond', hzeroThird⟩ :=
    exists_first_cyclic_owner_change ha hb hc hd he hf path second hsecondActive
  obtain ⟨fourth, hthird, _, hfourthOwner, _, hzeroThird', hzeroFourth⟩ :=
    exists_first_cyclic_owner_change ha hb hc hd he hf path third hthirdActive
  obtain ⟨time, htime, hvertex⟩ := exists_vertex_at_three_changes path first second third fourth
    hsecondOwner hthirdOwner hfourthOwner hzeroFirst hzeroSecond hzeroSecond' hzeroThird
    hzeroThird' hzeroFourth j
  exact ⟨time, by rcases htime with rfl | rfl | rfl <;> omega, hvertex⟩

/-- Every requested vertex is reached from an arbitrary starting date with
survival at least the full three-block product. The first positive row is
chosen minimally, so an arbitrarily long initial zero-hazard gap costs no
survival. No block lengths, vertex visits, or periodicity are supplied. -/
theorem exists_vertex_after_with_survival_ge
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (path : NormalizedSingletonPath (directedCycleMatrix a b c d e f)
      (columnWeight a b c d e f)) (start : ℕ) (j : Fin 3) :
    ∃ time, start ≤ time ∧
      path.value time = Pi.single j (1 / columnWeight a b c d e f j) ∧
      a * d * e / (b * c * f) ≤
        survivalProduct (fun date => 1 - path.hazard date) start (time - start) := by
  have hexists : ∃ time, start ≤ time ∧ 0 < path.hazard time := by
    obtain ⟨time, htime, hactive, _hne⟩ := path.exists_active_owner_ne start 0
      ⟨2, by simpa [directedCycleMatrix] using neg_neg_of_pos he⟩
    exact ⟨time, htime, hactive⟩
  let first := Nat.find hexists
  have hfirstSpec : start ≤ first ∧ 0 < path.hazard first := Nat.find_spec hexists
  let discount := fun time => 1 - path.hazard time
  let fraction := survivalFraction a b c d e f
  have hdiscount0 : ∀ time, 0 ≤ discount time :=
    fun time => (sub_pos.mpr (path.hazard_lt_one time)).le
  have hdiscount1 : ∀ time, discount time ≤ 1 :=
    fun time => sub_le_self _ (path.hazard_nonneg time)
  have hgapSurvival : survivalProduct discount start (first - start) = 1 := by
    apply Finset.prod_eq_one
    intro offset hoffset
    have hoffsetLt : offset < first - start := Finset.mem_range.mp hoffset
    have hnotPositive : ¬0 < path.hazard (start + offset) := by
      intro hpositive
      exact Nat.find_min hexists (by change start + offset < first; omega)
        ⟨by omega, hpositive⟩
    have hzero : path.hazard (start + offset) = 0 :=
      le_antisymm (le_of_not_gt hnotPositive) (path.hazard_nonneg _)
    simp only [discount, hzero, sub_zero]
  obtain ⟨second, hfirst, hsecondActive, hsecondOwner, hblockFirst,
      hzeroFirst, hzeroSecond⟩ :=
    exists_first_cyclic_owner_change ha hb hc hd he hf path first hfirstSpec.2
  obtain ⟨third, hsecond, hthirdActive, hthirdOwner, hblockSecond,
      hzeroSecond', hzeroThird⟩ :=
    exists_first_cyclic_owner_change ha hb hc hd he hf path second hsecondActive
  obtain ⟨fourth, hthird, _, hfourthOwner, hblockThird, hzeroThird', hzeroFourth⟩ :=
    exists_first_cyclic_owner_change ha hb hc hd he hf path third hthirdActive
  have hwindow (left right : ℕ) (hle : left ≤ right)
      (howner : path.owner right = finRotate 3 (path.owner left))
      (hblock : ∀ time, left ≤ time → time < right →
        0 < path.hazard time → path.owner time = path.owner left)
      (hzero : path.value right (path.owner right) = 0) :
      fraction (path.owner left) ≤ survivalProduct discount left (right - left) := by
    apply survivalFraction_le_window_survival ha hb hc hd he hf hgap path
      left (right - left) (path.owner left)
    · intro offset hoffset hpositive
      exact hblock (left + offset) (by omega) (by omega) hpositive
    · rw [Nat.add_sub_of_le hle, ← howner]
      exact hzero
  have hsurvFirst := hwindow first second hfirst.le hsecondOwner hblockFirst hzeroSecond
  have hsurvSecond := hwindow second third hsecond.le hthirdOwner hblockSecond hzeroThird
  have hsurvThird := hwindow third fourth hthird.le hfourthOwner hblockThird hzeroFourth
  have hfraction0 : ∀ i, 0 ≤ fraction i :=
    fun i => (fractions_pos_lt_one_add_eq_one ha hb hc hd he hf hgap i).2.2.1.le
  have hcycleProduct (i : Fin 3) :
      fraction i * (fraction (finRotate 3 i) * fraction (finRotate 3 (finRotate 3 i))) =
        ∏ k, fraction k := by
    rw [Fin.prod_univ_three]
    fin_cases i
    · change fraction 0 * (fraction 1 * fraction 2) = fraction 0 * fraction 1 * fraction 2
      ring
    · change fraction 1 * (fraction 2 * fraction 0) = fraction 0 * fraction 1 * fraction 2
      ring
    · change fraction 2 * (fraction 0 * fraction 1) = fraction 0 * fraction 1 * fraction 2
      ring
  have hfractions : fraction (path.owner first) *
      (fraction (path.owner second) * fraction (path.owner third)) =
        a * d * e / (b * c * f) := by
    rw [hthirdOwner, hsecondOwner, hcycleProduct]
    exact prod_survivalFraction ha hb hc hd he hf hgap
  have hmul : a * d * e / (b * c * f) ≤
      survivalProduct discount first (second - first) *
        (survivalProduct discount second (third - second) *
          survivalProduct discount third (fourth - third)) := by
    rw [← hfractions]
    exact mul_le_mul hsurvFirst
      (mul_le_mul hsurvSecond hsurvThird (hfraction0 _)
        (survivalProduct_nonneg discount hdiscount0 _ _))
      (mul_nonneg (hfraction0 _) (hfraction0 _))
      (survivalProduct_nonneg discount hdiscount0 _ _)
  have hsplit (left middle right : ℕ) (hlm : left ≤ middle) (hmr : middle ≤ right) :
      survivalProduct discount left (right - left) =
        survivalProduct discount left (middle - left) *
          survivalProduct discount middle (right - middle) := by
    rw [show right - left = (middle - left) + (right - middle) by omega,
      survivalProduct_add, Nat.add_sub_of_le hlm]
  have hlast : a * d * e / (b * c * f) ≤
      survivalProduct discount start (fourth - start) := by
    rw [hsplit start first fourth hfirstSpec.1 (by omega), hgapSurvival, one_mul,
      hsplit first second fourth hfirst.le (by omega),
      hsplit second third fourth hsecond.le hthird.le]
    exact hmul
  obtain ⟨time, htime, hvertex⟩ := exists_vertex_at_three_changes path first second third fourth
    hsecondOwner hthirdOwner hfourthOwner hzeroFirst hzeroSecond hzeroSecond' hzeroThird
    hzeroThird' hzeroFourth j
  have htimeStart : start ≤ time := by rcases htime with rfl | rfl | rfl <;> omega
  have htimeLast : time ≤ fourth := by rcases htime with rfl | rfl | rfl <;> omega
  refine ⟨time, htimeStart, hvertex, hlast.trans ?_⟩
  rw [hsplit start time fourth htimeStart htimeLast]
  exact mul_le_of_le_one_right (survivalProduct_nonneg discount hdiscount0 _ _)
    (survivalProduct_le_one discount hdiscount0 hdiscount1 _ _)

/-- An affine singleton-row surplus is nonnegative along any whole tail
exactly when its three vertex coefficients are nonnegative. -/
theorem dotProduct_nonneg_on_tail_iff
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) {weight : Fin 3 → ℝ}
    (path : NormalizedSingletonPath (directedCycleMatrix a b c d e f) weight)
    (coefficient : Fin 3 → ℝ) (start : ℕ) :
    (∀ time, start ≤ time → 0 ≤ dotProduct coefficient (path.value time)) ↔
      ∀ j, 0 ≤ coefficient j := by
  constructor
  · intro hfloor j
    obtain ⟨time, htime, hvertex⟩ :=
      exists_vertex_after ha hb hc hd he hf path start j
    have h := hfloor time htime
    rw [hvertex, dotProduct_single] at h
    exact nonneg_of_mul_nonneg_right (by simpa only [mul_comm] using h)
      (one_div_pos.mpr (path.weight_pos j))
  · intro hcoefficient time _
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (hcoefficient j) (path.value_nonneg time j)

end ThreeCycleInverseFormulas
end Math.LinearProgramming
