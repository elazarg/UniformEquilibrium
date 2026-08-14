/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNFiberLift

/-!
# Primitive cyclic blocks and sufficiency of every gcd collapse

For `0 < k < n`, the consecutive block

`{0, 1, ..., k - 1} ⊂ ZMod n`

has trivial translation stabilizer.  Its key invariant is elementary: zero
is the unique active point whose predecessor is inactive.  Any translation
preserving the block must preserve that unique entry boundary, hence must be
the zero translation.

Fiber lifting this primitive block by a group of size `d` constructs a block
with parameters

`K = k*d`, `N = n*d`, `period = n`, `stabilizer = d`.

Consequently every positive common divisor `d ∣ K` and `d ∣ N` is not only a
necessary cyclic collapse factor: for `0 < K < N` it is attainable on an
`N`-player finite additive population.
-/

namespace GameTheory

namespace CyclicKofNPrimitiveBlocks

open CyclicKofNArithmetic CyclicKofNFiberLift
open scoped Pointwise

noncomputable section

/-! ## Consecutive blocks in `ZMod n` -/

/-- The first `k` residues in `ZMod n`. -/
def initialBlock (n k : ℕ) : Finset (ZMod n) :=
  (Finset.range k).image fun j : ℕ => (j : ZMod n)

/-- Membership in the consecutive block is exactly the canonical-value
inequality `x.val < k`. -/
theorem mem_initialBlock_iff {n k : ℕ} [NeZero n] (hk : k ≤ n)
    (x : ZMod n) :
    x ∈ initialBlock n k ↔ x.val < k := by
  constructor
  · intro hx
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx
    have hjk : j < k := Finset.mem_range.mp hj
    have hjn : j < n := hjk.trans_le hk
    rw [← hjx]
    simpa [ZMod.val_natCast_of_lt hjn] using hjk
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨x.val, Finset.mem_range.mpr hx, ?_⟩
    exact ZMod.natCast_zmod_val x

/-- The consecutive block has exactly `k` elements. -/
theorem card_initialBlock {n k : ℕ} [NeZero n] (hk : k ≤ n) :
    (initialBlock n k).card = k := by
  calc
    (initialBlock n k).card = (Finset.range k).card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      have ha_lt : a < n := (Finset.mem_range.mp ha).trans_le hk
      have hb_lt : b < n := (Finset.mem_range.mp hb).trans_le hk
      have hval := congrArg ZMod.val hab
      simpa [ZMod.val_natCast_of_lt ha_lt,
        ZMod.val_natCast_of_lt hb_lt] using hval
    _ = k := Finset.card_range k

/-- Zero is the unique entry boundary of a nonempty proper consecutive
block: it is active while its predecessor is inactive. -/
theorem initialBlock_entry_iff {n k : ℕ} [NeZero n]
    (hkpos : 0 < k) (hkproper : k < n) (x : ZMod n) :
    x ∈ initialBlock n k ∧ x - 1 ∉ initialBlock n k ↔ x = 0 := by
  have hnTwo : 1 < n := by omega
  have hk : k ≤ n := hkproper.le
  letI : Fact (1 < n) := ⟨hnTwo⟩
  constructor
  · rintro ⟨hx, hxprev⟩
    have hxval : x.val < k := (mem_initialBlock_iff hk x).mp hx
    by_contra hxzero
    have hxvalne : x.val ≠ 0 := by
      intro hval
      apply hxzero
      apply ZMod.val_injective n
      simp [hval]
    have honele : (1 : ZMod n).val ≤ x.val := by
      rw [ZMod.val_one n]
      exact Nat.one_le_iff_ne_zero.mpr hxvalne
    apply hxprev
    apply (mem_initialBlock_iff hk (x - 1)).mpr
    rw [ZMod.val_sub honele, ZMod.val_one n]
    omega
  · intro hxzero
    subst x
    constructor
    · apply (mem_initialBlock_iff hk 0).mpr
      simpa using hkpos
    · intro hneg
      have hnegval : ((-1 : ZMod n).val) = n - 1 := by
        letI : NeZero (1 : ZMod n) := ⟨one_ne_zero⟩
        rw [ZMod.val_neg_of_ne_zero, ZMod.val_one n]
      have hlt : (-1 : ZMod n).val < k :=
        (mem_initialBlock_iff hk (-1)).mp (by simpa using hneg)
      rw [hnegval] at hlt
      omega

/-- Every nonempty proper consecutive block is translation primitive. -/
theorem initialBlock_stabilizer_card_eq_one {n k : ℕ} [NeZero n]
    (hkpos : 0 < k) (hkproper : k < n) :
    Fintype.card (AddAction.stabilizer (ZMod n) (initialBlock n k)) = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨0, by simp⟩, ?_⟩
  rintro ⟨g, hg⟩
  apply Subtype.ext
  change g = 0
  change g +ᵥ initialBlock n k = initialBlock n k at hg
  have hentry := (initialBlock_entry_iff hkpos hkproper 0).mpr rfl
  have hgmem : g ∈ initialBlock n k := by
    rw [← hg]
    simpa only [vadd_eq_add, add_zero] using
      (Finset.vadd_mem_vadd_finset_iff (s := initialBlock n k)
        (b := (0 : ZMod n)) g).mpr hentry.1
  have hgprev : g - 1 ∉ initialBlock n k := by
    intro hbad
    have hbadTranslate : g - 1 ∈ g +ᵥ initialBlock n k := by
      rwa [hg]
    have hminus : -g + (g - 1) ∈ initialBlock n k :=
      (Finset.neg_vadd_mem_iff).mpr hbadTranslate
    have : (-1 : ZMod n) ∈ initialBlock n k := by
      convert hminus using 1
      all_goals ring
    apply hentry.2
    simpa using this
  exact (initialBlock_entry_iff hkpos hkproper g).mp ⟨hgmem, hgprev⟩

/-- A primitive consecutive block has the full `n` translation phases. -/
theorem card_translationPhase_initialBlock {n k : ℕ} [NeZero n]
    (hkpos : 0 < k) (hkproper : k < n) :
    Fintype.card (TranslationPhase (initialBlock n k)) = n := by
  rw [card_translationPhase_eq_div_stabilizer,
    initialBlock_stabilizer_card_eq_one hkpos hkproper, Nat.div_one]
  simp

/-! ## Exact realization of an arbitrary admissible collapse factor -/

/-- Factored form: a primitive `k/n` base block lifted by `ZMod d` has
block size `k*d`, population `n*d`, period `n`, and stabilizer size `d`. -/
theorem exists_factored_block_with_exact_collapse
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hkpos : 0 < k) (hkproper : k < n) :
    ∃ A : Finset (ZMod n × ZMod d),
      A.card = k * d ∧
      Fintype.card (ZMod n × ZMod d) = n * d ∧
      Fintype.card (TranslationPhase A) = n ∧
      Fintype.card (AddAction.stabilizer (ZMod n × ZMod d) A) = d := by
  let base := initialBlock n k
  let A := fiberLift (H := ZMod d) base
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simp [A, base, card_fiberLift, card_initialBlock hkproper.le]
  · simp
  · dsimp only [A]
    rw [card_translationPhase_fiberLift,
      card_translationPhase_initialBlock hkpos hkproper]
  · dsimp only [A]
    rw [card_stabilizer_fiberLift_of_primitive base]
    · simp
    · exact initialBlock_stabilizer_card_eq_one hkpos hkproper

/-- **Sufficiency of every gcd collapse.**  If `d` is a positive common
divisor of `K` and `N`, with `0 < K < N`, then there is an `N`-player finite
additive population and a `K`-block whose distinct-translation period is
exactly `N/d` and whose stabilizer size is exactly `d`. -/
theorem exists_block_with_exact_admissible_collapse
    {K N d : ℕ} (hKpos : 0 < K) (hKN : K < N)
    (hdpos : 0 < d) (hdK : d ∣ K) (hdN : d ∣ N) :
    letI : NeZero (N / d) :=
      ⟨(Nat.div_pos (Nat.le_of_dvd (hKpos.trans hKN) hdN) hdpos).ne'⟩
    letI : NeZero d := ⟨hdpos.ne'⟩
    ∃ A : Finset (ZMod (N / d) × ZMod d),
      A.card = K ∧
      Fintype.card (ZMod (N / d) × ZMod d) = N ∧
      Fintype.card (TranslationPhase A) = N / d ∧
      Fintype.card
        (AddAction.stabilizer (ZMod (N / d) × ZMod d) A) = d := by
  have hdleK : d ≤ K := Nat.le_of_dvd hKpos hdK
  have hdleN : d ≤ N := hdleK.trans hKN.le
  have hkpos : 0 < K / d := Nat.div_pos hdleK hdpos
  have hnpos : 0 < N / d := Nat.div_pos hdleN hdpos
  have hkproper : K / d < N / d := by
    by_contra hnot
    have hle : N / d ≤ K / d := Nat.le_of_not_gt hnot
    have hmul := Nat.mul_le_mul_right d hle
    rw [Nat.div_mul_cancel hdN, Nat.div_mul_cancel hdK] at hmul
    exact (Nat.not_le_of_lt hKN) hmul
  letI : NeZero (N / d) := ⟨hnpos.ne'⟩
  letI : NeZero d := ⟨hdpos.ne'⟩
  obtain ⟨A, hcard, hpopulation, hperiod, hstabilizer⟩ :=
    exists_factored_block_with_exact_collapse
      (n := N / d) (k := K / d) (d := d) hkpos hkproper
  refine ⟨A, ?_, ?_, hperiod, hstabilizer⟩
  · simpa [Nat.div_mul_cancel hdK] using hcard
  · simp [Nat.div_mul_cancel hdN]

end

end CyclicKofNPrimitiveBlocks

end GameTheory
