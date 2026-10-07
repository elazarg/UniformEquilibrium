import GameTheory.Math.Probability.Simplex
import FixedPointTheorems.kakutani
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proper pairs for finite ratio rankings

The coefficients and numerators are raw finite real tables. A zero denominator
has value zero. The proper-pair construction follows the finite ranking and
restricted-simplex argument of Flesch, Thuijsman and Vrieze (1996), Definition
2.3 and Theorem 2.4. No stochastic-game semantics is imported here.
-/

noncomputable section

open scoped BigOperators
open Filter Topology
open GameTheory.Math.Probability

namespace Math.Probability.RatioProperPair

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Pure row value against a column probability vector. -/
def rowRatio (p a : I → J → ℝ) (y : J → ℝ) (i : I) : ℝ :=
  (∑ j, y j * a i j) / (∑ j, y j * p i j)

/-- Pure column value against a row probability vector. -/
def columnRatio (p b : I → J → ℝ) (x : I → ℝ) (j : J) : ℝ :=
  (∑ i, x i * b i j) / (∑ i, x i * p i j)

/-- A fully supported pair satisfying both ratio-ranking inequalities. -/
def IsDeltaProperPair (p a b : I → J → ℝ) (δ : ℝ)
    (x : I → ℝ) (y : J → ℝ) : Prop :=
  0 < δ ∧ δ < 1 ∧ x ∈ simplexWeights I ∧ y ∈ simplexWeights J ∧
    (∀ i, 0 < x i) ∧ (∀ j, 0 < y j) ∧
    (∀ i e, rowRatio p a y e < rowRatio p a y i → x e ≤ δ * x i) ∧
    (∀ j f, columnRatio p b x f < columnRatio p b x j → y f ≤ δ * y j)

/-- A simplex pair obtained as a limit of delta-proper pairs with delta tending to zero. -/
def IsProperPair (p a b : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) : Prop :=
  x ∈ simplexWeights I ∧ y ∈ simplexWeights J ∧
    ∃ (δ : ℕ → ℝ) (xs : ℕ → I → ℝ) (ys : ℕ → J → ℝ),
      Tendsto δ atTop (𝓝 0) ∧ Tendsto xs atTop (𝓝 x) ∧ Tendsto ys atTop (𝓝 y) ∧
        ∀ n, IsDeltaProperPair p a b (δ n) (xs n) (ys n)

/-- The paper's compact simplex with its cardinality-power coordinate floor. -/
def lowerSimplex (I : Type*) [Fintype I] (δ : ℝ) : Set (I → ℝ) :=
  {x | x ∈ simplexWeights I ∧ ∀ i, δ ^ Fintype.card I ≤ x i}

theorem isClosed_lowerSimplex (δ : ℝ) : IsClosed (lowerSimplex I δ) := by
  have heq : lowerSimplex I δ = simplexWeights I ∩
      ⋂ i : I, {x : I → ℝ | δ ^ Fintype.card I ≤ x i} := by
    ext x
    simp [lowerSimplex]
  rw [heq]
  exact (isClosed_simplexWeights I).inter
    (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))

theorem isCompact_lowerSimplex (δ : ℝ) : IsCompact (lowerSimplex I δ) :=
  (isCompact_simplexWeights I).of_isClosed_subset (isClosed_lowerSimplex δ)
    (fun _ hx => hx.1)

theorem convex_lowerSimplex (δ : ℝ) : Convex ℝ (lowerSimplex I δ) := by
  intro x hx y hy s t hs ht hst
  refine ⟨convex_simplexWeights I hx.1 hy.1 hs ht hst, ?_⟩
  intro i
  change δ ^ Fintype.card I ≤ s * x i + t * y i
  calc
    δ ^ Fintype.card I = s * δ ^ Fintype.card I + t * δ ^ Fintype.card I := by
      rw [← add_mul, hst, one_mul]
    _ ≤ s * x i + t * y i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 i) hs)
        (mul_le_mul_of_nonneg_left (hy.2 i) ht)

theorem coordinate_pos_of_mem_lowerSimplex {δ : ℝ} (hδ : 0 < δ)
    {x : I → ℝ} (hx : x ∈ lowerSimplex I δ) (i : I) : 0 < x i :=
  lt_of_lt_of_le (pow_pos hδ _) (hx.2 i)

/-- Number of strictly better alternatives. -/
def strictRank (v : I → ℝ) (i : I) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => v i < v j).card

theorem strictRank_lt_card (v : I → ℝ) (i : I) : strictRank v i < Fintype.card I := by
  classical
  have hsub : (Finset.univ.filter fun j => v i < v j) ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hi : i ∈ Finset.univ.filter fun j => v i < v j := heq.symm ▸ Finset.mem_univ i
    exact (lt_irrefl (v i)) (Finset.mem_filter.mp hi).2
  exact Finset.card_lt_card hsub

theorem strictRank_lt_of_lt (v : I → ℝ) {i e : I} (h : v e < v i) :
    strictRank v i < strictRank v e := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (Finset.mem_filter.mp hj).2⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter fun j => v e < v j :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [← heq] at hi
    exact (lt_irrefl (v i)) (Finset.mem_filter.mp hi).2

/-- The constrained reply polytope for one fixed finite ranking. -/
def rankingReply (δ : ℝ) (v : I → ℝ) : Set (I → ℝ) :=
  {x | x ∈ lowerSimplex I δ ∧ ∀ i e, v e < v i → x e ≤ δ * x i}

theorem convex_rankingReply (δ : ℝ) (v : I → ℝ) :
    Convex ℝ (rankingReply δ v) := by
  intro x hx y hy s t hs ht hst
  refine ⟨convex_lowerSimplex δ hx.1 hy.1 hs ht hst, ?_⟩
  intro i e hie
  change s * x e + t * y e ≤ δ * (s * x i + t * y i)
  calc
    s * x e + t * y e ≤ s * (δ * x i) + t * (δ * y i) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 i e hie) hs)
        (mul_le_mul_of_nonneg_left (hy.2 i e hie) ht)
    _ = δ * (s * x i + t * y i) := by ring

/-- Normalized geometric rank weights satisfy the floor and every ranking inequality. -/
theorem rankingReply_nonempty [Nonempty I] (v : I → ℝ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hcard : δ * Fintype.card I ≤ 1) :
    (rankingReply δ v).Nonempty := by
  classical
  let w : I → ℝ := fun i => δ ^ strictRank v i
  let Z : ℝ := ∑ i, w i
  have hwpos : ∀ i, 0 < w i := fun i => pow_pos hδ0 _
  have hZpos : 0 < Z := by
    exact Finset.sum_pos (fun i _ => hwpos i) Finset.univ_nonempty
  have hZle : Z ≤ Fintype.card I := by
    calc
      Z ≤ ∑ _i : I, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => pow_le_one₀ hδ0.le hδ1
      _ = Fintype.card I := by simp
  have hδZ : δ * Z ≤ 1 :=
    (mul_le_mul_of_nonneg_left hZle hδ0.le).trans hcard
  refine ⟨fun i => w i / Z, ⟨?_, ?_⟩, ?_⟩
  · apply mem_simplexWeights.mpr
    refine ⟨fun i => (div_pos (hwpos i) hZpos).le, ?_⟩
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  · intro i
    apply (le_div_iff₀ hZpos).2
    have hpow : δ ^ Fintype.card I ≤ δ ^ (strictRank v i + 1) :=
      pow_le_pow_of_le_one hδ0.le hδ1 (Nat.succ_le_of_lt (strictRank_lt_card v i))
    calc
      δ ^ Fintype.card I * Z ≤ (δ * w i) * Z :=
        mul_le_mul_of_nonneg_right (by simpa [w, pow_succ, mul_comm] using hpow) hZpos.le
      _ = w i * (δ * Z) := by ring
      _ ≤ w i * 1 := mul_le_mul_of_nonneg_left hδZ (hwpos i).le
      _ = w i := mul_one _
  · intro i e hie
    have hpow : w e ≤ δ * w i := by
      simpa [w, pow_succ, mul_comm] using
        (pow_le_pow_of_le_one hδ0.le hδ1
          (Nat.succ_le_of_lt (strictRank_lt_of_lt v hie)))
    calc
      w e / Z ≤ (δ * w i) / Z := div_le_div_of_nonneg_right hpow hZpos.le
      _ = δ * (w i / Z) := by ring

private theorem continuous_ratio_lowerSimplex (p a : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) {δ : ℝ} (hδ : 0 < δ) :
    Continuous fun x : lowerSimplex I δ =>
      (∑ i, x.1 i * a i) / (∑ i, x.1 i * p i) := by
  classical
  by_cases hz : ∀ i, p i = 0
  · simp_rw [hz, mul_zero, Finset.sum_const_zero, div_zero]
    exact continuous_const
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hi)
    have hden : ∀ x : lowerSimplex I δ, 0 < ∑ j, x.1 j * p j := by
      intro x
      exact lt_of_lt_of_le
        (mul_pos (coordinate_pos_of_mem_lowerSimplex hδ x.2 i) hpi)
        (Finset.single_le_sum
          (fun j _ => mul_nonneg
            (coordinate_pos_of_mem_lowerSimplex hδ x.2 j).le (hp j))
          (Finset.mem_univ i))
    exact (continuous_finsetSum Finset.univ fun j _ =>
      ((continuous_apply j).comp continuous_subtype_val).mul continuous_const).div
      (continuous_finsetSum Finset.univ fun j _ =>
        ((continuous_apply j).comp continuous_subtype_val).mul continuous_const)
      (fun x => (hden x).ne')

omit [Fintype I] in
/-- Each pure ratio is continuous on the restricted, fully mixed simplex. -/
theorem continuous_rowRatio_lowerSimplex (p a : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) {δ : ℝ} (hδ : 0 < δ) (i : I) :
    Continuous fun y : lowerSimplex J δ => rowRatio p a y.1 i :=
  continuous_ratio_lowerSimplex (p i) (a i) (hp i) hδ

omit [Fintype J] in
theorem continuous_columnRatio_lowerSimplex (p b : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) {δ : ℝ} (hδ : 0 < δ) (j : J) :
    Continuous fun x : lowerSimplex I δ => columnRatio p b x.1 j :=
  continuous_ratio_lowerSimplex (fun i => p i j) (fun i => b i j)
    (fun i => hp i j) hδ

private theorem closedGraph_rankingReply {X : Type*} [TopologicalSpace X]
    (v : X → I → ℝ) (hv : ∀ i, Continuous fun x => v x i) (δ : ℝ) :
    closedGraph (fun x => rankingReply δ (v x)) := by
  classical
  have heq : {z : X × (I → ℝ) | z.2 ∈ rankingReply δ (v z.1)} =
      {z | z.2 ∈ lowerSimplex I δ} ∩
        ⋂ i : I, ⋂ e : I,
          ({z | v z.1 i ≤ v z.1 e} ∪ {z | z.2 e ≤ δ * z.2 i}) := by
    ext z
    simp [rankingReply, imp_iff_not_or, not_lt]
  change IsClosed {z : X × (I → ℝ) | z.2 ∈ rankingReply δ (v z.1)}
  rw [heq]
  exact ((isClosed_lowerSimplex δ).preimage continuous_snd).inter
    (isClosed_iInter fun i => isClosed_iInter fun e =>
      (isClosed_le ((hv i).comp continuous_fst) ((hv e).comp continuous_fst)).union
        (isClosed_le ((continuous_apply e).comp continuous_snd)
          (continuous_const.mul ((continuous_apply i).comp continuous_snd))))

private def pairDomain (I J : Type*) [Fintype I] [Fintype J] (δ : ℝ) :
    Set ((I → ℝ) × (J → ℝ)) :=
  lowerSimplex I δ ×ˢ lowerSimplex J δ

private def pairReply (p a b : I → J → ℝ) (δ : ℝ) (z : pairDomain I J δ) :
    Set ((I → ℝ) × (J → ℝ)) :=
  rankingReply δ (rowRatio p a z.1.2) ×ˢ rankingReply δ (columnRatio p b z.1.1)

private theorem closedGraph_pairReply (p a b : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) {δ : ℝ} (hδ : 0 < δ) :
    closedGraph (pairReply p a b δ) := by
  have hcolumn : Continuous fun z : pairDomain I J δ =>
      (⟨z.1.2, z.2.2⟩ : lowerSimplex J δ) :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk (fun z => z.2.2)
  have hrow : Continuous fun z : pairDomain I J δ =>
      (⟨z.1.1, z.2.1⟩ : lowerSimplex I δ) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk (fun z => z.2.1)
  have hr := closedGraph_rankingReply
    (fun z : pairDomain I J δ => rowRatio p a z.1.2)
    (fun i => (continuous_rowRatio_lowerSimplex p a hp hδ i).comp hcolumn) δ
  have hc := closedGraph_rankingReply
    (fun z : pairDomain I J δ => columnRatio p b z.1.1)
    (fun j => (continuous_columnRatio_lowerSimplex p b hp hδ j).comp hrow) δ
  change IsClosed _ at hr hc ⊢
  have heq : {z : pairDomain I J δ × ((I → ℝ) × (J → ℝ)) |
      z.2 ∈ pairReply p a b δ z.1} =
      {z | z.2.1 ∈ rankingReply δ (rowRatio p a z.1.1.2)} ∩
        {z | z.2.2 ∈ rankingReply δ (columnRatio p b z.1.1.1)} := by
    ext z
    rfl
  rw [heq]
  exact (hr.preimage
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).inter
      (hc.preimage (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

private theorem exists_deltaProperPair_small [Nonempty I] [Nonempty J]
    (p a b : I → J → ℝ) (hp : ∀ i j, 0 ≤ p i j) {δ : ℝ}
    (hδ0 : 0 < δ)
    (hδbound : δ ≤ 1 / (Fintype.card I + Fintype.card J + 1 : ℝ)) :
    ∃ x y, IsDeltaProperPair p a b δ x y := by
  have hm : (1 : ℝ) ≤ Fintype.card I := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card I))
  have hn : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card J))
  have hsumpos : 0 < (Fintype.card I + Fintype.card J + 1 : ℝ) := by positivity
  have hδsum : δ * (Fintype.card I + Fintype.card J + 1 : ℝ) ≤ 1 :=
    (le_div_iff₀ hsumpos).mp hδbound
  have hδthree : δ * 3 ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith :
      (3 : ℝ) ≤ Fintype.card I + Fintype.card J + 1) hδ0.le).trans hδsum
  have hδ1 : δ < 1 := by linarith
  have hcardI : δ * Fintype.card I ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith :
      (Fintype.card I : ℝ) ≤ Fintype.card I + Fintype.card J + 1) hδ0.le).trans hδsum
  have hcardJ : δ * Fintype.card J ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith :
      (Fintype.card J : ℝ) ≤ Fintype.card I + Fintype.card J + 1) hδ0.le).trans hδsum
  have hnonempty : (pairDomain I J δ).Nonempty := by
    obtain ⟨x, hx⟩ := rankingReply_nonempty (fun _ : I => 0) hδ0 hδ1.le hcardI
    obtain ⟨y, hy⟩ := rankingReply_nonempty (fun _ : J => 0) hδ0 hδ1.le hcardJ
    exact ⟨(x, y), hx.1, hy.1⟩
  have hself : ∀ z : pairDomain I J δ, pairReply p a b δ z ⊆ pairDomain I J δ := by
    intro z w hw
    exact ⟨hw.1.1, hw.2.1⟩
  have hconvex : ∀ z : pairDomain I J δ, Convex ℝ (pairReply p a b δ z) :=
    fun z => (convex_rankingReply δ (rowRatio p a z.1.2)).prod
      (convex_rankingReply δ (columnRatio p b z.1.1))
  have hreply : ∀ z : pairDomain I J δ, (pairReply p a b δ z).Nonempty :=
    fun z => (rankingReply_nonempty (rowRatio p a z.1.2) hδ0 hδ1.le hcardI).prod
      (rankingReply_nonempty (columnRatio p b z.1.1) hδ0 hδ1.le hcardJ)
  obtain ⟨z, hz⟩ := kakutani_fixed_point (pairDomain I J δ)
    ((convex_lowerSimplex δ).prod (convex_lowerSimplex δ))
    ((isCompact_lowerSimplex δ).prod (isCompact_lowerSimplex δ)) hnonempty
    (pairReply p a b δ) (closedGraph_pairReply p a b hp hδ0)
    (fun z => ⟨hself z, hconvex z, hreply z⟩)
  refine ⟨z.1.1, z.1.2, hδ0, hδ1, z.2.1.1, z.2.2.1, ?_, ?_, hz.1.2, hz.2.2⟩
  · exact fun i => coordinate_pos_of_mem_lowerSimplex hδ0 z.2.1 i
  · exact fun j => coordinate_pos_of_mem_lowerSimplex hδ0 z.2.2 j

/-- Increasing delta preserves every ranking inequality of a delta-proper pair. -/
theorem IsDeltaProperPair.mono {p a b : I → J → ℝ} {δ η : ℝ}
    {x : I → ℝ} {y : J → ℝ} (h : IsDeltaProperPair p a b δ x y)
    (hle : δ ≤ η) (hη : η < 1) : IsDeltaProperPair p a b η x y := by
  rcases h with ⟨hδ0, _, hx, hy, hxpos, hypos, hr, hc⟩
  refine ⟨hδ0.trans_le hle, hη, hx, hy, hxpos, hypos, ?_, ?_⟩
  · intro i e hie
    exact (hr i e hie).trans (mul_le_mul_of_nonneg_right hle (hxpos i).le)
  · intro j f hjf
    exact (hc j f hjf).trans (mul_le_mul_of_nonneg_right hle (hypos j).le)

/-- Every finite nonnegative coefficient table has a delta-proper pair at every delta in (0,1). -/
theorem exists_deltaProperPair [Nonempty I] [Nonempty J]
    (p a b : I → J → ℝ) (hp : ∀ i j, 0 ≤ p i j) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) : ∃ x y, IsDeltaProperPair p a b δ x y := by
  let η : ℝ := min δ (1 / (Fintype.card I + Fintype.card J + 1 : ℝ))
  have hηpos : 0 < η := lt_min hδ0 (by positivity)
  obtain ⟨x, y, hxy⟩ := exists_deltaProperPair_small p a b hp hηpos (min_le_right _ _)
  exact ⟨x, y, hxy.mono (min_le_left _ _) hδ1⟩

/-- A proper pair is produced from the raw tables, with no supplied fixed-point certificates. -/
theorem exists_properPair [Nonempty I] [Nonempty J]
    (p a b : I → J → ℝ) (hp : ∀ i j, 0 ≤ p i j) :
    ∃ x y, IsProperPair p a b x y := by
  let δ : ℕ → ℝ := fun n => (1 / 2 : ℝ) * (1 / (n + 1 : ℝ))
  have hδ : ∀ n, 0 < δ n ∧ δ n < 1 := by
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hinv : (1 / (n + 1 : ℝ)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    constructor
    · dsimp [δ]
      positivity
    · have hhalf := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 1 / 2)
      dsimp [δ]
      linarith
  have hδlimit : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0)).const_mul (1 / 2 : ℝ)
  choose x y hxy using fun n => exists_deltaProperPair p a b hp (hδ n).1 (hδ n).2
  have hmem : ∀ n, (x n, y n) ∈ simplexWeights I ×ˢ simplexWeights J :=
    fun n => ⟨(hxy n).2.2.1, (hxy n).2.2.2.1⟩
  obtain ⟨z, hz, φ, hφ, hlimit⟩ :=
    ((isCompact_simplexWeights I).prod (isCompact_simplexWeights J)).tendsto_subseq hmem
  refine ⟨z.1, z.2, hz.1, hz.2, δ ∘ φ, x ∘ φ, y ∘ φ,
    hδlimit.comp hφ.tendsto_atTop, hlimit.fst_nhds, hlimit.snd_nhds, ?_⟩
  exact fun n => hxy (φ n)

end Math.Probability.RatioProperPair
