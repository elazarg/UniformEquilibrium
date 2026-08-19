from pathlib import Path
import re

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")


def replace_sorry(name: str, proof: str) -> None:
    global text
    pattern = rf"(theorem {re.escape(name)}\b.*?:= by)\n  sorry"
    text2, count = re.subn(
        pattern,
        lambda m: m.group(1) + "\n" + proof.rstrip(),
        text,
        count=1,
        flags=re.S,
    )
    if count == 1:
        text = text2
        return
    # Idempotence: an already proved declaration is fine.
    if f"theorem {name}" in text:
        return
    raise RuntimeError(f"could not locate declaration {name}")


property_a = r'''  classical
  apply continuous_pi
  intro s
  apply continuous_pi
  intro who
  unfold f
  simp_rw [P.fCoord_eq_sum]
  unfold oneStepCost
  simp_rw [expect_eq_sum]
  apply continuous_finsetSum Finset.univ
  intro a _
  apply Continuous.mul
  · apply Continuous.mul
    · exact (continuous_apply (a who)).comp
        (continuous_subtype_val.comp
          ((continuous_apply (s, who)).comp
            (continuous_fst.comp continuous_snd)))
    · apply continuous_finsetProd (Finset.univ.erase who)
      intro i _
      exact (continuous_apply (a i)).comp
        (continuous_subtype_val.comp
          ((continuous_apply (s, i)).comp continuous_fst))
  · apply Continuous.add
    · exact continuous_const
    · apply Continuous.mul
      · exact continuous_const
      · apply continuous_finsetSum Finset.univ
        intro s' _
        apply Continuous.mul
        · exact continuous_const
        · exact (continuous_apply who).comp
            ((continuous_apply s').comp
              (continuous_snd.comp continuous_snd))'''
replace_sorry("property_a_continuous", property_a)

continuity_helpers = r'''

/-- One coordinate of `f` is jointly continuous in the baseline profile and
continuation vector when the deviating mixed action is fixed. -/
theorem continuous_fCoord
    (P : Game ι) [Fintype P.State] [Fintype ι] [DecidableEq ι]
    [∀ s i, Fintype (P.Act s i)]
    (s : P.State) (who : ι) (y : stdSimplex ℝ (P.Act s who)) :
    Continuous (fun q : P.X × P.R => P.fCoord q.1 s who y q.2) := by
  classical
  simp_rw [P.fCoord_eq_sum]
  unfold oneStepCost
  simp_rw [expect_eq_sum]
  apply continuous_finsetSum Finset.univ
  intro a _
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_const
    · apply continuous_finsetProd (Finset.univ.erase who)
      intro i _
      exact (continuous_apply (a i)).comp
        (continuous_subtype_val.comp
          ((continuous_apply (s, i)).comp continuous_fst))
  · apply Continuous.add
    · exact continuous_const
    · apply Continuous.mul
      · exact continuous_const
      · apply continuous_finsetSum Finset.univ
        intro s' _
        apply Continuous.mul
        · exact continuous_const
        · exact (continuous_apply who).comp
            ((continuous_apply s').comp continuous_snd)

/-- The optimality operator is jointly continuous in the profile and
continuation vector. -/
theorem continuous_T
    (P : Game ι) [Fintype P.State] [Fintype ι] [DecidableEq ι]
    [∀ s i, Fintype (P.Act s i)] [∀ s i, Nonempty (P.Act s i)] :
    Continuous (fun q : P.X × P.R => P.T q.1 q.2) := by
  classical
  apply continuous_pi
  intro s
  apply continuous_pi
  intro who
  change Continuous (fun q : P.X × P.R =>
    -Finset.sup' Finset.univ Finset.univ_nonempty
      (fun a : P.Act s who => -P.fCoord q.1 s who (P.pureAction a) q.2))
  apply Continuous.neg
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro a _
  exact (P.continuous_fCoord s who (P.pureAction a)).neg
'''

if "theorem continuous_fCoord" not in text:
    marker = "\n/-- Property (b): one coordinate of `f` changes"
    if marker not in text:
        raise RuntimeError("continuity helper insertion marker not found")
    text = text.replace(marker, continuity_helpers + marker, 1)

phi_closed = r'''  unfold phi
  have htriple : Continuous (fun y : P.X => (x, y, P.beta x)) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  exact isClosed_eq (P.property_a_continuous.comp htriple) continuous_const'''
replace_sorry("phi_isClosed", phi_closed)

cost_infrastructure = r'''

/-- One entry of the finite cost table, including its state and player. -/
abbrev CostEntry (P : Game ι) :=
  Σ s : P.State, P.JointActionAt s × ι

/-- The scalar cost selected by a finite cost-table entry. -/
def costCoordinate (P : Game ι) (entry : P.CostEntry) : ℝ :=
  P.cost entry.1 entry.2.1 entry.2.2

/-- A common absolute bound for the finite cost table. -/
noncomputable def costBound
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [∀ s i, Fintype (P.Act s i)] : ℝ :=
  Classical.choose
    (Math.Probability.exists_abs_bound_of_finite P.costCoordinate)

theorem abs_cost_le_costBound
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [∀ s i, Fintype (P.Act s i)] (entry : P.CostEntry) :
    |P.costCoordinate entry| ≤ P.costBound :=
  Classical.choose_spec
    (Math.Probability.exists_abs_bound_of_finite P.costCoordinate) entry

theorem costBound_nonneg
    (P : Game ι) [Fintype P.State] [Fintype ι] [Nonempty ι]
    [∀ s i, Fintype (P.Act s i)] : 0 ≤ P.costBound := by
  classical
  let s : P.State := Classical.choice P.state_nonempty
  let who : ι := Classical.choice (inferInstance : Nonempty ι)
  let a : P.JointActionAt s :=
    fun i => Classical.choice (P.act_nonempty s i)
  exact (abs_nonneg (P.cost s a who)).trans
    (P.abs_cost_le_costBound (⟨s, (a, who)⟩ : P.CostEntry))

theorem abs_fCoord_zero_le_costBound
    (P : Game ι) [Fintype P.State] [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [∀ s i, Fintype (P.Act s i)]
    (x : P.X) (s : P.State) (who : ι)
    (y : stdSimplex ℝ (P.Act s who)) :
    |P.fCoord x s who y (0 : P.R)| ≤ P.costBound := by
  unfold fCoord
  refine abs_expect_le_of_abs_le _ _ (fun a => ?_)
  have h := P.abs_cost_le_costBound
    (⟨s, (a, who)⟩ : P.CostEntry)
  simpa [costCoordinate, oneStepCost] using h

theorem dist_zero_T_zero_le_costBound
    (P : Game ι) [Fintype P.State] [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [∀ s i, Fintype (P.Act s i)]
    [∀ s i, Nonempty (P.Act s i)] (x : P.X) :
    dist (0 : P.R) (P.T x 0) ≤ P.costBound := by
  rw [dist_pi_le_iff P.costBound_nonneg]
  intro s
  rw [dist_pi_le_iff P.costBound_nonneg]
  intro who
  rw [Real.dist_eq, zero_sub, abs_neg]
  obtain ⟨a, ha⟩ := P.exists_pure_fCoord_eq_T x 0 s who
  rw [← ha]
  exact P.abs_fCoord_zero_le_costBound x s who (P.pureAction a)
'''

if "abbrev CostEntry" not in text:
    marker = "\n/-- **Lemma 2.** The range of `β(x)` is bounded. -/"
    if marker not in text:
        marker = "\n/-- **Lemma 2.** The range of `β` is bounded. -/"
    if marker not in text:
        raise RuntimeError("cost infrastructure insertion marker not found")
    text = text.replace(marker, cost_infrastructure + marker, 1)

lemma2 = r'''  let B : ℝ := P.costBound /
    (1 - (P.maxDiscountNNReal : ℝ))
  refine ⟨B, ?_⟩
  intro x s who
  have hα : (P.maxDiscountNNReal : ℝ) < 1 := by
    change P.maxDiscount < 1
    exact P.maxDiscount_lt_one
  have hden : 0 < 1 - (P.maxDiscountNNReal : ℝ) := sub_pos.mpr hα
  have hfixed :
      dist (0 : P.R) (P.beta x) ≤
        dist (0 : P.R) (P.T x 0) /
          (1 - (P.maxDiscountNNReal : ℝ)) := by
    simpa [beta] using
      (P.theorem_1 x).dist_fixedPoint_le (0 : P.R)
  have hglobal : dist (0 : P.R) (P.beta x) ≤ B := by
    exact hfixed.trans
      ((div_le_div_iff_of_pos_right hden).2
        (P.dist_zero_T_zero_le_costBound x))
  calc
    |P.beta x s who| = dist ((0 : P.R) s who) (P.beta x s who) := by
      simp [Real.dist_eq]
    _ ≤ dist ((0 : P.R) s) (P.beta x s) :=
      dist_le_pi_dist ((0 : P.R) s) (P.beta x s) who
    _ ≤ dist (0 : P.R) (P.beta x) :=
      dist_le_pi_dist (0 : P.R) (P.beta x) s
    _ ≤ B := hglobal'''
replace_sorry("lemma_2", lemma2)

lemma3_cont = r'''  simpa [S] using
    P.continuous_T.comp (continuous_id.prodMk continuous_const)'''
replace_sorry("lemma_3_continuous", lemma3_cont)

lemma3_equi = r'''  letI : CompactSpace {v : P.R // v ∈ P.valueCube B} :=
    isCompact_iff_compactSpace.mp (P.valueCube_isCompact B)
  let F : P.X → {v : P.R // v ∈ P.valueCube B} → P.R :=
    fun x' v => P.S v.1 x'
  have hF : Continuous (Function.uncurry F) := by
    change Continuous (fun q :
      P.X × {v : P.R // v ∈ P.valueCube B} => P.T q.1 q.2.1)
    exact P.continuous_T.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  simpa [F] using Continuous.tendstoUniformly F hF x'''
replace_sorry("lemma_3_equicontinuous", lemma3_equi)

continuous_beta = r'''

/-- The fixed point `β(x)` depends continuously on the profile.  This is the
standard uniform-contraction parameter theorem, proved from the residual
estimate rather than by a subsequence argument. -/
theorem continuous_beta
    (P : Game ι) [Fintype P.State] [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [∀ s i, Fintype (P.Act s i)]
    [∀ s i, Nonempty (P.Act s i)] : Continuous P.beta := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hα : (P.maxDiscountNNReal : ℝ) < 1 := by
    change P.maxDiscount < 1
    exact P.maxDiscount_lt_one
  have hden : 0 < 1 - (P.maxDiscountNNReal : ℝ) := sub_pos.mpr hα
  have hcont := (P.lemma_3_continuous (P.beta x)).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδbound⟩ :=
    hcont (ε * (1 - (P.maxDiscountNNReal : ℝ))) (mul_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  intro x' hx'
  have hres := hδbound hx'
  have hnum :
      dist (P.beta x) (P.T x' (P.beta x)) <
        ε * (1 - (P.maxDiscountNNReal : ℝ)) := by
    simpa [dist_comm] using hres
  have hfixed :
      dist (P.beta x) (P.beta x') ≤
        dist (P.beta x) (P.T x' (P.beta x)) /
          (1 - (P.maxDiscountNNReal : ℝ)) :=
    (P.theorem_1 x').dist_le_of_fixedPoint
      (P.beta x) (P.T_beta x')
  calc
    dist (P.beta x') (P.beta x) = dist (P.beta x) (P.beta x') :=
      dist_comm _ _
    _ ≤ dist (P.beta x) (P.T x' (P.beta x)) /
          (1 - (P.maxDiscountNNReal : ℝ)) := hfixed
    _ < (ε * (1 - (P.maxDiscountNNReal : ℝ))) /
          (1 - (P.maxDiscountNNReal : ℝ)) :=
      (div_lt_div_iff_of_pos_right hden).2 hnum
    _ = ε := by field_simp [ne_of_gt hden]
'''

if "theorem continuous_beta" not in text:
    marker = "\n/-- **Lemma 4.** The graph of `β` is sequentially closed. -/"
    if marker not in text:
        raise RuntimeError("continuous_beta insertion marker not found")
    text = text.replace(marker, continuous_beta + marker, 1)

lemma4 = r'''  have hβ : Tendsto (fun n => P.beta (xn n)) atTop (𝓝 (P.beta x)) :=
    P.continuous_beta.continuousAt.tendsto.comp hx
  exact tendsto_nhds_unique hβ hv'''
replace_sorry("lemma_4", lemma4)

lemma5 = r'''  have hβ : Tendsto (fun n => P.beta (xn n)) atTop (𝓝 (P.beta x)) :=
    P.continuous_beta.continuousAt.tendsto.comp hx
  have htriple : Tendsto
      (fun n => (xn n, yn n, P.beta (xn n))) atTop
      (𝓝 (x, y, P.beta x)) :=
    hx.prodMk_nhds (hy.prodMk_nhds hβ)
  have hf : Tendsto
      (fun n => P.f (xn n) (yn n) (P.beta (xn n))) atTop
      (𝓝 (P.f x y (P.beta x))) :=
    P.property_a_continuous.continuousAt.tendsto.comp htriple
  have heq :
      (fun n => P.f (xn n) (yn n) (P.beta (xn n))) =
        fun n => P.beta (xn n) := by
    funext n
    simpa [phi] using hphi n
  rw [heq] at hf
  have hlimit : P.f x y (P.beta x) = P.beta x :=
    tendsto_nhds_unique hf hβ
  simpa [phi] using hlimit'''
replace_sorry("lemma_5", lemma5)

path.write_text(text, encoding="utf-8")
