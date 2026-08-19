from pathlib import Path
import re

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")

proofs = {
"property_a_continuous": r'''  classical
  unfold f fCoord oneStepCost actionPMF
  simp_rw [expect_eq_sum, pmfPi_apply, ENNReal.toReal_prod]
  simp only [stdSimplexEquiv_symm_apply, ofVector_toReal]
  fun_prop''',
"property_b": r'''  unfold fCoord oneStepCost
  rw [← expect_sub]
  refine abs_expect_le_of_abs_le _ _ (fun a => ?_)
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
    abs_of_nonneg (P.discount_pos who).le]
  apply mul_le_mul_of_nonneg_left _ (P.discount_pos who).le
  rw [← expect_sub]
  refine abs_expect_le_of_abs_le _ _ (fun s' => ?_)
  rw [← Real.dist_eq]
  exact (dist_le_pi_dist (v s') (u s') who).trans
    (dist_le_pi_dist v u s')''',
"property_c": r'''  unfold fCoord
  rw [pmfPi_update_bind, expect_bind,
    expect_stdSimplexEquiv_symm_eq_wsum]
  simp [pureAction]''',
"contractingWith_valueOperator": r'''  refine ⟨P.maxDiscountNNReal_lt_one,
    LipschitzWith.of_dist_le_mul (fun v u => ?_)⟩
  rw [dist_pi_le_iff (by positivity)]
  intro s
  rw [dist_pi_le_iff (by positivity)]
  intro who
  rw [Real.dist_eq]
  change |P.fCoord x s who (x (s, who)) v -
      P.fCoord x s who (x (s, who)) u| ≤
    (P.maxDiscountNNReal : ℝ) * dist v u
  calc
    |P.fCoord x s who (x (s, who)) v -
        P.fCoord x s who (x (s, who)) u|
        ≤ P.discount who * dist v u :=
          P.property_b x s who (x (s, who)) v u
    _ ≤ P.maxDiscount * dist v u :=
      mul_le_mul_of_nonneg_right (P.discount_le_maxDiscount who) dist_nonneg
    _ = (P.maxDiscountNNReal : ℝ) * dist v u := rfl''',
"lemma_1": r'''  have hc := P.contractingWith_valueOperator x
  let e := ContractingWith.fixedPoint (P.valueOperator x) hc
  refine ⟨e, ?_, ?_⟩
  · change P.valueOperator x e = e
    exact hc.fixedPoint_isFixedPt
  · intro u hu
    change P.valueOperator x u = u at hu
    exact hc.fixedPoint_unique hu''',
"T_le_fCoord": r'''  rw [P.property_c]
  calc
    P.T x v s who = wsum y (fun _ => P.T x v s who) :=
      (wsum_const y _).symm
    _ ≤ wsum y
        (fun a => P.fCoord x s who (P.pureAction a) v) := by
      apply wsum_le_wsum
      intro a
      unfold T
      have h := Finset.le_sup'
        (f := fun b : P.Act s who =>
          -P.fCoord x s who (P.pureAction b) v)
        (Finset.mem_univ a)
      linarith''',
"exists_pure_fCoord_eq_T": r'''  obtain ⟨a, -, ha⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun a : P.Act s who =>
        -P.fCoord x s who (P.pureAction a) v)
  refine ⟨a, ?_⟩
  unfold T
  rw [ha]
  ring''',
"theorem_1": r'''  refine ⟨P.maxDiscountNNReal_lt_one,
    LipschitzWith.of_dist_le_mul (fun v u => ?_)⟩
  rw [dist_pi_le_iff (by positivity)]
  intro s
  rw [dist_pi_le_iff (by positivity)]
  intro who
  rw [Real.dist_eq]
  have hcoord :
      |P.T x v s who - P.T x u s who| ≤
        P.discount who * dist v u := by
    unfold T
    have h := Math.Finset.abs_sup'_sub_sup'_le_const
      (indices := (Finset.univ : Finset (P.Act s who)))
      Finset.univ_nonempty
      (fun a => -P.fCoord x s who (P.pureAction a) v)
      (fun a => -P.fCoord x s who (P.pureAction a) u)
      (bound := P.discount who * dist v u)
      (fun a _ => by
        simpa [abs_sub_comm] using
          P.property_b x s who (P.pureAction a) v u)
    simpa [abs_sub_comm] using h
  calc
    |P.T x v s who - P.T x u s who|
        ≤ P.discount who * dist v u := hcoord
    _ ≤ P.maxDiscount * dist v u :=
      mul_le_mul_of_nonneg_right (P.discount_le_maxDiscount who) dist_nonneg
    _ = (P.maxDiscountNNReal : ℝ) * dist v u := rfl''',
"corollary_1": r'''  have hc := P.theorem_1 x
  exact ⟨ContractingWith.fixedPoint (P.T x) hc,
    hc.fixedPoint_isFixedPt,
    fun v hv => hc.fixedPoint_unique hv⟩''',
"corollary_2": r'''  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x u v huv
  have hL := (P.theorem_1 x).toLipschitzWith.dist_le_mul u v
  have hα0 : 0 ≤ (P.maxDiscountNNReal : ℝ) :=
    P.maxDiscountNNReal.property
  have hα1 : (P.maxDiscountNNReal : ℝ) < 1 := by
    change P.maxDiscount < 1
    exact P.maxDiscount_lt_one
  calc
    dist (P.T x u) (P.T x v)
        ≤ (P.maxDiscountNNReal : ℝ) * dist u v := hL
    _ < (1 : ℝ) * ε := by nlinarith [dist_nonneg]
    _ = ε := one_mul ε''',
"phi_nonempty": r'''  have hmin : ∀ p : P.Agent,
      ∃ a : P.AgentAction p,
        P.fCoord x p.1 p.2 (P.pureAction a) (P.beta x) =
          P.T x (P.beta x) p.1 p.2 := by
    intro p
    exact P.exists_pure_fCoord_eq_T x (P.beta x) p.1 p.2
  choose a ha using hmin
  let y : P.X := fun p => P.pureAction (a p)
  refine ⟨y, ?_⟩
  unfold phi
  funext s who
  change P.fCoord x s who (P.pureAction (a (s, who))) (P.beta x) =
    P.beta x s who
  rw [ha (s, who)]
  exact congrFun (congrFun (P.T_beta x) s) who''',
"phi_segment": r'''  unfold phi at hy hz ⊢
  funext s who
  have hyc := congrFun (congrFun hy s) who
  have hzc := congrFun (congrFun hz s) who
  change P.fCoord x s who (y (s, who)) (P.beta x) =
    P.beta x s who at hyc
  change P.fCoord x s who (z (s, who)) (P.beta x) =
    P.beta x s who at hzc
  change P.fCoord x s who
      (stdSimplex.mix t ht0 ht1 (y (s, who)) (z (s, who)))
      (P.beta x) = P.beta x s who
  calc
    P.fCoord x s who
        (stdSimplex.mix t ht0 ht1 (y (s, who)) (z (s, who)))
        (P.beta x)
        = wsum (stdSimplex.mix t ht0 ht1
            (y (s, who)) (z (s, who)))
            (fun a => P.fCoord x s who (P.pureAction a) (P.beta x)) :=
          P.property_c x s who _ (P.beta x)
    _ = t * wsum (y (s, who))
          (fun a => P.fCoord x s who (P.pureAction a) (P.beta x)) +
        (1 - t) * wsum (z (s, who))
          (fun a => P.fCoord x s who (P.pureAction a) (P.beta x)) := by
          rw [wsum_mix]
    _ = t * P.fCoord x s who (y (s, who)) (P.beta x) +
        (1 - t) * P.fCoord x s who (z (s, who)) (P.beta x) := by
          rw [← P.property_c, ← P.property_c]
    _ = P.beta x s who := by rw [hyc, hzc]; ring''',
"phi_isClosed": r'''  unfold phi
  have hcont : Continuous (fun y : P.X => P.f x y (P.beta x)) := by
    exact P.property_a_continuous.comp
      (continuous_const.prodMk
        (continuous_id.prodMk continuous_const))
  exact isClosed_eq hcont continuous_const''',
}

for name, proof in proofs.items():
    pattern = rf"(theorem {re.escape(name)}\b.*?:= by)\n  sorry"
    text, count = re.subn(pattern, lambda m: m.group(1) + "\n" + proof,
                          text, count=1, flags=re.S)
    if count == 0 and f"theorem {name}" not in text:
        raise RuntimeError(f"theorem not found: {name}")

path.write_text(text, encoding="utf-8")
