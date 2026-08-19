from pathlib import Path
import re

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")

proofs = {
"property_a_continuous": r'''  classical
  apply continuous_pi
  intro s
  apply continuous_pi
  intro who
  unfold f
  simp_rw [P.fCoord_eq_sum]
  unfold oneStepCost
  simp_rw [expect_eq_sum]
  apply continuous_finsetSum Finset.univ
  intro a ha
  apply Continuous.mul
  · apply Continuous.mul
    · fun_prop
    · apply continuous_finsetProd (Finset.univ.erase who)
      intro i hi
      fun_prop
  · apply Continuous.add
    · exact continuous_const
    · apply Continuous.mul
      · exact continuous_const
      · apply continuous_finsetSum Finset.univ
        intro s' hs'
        apply Continuous.mul
        · exact continuous_const
        · fun_prop''',
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
        have hb := P.property_b x s who (P.pureAction a) v u
        simpa only [neg_sub_neg, abs_sub_comm] using hb)
    simpa only [neg_sub_neg, abs_sub_comm] using h
  calc
    |P.T x v s who - P.T x u s who|
        ≤ P.discount who * dist v u := hcoord
    _ ≤ P.maxDiscount * dist v u :=
      mul_le_mul_of_nonneg_right (P.discount_le_maxDiscount who) dist_nonneg
    _ = (P.maxDiscountNNReal : ℝ) * dist v u := rfl''',
"phi_isClosed": r'''  unfold phi
  have htriple : Continuous (fun y : P.X => (x, y, P.beta x)) := by
    fun_prop
  exact isClosed_eq (P.property_a_continuous.comp htriple) continuous_const''',
}

for name, proof in proofs.items():
    pattern = rf"(theorem {name}\b.*?:= by)\n  sorry"
    text, count = re.subn(pattern, lambda m: m.group(1) + "\n" + proof,
                          text, count=1, flags=re.S)
    if count != 1:
        raise RuntimeError(f"could not replace sorry proof: {name}")

path.write_text(text, encoding="utf-8")
