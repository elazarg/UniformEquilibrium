from pathlib import Path

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")

property_old = '''/-- Property (a): `f` is continuous in all three finite-dimensional
variables. -/
theorem property_a_continuous
    (P : Game ι) [Fintype P.State] [Fintype ι] [DecidableEq ι]
    [∀ s i, Fintype (P.Act s i)] :
    Continuous (fun q : P.X × P.X × P.R => P.f q.1 q.2.1 q.2.2) := by
  classical
  unfold f fCoord oneStepCost actionPMF
  simp_rw [expect_eq_sum, pmfPi_apply, ENNReal.toReal_prod]
  simp only [stdSimplexEquiv_symm_apply, ofVector_toReal]
  fun_prop
'''
property_new = '''/-- Finite-coordinate form of equation (6). -/
theorem fCoord_eq_sum
    (P : Game ι) [Fintype P.State] [Fintype ι] [DecidableEq ι]
    [∀ s i, Fintype (P.Act s i)]
    (x : P.X) (s : P.State) (who : ι)
    (y : stdSimplex ℝ (P.Act s who)) (e : P.R) :
    P.fCoord x s who y e =
      ∑ a : P.JointActionAt s,
        (y (a who) *
          ∏ i ∈ Finset.univ.erase who, x (s, i) (a i)) *
            P.oneStepCost e s a who := by
  classical
  unfold fCoord
  rw [expect_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [pmfPi_apply_update_family, ENNReal.toReal_mul,
    ENNReal.toReal_prod]
  simp [actionPMF_apply_toReal, stdSimplexEquiv_symm_apply,
    ofVector_toReal]

/-- Property (a): `f` is continuous in all three finite-dimensional
variables. -/
theorem property_a_continuous
    (P : Game ι) [Fintype P.State] [Fintype ι] [DecidableEq ι]
    [∀ s i, Fintype (P.Act s i)] :
    Continuous (fun q : P.X × P.X × P.R => P.f q.1 q.2.1 q.2.2) := by
  classical
  apply continuous_pi
  intro s
  apply continuous_pi
  intro who
  simp_rw [P.fCoord_eq_sum]
  unfold oneStepCost
  simp_rw [expect_eq_sum]
  fun_prop
'''
if property_old not in text:
    raise RuntimeError("property_a block not found")
text = text.replace(property_old, property_new, 1)

inner_old = '''      (fun a _ => by
        simpa [abs_sub_comm] using
          P.property_b x s who (P.pureAction a) v u)
    simpa [abs_sub_comm] using h
'''
inner_new = '''      (fun a _ => by
        have hb := P.property_b x s who (P.pureAction a) v u
        calc
          |-P.fCoord x s who (P.pureAction a) v +
              P.fCoord x s who (P.pureAction a) u| =
              |P.fCoord x s who (P.pureAction a) v -
                P.fCoord x s who (P.pureAction a) u| := by
                rw [show
                  -P.fCoord x s who (P.pureAction a) v +
                      P.fCoord x s who (P.pureAction a) u =
                    -(P.fCoord x s who (P.pureAction a) v -
                      P.fCoord x s who (P.pureAction a) u) by ring,
                  abs_neg]
          _ ≤ P.discount who * dist v u := hb)
    calc
      |(-Finset.sup' Finset.univ Finset.univ_nonempty
            (fun a : P.Act s who =>
              -P.fCoord x s who (P.pureAction a) v)) +
          Finset.sup' Finset.univ Finset.univ_nonempty
            (fun a : P.Act s who =>
              -P.fCoord x s who (P.pureAction a) u)| =
          |Finset.sup' Finset.univ Finset.univ_nonempty
              (fun a : P.Act s who =>
                -P.fCoord x s who (P.pureAction a) v) -
            Finset.sup' Finset.univ Finset.univ_nonempty
              (fun a : P.Act s who =>
                -P.fCoord x s who (P.pureAction a) u)| := by
            rw [show
              (-Finset.sup' Finset.univ Finset.univ_nonempty
                  (fun a : P.Act s who =>
                    -P.fCoord x s who (P.pureAction a) v)) +
                Finset.sup' Finset.univ Finset.univ_nonempty
                  (fun a : P.Act s who =>
                    -P.fCoord x s who (P.pureAction a) u) =
              -(Finset.sup' Finset.univ Finset.univ_nonempty
                  (fun a : P.Act s who =>
                    -P.fCoord x s who (P.pureAction a) v) -
                Finset.sup' Finset.univ Finset.univ_nonempty
                  (fun a : P.Act s who =>
                    -P.fCoord x s who (P.pureAction a) u)) by ring,
              abs_neg]
      _ ≤ P.discount who * dist v u := h
'''
if inner_old not in text:
    raise RuntimeError("theorem_1 sign block not found")
text = text.replace(inner_old, inner_new, 1)

cor_old = '''  calc
    dist (P.T x u) (P.T x v)
        ≤ (P.maxDiscountNNReal : ℝ) * dist u v := hL
    _ < (1 : ℝ) * ε := by nlinarith [dist_nonneg]
    _ = ε := one_mul ε
'''
cor_new = '''  have hdist : 0 ≤ dist u v := dist_nonneg
  calc
    dist (P.T x u) (P.T x v)
        ≤ (P.maxDiscountNNReal : ℝ) * dist u v := hL
    _ ≤ (1 : ℝ) * dist u v :=
      mul_le_mul_of_nonneg_right hα1.le hdist
    _ < (1 : ℝ) * ε := mul_lt_mul_of_pos_left huv zero_lt_one
    _ = ε := one_mul ε
'''
if cor_old not in text:
    raise RuntimeError("corollary_2 block not found")
text = text.replace(cor_old, cor_new, 1)

bound_old = '''/-- A uniform finite bound on the cost table. -/
def costBound
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [∀ s i, Fintype (P.Act s i)] : ℝ := by
  classical
  exact ∑ s : P.State,
    letI : ∀ i, Fintype (P.Act s i) := fun i => inferInstance
    ∑ a : P.JointActionAt s, ∑ who : ι, |P.cost s a who|
'''
bound_new = '''/-- The contribution of one state to a uniform finite cost bound. -/
def stateCostBound
    (P : Game ι) [Fintype ι]
    [∀ s i, Fintype (P.Act s i)] (s : P.State) : ℝ := by
  classical
  letI : ∀ i, Fintype (P.Act s i) := fun i => inferInstance
  exact ∑ a : P.JointActionAt s, ∑ who : ι, |P.cost s a who|

/-- A uniform finite bound on the cost table. -/
def costBound
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [∀ s i, Fintype (P.Act s i)] : ℝ :=
  ∑ s : P.State, P.stateCostBound s
'''
if bound_old not in text:
    raise RuntimeError("costBound block not found")
text = text.replace(bound_old, bound_new, 1)

path.write_text(text, encoding="utf-8")
