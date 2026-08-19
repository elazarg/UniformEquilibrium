from pathlib import Path

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")

old = '''  apply continuous_pi
  intro who
  simp_rw [P.fCoord_eq_sum]
'''
new = '''  apply continuous_pi
  intro who
  unfold f
  simp_rw [P.fCoord_eq_sum]
'''
if old not in text:
    raise RuntimeError("property_a unfolding anchor not found")
text = text.replace(old, new, 1)

old = '''      (fun a _ => by
        have hb := P.property_b x s who (P.pureAction a) v u
        calc
'''
new = '''      (fun a _ => by
        change
          |-P.fCoord x s who (P.pureAction a) v +
              P.fCoord x s who (P.pureAction a) u| ≤
            P.discount who * dist v u
        have hb := P.property_b x s who (P.pureAction a) v u
        calc
'''
if old not in text:
    raise RuntimeError("inner contraction change anchor not found")
text = text.replace(old, new, 1)

old = '''          _ ≤ P.discount who * dist v u := hb)
    calc
      |(-Finset.sup' Finset.univ Finset.univ_nonempty
'''
new = '''          _ ≤ P.discount who * dist v u := hb)
    change
      |(-Finset.sup' Finset.univ Finset.univ_nonempty
            (fun a : P.Act s who =>
              -P.fCoord x s who (P.pureAction a) v)) +
          Finset.sup' Finset.univ Finset.univ_nonempty
            (fun a : P.Act s who =>
              -P.fCoord x s who (P.pureAction a) u)| ≤
        P.discount who * dist v u
    calc
      |(-Finset.sup' Finset.univ Finset.univ_nonempty
'''
if old not in text:
    raise RuntimeError("outer contraction change anchor not found")
text = text.replace(old, new, 1)

bound_start = text.index('/-- The contribution of one state to a uniform finite cost bound. -/')
bound_end = text.index('/-- **Lemma 2.**', bound_start)
bound_new = '''/-- A finite index for one entry of the paper's cost table. -/
abbrev CostEntry (P : Game ι) :=
  Σ s : P.State, P.JointActionAt s × ι

/-- Absolute value of the cost-table entry selected by `entry`. -/
def costCoordinate (P : Game ι) (entry : P.CostEntry) : ℝ :=
  |P.cost entry.1 entry.2.1 entry.2.2|

/-- An arbitrary finite upper bound supplied by finiteness of the cost table. -/
def rawCostBound
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [∀ s i, Fintype (P.Act s i)] : ℝ :=
  Classical.choose
    (Math.Probability.exists_abs_bound_of_finite
      (P.costCoordinate : P.CostEntry → ℝ))

/-- A nonnegative uniform finite bound on the cost table. -/
def costBound
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [∀ s i, Fintype (P.Act s i)] : ℝ :=
  max P.rawCostBound 0

theorem costCoordinate_le_rawCostBound
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [∀ s i, Fintype (P.Act s i)] (entry : P.CostEntry) :
    P.costCoordinate entry ≤ P.rawCostBound :=
  Classical.choose_spec
    (Math.Probability.exists_abs_bound_of_finite
      (P.costCoordinate : P.CostEntry → ℝ)) entry

theorem costBound_nonneg
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [∀ s i, Fintype (P.Act s i)] :
    0 ≤ P.costBound :=
  le_max_right _ _

theorem abs_cost_le_costBound
    (P : Game ι) [Fintype P.State] [Fintype ι]
    [∀ s i, Fintype (P.Act s i)]
    (s : P.State) (a : P.JointActionAt s) (who : ι) :
    |P.cost s a who| ≤ P.costBound := by
  exact (P.costCoordinate_le_rawCostBound ⟨s, (a, who)⟩).trans
    (le_max_left _ _)

'''
text = text[:bound_start] + bound_new + text[bound_end:]

path.write_text(text, encoding="utf-8")
