import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-! # The finite next-to-top elementary symmetric mean

The supplied averaging proof uses only the degree-(m-1) symmetric polynomial,
not the full Newton or Maclaurin inequality hierarchy. Its pair decomposition
and averaging identity feed a compact-maximum argument on a finite simplex.
The literal bound includes arbitrary finite inventories and boundary vectors.
-/

noncomputable section

namespace Math.NextToTopSymmetric

variable {ι : Type*} [DecidableEq ι]

def value (carrier : Finset ι) (coordinates : ι → ℝ) : ℝ :=
  ∑ who ∈ carrier, ∏ other ∈ carrier.erase who, coordinates other

theorem value_congr (carrier : Finset ι) {first second : ι → ℝ}
    (hequal : ∀ who ∈ carrier, first who = second who) :
    value carrier first = value carrier second := by
  apply Finset.sum_congr rfl
  intro who _
  apply Finset.prod_congr rfl
  intro other hother
  exact hequal other (Finset.mem_of_mem_erase hother)

theorem value_nonneg (carrier : Finset ι) (coordinates : ι → ℝ)
    (hnonneg : ∀ who ∈ carrier, 0 ≤ coordinates who) : 0 ≤ value carrier coordinates := by
  apply Finset.sum_nonneg
  intro who _
  apply Finset.prod_nonneg
  intro other hother
  exact hnonneg other (Finset.mem_of_mem_erase hother)

theorem value_pair_decomposition (rest : Finset ι) (coordinates : ι → ℝ)
    (first second : ι) (hfirst : first ∉ rest) (hsecond : second ∉ rest)
    (hne : first ≠ second) :
    value (insert first (insert second rest)) coordinates =
      (coordinates first + coordinates second) * (∏ who ∈ rest, coordinates who) +
        coordinates first * coordinates second * value rest coordinates := by
  have hsum :
      (∑ who ∈ rest, ∏ other ∈ (insert first (insert second rest)).erase who,
        coordinates other) = coordinates first * coordinates second * value rest coordinates := by
    rw [value, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro who hwho
    have hwhoFirst : first ≠ who := fun heq => hfirst (heq ▸ hwho)
    have hwhoSecond : second ≠ who := fun heq => hsecond (heq ▸ hwho)
    rw [Finset.erase_insert_of_ne hwhoFirst, Finset.erase_insert_of_ne hwhoSecond]
    rw [Finset.prod_insert (by simp [hfirst, hne]),
      Finset.prod_insert (by exact fun h => hsecond (Finset.mem_of_mem_erase h))]
    ring
  unfold value
  rw [Finset.sum_insert (by simp [hfirst, hne]), Finset.sum_insert hsecond]
  rw [Finset.erase_insert (by simp [hfirst, hne]), Finset.prod_insert hsecond,
    Finset.erase_insert_of_ne hne, Finset.erase_insert hsecond, Finset.prod_insert hfirst]
  rw [hsum]
  dsimp only [value]
  ring

def averagePair (coordinates : ι → ℝ) (first second : ι) : ι → ℝ :=
  Function.update (Function.update coordinates first ((coordinates first + coordinates second) / 2))
    second ((coordinates first + coordinates second) / 2)

theorem averagePair_on_rest (rest : Finset ι) (coordinates : ι → ℝ)
    (first second : ι) (hfirst : first ∉ rest) (hsecond : second ∉ rest) :
    ∀ who ∈ rest, averagePair coordinates first second who = coordinates who := by
  intro who hwho
  simp [averagePair, ne_of_mem_of_not_mem hwho hfirst, ne_of_mem_of_not_mem hwho hsecond]

theorem value_averagePair_sub (rest : Finset ι) (coordinates : ι → ℝ)
    (first second : ι) (hfirst : first ∉ rest) (hsecond : second ∉ rest)
    (hne : first ≠ second) :
    value (insert first (insert second rest)) (averagePair coordinates first second) -
        value (insert first (insert second rest)) coordinates =
      (coordinates first - coordinates second) ^ 2 / 4 * value rest coordinates := by
  rw [value_pair_decomposition rest _ first second hfirst hsecond hne,
    value_pair_decomposition rest _ first second hfirst hsecond hne]
  have hrest := averagePair_on_rest rest coordinates first second hfirst hsecond
  have hprod : (∏ who ∈ rest, averagePair coordinates first second who) =
      ∏ who ∈ rest, coordinates who := Finset.prod_congr rfl hrest
  rw [hprod, value_congr rest hrest]
  simp only [averagePair, Function.update_self, Function.update_of_ne hne]
  ring

theorem value_rest_pos_of_pair_value_pos (rest : Finset ι) (coordinates : ι → ℝ)
    (first second : ι) (hfirst : first ∉ rest) (hsecond : second ∉ rest)
    (hne : first ≠ second) (hrest : rest.Nonempty)
    (hnonneg : ∀ who ∈ rest, 0 ≤ coordinates who)
    (hpositive : 0 < value (insert first (insert second rest)) coordinates) :
    0 < value rest coordinates := by
  have hrestNonneg : ∀ who ∈ rest, 0 ≤ coordinates who := hnonneg
  have hvalueNonneg := value_nonneg rest coordinates hrestNonneg
  by_contra hnot
  have hzero : value rest coordinates = 0 := le_antisymm (le_of_not_gt hnot) hvalueNonneg
  have hprodNonneg : 0 ≤ ∏ who ∈ rest, coordinates who := Finset.prod_nonneg hrestNonneg
  have hprodZero : (∏ who ∈ rest, coordinates who) = 0 := by
    by_contra hnotZero
    have hprodPos : 0 < ∏ who ∈ rest, coordinates who :=
      lt_of_le_of_ne hprodNonneg (Ne.symm hnotZero)
    obtain ⟨who, hwho⟩ := hrest
    have herase := Finset.mul_prod_erase rest coordinates hwho
    have heraseNonneg : 0 ≤ ∏ other ∈ rest.erase who, coordinates other :=
      Finset.prod_nonneg (fun other hother => hrestNonneg other
        (Finset.mem_of_mem_erase hother))
    have herasePos : 0 < ∏ other ∈ rest.erase who, coordinates other := by
      by_contra hnotPos
      have hmul := mul_nonpos_of_nonneg_of_nonpos (hrestNonneg who hwho)
        (le_of_not_gt hnotPos)
      rw [herase] at hmul
      linarith
    have hterm := Finset.single_le_sum
      (f := fun other => ∏ coordinate ∈ rest.erase other, coordinates coordinate)
      (fun other _ =>
      Finset.prod_nonneg (fun coordinate hcoordinate => hrestNonneg coordinate
        (Finset.mem_of_mem_erase hcoordinate))) hwho
    change (∏ other ∈ rest.erase who, coordinates other) ≤ value rest coordinates at hterm
    rw [hzero] at hterm
    linarith
  rw [value_pair_decomposition rest coordinates first second hfirst hsecond hne,
    hzero, hprodZero] at hpositive
  norm_num at hpositive

theorem sum_averagePair (rest : Finset ι) (coordinates : ι → ℝ)
    (first second : ι) (hfirst : first ∉ rest) (hsecond : second ∉ rest)
    (hne : first ≠ second) :
    (∑ who ∈ insert first (insert second rest), averagePair coordinates first second who) =
      ∑ who ∈ insert first (insert second rest), coordinates who := by
  rw [Finset.sum_insert (by simp [hfirst, hne]), Finset.sum_insert hsecond,
    Finset.sum_insert (by simp [hfirst, hne]), Finset.sum_insert hsecond]
  rw [Finset.sum_congr rfl
    (averagePair_on_rest rest coordinates first second hfirst hsecond)]
  simp only [averagePair, Function.update_self, Function.update_of_ne hne]
  ring

variable [Fintype ι]

theorem continuous_value : Continuous (value (Finset.univ : Finset ι)) := by
  unfold value
  apply continuous_finsetSum
  intro who _
  apply continuous_finsetProd
  intro other _
  exact continuous_apply other

/-- The supplied compact-maximum averaging proof, including boundary vectors,
for every finite inventory of at least three coordinates. -/
theorem value_le_card_mul_mean_pow (coordinates : ι → ℝ)
    (hcard : 3 ≤ Fintype.card ι) (hnonneg : ∀ who, 0 ≤ coordinates who) :
    value Finset.univ coordinates ≤
      (Fintype.card ι : ℝ) * ((∑ who, coordinates who) / Fintype.card ι) ^
        (Fintype.card ι - 1) := by
  classical
  let total := ∑ who, coordinates who
  let count : ℝ := Fintype.card ι
  let uniform : ι → ℝ := fun _ => total / count
  let region : Set (ι → ℝ) := Set.Icc (fun _ => 0) (fun _ => total) ∩
    {point | ∑ who, point who = total}
  have htotal : 0 ≤ total := Finset.sum_nonneg (fun who _ => hnonneg who)
  have hcount : 0 < count := by dsimp [count]; exact_mod_cast (by omega : 0 < Fintype.card ι)
  have hcountOne : 1 ≤ count := by
    dsimp [count]
    exact_mod_cast (by omega : 1 ≤ Fintype.card ι)
  have huniform : uniform ∈ region := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro who
      exact div_nonneg htotal hcount.le
    · intro who
      apply (div_le_iff₀ hcount).mpr
      nlinarith
    · change (∑ _ : ι, total / count) = total
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change count * (total / count) = total
      field_simp [hcount.ne']
  have hcompact : IsCompact region := by
    apply isCompact_Icc.inter_right
    apply isClosed_eq _ continuous_const
    exact continuous_finsetSum _ (fun who _ => continuous_apply who)
  obtain ⟨maximum, hmaximum, hmax⟩ :=
    hcompact.exists_isMaxOn ⟨uniform, huniform⟩ continuous_value.continuousOn
  have hcoordinates : coordinates ∈ region := by
    refine ⟨⟨hnonneg, ?_⟩, rfl⟩
    intro who
    exact Finset.single_le_sum (fun other _ => hnonneg other) (Finset.mem_univ who)
  have huniformValue : value Finset.univ uniform =
      count * (total / count) ^ (Fintype.card ι - 1) := by
    unfold value
    simp [uniform, count, div_pow]
  have huniformNonneg : 0 ≤ value Finset.univ uniform :=
    value_nonneg _ uniform (fun who _ => div_nonneg htotal hcount.le)
  by_cases hpositive : 0 < value Finset.univ maximum
  · have hequal (first second : ι) : maximum first = maximum second := by
      by_cases hsame : first = second
      · exact congrArg maximum hsame
      let rest := (Finset.univ : Finset ι).erase first |>.erase second
      have hfirst : first ∉ rest := by simp [rest]
      have hsecond : second ∉ rest := by simp [rest]
      have hcarrier : insert first (insert second rest) = Finset.univ := by
        dsimp only [rest]
        rw [Finset.insert_erase (by simp [Ne.symm hsame]),
          Finset.insert_erase (Finset.mem_univ first)]
      have hrest : rest.Nonempty := by
        apply Finset.card_pos.mp
        have hfirstCard := Finset.card_erase_of_mem (Finset.mem_univ first)
        have hsecondCard := Finset.card_erase_of_mem
          (show second ∈ (Finset.univ : Finset ι).erase first by simp [Ne.symm hsame])
        simp only [Finset.card_univ] at hfirstCard
        change 0 < ((Finset.univ : Finset ι).erase first |>.erase second).card
        omega
      have hcoefficient : 0 < value rest maximum :=
        value_rest_pos_of_pair_value_pos rest maximum first second hfirst hsecond hsame hrest
          (fun who _ => hmaximum.1.1 who) (by simpa only [hcarrier] using hpositive)
      let averaged := averagePair maximum first second
      have havg : averaged ∈ region := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro who
          by_cases hwhoFirst : who = first
          · subst who
            simp only [averaged, averagePair, Function.update_of_ne hsame, Function.update_self]
            exact div_nonneg (add_nonneg (hmaximum.1.1 first) (hmaximum.1.1 second))
              (by norm_num)
          · by_cases hwhoSecond : who = second
            · subst who
              simp only [averaged, averagePair, Function.update_self]
              exact div_nonneg (add_nonneg (hmaximum.1.1 first) (hmaximum.1.1 second))
                (by norm_num)
            · simpa [averaged, averagePair, hwhoFirst, hwhoSecond] using hmaximum.1.1 who
        · intro who
          by_cases hwhoFirst : who = first
          · subst who
            simp only [averaged, averagePair, Function.update_of_ne hsame, Function.update_self]
            linarith [hmaximum.1.2 first, hmaximum.1.2 second]
          · by_cases hwhoSecond : who = second
            · subst who
              simp only [averaged, averagePair, Function.update_self]
              linarith [hmaximum.1.2 first, hmaximum.1.2 second]
            · simpa [averaged, averagePair, hwhoFirst, hwhoSecond] using hmaximum.1.2 who
        · have hsum := sum_averagePair rest maximum first second hfirst hsecond hsame
          rw [hcarrier] at hsum
          exact hsum.trans hmaximum.2
      have himprovement := value_averagePair_sub rest maximum first second hfirst hsecond hsame
      rw [hcarrier] at himprovement
      have hmaximal := hmax havg
      by_contra hneq
      have hsquare : 0 < (maximum first - maximum second) ^ 2 := sq_pos_of_ne_zero
        (sub_ne_zero.mpr hneq)
      have hgain : 0 < (maximum first - maximum second) ^ 2 / 4 * value rest maximum :=
        mul_pos (div_pos hsquare (by norm_num)) hcoefficient
      change value Finset.univ averaged - value Finset.univ maximum = _ at himprovement
      change value Finset.univ averaged ≤ value Finset.univ maximum at hmaximal
      linarith
    obtain ⟨first⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
    have hsum : count * maximum first = total := by
      calc
        _ = ∑ who : ι, maximum first := by simp [count]
        _ = ∑ who : ι, maximum who := Finset.sum_congr rfl (fun who _ => hequal first who)
        _ = total := hmaximum.2
    have hmean : maximum first = total / count := by
      apply (eq_div_iff hcount.ne').mpr
      simpa only [mul_comm] using hsum
    have hmaxUniform : maximum = uniform := by
      funext who
      exact (hequal who first).trans hmean
    have hbound := hmax hcoordinates
    rw [hmaxUniform, huniformValue] at hbound
    exact hbound
  · have hbound := (hmax hcoordinates).trans (le_of_not_gt hpositive)
    rw [huniformValue] at huniformNonneg
    exact hbound.trans huniformNonneg

/-- Literal next-to-top symmetric-mean bound used by the boxed Nash charge. -/
theorem value_le_sum_pow_div_card_pow (coordinates : ι → ℝ)
    (hcard : 3 ≤ Fintype.card ι) (hnonneg : ∀ who, 0 ≤ coordinates who) :
    value Finset.univ coordinates ≤ (∑ who, coordinates who) ^ (Fintype.card ι - 1) /
      (Fintype.card ι : ℝ) ^ (Fintype.card ι - 2) := by
  have hcount : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  have hpower : Fintype.card ι - 1 = (Fintype.card ι - 2) + 1 := by omega
  have hnormalize : (Fintype.card ι : ℝ) *
      ((∑ who, coordinates who) / Fintype.card ι) ^ (Fintype.card ι - 1) =
      (∑ who, coordinates who) ^ (Fintype.card ι - 1) /
        (Fintype.card ι : ℝ) ^ (Fintype.card ι - 2) := by
    rw [div_pow]
    rw [hpower, pow_succ]
    field_simp [hcount]
    rw [pow_succ]
    ring
  rw [← hnormalize]
  exact value_le_card_mul_mean_pow coordinates hcard hnonneg

end Math.NextToTopSymmetric
