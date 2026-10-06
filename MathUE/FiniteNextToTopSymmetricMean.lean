import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

omit [DecidableEq ι] in
theorem sum_prod_powersetCard_one (carrier : Finset ι) (coordinates : ι → ℝ) :
    (∑ coalition ∈ carrier.powersetCard 1, ∏ who ∈ coalition, coordinates who) =
      ∑ who ∈ carrier, coordinates who := by
  rw [Finset.powersetCard_one, Finset.sum_map]
  simp

theorem filter_properSubsets_card_eq_powersetCard
    (carrier : Finset ι) (degree : ℕ) (hpositive : 0 < degree)
    (hless : degree < carrier.card) :
    ((carrier.powerset.erase ∅).erase carrier).filter (fun coalition => coalition.card = degree) =
      carrier.powersetCard degree := by
  ext coalition
  constructor
  · intro hcoalition
    have hfiltered := Finset.mem_filter.mp hcoalition
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp
        (Finset.mem_erase.mp hfiltered.1).2).2, hfiltered.2⟩
  · intro hcoalition
    have hmember := Finset.mem_powersetCard.mp hcoalition
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
      Finset.mem_powerset.mpr hmember.1⟩⟩, hmember.2⟩
    · intro hequal
      have hcard := congrArg Finset.card hequal
      omega
    · intro hequal
      simp only [hequal, Finset.card_empty] at hmember
      omega

theorem sum_prod_powersetCard_pred (carrier : Finset ι) (coordinates : ι → ℝ)
    (hne : carrier.Nonempty) :
    (∑ coalition ∈ carrier.powersetCard (carrier.card - 1),
      ∏ who ∈ coalition, coordinates who) = value carrier coordinates := by
  unfold value
  symm
  apply Finset.sum_bij (fun who _ => carrier.erase who)
  · intro who hwho
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.erase_subset _ _, Finset.card_erase_of_mem hwho⟩
  · intro first hfirst second hsecond hequal
    by_contra hnequal
    have hmember : first ∈ carrier.erase second := Finset.mem_erase.mpr ⟨hnequal, hfirst⟩
    rw [← hequal] at hmember
    exact Finset.notMem_erase first carrier hmember
  · intro coalition hcoalition
    obtain ⟨hsubset, hcard⟩ := Finset.mem_powersetCard.mp hcoalition
    have hproper : coalition ⊂ carrier := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsubset, ?_⟩
      intro hequal
      have hpositive := Finset.card_pos.mpr hne
      have hsame := congrArg Finset.card hequal
      omega
    obtain ⟨who, hwho, hnot⟩ := Finset.exists_of_ssubset hproper
    refine ⟨who, hwho, ?_⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.subset_erase.mpr ⟨hsubset, hnot⟩
    · rw [Finset.card_erase_of_mem hwho, hcard]
  · intro who _
    rfl

theorem sum_prod_coefficient_le_two_layers
    (carrier : Finset ι) (hcard : 2 ≤ carrier.card) (coordinates : ι → ℝ)
    (hnonnegative : ∀ player ∈ carrier, 0 ≤ coordinates player)
    (coefficient : Finset ι → ℝ) (singletonCoefficient lastCoefficient : ℝ)
    (hbound : ∀ coalition ∈ (carrier.powerset.erase ∅).erase carrier,
      coefficient coalition ≤ (if coalition.card = 1 then singletonCoefficient else 0) +
        (if coalition.card = carrier.card - 1 then lastCoefficient else 0)) :
    (∑ coalition ∈ (carrier.powerset.erase ∅).erase carrier,
      (∏ player ∈ coalition, coordinates player) * coefficient coalition) ≤
      singletonCoefficient * (∑ player ∈ carrier, coordinates player) +
        lastCoefficient * value carrier coordinates := by
  let family := (carrier.powerset.erase ∅).erase carrier
  have hsingleLayer : (∑ coalition ∈ family,
      (∏ player ∈ coalition, coordinates player) *
        (if coalition.card = 1 then singletonCoefficient else 0)) =
      singletonCoefficient * (∑ player ∈ carrier, coordinates player) := by
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    change (∑ coalition ∈ ((carrier.powerset.erase ∅).erase carrier).filter
        (fun coalition => coalition.card = 1),
      (∏ player ∈ coalition, coordinates player) * singletonCoefficient) = _
    rw [filter_properSubsets_card_eq_powersetCard carrier 1 (by omega) (by omega),
      ← Finset.sum_mul, sum_prod_powersetCard_one, mul_comm]
  have hlastLayer : (∑ coalition ∈ family,
      (∏ player ∈ coalition, coordinates player) *
        (if coalition.card = carrier.card - 1 then lastCoefficient else 0)) =
      lastCoefficient * value carrier coordinates := by
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    change (∑ coalition ∈ ((carrier.powerset.erase ∅).erase carrier).filter
        (fun coalition => coalition.card = carrier.card - 1),
      (∏ player ∈ coalition, coordinates player) * lastCoefficient) = _
    rw [filter_properSubsets_card_eq_powersetCard carrier (carrier.card - 1)
      (by omega) (by omega), ← Finset.sum_mul,
      sum_prod_powersetCard_pred carrier coordinates (Finset.card_pos.mp (by omega)), mul_comm]
  calc
    _ ≤ ∑ coalition ∈ family, (∏ player ∈ coalition, coordinates player) *
        ((if coalition.card = 1 then singletonCoefficient else 0) +
          (if coalition.card = carrier.card - 1 then lastCoefficient else 0)) := by
      apply Finset.sum_le_sum
      intro coalition hcoalition
      apply mul_le_mul_of_nonneg_left (hbound coalition hcoalition)
      apply Finset.prod_nonneg
      intro player hplayer
      exact hnonnegative player ((Finset.mem_powerset.mp (Finset.mem_erase.mp
        (Finset.mem_erase.mp hcoalition).2).2) hplayer)
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, hsingleLayer, hlastLayer]

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

omit [Fintype ι] in
theorem value_univ_subtype (carrier : Finset ι) (coordinates : ι → ℝ) :
    value (Finset.univ : Finset carrier) (fun player => coordinates player.val) =
      value carrier coordinates := by
  calc
    _ = ∑ player : carrier, ∏ other ∈ carrier.erase player.val, coordinates other := by
      unfold value
      apply Finset.sum_congr rfl
      intro player _
      apply Finset.prod_bij (fun other _ => other.val)
      · intro other hother
        apply Finset.mem_erase.mpr
        refine ⟨?_, other.property⟩
        intro hequal
        exact (Finset.mem_erase.mp hother).1 (Subtype.ext hequal)
      · intro first _ second _ hequal
        exact Subtype.ext hequal
      · intro other hother
        refine ⟨⟨other, (Finset.mem_erase.mp hother).2⟩, ?_, rfl⟩
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_univ _⟩
        intro hequal
        exact (Finset.mem_erase.mp hother).1 (congrArg Subtype.val hequal)
      · intro other _
        rfl
    _ = _ := by
      unfold value
      exact Finset.sum_coe_sort carrier (fun player =>
        ∏ other ∈ carrier.erase player, coordinates other)

omit [Fintype ι] in
theorem value_finset_le_sum_pow_div_card_pow
    (carrier : Finset ι) (coordinates : ι → ℝ) (hcard : 3 ≤ carrier.card)
    (hnonnegative : ∀ player ∈ carrier, 0 ≤ coordinates player) :
    value carrier coordinates ≤
      (∑ player ∈ carrier, coordinates player) ^ (carrier.card - 1) /
        (carrier.card : ℝ) ^ (carrier.card - 2) := by
  have hbound := value_le_sum_pow_div_card_pow (fun player : carrier => coordinates player.val)
    (by simpa using hcard) (fun player => hnonnegative player.val player.property)
  simpa only [value_univ_subtype, Finset.sum_coe_sort, Fintype.card_coe] using hbound

omit [Fintype ι] [DecidableEq ι] in
theorem card_mul_ratio_rpow_lt_total_of_symmetric_bound
    (count : ℕ) (hcount : 3 ≤ count) (total symmetric delta tau : ℝ)
    (htotal : 0 < total) (hdelta : 0 < delta) (htau : 0 < tau)
    (hsymmetric : symmetric ≤ total ^ (count - 1) / (count : ℝ) ^ (count - 2))
    (hpremium : delta * total < tau * symmetric) :
    (count : ℝ) * (delta / tau) ^ ((count - 2 : ℕ) : ℝ)⁻¹ < total := by
  have hcountPositive : 0 < (count : ℝ) := by exact_mod_cast (by omega : 0 < count)
  have hcountNonzero : (count : ℝ) ≠ 0 := ne_of_gt hcountPositive
  have hdegreeNonzero : count - 2 ≠ 0 := by omega
  have hdegreePositive : 0 < ((count - 2 : ℕ) : ℝ) :=
    by exact_mod_cast (by omega : 0 < count - 2)
  have hpower : count - 1 = (count - 2) + 1 := by omega
  have hnormalize : total ^ (count - 1) / (count : ℝ) ^ (count - 2) =
      (total / count) ^ (count - 2) * total := by
    rw [hpower, pow_succ, div_pow]
    field_simp
  have hstrict := hpremium.trans_le (mul_le_mul_of_nonneg_left hsymmetric htau.le)
  rw [hnormalize] at hstrict
  have hcoefficient : delta < tau * (total / count) ^ (count - 2) := by
    exact lt_of_mul_lt_mul_right (by simpa only [mul_assoc] using hstrict) htotal.le
  have hratio : delta / tau < (total / count) ^ (count - 2) :=
    (div_lt_iff₀ htau).mpr (by simpa only [mul_comm] using hcoefficient)
  have hroot := Real.rpow_lt_rpow (div_pos hdelta htau).le hratio
    (inv_pos.mpr hdegreePositive)
  rw [Real.pow_rpow_inv_natCast (div_pos htotal hcountPositive).le hdegreeNonzero] at hroot
  simpa only [mul_comm] using (lt_div_iff₀ hcountPositive).mp hroot

end Math.NextToTopSymmetric
