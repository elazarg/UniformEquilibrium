import MathUE.RationalCalendarSearch
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Rational dyadic levels and finite logarithmic calendar sums

The accuracy search starts at zero and uses only exact rational comparisons.
Logarithms occur solely in the finite calendar estimates. No recurrence or
termination rank is supplied: the estimates aggregate literal scalar row counts.
-/

namespace Math

def rationalDyadicLevel (M : ℚ) (level : ℕ) : ℚ := M / 2 ^ level

@[simp] theorem rationalDyadicLevel_zero (M : ℚ) : rationalDyadicLevel M 0 = M := by
  simp [rationalDyadicLevel]

theorem rationalDyadicLevel_pos {M : ℚ} (hM : 0 < M) (level : ℕ) :
    0 < rationalDyadicLevel M level := by
  unfold rationalDyadicLevel
  positivity

theorem rationalDyadicLevel_succ (M : ℚ) (level : ℕ) :
    rationalDyadicLevel M (level + 1) = rationalDyadicLevel M level / 2 := by
  simp only [rationalDyadicLevel, pow_succ, div_div]

theorem rationalDyadicLevel_antitone {M : ℚ} (hM : 0 ≤ M) :
    Antitone (rationalDyadicLevel M) := by
  apply antitone_nat_of_succ_le
  intro level
  rw [rationalDyadicLevel_succ]
  have hnonnegative : 0 ≤ rationalDyadicLevel M level := by
    unfold rationalDyadicLevel
    positivity
  linarith

theorem rationalDyadicLevel_le {M : ℚ} (hM : 0 ≤ M) (level : ℕ) :
    rationalDyadicLevel M level ≤ M := by
  simpa only [rationalDyadicLevel_zero] using
    rationalDyadicLevel_antitone hM (Nat.zero_le level)

private theorem exists_rationalDyadicLevel_le {M accuracy : ℚ}
    (hM : 0 < M) (haccuracy : 0 < accuracy) :
    ∃ level, rationalDyadicLevel M level ≤ accuracy := by
  obtain ⟨level, _, hpower⟩ := exists_positive_rational_power_cutoff
    (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℚ) < 1)
    (div_pos haccuracy hM)
  refine ⟨level, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left hpower hM.le
  have hleft : M * (1 / 2 : ℚ) ^ level = rationalDyadicLevel M level := by
    unfold rationalDyadicLevel
    rw [div_pow, one_pow]
    ring
  have hright : M * (accuracy / M) = accuracy := by
    exact mul_div_cancel₀ accuracy hM.ne'
  rwa [hleft, hright] at hscaled

/-- First zero-allowed dyadic level passing the exact rational accuracy test. -/
def rationalDyadicAccuracyIndex (M accuracy : ℚ)
    (hM : 0 < M) (haccuracy : 0 < accuracy) : ℕ :=
  Nat.find (exists_rationalDyadicLevel_le hM haccuracy)

theorem rationalDyadicAccuracyIndex_spec {M accuracy : ℚ}
    (hM : 0 < M) (haccuracy : 0 < accuracy) (haccuracyM : accuracy ≤ M) :
    let level := rationalDyadicAccuracyIndex M accuracy hM haccuracy
    accuracy / 2 < rationalDyadicLevel M level ∧
      rationalDyadicLevel M level ≤ accuracy := by
  dsimp only
  have hupper := Nat.find_spec (exists_rationalDyadicLevel_le hM haccuracy)
  refine ⟨?_, hupper⟩
  generalize hindex : rationalDyadicAccuracyIndex M accuracy hM haccuracy = level
  cases level with
  | zero => simp only [rationalDyadicLevel_zero]; linarith
  | succ level =>
      have hbefore : ¬rationalDyadicLevel M level ≤ accuracy :=
        Nat.find_min (exists_rationalDyadicLevel_le hM haccuracy) (by
          change level < rationalDyadicAccuracyIndex M accuracy hM haccuracy
          rw [hindex]
          exact Nat.lt_succ_self level)
      rw [rationalDyadicLevel_succ]
      linarith [lt_of_not_ge hbefore]

theorem rationalDyadicAccuracyIndex_eq_zero {M : ℚ} (hM : 0 < M) :
    rationalDyadicAccuracyIndex M M hM hM = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' (exists_rationalDyadicLevel_le hM hM) (by simp)

/-- Scalar charged expenditure; semantic applications identify their actual
prefix expenditure with this literal rational expression. -/
def chargedCalendarDebtDrop (M working : ℚ) : ℚ :=
  ((working / 8) / (4 * M + working / 8)) * (working / 8) / 8

theorem chargedCalendarDebtDrop_pos {M working : ℚ}
    (hM : 0 < M) (hworking : 0 < working) :
    0 < chargedCalendarDebtDrop M working := by
  unfold chargedCalendarDebtDrop
  positivity

theorem chargedCalendarDebtDrop_eq {M working : ℚ}
    (hM : 0 < M) (hworking : 0 < working) :
    chargedCalendarDebtDrop M working = working ^ 2 / (512 * (4 * M + working / 8)) := by
  unfold chargedCalendarDebtDrop
  have hdenominator : 4 * M + working / 8 ≠ 0 := by positivity
  field_simp [hdenominator]
  ring

theorem chargedCalendarDebtDrop_lower {M working : ℚ}
    (hworking : 0 < working) (hworkingM : working ≤ M) :
    working ^ 2 / (2112 * M) ≤ chargedCalendarDebtDrop M working := by
  have hM := hworking.trans_le hworkingM
  rw [chargedCalendarDebtDrop_eq hM hworking]
  apply div_le_div_of_nonneg_left (sq_nonneg working)
  · positivity
  · linarith

noncomputable def chargedCalendarRows (M working debt : ℚ) : ℕ :=
  (Nat.ceil ((16 * (M : ℝ) / (working : ℝ)) *
    Real.log (8 * (M : ℝ) / (working : ℝ))) + 1) *
    (Nat.ceil (debt / chargedCalendarDebtDrop M working) + 1)

noncomputable def dyadicChargedCalendarBudget (M : ℚ) (players stages : ℕ) : ℕ :=
  if stages = 0 then 0 else
    chargedCalendarRows M M (players * M) +
      ∑ index ∈ Finset.range (stages - 1),
        chargedCalendarRows M (rationalDyadicLevel M (index + 1))
          (2 * rationalDyadicLevel M (index + 1))

@[simp] theorem dyadicChargedCalendarBudget_zero (M : ℚ) (players : ℕ) :
    dyadicChargedCalendarBudget M players 0 = 0 := by
  simp [dyadicChargedCalendarBudget]

@[simp] theorem dyadicChargedCalendarBudget_one (M : ℚ) (players : ℕ) :
    dyadicChargedCalendarBudget M players 1 = chargedCalendarRows M M (players * M) := by
  simp [dyadicChargedCalendarBudget]

theorem dyadicChargedCalendarBudget_succ (M : ℚ) (players stages : ℕ)
    (hstages : 0 < stages) :
    dyadicChargedCalendarBudget M players (stages + 1) =
      dyadicChargedCalendarBudget M players stages +
        chargedCalendarRows M (rationalDyadicLevel M stages)
          (2 * rationalDyadicLevel M stages) := by
  obtain ⟨stages, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hstages.ne'
  simp only [dyadicChargedCalendarBudget, Nat.succ_ne_zero, ite_false,
    Nat.succ_sub_one, Finset.sum_range_succ]
  rw [Nat.add_assoc]

theorem chargedCalendarRows_mono_debt (M working : ℚ) {first second : ℚ}
    (hworking : 0 < working) (hworkingM : working ≤ M) (hdebt : first ≤ second) :
    chargedCalendarRows M working first ≤ chargedCalendarRows M working second := by
  have hdrop := chargedCalendarDebtDrop_pos (hworking.trans_le hworkingM) hworking
  unfold chargedCalendarRows
  exact Nat.mul_le_mul_left _
    (Nat.add_le_add_right (Nat.ceil_mono (div_le_div_of_nonneg_right hdebt hdrop.le)) 1)

private theorem final_log_lower {M accuracy : ℝ} {players : ℕ}
    (haccuracy : 0 < accuracy) (haccuracyM : accuracy ≤ M) (hplayers : 0 < players) :
    (1 / 2 : ℝ) ≤ Real.log (16 * players * M / accuracy) := by
  have hn : (1 : ℝ) ≤ players := by exact_mod_cast Nat.succ_le_of_lt hplayers
  have hM : 0 < M := haccuracy.trans_le haccuracyM
  have hargument : (2 : ℝ) ≤ 16 * players * M / accuracy := by
    apply (le_div_iff₀ haccuracy).mpr
    nlinarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hargument
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  linarith

private theorem first_chargedCalendarRows_le {M : ℚ} {players : ℕ}
    (hM : 0 < M) (hplayers : 0 < players) :
    (chargedCalendarRows M M (players * M) : ℝ) ≤ 241000 * players := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hdrop : chargedCalendarDebtDrop M M = M / 2112 := by
    unfold chargedCalendarDebtDrop
    field_simp [hM.ne']
    ring
  have hratio : (players : ℚ) * M / chargedCalendarDebtDrop M M =
      ((2112 * players : ℕ) : ℚ) := by
    rw [hdrop]
    push_cast
    field_simp [hM.ne']
  have hcount : Nat.ceil ((players : ℚ) * M / chargedCalendarDebtDrop M M) + 1 =
      2112 * players + 1 := by rw [hratio, Nat.ceil_natCast]
  have hlog0 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log (8 : ℝ) ≤ 7 := by
    simpa only [show (8 : ℝ) - 1 = 7 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  have hceil := (Nat.ceil_lt_add_one
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hlog0)).le
  have hrows : ((Nat.ceil (16 * Real.log (8 : ℝ)) + 1 : ℕ) : ℝ) ≤ 114 := by
    push_cast
    linarith
  have hn : (1 : ℝ) ≤ players := by exact_mod_cast Nat.succ_le_of_lt hplayers
  have hfirst : ((2112 * players + 1 : ℕ) : ℝ) ≤ 2113 * players := by
    push_cast
    linarith
  unfold chargedCalendarRows
  rw [hcount]
  have hleft : (16 * (M : ℝ) / (M : ℝ)) *
        Real.log (8 * (M : ℝ) / (M : ℝ)) = 16 * Real.log (8 : ℝ) := by
    rw [mul_div_cancel_right₀ _ hMr.ne', mul_div_cancel_right₀ _ hMr.ne']
  rw [hleft, Nat.cast_mul]
  exact (mul_le_mul hrows hfirst (by positivity) (by norm_num)).trans (by nlinarith)

/-- Ceiling arithmetic for a later stage with incoming debt at most twice its level. -/
theorem chargedCalendarRows_later_le {M working accuracy : ℚ} {players : ℕ}
    (hworking : 0 < working) (hworkingM : working ≤ M)
    (haccuracy : 0 < accuracy) (haccuracyM : accuracy ≤ M)
    (haccuracyWorking : accuracy / 2 ≤ working) (hplayers : 0 < players) :
    (chargedCalendarRows M working (2 * working) : ℝ) ≤
      84520 * ((M : ℝ) / (working : ℝ)) ^ 2 *
        Real.log (16 * players * (M : ℝ) / (accuracy : ℝ)) := by
  let x := (M : ℝ) / (working : ℝ)
  let logarithm := Real.log (16 * players * (M : ℝ) / (accuracy : ℝ))
  have hwr : (0 : ℝ) < working := by exact_mod_cast hworking
  have hMr : (0 : ℝ) < M := by exact_mod_cast (hworking.trans_le hworkingM)
  have har : (0 : ℝ) < accuracy := by exact_mod_cast haccuracy
  have hx : 1 ≤ x := (one_le_div hwr).mpr (by exact_mod_cast hworkingM)
  have hlog : (1 / 2 : ℝ) ≤ logarithm :=
    final_log_lower har (by exact_mod_cast haccuracyM) hplayers
  have hx0 : 0 ≤ x := by linarith
  have hlog0Final : 0 ≤ logarithm := by linarith
  have hxLog : (1 / 2 : ℝ) ≤ x * logarithm := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 1) hlog0Final]
  have hargument : 8 * (M : ℝ) / (working : ℝ) ≤
      16 * players * (M : ℝ) / (accuracy : ℝ) := by
    have hden : (accuracy : ℝ) / 2 ≤ working := by exact_mod_cast haccuracyWorking
    have hn : (1 : ℝ) ≤ players := by exact_mod_cast Nat.succ_le_of_lt hplayers
    calc
      _ ≤ 8 * (M : ℝ) / ((accuracy : ℝ) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 16 * (M : ℝ) / (accuracy : ℝ) := by
        field_simp [har.ne']
        ring
      _ ≤ _ := by apply (div_le_div_iff_of_pos_right har).mpr; nlinarith
  have hsmallLog : Real.log (8 * (M : ℝ) / (working : ℝ)) ≤ logarithm :=
    Real.log_le_log (by positivity) hargument
  have hlog0 : 0 ≤ Real.log (8 * (M : ℝ) / (working : ℝ)) :=
    Real.log_nonneg (by rw [mul_div_assoc]; change 1 ≤ 8 * x; linarith)
  have hceilRows := (Nat.ceil_lt_add_one
    (mul_nonneg (by positivity : 0 ≤ 16 * (M : ℝ) / (working : ℝ)) hlog0)).le
  have hcoefficient : 16 * (M : ℝ) / (working : ℝ) = 16 * x := by
    dsimp only [x]
    ring
  have hrows : ((Nat.ceil ((16 * (M : ℝ) / (working : ℝ)) *
      Real.log (8 * (M : ℝ) / (working : ℝ))) + 1 : ℕ) : ℝ) ≤ 20 * x * logarithm := by
    have hscaled := mul_le_mul_of_nonneg_left hsmallLog (by positivity : 0 ≤ 16 * x)
    rw [hcoefficient] at hceilRows ⊢
    push_cast
    nlinarith
  have hdrop := chargedCalendarDebtDrop_pos (hworking.trans_le hworkingM) hworking
  have hdelta := chargedCalendarDebtDrop_lower hworking hworkingM
  have hratio : 2 * working / chargedCalendarDebtDrop M working ≤ 4224 * M / working := by
    apply (div_le_iff₀ hdrop).mpr
    have hMq : 0 < M := hworking.trans_le hworkingM
    have hscale := mul_le_mul_of_nonneg_left hdelta
      (show 0 ≤ 4224 * M / working by positivity)
    have hidentity : (4224 * M / working) * (working ^ 2 / (2112 * M)) =
        2 * working := by
      field_simp [hworking.ne', (hworking.trans_le hworkingM).ne']
      ring
    rw [hidentity] at hscale
    exact hscale
  have hceilFuel := (Nat.ceil_lt_add_one
    (show 0 ≤ 2 * working / chargedCalendarDebtDrop M working by positivity)).le
  have hfuelQ : ((Nat.ceil (2 * working / chargedCalendarDebtDrop M working) + 1 : ℕ) : ℚ) ≤
      4224 * M / working + 2 := by push_cast; linarith
  have hfuel : ((Nat.ceil (2 * working / chargedCalendarDebtDrop M working) + 1 : ℕ) : ℝ) ≤
      4226 * x := by
    have hcast : ((Nat.ceil (2 * working / chargedCalendarDebtDrop M working) + 1 : ℕ) : ℝ) ≤
        4224 * (M : ℝ) / (working : ℝ) + 2 := by exact_mod_cast hfuelQ
    have hcoefficientFuel : 4224 * (M : ℝ) / (working : ℝ) = 4224 * x := by
      dsimp only [x]
      ring
    rw [hcoefficientFuel] at hcast
    change _ ≤ 4224 * x + 2 at hcast
    linarith
  rw [chargedCalendarRows, Nat.cast_mul]
  have hscaled := mul_le_mul hrows hfuel (by positivity) (by positivity)
  dsimp only [x, logarithm] at hscaled ⊢
  nlinarith

theorem rationalDyadicLevel_ratio_eq {M : ℚ} (hM : 0 < M) (level : ℕ) :
    (M : ℝ) / (rationalDyadicLevel M level : ℝ) = (2 : ℝ) ^ level := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  simp only [rationalDyadicLevel, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  field_simp [hMr.ne', pow_ne_zero level (by norm_num : (2 : ℝ) ≠ 0)]

private theorem sum_four_powers_le (last : ℕ) :
    (∑ level ∈ Finset.range last, (4 : ℝ) ^ (level + 1)) ≤ 2 * 4 ^ last := by
  calc
    _ = (∑ level ∈ Finset.range last, (4 : ℝ) ^ level) * 4 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro level _
      exact pow_succ 4 level
    _ = ((4 ^ last - 1) / (4 - 1)) * 4 := by rw [geom_sum_eq (by norm_num)]
    _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) last]

/-- The displayed absolute-constant date bound for the finite sum of dyadic stages. -/
theorem dyadicChargedCalendarBudget_le_absolute
    {M accuracy : ℚ} {players last : ℕ}
    (haccuracy : 0 < accuracy) (haccuracyM : accuracy ≤ M) (hplayers : 0 < players)
    (hfinal : accuracy / 2 < rationalDyadicLevel M last) :
    (dyadicChargedCalendarBudget M players (last + 1) : ℝ) ≤
      1000000 * ((players : ℝ) + ((M : ℝ) / (accuracy : ℝ)) ^ 2 *
        Real.log (16 * players * (M : ℝ) / (accuracy : ℝ))) := by
  let logarithm := Real.log (16 * players * (M : ℝ) / (accuracy : ℝ))
  have hM := haccuracy.trans_le haccuracyM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : 0 ≤ logarithm :=
    (by have h := final_log_lower (M := (M : ℝ)) (accuracy := (accuracy : ℝ))
          (by exact_mod_cast haccuracy) (by exact_mod_cast haccuracyM) hplayers
        linarith)
  have hfirst := first_chargedCalendarRows_le hM hplayers
  have hsum : (∑ index ∈ Finset.range last,
      (chargedCalendarRows M (rationalDyadicLevel M (index + 1))
        (2 * rationalDyadicLevel M (index + 1)) : ℝ)) ≤
      84520 * logarithm * (∑ index ∈ Finset.range last, (4 : ℝ) ^ (index + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index hindex
    have hlevel : index + 1 ≤ last := Nat.succ_le_of_lt (Finset.mem_range.mp hindex)
    have hfinalLe := rationalDyadicLevel_antitone hM.le hlevel
    have hbound := chargedCalendarRows_later_le
      (rationalDyadicLevel_pos hM (index + 1)) (rationalDyadicLevel_le hM.le (index + 1))
      haccuracy haccuracyM (hfinal.le.trans hfinalLe) hplayers
    rw [rationalDyadicLevel_ratio_eq hM] at hbound
    have hpower : ((2 : ℝ) ^ (index + 1)) ^ 2 = 4 ^ (index + 1) := by
      rw [← pow_mul, mul_comm (index + 1) 2, pow_mul]
      norm_num
    simpa only [hpower, logarithm, mul_assoc, mul_comm, mul_left_comm] using hbound
  have hgeometry := mul_le_mul_of_nonneg_left (sum_four_powers_le last)
    (show 0 ≤ 84520 * logarithm by positivity)
  have hratio : (2 : ℝ) ^ last < 2 * (M : ℝ) / (accuracy : ℝ) := by
    rw [← rationalDyadicLevel_ratio_eq hM last]
    have hfinalR : (accuracy : ℝ) / 2 < (rationalDyadicLevel M last : ℝ) := by
      exact_mod_cast hfinal
    have har : (0 : ℝ) < accuracy := by exact_mod_cast haccuracy
    apply (div_lt_div_iff₀ (by exact_mod_cast rationalDyadicLevel_pos hM last) har).mpr
    nlinarith
  have hsquare : (4 : ℝ) ^ last ≤ 4 * ((M : ℝ) / (accuracy : ℝ)) ^ 2 := by
    rw [mul_div_assoc] at hratio
    have hpower : ((2 : ℝ) ^ last) ^ 2 = 4 ^ last := by
      rw [← pow_mul, mul_comm last 2, pow_mul]
      norm_num
    rw [← hpower]
    calc
      _ ≤ (2 * ((M : ℝ) / (accuracy : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) last) hratio.le 2
      _ = 4 * ((M : ℝ) / (accuracy : ℝ)) ^ 2 := by ring
  have hlast := mul_le_mul_of_nonneg_left hsquare
    (show 0 ≤ 169040 * logarithm by positivity)
  have hsumBound :
      (∑ index ∈ Finset.range last,
        (chargedCalendarRows M (rationalDyadicLevel M (index + 1))
          (2 * rationalDyadicLevel M (index + 1)) : ℝ)) ≤
      676160 * ((M : ℝ) / (accuracy : ℝ)) ^ 2 * logarithm := by nlinarith
  have htotal : (dyadicChargedCalendarBudget M players (last + 1) : ℝ) ≤
      241000 * players + 676160 * ((M : ℝ) / (accuracy : ℝ)) ^ 2 * logarithm := by
    rw [dyadicChargedCalendarBudget, ite_eq_right (Nat.succ_ne_zero last),
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_sum]
    exact add_le_add hfirst hsumBound
  have hplayersR : (0 : ℝ) ≤ players := Nat.cast_nonneg players
  have hpositiveTerm : 0 ≤ ((M : ℝ) / (accuracy : ℝ)) ^ 2 * logarithm := by positivity
  dsimp only [logarithm] at htotal hpositiveTerm ⊢
  nlinarith


/-- A scalar bound for the separately censored fresh solo EXIT. This compares
the existing logarithmic cutoff, not another power-search construction. -/
theorem soloLogCutoff_le_absolute
    {M accuracy hazard : ℝ} {players : ℕ}
    (haccuracy : 0 < accuracy) (haccuracyM : accuracy ≤ M) (hplayers : 0 < players)
    (hhazard1 : hazard < 1)
    (hfloor : accuracy / (32 * M) ≤ hazard) :
    1 + Real.log (2 * players * M / accuracy) / (-Real.log (1 - hazard)) ≤
      34 * (M / accuracy) ^ 2 * Real.log (16 * players * M / accuracy) := by
  let x := M / accuracy
  let logarithm := Real.log (16 * players * M / accuracy)
  have hM := haccuracy.trans_le haccuracyM
  have hn : (1 : ℝ) ≤ players := by exact_mod_cast Nat.succ_le_of_lt hplayers
  have hx : 1 ≤ x := (one_le_div haccuracy).mpr haccuracyM
  have hlog : (1 / 2 : ℝ) ≤ logarithm := final_log_lower haccuracy haccuracyM hplayers
  have hlog0 : 0 ≤ logarithm := by linarith
  have hargument : (1 : ℝ) ≤ 2 * players * M / accuracy := by
    apply (le_div_iff₀ haccuracy).mpr
    nlinarith
  have hsmallLog0 := Real.log_nonneg hargument
  have hsmallLog : Real.log (2 * players * M / accuracy) ≤ logarithm := by
    apply Real.log_le_log (by positivity)
    apply (div_le_div_iff_of_pos_right haccuracy).mpr
    nlinarith
  have hsurvival : 0 < 1 - hazard := by linarith
  have hden := Real.log_le_sub_one_of_pos hsurvival
  have hdenFloor : accuracy / (32 * M) ≤ -Real.log (1 - hazard) := by linarith
  have hratio := div_le_div_of_nonneg_left hsmallLog0
    (show 0 < accuracy / (32 * M) by positivity) hdenFloor
  have hidentity : Real.log (2 * players * M / accuracy) / (accuracy / (32 * M)) =
      32 * x * Real.log (2 * players * M / accuracy) := by
    dsimp only [x]
    field_simp [haccuracy.ne', hM.ne']
  rw [hidentity] at hratio
  have hscaled := mul_le_mul_of_nonneg_left hsmallLog (show 0 ≤ 32 * x by positivity)
  have hxSquare : x ≤ x ^ 2 := by nlinarith
  have hxLog : (1 / 2 : ℝ) ≤ x ^ 2 * logarithm := by
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ x ^ 2 - 1) hlog0]
  have hscaleSquare := mul_le_mul_of_nonneg_right hxSquare hlog0
  dsimp only [x, logarithm] at hratio hscaled hxLog hscaleSquare ⊢
  nlinarith

end Math
