import MathUE.Analysis.SignedMixedCurvatureAccount
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Order.Compact

/-! # Attained off-diagonal maximum and the packet's mixed-curvature bound -/

noncomputable section

namespace Math

open Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def boxMixedCurvatureValues (potential : (ι → ℝ) → ℝ) (box : Set (ι → ℝ)) : Set ℝ :=
  {value | ∃ point ∈ box, ∃ owner receiver, owner ≠ receiver ∧
    value = |coordinateMixedPartial potential point owner receiver|}

def boxMixedCurvatureSup (potential : (ι → ℝ) → ℝ) (box : Set (ι → ℝ)) : ℝ :=
  sSup (boxMixedCurvatureValues potential box)

/-- Off-diagonal means genuinely distinct coordinates. The maximum is
internally produced by compactness and finite maximization. -/
theorem exists_box_mixed_curvature_max [Nontrivial ι]
    (lower upper : ι → ℝ) (potential : (ι → ℝ) → ℝ) (domain : Set (ι → ℝ))
    (hwidth : ∀ who, lower who < upper who) (hopen : IsOpen domain)
    (hbox : Icc lower upper ⊆ domain) (hsmooth : ContDiffOn ℝ 2 potential domain) :
    ∃ point ∈ Icc lower upper, ∃ owner receiver, owner ≠ receiver ∧
      ∀ other ∈ Icc lower upper, ∀ first second, first ≠ second →
        |coordinateMixedPartial potential other first second| ≤
          |coordinateMixedPartial potential point owner receiver| := by
  classical
  let Index := {pair : ι × ι // pair.1 ≠ pair.2}
  obtain ⟨first, second, hne⟩ := exists_pair_ne ι
  let : Nonempty Index := ⟨⟨(first, second), hne⟩⟩
  let : Fintype Index := Fintype.ofFinite Index
  have hnonempty : (Icc lower upper).Nonempty :=
    ⟨lower, le_rfl, fun who => (hwidth who).le⟩
  have hmaxima : ∀ pair : Index, ∃ point ∈ Icc lower upper,
      IsMaxOn (fun input => |coordinateMixedPartial potential input pair.1.1 pair.1.2|)
        (Icc lower upper) point := by
    intro pair
    exact isCompact_Icc.exists_isMaxOn hnonempty
      ((coordinateMixedPartial_continuousOn potential domain hopen hsmooth
        pair.1.1 pair.1.2).mono hbox).abs
  choose point hpoint hmax using hmaxima
  let value := fun pair : Index =>
    |coordinateMixedPartial potential (point pair) pair.1.1 pair.1.2|
  obtain ⟨pair, _, hsup⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ) Finset.univ_nonempty value
  refine ⟨point pair, hpoint pair, pair.1.1, pair.1.2, pair.2, ?_⟩
  intro other hother first second hdistinct
  let otherPair : Index := ⟨(first, second), hdistinct⟩
  exact (hmax otherPair hother).trans (by
    change value otherPair ≤ value pair
    rw [← hsup]
    exact Finset.le_sup' value (Finset.mem_univ otherPair))

omit [Fintype ι] in
theorem boxMixedCurvatureSup_eq_of_maximum
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ) (owner receiver : ι)
    (hpoint : point ∈ Icc lower upper) (hne : owner ≠ receiver)
    (hmax : ∀ other ∈ Icc lower upper, ∀ first second, first ≠ second →
      |coordinateMixedPartial potential other first second| ≤
        |coordinateMixedPartial potential point owner receiver|) :
    boxMixedCurvatureSup potential (Icc lower upper) =
      |coordinateMixedPartial potential point owner receiver| := by
  have hmember : |coordinateMixedPartial potential point owner receiver| ∈
      boxMixedCurvatureValues potential (Icc lower upper) :=
    ⟨point, hpoint, owner, receiver, hne, rfl⟩
  have hbound : ∀ value ∈ boxMixedCurvatureValues potential (Icc lower upper),
      value ≤ |coordinateMixedPartial potential point owner receiver| := by
    rintro value ⟨other, hother, first, second, hdistinct, rfl⟩
    exact hmax other hother first second hdistinct
  exact le_antisymm (csSup_le ⟨_, hmember⟩ hbound)
    (le_csSup ⟨_, hbound⟩ hmember)

omit [Fintype ι] in
/-- The norm bound on a single actual coordinate-reset integral. -/
theorem abs_coordinateResetIntegral_le
    (lower upper minimum : ι → ℝ) (potential : (ι → ℝ) → ℝ) (width maximum : ℝ)
    (hminimum : minimum ∈ Icc lower upper)
    (hlength : ∀ who, upper who - lower who ≤ width)
    (hmaximum : 0 ≤ maximum)
    (hbound : ∀ point ∈ Icc lower upper, ∀ owner receiver, owner ≠ receiver →
      |coordinateMixedPartial potential point owner receiver| ≤ maximum)
    (owner receiver : ι) (hne : owner ≠ receiver) :
    |coordinateResetIntegral lower minimum potential owner receiver| ≤ maximum * width := by
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := lower owner) (b := minimum owner)
    (f := fun value =>
      coordinateMixedPartial potential (Function.update minimum owner value) owner receiver)
    (C := maximum) (by
      intro value hvalue
      have hclosed : value ∈ Icc (lower owner) (minimum owner) := by
        simpa only [uIcc_of_le (hminimum.1 owner)] using uIoc_subset_uIcc hvalue
      simpa only [Real.norm_eq_abs] using hbound
        (Function.update minimum owner value)
        (box_update_mem lower upper minimum hminimum owner value
          ⟨hclosed.1, hclosed.2.trans (hminimum.2 owner)⟩) owner receiver hne)
  have hlength' : |minimum owner - lower owner| ≤ width := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hminimum.1 owner))]
    exact (sub_le_sub_right (hminimum.2 owner) _).trans (hlength owner)
  have hintegral' : |coordinateResetIntegral lower minimum potential owner receiver| ≤
      maximum * |minimum owner - lower owner| := by
    simpa only [coordinateResetIntegral, Real.norm_eq_abs] using hintegral
  exact hintegral'.trans (mul_le_mul_of_nonneg_left hlength' hmaximum)

/-- Absolute values lose signs only here, after the signed account. The
number of terms is exactly n−1, never n or a count including the diagonal. -/
theorem abs_signedMixedCurvatureAccount_le
    (lower upper minimum : ι → ℝ) (face : ι → ι → ℝ) (weight : ι → ℝ)
    (potential : (ι → ℝ) → ℝ) (width maximum : ℝ)
    (hminimum : minimum ∈ Icc lower upper) (hwidth : 0 ≤ width)
    (hlength : ∀ who, upper who - lower who ≤ width)
    (hcoefficient : ∀ owner receiver, |minimum receiver - face owner receiver| ≤ width)
    (hweight : ∀ who, 0 ≤ weight who) (hweightSum : ∑ who, weight who = 1)
    (hmaximum : 0 ≤ maximum)
    (hbound : ∀ point ∈ Icc lower upper, ∀ owner receiver, owner ≠ receiver →
      |coordinateMixedPartial potential point owner receiver| ≤ maximum) :
    |signedMixedCurvatureAccount lower minimum face weight potential| ≤
      ((Fintype.card ι - 1 : ℕ) : ℝ) * width ^ 2 * maximum := by
  classical
  let bound := ((Fintype.card ι - 1 : ℕ) : ℝ) * width ^ 2 * maximum
  have hinner : ∀ owner,
      |∑ receiver ∈ Finset.univ.erase owner,
        (minimum receiver - face owner receiver) *
          coordinateResetIntegral lower minimum potential owner receiver| ≤ bound := by
    intro owner
    calc
      _ ≤ ∑ receiver ∈ Finset.univ.erase owner,
          |(minimum receiver - face owner receiver) *
            coordinateResetIntegral lower minimum potential owner receiver| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _receiver ∈ Finset.univ.erase owner, width ^ 2 * maximum := by
        apply Finset.sum_le_sum
        intro receiver hreceiver
        rw [abs_mul]
        have hintegral := abs_coordinateResetIntegral_le lower upper minimum potential
          width maximum hminimum hlength hmaximum hbound owner receiver
          (Ne.symm (Finset.mem_erase.mp hreceiver).1)
        have hproduct := mul_le_mul (hcoefficient owner receiver) hintegral
          (abs_nonneg _) hwidth
        nlinarith [hproduct]
      _ = bound := by
        simp only [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ owner), Finset.card_univ, bound]
        ring
  change |-(∑ owner, weight owner * _)| ≤ bound
  rw [abs_neg]
  calc
    _ ≤ ∑ owner, |weight owner *
        ∑ receiver ∈ Finset.univ.erase owner,
          (minimum receiver - face owner receiver) *
            coordinateResetIntegral lower minimum potential owner receiver| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ owner, weight owner * bound := by
      apply Finset.sum_le_sum
      intro owner _
      rw [abs_mul, abs_of_nonneg (hweight owner)]
      exact mul_le_mul_of_nonneg_left (hinner owner) (hweight owner)
    _ = bound := by rw [← Finset.sum_mul, hweightSum, one_mul]

/-- A supplied analytic simplex and positive face gain force the packet's
supremum estimate. The minimum and maximizing point are both produced here. -/
theorem exists_box_mixed_curvature_max_ge_of_face_drift [Nontrivial ι]
    (lower upper : ι → ℝ) (face : ι → ι → ℝ) (weight : ι → ℝ)
    (potential : (ι → ℝ) → ℝ) (domain : Set (ι → ℝ)) (gain width : ℝ)
    (hwidth : ∀ who, lower who < upper who)
    (hdiagonal : ∀ who, face who who = lower who)
    (hupper : ∀ owner receiver, face owner receiver ≤ upper receiver)
    (hweight : ∀ who, 0 ≤ weight who) (hweightSum : ∑ who, weight who = 1)
    (himage : ∀ receiver, 0 ≤ ∑ owner,
      (face owner receiver - lower receiver) * weight owner)
    (hopen : IsOpen domain) (hbox : Icc lower upper ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain) (hpositiveWidth : 0 < width)
    (hlength : ∀ who, upper who - lower who ≤ width)
    (hcoefficient : ∀ point ∈ Icc lower upper, ∀ owner receiver,
      |point receiver - face owner receiver| ≤ width)
    (hdrift : ∀ point ∈ Icc lower upper, ∀ owner, point owner = lower owner →
      gain ≤ fderiv ℝ potential point (point - face owner)) :
    ∃ point ∈ Icc lower upper, ∃ owner receiver, owner ≠ receiver ∧
      gain / (((Fintype.card ι - 1 : ℕ) : ℝ) * width ^ 2) ≤
        |coordinateMixedPartial potential point owner receiver| ∧
      boxMixedCurvatureSup potential (Icc lower upper) =
        |coordinateMixedPartial potential point owner receiver| := by
  obtain ⟨minimum, hminimum, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨lower, le_rfl, fun who => (hwidth who).le⟩ (hsmooth.continuousOn.mono hbox)
  have haccount := signedMixedCurvatureAccount_at_every_box_minimum lower upper face weight
    potential domain gain hwidth hdiagonal hupper hweight hweightSum himage hopen hbox
    hsmooth hdrift minimum hminimum hmin
  obtain ⟨point, hpoint, owner, receiver, hne, hmax⟩ :=
    exists_box_mixed_curvature_max lower upper potential domain hwidth hopen hbox hsmooth
  have hnorm := abs_signedMixedCurvatureAccount_le lower upper minimum face weight potential
    width |coordinateMixedPartial potential point owner receiver| hminimum hpositiveWidth.le
    hlength (hcoefficient minimum hminimum) hweight hweightSum (abs_nonneg _) hmax
  have hdenominator : 0 < ((Fintype.card ι - 1 : ℕ) : ℝ) * width ^ 2 := by
    have hcard : 0 < Fintype.card ι - 1 := Nat.sub_pos_of_lt (Fintype.one_lt_card (α := ι))
    exact mul_pos (by exact_mod_cast hcard) (sq_pos_of_pos hpositiveWidth)
  refine ⟨point, hpoint, owner, receiver, hne, ?_,
    boxMixedCurvatureSup_eq_of_maximum lower upper point potential owner receiver hpoint hne hmax⟩
  apply (div_le_iff₀ hdenominator).mpr
  have hgain := haccount.2.2.trans haccount.2.1
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    (hgain.trans (le_abs_self _)).trans hnorm

end Math
