import MathUE.Analysis.CoordinateResetFTC
import Mathlib.Algebra.BigOperators.Pi

/-! # The signed coordinate-reset mixed-curvature account

The simplex is an analytic input, not a homogeneous LCP solution. All
closed-box minima, including upper-face minima, satisfy the account.
-/

noncomputable section

namespace Math

open Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def lowerBoundaryMultiplier (lower minimum : ι → ℝ)
    (potential : (ι → ℝ) → ℝ) (receiver : ι) : ℝ :=
  if minimum receiver = lower receiver then coordinatePartial potential minimum receiver else 0

def coordinateResetIntegral (lower minimum : ι → ℝ)
    (potential : (ι → ℝ) → ℝ) (owner receiver : ι) : ℝ :=
  ∫ value in (lower owner)..(minimum owner),
    coordinateMixedPartial potential (Function.update minimum owner value) owner receiver

def signedMixedCurvatureAccount (lower minimum : ι → ℝ) (face : ι → ι → ℝ)
    (weight : ι → ℝ) (potential : (ι → ℝ) → ℝ) : ℝ :=
  -∑ owner, weight owner * ∑ receiver ∈ Finset.univ.erase owner,
    (minimum receiver - face owner receiver) *
      coordinateResetIntegral lower minimum potential owner receiver

def lowerBoundaryMatrixContribution (lower minimum : ι → ℝ) (face : ι → ι → ℝ)
    (weight : ι → ℝ) (potential : (ι → ℝ) → ℝ) : ℝ :=
  ∑ receiver, lowerBoundaryMultiplier lower minimum potential receiver *
    ∑ owner, (face owner receiver - lower receiver) * weight owner

theorem fderiv_eq_sum_coordinatePartial
    (potential : (ι → ℝ) → ℝ) (point direction : ι → ℝ) :
    fderiv ℝ potential point direction =
      ∑ receiver, coordinatePartial potential point receiver * direction receiver := by
  calc
    _ = fderiv ℝ potential point
        (∑ receiver, direction receiver • Pi.single receiver 1) :=
      congrArg (fderiv ℝ potential point) (pi_eq_sum_univ' direction)
    _ = _ := by simp [map_sum, map_smul, coordinatePartial, mul_comm]

/-- The gradient contribution at a box minimum. Upper-bound coordinates
have nonpositive partials and nonnegative payoff coefficients; they are not
silently treated as interior stationary coordinates. -/
theorem box_minimum_erased_gradient_le
    (lower upper minimum : ι → ℝ) (face : ι → ι → ℝ)
    (potential : (ι → ℝ) → ℝ)
    (hwidth : ∀ who, lower who < upper who)
    (hdiagonal : ∀ who, face who who = lower who)
    (hupper : ∀ owner receiver, face owner receiver ≤ upper receiver)
    (hminimum : minimum ∈ Icc lower upper)
    (hmin : IsMinOn potential (Icc lower upper) minimum)
    (hdiff : DifferentiableAt ℝ potential minimum) (owner : ι) :
    (∑ receiver ∈ Finset.univ.erase owner,
      coordinatePartial potential minimum receiver * (minimum receiver - face owner receiver)) ≤
      -∑ receiver, lowerBoundaryMultiplier lower minimum potential receiver *
        (face owner receiver - lower receiver) := by
  classical
  have hsign := box_minimum_coordinatePartial_signs lower upper minimum potential
    hwidth hminimum hmin hdiff
  have hterm : ∀ receiver,
      coordinatePartial potential minimum receiver * (minimum receiver - face owner receiver) ≤
        -(lowerBoundaryMultiplier lower minimum potential receiver *
          (face owner receiver - lower receiver)) := by
    intro receiver
    by_cases hbottom : minimum receiver = lower receiver
    · simp only [lowerBoundaryMultiplier, ite_eq_left hbottom]
      rw [hbottom]
      ring_nf
      exact le_rfl
    · simp only [lowerBoundaryMultiplier, ite_eq_right hbottom, zero_mul, neg_zero]
      by_cases htop : minimum receiver = upper receiver
      · exact mul_nonpos_of_nonpos_of_nonneg ((hsign receiver).2.2 htop)
          (by rw [htop]; exact sub_nonneg.mpr (hupper owner receiver))
      · rw [(hsign receiver).2.1
          (lt_of_le_of_ne (hminimum.1 receiver) (Ne.symm hbottom))
          (lt_of_le_of_ne (hminimum.2 receiver) htop), zero_mul]
  calc
    _ ≤ ∑ receiver ∈ Finset.univ.erase owner,
        -(lowerBoundaryMultiplier lower minimum potential receiver *
          (face owner receiver - lower receiver)) :=
      Finset.sum_le_sum fun receiver _ => hterm receiver
    _ = -∑ receiver, lowerBoundaryMultiplier lower minimum potential receiver *
        (face owner receiver - lower receiver) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ owner)]
      simp [hdiagonal owner]

/-- The literal face derivative expanded using the exact reset FTC identity. -/
theorem coordinate_reset_face_drift_eq
    (lower upper minimum : ι → ℝ) (face : ι → ι → ℝ)
    (potential : (ι → ℝ) → ℝ) (domain : Set (ι → ℝ))
    (hopen : IsOpen domain) (hbox : Icc lower upper ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain)
    (hminimum : minimum ∈ Icc lower upper)
    (hdiagonal : ∀ who, face who who = lower who) (owner : ι) :
    fderiv ℝ potential (Function.update minimum owner (lower owner))
      (Function.update minimum owner (lower owner) - face owner) =
      (∑ receiver ∈ Finset.univ.erase owner,
        coordinatePartial potential minimum receiver *
          (minimum receiver - face owner receiver)) -
      ∑ receiver ∈ Finset.univ.erase owner,
        (minimum receiver - face owner receiver) *
          coordinateResetIntegral lower minimum potential owner receiver := by
  classical
  rw [fderiv_eq_sum_coordinatePartial]
  have hown : coordinatePartial potential (Function.update minimum owner (lower owner)) owner *
      (Function.update minimum owner (lower owner) - face owner) owner = 0 := by
    simp [hdiagonal owner]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ owner), hown, add_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro receiver hreceiver
  have hne := (Finset.mem_erase.mp hreceiver).1
  rw [coordinatePartial_reset_eq_sub_integral lower upper minimum potential domain
    hopen hbox hsmooth hminimum owner receiver]
  simp only [Pi.sub_apply, Function.update_of_ne hne, coordinateResetIntegral]
  ring

/-- The source's signed account, before any absolute-value estimate. This
requires no standard-Q premise and does not assume the minimum is interior. -/
theorem signedMixedCurvatureAccount_at_every_box_minimum
    (lower upper : ι → ℝ) (face : ι → ι → ℝ) (weight : ι → ℝ)
    (potential : (ι → ℝ) → ℝ) (domain : Set (ι → ℝ)) (gain : ℝ)
    (hwidth : ∀ who, lower who < upper who)
    (hdiagonal : ∀ who, face who who = lower who)
    (hupper : ∀ owner receiver, face owner receiver ≤ upper receiver)
    (hweight : ∀ who, 0 ≤ weight who) (hweightSum : ∑ who, weight who = 1)
    (himage : ∀ receiver, 0 ≤ ∑ owner,
      (face owner receiver - lower receiver) * weight owner)
    (hopen : IsOpen domain) (hbox : Icc lower upper ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain)
    (hdrift : ∀ point ∈ Icc lower upper, ∀ owner, point owner = lower owner →
      gain ≤ fderiv ℝ potential point (point - face owner)) :
    ∀ minimum ∈ Icc lower upper, IsMinOn potential (Icc lower upper) minimum →
      (∀ receiver, 0 ≤ lowerBoundaryMultiplier lower minimum potential receiver) ∧
      gain + lowerBoundaryMatrixContribution lower minimum face weight potential ≤
        signedMixedCurvatureAccount lower minimum face weight potential ∧
      gain ≤ gain + lowerBoundaryMatrixContribution lower minimum face weight potential := by
  classical
  intro minimum hminimum hmin
  have hdiff : DifferentiableAt ℝ potential minimum :=
    (hsmooth.differentiableOn (by norm_num) minimum (hbox hminimum)).differentiableAt
      (hopen.mem_nhds (hbox hminimum))
  have hsign := box_minimum_coordinatePartial_signs lower upper minimum potential
    hwidth hminimum hmin hdiff
  have hmultiplier : ∀ receiver, 0 ≤ lowerBoundaryMultiplier lower minimum potential receiver := by
    intro receiver
    dsimp [lowerBoundaryMultiplier]
    split_ifs with hbottom
    · exact (hsign receiver).1 hbottom
    · exact le_rfl
  have howner : ∀ owner,
      gain + (∑ receiver, lowerBoundaryMultiplier lower minimum potential receiver *
        (face owner receiver - lower receiver)) ≤
      -(∑ receiver ∈ Finset.univ.erase owner,
        (minimum receiver - face owner receiver) *
          coordinateResetIntegral lower minimum potential owner receiver) := by
    intro owner
    have hreset := box_update_mem lower upper minimum hminimum owner (lower owner)
      ⟨le_rfl, (hwidth owner).le⟩
    have hface := hdrift _ hreset owner (by simp)
    rw [coordinate_reset_face_drift_eq lower upper minimum face potential domain
      hopen hbox hsmooth hminimum hdiagonal owner] at hface
    have hgradient := box_minimum_erased_gradient_le lower upper minimum face potential
      hwidth hdiagonal hupper hminimum hmin hdiff owner
    linarith
  have hweighted := Finset.sum_le_sum (s := Finset.univ) fun owner _ =>
    mul_le_mul_of_nonneg_left (howner owner) (hweight owner)
  have hleft : (∑ owner, weight owner * (gain +
      ∑ receiver, lowerBoundaryMultiplier lower minimum potential receiver *
        (face owner receiver - lower receiver))) =
      gain + lowerBoundaryMatrixContribution lower minimum face weight potential := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hweightSum, one_mul]
    rw [lowerBoundaryMatrixContribution]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro receiver _
    apply Finset.sum_congr rfl
    intro owner _
    ring
  have hright : (∑ owner, weight owner *
      -(∑ receiver ∈ Finset.univ.erase owner,
        (minimum receiver - face owner receiver) *
          coordinateResetIntegral lower minimum potential owner receiver)) =
      signedMixedCurvatureAccount lower minimum face weight potential := by
    simp only [signedMixedCurvatureAccount, mul_neg, Finset.sum_neg_distrib]
  refine ⟨hmultiplier, ?_, ?_⟩
  · rwa [hleft, hright] at hweighted
  · have hnonneg : 0 ≤ lowerBoundaryMatrixContribution lower minimum face weight potential :=
      Finset.sum_nonneg fun receiver _ => mul_nonneg (hmultiplier receiver) (himage receiver)
    linarith

end Math
