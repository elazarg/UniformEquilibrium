import MathUE.Analysis.BoxedAdditiveCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Actual coordinate partials, closed-box minimum signs, and reset FTC -/

noncomputable section

namespace Math

open Set Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual Fréchet derivative evaluated on a coordinate vector. -/
def coordinatePartial (potential : (ι → ℝ) → ℝ) (point : ι → ℝ) (receiver : ι) : ℝ :=
  fderiv ℝ potential point (Pi.single receiver 1)

/-- Differentiate receiver's partial in owner's coordinate. No symmetry
or prescribed Hessian is assumed; this is the actual iterated derivative. -/
def coordinateMixedPartial (potential : (ι → ℝ) → ℝ)
    (point : ι → ℝ) (owner receiver : ι) : ℝ :=
  fderiv ℝ (fun input => coordinatePartial potential input receiver) point (Pi.single owner 1)

theorem coordinatePartial_contDiffOn
    (potential : (ι → ℝ) → ℝ) (domain : Set (ι → ℝ)) (hopen : IsOpen domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain) (receiver : ι) :
    ContDiffOn ℝ 1 (fun point => coordinatePartial potential point receiver) domain :=
  (hsmooth.fderiv_of_isOpen hopen (by norm_num)).clm_apply contDiffOn_const

theorem coordinateMixedPartial_continuousOn
    (potential : (ι → ℝ) → ℝ) (domain : Set (ι → ℝ)) (hopen : IsOpen domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain) (owner receiver : ι) :
    ContinuousOn (fun point => coordinateMixedPartial potential point owner receiver) domain := by
  have hpartial := coordinatePartial_contDiffOn potential domain hopen hsmooth receiver
  exact (hpartial.continuousOn_fderiv_of_isOpen hopen le_rfl).clm_apply continuousOn_const

omit [Fintype ι] in
theorem box_update_mem
    (lower upper point : ι → ℝ) (hpoint : point ∈ Icc lower upper)
    (owner : ι) (value : ℝ) (hvalue : value ∈ Icc (lower owner) (upper owner)) :
    Function.update point owner value ∈ Icc lower upper := by
  constructor <;> intro receiver
  · by_cases heq : receiver = owner
    · subst receiver; simpa using hvalue.1
    · simpa [heq] using hpoint.1 receiver
  · by_cases heq : receiver = owner
    · subst receiver; simpa using hvalue.2
    · simpa [heq] using hpoint.2 receiver

/-- All closed-box minimum signs, obtained from scalar coordinate minima.
Upper-face, interior, lower-face, and flat minima are retained. -/
theorem box_minimum_coordinatePartial_signs
    (lower upper minimum : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (hwidth : ∀ who, lower who < upper who) (hminimum : minimum ∈ Icc lower upper)
    (hmin : IsMinOn potential (Icc lower upper) minimum)
    (hdiff : DifferentiableAt ℝ potential minimum) :
    ∀ receiver,
      (minimum receiver = lower receiver → 0 ≤ coordinatePartial potential minimum receiver) ∧
      (lower receiver < minimum receiver → minimum receiver < upper receiver →
        coordinatePartial potential minimum receiver = 0) ∧
      (minimum receiver = upper receiver → coordinatePartial potential minimum receiver ≤ 0) := by
  intro receiver
  let slice := fun value => potential (Function.update minimum receiver value)
  have hslice : HasDerivAt slice (coordinatePartial potential minimum receiver)
      (minimum receiver) :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (minimum receiver)
      (hasDerivAt_update minimum receiver (minimum receiver)) (by simp)
  have hsliceMin : IsMinOn slice (Icc (lower receiver) (upper receiver)) (minimum receiver) := by
    intro value hvalue
    simpa [slice] using hmin (box_update_mem lower upper minimum hminimum receiver value hvalue)
  have hsigns := interval_minimum_derivative_signs slice (lower receiver) (upper receiver)
    (minimum receiver) (hwidth receiver) ⟨hminimum.1 receiver, hminimum.2 receiver⟩
    hsliceMin hslice.differentiableAt
  simpa only [hslice.deriv] using hsigns

/-- The exact FTC identity for resetting one coordinate to its lower face.
The closed interval can have zero length. Receiver may even equal owner. -/
theorem coordinatePartial_reset_eq_sub_integral
    (lower upper minimum : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (domain : Set (ι → ℝ)) (hopen : IsOpen domain)
    (hbox : Icc lower upper ⊆ domain) (hsmooth : ContDiffOn ℝ 2 potential domain)
    (hminimum : minimum ∈ Icc lower upper) (owner receiver : ι) :
    coordinatePartial potential (Function.update minimum owner (lower owner)) receiver =
      coordinatePartial potential minimum receiver -
        ∫ value in (lower owner)..(minimum owner),
          coordinateMixedPartial potential (Function.update minimum owner value)
            owner receiver := by
  have hupdate : ∀ value ∈ Icc (lower owner) (minimum owner),
      Function.update minimum owner value ∈ domain := by
    intro value hvalue
    exact hbox (box_update_mem lower upper minimum hminimum owner value
      ⟨hvalue.1, hvalue.2.trans (hminimum.2 owner)⟩)
  have hpartial := coordinatePartial_contDiffOn potential domain hopen hsmooth receiver
  have hderivative : ∀ value ∈ Icc (lower owner) (minimum owner),
      HasDerivAt (fun rate =>
        coordinatePartial potential (Function.update minimum owner rate) receiver)
        (coordinateMixedPartial potential (Function.update minimum owner value) owner receiver)
        value := by
    intro value hvalue
    have hdiff := (hpartial.differentiableOn_one _ (hupdate value hvalue)).differentiableAt
      (hopen.mem_nhds (hupdate value hvalue))
    exact hdiff.hasFDerivAt.comp_hasDerivAt value (hasDerivAt_update minimum owner value)
  have hcontinuous : ContinuousOn
      (fun value => coordinateMixedPartial potential (Function.update minimum owner value)
        owner receiver) (Icc (lower owner) (minimum owner)) :=
    (coordinateMixedPartial_continuousOn potential domain hopen hsmooth owner receiver).comp
      ((continuous_const : Continuous (fun _ : ℝ => minimum)).update
        owner continuous_id).continuousOn hupdate
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun value hvalue => hderivative value (by
      simpa only [uIcc_of_le (hminimum.1 owner)] using hvalue))
    (hcontinuous.intervalIntegrable_of_Icc (hminimum.1 owner))
  simp only [Function.update_eq_self] at hFTC
  linarith

end Math
