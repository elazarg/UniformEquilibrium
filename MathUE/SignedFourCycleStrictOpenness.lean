import MathUE.SignedFourCycleAlgebra
import Mathlib.Topology.Instances.Matrix

noncomputable section

namespace Math

local notation "FourMatrix" => Matrix (Fin 4) (Fin 4) ℝ

/-- Extract the eight signed-cycle recurrence coefficients from a four-by-four matrix. -/
def signedFourCycleCoefficientsOfMatrix (M : FourMatrix) : SignedFourCycleCoefficients where
  aZero := M 0 2 / (-M 0 1)
  aOne := M 1 3 / (-M 1 2)
  aTwo := M 2 0 / (-M 2 3)
  aThree := M 3 1 / (-M 3 0)
  dZero := M 0 3 / (-M 0 1)
  dOne := M 1 0 / (-M 1 2)
  dTwo := M 2 1 / (-M 2 3)
  dThree := M 3 2 / (-M 3 0)

/-- The literal successor/predecessor signs and six strict spectral tests for a matrix. -/
def HasSignedFourCycleStrictTests (M : FourMatrix) : Prop :=
  (M 0 1 < 0 ∧ 0 < M 0 3) ∧
  (M 1 2 < 0 ∧ 0 < M 1 0) ∧
  (M 2 3 < 0 ∧ 0 < M 2 1) ∧
  (M 3 0 < 0 ∧ 0 < M 3 2) ∧
  let c := signedFourCycleCoefficientsOfMatrix M
  0 < c.discriminant ∧ 1 < c.smallerEigenvalue ∧ c.upperRight < 0 ∧
    0 < c.rawWeightOne ∧ 0 < c.rawWeightTwo ∧ 0 < c.rawWeightThree

private theorem continuousAt_discriminant {M : FourMatrix}
    (h : HasSignedFourCycleStrictTests M) :
    ContinuousAt (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).discriminant) M := by
  rcases h with ⟨⟨h01, -⟩, ⟨h12, -⟩, ⟨h23, -⟩, ⟨h30, -⟩, -⟩
  simp only [signedFourCycleCoefficientsOfMatrix,
    SignedFourCycleCoefficients.discriminant,
    SignedFourCycleCoefficients.upperLeft, SignedFourCycleCoefficients.lowerRight,
    SignedFourCycleCoefficients.upperRight, SignedFourCycleCoefficients.lowerLeft]
  fun_prop (disch := aesop)

private theorem successor_ne {M : FourMatrix} (h : HasSignedFourCycleStrictTests M) :
    M 0 1 ≠ 0 ∧ M 1 2 ≠ 0 ∧ M 2 3 ≠ 0 ∧ M 3 0 ≠ 0 := by
  rcases h with ⟨⟨h01, -⟩, ⟨h12, -⟩, ⟨h23, -⟩, ⟨h30, -⟩, -⟩
  exact ⟨ne_of_lt h01, ne_of_lt h12, ne_of_lt h23, ne_of_lt h30⟩

private theorem continuousAt_smallerEigenvalue {M : FourMatrix}
    (h : HasSignedFourCycleStrictTests M) :
    ContinuousAt
      (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).smallerEigenvalue) M := by
  have hs := successor_ne h
  simp only [signedFourCycleCoefficientsOfMatrix,
    SignedFourCycleCoefficients.smallerEigenvalue,
    SignedFourCycleCoefficients.discriminant,
    SignedFourCycleCoefficients.upperLeft, SignedFourCycleCoefficients.lowerRight,
    SignedFourCycleCoefficients.upperRight, SignedFourCycleCoefficients.lowerLeft]
  fun_prop (disch := aesop)

private theorem continuousAt_upperRight {M : FourMatrix}
    (h : HasSignedFourCycleStrictTests M) :
    ContinuousAt (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).upperRight) M := by
  have hs := successor_ne h
  simp only [signedFourCycleCoefficientsOfMatrix,
    SignedFourCycleCoefficients.upperRight,
    SignedFourCycleCoefficients.lowerRight]
  fun_prop (disch := aesop)

private theorem continuousAt_rawWeightOne {M : FourMatrix}
    (h : HasSignedFourCycleStrictTests M) :
    ContinuousAt (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).rawWeightOne) M := by
  have hs := successor_ne h
  simp only [signedFourCycleCoefficientsOfMatrix,
    SignedFourCycleCoefficients.rawWeightOne,
    SignedFourCycleCoefficients.smallerEigenvalue,
    SignedFourCycleCoefficients.discriminant,
    SignedFourCycleCoefficients.upperLeft, SignedFourCycleCoefficients.lowerRight,
    SignedFourCycleCoefficients.upperRight, SignedFourCycleCoefficients.lowerLeft]
  fun_prop (disch := aesop)

private theorem continuousAt_rawWeightThree {M : FourMatrix}
    (h : HasSignedFourCycleStrictTests M) :
    ContinuousAt (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).rawWeightThree) M := by
  have hs := successor_ne h
  have hlambda :
      (signedFourCycleCoefficientsOfMatrix M).smallerEigenvalue ≠ 0 := by
    rcases h with ⟨-, -, -, -, -, hlambda, -⟩
    exact ne_of_gt (lt_trans (by norm_num) hlambda)
  have haTwo : ContinuousAt
      (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).aTwo) M := by
    simp only [signedFourCycleCoefficientsOfMatrix]
    fun_prop (disch := aesop)
  have hdTwo : ContinuousAt
      (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).dTwo) M := by
    simp only [signedFourCycleCoefficientsOfMatrix]
    fun_prop (disch := aesop)
  have hperiod : ContinuousAt
      (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).periodSurvival) M := by
    simp only [SignedFourCycleCoefficients.periodSurvival]
    exact continuousAt_const.div (continuousAt_smallerEigenvalue h) hlambda
  simp only [SignedFourCycleCoefficients.rawWeightThree,
    SignedFourCycleCoefficients.rawWeightZero]
  exact hperiod.mul (haTwo.mul (continuousAt_upperRight h).neg |>.add
    (hdTwo.mul (continuousAt_rawWeightOne h)))

private theorem continuousAt_rawWeightTwo {M : FourMatrix}
    (h : HasSignedFourCycleStrictTests M) :
    ContinuousAt (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).rawWeightTwo) M := by
  have hs := successor_ne h
  have hlambda :
      (signedFourCycleCoefficientsOfMatrix M).smallerEigenvalue ≠ 0 := by
    rcases h with ⟨-, -, -, -, -, hlambda, -⟩
    exact ne_of_gt (lt_trans (by norm_num) hlambda)
  have haOne : ContinuousAt
      (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).aOne) M := by
    simp only [signedFourCycleCoefficientsOfMatrix]
    fun_prop (disch := aesop)
  have hdOne : ContinuousAt
      (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).dOne) M := by
    simp only [signedFourCycleCoefficientsOfMatrix]
    fun_prop (disch := aesop)
  have hperiod : ContinuousAt
      (fun N ↦ (signedFourCycleCoefficientsOfMatrix N).periodSurvival) M := by
    simp only [SignedFourCycleCoefficients.periodSurvival]
    exact continuousAt_const.div (continuousAt_smallerEigenvalue h) hlambda
  simp only [SignedFourCycleCoefficients.rawWeightTwo,
    SignedFourCycleCoefficients.rawWeightZero]
  exact ((hperiod.mul hdOne).mul (continuousAt_upperRight h).neg).add
    (haOne.mul (continuousAt_rawWeightThree h))

theorem isOpen_hasSignedFourCycleStrictTests :
    IsOpen {M : FourMatrix | HasSignedFourCycleStrictTests M} := by
  rw [isOpen_iff_mem_nhds]
  intro M h
  rcases h with
    ⟨⟨h01, h03⟩, ⟨h12, h10⟩, ⟨h23, h21⟩, ⟨h30, h32⟩,
      hdisc, hlambda, hupper, hwOne, hwTwo, hwThree⟩
  have hfull : HasSignedFourCycleStrictTests M :=
    ⟨⟨h01, h03⟩, ⟨h12, h10⟩, ⟨h23, h21⟩, ⟨h30, h32⟩,
      hdisc, hlambda, hupper, hwOne, hwTwo, hwThree⟩
  have c01 : ContinuousAt (fun N : FourMatrix ↦ N 0 1) M :=
    (continuous_apply_apply 0 1).continuousAt
  have c03 : ContinuousAt (fun N : FourMatrix ↦ N 0 3) M :=
    (continuous_apply_apply 0 3).continuousAt
  have c12 : ContinuousAt (fun N : FourMatrix ↦ N 1 2) M :=
    (continuous_apply_apply 1 2).continuousAt
  have c10 : ContinuousAt (fun N : FourMatrix ↦ N 1 0) M :=
    (continuous_apply_apply 1 0).continuousAt
  have c23 : ContinuousAt (fun N : FourMatrix ↦ N 2 3) M :=
    (continuous_apply_apply 2 3).continuousAt
  have c21 : ContinuousAt (fun N : FourMatrix ↦ N 2 1) M :=
    (continuous_apply_apply 2 1).continuousAt
  have c30 : ContinuousAt (fun N : FourMatrix ↦ N 3 0) M :=
    (continuous_apply_apply 3 0).continuousAt
  have c32 : ContinuousAt (fun N : FourMatrix ↦ N 3 2) M :=
    (continuous_apply_apply 3 2).continuousAt
  filter_upwards [c01.eventually_lt_const h01, c03.eventually_const_lt h03,
    c12.eventually_lt_const h12, c10.eventually_const_lt h10,
    c23.eventually_lt_const h23, c21.eventually_const_lt h21,
    c30.eventually_lt_const h30, c32.eventually_const_lt h32,
    (continuousAt_discriminant hfull).eventually_const_lt hdisc,
    (continuousAt_smallerEigenvalue hfull).eventually_const_lt hlambda,
    (continuousAt_upperRight hfull).eventually_lt_const hupper,
    (continuousAt_rawWeightOne hfull).eventually_const_lt hwOne,
    (continuousAt_rawWeightTwo hfull).eventually_const_lt hwTwo,
    (continuousAt_rawWeightThree hfull).eventually_const_lt hwThree] with
      N hn01 hn03 hn12 hn10 hn23 hn21 hn30 hn32 hndisc hnlambda hnupper
        hnwOne hnwTwo hnwThree
  exact ⟨⟨hn01, hn03⟩, ⟨hn12, hn10⟩, ⟨hn23, hn21⟩, ⟨hn30, hn32⟩,
    hndisc, hnlambda, hnupper, hnwOne, hnwTwo, hnwThree⟩

end Math
