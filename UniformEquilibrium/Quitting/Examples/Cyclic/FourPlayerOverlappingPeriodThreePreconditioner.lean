import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreePolynomialSystem
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact nonsingularity witness for the overlapping period-three chart

The integer numerator matrix of the preconditioner has an explicit inverse
modulo a prime.  This compact witness proves nonsingularity over the
integers and hence over the rationals without expanding an eight-dimensional
determinant.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

/-- Integer numerator of the rational preconditioning matrix. -/
def preconditionerNumerator : Matrix HazardCoordinate HazardCoordinate ℤ :=
  ![![315143353187, 366974958817, -49078078206, 184811852330,
      232875167579, -254869288005, -25099394501, -1470845305],
    ![602147704263, 145073028566, -9776944759, -100954767104,
      648395477518, 294319240668, 121157930961, -211997987049],
    ![-309126321348, 258278517492, -102280783703, 318835250165,
      477261949039, 398272112383, 56650468854, -195187547313],
    ![8141174505, -8490457215, -341152554699, 89200975646,
      81054707800, 142638748426, 6864760919, -901901991],
    ![68266279421, -92414191444, 99419891079, 230779479327,
      330411042247, -49452845261, 97457493728, -65051669603],
    ![-4718561732, 76693224365, -112489910972, 84672772712,
      -120106797257, 339836466727, 67508004707, 469042378865],
    ![-344947719758, 240513202079, -265825502558, 367886940515,
      -509613507555, 329832798069, 25940159701, 158832741351],
    ![-2160865764, 181328381440, -51514764712, 38775903777,
      -55002918462, 155628140095, -395004284185, 214797999024]]

/-- Prime modulus used by the exact nonsingularity witness. -/
private abbrev preconditionerWitnessPrime : ℕ := 1000003

/-- Reduction of the integer numerator matrix modulo the witness prime. -/
private def preconditionerNumeratorMod :
    Matrix HazardCoordinate HazardCoordinate (ZMod preconditionerWitnessPrime) :=
  fun row column => preconditionerNumerator row column

/-- Explicit modular inverse of the integer numerator matrix. -/
private def preconditionerModularInverse :
    Matrix HazardCoordinate HazardCoordinate (ZMod preconditionerWitnessPrime) :=
  ![![326778, 874104, 987565, 352559, 876500, 320612, 266963, 304544],
    ![544762, 511213, 472898, 594170, 537315, 52079, 656961, 818813],
    ![539325, 700770, 272728, 802074, 977652, 125914, 35433, 563747],
    ![201692, 854626, 38434, 596694, 784252, 25659, 149101, 754780],
    ![870872, 476882, 414929, 296197, 50733, 154310, 800128, 783024],
    ![913669, 673179, 839413, 529438, 838420, 208844, 887557, 98147],
    ![510111, 310010, 955795, 733387, 385054, 231811, 327885, 187357],
    ![533646, 134224, 702476, 981238, 378663, 339354, 963098, 419990]]

/-- The displayed modular matrix is a right inverse. -/
private theorem preconditionerNumeratorMod_mul_inverse :
    preconditionerNumeratorMod * preconditionerModularInverse = 1 := by
  decide

/-- The modular numerator determinant is nonzero. -/
private theorem preconditionerNumeratorMod_det_ne_zero :
    Matrix.det preconditionerNumeratorMod ≠ 0 := by
  letI : Fact (1 < preconditionerWitnessPrime) := ⟨by
    norm_num [preconditionerWitnessPrime]⟩
  exact Matrix.det_ne_zero_of_right_inverse
    preconditionerNumeratorMod_mul_inverse

/-- The integer numerator determinant is nonzero. -/
theorem preconditionerNumerator_det_ne_zero :
    Matrix.det preconditionerNumerator ≠ 0 := by
  intro hzero
  apply preconditionerNumeratorMod_det_ne_zero
  have hmapped := congrArg
    (Int.castRingHom (ZMod preconditionerWitnessPrime)) hzero
  rw [map_zero, RingHom.map_det] at hmapped
  exact hmapped

/-- The rational preconditioner is the scalar rescaling of its displayed
integer numerator. -/
theorem preconditioner_eq_scaledNumerator :
    (fun row column => preconditioner row column) =
      (1 / (10 ^ 12 : ℚ)) •
        preconditionerNumerator.map (Int.castRingHom ℚ) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [preconditioner, preconditionerNumerator]

/-- The rational preconditioning matrix is nonsingular. -/
theorem preconditioner_det_ne_zero :
    Matrix.det (fun row column => preconditioner row column) ≠ 0 := by
  rw [preconditioner_eq_scaledNumerator, Matrix.det_smul]
  apply mul_ne_zero
  · norm_num
  · intro hzero
    apply preconditionerNumerator_det_ne_zero
    have hcast : ((Matrix.det preconditionerNumerator : ℤ) : ℚ) = 0 := by
      rw [Int.cast_det]
      exact hzero
    exact_mod_cast hcast

/-- Multiplication by the rational preconditioner is injective. -/
theorem preconditioner_mulVec_injective :
    Function.Injective
      (Matrix.mulVec (fun row column => preconditioner row column)) :=
  Matrix.mulVec_injective_iff_isUnit.mpr <|
    (Matrix.isUnit_iff_isUnit_det
      (fun row column => preconditioner row column)).mpr
        (isUnit_iff_ne_zero.mpr preconditioner_det_ne_zero)

/-- The same exact preconditioner is nonsingular after embedding its rational
entries into the reals. -/
theorem realPreconditioner_mulVec_injective :
    Function.Injective
      (Matrix.mulVec fun row column => (preconditioner row column : ℝ)) := by
  let rationalMatrix : Matrix HazardCoordinate HazardCoordinate ℚ :=
    fun row column => preconditioner row column
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  change Matrix.det (rationalMatrix.map fun value => (value : ℝ)) ≠ 0
  rw [← Rat.cast_det]
  exact_mod_cast (show Matrix.det rationalMatrix ≠ 0 by
    simpa [rationalMatrix] using preconditioner_det_ne_zero)

end GameTheory.FourPlayerOverlappingPeriodThree

end
