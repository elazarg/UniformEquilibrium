/- A standard-smooth chart relative to the distinguished parameter. -/
import MathUE.CurveSelection.FunctionField
import MathUE.CurveSelection.GermComponent
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

noncomputable section

open Filter

namespace Math
namespace CurveSelection.RelativeSmoothGerm

open CurveSelection.FunctionField
open CurveSelection.Internal.GermComponent

/-- A prime affine quotient with a transcendental distinguished parameter
is generically standard smooth over the polynomial ring in that parameter.

The generic field extension factors through `ℝ(t)`.  The first map is a
localization and the second is a finitely generated extension of a
characteristic-zero field, hence formally smooth.  Standard smoothness then
holds after shrinking by one polynomial outside the prime. -/
theorem exists_parameter_standardSmooth_basicOpen_of_prime
    {σ : Type*} [Finite σ]
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0) :
    ∃ g : MvPolynomial σ ℝ,
      g ∉ J ∧
      letI : Algebra (Polynomial ℝ)
          (MvPolynomial σ ℝ ⧸ J) :=
        parameterPolynomialAlgebra J parameter
      Algebra.IsStandardSmooth (Polynomial ℝ)
        (Localization.Away (Ideal.Quotient.mk J g)) := by
  let : Fintype σ := Fintype.ofFinite σ
  let R := Polynomial ℝ
  let A := MvPolynomial σ ℝ ⧸ J
  let K := FractionRing R
  let L := FractionRing A
  let : Algebra R A :=
    parameterPolynomialAlgebra J parameter
  let : IsScalarTower ℝ R A :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change Ideal.Quotient.mk J (MvPolynomial.C r) =
        parameterPolynomialHom J parameter (Polynomial.C r)
      simp [parameterPolynomialHom]
  let : Algebra.FiniteType R A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℝ R A
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra K L :=
    parameterFractionRingAlgebra J parameter hparameter
  let algRL : Algebra R L :=
    (parameterToFunctionFieldHom J parameter).toAlgebra
  let : SMul R L := algRL.toSMul
  let : IsScalarTower R K L :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := K) (A := L)
      fun r => by
        rw [show
          (algebraMap K L) =
              parameterFractionRingHom J parameter hparameter by
            exact RingHom.algebraMap_toAlgebra _]
        rw [parameterFractionRingHom,
          IsFractionRing.lift_algebraMap]
        rfl
  let : IsScalarTower R A L :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := A) (A := L)
      fun _ => rfl
  let : Algebra.FormallySmooth R K :=
    Algebra.FormallySmooth.of_isLocalization
      (nonZeroDivisors R)
  let : Algebra.EssFiniteType K L :=
    essFiniteType_parameterFunctionField J parameter hparameter
  let : Algebra.FormallySmooth K L :=
    Algebra.FormallySmooth.of_perfectField
  let : Algebra.FormallySmooth R L :=
    Algebra.FormallySmooth.comp R K L
  have hminimal :
      (⊥ : Ideal A) ∈ minimalPrimes A := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton _
  let L' := Localization.AtPrime (⊥ : Ideal A)
  have : Ring.KrullDimLE 0 L' :=
    Ring.KrullDimLE.of_isLocalization
      (⊥ : Ideal A) hminimal L'
  let : Field L' :=
    Ring.KrullDimLE.isField_of_isReduced.toField
  let : IsLocalization (⊥ : Ideal A).primeCompl L := by
    simpa only [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization (nonZeroDivisors A) L)
  let e : L' ≃ₐ[A] L :=
    IsLocalization.algEquiv (⊥ : Ideal A).primeCompl L' L
  let : IsScalarTower R A L' :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := A) (A := L')
      fun _ => rfl
  let eR : L ≃ₐ[R] L' :=
    (e.restrictScalars R).symm
  let : Algebra.FormallySmooth R L' :=
    Algebra.FormallySmooth.of_equiv eR
  let : Algebra.IsSmoothAt R (⊥ : Ideal A) :=
    inferInstance
  obtain ⟨f, hf, hstandard⟩ :=
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth
      R (⊥ : Ideal A)
  obtain ⟨g, rfl⟩ :=
    Ideal.Quotient.mk_surjective f
  refine ⟨g, ?_, hstandard⟩
  intro hg
  exact hf (Ideal.Quotient.eq_zero_iff_mem.mpr hg)

/-- The relative standard-smooth chart retains every sequence defining the
prime germ: its denominator is eventually nonzero along the same free
ultrafilter. -/
theorem exists_eventually_parameter_standardSmooth_basicOpen
    {σ : Type*} [Finite σ]
    (x : ℕ → (σ → ℝ))
    (J : Ideal (MvPolynomial σ ℝ)) [J.IsPrime]
    (parameter : σ)
    (hparameter :
      ∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0)
    (hJmem :
      ∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0) :
    ∃ g : MvPolynomial σ ℝ,
      g ∉ J ∧
      (∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g ≠ 0) ∧
      letI : Algebra (Polynomial ℝ)
          (MvPolynomial σ ℝ ⧸ J) :=
        parameterPolynomialAlgebra J parameter
      Algebra.IsStandardSmooth (Polynomial ℝ)
        (Localization.Away (Ideal.Quotient.mk J g)) := by
  let : Fintype σ := Fintype.ofFinite σ
  obtain ⟨g, hgJ, hstandard⟩ :=
    exists_parameter_standardSmooth_basicOpen_of_prime
      J parameter hparameter
  have hnotEventuallyZero :
      ¬∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g = 0 := by
    intro hzero
    exact hgJ ((hJmem g).mpr hzero)
  have hnonzero :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) g ≠ 0 := by
    rw [Ultrafilter.eventually_not]
    exact hnotEventuallyZero
  exact ⟨g, hgJ, hnonzero, hstandard⟩

end CurveSelection.RelativeSmoothGerm
end Math
