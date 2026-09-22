import Mathlib.LinearAlgebra.Matrix.DotProduct
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPositiveSingletonQuietExtension

/-!
# Singleton future rows force a nonnegative inverse row

Only the singleton future inequalities enter the core result. If the actual
child comparison matrix has a nonnegative inverse, multiplying these rows by
that inverse bounds the certificate weights by the actual parent's inverse
row. Nonnegative weights therefore rule out a negative inverse-row entry.
Neither Never nor joining inequalities, strict positivity, three players,
or a supplied child strategy is needed for this obstruction.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {ι κ : Type} [Fintype κ] [DecidableEq κ]

/-- The singleton future inequalities alone bound the weights by the actual
inverse row. This comparison does not even require the weights to be
nonnegative; that sign is used only by the following corollary. -/
theorem weight_le_inverseRow_of_singletonFutureRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child : κ ↪ ι) (who : ι) (weight : κ → ℝ)
    (hdet : ((quittingSingletonMatrix reward).submatrix child child).det ≠ 0)
    (hinverse : ∀ i j,
      0 ≤ ((quittingSingletonMatrix reward).submatrix child child)⁻¹ i j)
    (hfuture : ∀ j, -quittingSingletonMatrix reward who (child j) ≤
      ∑ i, weight i * (-quittingSingletonMatrix reward (child i) (child j))) :
    ∀ j, weight j ≤ Matrix.vecMul
      (fun i => quittingSingletonMatrix reward who (child i))
      ((quittingSingletonMatrix reward).submatrix child child)⁻¹ j := by
  let matrix := (quittingSingletonMatrix reward).submatrix child child
  let outside := fun i => quittingSingletonMatrix reward who (child i)
  have hrow : Matrix.vecMul weight matrix ≤ outside := by
    intro j
    have h := hfuture j
    simp only [mul_neg, Finset.sum_neg_distrib] at h
    exact neg_le_neg_iff.mp h
  intro j
  have hmono : Matrix.vecMul (Matrix.vecMul weight matrix) matrix⁻¹ j ≤
      Matrix.vecMul outside matrix⁻¹ j :=
    dotProduct_le_dotProduct_of_nonneg_right hrow (fun i => hinverse i j)
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.vecMul_one] at hmono
  exact hmono

/-- Nonnegative singleton-future weights force every actual inverse-row
coordinate to be nonnegative, at any finite child cardinality. -/
theorem inverseRow_nonneg_of_singletonFutureRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child : κ ↪ ι) (who : ι) (weight : κ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hdet : ((quittingSingletonMatrix reward).submatrix child child).det ≠ 0)
    (hinverse : ∀ i j,
      0 ≤ ((quittingSingletonMatrix reward).submatrix child child)⁻¹ i j)
    (hfuture : ∀ j, -quittingSingletonMatrix reward who (child j) ≤
      ∑ i, weight i * (-quittingSingletonMatrix reward (child i) (child j))) :
    ∀ j, 0 ≤ Matrix.vecMul
      (fun i => quittingSingletonMatrix reward who (child i))
      ((quittingSingletonMatrix reward).submatrix child child)⁻¹ j := by
  intro j
  exact (hweight j).trans
    (weight_le_inverseRow_of_singletonFutureRows reward child who weight hdet hinverse hfuture j)

section Certificates

variable {reward : {S : Finset (Option κ) // S.Nonempty} → Payoff (Option κ)}

/-- The exact capped-clock certificate cannot have weights exceeding the
outside inverse row; only its singleton future rows are used. -/
theorem CappedClockParentRewardCertificate.weight_le_inverseRow
    (certificate : CappedClockParentRewardCertificate reward)
    (hdet : ((quittingSingletonMatrix reward).submatrix some some).det ≠ 0)
    (hinverse : ∀ i j, 0 ≤ ((quittingSingletonMatrix reward).submatrix some some)⁻¹ i j) :
    ∀ j, certificate.weight j ≤ Matrix.vecMul
      (fun i => quittingSingletonMatrix reward none (some i))
      ((quittingSingletonMatrix reward).submatrix some some)⁻¹ j := by
  apply weight_le_inverseRow_of_singletonFutureRows
    reward Function.Embedding.some none certificate.weight hdet hinverse
  intro j
  have hcoalition :
      (⟨cappedClockChildCoalition ({j} : Finset κ),
        cappedClockChildCoalition_nonempty (Finset.singleton_nonempty j)⟩ :
          {S : Finset (Option κ) // S.Nonempty}) =
        ⟨{some j}, Finset.singleton_nonempty (some j)⟩ := by
    apply Subtype.ext
    change ({j} : Finset κ).map Function.Embedding.some = {some j}
    exact Finset.map_singleton _ _
  have h := certificate.future_row {j} (Finset.singleton_nonempty j)
  rw [hcoalition] at h
  simpa only [quittingSingletonMatrix, Function.Embedding.some,
    Function.Embedding.coeFn_mk, neg_sub] using h

/-- Exact capped-clock rows exclude a negative outside inverse-row entry. -/
theorem CappedClockParentRewardCertificate.inverseRow_nonneg
    (certificate : CappedClockParentRewardCertificate reward)
    (hdet : ((quittingSingletonMatrix reward).submatrix some some).det ≠ 0)
    (hinverse : ∀ i j, 0 ≤ ((quittingSingletonMatrix reward).submatrix some some)⁻¹ i j) :
    ∀ j, 0 ≤ Matrix.vecMul
      (fun i => quittingSingletonMatrix reward none (some i))
      ((quittingSingletonMatrix reward).submatrix some some)⁻¹ j := by
  intro j
  exact (certificate.weight_nonneg j).trans (certificate.weight_le_inverseRow hdet hinverse j)

/-- Omitting the Never row does not remove the inverse-row obstruction. -/
theorem CappedClockParentFutureJoinCertificate.weight_le_inverseRow
    (certificate : CappedClockParentFutureJoinCertificate reward)
    (hdet : ((quittingSingletonMatrix reward).submatrix some some).det ≠ 0)
    (hinverse : ∀ i j, 0 ≤ ((quittingSingletonMatrix reward).submatrix some some)⁻¹ i j) :
    ∀ j, certificate.weight j ≤ Matrix.vecMul
      (fun i => quittingSingletonMatrix reward none (some i))
      ((quittingSingletonMatrix reward).submatrix some some)⁻¹ j := by
  apply weight_le_inverseRow_of_singletonFutureRows
    reward Function.Embedding.some none certificate.weight hdet hinverse
  intro j
  have hcoalition :
      (⟨cappedClockChildCoalition ({j} : Finset κ),
        cappedClockChildCoalition_nonempty (Finset.singleton_nonempty j)⟩ :
          {S : Finset (Option κ) // S.Nonempty}) =
        ⟨{some j}, Finset.singleton_nonempty (some j)⟩ := by
    apply Subtype.ext
    change ({j} : Finset κ).map Function.Embedding.some = {some j}
    exact Finset.map_singleton _ _
  have h := certificate.future_row {j} (Finset.singleton_nonempty j)
  rw [hcoalition] at h
  simpa only [quittingSingletonMatrix, Function.Embedding.some,
    Function.Embedding.coeFn_mk, neg_sub] using h

/-- Even future/join certificates require a nonnegative outside inverse row,
independently of a positive-singleton repair of the Never row. -/
theorem CappedClockParentFutureJoinCertificate.inverseRow_nonneg
    (certificate : CappedClockParentFutureJoinCertificate reward)
    (hdet : ((quittingSingletonMatrix reward).submatrix some some).det ≠ 0)
    (hinverse : ∀ i j, 0 ≤ ((quittingSingletonMatrix reward).submatrix some some)⁻¹ i j) :
    ∀ j, 0 ≤ Matrix.vecMul
      (fun i => quittingSingletonMatrix reward none (some i))
      ((quittingSingletonMatrix reward).submatrix some some)⁻¹ j := by
  intro j
  exact (certificate.weight_nonneg j).trans (certificate.weight_le_inverseRow hdet hinverse j)

end Certificates
end GameTheory
