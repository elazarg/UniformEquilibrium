import MathUE.Analysis.StandardQFaceQuasiconvexExclusion
import UniformEquilibrium.Quitting.Projective.SingletonBoxTranslation
import UniformEquilibrium.Quitting.Projective.FinFourAmbientQSimplex

/-! # Direct actual singleton-box adapter of the separate standard-Q face theorem

The face drift is the genuine premise. The source no-UE facade produces Q but
does not assume the full exact-root potential relation or reprove its stronger
matrix-free quasiconvex exclusion.
-/

noncomputable section

namespace GameTheory

open Set Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The literal translation pulls quasiconvexity back from the actual
singleton rectangle to the zero-based positive-width box. -/
theorem quasiconvexOn_quittingSingletonBoxTranslate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (potential : Payoff ι → ℝ)
    (hquasiconvex : QuasiconvexOn ℝ (quittingSingletonBox reward bound) potential) :
    QuasiconvexOn ℝ (Icc (0 : Payoff ι) (quittingSingletonBoxWidth reward bound))
      (potential ∘ quittingSingletonBoxTranslate reward) := by
  apply quasiconvexOn_iff_le_max.mpr
  refine ⟨convex_Icc _ _, ?_⟩
  intro first hfirst second hsecond left right hleft hright htotal
  change potential (quittingSingletonBoxTranslate reward (left • first + right • second)) ≤ _
  rw [quittingSingletonBoxTranslate_affine reward first second left right htotal]
  exact (quasiconvexOn_iff_le_max.mp hquasiconvex).2
    ((quittingSingletonBoxTranslate_mem_iff reward bound first).mpr hfirst)
    ((quittingSingletonBoxTranslate_mem_iff reward bound second).mpr hsecond)
    hleft hright htotal

omit [DecidableEq ι] in
/-- Actual reward bounds, actual standard Q, and strictly positive singleton
face drift suffice. No full-root relation or ambient continuity is an input. -/
theorem not_quasiconvex_singletonBox_of_standardQ_positive_face_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hQ : IsStandardQ (quittingProjectiveLCPMatrix reward))
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential point)
    (hdrift : ∀ point ∈ quittingSingletonBox reward bound, ∀ owner,
      point owner = quittingSoloReward reward owner owner →
      0 < fderiv ℝ potential point (point - quittingSoloReward reward owner)) :
    ¬ QuasiconvexOn ℝ (quittingSingletonBox reward bound) potential := by
  intro hquasiconvex
  have htranslatedDiff : ∀ point ∈ Icc (0 : Payoff ι) (quittingSingletonBoxWidth reward bound),
      DifferentiableAt ℝ (potential ∘ quittingSingletonBoxTranslate reward) point := by
    intro point hpoint
    exact (hdiff _ ((quittingSingletonBoxTranslate_mem_iff reward bound point).mpr hpoint)).comp
      point (hasFDerivAt_quittingSingletonBoxTranslate reward point).differentiableAt
  exact not_quasiconvexOn_of_standardQ_positive_face_drift
    (quittingProjectiveLCPMatrix reward) (quittingSingletonBoxWidth reward bound)
    (potential ∘ quittingSingletonBoxTranslate reward) hQ
    (by intro who; simp [quittingProjectiveLCPMatrix])
    (quittingSingletonBoxWidth_pos reward hreward)
    (quittingProjectiveLCPMatrix_lt_singletonBoxWidth reward hreward) htranslatedDiff
    (quittingSingletonBoxTranslate_positive_face_drift reward bound potential hdiff hdrift)
    (quasiconvexOn_quittingSingletonBoxTranslate reward bound potential hquasiconvex)

/-- Bare Fin4 no-UE supplies actual ambient standard Q. The analytic input
is still genuine face-only drift, not a full-root potential certificate. -/
theorem not_quasiconvex_singletonBox_of_finFour_no_uniformPayoff_positive_face_drift
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (potential : Payoff (Fin 4) → ℝ)
    (hdiff : ∀ point ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential point)
    (hdrift : ∀ point ∈ quittingSingletonBox reward bound, ∀ owner,
      point owner = quittingSoloReward reward owner owner →
      0 < fderiv ℝ potential point (point - quittingSoloReward reward owner)) :
    ¬ QuasiconvexOn ℝ (quittingSingletonBox reward bound) potential :=
  not_quasiconvex_singletonBox_of_standardQ_positive_face_drift reward hreward
    (isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff reward hnot)
    potential hdiff hdrift

end GameTheory
