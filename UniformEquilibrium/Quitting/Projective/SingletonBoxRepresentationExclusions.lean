import MathUE.Analysis.FaceDriftScalarCompositionExclusion
import MathUE.LinearProgramming.StandardQSimplexImage
import UniformEquilibrium.Quitting.Projective.SingletonBoxTranslation
import UniformEquilibrium.Quitting.Projective.RobustPotentialSingletonFaceDrift

/-! # Actual face-only additive and nonmonotone composition exclusions

Representation identities are confined to the actual closed singleton box.
The weaker analytic result uses only a supplied simplex with nonnegative
matrix image. Standard Q produces that simplex for its separate corollaries.
The robust facade derives face drift from the same actual full relation.
-/

noncomputable section

namespace GameTheory

open Set Math.LinearProgramming
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Additive representability on the actual closed singleton box only.
No regularity assumption is imposed on arbitrary represented summands. -/
def IsQuittingSingletonBoxAdditive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (potential : Payoff ι → ℝ) : Prop :=
  ∃ constant : ℝ, ∃ component : ι → ℝ → ℝ,
    EqOn potential (Math.boxAdditiveFunction constant component) (quittingSingletonBox reward bound)

/-- The packet's regular scalar-composition class. The component and outer
domains contain the whole relevant images, but equality is only on the box.
Neither monotonicity nor a boundary sign is part of this representation class. -/
def IsQuittingSingletonBoxRegularScalarComposition
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (potential : Payoff ι → ℝ) : Prop :=
  ∃ constant : ℝ, ∃ component : ι → ℝ → ℝ, ∃ componentDomain : ι → Set ℝ,
    ∃ outer : ℝ → ℝ, ∃ outerDomain : Set ℝ,
      (∀ who, IsOpen (componentDomain who)) ∧
      (∀ who, Icc (quittingSoloReward reward who who) (bound + 1) ⊆ componentDomain who) ∧
      (∀ who, ContDiffOn ℝ 1 (component who) (componentDomain who)) ∧
      (IsOpen outerDomain ∧ Convex ℝ outerDomain) ∧
      ContDiffOn ℝ 1 outer outerDomain ∧
      MapsTo (Math.boxAdditiveFunction constant component)
        (quittingSingletonBox reward bound) outerDomain ∧
      EqOn potential (outer ∘ Math.boxAdditiveFunction constant component)
        (quittingSingletonBox reward bound)

omit [Nonempty ι] in
/-- Face-only positive drift plus an analytic simplex excludes every additive
representation of the actual function on the actual closed singleton box. -/
theorem not_singletonBox_additive_of_simplex_positive_face_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (weight : ι → ℝ) (hweight : ∀ who, 0 ≤ weight who)
    (hweightSum : ∑ who, weight who = 1)
    (hweightImage : ∀ receiver,
      0 ≤ ∑ owner, quittingProjectiveLCPMatrix reward receiver owner * weight owner)
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential point)
    (hdrift : ∀ point ∈ quittingSingletonBox reward bound, ∀ owner,
      point owner = quittingSoloReward reward owner owner →
      0 < fderiv ℝ potential point (point - quittingSoloReward reward owner)) :
    ¬ IsQuittingSingletonBoxAdditive reward bound potential := by
  rintro ⟨constant, component, heq⟩
  let translated := potential ∘ quittingSingletonBoxTranslate reward
  let translatedComponent := fun who value =>
    component who (quittingSoloReward reward who who + value)
  have htranslatedDiff : ∀ point ∈ Icc (0 : Payoff ι) (quittingSingletonBoxWidth reward bound),
      DifferentiableAt ℝ translated point := by
    intro point hpoint
    exact (hdiff _ ((quittingSingletonBoxTranslate_mem_iff reward bound point).mpr hpoint)).comp
      point (hasFDerivAt_quittingSingletonBoxTranslate reward point).differentiableAt
  have htranslatedEq : EqOn translated (Math.boxAdditiveFunction constant translatedComponent)
      (Icc (0 : Payoff ι) (quittingSingletonBoxWidth reward bound)) := by
    intro point hpoint
    exact heq ((quittingSingletonBoxTranslate_mem_iff reward bound point).mpr hpoint)
  apply Math.not_positive_box_face_drift_of_additive_representation
    (quittingSingletonBoxWidth reward bound) (quittingProjectiveLCPMatrix reward) weight
    translated constant translatedComponent (quittingSingletonBoxWidth_pos reward hreward)
    (by intro who; simp [quittingProjectiveLCPMatrix])
    (quittingProjectiveLCPMatrix_lt_singletonBoxWidth reward hreward)
    hweight hweightSum hweightImage
    htranslatedDiff htranslatedEq
  exact quittingSingletonBoxTranslate_positive_face_drift reward bound potential hdiff hdrift

/-- The nonmonotone scalar-composition exclusion on the actual closed box.
All component neighborhoods and the entire outer inner-image domain are kept. -/
theorem not_singletonBox_scalarComposition_of_simplex_positive_face_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (weight : ι → ℝ) (hweight : ∀ who, 0 ≤ weight who)
    (hweightSum : ∑ who, weight who = 1)
    (hweightImage : ∀ receiver,
      0 ≤ ∑ owner, quittingProjectiveLCPMatrix reward receiver owner * weight owner)
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential point)
    (hdrift : ∀ point ∈ quittingSingletonBox reward bound, ∀ owner,
      point owner = quittingSoloReward reward owner owner →
      0 < fderiv ℝ potential point (point - quittingSoloReward reward owner)) :
    ¬ IsQuittingSingletonBoxRegularScalarComposition reward bound potential := by
  rintro ⟨constant, component, componentDomain, outer, outerDomain,
    hcomponentOpen, hcomponentInterval, hcomponent, houterDomain, houter, hinnerImage, heq⟩
  let translated := potential ∘ quittingSingletonBoxTranslate reward
  let translatedComponent := fun who value =>
    component who (quittingSoloReward reward who who + value)
  let translatedDomain := fun who =>
    (fun value => quittingSoloReward reward who who + value) ⁻¹' componentDomain who
  have htranslatedDiff : ∀ point ∈ Icc (0 : Payoff ι) (quittingSingletonBoxWidth reward bound),
      DifferentiableAt ℝ translated point := by
    intro point hpoint
    exact (hdiff _ ((quittingSingletonBoxTranslate_mem_iff reward bound point).mpr hpoint)).comp
      point (hasFDerivAt_quittingSingletonBoxTranslate reward point).differentiableAt
  have htranslatedOpen : ∀ who, IsOpen (translatedDomain who) :=
    fun who => (hcomponentOpen who).preimage (continuous_const.add continuous_id)
  have htranslatedInterval : ∀ who, Icc 0 (quittingSingletonBoxWidth reward bound who) ⊆
      translatedDomain who := by
    intro who value hvalue
    apply hcomponentInterval who
    constructor
    · change quittingSoloReward reward who who ≤ quittingSoloReward reward who who + value
      linarith [hvalue.1]
    · change quittingSoloReward reward who who + value ≤ bound + 1
      have hupper := hvalue.2
      change value ≤ bound + 1 - quittingSoloReward reward who who at hupper
      linarith
  have htranslatedComponent : ∀ who, ContDiffOn ℝ 1 (translatedComponent who)
      (translatedDomain who) := by
    intro who
    exact (hcomponent who).comp (contDiff_const.add contDiff_id).contDiffOn
      (fun _ hvalue => hvalue)
  have htranslatedImage : MapsTo (Math.boxAdditiveFunction constant translatedComponent)
      (Icc (0 : Payoff ι) (quittingSingletonBoxWidth reward bound)) outerDomain := by
    intro point hpoint
    exact hinnerImage ((quittingSingletonBoxTranslate_mem_iff reward bound point).mpr hpoint)
  have htranslatedEq : EqOn translated
      (outer ∘ Math.boxAdditiveFunction constant translatedComponent)
      (Icc (0 : Payoff ι) (quittingSingletonBoxWidth reward bound)) := by
    intro point hpoint
    exact heq ((quittingSingletonBoxTranslate_mem_iff reward bound point).mpr hpoint)
  apply Math.not_positive_box_face_drift_of_scalar_composition
    (quittingSingletonBoxWidth reward bound) (quittingProjectiveLCPMatrix reward) weight
    translated constant translatedComponent translatedDomain outer outerDomain
    (quittingSingletonBoxWidth_pos reward hreward)
    (by intro who; simp [quittingProjectiveLCPMatrix])
    (quittingProjectiveLCPMatrix_lt_singletonBoxWidth reward hreward)
    hweight hweightSum hweightImage
    htranslatedDiff htranslatedOpen htranslatedInterval htranslatedComponent
    houterDomain houter htranslatedImage htranslatedEq
  exact quittingSingletonBoxTranslate_positive_face_drift reward bound potential hdiff hdrift

/-- The existing standard-Q surface delegates to the weaker simplex theorem. -/
theorem not_singletonBox_additive_of_standardQ_positive_face_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hQ : IsStandardQ (quittingProjectiveLCPMatrix reward))
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential point)
    (hdrift : ∀ point ∈ quittingSingletonBox reward bound, ∀ owner,
      point owner = quittingSoloReward reward owner owner →
      0 < fderiv ℝ potential point (point - quittingSoloReward reward owner)) :
    ¬ IsQuittingSingletonBoxAdditive reward bound potential := by
  obtain ⟨weight, hweightImage⟩ :=
    exists_simplex_positive_residual_of_standardQ (quittingProjectiveLCPMatrix reward) hQ
  exact not_singletonBox_additive_of_simplex_positive_face_drift reward hreward
    weight.weights weight.weights_nonneg weight.total_of_fintype
    (fun receiver => by
      simpa only [singletonLCPResidual_eq, mul_comm] using (hweightImage receiver).le)
    potential hdiff hdrift

/-- The existing standard-Q surface delegates to the weaker simplex theorem. -/
theorem not_singletonBox_scalarComposition_of_standardQ_positive_face_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hQ : IsStandardQ (quittingProjectiveLCPMatrix reward))
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential point)
    (hdrift : ∀ point ∈ quittingSingletonBox reward bound, ∀ owner,
      point owner = quittingSoloReward reward owner owner →
      0 < fderiv ℝ potential point (point - quittingSoloReward reward owner)) :
    ¬ IsQuittingSingletonBoxRegularScalarComposition reward bound potential := by
  obtain ⟨weight, hweightImage⟩ :=
    exists_simplex_positive_residual_of_standardQ (quittingProjectiveLCPMatrix reward) hQ
  exact not_singletonBox_scalarComposition_of_simplex_positive_face_drift reward hreward
    weight.weights weight.weights_nonneg weight.total_of_fintype
    (fun receiver => by
      simpa only [singletonLCPResidual_eq, mul_comm] using (hweightImage receiver).le)
    potential hdiff hdrift

/-- The source Theorem3 representation exclusions with only its analytic simplex.
The same potential on the full actual robust relation supplies positive face
drift; no standard-Q, normality, no-UE or singleton-sign premise is needed. -/
theorem quittingRobustPotential_not_singletonBox_representations_of_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound tolerance : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (htolerance0 : 0 < tolerance) (htolerance1 : tolerance ≤ 1 / 4)
    (weight : ι → ℝ) (hweight : ∀ who, 0 ≤ weight who)
    (hweightSum : ∑ who, weight who = 1)
    (hweightImage : ∀ receiver,
      0 ≤ ∑ owner, quittingProjectiveLCPMatrix reward receiver owner * weight owner)
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ quittingSingletonBox reward bound, DifferentiableAt ℝ potential point)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (bound + 2)).IsPotential
        (fun state => potential state.1)) :
    (¬ IsQuittingSingletonBoxAdditive reward bound potential) ∧
      (¬ IsQuittingSingletonBoxRegularScalarComposition reward bound potential) := by
  have hdrift : ∀ point ∈ quittingSingletonBox reward bound, ∀ owner,
      point owner = quittingSoloReward reward owner owner →
      0 < fderiv ℝ potential point (point - quittingSoloReward reward owner) := by
    intro point hpoint owner howner
    have hface := (quittingRobustPotential_singletonFace_fderiv_bounds reward hreward
      htolerance0 htolerance1 potential hpotential point owner
      (fun who => ⟨hpoint.1 who, hpoint.2 who⟩) howner (hdiff point hpoint)).1
    have hsum : 0 ≤ ∑ who, |(fderiv ℝ potential point) (Pi.single who 1)| :=
      Finset.sum_nonneg fun who _ => abs_nonneg _
    have hterm := mul_nonneg htolerance0.le hsum
    linarith
  exact ⟨not_singletonBox_additive_of_simplex_positive_face_drift reward hreward
      weight hweight hweightSum hweightImage potential hdiff hdrift,
    not_singletonBox_scalarComposition_of_simplex_positive_face_drift reward hreward
      weight hweight hweightSum hweightImage potential hdiff hdrift⟩

end GameTheory
