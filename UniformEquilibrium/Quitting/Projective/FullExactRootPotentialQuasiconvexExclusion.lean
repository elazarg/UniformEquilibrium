import MathUE.Analysis.QuasiconvexLowerBoxBoundary
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialMinimum
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction

/-! # Matrix-free quasiconvex exclusion for the full exact-root relation

Signed singleton rewards and arbitrary finite nonempty player sets are allowed.
All exact roots at all boxed annotations belong to the unchanged source relation.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology
open Maths.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A continuous full exact-root potential, differentiable on the upper
singleton rectangle, cannot be quasiconvex there. No matrix premise is used. -/
theorem IsQuittingFullExactRootPotential.not_quasiconvex
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (hcontinuous : ContinuousOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)))
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => bound), DifferentiableAt ℝ potential point) :
    ¬QuasiconvexOn ℝ (Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => bound)) potential := by
  intro hquasiconvex
  let lower : Payoff ι := fun who => quittingSoloReward reward who who
  let upper : Payoff ι := fun _ => bound
  let face : ι → Payoff ι := quittingSoloReward reward
  have hwidth : ∀ who, lower who < upper who := fun who =>
    ((le_abs_self _).trans (hreward (quittingSingletonTerminal who) who)).trans_lt hbound
  obtain ⟨point, boundary, hpoint, hboundary, _, _, hboundaryMin, hgap⟩ :=
    hpotential.exists_minima_strict_gap hreward hbound hcontinuous hdiff
  let derivative := fderiv ℝ potential boundary
  have hderivative : HasFDerivAt potential derivative boundary :=
    (hdiff boundary hboundary.1).hasFDerivAt
  have hdiagonal : ∀ who, face who who = lower who := fun _ => rfl
  have hfaceUpper : ∀ owner other, face owner other ≤ upper other :=
    fun owner other => (le_abs_self _).trans
      ((hreward (quittingSingletonTerminal owner) other).trans hbound.le)
  have hdrift : ∀ owner, boundary owner = lower owner →
      0 < derivative (boundary - face owner) := by
    intro owner howner
    exact (show (0 : ℝ) < 1 by norm_num).trans_le
      (hpotential.singletonFace_drift hreward hbound boundary owner
        (fun who => ⟨hboundary.1.1 who, hboundary.1.2 who⟩) howner derivative hderivative)
  have hminimum := Math.lowerBoxBoundary_minimum_isMinOn_of_quasiconvex
    lower upper boundary potential derivative face hboundary hboundaryMin hderivative
    hwidth hdiagonal hfaceUpper hdrift hquasiconvex
  exact (not_lt_of_ge (hminimum hpoint)) hgap

/-- Quasiconvexity produces an actual boxed source and exact Nash root that
strictly violate unit absorption drift. Positive absorption is derived,
and the target is the identical canonical product-root successor. -/
theorem exists_positive_exactRoot_potential_violation_of_quasiconvex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) (potential : Payoff ι → ℝ)
    (hcontinuous : ContinuousOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)))
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => bound), DifferentiableAt ℝ potential point)
    (hquasiconvex : QuasiconvexOn ℝ (Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => bound)) potential) :
    ∃ source root,
      (∀ who, |source who| ≤ bound) ∧ IsεQuittingRootNash reward source 0 root ∧
      0 < quittingRootAbsorptionMass root ∧
      (∀ who, |quittingRootSuccessorPayoff reward source root who| ≤ bound) ∧
      potential source - potential (quittingRootSuccessorPayoff reward source root) <
        quittingRootAbsorptionMass root := by
  classical
  have hnot : ¬IsQuittingFullExactRootPotential reward bound potential := by
    intro hpotential
    exact hpotential.not_quasiconvex hreward hbound hcontinuous hdiff hquasiconvex
  unfold IsQuittingFullExactRootPotential at hnot
  push Not at hnot
  obtain ⟨source, hsource, root, hnash, hviolation⟩ := hnot
  have hpositive : 0 < quittingRootAbsorptionMass root := by
    by_contra hnotPositive
    have habsorption : quittingRootAbsorptionMass root = 0 :=
      le_antisymm (le_of_not_gt hnotPositive) (quittingRootAbsorptionMass_nonneg root)
    have hcontinue : quittingStationaryContinueMass root = 1 := by
      unfold quittingRootAbsorptionMass at habsorption
      linarith
    have hroot : root = quittingAllContinueRoot := by
      funext who
      exact eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who
    rw [habsorption, hroot, quittingRootSuccessorPayoff_allContinueRoot_eq] at hviolation
    linarith
  refine ⟨source, root, hsource, hnash, hpositive, ?_, ?_⟩
  · intro who
    exact abs_quittingRootSuccessorPayoff_le_bound reward source root who
      (fun terminal who => (hreward terminal who).trans hbound.le) hsource
  · linarith

/-- The robust relation on radius M+2 rejects quasiconvexity on the packet's
smaller upper-singleton rectangle, retaining the identical potential and table. -/
theorem not_quasiconvex_of_quittingRobustPotential_add_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M tolerance : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htolerance : 0 ≤ tolerance) (potential : Payoff ι → ℝ)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (M + 2)).IsPotential
        (fun state => potential state.1))
    (hcontinuous : ContinuousOn potential
      (Set.Icc (fun _ => -(M + 1)) (fun _ => M + 1)))
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => M + 1), DifferentiableAt ℝ potential point) :
    ¬QuasiconvexOn ℝ (Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => M + 1)) potential := by
  have hexact := isQuittingFullExactRootPotential_add_one_of_robust_add_two
    reward htolerance hreward potential hpotential
  exact hexact.not_quasiconvex hreward (by linarith) hcontinuous hdiff

/-- Every regular quasiconvex candidate has a literal rejecting robust edge
at every nonnegative supplied tolerance. Its endpoints already lie in radius
M+1, its root is exact Nash, and its target is the actual identical successor. -/
theorem exists_positive_quittingRobustEdge_potential_violation_of_quasiconvex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M tolerance : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htolerance : 0 ≤ tolerance) (potential : Payoff ι → ℝ)
    (hcontinuous : ContinuousOn potential
      (Set.Icc (fun _ => -(M + 1)) (fun _ => M + 1)))
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => M + 1), DifferentiableAt ℝ potential point)
    (hquasiconvex : QuasiconvexOn ℝ (Set.Icc
      (fun who => quittingSoloReward reward who who) (fun _ => M + 1)) potential) :
    ∃ source : QuittingRobustChargedState ι (M + 2), ∃ root : ι → PMF Bool,
      ∃ target : QuittingRobustChargedState ι (M + 2),
      (∀ who, |source.1 who| ≤ M + 1) ∧ (∀ who, |target.1 who| ≤ M + 1) ∧
      IsεQuittingRootNash reward source.1 0 root ∧
      target.1 = quittingRootSuccessorPayoff reward source.1 root ∧
      IsQuittingFloorFreeRobustEdge reward tolerance (M + 2) source
        (quittingSimplexOfRoot root) target ∧
      0 < quittingRootAbsorptionMass root ∧
      potential source.1 - potential target.1 < quittingRootAbsorptionMass root := by
  obtain ⟨tail, root, htail, hnash, hpositive, hsuccessor, hdrop⟩ :=
    exists_positive_exactRoot_potential_violation_of_quasiconvex reward hreward
      (show M < M + 1 by linarith) potential hcontinuous hdiff hquasiconvex
  let source : QuittingRobustChargedState ι (M + 2) :=
    ⟨tail, fun who => (htail who).trans (by linarith)⟩
  let target : QuittingRobustChargedState ι (M + 2) :=
    ⟨quittingRootSuccessorPayoff reward tail root,
      fun who => (hsuccessor who).trans (by linarith)⟩
  have hedge : IsQuittingFloorFreeRobustEdge reward tolerance (M + 2) source
      (quittingSimplexOfRoot root) target :=
    isQuittingFloorFreeRobustEdge_of_exactRoot reward htolerance
      (fun terminal who => (hreward terminal who).trans (by linarith)) source root hnash
  exact ⟨source, root, target, htail, hsuccessor, hnash, rfl, hedge, hpositive, hdrop⟩

end GameTheory
