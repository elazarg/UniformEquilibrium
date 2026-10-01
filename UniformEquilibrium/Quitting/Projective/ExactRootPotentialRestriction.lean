import UniformEquilibrium.Quitting.Projective.RobustChargedRelation
import UniformEquilibrium.Quitting.Root.BoundedEndpoint

/-! # The same robust potential on every boxed exact root

Continuation annotations need no behavioral realization. The root and its
successor are the canonical product-root objects; only their errors vanish.
-/

noncomputable section

namespace GameTheory

open Maths.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every exact Nash root and its exact successor give a robust edge. -/
theorem isQuittingFloorFreeRobustEdge_of_exactRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {tolerance bound : ℝ} (htolerance : 0 ≤ tolerance)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (source : QuittingRobustChargedState ι bound) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward source.1 0 root) :
    IsQuittingFloorFreeRobustEdge reward tolerance bound source
      (quittingSimplexOfRoot root)
      ⟨quittingRootSuccessorPayoff reward source.1 root,
        fun who => abs_quittingRootSuccessorPayoff_le_bound
          reward source.1 root who hreward source.2⟩ := by
  have hcharge := mul_nonneg htolerance (quittingRootAbsorptionMass_nonneg root)
  have hdefect := (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
    reward source.1 root).mp hnash
  intro who
  simpa only [quittingRobustChargedEdgeResidual, quittingRobustChargedEdgeRegret,
    quittingRobustChargedEdgeAbsorption, quittingRootOfSimplex_simplexOfRoot,
    sub_self, abs_zero, hdefect who] using And.intro hcharge hcharge

/-- Unit absorption drift on all boxed exact roots, with no root selection. -/
def IsQuittingFullExactRootPotential
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (potential : Payoff ι → ℝ) : Prop :=
  ∀ tail, (∀ who, |tail who| ≤ bound) → ∀ root,
    IsεQuittingRootNash reward tail 0 root →
      potential (quittingRootSuccessorPayoff reward tail root) +
        quittingRootAbsorptionMass root ≤ potential tail

/-- Restrict the same function from the full robust relation to exact roots. -/
theorem isQuittingFullExactRootPotential_of_robustPotential
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {tolerance bound : ℝ} (htolerance : 0 ≤ tolerance)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (potential : Payoff ι → ℝ)
    (hpotential : (quittingFloorFreeRobustChargedRelation reward tolerance bound).IsPotential
      (fun state => potential state.1)) :
    IsQuittingFullExactRootPotential reward bound potential := by
  intro tail htail root hnash
  let source : QuittingRobustChargedState ι bound := ⟨tail, htail⟩
  let target : QuittingRobustChargedState ι bound :=
    ⟨quittingRootSuccessorPayoff reward tail root,
      fun who => abs_quittingRootSuccessorPayoff_le_bound
        reward tail root who hreward htail⟩
  let edge : QuittingRobustChargedEdge reward tolerance bound :=
    ⟨((source, quittingSimplexOfRoot root), target),
      isQuittingFloorFreeRobustEdge_of_exactRoot reward htolerance hreward source root hnash⟩
  simpa only [quittingFloorFreeRobustChargedRelation, source, target, edge,
    quittingRootOfSimplex_simplexOfRoot] using hpotential edge

/-- Restriction retains the identical potential, game, actual root and successor. -/
theorem IsQuittingFullExactRootPotential.mono_box
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {small large : ℝ} {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward large potential)
    (hbox : small ≤ large) :
    IsQuittingFullExactRootPotential reward small potential := by
  intro tail htail root hnash
  exact hpotential tail (fun who => (htail who).trans hbox) root hnash

/-- The larger robust box used by the polynomial interface supplies the smaller
exact box used by the shape packet, for the same function. -/
theorem isQuittingFullExactRootPotential_add_one_of_robust_add_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M tolerance : ℝ} (htolerance : 0 ≤ tolerance)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (potential : Payoff ι → ℝ)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (M + 2)).IsPotential
        (fun state => potential state.1)) :
    IsQuittingFullExactRootPotential reward (M + 1) potential := by
  have hlarge := isQuittingFullExactRootPotential_of_robustPotential reward htolerance
    (fun terminal who => (hreward terminal who).trans (by linarith)) potential hpotential
  exact hlarge.mono_box (by linarith)

end GameTheory
