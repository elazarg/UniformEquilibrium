import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Discrete labels on fibers of a compact quotient

If a continuous discrete label takes two different values on a compact
space mapping onto a Hausdorff preconnected space, then some actual fiber
contains two points with different labels. No continuous fiber selector is
assumed. This is the compactness step in Sorin (1986), Proposition 11.
-/

namespace Math.Topology

/-- Two different continuous discrete labels force disagreement within an
actual fiber of a compact-to-Hausdorff preconnected quotient. -/
theorem exists_same_fiber_different_labels
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [CompactSpace X] [T2Space Y]
    [PreconnectedSpace Y] [DiscreteTopology Z]
    (projection : C(X, Y)) (hsurjective : Function.Surjective projection)
    (label : C(X, Z)) {first last : X} (hne : label first ≠ label last) :
    ∃ left right : X, projection left = projection right ∧ label left ≠ label right := by
  classical
  by_contra hnone
  have hfactors : Function.FactorsThrough label projection := by
    intro left right hequal
    by_contra hlabels
    exact hnone ⟨left, right, hequal, hlabels⟩
  have hquotient : _root_.Topology.IsQuotientMap projection :=
    _root_.Topology.IsQuotientMap.of_surjective_continuous
      hsurjective projection.continuous
  let descended : C(Y, Z) := hquotient.lift label hfactors
  have hcomp : descended.comp projection = label :=
    hquotient.lift_comp label hfactors
  have hconstant : descended (projection first) = descended (projection last) :=
    PreconnectedSpace.constant (inferInstance : PreconnectedSpace Y) descended.continuous
  apply hne
  calc
    label first = descended (projection first) :=
      (DFunLike.congr_fun hcomp first).symm
    _ = descended (projection last) := hconstant
    _ = label last := DFunLike.congr_fun hcomp last

end Math.Topology
