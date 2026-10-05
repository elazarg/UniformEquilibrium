import MathUE.Topology.SeparatelyAffineFiberLoops

/-! # Equal-fiber return connectors in a separately affine image

This is the concatenation and cancellation step of Sorin's printed fiber-loop
argument. Only payoff-image paths reverse; no reversal law is imposed on the
strategy mixers. The result does not assert that arbitrary image loops lift.
-/

noncomputable section

namespace Math.Topology

/-- Cancel the null bridge in a six-edge loop, then cancel the outgoing path.
All paths and homotopies are in the same space, including when it is an image subtype. -/
theorem return_homotopic_of_sixEdgeLoop
    {Z : Type*} [TopologicalSpace Z] {base first point middle last : Z}
    (out₁ : Path base first) (out₂ : Path first point)
    (bridge₁ : Path point middle) (bridge₂ : Path middle point)
    (back₁ : Path point last) (back₂ : Path last base)
    (hloop : (out₁.trans (out₂.trans (bridge₁.trans
      (bridge₂.trans (back₁.trans back₂))))).Homotopic (Path.refl base))
    (hbridge : (bridge₁.trans bridge₂).Homotopic (Path.refl point)) :
    (back₁.trans back₂).Homotopic (out₁.trans out₂).symm := by
  let outgoing := Path.Homotopic.Quotient.mk (out₁.trans out₂)
  let returning := Path.Homotopic.Quotient.mk (back₁.trans back₂)
  have hloopClass := Path.Homotopic.Quotient.eq.mpr hloop
  have hbridgeClass := Path.Homotopic.Quotient.eq.mpr hbridge
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl]
    at hloopClass hbridgeClass
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk bridge₁) (Path.Homotopic.Quotient.mk bridge₂)
    ((Path.Homotopic.Quotient.mk back₁).trans (Path.Homotopic.Quotient.mk back₂)),
    hbridgeClass, Path.Homotopic.Quotient.refl_trans] at hloopClass
  have hclosed : outgoing.trans returning = Path.Homotopic.Quotient.refl base := by
    simpa only [outgoing, returning, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.trans_assoc] using hloopClass
  apply Path.Homotopic.Quotient.exact
  change returning = outgoing.symm
  calc
    returning = (Path.Homotopic.Quotient.refl point).trans returning :=
      (Path.Homotopic.Quotient.refl_trans returning).symm
    _ = (outgoing.symm.trans outgoing).trans returning := by
      rw [Path.Homotopic.Quotient.symm_trans]
    _ = outgoing.symm.trans (outgoing.trans returning) :=
      Path.Homotopic.Quotient.trans_assoc _ _ _
    _ = outgoing.symm := by rw [hclosed, Path.Homotopic.Quotient.trans_refl]

namespace SeparatelyAffinePair

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {left : ContinuousMixer X} {right : ContinuousMixer Y}
  (field : SeparatelyAffinePair (E := E) left right)

theorem imageLeftPath_reverse (first last : X) (other : Y) :
    ((leftPath (left := left) first last other).map field.rangeMap.continuous).symm =
      (leftPath (left := left) last first other).map field.rangeMap.continuous := by
  apply Path.ext
  funext time
  apply Subtype.ext
  change field.value (left.mix (unitInterval.symm time, (last, first)), other) =
    field.value (left.mix (time, (first, last)), other)
  rw [field.affine_left, field.affine_left]
  simp only [unitInterval.coe_symm_eq, sub_sub_cancel]
  exact add_comm _ _

theorem imageRightPath_reverse (other : X) (first last : Y) :
    ((rightPath (right := right) other first last).map field.rangeMap.continuous).symm =
      (rightPath (right := right) other last first).map field.rangeMap.continuous := by
  apply Path.ext
  funext time
  apply Subtype.ext
  change field.value (other, right.mix (unitInterval.symm time, (last, first))) =
    field.value (other, right.mix (time, (first, last)))
  rw [field.affine_right, field.affine_right]
  simp only [unitInterval.coe_symm_eq, sub_sub_cancel]
  exact add_comm _ _

/-- Return to the base payoff by first restoring the second strategy, then the first. -/
def returnConnector (base point : X × Y) : Path (field.rangeMap point) (field.rangeMap base) :=
  ((rightPath (right := right) point.1 point.2 base.2).map
    field.rangeMap.continuous).trans
      ((leftPath (left := left) point.1 base.1 base.2).map field.rangeMap.continuous)

/-- The return connector's based homotopy class is independent of the chosen
strategy pair in one payoff fiber. Endpoint casts use literal payoff equality. -/
theorem returnConnector_homotopic_of_same_value
    (base : X × Y) (a a' : X) (b b' : Y)
    (hfiber : field.value (a, b) = field.value (a', b')) :
    ((field.returnConnector base (a, b)).cast
      (show field.rangeMap (a', b') = field.rangeMap (a, b) from
        Subtype.ext hfiber.symm) rfl).Homotopic
      (field.returnConnector base (a', b')) := by
  have hpoint : field.rangeMap (a', b') = field.rangeMap (a, b) :=
    Subtype.ext hfiber.symm
  have hloop := field.sixVertexLoop_nullhomotopic base a a' b b'
  simp only [sixVertexLoop, Path.map_trans] at hloop
  have hbridge := field.fiberBridge_nullhomotopic a a' b b' hfiber
  have hreturn := return_homotopic_of_sixEdgeLoop
    ((leftPath (left := left) base.1 a' base.2).map field.rangeMap.continuous)
    ((rightPath (right := right) a' base.2 b').map field.rangeMap.continuous)
    ((leftPath (left := left) a' a b').map field.rangeMap.continuous)
    (((rightPath (right := right) a b' b).map field.rangeMap.continuous).cast rfl hpoint)
    (((rightPath (right := right) a b base.2).map field.rangeMap.continuous).cast hpoint rfl)
    ((leftPath (left := left) a base.1 base.2).map field.rangeMap.continuous)
    hloop hbridge
  simp only [returnConnector, Path.cast_trans _ _ _ rfl _, Path.cast_rfl_rfl]
  simpa only [Path.trans_symm, field.imageRightPath_reverse,
    field.imageLeftPath_reverse] using hreturn

end SeparatelyAffinePair

end Math.Topology
