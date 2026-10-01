import MathUE.Analysis.LowerBoxBoundaryMinimum
import Mathlib.Analysis.Convex.Quasiconvex

/-! # Quasiconvexity at minima on the union of lower box faces -/

noncomputable section

namespace Math

open Set Filter Topology

section FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The usual first-order quasiconvex inequality holds at boundary points too.
It is obtained from the actual convex sublevel and its positive tangent cone. -/
theorem quasiconvexOn_hasFDerivAt_sub_nonpos
    (domain : Set E) (potential : E → ℝ) (point target : E)
    (derivative : E →L[ℝ] ℝ) (hquasiconvex : QuasiconvexOn ℝ domain potential)
    (hpoint : point ∈ domain) (htarget : target ∈ domain)
    (hvalue : potential target ≤ potential point)
    (hdiff : HasFDerivAt potential derivative point) :
    derivative (target - point) ≤ 0 := by
  have hlocal : IsLocalMaxOn potential {value ∈ domain | potential value ≤ potential point}
      point := Filter.mem_of_superset self_mem_nhdsWithin (fun _ hmem => hmem.2)
  exact hlocal.hasFDerivWithinAt_nonpos hdiff.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset
      ((hquasiconvex (potential point)).segment_subset
        ⟨hpoint, le_rfl⟩ ⟨htarget, hvalue⟩))

end FirstOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Under positive face drift a quasiconvex function's lower-boundary minimum
is a minimum on the whole box. Only a derivative at the given minimum is needed;
every strictly better boxed point is already above all lower faces. -/
theorem lowerBoxBoundary_minimum_isMinOn_of_quasiconvex
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ) (face : ι → ι → ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (hwidth : ∀ player, lower player < upper player)
    (hdiagonal : ∀ player, face player player = lower player)
    (hfaceUpper : ∀ player other, face player other ≤ upper other)
    (hdrift : ∀ player, point player = lower player →
      0 < derivative (point - face player))
    (hquasiconvex : QuasiconvexOn ℝ (Set.Icc lower upper) potential) :
    IsMinOn potential (Set.Icc lower upper) point := by
  intro target htarget
  by_contra hnot
  have hvalue : potential target < potential point := lt_of_not_ge hnot
  have hstrictLower : ∀ player, lower player < target player := by
    intro player
    apply lt_of_le_of_ne (htarget.1 player)
    intro heq
    have hboundary : target ∈ lowerBoxBoundary lower upper :=
      ⟨htarget, player, heq.symm⟩
    exact (not_lt_of_ge (hmin hboundary)) hvalue
  have hpositive := lowerBoxBoundary_minimum_derivative_toward_strictLower_pos
    lower upper point potential derivative face hpoint hmin hdiff hwidth hdiagonal
    hfaceUpper hdrift target hstrictLower htarget.2
  have hnonpos := quasiconvexOn_hasFDerivAt_sub_nonpos (Set.Icc lower upper)
    potential point target derivative hquasiconvex hpoint.1 htarget hvalue.le hdiff
  exact (not_lt_of_ge hnonpos) hpositive

end Math
