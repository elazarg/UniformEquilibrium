import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! # Fiber-loop correction for a separately affine image

The six-edge loop and backtracking bridge are the concrete homotopy step in
Sorin (1986), Proposition 11, page 155. Homotopies stay in the actual image
and fix their payoff base point. The strategy mixers need not fix equal inputs.
No winding-number theorem or simply-connectedness of the whole image is asserted.
-/

noncomputable section

namespace Math.Topology

open unitInterval

/-- Continuous interpolation with its two endpoints, without an idempotence law. -/
structure ContinuousMixer (X : Type*) [TopologicalSpace X] where
  mix : unitInterval × (X × X) → X
  continuous_mix : Continuous mix
  mix_zero : ∀ x y, mix (0, (x, y)) = y
  mix_one : ∀ x y, mix (1, (x, y)) = x

namespace ContinuousMixer

variable {X : Type*} [TopologicalSpace X]

/-- The mixer path starts at its first displayed endpoint. -/
def path (mixer : ContinuousMixer X) (first last : X) : Path first last where
  toFun time := mixer.mix (time, (last, first))
  continuous_toFun := mixer.continuous_mix.comp
    (continuous_id.prodMk continuous_const)
  source' := mixer.mix_zero last first
  target' := mixer.mix_one last first

end ContinuousMixer

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- A continuous map affine along each supplied coordinate mixer. -/
structure SeparatelyAffinePair (left : ContinuousMixer X) (right : ContinuousMixer Y) where
  value : X × Y → E
  continuous_value : Continuous value
  affine_left : ∀ (time : unitInterval) first last other,
    value (left.mix (time, (last, first)), other) =
      (time : ℝ) • value (last, other) + (1 - (time : ℝ)) • value (first, other)
  affine_right : ∀ (time : unitInterval) other first last,
    value (other, right.mix (time, (last, first))) =
      (time : ℝ) • value (other, last) + (1 - (time : ℝ)) • value (other, first)

namespace SeparatelyAffinePair

variable {left : ContinuousMixer X} {right : ContinuousMixer Y}
  (field : SeparatelyAffinePair (E := E) left right)

/-- Retain image membership rather than contracting in the ambient payoff space. -/
def rangeMap : C(X × Y, Set.range field.value) where
  toFun point := ⟨field.value point, point, rfl⟩
  continuous_toFun := field.continuous_value.subtype_mk _

/-- Equal strategy inputs may move, but their payoff stays fixed. -/
theorem diagonal_mix_value (base : X × Y) (time : unitInterval) :
    field.value (left.mix (time, (base.1, base.1)),
      right.mix (time, (base.2, base.2))) = field.value base := by
  simp only [field.affine_left, field.affine_right]
  simp [← add_smul]

/-- Every lifted closed strategy path has a based null-homotopy inside the image. -/
def imageLoopHomotopy (base : X × Y) (loop : Path base base) :
    (loop.map field.rangeMap.continuous).Homotopy (Path.refl (field.rangeMap base)) where
  toFun point := field.rangeMap
    (left.mix (point.1, (base.1, (loop point.2).1)),
      right.mix (point.1, (base.2, (loop point.2).2)))
  continuous_toFun := field.rangeMap.continuous.comp
    ((left.continuous_mix.comp
      (continuous_fst.prodMk (continuous_const.prodMk
        (continuous_fst.comp (loop.continuous.comp continuous_snd))))).prodMk
      (right.continuous_mix.comp
        (continuous_fst.prodMk (continuous_const.prodMk
          (continuous_snd.comp (loop.continuous.comp continuous_snd))))))
  map_zero_left time := by
    simp only [left.mix_zero, right.mix_zero]
    rfl
  map_one_left time := by
    simp only [left.mix_one, right.mix_one]
    rfl
  prop' time endpoint hendpoint := by
    rcases hendpoint with hzero | hone
    · subst endpoint
      apply Subtype.ext
      change field.value (left.mix (time, (base.1, (loop 0).1)),
        right.mix (time, (base.2, (loop 0).2))) = field.value (loop 0)
      rw [loop.source]
      exact field.diagonal_mix_value base time
    · rw [Set.mem_singleton_iff] at hone
      subst endpoint
      apply Subtype.ext
      change field.value (left.mix (time, (base.1, (loop 1).1)),
        right.mix (time, (base.2, (loop 1).2))) = field.value (loop 1)
      rw [loop.target]
      exact field.diagonal_mix_value base time

/-- Change the first strategy, leaving the second fixed. -/
def leftPath (first last : X) (other : Y) : Path (first, other) (last, other) :=
  (left.path first last).prod (Path.refl other)

/-- Change the second strategy, leaving the first fixed. -/
def rightPath (other : X) (first last : Y) : Path (other, first) (other, last) :=
  (Path.refl other).prod (right.path first last)

/-- The literal six-edge strategy loop in the fiber correction.
Its vertices are base, (a',b0), (a',b'), (a,b'), (a,b), (a,b0), base. -/
def sixVertexLoop (base : X × Y) (a a' : X) (b b' : Y) : Path base base :=
  (leftPath (left := left) base.1 a' base.2).trans
    ((rightPath (right := right) a' base.2 b').trans
      ((leftPath (left := left) a' a b').trans
        ((rightPath (right := right) a b' b).trans
          ((rightPath (right := right) a b base.2).trans
            (leftPath (left := left) a base.1 base.2)))))

/-- The payoff image of the displayed six-edge loop contracts in the payoff image. -/
theorem sixVertexLoop_nullhomotopic (base : X × Y) (a a' : X) (b b' : Y) :
    ((sixVertexLoop (left := left) (right := right) base a a' b b').map
      field.rangeMap.continuous).Homotopic (Path.refl (field.rangeMap base)) :=
  ⟨field.imageLoopHomotopy base (sixVertexLoop base a a' b b')⟩

/-- Equality of the two endpoint payoffs makes the inserted two-edge bridge
an exact backtrack, not just a loop in the ambient vector space. -/
theorem fiberBridge_return_eq_reverse (a a' : X) (b b' : Y)
    (hfiber : field.value (a, b) = field.value (a', b')) :
    (((rightPath (right := right) a b' b).map field.rangeMap.continuous).cast rfl
      (show field.rangeMap (a', b') = field.rangeMap (a, b) from
        Subtype.ext hfiber.symm)) =
      ((leftPath (left := left) a' a b').map field.rangeMap.continuous).symm := by
  apply Path.ext
  funext time
  apply Subtype.ext
  change field.value (a, right.mix (time, (b, b'))) =
    field.value (left.mix (unitInterval.symm time, (a, a')), b')
  rw [field.affine_right, field.affine_left, hfiber]
  simp only [unitInterval.coe_symm_eq, sub_sub_cancel]
  exact add_comm _ _

/-- The equal-fiber bridge is null-homotopic in the actual payoff image. -/
theorem fiberBridge_nullhomotopic (a a' : X) (b b' : Y)
    (hfiber : field.value (a, b) = field.value (a', b')) :
    (((leftPath (left := left) a' a b').map field.rangeMap.continuous).trans
      (((rightPath (right := right) a b' b).map field.rangeMap.continuous).cast rfl
        (show field.rangeMap (a', b') = field.rangeMap (a, b) from
          Subtype.ext hfiber.symm))).Homotopic (Path.refl (field.rangeMap (a', b'))) := by
  rw [field.fiberBridge_return_eq_reverse a a' b b' hfiber]
  exact Path.Homotopic.trans_symm _

end SeparatelyAffinePair

end Math.Topology
