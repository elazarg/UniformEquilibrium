import MathUE.Topology.SeparatelyAffineFiberConnectors
import MathUE.Topology.QuotientFiberCollision

/-! # Actual prefix-and-return loops in a separately affine image

Every incidence pairs a time on an image loop with strategies realizing its
value. Follow the loop up to that time, then restore the second and first
strategies. This is a continuous family in the image itself. Equal-time slices
are homotopic, and the original base strategy pair normalizes the endpoints.
-/

noncomputable section

namespace Math.Topology

/-- A prefix with its literal moving endpoint, using the constant-extension truncation. -/
def loopPrefix {Z : Type*} [TopologicalSpace Z] {base : Z}
    (loop : Path base base) (time : unitInterval) : Path base (loop time) :=
  (loop.truncateOfLE (t₀ := 0) (t₁ := (time : ℝ)) time.2.1).cast
    loop.extend_zero.symm (loop.extend_extends' time).symm

theorem loopPrefix_continuous {Z : Type*} [TopologicalSpace Z] {base : Z}
    (loop : Path base base) :
    Continuous (fun point : unitInterval × unitInterval => loopPrefix loop point.1 point.2) := by
  exact (loop.truncate_const_continuous_family 0).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

namespace SeparatelyAffinePair

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {left : ContinuousMixer X} {right : ContinuousMixer Y}
  (field : SeparatelyAffinePair (E := E) left right)

theorem returnConnector_continuous (base : X × Y) :
    Continuous (fun point : (X × Y) × unitInterval =>
      field.returnConnector base point.1 point.2) := by
  apply Path.trans_continuous_family
    (fun point : X × Y => (rightPath (right := right) point.1 point.2 base.2).map
      field.rangeMap.continuous) _
    (fun point : X × Y => (leftPath (left := left) point.1 base.1 base.2).map
      field.rangeMap.continuous) _
  · exact field.rangeMap.continuous.comp
      ((continuous_fst.fst).prodMk (right.continuous_mix.comp
        (continuous_snd.prodMk (continuous_const.prodMk continuous_fst.snd))))
  · exact field.rangeMap.continuous.comp
      ((left.continuous_mix.comp
        (continuous_snd.prodMk (continuous_const.prodMk continuous_fst.fst))).prodMk
          continuous_const)

/-- The return path at the base pair is constant in payoff, even if its
strategy mixers are not idempotent. -/
theorem returnConnector_base (base : X × Y) :
    field.returnConnector base base = Path.refl (field.rangeMap base) := by
  have hright : ((rightPath (right := right) base.1 base.2 base.2).map
      field.rangeMap.continuous) = Path.refl (field.rangeMap base) := by
    apply Path.ext
    funext time
    apply Subtype.ext
    change field.value (base.1, right.mix (time, (base.2, base.2))) = field.value base
    rw [field.affine_right]
    simp [← add_smul]
  have hleft : ((leftPath (left := left) base.1 base.1 base.2).map
      field.rangeMap.continuous) = Path.refl (field.rangeMap base) := by
    apply Path.ext
    funext time
    apply Subtype.ext
    change field.value (left.mix (time, (base.1, base.1)), base.2) = field.value base
    rw [field.affine_left]
    simp [← add_smul]
  rw [returnConnector, hright, hleft, Path.refl_trans_refl]

/-- Realizations of the actual image loop, not a chosen lifting of it. -/
abbrev LoopIncidence (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base)) :=
  ImageIncidence (fun time => loop time) field.rangeMap

/-- A return connector cast using the incidence's exact payoff equality. -/
def incidenceReturn (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base))
    (point : field.LoopIncidence base loop) :
    Path (loop point.val.1) (field.rangeMap base) :=
  (field.returnConnector base point.val.2).cast point.property rfl

/-- The literal loop prefix followed by the two-coordinate return. -/
def prefixReturnLoop (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base))
    (point : field.LoopIncidence base loop) :
    Path (field.rangeMap base) (field.rangeMap base) :=
  (loopPrefix loop point.val.1).trans (field.incidenceReturn base loop point)

theorem prefixReturnLoop_continuous (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base)) :
    Continuous (fun point : field.LoopIncidence base loop × unitInterval =>
      field.prefixReturnLoop base loop point.1 point.2) := by
  let prefixPath : ∀ point : field.LoopIncidence base loop,
      Path (field.rangeMap base) (loop point.val.1) :=
    fun point => loopPrefix loop point.val.1
  let returning : ∀ point : field.LoopIncidence base loop,
      Path (loop point.val.1) (field.rangeMap base) := field.incidenceReturn base loop
  have hprefix : Continuous (fun point : field.LoopIncidence base loop × unitInterval =>
      prefixPath point.1 point.2) := by
    let coordinates : field.LoopIncidence base loop × unitInterval →
        unitInterval × unitInterval := fun point => (point.1.val.1, point.2)
    have hcoordinates : Continuous coordinates :=
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
    have hcomposition : Continuous
        ((fun point : unitInterval × unitInterval => loopPrefix loop point.1 point.2) ∘
          coordinates) := (loopPrefix_continuous loop).comp hcoordinates
    exact hcomposition.congr (fun _ => rfl)
  have hreturning : Continuous (fun point : field.LoopIncidence base loop × unitInterval =>
      returning point.1 point.2) := by
    let coordinates : field.LoopIncidence base loop × unitInterval →
        (X × Y) × unitInterval := fun point => (point.1.val.2, point.2)
    have hcoordinates : Continuous coordinates :=
      (continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
    have hcomposition : Continuous
        ((fun point : (X × Y) × unitInterval => field.returnConnector base point.1 point.2) ∘
          coordinates) := (field.returnConnector_continuous base).comp hcoordinates
    exact hcomposition.congr (fun _ => rfl)
  have htrans : Continuous (fun point : field.LoopIncidence base loop × unitInterval =>
      (prefixPath point.1).trans (returning point.1) point.2) :=
    Path.trans_continuous_family prefixPath hprefix returning hreturning
  exact htrans.congr (fun _ => rfl)

/-- The uncurried path family, with the incidence before path time. -/
def prefixReturnMap (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base)) :
    C(field.LoopIncidence base loop × unitInterval, Set.range field.value) :=
  ⟨fun point => field.prefixReturnLoop base loop point.1 point.2,
    field.prefixReturnLoop_continuous base loop⟩

/-- Time is the first coordinate, matching the covering loop-family interface. -/
def prefixReturnFamily (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base)) :
    C(unitInterval × field.LoopIncidence base loop, Set.range field.value) :=
  (field.prefixReturnMap base loop).comp ⟨Prod.swap, continuous_swap⟩

theorem prefixReturnFamily_zero (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base))
    (point : field.LoopIncidence base loop) :
    field.prefixReturnFamily base loop (0, point) = field.rangeMap base :=
  (field.prefixReturnLoop base loop point).source

theorem prefixReturnFamily_one (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base))
    (point : field.LoopIncidence base loop) :
    field.prefixReturnFamily base loop (1, point) = field.rangeMap base :=
  (field.prefixReturnLoop base loop point).target

/-- Equal-time realizations give homotopic prefix-and-return loops in the image. -/
theorem prefixReturnLoop_homotopic_of_same_time (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base))
    (first last : field.LoopIncidence base loop) (htime : first.val.1 = last.val.1) :
    (field.prefixReturnLoop base loop first).Homotopic
      (field.prefixReturnLoop base loop last) := by
  rcases first with ⟨⟨time, point⟩, hpoint⟩
  rcases last with ⟨⟨other, target⟩, htarget⟩
  dsimp only at htime
  subst other
  have hfiber : field.value point = field.value target :=
    congrArg Subtype.val (hpoint.symm.trans htarget)
  have hreturn := field.returnConnector_homotopic_of_same_value
    base point.1 target.1 point.2 target.2 hfiber
  have hcast := hreturn.pathCast htarget rfl
  exact (Path.Homotopic.refl (loopPrefix loop time)).hcomp hcast

/-- The original base strategy pair at the initial time is an actual incidence. -/
def initialIncidence (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base)) :
    field.LoopIncidence base loop := ⟨(0, base), loop.source⟩

/-- The original base strategy pair also realizes the final time. -/
def finalIncidence (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base)) :
    field.LoopIncidence base loop := ⟨(1, base), loop.target⟩

theorem prefixReturnLoop_initial (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base)) :
    field.prefixReturnLoop base loop (field.initialIncidence base loop) =
      Path.refl (field.rangeMap base) := by
  have hprefix : loopPrefix loop 0 = (Path.refl (field.rangeMap base)).cast rfl loop.source := by
    apply Path.ext
    funext time
    simp [loopPrefix, Path.truncateOfLE, Path.truncate]
  simp only [prefixReturnLoop, initialIncidence, incidenceReturn, returnConnector_base, hprefix]
  exact Path.refl_trans_refl

/-- At the final incidence only a constant return is appended to the original loop. -/
theorem prefixReturnLoop_final_homotopic (base : X × Y)
    (loop : Path (field.rangeMap base) (field.rangeMap base)) :
    (field.prefixReturnLoop base loop (field.finalIncidence base loop)).Homotopic loop := by
  have hprefix : loopPrefix loop 1 = loop.cast rfl loop.target := by
    apply Path.ext
    funext time
    simp [loopPrefix, Path.truncateOfLE]
  have hloop : field.prefixReturnLoop base loop (field.finalIncidence base loop) =
      loop.trans (Path.refl (field.rangeMap base)) := by
    dsimp only [prefixReturnLoop, finalIncidence, incidenceReturn]
    rw [hprefix, field.returnConnector_base]
    exact (Path.cast_trans loop (Path.refl (field.rangeMap base))
      rfl loop.target rfl).symm
  rw [hloop]
  exact Path.Homotopic.trans_refl loop

end SeparatelyAffinePair

end Math.Topology
