/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.CategoricalRetracts
import Mathlib.CategoryTheory.Retract

/-!
# Categorical retract adapter for directed transport

One-base-flat path functors supply explicit ingress and return morphisms.  They
form Mathlib categorical retracts, connecting retract-flat transport to generic
results about split monomorphisms, split epimorphisms, and retracts.
-/

noncomputable section

namespace Math
namespace DirectedTransport

open CategoryTheory

universe uV uE uC vC

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {C : Type uC} [Category.{vC} C]

section

variable (F : PathCategory G ⥤ C) {base : V}
variable (paths : ∀ vertex, G.Walk base vertex)
variable (returns : ∀ vertex, G.Walk vertex base)

/-- The base object as an actual categorical retract of a vertex object. -/
def categoricalRetract (hflat : IsFlatAt F base) (vertex : V) :
    Retract (F.obj (PathCategory.ofVertex G base))
      (F.obj (PathCategory.ofVertex G vertex)) where
  i := categoricalIngress F paths vertex
  r := categoricalReturn F returns vertex
  retract := categoricalIngress_comp_return F hflat paths returns vertex

@[simp] theorem categoricalRetract_i
    (hflat : IsFlatAt F base) (vertex : V) :
    (categoricalRetract F paths returns hflat vertex).i =
      categoricalIngress F paths vertex := rfl

@[simp] theorem categoricalRetract_r
    (hflat : IsFlatAt F base) (vertex : V) :
    (categoricalRetract F paths returns hflat vertex).r =
      categoricalReturn F returns vertex := rfl

/-- The idempotent induced by the packaged retract is exactly the transport
projector used by categorical retract-flatness. -/
@[simp] theorem categoricalRetract_r_comp_i
    (hflat : IsFlatAt F base) (vertex : V) :
    (categoricalRetract F paths returns hflat vertex).r ≫
        (categoricalRetract F paths returns hflat vertex).i =
      categoricalRetractProjector F paths returns vertex := rfl

/-- The path-independent core map is the canonical return-ingress morphism
between the packaged endpoint retracts. -/
theorem categorical_compressed_map_eq_retract_r_comp_i
    (hflat : IsFlatAt F base) {source target : V}
    (walk : G.Walk source target) :
    categoricalRetractProjector F paths returns source ≫ F.map walk ≫
        categoricalRetractProjector F paths returns target =
      (categoricalRetract F paths returns hflat source).r ≫
        (categoricalRetract F paths returns hflat target).i := by
  exact categorical_compressed_map_eq F hflat paths returns walk

end

end DirectedTransport
end Math

end
