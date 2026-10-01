import UniformEquilibrium.ProofView.Concepts.Existence.ProductSimplexBrouwer
import MathUE.Topology.ConnectedFixedPointContinuation

/-! # Connected continuation on the existing product simplex

The canonical coordinate homeomorphism transports the checked interval fixed-point
continuation theorem. No component hypothesis or new separation argument is used.
-/

noncomputable section

namespace GameTheory

variable {ι : Type*} {Action : ι → Type*}
variable [Fintype ι] [∀ who, Fintype (Action who)] [∀ who, Nonempty (Action who)]

/-- A jointly continuous family on the product simplex has one compact connected
set of actual fixed points meeting both endpoint fibers. -/
theorem exists_compact_connected_mixedSimplex_fixedPoint_continuation
    (f : C(unitInterval × MixedSimplex ι Action, MixedSimplex ι Action)) :
    ∃ component : Set (unitInterval × MixedSimplex ι Action),
      IsCompact component ∧ IsConnected component ∧
      (∀ point ∈ component, f point = point.2) ∧
      (∃ simplex, (0, simplex) ∈ component) ∧
      (∃ simplex, (1, simplex) ∈ component) := by
  classical
  let e := mixedSimplexHomeomorph (ι := ι) (A := Action)
  let lift : C(unitInterval × ↥(mixedSimplexAsSet ι Action),
      ↥(mixedSimplexAsSet ι Action)) :=
    ⟨fun point => e (f (point.1, e.symm point.2)),
      e.continuous.comp
        (f.continuous.comp (continuous_fst.prodMk
          (e.symm.continuous.comp continuous_snd)))⟩
  obtain ⟨component, hcompact, hconnected, hfixed, hzero, hone⟩ :=
    Math.exists_compact_connected_fixedPoint_continuation
      (convex_mixedSimplexAsSet (ι := ι) (A := Action))
      (isCompact_mixedSimplexAsSet (ι := ι) (A := Action))
      (nonempty_mixedSimplexAsSet (ι := ι) (A := Action)) lift
  let decode := fun point : unitInterval × ↥(mixedSimplexAsSet ι Action) =>
    (point.1, e.symm point.2)
  have hdecode : Continuous decode :=
    continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)
  refine ⟨decode '' component, hcompact.image hdecode,
    hconnected.image decode hdecode.continuousOn, ?_, ?_, ?_⟩
  · rintro point ⟨source, hsource, rfl⟩
    have hequal := congrArg e.symm (hfixed source hsource)
    change e.symm (e (f (source.1, e.symm source.2))) = e.symm source.2 at hequal
    simpa only [e.symm_apply_apply] using hequal
  · obtain ⟨simplex, hsimplex⟩ := hzero
    exact ⟨e.symm simplex, ⟨(0, simplex), hsimplex, rfl⟩⟩
  · obtain ⟨simplex, hsimplex⟩ := hone
    exact ⟨e.symm simplex, ⟨(1, simplex), hsimplex, rfl⟩⟩

end GameTheory
