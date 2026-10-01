import UniformEquilibrium.ProofView.Concepts.Existence.ProductSimplexBrouwer
import MathUE.Topology.CompactConnectedFixedPointGraph

/-!
# Product-simplex fixed points over compact connected parameter sets

The parameter set need not admit paths between its points. The canonical simplex
homeomorphism transports the generic connected-parameter theorem once.
-/

namespace GameTheory

variable {X ι : Type*} {Action : ι → Type*}
variable [MetricSpace X] [LocallyPathConnectedSpace X]
variable [Fintype ι] [∀ who, Fintype (Action who)] [∀ who, Nonempty (Action who)]

/-- Above any two points of a compact preconnected parameter set there are
actual product-simplex fixed points in one compact connected graph subset. -/
theorem exists_compact_connected_mixedSimplex_graph_over_connected_set
    (f : C(X × MixedSimplex ι Action, MixedSimplex ι Action))
    (D : Set X) (hDcompact : IsCompact D) (hD : IsPreconnected D)
    (x : X) (hx : x ∈ D) (y : X) (hy : y ∈ D) :
    ∃ component : Set (X × MixedSimplex ι Action),
      IsCompact component ∧ IsConnected component ∧
      (∀ point ∈ component, point.1 ∈ D ∧ f point = point.2) ∧
      (∃ simplex, (x, simplex) ∈ component) ∧
      (∃ simplex, (y, simplex) ∈ component) := by
  classical
  let e := mixedSimplexHomeomorph (ι := ι) (A := Action)
  let lift : C(X × ↥(mixedSimplexAsSet ι Action), ↥(mixedSimplexAsSet ι Action)) :=
    ⟨fun point => e (f (point.1, e.symm point.2)),
      e.continuous.comp
        (f.continuous.comp (continuous_fst.prodMk
          (e.symm.continuous.comp continuous_snd)))⟩
  obtain ⟨component, hcompact, hconnected, hfixed, hfirst, hlast⟩ :=
    Math.exists_compact_connected_fixedPoint_graph_over_connected_set
      (convex_mixedSimplexAsSet (ι := ι) (A := Action))
      (isCompact_mixedSimplexAsSet (ι := ι) (A := Action))
      (nonempty_mixedSimplexAsSet (ι := ι) (A := Action))
      lift D hDcompact hD x hx y hy
  let decode := fun point : X × ↥(mixedSimplexAsSet ι Action) =>
    (point.1, e.symm point.2)
  have hdecode : Continuous decode :=
    continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)
  refine ⟨decode '' component, hcompact.image hdecode,
    hconnected.image decode hdecode.continuousOn, ?_, ?_, ?_⟩
  · rintro point ⟨source, hsource, rfl⟩
    refine ⟨(hfixed source hsource).1, ?_⟩
    have hequal := congrArg e.symm (hfixed source hsource).2
    change e.symm (e (f (source.1, e.symm source.2))) = e.symm source.2 at hequal
    simpa only [e.symm_apply_apply] using hequal
  · obtain ⟨simplex, hsimplex⟩ := hfirst
    exact ⟨e.symm simplex, ⟨(x, simplex), hsimplex, rfl⟩⟩
  · obtain ⟨simplex, hsimplex⟩ := hlast
    exact ⟨e.symm simplex, ⟨(y, simplex), hsimplex, rfl⟩⟩

end GameTheory
