import UniformEquilibrium.VanishingDiscount.Bellman.Germ
import MathUE.CurveSelection.PolynomialSignCellArc

/-!
# Analytic Bellman germs through a specified complete assignment

The supplied endpoint is retained literally. Unconditional finite polynomial
sign-cell curve selection provides the arc; no Fink endpoint is reselected.
This theorem does not construct a closure witness from a root-only game source.
-/

noncomputable section

open Math Math.PolynomialSignCell Set Topology

namespace GameTheory.StochasticGame

variable {ι : Type} (G : StochasticGame ι)
  [Fintype G.State] [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Every specified complete assignment approached by positive-discount
polynomial Bellman solutions is the literal endpoint of an analytic Bellman germ. -/
theorem exists_analyticBellmanGerm_of_mem_closure_positiveDiscount
    (assignment : BellmanVar G → ℝ)
    (hdiscount : assignment BellmanVar.disc = 0)
    (hclosure : assignment ∈ closure
      (G.polynomialBellmanSolutionSet ∩
        {point | 0 < point BellmanVar.disc})) :
    ∃ germ : G.AnalyticBellmanGerm, germ.endpoint = assignment := by
  let patterns := selectedPatterns G.bellmanConstraintPoly G.polynomialBellmanSolutionSet
  have hrepresentation :
      G.polynomialBellmanSolutionSet =
        ⋃ signs ∈ patterns, signCell G.bellmanConstraintPoly signs :=
    signInvariant_eq_iUnion_signCell G.signInvariant_polynomialBellmanSolutionSet
  have hpositiveRepresentation :
      G.polynomialBellmanSolutionSet ∩ {point | 0 < point BellmanVar.disc} =
        ⋃ signs ∈ patterns,
          signCell G.bellmanConstraintPoly signs ∩
            {point | 0 < point BellmanVar.disc} := by
    rw [hrepresentation]
    simp only [iUnion_inter]
  rw [hpositiveRepresentation,
    patterns.closure_biUnion (fun signs =>
      signCell G.bellmanConstraintPoly signs ∩
        {point | 0 < point BellmanVar.disc})] at hclosure
  obtain ⟨signs, hclosure⟩ := Set.mem_iUnion.mp hclosure
  obtain ⟨hselected, hcell⟩ := Set.mem_iUnion.mp hclosure
  have hsubset : signCell G.bellmanConstraintPoly signs ⊆
      G.polynomialBellmanSolutionSet :=
    signCell_subset_of_mem_selectedPatterns
      G.signInvariant_polynomialBellmanSolutionSet hselected
  have harc :=
    Math.CurveSelection.PolynomialSignCellArc.hasPositiveCoordinateAnalyticArcAt_signCell
      G.bellmanConstraintPoly signs BellmanVar.disc assignment hdiscount hcell
  apply G.exists_analyticBellmanGerm_of_positiveCoordinateArc
  simpa only [bellmanDiscountCoordinate] using harc.mono hsubset

end GameTheory.StochasticGame
