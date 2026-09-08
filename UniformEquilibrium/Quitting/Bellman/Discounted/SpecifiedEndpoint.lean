import UniformEquilibrium.Quitting.Bellman.Discounted.FixedPointLift
import UniformEquilibrium.VanishingDiscount.Bellman.SpecifiedEndpointGerm

/-!

# The supplied full endpoint of discounted quitting fixed points

Convergent discounts, root hazards, and live values determine convergence of
the entire Bellman assignment, including all absorbed-state coordinates.
Positive-discount fixed points therefore give a closure witness at that exact
assignment, and specified-endpoint curve selection retains it literally.
No compactness subsequence, root, payoff target, or reward table is selected.
-/

noncomputable section

namespace GameTheory

open Filter Set Topology StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Convergence of all source coordinates gives convergence of the complete assignment. -/
theorem tendsto_quittingDiscountedBellmanAssignment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {κ : Type*} {sourceFilter : Filter κ}
    (discountComplement : κ → ℝ) (root : κ → ι → PMF Bool) (value : κ → Payoff ι)
    (discountLimit : ℝ) (rootLimit : ι → PMF Bool) (valueLimit : Payoff ι)
    (hdiscount : Tendsto discountComplement sourceFilter (𝓝 discountLimit))
    (hroot : Tendsto (fun index => hazardOfRoot (root index)) sourceFilter
      (𝓝 (hazardOfRoot rootLimit)))
    (hvalue : Tendsto value sourceFilter (𝓝 valueLimit)) :
    Tendsto (fun index => quittingDiscountedBellmanAssignment reward
      (discountComplement index) (root index) (value index)) sourceFilter
        (𝓝 (quittingDiscountedBellmanAssignment reward discountLimit rootLimit valueLimit)) := by
  apply tendsto_pi_nhds.mpr
  intro coordinate
  cases coordinate with
  | disc =>
      simpa only [quittingDiscountedBellmanAssignment_discount] using hdiscount
  | val state who =>
      cases state with
      | none => exact (tendsto_pi_nhds.mp hvalue) who
      | some terminal => exact tendsto_const_nhds
  | mix state who action =>
      cases state with
      | none =>
          cases action with
          | false =>
              change Tendsto (fun index => (root index who false).toReal) sourceFilter
                (𝓝 (rootLimit who false).toReal)
              simp_rw [Math.PMFProduct.pmfBool_false_toReal]
              exact tendsto_const_nhds.sub ((tendsto_pi_nhds.mp hroot) who)
          | true => exact (tendsto_pi_nhds.mp hroot) who
      | some terminal => exact tendsto_const_nhds

/-- The complete assignment at the supplied limit is approached by actual
positive-discount polynomial Bellman solutions, not only by projected root rows. -/
theorem quittingDiscountedBellmanAssignment_mem_closure_positiveDiscount
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {κ : Type*} {sourceFilter : Filter κ} [sourceFilter.NeBot]
    (discountComplement : κ → ℝ) (root : κ → ι → PMF Bool) (value : κ → Payoff ι)
    (rootLimit : ι → PMF Bool) (valueLimit : Payoff ι)
    (hdiscount : Tendsto discountComplement sourceFilter (𝓝 0))
    (hroot : Tendsto (fun index => hazardOfRoot (root index)) sourceFilter
      (𝓝 (hazardOfRoot rootLimit)))
    (hvalue : Tendsto value sourceFilter (𝓝 valueLimit))
    (hsource : ∀ᶠ index in sourceFilter,
      0 < discountComplement index ∧ discountComplement index ≤ 1 ∧
        value index = quittingDiscountedLiveValue reward (discountComplement index) (root index) ∧
          quittingDiscountedClippedMap reward (discountComplement index)
            (hazardOfRoot (root index)) = hazardOfRoot (root index)) :
    quittingDiscountedBellmanAssignment reward 0 rootLimit valueLimit ∈ closure
      ((quittingGame reward).polynomialBellmanSolutionSet ∩
        {assignment | 0 < assignment .disc}) := by
  apply mem_closure_of_tendsto (tendsto_quittingDiscountedBellmanAssignment
    reward discountComplement root value 0 rootLimit valueLimit hdiscount hroot hvalue)
  filter_upwards [hsource] with index hindex
  refine ⟨isPolynomialBellmanSolution_quittingDiscountedBellmanAssignment
    reward hindex.1 hindex.2.1 (root index) (value index) hindex.2.2.1 hindex.2.2.2, ?_⟩
  simpa only [mem_setOf_eq, quittingDiscountedBellmanAssignment_discount] using hindex.1

/-- Every supplied full limit of actual discounted fixed points is retained as
the endpoint of an analytic Bellman germ for the same actual reward table. -/
theorem exists_analyticBellmanGerm_at_quittingDiscountedFixedPoint_limit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {κ : Type*} {sourceFilter : Filter κ} [sourceFilter.NeBot]
    (discountComplement : κ → ℝ) (root : κ → ι → PMF Bool) (value : κ → Payoff ι)
    (rootLimit : ι → PMF Bool) (valueLimit : Payoff ι)
    (hdiscount : Tendsto discountComplement sourceFilter (𝓝 0))
    (hroot : Tendsto (fun index => hazardOfRoot (root index)) sourceFilter
      (𝓝 (hazardOfRoot rootLimit)))
    (hvalue : Tendsto value sourceFilter (𝓝 valueLimit))
    (hsource : ∀ᶠ index in sourceFilter,
      0 < discountComplement index ∧ discountComplement index ≤ 1 ∧
        value index = quittingDiscountedLiveValue reward (discountComplement index) (root index) ∧
          quittingDiscountedClippedMap reward (discountComplement index)
            (hazardOfRoot (root index)) = hazardOfRoot (root index)) :
    ∃ germ : (quittingGame reward).AnalyticBellmanGerm,
      germ.endpoint = quittingDiscountedBellmanAssignment reward 0 rootLimit valueLimit := by
  apply (quittingGame reward).exists_analyticBellmanGerm_of_mem_closure_positiveDiscount
  · exact quittingDiscountedBellmanAssignment_discount reward 0 rootLimit valueLimit
  · exact quittingDiscountedBellmanAssignment_mem_closure_positiveDiscount reward
      discountComplement root value rootLimit valueLimit hdiscount hroot hvalue hsource

end GameTheory
