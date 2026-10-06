import MathUE.Topology.AmbientDegreeNegativeFixedPointObstruction
import UniformEquilibrium.Quitting.Root.FullClippedEndpointMap
import UniformEquilibrium.Quitting.Root.SingletonSublevelReturnClosed
import Mathlib.Topology.Neighborhoods

/-! # Conditional actual-root negative-index obstruction and dense restoration

These helpers consume actual derivative and dense-source hypotheses. Raw
reward criteria must supply those hypotheses internally before obtaining a
strategic conclusion. The selected relation is existential, not universal.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_exactRoot_singletonSublevel_of_badRoot_negative_derivatives
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hnegative : ∀ root, IsεQuittingRootNash reward tail 0 root →
      (∀ player, reward (quittingSingletonTerminal player) player <
        quittingRootSuccessorPayoff reward tail root player) →
      ∃ derivative : (ι → ℝ) →L[ℝ] (ι → ℝ),
        HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
          derivative (hazardOfRoot root) ∧
          (LinearMap.toMatrix' derivative.toLinearMap).det < 0) :
    ∃ root, IsεQuittingRootNash reward tail 0 root ∧
      ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
        reward (quittingSingletonTerminal player) player := by
  by_contra hreturn
  have hbad : ∀ root, IsεQuittingRootNash reward tail 0 root →
      ∀ player, reward (quittingSingletonTerminal player) player <
        quittingRootSuccessorPayoff reward tail root player := by
    intro root hnash player
    by_contra hnot
    exact hreturn ⟨root, hnash, player, le_of_not_gt hnot⟩
  apply Math.Topology.not_all_fixedPoints_have_negative_det_finite
    (quittingFullClippedEndpointMap reward tail)
    (continuous_quittingFullClippedEndpointMap reward tail)
    (quittingFullClippedEndpointMap_mem_unitCube reward tail)
  intro hazard hfixed
  have hcube : hazard ∈ Icc (fun _ => 0) (fun _ => 1) := by
    rw [← hfixed]
    exact quittingFullClippedEndpointMap_mem_unitCube reward tail hazard
  let root := rootOfHazard hazard hcube.1 hcube.2
  have hnash : IsεQuittingRootNash reward tail 0 root :=
    (quittingFullClippedEndpointMap_eq_self_iff_isZeroNash_rootOfHazard
      reward tail hazard hcube.1 hcube.2).mp hfixed
  obtain ⟨derivative, hdiff, hdet⟩ := hnegative root hnash (hbad root hnash)
  exact ⟨derivative, by simpa only [root, hazardOfRoot_rootOfHazard] using hdiff, hdet⟩

theorem exists_exactRoot_singletonSublevel_of_dense_sources_excluding_root
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (domain : Set (Payoff ι)) (hdense : Dense domain) (excludedRoot : ι → PMF Bool)
    (hgeneric : ∀ tail ∈ domain,
      (∃ player, tail player < reward (quittingSingletonTerminal player) player) →
      ¬IsεQuittingRootNash reward tail 0 excludedRoot →
      ∃ root, IsεQuittingRootNash reward tail 0 root ∧
        ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
          reward (quittingSingletonTerminal player) player)
    (tail : Payoff ι)
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hexcluded : ¬IsεQuittingRootNash reward tail 0 excludedRoot) :
    ∃ root, IsεQuittingRootNash reward tail 0 root ∧
      ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
        reward (quittingSingletonTerminal player) player := by
  let sources : Set (Payoff ι) := {source |
    (∃ player, source player < reward (quittingSingletonTerminal player) player) ∧
      ¬IsεQuittingRootNash reward source 0 excludedRoot}
  have hbelowOpen := isOpen_iUnion fun player : ι =>
    isOpen_lt (continuous_apply player)
      (continuous_const (y := reward (quittingSingletonTerminal player) player))
  have hbelowSet : {source : Payoff ι | ∃ player,
      source player < reward (quittingSingletonTerminal player) player} =
      ⋃ player : ι, {source : Payoff ι |
        source player < reward (quittingSingletonTerminal player) player} := by
    ext source
    simp
  rw [← hbelowSet] at hbelowOpen
  have hpureClosed : IsClosed {source : Payoff ι | IsεQuittingRootNash reward source 0
      excludedRoot} := by
    simpa only [quittingRootOfSimplex_simplexOfRoot,
      isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash] using
      isClosed_setOf_isZeroQuittingRootEndpointNash_tail reward
        (quittingSimplexOfRoot excludedRoot)
  have hsourcesOpen : IsOpen sources := hbelowOpen.inter hpureClosed.isOpen_compl
  have hsubset : sources ∩ domain ⊆ {source : Payoff ι |
      ∃ root, IsεQuittingRootNash reward source 0 root ∧ ∃ player,
        quittingRootSuccessorPayoff reward source root player ≤
          reward (quittingSingletonTerminal player) player} := by
    intro source hsource
    exact hgeneric source hsource.2 hsource.1.1 hsource.1.2
  have hclosed := isClosed_setOf_exists_exactRoot_singletonSublevel reward
  exact (hclosed.closure_subset_iff.mpr hsubset)
    (hdense.open_subset_closure_inter hsourcesOpen ⟨hbelow, hexcluded⟩)

end GameTheory
