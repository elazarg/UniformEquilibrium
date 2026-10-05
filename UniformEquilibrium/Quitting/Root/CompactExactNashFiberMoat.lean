import MathUE.Topology.CompactRobustMoat
import UniformEquilibrium.Quitting.Root.NashDefectContinuity

/-! # Compact exact-root fibers and vanishing absorption

A continuous root statistic which vanishes on one exact Nash fiber has a
positive defect moat above any positive statistic threshold, uniformly at
nearby sources. No root selector continuity, strict singleton gap, or boundary
minimum assumption is part of this interface.
-/

noncomputable section

namespace GameTheory

open Set Filter _root_.Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The exact fiber, rather than an all-Continue characterization, supplies
the vanishing statistic hypothesis. The high-statistic set may be empty. -/
theorem exists_eventually_totalNashDefect_moat_of_measure_zero_on_exact_fiber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (measure : QuittingRootSimplex ι → ℝ)
    (hmeasure : Continuous measure)
    (hzero : ∀ root : QuittingRootSimplex ι,
      IsεQuittingRootNash reward tail 0 (quittingRootOfSimplex root) → measure root = 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ nearby in 𝓝 tail, ∀ root : QuittingRootSimplex ι,
        eta ≤ measure root →
          moat ≤ quittingRootTotalNashDefect reward nearby (quittingRootOfSimplex root) := by
  let high : Set (QuittingRootSimplex ι) := {root | eta ≤ measure root}
  have hhighClosed : IsClosed high := isClosed_Ici.preimage hmeasure
  have hpositive : ∀ root ∈ high,
      0 < quittingRootTotalNashDefect reward tail (quittingRootOfSimplex root) := by
    intro root hrootHigh
    have hnonneg := quittingRootTotalNashDefect_nonneg reward tail (quittingRootOfSimplex root)
    apply lt_of_le_of_ne hnonneg
    intro hdefectZero
    have hnash := (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward tail (quittingRootOfSimplex root)).2 hdefectZero.symm
    have hmeasureZero := hzero root hnash
    change eta ≤ measure root at hrootHigh
    rw [hmeasureZero] at hrootHigh
    linarith
  simpa only [high, Set.mem_ofPred_eq] using
    (Math.Topology.exists_eventually_uniform_pos_on_closed_of_compactSpace
      (fun nearby root => quittingRootTotalNashDefect reward nearby (quittingRootOfSimplex root))
      (continuous_quittingRootTotalNashDefect_simplex reward)
      high hhighClosed tail hpositive)

/-- Every nearby exact root has small absorption if every exact root at the
limiting source has zero absorption. This is uniform over all root choices. -/
theorem eventually_exactRoot_absorption_lt_of_exact_fiber_absorption_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hzero : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail 0 root → quittingRootAbsorptionMass root = 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ nearby in 𝓝 tail, ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward nearby 0 root → quittingRootAbsorptionMass root < eta := by
  obtain ⟨moat, hmoat, hnear⟩ :=
    exists_eventually_totalNashDefect_moat_of_measure_zero_on_exact_fiber reward tail
      (fun root => quittingRootAbsorptionMass (quittingRootOfSimplex root))
      continuous_quittingRootAbsorptionMass_simplex
      (fun root hnash => hzero (quittingRootOfSimplex root) hnash) eta heta
  filter_upwards [hnear] with nearby hnear root hnash
  by_contra hnot
  have hlarge : eta ≤ quittingRootAbsorptionMass (quittingRootOfSimplex
      (quittingSimplexOfRoot root)) := by
    simpa only [quittingRootOfSimplex_simplexOfRoot] using le_of_not_gt hnot
  have hlower := hnear (quittingSimplexOfRoot root) hlarge
  have hdefect := (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero reward nearby root).1 hnash
  simp only [quittingRootOfSimplex_simplexOfRoot, hdefect] at hlower
  exact (not_le_of_gt hmoat) hlower

/-- Arbitrary exact-root selections over convergent sources have absorption
tending to zero at a zero-absorption exact fiber. The selections need not converge. -/
theorem tendsto_exactRoot_absorption_zero_of_exact_fiber_absorption_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hzero : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail 0 root → quittingRootAbsorptionMass root = 0)
    {α : Type*} {filter : Filter α} (nearby : α → Payoff ι) (roots : α → ι → PMF Bool)
    (hnearby : Tendsto nearby filter (𝓝 tail))
    (hnash : ∀ᶠ index in filter, IsεQuittingRootNash reward (nearby index) 0 (roots index)) :
    Tendsto (fun index => quittingRootAbsorptionMass (roots index)) filter (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro lower hlower
    exact Eventually.of_forall fun index =>
      hlower.trans_le (quittingRootAbsorptionMass_nonneg (roots index))
  · intro upper hupper
    have hsmall := hnearby.eventually
      (eventually_exactRoot_absorption_lt_of_exact_fiber_absorption_zero
        reward tail hzero upper hupper)
    filter_upwards [hsmall, hnash] with index hsmall hnash
    exact hsmall (roots index) hnash

end GameTheory
