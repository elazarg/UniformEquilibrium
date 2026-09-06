import UniformEquilibrium.Quitting.Bellman.Finite.EndpointNashClosed
import UniformEquilibrium.Quitting.Paths.ActualExactPrefixBlock

/-! # All-Continue limits of summable prefix roots -/

noncomputable section
namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Summable total marginal Quit hazard forces the literal product roots to
converge to all Continue in the canonical simplex topology. -/
theorem tendsto_quittingSimplexOfRoot_allContinue_of_summable_marginalHazard
    (roots : ℕ → ι → PMF Bool)
    (hhazard : Summable (fun time =>
      ∑ player, (roots time player true).toReal)) :
    Tendsto (fun time => quittingSimplexOfRoot (roots time)) atTop
      (nhds (quittingSimplexOfRoot
        (quittingAllContinueRoot : ι → PMF Bool))) := by
  have htotal := hhazard.tendsto_atTop_zero
  apply tendsto_pi_nhds.2
  intro player
  apply tendsto_subtype_rng.2
  apply tendsto_pi_nhds.2
  intro action
  cases action with
  | false =>
      have hquit : Tendsto (fun time => (roots time player true).toReal)
          atTop (nhds 0) := by
        apply squeeze_zero'
        · exact Eventually.of_forall fun _ => ENNReal.toReal_nonneg
        · exact Eventually.of_forall fun time =>
          Finset.single_le_sum (s := Finset.univ)
            (f := fun other => (roots time other true).toReal)
            (fun other _ => ENNReal.toReal_nonneg) (Finset.mem_univ player)
        · exact htotal
      have hsum := fun time =>
        quittingRoot_continueProbability_add_quitProbability (roots time) player
      have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      have hfalse := hone.sub hquit
      have hfalse' : Tendsto (fun time => (roots time player false).toReal)
          atTop (nhds 1) := by
        convert hfalse using 1
        · funext time
          linarith [hsum time]
        · norm_num
      convert hfalse' using 1 <;> simp [quittingSimplexOfRoot,
        Math.ProbabilityMassFunction.stdSimplexEquiv,
        Math.ProbabilityMassFunction.toVector, quittingAllContinueRoot]
  | true =>
      have hquit : Tendsto (fun time => (roots time player true).toReal)
          atTop (nhds 0) := by
        apply squeeze_zero'
        · exact Eventually.of_forall fun _ => ENNReal.toReal_nonneg
        · exact Eventually.of_forall fun time =>
          Finset.single_le_sum (s := Finset.univ)
            (f := fun other => (roots time other true).toReal)
            (fun other _ => ENNReal.toReal_nonneg) (Finset.mem_univ player)
        · exact htotal
      convert hquit using 1 <;> simp [quittingSimplexOfRoot,
        Math.ProbabilityMassFunction.stdSimplexEquiv,
        Math.ProbabilityMassFunction.toVector, quittingAllContinueRoot]

omit [DecidableEq ι] in
/-- Every fixed front position of reverse prefixes converges to all Continue.
The newest root has offset zero. -/
theorem tendsto_reversePrefix_frontRoot_allContinue
    (roots : ℕ → ι → PMF Bool)
    (hhazard : Summable (fun time =>
      ∑ player, (roots time player true).toReal))
    (offset : ℕ) :
    Tendsto (fun depth =>
      quittingSimplexOfRoot (roots (depth - (offset + 1)))) atTop
      (nhds (quittingSimplexOfRoot
        (quittingAllContinueRoot : ι → PMF Bool))) := by
  exact
    (tendsto_quittingSimplexOfRoot_allContinue_of_summable_marginalHazard
      roots hhazard).comp (Filter.tendsto_sub_atTop_nat (offset + 1))

/-- If exact root Nash conditions converge to all Continue while their terminal
payoffs converge, then all Continue is exact Nash against the limiting payoff
and its Bellman successor fixes that payoff. -/
theorem allContinue_exactNash_and_fixedPoint_of_tendsto_terminalPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (limit : Payoff ι)
    (hpayoff : ∀ player, Tendsto
      (fun time => quittingTerminalPayoff reward (profiles time) player)
      atTop (nhds (limit player)))
    (hhazard : Summable (fun time =>
      ∑ player, (roots time player true).toReal))
    (hexact : ∀ time, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles time) player)
      0 (roots time)) :
    IsεQuittingRootNash reward limit 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingRootSuccessorPayoff reward limit
        (quittingAllContinueRoot : ι → PMF Bool) = limit := by
  have htail : Tendsto
      (fun time player => quittingTerminalPayoff reward (profiles time) player)
      atTop (nhds limit) := tendsto_pi_nhds.mpr hpayoff
  have hroot :=
    tendsto_quittingSimplexOfRoot_allContinue_of_summable_marginalHazard
      roots hhazard
  have hendpoint : IsεQuittingRootEndpointNash reward limit 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    simpa only [quittingRootOfSimplex_simplexOfRoot] using
      isεQuittingRootEndpointNash_of_tendsto reward
        (fun _ : ℕ => 0)
        (fun time player => quittingTerminalPayoff reward (profiles time) player)
        (fun time => quittingSimplexOfRoot (roots time))
        tendsto_const_nhds htail hroot
        (Eventually.of_forall fun time => by
          simpa only [quittingRootOfSimplex_simplexOfRoot] using
            (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
              reward _ 0 (roots time)).mpr (hexact time))
  constructor
  · exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward limit 0 quittingAllContinueRoot).mp hendpoint
  · exact quittingRootSuccessorPayoff_allContinueRoot_eq reward limit

end GameTheory
