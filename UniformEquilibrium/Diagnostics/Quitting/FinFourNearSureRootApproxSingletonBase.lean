import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.SureRootSingletonHandoff
import UniformEquilibrium.Diagnostics.Quitting.FirstExactRootStationaryDichotomy
import UniformEquilibrium.Quitting.Root.ForcedQuitEndpointStability

/-! # Approximate singleton-base roots from a nearly sure owner -/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At every finite selected source row, replacing the limiting sure owner by
a sure Quit produces a genuine approximate singleton-base root.  The tail
bound is derived from the actual stationary source rather than supplied as
additional scalar data. -/
theorem FirstStationaryRootZeroBranch.finite_forceSureOwner_weighted_regrets
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : StationaryQuitNowCapPinSource reward}
    {root : ℕ → ι → PMF Bool} {minimum gap : ℝ}
    (branch : FirstStationaryRootZeroBranch source root minimum gap)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (source.pair index).1 0 (root index))
    (index : ℕ) (who : ι) (hne : who ≠ branch.owner) :
    let selectedRoot := root (branch.select index)
    let forced := Function.update selectedRoot branch.owner (PMF.pure true)
    (selectedRoot who false).toReal *
          quittingRootEndpointDifference reward 0 forced who ≤
        4 * source.bound * (selectedRoot branch.owner false).toReal ∧
      -(selectedRoot who true).toReal *
          quittingRootEndpointDifference reward 0 forced who ≤
        4 * source.bound * (selectedRoot branch.owner false).toReal := by
  apply forceSureOwner_weighted_endpoint_regrets
    reward (source.pair (branch.select index)).1
      (root (branch.select index)) branch.owner who hne source.reward_bound
  · intro player
    exact abs_quittingTerminalPayoff_le reward
      (source.profile (branch.select index)) player source.reward_bound
  · exact hnash (branch.select index)

/-- The explicit finite singleton-base error tends to zero along the actual
selected root sequence. -/
theorem FirstStationaryRootZeroBranch.singletonBase_error_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : StationaryQuitNowCapPinSource reward}
    {root : ℕ → ι → PMF Bool} {minimum gap : ℝ}
    (branch : FirstStationaryRootZeroBranch source root minimum gap) :
    Tendsto (fun index ↦
      4 * source.bound * (root (branch.select index) branch.owner false).toReal)
      atTop (nhds 0) := by
  have hquit := (uniqueSureLimit_ownerQuit_and_opponentReach
    (fun index ↦ root (branch.select index)) branch.rootLimit branch.owner
      branch.root_tendsto branch.owner_sure branch.owner_unique).1
  have hcontinue : Tendsto (fun index ↦
      (root (branch.select index) branch.owner false).toReal) atTop (nhds 0) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    convert hone.sub hquit using 1
    · funext index
      linarith [quittingRoot_continueProbability_add_quitProbability
        (root (branch.select index)) branch.owner]
    · norm_num
  simpa using (show Tendsto (fun index ↦
      (4 * source.bound) * (root (branch.select index) branch.owner false).toReal)
      atTop (nhds ((4 * source.bound) * 0)) from tendsto_const_nhds.mul hcontinue)

/-- Exact induced-Nash membership is asserted at the limiting root, where the
owner is surely quitting, and not at any finite nearly-sure approximation. -/
theorem FirstStationaryRootZeroBranch.limit_freePoint_mem_singletonBaseNashSet
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : StationaryQuitNowCapPinSource reward}
    {root : ℕ → ι → PMF Bool} {minimum gap : ℝ}
    (branch : FirstStationaryRootZeroBranch source root minimum gap) :
    quittingRootFreeMixedPoint (Finset.univ.erase branch.owner) branch.rootLimit ∈
      quittingPersistentBaseNashSet reward {branch.owner}
        (Finset.univ.erase branch.owner) :=
  quittingRootFreeMixedPoint_mem_singletonBaseNashSet_of_sure_exactNash
    reward branch.sourceLimit.1 branch.rootLimit branch.owner
      branch.owner_sure branch.exactNash

end GameTheory
