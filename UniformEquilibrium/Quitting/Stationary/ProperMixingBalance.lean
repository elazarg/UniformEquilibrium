import UniformEquilibrium.Quitting.Stationary.EndpointCompiler
import UniformEquilibrium.Quitting.Stationary.HazardPayoffCap
import Mathlib.Tactic.Linarith

/-! # Actual stationary balance at a proper mixing coordinate -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Proper mixing in actual terminal Nash balances Quit against continued
opponent absorption. No externally supplied continuation value is used. -/
theorem stationary_proper_mixing_balance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (player : ι)
    (hproper : hazardOfRoot root player ∈ Set.Ioo (0 : ℝ) 1)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root)) :
    sigmaValue (weightOfReward reward) (hazardOfRoot root) player *
      (1 - continueMassExcl (hazardOfRoot root) player) =
        excludedValue (weightOfReward reward) (hazardOfRoot root) player := by
  let value : Payoff ι := quittingTerminalPayoff reward
    (quittingStationaryProfile reward root)
  have hendpoint :=
    (isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary reward root).mp hnash
  have htrue : 0 < (root player true).toReal := hproper.1
  have hfalse : 0 < (root player false).toReal := by
    rw [Math.PMFProduct.pmfBool_false_toReal]
    change 0 < 1 - hazardOfRoot root player
    exact sub_pos.mpr hproper.2
  have hgap := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    reward value root player hendpoint.1 hfalse htrue
  have hequal := sub_eq_zero.mp hgap
  have hfixed : value player = quittingRootSuccessorPayoff reward value root player :=
    quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root player
  rw [quittingRootSuccessorPayoff_eq_endpointMix, ← hequal] at hfixed
  have hsum := quittingRoot_continueProbability_add_quitProbability root player
  have hv : value player = quittingRootQuitPayoff reward value root player := by
    rw [← add_mul, add_comm (root player true).toReal (root player false).toReal,
      hsum, one_mul] at hfixed
    exact hfixed
  rw [quittingRootQuitPayoff_eq_sigmaValue, quittingRootContinuePayoff_eq_gammaValue] at hequal
  rw [quittingRootQuitPayoff_eq_sigmaValue] at hv
  unfold gammaValue at hequal
  rw [hv] at hequal
  nlinarith [hequal]

end GameTheory
