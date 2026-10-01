import MathUE.Analysis.GeometricCesaroError
import UniformEquilibrium.Quitting.Paths.JointSurvivalSelection
import UniformEquilibrium.Quitting.Paths.LiveRootSurvival
import UniformEquilibrium.Quitting.Punishment.NonnegativeSoloUniformization

/-! # Prescribed horizon delivery from actual joint absorption

Joint absorption controls prescribed delivery, not deleted-opponent contraction.
With nonnegative solo rewards, every complete reply has the separate canonical
opponent live-tail error, including positive opponent Never mass.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual finite-opponent-clock error, subtracting its genuine Never mass. -/
def quittingOpponentLiveTailCesaro
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (horizon : ℕ) : ℝ :=
  (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
    (quittingLiveMass reward (quittingOpponentOnlyProfile reward profile who) time -
      quittingLiveMassLimit reward (quittingOpponentOnlyProfile reward profile who))

/-- This error tends to zero without requiring opponents to absorb almost surely. -/
theorem tendsto_quittingOpponentLiveTailCesaro_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    Filter.Tendsto (quittingOpponentLiveTailCesaro reward profile who)
      Filter.atTop (nhds 0) :=
  tendsto_opponentLiveTailCesaro_zero reward profile who

omit [DecidableEq ι] in
/-- The actual finite average of any literal root-sequence suffix has the
geometric joint-clock delivery bound. No singleton sign is needed for delivery. -/
theorem abs_finiteAveragePayoff_sub_terminal_rootSequence_of_absorption_lower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) (who : ι)
    {bound charge : ℝ} (hcharge : 0 < charge)
    (hlower : ∀ time, charge ≤ quittingRootAbsorptionMass (roots time))
    (hreward : ∀ terminal, |reward terminal who| ≤ bound)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon
        (quittingRootSequenceProfile reward roots start) who -
      quittingTerminalPayoff reward (quittingRootSequenceProfile reward roots start) who| ≤
      bound / (charge * (horizon : ℝ)) := by
  classical
  let profile := quittingRootSequenceProfile reward roots start
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have hcharge1 : charge ≤ 1 := by
    have h := hlower start
    unfold quittingRootAbsorptionMass at h
    linarith [quittingStationaryContinueMass_nonneg (roots start)]
  have hroot : quittingProfileLiveRoot reward profile = fun time => roots (start + time) := by
    funext time player
    rfl
  have hlive (time : ℕ) : quittingLiveMass reward profile time ≤ (1 - charge) ^ time := by
    rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot, hroot]
    exact quittingJointSurvivalWeight_le_pow_of_absorption_lower
      (fun time => roots (start + time)) (fun time => hlower (start + time)) 0 time
  have herror (time : ℕ) :
      |(quittingGame reward).expectedStagePayoff profile none time who -
        quittingTerminalPayoff reward profile who| ≤ bound * (1 - charge) ^ time := by
    have htail := abs_quittingTerminalPayoff_sub_expectedStagePayoff_le_liveTail
      reward profile time who bound hreward
    have hmass : quittingLiveMass reward profile time - quittingLiveMassLimit reward profile ≤
        (1 - charge) ^ time :=
      (sub_le_self _ (quittingLiveMassLimit_nonneg reward profile)).trans (hlive time)
    have htail' :
        |(quittingGame reward).expectedStagePayoff profile none time who -
          quittingTerminalPayoff reward profile who| ≤
        bound * (quittingLiveMass reward profile time - quittingLiveMassLimit reward profile) := by
      simpa only [abs_sub_comm] using htail
    exact htail'.trans (mul_le_mul_of_nonneg_left hmass hbound)
  let : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  let : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  change |(quittingGame reward).finiteAveragePayoff none horizon profile who -
    quittingTerminalPayoff reward profile who| ≤ bound / (charge * (horizon : ℝ))
  rw [(quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff profile
    (show (quittingGame reward).State from none) who horizon]
  simpa only [sub_sub_cancel] using Math.abs_cesaro_sub_le_of_geometric_error
    (fun time => (quittingGame reward).expectedStagePayoff profile none time who)
    (quittingTerminalPayoff reward profile who) (sub_nonneg.mpr hcharge1)
    (by linarith) herror horizon hhorizon

/-- Every complete reply to the SAME exact terminal-Nash suffix is controlled
by its actual opponent live tail plus the prescribed joint-clock delivery error.
Opponent Never mass is subtracted, not required to vanish. -/
theorem finiteAveragePayoff_update_sub_rootSequence_le_of_terminalNash_absorption_lower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    {bound charge : ℝ} (hcharge : 0 < charge)
    (hlower : ∀ time, charge ≤ quittingRootAbsorptionMass (roots time))
    (hreward : ∀ terminal, |reward terminal who| ≤ bound)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingRootSequenceProfile reward roots start))
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    let profile := quittingRootSequenceProfile reward roots start
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update profile who deviation) who -
      (quittingGame reward).finiteAveragePayoff none horizon profile who ≤
      bound * quittingOpponentLiveTailCesaro reward profile who horizon +
      bound / (charge * (horizon : ℝ)) := by
  dsimp only
  unfold quittingOpponentLiveTailCesaro
  have hbound : 0 ≤ bound := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have hdelivery := abs_finiteAveragePayoff_sub_terminal_rootSequence_of_absorption_lower
    reward roots start who hcharge hlower hreward horizon hhorizon
  have hreply := finiteAveragePayoff_update_le_terminal_add_opponentLiveTailCesaro_of_solo_nonneg
    reward (quittingRootSequenceProfile reward roots start) who deviation horizon hhorizon
    bound hbound hreward hsolo
  have hterminal := hnash who deviation
  simp only [add_zero] at hterminal
  linarith [(abs_le.mp hdelivery).1]

end GameTheory
