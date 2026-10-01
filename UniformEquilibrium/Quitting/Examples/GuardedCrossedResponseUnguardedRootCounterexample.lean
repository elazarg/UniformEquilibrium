import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponse
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# The literal unguarded crossed fixed point need not be an original equilibrium

The only nonzero reward coordinate is player zero's payoff two from the
coalition `{0,1}`. Only player one initially quits. The crossed unit map
fixes this actual root's hazards, but player zero's actual Quit-now
behavioral deviation gains two. This refutes unguarded fixed-point
transfer, not uniform-equilibrium existence for this reward table.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseUnguardedRootCounterexample

open QuittingSureSetOwnerRepair QuittingFinFourEndpointRows

/-- Packet §9's literal table, with precisely one nonzero reward coordinate. -/
def reward
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) : ℝ :=
  if terminal.1 = {0, 1} ∧ who = 0 then 2 else 0

/-- The actual stationary product root where only player one quits surely. -/
def root : Fin 4 → PMF Bool := quittingPureSetRoot {1}

def profile : (quittingGame reward).BehaviorProfile := quittingStationaryProfile reward root

theorem root_hazard : hazardOfRoot root = ![0, 1, 0, 0] := by
  funext who
  fin_cases who <;> norm_num [hazardOfRoot, root, quittingPureSetRoot, quittingSetAction]

/-- Evaluation is of the actual reward-generated displacement, not a surrogate field. -/
theorem root_displacement :
    (fun who => quittingDiscountedDisplacement reward 0 (hazardOfRoot root) who) =
      ![2, 0, 0, 0] := by
  rw [root_hazard]
  funext who
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  unfold quittingDiscountedDisplacement
  rw [sigmaValue_eq_pureQuitEndpointRowSum, excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals simp only [pureQuitEndpointRowSum, excludedEndpointRowSum, Fin.sum_univ_succ]
  all_goals simp +decide [opponentCoalitionMass, Math.Finset.finFourCoalitionOfRow,
    weightOfReward, reward, continueMassExcl, huniv]

/-- The original player's displacement is swapped only inside the auxiliary map. -/
theorem root_crossed_unit_fixed :
    quittingCrossedClippedMap reward 0 1 1 (hazardOfRoot root) = hazardOfRoot root := by
  funext who
  simp only [quittingCrossedClippedMap, quittingCrossedResponse]
  rw [congrFun root_displacement ((Equiv.swap (0 : Fin 4) 1) who), root_hazard]
  fin_cases who
  · norm_num [quittingCrossedCeiling]
  · norm_num [quittingCrossedCeiling]
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    norm_num [quittingCrossedCeiling]
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    norm_num [quittingCrossedCeiling]

/-- The actual prescribed behavioral payoff is the zero vector. -/
theorem profile_terminalPayoff : quittingTerminalPayoff reward profile = 0 := by
  funext who
  unfold profile root
  rw [quittingTerminalPayoff_pureSetRoot]
  fin_cases who <;> norm_num +decide [quittingSetReward, reward]

/-- Original player zero joins at date zero; the actual terminal payoff is two. -/
theorem joining_zero_terminalPayoff :
    quittingTerminalPayoff reward
      (Function.update profile 0 (quittingPureTimeBehaviorStrategy reward 0 (some 0))) 0 = 2 := by
  unfold profile root
  rw [quittingTerminalPayoff_update_pureSetRoot_quitNow]
  norm_num +decide [quittingSetReward, reward]

/-- The pure-time response is a genuine unilateral behavioral deviation with gain two. -/
theorem joining_zero_gain_eq_two :
    quittingTerminalPayoff reward
        (Function.update profile 0 (quittingPureTimeBehaviorStrategy reward 0 (some 0))) 0 -
      quittingTerminalPayoff reward profile 0 = 2 := by
  rw [joining_zero_terminalPayoff, profile_terminalPayoff]
  norm_num

/-- Thus this actual crossed fixed root is not an original terminal behavioral Nash profile. -/
theorem profile_not_exact_terminalNash :
    ¬(quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile := by
  intro hnash
  have h := hnash 0 (quittingPureTimeBehaviorStrategy reward 0 (some 0))
  rw [joining_zero_terminalPayoff, profile_terminalPayoff] at h
  norm_num at h

end GameTheory.GuardedCrossedResponseUnguardedRootCounterexample
