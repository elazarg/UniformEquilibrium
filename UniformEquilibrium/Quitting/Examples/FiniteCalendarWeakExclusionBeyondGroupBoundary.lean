import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Weak exclusion without group exclusion or strict deficit

Player zero receives one at every terminal coalition.  Every other player
receives one only when zero quits alone, and zero otherwise.  Coordinate zero
therefore supplies actual weak exclusion.  The actual pure-zero exit has
surplus `(0,1,1,1)`, which refutes every group cap below one and every positive
strict singleton deficit.
-/

noncomputable section

namespace GameTheory.FiniteCalendarWeakExclusionBeyondGroupBoundary

open QuittingSureSetOwnerRepair

/-- The literal four-player reward table from the boundary test. -/
def reward
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) : ℝ :=
  if who = 0 then 1 else if terminal.1 = {0} then 1 else 0

@[simp] theorem reward_singleton_zero :
    reward (quittingSingletonTerminal 0) 0 = 1 := by
  simp [reward]

@[simp] theorem reward_singleton_ne_zero
    (who : Fin 4) (hwho : who ≠ 0) :
    reward (quittingSingletonTerminal who) who = 0 := by
  simp [reward, hwho, quittingSingletonTerminal]

/-- Every actual terminal payoff of player zero is at most one. -/
theorem terminalPayoff_zero_le_one
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile 0 ≤ 1 := by
  have hreward : ∀ terminal player, |reward terminal player| ≤ 1 := by
    intro terminal player
    simp only [reward]
    split_ifs <;> norm_num
  exact (le_abs_self _).trans
    (abs_quittingTerminalPayoff_le reward profile 0 hreward)

/-- Actual weak exclusion holds on the singleton owner set `{0}`. -/
theorem hasQuittingActualWeakSubsetExclusion_zero :
    HasQuittingActualWeakSubsetExclusion reward {0} := by
  constructor
  · intro who hwho
    simp only [Finset.mem_singleton] at hwho
    subst who
    rw [reward_singleton_zero]
    norm_num
  · intro profile
    exact ⟨0, Finset.mem_singleton_self 0, terminalPayoff_zero_le_one profile⟩

/-- The actual behavioral profile in which only player zero quits immediately. -/
def pureZeroProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot {0})

/-- The pure-zero exit pays every player one, while the own-singleton vector
is `(1,0,0,0)`. -/
theorem pureZeroProfile_terminalPayoff :
    quittingTerminalPayoff reward pureZeroProfile = ![1, 1, 1, 1] := by
  funext who
  unfold pureZeroProfile
  rw [quittingTerminalPayoff_pureSetRoot]
  fin_cases who <;>
    norm_num +decide [quittingSetReward, reward, quittingSingletonTerminal]

/-- The pure-zero profile is itself an exact terminal Nash equilibrium against
unrestricted behavioral deviations. -/
theorem pureZeroProfile_isExactTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 pureZeroProfile := by
  unfold pureZeroProfile
  apply (isεAsymptoticNash_pureSetRoot_iff reward {0} 0).mpr
  intro who
  fin_cases who <;>
    norm_num +decide [quittingSetReward, reward, quittingSingletonTerminal]

/-- The pure-zero payoff refutes every positive strict singleton deficit. -/
theorem not_hasQuittingActualStrictSingletonDeficit
    (gap : ℝ) (hgap : 0 < gap) :
    ¬ HasQuittingActualStrictSingletonDeficit reward gap := by
  intro hdeficit
  obtain ⟨who, hwho⟩ := hdeficit pureZeroProfile
  have hpayoff := congrFun pureZeroProfile_terminalPayoff who
  fin_cases who <;>
    norm_num [reward, quittingSingletonTerminal] at hpayoff hwho ⊢ <;> linarith

theorem not_exists_positive_actualStrictSingletonDeficit :
    ¬ ∃ gap : ℝ, 0 < gap ∧
      HasQuittingActualStrictSingletonDeficit reward gap := by
  rintro ⟨gap, hgap, hdeficit⟩
  exact not_hasQuittingActualStrictSingletonDeficit gap hgap hdeficit

/-- Every group-exclusion cap strictly below one fails at the pure-zero
profile: the weight outside coordinate zero is at least `1 - beta > 0`. -/
theorem not_hasQuittingActualNonconcentratedGroupExclusion
    (beta : ℝ) (hbeta : beta < 1) :
    ¬ HasQuittingActualNonconcentratedGroupExclusion reward beta := by
  intro hgroup
  obtain ⟨weight, _, hsum, hcapped, hweighted⟩ :=
    hgroup pureZeroProfile
  have hpayoff (who : Fin 4) :
      quittingTerminalPayoff reward pureZeroProfile who = 1 := by
    have h := congrFun pureZeroProfile_terminalPayoff who
    fin_cases who <;> simpa using h
  simp_rw [hpayoff] at hweighted
  simp only [Fin.sum_univ_four] at hsum hweighted
  norm_num +decide [reward, quittingSingletonTerminal] at hweighted
  have hzeroCap := hcapped 0
  linarith

end GameTheory.FiniteCalendarWeakExclusionBeyondGroupBoundary
