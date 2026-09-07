import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Exact Nash boundary where all finite-calendar exclusion predicates fail

This four-player table pays each player `1` at that player's singleton,
`2` at the grand coalition, and `0` at every other coalition.  The pure
grand-coalition exit is an exact terminal Nash equilibrium.  Its payoff is
strictly above every own singleton, so it witnesses failure of every positive
strict deficit, every nonconcentrated group exclusion, and every weak subset
exclusion predicate.
-/

noncomputable section

namespace GameTheory.FiniteCalendarPredicateFailureExactNashBoundary

open QuittingSureSetOwnerRepair

/-- The literal four-player reward table: own singleton `1`, grand coalition
`2`, and every other coordinate `0`. -/
def reward
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) : ℝ :=
  if terminal.1 = Finset.univ then 2
  else if terminal.1 = {who} then 1
  else 0

/-- The actual behavioral profile in which all four players quit immediately. -/
def fullQuitProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot Finset.univ)

@[simp] theorem reward_singleton (who : Fin 4) :
    reward (quittingSingletonTerminal who) who = 1 := by
  fin_cases who <;> norm_num +decide [reward, quittingSingletonTerminal]

@[simp] theorem reward_full (who : Fin 4) :
    reward ⟨Finset.univ, Finset.univ_nonempty⟩ who = 2 := by
  simp [reward]

/-- The full-quitting behavioral profile has the literal payoff vector `(2,2,2,2)`. -/
theorem fullQuitProfile_terminalPayoff :
    quittingTerminalPayoff reward fullQuitProfile = fun _ ↦ 2 := by
  funext who
  unfold fullQuitProfile
  rw [quittingTerminalPayoff_pureSetRoot]
  fin_cases who <;> norm_num +decide [quittingSetReward, reward]

/-- Full quitting is an exact terminal Nash equilibrium against unrestricted
behavioral deviations. -/
theorem fullQuitProfile_isExactTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 fullQuitProfile := by
  unfold fullQuitProfile
  apply (isεAsymptoticNash_pureSetRoot_univ_iff reward).mpr
  intro who
  fin_cases who <;> norm_num +decide [quittingSetReward, reward]

/-- The full-quitting profile rules out every strictly positive uniform
singleton-deficit parameter. -/
theorem not_hasQuittingActualStrictSingletonDeficit
    (gap : ℝ) (hgap : 0 < gap) :
    ¬ HasQuittingActualStrictSingletonDeficit reward gap := by
  intro hdeficit
  obtain ⟨who, hwho⟩ := hdeficit fullQuitProfile
  have hpayoff := congrFun fullQuitProfile_terminalPayoff who
  rw [hpayoff, reward_singleton] at hwho
  linarith

/-- Thus no positive strict-deficit certificate exists for this actual table. -/
theorem not_exists_positive_actualStrictSingletonDeficit :
    ¬ ∃ gap : ℝ, 0 < gap ∧
      HasQuittingActualStrictSingletonDeficit reward gap := by
  rintro ⟨gap, hgap, hdeficit⟩
  exact not_hasQuittingActualStrictSingletonDeficit gap hgap hdeficit

/-- Group exclusion fails for every cap `beta` (hence, in particular, for
every `beta < 1`): at the full-quitting profile every singleton-relative
surplus is exactly one, while the weights must sum to one. -/
theorem not_hasQuittingActualNonconcentratedGroupExclusion (beta : ℝ) :
    ¬ HasQuittingActualNonconcentratedGroupExclusion reward beta := by
  intro hgroup
  obtain ⟨weight, _, hsum, _, hweighted⟩ := hgroup fullQuitProfile
  have hsurplus (who : Fin 4) :
      quittingTerminalPayoff reward fullQuitProfile who -
          reward (quittingSingletonTerminal who) who = 1 := by
    rw [congrFun fullQuitProfile_terminalPayoff who, reward_singleton]
    norm_num
  simp_rw [hsurplus, mul_one] at hweighted
  linarith

/-- Weak exclusion fails for every owner set, including every nonempty one:
the full-quitting payoff is `2` at every coordinate and every own singleton is
`1`.  The stronger empty-set case also follows from its impossible witness. -/
theorem not_hasQuittingActualWeakSubsetExclusion (owners : Finset (Fin 4)) :
    ¬ HasQuittingActualWeakSubsetExclusion reward owners := by
  rintro ⟨_, hexclusion⟩
  obtain ⟨who, _, hwho⟩ := hexclusion fullQuitProfile
  have hpayoff := congrFun fullQuitProfile_terminalPayoff who
  rw [hpayoff, reward_singleton] at hwho
  norm_num at hwho

end GameTheory.FiniteCalendarPredicateFailureExactNashBoundary
