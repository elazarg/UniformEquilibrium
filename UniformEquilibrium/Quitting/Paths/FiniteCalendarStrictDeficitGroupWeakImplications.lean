import UniformEquilibrium.Quitting.Paths.FiniteCalendarOrderedPairGroupExclusion
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Strict deficit, group exclusion, and weak exclusion

A uniform positive singleton deficit yields a uniform nonconcentrated group
exclusion parameter.  The proof derives the required second player from the
strict-deficit hypothesis itself.  Conversely, a normalized nonnegative group
weight yields weak exclusion on all players when all own singleton rewards are
nonnegative.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A positive uniform singleton deficit implies nonconcentrated group
exclusion, with one cap shared by all actual profiles.  No cardinality
assumption is needed: the deficit hypothesis itself rules out a one-player
type. -/
theorem exists_actualNonconcentratedGroupExclusion_of_strictSingletonDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (hgap : 0 < gap)
    (hdeficit : HasQuittingActualStrictSingletonDeficit reward gap) :
    ∃ beta < 1,
      HasQuittingActualNonconcentratedGroupExclusion reward beta := by
  let bound := quittingRewardBound reward
  let lambda := min ((1 : ℝ) / 2) (gap / (2 * bound + gap))
  have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
  have hdenominator : 0 < 2 * bound + gap := by
    positivity
  have hlambdaPos : 0 < lambda := by
    dsimp only [lambda]
    exact lt_min (by norm_num) (div_pos hgap hdenominator)
  have hlambdaHalf : lambda ≤ (1 : ℝ) / 2 := by
    exact min_le_left _ _
  have hlambdaFraction : lambda ≤ gap / (2 * bound + gap) := by
    exact min_le_right _ _
  have hlambdaBudget : lambda * (2 * bound + gap) ≤ gap := by
    exact (le_div_iff₀ hdenominator).mp hlambdaFraction
  let anchor : ι := Classical.choice inferInstance
  let anchorProfile := quittingStationaryProfile reward
    (quittingPureSetRoot ({anchor} : Finset ι))
  obtain ⟨other, hotherDeficit⟩ := hdeficit anchorProfile
  have hanchorOther : anchor ≠ other := by
    intro hequal
    subst other
    have hpayoff := quittingTerminalPayoff_pureSetRoot reward
      ({anchor} : Finset ι) anchor
    rw [quittingSetReward_singleton_eq_soloReward] at hpayoff
    have hpayoff' : quittingTerminalPayoff reward anchorProfile anchor =
        reward (quittingSingletonTerminal anchor) anchor := by
      dsimp only [anchorProfile]
      convert hpayoff using 1
      apply congrArg (fun terminal => reward terminal anchor)
      apply Subtype.ext
      rfl
    rw [hpayoff'] at hotherDeficit
    linarith
  apply
    (exists_actualNonconcentratedGroupExclusion_iff_exists_orderedPair
      reward).mpr
  refine ⟨lambda, hlambdaPos, hlambdaHalf, ?_⟩
  intro profile
  obtain ⟨first, hfirst⟩ := hdeficit profile
  let second := if first = anchor then other else anchor
  have hfirstSecond : first ≠ second := by
    dsimp only [second]
    split_ifs with hequal
    · intro hfirstOther
      apply hanchorOther
      rw [← hequal, hfirstOther]
    · exact hequal
  have hfirstSurplus :
      quittingTerminalPayoff reward profile first -
          reward (quittingSingletonTerminal first) first ≤ -gap := by
    linarith
  have hsecondPayoff :
      quittingTerminalPayoff reward profile second ≤ bound :=
    (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le_quittingRewardBound reward profile second)
  have hsecondSingleton :
      -bound ≤ reward (quittingSingletonTerminal second) second :=
    neg_le_of_abs_le
      (abs_reward_le_quittingRewardBound reward
        (quittingSingletonTerminal second) second)
  have hsecondSurplus :
      quittingTerminalPayoff reward profile second -
          reward (quittingSingletonTerminal second) second ≤ 2 * bound := by
    linarith
  refine ⟨first, second, hfirstSecond, ?_⟩
  calc
    (1 - lambda) *
          (quittingTerminalPayoff reward profile first -
            reward (quittingSingletonTerminal first) first) +
        lambda *
          (quittingTerminalPayoff reward profile second -
            reward (quittingSingletonTerminal second) second) ≤
        (1 - lambda) * (-gap) + lambda * (2 * bound) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hfirstSurplus (by linarith))
            (mul_le_mul_of_nonneg_left hsecondSurplus hlambdaPos.le)
    _ = lambda * (2 * bound + gap) - gap := by ring
    _ ≤ 0 := by linarith

/-- The raw finite-calendar strict-deficit condition gives the same actual
uniform group-exclusion conclusion. -/
theorem exists_actualNonconcentratedGroupExclusion_of_finiteCalendarRawStrictDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (hgap : 0 < gap)
    (hdeficit : HasQuittingFiniteCalendarRawStrictSingletonDeficit reward gap) :
    ∃ beta < 1,
      HasQuittingActualNonconcentratedGroupExclusion reward beta := by
  apply exists_actualNonconcentratedGroupExclusion_of_strictSingletonDeficit
    reward gap hgap
  exact
    (hasQuittingFiniteCalendarRawStrictSingletonDeficit_iff_actual
      reward gap).mp hdeficit

/-- A raw finite-calendar strict deficit yields raw finite-calendar group
exclusion with one uniform cap. -/
theorem exists_finiteCalendarRawNonconcentratedGroupExclusion_of_strictDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (hgap : 0 < gap)
    (hdeficit : HasQuittingFiniteCalendarRawStrictSingletonDeficit reward gap) :
    ∃ beta < 1,
      HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta := by
  obtain ⟨beta, hbeta, hactual⟩ :=
    exists_actualNonconcentratedGroupExclusion_of_finiteCalendarRawStrictDeficit
      reward gap hgap hdeficit
  exact ⟨beta, hbeta,
    (hasQuittingFiniteCalendarRawNonconcentratedGroupExclusion_iff_actual
      reward beta).mpr hactual⟩

omit [DecidableEq ι] [Nonempty ι] in
/-- Any normalized nonnegative group-exclusion weight forces some coordinate
to have nonpositive surplus.  With nonnegative own singleton rewards this is
weak exclusion on the full player set. -/
theorem hasQuittingActualWeakSubsetExclusion_univ_of_groupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ)
    (hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (hgroup : HasQuittingActualNonconcentratedGroupExclusion reward beta) :
    HasQuittingActualWeakSubsetExclusion reward Finset.univ := by
  refine ⟨fun who _ => hsingleton who, ?_⟩
  intro profile
  obtain ⟨weight, hweightNonnegative, hweightSum, _, hweighted⟩ := hgroup profile
  have hpositiveWeight : ∃ who, 0 < weight who := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ who, weight who = 0 := fun who =>
      le_antisymm (hnone who) (hweightNonnegative who)
    have : ∑ who, weight who = 0 := by
      apply Finset.sum_eq_zero
      intro who _
      exact hzero who
    linarith
  by_contra hnone
  push Not at hnone
  have hsurplusPositive : ∀ who,
      0 < quittingTerminalPayoff reward profile who -
        reward (quittingSingletonTerminal who) who := by
    intro who
    have hnoneWho := hnone who (Finset.mem_univ who)
    linarith
  have htermNonnegative : ∀ who ∈ Finset.univ,
      0 ≤ weight who *
        (quittingTerminalPayoff reward profile who -
          reward (quittingSingletonTerminal who) who) := by
    intro who _
    exact mul_nonneg (hweightNonnegative who) (hsurplusPositive who).le
  obtain ⟨who, hwhoWeight⟩ := hpositiveWeight
  have hsumPositive : 0 < ∑ who, weight who *
      (quittingTerminalPayoff reward profile who -
        reward (quittingSingletonTerminal who) who) := by
    apply Finset.sum_pos' htermNonnegative
    exact ⟨who, Finset.mem_univ who,
      mul_pos hwhoWeight (hsurplusPositive who)⟩
  linarith

/-- Raw group exclusion and nonnegative own singletons imply raw weak
exclusion on all players. -/
theorem hasQuittingFiniteCalendarRawWeakSubsetExclusion_univ_of_groupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ)
    (hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (hgroup :
      HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta) :
    HasQuittingFiniteCalendarRawWeakSubsetExclusion reward Finset.univ := by
  apply
    (hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_actual
      reward Finset.univ).mpr
  apply hasQuittingActualWeakSubsetExclusion_univ_of_groupExclusion
    reward beta hsingleton
  exact
    (hasQuittingFiniteCalendarRawNonconcentratedGroupExclusion_iff_actual
      reward beta).mp hgroup

end GameTheory
