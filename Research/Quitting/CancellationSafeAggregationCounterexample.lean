/-
Experimental: a literal two-row obstruction to converting eventwise positive
Quit accounts into one behavioral deviation.
-/

import UniformEquilibrium.Quitting.Terminal.TargetTail.FiniteChainTerminalCompiler
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity

noncomputable section

namespace GameTheory
namespace CancellationSafeAggregationCounterexample

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

/-- Two-player table, scaled by `s`.  Player `false` is the marked player;
player `true` has zero payoff throughout. -/
def reward (s : ℝ)
    (S : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun player =>
    if player then 0
    else
      match decide (false ∈ S.1), decide (true ∈ S.1) with
      | true, false => s
      | false, true => 4 * s / 3
      | true, true => s / 3
      | false, false => 0

/-- Product row with arbitrary marked-player marginal and displayed opponent
marginal. -/
def row (own opponent : PMF Bool) : Bool → PMF Bool :=
  fun player => if player then opponent else own

def quarter : PMF Bool :=
  quittingHazardCoin (1 / 4 : ℝ) (by norm_num) (by norm_num)

def half : PMF Bool :=
  quittingHazardCoin (1 / 2 : ℝ) (by norm_num) (by norm_num)

@[simp] theorem quarter_true : (quarter true).toReal = 1 / 4 := by
  simp [quarter]

@[simp] theorem quarter_false : (quarter false).toReal = 3 / 4 := by
  simp [quarter]
  norm_num

@[simp] theorem half_true : (half true).toReal = 1 / 2 := by
  simp [half]

@[simp] theorem half_false : (half false).toReal = 1 / 2 := by
  simp [half]
  norm_num

/-- The marked player's Quit endpoint at the second row. -/
theorem second_quitValue (s : ℝ) (own : PMF Bool) :
    quittingRootQuitPayoff (reward s) 0 (row own half) false = 2 * s / 3 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp [row, reward, quittingRootPayoff, quittingQuitters]
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  rw [if_pos ⟨false, by simp⟩]
  ring

/-- The marked player's Continue endpoint at the second row. -/
theorem second_continueValue (s : ℝ) (own : PMF Bool) :
    quittingRootContinuePayoff (reward s) 0 (row own half) false = 2 * s / 3 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp [row, reward, quittingRootPayoff, quittingQuitters]
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  rw [if_pos ⟨true, by simp⟩]
  ring

/-- Since both endpoints tie, the second-row value is independent of the
marked player's marginal. -/
theorem second_successorValue (s : ℝ) (own : PMF Bool) :
    quittingRootSuccessorPayoff (reward s) 0 (row own half) false = 2 * s / 3 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    second_quitValue, second_continueValue]
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (row own half) false
  change (own false).toReal + (own true).toReal = 1 at hsum
  change (own true).toReal * (2 * s / 3) +
    (own false).toReal * (2 * s / 3) = 2 * s / 3
  calc
    _ = ((own false).toReal + (own true).toReal) * (2 * s / 3) := by ring
    _ = 2 * s / 3 := by rw [hsum]; ring

/-- The marked player's Quit endpoint at the first row, when the literal
continuation value is the second-row tie value. -/
theorem first_quitValue (s : ℝ) (own : PMF Bool) :
    quittingRootQuitPayoff (reward s)
      (fun _ => 2 * s / 3) (row own quarter) false = 5 * s / 6 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp [row, reward, quittingRootPayoff, quittingQuitters]
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  rw [if_pos ⟨false, by simp⟩]
  ring

/-- The marked player's Continue endpoint at the first row has the same
value, with the second-row payoff as literal continuation. -/
theorem first_continueValue (s : ℝ) (own : PMF Bool) :
    quittingRootContinuePayoff (reward s)
      (fun _ => 2 * s / 3) (row own quarter) false = 5 * s / 6 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp [row, reward, quittingRootPayoff, quittingQuitters]
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  rw [if_pos ⟨true, by simp⟩]
  ring

/-- The first-row value is likewise independent of the marked player's
marginal. -/
theorem first_successorValue (s : ℝ) (own : PMF Bool) :
    quittingRootSuccessorPayoff (reward s)
      (fun _ => 2 * s / 3) (row own quarter) false = 5 * s / 6 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    first_quitValue, first_continueValue]
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (row own quarter) false
  change (own false).toReal + (own true).toReal = 1 at hsum
  change (own true).toReal * (5 * s / 6) +
    (own false).toReal * (5 * s / 6) = 5 * s / 6
  calc
    _ = ((own false).toReal + (own true).toReal) * (5 * s / 6) := by ring
    _ = 5 * s / 6 := by rw [hsum]; ring

/-- The literal two-row chronology, with arbitrary marked-player marginals
at its two marked rows and perpetual continuation afterwards. -/
def roots (ownFirst ownSecond : PMF Bool) : ℕ → Bool → PMF Bool
  | 0 => row ownFirst quarter
  | 1 => row ownSecond half
  | _ => quittingAllContinueRoot

theorem roots_allContinue_from_two (ownFirst ownSecond : PMF Bool)
    (time : ℕ) (htime : 2 ≤ time) :
    roots ownFirst ownSecond time = quittingAllContinueRoot := by
  cases time with
  | zero => omega
  | succ time =>
      cases time with
      | zero => omega
      | succ time => rfl

/-- The tail after the two marked rows is literal Never. -/
theorem terminalValue_two (s : ℝ) (ownFirst ownSecond : PMF Bool) :
    quittingRootSequenceTerminalValue (reward s)
      (roots ownFirst ownSecond) false 2 = 0 := by
  exact quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
    (reward s) (roots ownFirst ownSecond) false 2
      (roots_allContinue_from_two ownFirst ownSecond)

/-- Conditional value at the second marked row. -/
theorem terminalValue_one (s : ℝ) (ownFirst ownSecond : PMF Bool) :
    quittingRootSequenceTerminalValue (reward s)
      (roots ownFirst ownSecond) false 1 = 2 * s / 3 := by
  rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff,
    terminalValue_two]
  change quittingRootSuccessorPayoff (reward s) 0
    (row ownSecond half) false = 2 * s / 3
  exact second_successorValue s ownSecond

/-- **Literal cancellation obstruction.**  Every behavioral modification of
the marked player supported on the two rows has exactly the same payoff.
The two arbitrary Boolean marginals are the complete behavioral choice set
on this finite live spine. -/
theorem terminalValue_zero_independent_of_marked_strategy
    (s : ℝ) (ownFirst ownSecond : PMF Bool) :
    quittingRootSequenceTerminalValue (reward s)
      (roots ownFirst ownSecond) false 0 = 5 * s / 6 := by
  rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
  change quittingRootSuccessorPayoff (reward s)
    (fun player => quittingRootSequenceTerminalValue (reward s)
      (roots ownFirst ownSecond) player 1)
    (row ownFirst quarter) false = 5 * s / 6
  calc
    _ = quittingRootSuccessorPayoff (reward s)
        (fun _ => 2 * s / 3) (row ownFirst quarter) false :=
      quittingRootSuccessorPayoff_congr_apply
        (reward s)
        (fun player => quittingRootSequenceTerminalValue (reward s)
          (roots ownFirst ownSecond) player 1)
        (fun _ => 2 * s / 3) (row ownFirst quarter) false
        (terminalValue_one s ownFirst ownSecond)
    _ = 5 * s / 6 := first_successorValue s ownFirst

/-- At the first row the eventwise positive and negative accounts are both
`s/4`, even though the signed Quit gain is zero. -/
theorem first_positive_negative_accounts (s : ℝ) :
    (3 / 4 : ℝ) * (s / 3) = s / 4 ∧
      (1 / 4 : ℝ) * s = s / 4 := by
  constructor <;> ring

/-- At the second row the conditional positive and negative accounts are
both `s/2`; after multiplying by reach `3/4`, the positive account is
`3s/8`, while the signed Quit gain is zero. -/
theorem second_positive_negative_accounts (s : ℝ) :
    (1 / 2 : ℝ) * s = s / 2 ∧
      (3 / 4 : ℝ) * (s / 2) = 3 * s / 8 := by
  constructor <;> ring

/-- The first row's formal eventwise positive Quit account is `s/4` for
nonnegative scale.  The other opponent-coalition atom is negative and is
removed by the positive part. -/
theorem first_sum_quitDirectedAtoms (s : ℝ) (hs : 0 ≤ s) :
    (∑ coalition ∈ (Finset.univ.erase false).powerset,
      quittingRootQuitDirectedAtom (reward s) (fun _ => 2 * s / 3)
        (row (PMF.pure false) quarter) false coalition) = s / 4 := by
  classical
  have hcarrier : (Finset.univ.erase false).powerset =
      ({∅, {true}} : Finset (Finset Bool)) := by decide
  rw [hcarrier]
  simp [quittingRootQuitDirectedAtom, quittingOpponentCoalitionMass,
    quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    row, reward, quarter_true]
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  have hbool : ({true, false} : Finset Bool).erase false = {true} := by decide
  rw [hbool]
  simp [quarter_false]
  ring

/-- The second row's conditional formal eventwise positive Quit account is
`s/2`; its actual reach weight is `3/4`. -/
theorem second_sum_quitDirectedAtoms (s : ℝ) (hs : 0 ≤ s) :
    (∑ coalition ∈ (Finset.univ.erase false).powerset,
      quittingRootQuitDirectedAtom (reward s) 0
        (row (PMF.pure false) half) false coalition) = s / 2 := by
  classical
  have hcarrier : (Finset.univ.erase false).powerset =
      ({∅, {true}} : Finset (Finset Bool)) := by decide
  rw [hcarrier]
  simp [quittingRootQuitDirectedAtom, quittingOpponentCoalitionMass,
    quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    row, reward, half_true]
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  have hbool : ({true, false} : Finset Bool).erase false = {true} := by decide
  rw [hbool]
  simp [half_false]
  ring

/-- The two reached formal positive-part accounts sum to `κ` at the scale
used by the obstruction. -/
theorem reached_sum_quitDirectedAtoms_eq_kappa
    (κ : ℝ) (hκ : 0 ≤ κ) :
    let s := 8 * κ / 5
    (∑ coalition ∈ (Finset.univ.erase false).powerset,
        quittingRootQuitDirectedAtom (reward s) (fun _ => 2 * s / 3)
          (row (PMF.pure false) quarter) false coalition) +
      (3 / 4 : ℝ) *
        (∑ coalition ∈ (Finset.univ.erase false).powerset,
          quittingRootQuitDirectedAtom (reward s) 0
            (row (PMF.pure false) half) false coalition) = κ := by
  dsimp only
  rw [first_sum_quitDirectedAtoms, second_sum_quitDirectedAtoms]
  · ring
  · positivity
  · positivity

/-- With `s = 8κ/5`, the two literal positive-part accounts sum to exactly
`κ`, while every supported behavioral modification has zero gain. -/
theorem positiveAccount_eq_kappa_and_all_modifications_zero
    (κ : ℝ) (ownFirst ownSecond : PMF Bool) :
    let s := 8 * κ / 5
    s / 4 + 3 * s / 8 = κ ∧
      quittingRootSequenceTerminalValue (reward s)
          (roots ownFirst ownSecond) false 0 = 5 * s / 6 := by
  dsimp only
  constructor
  · ring
  · exact terminalValue_zero_independent_of_marked_strategy _ _ _

end CancellationSafeAggregationCounterexample
end GameTheory
