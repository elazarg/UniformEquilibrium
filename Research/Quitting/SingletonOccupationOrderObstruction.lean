/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFixedTableDiffuseIncidenceRegression
import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.Boundary.Holonomy.Basic
import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Unordered singleton occupation does not determine stopping incentives

After stochastic-button collision compression, the remaining diffuse object
is singleton flow.  This experiment tests whether that flow may be compressed
as an unordered occupation measure.

Two two-row opponent chronologies below have exactly the same survival-weighted
singleton occupation: one half on `{left}` and one half on `{right}`, zero on
the distinguished owner, zero collision, and zero survival after the block.
They differ only in order.

Nevertheless the owner's two-date pure-stopping cap is `1` in the first word
and `1/2` in the reversed word.  Thus terminal singleton weights, even with
the tail and collision ledgers fixed exactly, do not determine unilateral
stopping incentives.  Any useful finite compression must retain an ordered
continuation/obstacle coordinate.
-/


noncomputable section

namespace Research.QuittingSingletonOccupationOrderObstruction

open GameTheory Math.Probability Math.PMFProduct
open scoped BigOperators

abbrev Player := Fin 3

abbrev owner : Player := 0
abbrev left : Player := 1
abbrev right : Player := 2

abbrev fairCoin : PMF Bool := PMF.uniformOfFintype Bool

/-- Only the owner's rewards matter.  Quitting alone and quitting with
`left` pay `1`; quitting with `right` pays `-1`.  Opponent-only outcomes pay
zero. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who =>
    if who = owner then
      if owner ∈ terminal.1 then
        if left ∈ terminal.1 then 1
        else if right ∈ terminal.1 then -1
        else 1
      else 0
    else 0

/-- A row in which only the displayed opponent uses a fair button. -/
def fairSingletonRow (active : Player) : Player → PMF Bool := fun who =>
  quittingSoloStationaryRoot active fairCoin who

/-- A row in which only the displayed opponent quits surely. -/
def sureSingletonRow (active : Player) : Player → PMF Bool := fun who =>
  quittingSoloStationaryRoot active (PMF.pure true) who

/-- `left` receives the fair first button; conditional on survival, `right`
quits surely at the second row. -/
def leftThenRight : ℕ → Player → PMF Bool
  | 0 => fairSingletonRow left
  | 1 => sureSingletonRow right
  | _ => fun _ => PMF.pure false

/-- The same two singleton terminal weights in the reverse order. -/
def rightThenLeft : ℕ → Player → PMF Bool
  | 0 => fairSingletonRow right
  | 1 => sureSingletonRow left
  | _ => fun _ => PMF.pure false

@[simp] theorem singleton_owner_compl :
    ({owner} : Finset Player)ᶜ = {left, right} := by decide

@[simp] theorem singleton_left_compl :
    ({left} : Finset Player)ᶜ = {owner, right} := by decide

@[simp] theorem singleton_right_compl :
    ({right} : Finset Player)ᶜ = {owner, left} := by decide

@[simp] theorem univ_erase_owner :
    (Finset.univ : Finset Player).erase owner = {left, right} := by decide

@[simp] theorem univ_erase_left :
    (Finset.univ : Finset Player).erase left = {owner, right} := by decide

@[simp] theorem univ_erase_right :
    (Finset.univ : Finset Player).erase right = {owner, left} := by decide

@[simp] theorem fairSingletonRow_coalitionMass_self (active : Player) :
    quittingRootCoalitionMass (fairSingletonRow active) {active} = 1 / 2 := by
  unfold fairSingletonRow
  rw [quittingRootCoalitionMass_solo_of_nonempty active fairCoin {active}
    (by simp)]
  norm_num [fairSingletonRow, fairCoin, PMF.uniformOfFintype_apply]

@[simp] theorem fairSingletonRow_coalitionMass_other
    (active other : Player) (hne : other ≠ active) :
    quittingRootCoalitionMass (fairSingletonRow active) {other} = 0 := by
  unfold fairSingletonRow
  rw [quittingRootCoalitionMass_solo_of_nonempty active fairCoin {other}
    (by simp)]
  simp [hne]

@[simp] theorem sureSingletonRow_coalitionMass_self (active : Player) :
    quittingRootCoalitionMass (sureSingletonRow active) {active} = 1 := by
  unfold sureSingletonRow
  rw [quittingRootCoalitionMass_solo_of_nonempty active (PMF.pure true)
    {active} (by simp)]
  simp

@[simp] theorem sureSingletonRow_coalitionMass_other
    (active other : Player) (hne : other ≠ active) :
    quittingRootCoalitionMass (sureSingletonRow active) {other} = 0 := by
  unfold sureSingletonRow
  rw [quittingRootCoalitionMass_solo_of_nonempty active (PMF.pure true)
    {other} (by simp)]
  simp [hne]

@[simp] theorem fairSingletonRow_coalitionMass
    (active other : Player) :
    quittingRootCoalitionMass (fairSingletonRow active) {other} =
      if other = active then 1 / 2 else 0 := by
  by_cases h : other = active
  · subst other
    simp
  · exact (fairSingletonRow_coalitionMass_other active other h).trans <|
      by simp [h]

@[simp] theorem sureSingletonRow_coalitionMass
    (active other : Player) :
    quittingRootCoalitionMass (sureSingletonRow active) {other} =
      if other = active then 1 else 0 := by
  by_cases h : other = active
  · subst other
    simp
  · exact (sureSingletonRow_coalitionMass_other active other h).trans <|
      by simp [h]

@[simp] theorem quittingRootCollisionMass_solo
    (active : Player) (hazard : PMF Bool) :
    quittingRootCollisionMass
        (quittingSoloStationaryRoot active hazard) = 0 := by
  rw [quittingRootCollisionMass_eq_sum_coalitionMass]
  apply Finset.sum_eq_zero
  intro coalition hcoalition
  have hcard : 2 ≤ coalition.card := (Finset.mem_filter.mp hcoalition).2
  rw [quittingRootCoalitionMass_solo_of_nonempty active hazard coalition
    (Finset.card_pos.mp (by omega))]
  split_ifs with hsingleton
  · subst coalition
    simp at hcard
  · rfl

@[simp] theorem fairSingletonRow_continueMass (active : Player) :
    quittingStationaryContinueMass (fairSingletonRow active) = 1 / 2 := by
  unfold fairSingletonRow
  rw [quittingStationaryContinueMass_solo]
  norm_num [fairCoin, PMF.uniformOfFintype_apply]

@[simp] theorem sureSingletonRow_continueMass (active : Player) :
    quittingStationaryContinueMass (sureSingletonRow active) = 0 := by
  unfold sureSingletonRow
  rw [quittingStationaryContinueMass_solo]
  simp

@[simp] theorem fairSingletonRow_collisionMass (active : Player) :
    quittingRootCollisionMass (fairSingletonRow active) = 0 := by
  unfold fairSingletonRow
  exact quittingRootCollisionMass_solo active fairCoin

@[simp] theorem sureSingletonRow_collisionMass (active : Player) :
    quittingRootCollisionMass (sureSingletonRow active) = 0 := by
  unfold sureSingletonRow
  exact quittingRootCollisionMass_solo active (PMF.pure true)

/-- Survival-weighted mass of one singleton in the two-row block. -/
def twoRowSingletonOccupation
    (roots : ℕ → Player → PMF Bool) (who : Player) : ℝ :=
  ∑ time ∈ Finset.range 2,
    quittingSurvivalPrefix roots time *
      quittingRootCoalitionMass (roots time) {who}

/-- The two chronologies have exactly the same unordered singleton
occupation vector. -/
theorem singletonOccupation_eq :
    twoRowSingletonOccupation leftThenRight =
      twoRowSingletonOccupation rightThenLeft := by
  funext who
  fin_cases who <;>
    norm_num [twoRowSingletonOccupation, quittingSurvivalPrefix,
      leftThenRight, rightThenLeft, fairSingletonRow,
      sureSingletonRow, fairCoin, PMF.uniformOfFintype_apply,
      owner, left, right,
      Finset.sum_range_succ, Finset.prod_range_succ]

/-- Both words are fully absorbed after their two rows. -/
theorem terminalSurvival_eq_zero :
    quittingSurvivalPrefix leftThenRight 2 = 0 ∧
      quittingSurvivalPrefix rightThenLeft 2 = 0 := by
  constructor <;>
    norm_num [quittingSurvivalPrefix,
      leftThenRight, rightThenLeft, fairSingletonRow, sureSingletonRow,
      fairCoin, PMF.uniformOfFintype_apply, owner, left, right,
      Finset.prod_range_succ]

/-- Neither chronology contains a simultaneous opponent collision. -/
theorem twoRowCollisionMass_eq_zero :
    (∑ time ∈ Finset.range 2,
      quittingSurvivalPrefix leftThenRight time *
        quittingRootCollisionMass (leftThenRight time)) = 0 ∧
    (∑ time ∈ Finset.range 2,
      quittingSurvivalPrefix rightThenLeft time *
        quittingRootCollisionMass (rightThenLeft time)) = 0 := by
  constructor <;>
    norm_num [quittingSurvivalPrefix,
      leftThenRight, rightThenLeft, fairSingletonRow, sureSingletonRow,
      fairCoin, PMF.uniformOfFintype_apply, owner, left, right,
      Finset.sum_range_succ, Finset.prod_range_succ]

/-- At the first date of the first word, quitting yields `1`: either the
owner quits alone or together with `left`, and both outcomes pay `1`. -/
theorem leftThenRight_quitValue_zero :
    quittingFixedOpponentsQuitValue reward leftThenRight owner 0 = 1 := by
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  norm_num [expect_eq_sum, quittingRootPayoff, reward, leftThenRight,
    fairSingletonRow, quittingSoloStationaryRoot, fairCoin,
    PMF.uniformOfFintype_apply,
    owner, left, right]

/-- Reversing the first button averages the owner's solo payoff `1` and its
`right`-collision payoff `-1`. -/
theorem rightThenLeft_quitValue_zero :
    quittingFixedOpponentsQuitValue reward rightThenLeft owner 0 = 0 := by
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  norm_num [expect_eq_sum, quittingRootPayoff, reward, rightThenLeft,
    fairSingletonRow, quittingSoloStationaryRoot, fairCoin,
    PMF.uniformOfFintype_apply,
    owner, left, right]

theorem leftThenRight_quitValue_one :
    quittingFixedOpponentsQuitValue reward leftThenRight owner 1 = -1 := by
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  norm_num [expect_eq_sum, quittingRootPayoff, reward, leftThenRight,
    sureSingletonRow, quittingSoloStationaryRoot, owner, left, right]

theorem rightThenLeft_quitValue_one :
    quittingFixedOpponentsQuitValue reward rightThenLeft owner 1 = 1 := by
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  norm_num [expect_eq_sum, quittingRootPayoff, reward, rightThenLeft,
    sureSingletonRow, quittingSoloStationaryRoot, owner, left, right]

/-- Watching the first fair opponent button has zero immediate reward in
both words. -/
theorem first_continueReward_eq_zero :
    quittingFixedOpponentsContinueReward reward leftThenRight owner 0 = 0 ∧
      quittingFixedOpponentsContinueReward reward rightThenLeft owner 0 = 0 := by
  constructor <;>
    unfold quittingFixedOpponentsContinueReward
      quittingRootAbsorbingContribution quittingRootExpectedPayoff <;>
    rw [Math.PMFProduct.expect_pmfPi_fin3] <;>
    norm_num [expect_eq_sum, quittingRootPayoff, reward,
      leftThenRight, rightThenLeft, fairSingletonRow,
      quittingSoloStationaryRoot, fairCoin,
      PMF.uniformOfFintype_apply, owner, left, right]

/-- The sure opponent singleton at the second row also gives the continuing
owner zero immediate payoff. -/
theorem second_continueReward_eq_zero :
    quittingFixedOpponentsContinueReward reward leftThenRight owner 1 = 0 ∧
      quittingFixedOpponentsContinueReward reward rightThenLeft owner 1 = 0 := by
  constructor <;>
    unfold quittingFixedOpponentsContinueReward
      quittingRootAbsorbingContribution quittingRootExpectedPayoff <;>
    rw [Math.PMFProduct.expect_pmfPi_fin3] <;>
    norm_num [expect_eq_sum, quittingRootPayoff, reward,
      leftThenRight, rightThenLeft, sureSingletonRow,
      quittingSoloStationaryRoot, owner, left, right]

theorem first_opponentContinueMass_eq_half :
    quittingFixedOpponentsContinueMass leftThenRight owner 0 = 1 / 2 ∧
      quittingFixedOpponentsContinueMass rightThenLeft owner 0 = 1 / 2 := by
  constructor
  · change quittingStationaryContinueMass
      (Function.update (fairSingletonRow left) owner (PMF.pure false)) =
        1 / 2
    unfold fairSingletonRow
    rw [update_quittingSoloStationaryRoot_other (by decide : owner ≠ left),
      quittingStationaryContinueMass_solo]
    norm_num [fairCoin, PMF.uniformOfFintype_apply]
  · change quittingStationaryContinueMass
      (Function.update (fairSingletonRow right) owner (PMF.pure false)) =
        1 / 2
    unfold fairSingletonRow
    rw [update_quittingSoloStationaryRoot_other (by decide : owner ≠ right),
      quittingStationaryContinueMass_solo]
    norm_num [fairCoin, PMF.uniformOfFintype_apply]

theorem leftThenRight_pureTimeValues :
    quittingRootSequencePureTimeTerminalValue reward leftThenRight owner
        (some 0) 0 = 1 ∧
      quittingRootSequencePureTimeTerminalValue reward leftThenRight owner
        (some 1) 0 = -1 / 2 := by
  constructor
  · rw [quittingRootSequencePureTimeTerminalValue_some_eq]
    norm_num [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight,
      leftThenRight_quitValue_zero]
  · rw [quittingRootSequencePureTimeTerminalValue_some_eq]
    rcases first_continueReward_eq_zero with ⟨hreward, _⟩
    rcases first_opponentContinueMass_eq_half with ⟨hmass, _⟩
    norm_num [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight,
      hreward, hmass, leftThenRight_quitValue_one]

theorem rightThenLeft_pureTimeValues :
    quittingRootSequencePureTimeTerminalValue reward rightThenLeft owner
        (some 0) 0 = 0 ∧
      quittingRootSequencePureTimeTerminalValue reward rightThenLeft owner
        (some 1) 0 = 1 / 2 := by
  constructor
  · rw [quittingRootSequencePureTimeTerminalValue_some_eq]
    norm_num [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight,
      rightThenLeft_quitValue_zero]
  · rw [quittingRootSequencePureTimeTerminalValue_some_eq]
    rcases first_continueReward_eq_zero with ⟨_, hreward⟩
    rcases first_opponentContinueMass_eq_half with ⟨_, hmass⟩
    norm_num [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight,
      hreward, hmass, rightThenLeft_quitValue_one]

/-- The finite two-date stopping cap sees the order despite identical
singleton occupation, collision, and tail ledgers. -/
theorem twoDateStoppingCap_order_gap :
    max
        (quittingRootSequencePureTimeTerminalValue reward leftThenRight owner
          (some 0) 0)
        (quittingRootSequencePureTimeTerminalValue reward leftThenRight owner
          (some 1) 0) = 1 ∧
      max
        (quittingRootSequencePureTimeTerminalValue reward rightThenLeft owner
          (some 0) 0)
        (quittingRootSequencePureTimeTerminalValue reward rightThenLeft owner
          (some 1) 0) = 1 / 2 := by
  rw [leftThenRight_pureTimeValues.1, leftThenRight_pureTimeValues.2,
    rightThenLeft_pureTimeValues.1, rightThenLeft_pureTimeValues.2]
  norm_num

/-- There is no function of the unordered singleton occupation vector alone
which recovers the two-date stopping cap for all root words. -/
theorem not_exists_twoDateStoppingCap_of_singletonOccupation :
    ¬∃ decode : (Player → ℝ) → ℝ,
      ∀ roots : ℕ → Player → PMF Bool,
        decode (twoRowSingletonOccupation roots) =
          max
            (quittingRootSequencePureTimeTerminalValue reward roots owner
              (some 0) 0)
            (quittingRootSequencePureTimeTerminalValue reward roots owner
              (some 1) 0) := by
  rintro ⟨decode, hdecode⟩
  have hleft := hdecode leftThenRight
  have hright := hdecode rightThenLeft
  rw [singletonOccupation_eq] at hleft
  rw [twoDateStoppingCap_order_gap.1] at hleft
  rw [twoDateStoppingCap_order_gap.2] at hright
  linarith

/-! ## The correct exact quotient detects the order -/

/-- The literal two-row Bellman value of the first chronology. -/
theorem leftThenRight_finiteBestResponse :
    quittingFiniteTerminalBestResponseValue reward leftThenRight owner 0 0 2 =
      1 := by
  simp only [quittingFiniteTerminalBestResponseValue]
  rw [leftThenRight_quitValue_zero, first_continueReward_eq_zero.1,
    first_opponentContinueMass_eq_half.1, leftThenRight_quitValue_one,
    second_continueReward_eq_zero.1]
  norm_num [quittingFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueMass, leftThenRight, sureSingletonRow,
    quittingSoloStationaryRoot, reward]

/-- The literal two-row Bellman value of the reversed chronology. -/
theorem rightThenLeft_finiteBestResponse :
    quittingFiniteTerminalBestResponseValue reward rightThenLeft owner 0 0 2 =
      1 / 2 := by
  simp only [quittingFiniteTerminalBestResponseValue]
  rw [rightThenLeft_quitValue_zero, first_continueReward_eq_zero.2,
    first_opponentContinueMass_eq_half.2, rightThenLeft_quitValue_one,
    second_continueReward_eq_zero.2]
  norm_num [quittingFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueMass, rightThenLeft, sureSingletonRow,
    quittingSoloStationaryRoot, reward]

/-- Boundary holonomy retains precisely the chronological stopping datum
which unordered singleton occupation loses. -/
theorem finiteBoundaryHolonomy_ne :
    quittingFiniteBoundaryHolonomy reward leftThenRight 0 1 ≠
      quittingFiniteBoundaryHolonomy reward rightThenLeft 0 1 := by
  intro hequal
  have heval := congrArg
    (fun holonomy : QuittingBoundaryHolonomy Player =>
      (holonomy.bestResponse owner).eval 0) hequal
  rw [quittingFiniteBoundaryHolonomy_bestResponse_eval,
    quittingFiniteBoundaryHolonomy_bestResponse_eval,
    leftThenRight_finiteBestResponse,
    rightThenLeft_finiteBestResponse] at heval
  norm_num at heval

/-- Equal unordered occupation can therefore land in different exact
strategic equivalence classes. -/
theorem same_singletonOccupation_distinct_holonomy :
    twoRowSingletonOccupation leftThenRight =
        twoRowSingletonOccupation rightThenLeft ∧
      quittingFiniteBoundaryHolonomy reward leftThenRight 0 1 ≠
        quittingFiniteBoundaryHolonomy reward rightThenLeft 0 1 :=
  ⟨singletonOccupation_eq, finiteBoundaryHolonomy_ne⟩


end Research.QuittingSingletonOccupationOrderObstruction
