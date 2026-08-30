/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction
import UniformEquilibrium.Quitting.Examples.FinFourOwnerRiskyStationaryClosure
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff

/-!
# Exact roots of the sharp four-player table at its solo cap

`GameTheory.FinFourOwnerRiskyStationaryClosure.sharpReward R singletonLevel`
is
evaluated here against the cap vector `![0, 0, 0, singletonLevel]`.  That
vector is the table's own solo vector, so every cap gap
`cap who - reward (quittingSingletonTerminal who) who` vanishes.

Two properties of this table drive everything below, and neither holds of
quitting games in general.  The cap coincides with the solo vector, which
deletes the empty-coalition term of the endpoint expansion; and each player's
membership gain is additive over the opponent coalition, so the surviving
terms assemble into a linear form with the fixed rational coefficients
`J who other = reward {who, other} who - reward {other} who`.  Together they
give `quittingRootEndpointDifference_productRoot_eq_collisionForm`: against
this cap the endpoint difference of a product root is the homogeneous linear
`collisionForm` of its hazards, on the whole cube, at every `R` and every
singleton level.

`eq_zero_or_eq_one_or_gain_eq_zero` then pins each coordinate of an exact root
to Continue, Quit, or `collisionForm` indifference, which is what makes the
remaining problem finite.

Enumerating those activity patterns gives `eq_allContinueRoot_of_isNash`: all
Continue is the only exact root against this cap, at every `R` and every
singleton level.  `not_sum_quittingRootQuitRates_pos` is the immediate
consequence in the shape a `Regression`-style `limitRoot_positive` field would
need.

What that discharges is uniqueness at this one cap for this one table.  It
rests on the two properties above, both of which belong to `sharpReward` and
not to quitting games in general.  It says nothing about a maximum-absorption
or maximality obligation at a finite cap, about other tables, about other
caps, or about whether any ray exists.
-/

noncomputable section

namespace GameTheory

namespace FinFourOwnerRiskyCapLimitRootUniqueness

open FinFourOwnerRiskyStationaryClosure
open Math.ProbabilityMassFunction

abbrev Player := Fin 4

/-! ## The cap and the probe root -/

/-- Cap vector at which the sharp table's exact roots are decided here. -/
def sharpCapLimit (singletonLevel : ℝ) : Payoff Player :=
  ![0, 0, 0, singletonLevel]

/-- `sharpCapLimit` is the solo vector of `sharpReward`, at every `R`. -/
theorem sharpCapLimit_eq_solo (R singletonLevel : ℝ) (who : Player) :
    sharpCapLimit singletonLevel who =
      sharpReward R singletonLevel (quittingSingletonTerminal who) who := by
  fin_cases who <;>
    norm_num +decide [sharpCapLimit, sharpReward, quittingSingletonTerminal,
      sharpActivePassive, sharpActiveGain, indicator, sharpScale]

/-- Product root at which only player `3` quits, with probability `level`. -/
def soloOwnerRoot (level : ℝ) (hzero : 0 ≤ level) (hone : level ≤ 1) :
    Player → PMF Bool :=
  fun who ↦ if who = 3 then bernoulliBool level hzero hone else PMF.pure false

@[simp] theorem soloOwnerRoot_quitProbability
    (level : ℝ) (hzero : 0 ≤ level) (hone : level ≤ 1) (who : Player) :
    ((soloOwnerRoot level hzero hone who) true).toReal =
      if who = 3 then level else 0 := by
  unfold soloOwnerRoot
  split <;> simp

/-! ### Opponent complements

`quittingOpponentCoalitionMass` takes its Continue product over
`Finset.univ.erase who \ coalition`, so each coalition expansion below needs
the eight set differences of one opponent triple. -/

theorem opponentComplement_zero :
    (({1, 2, 3} : Finset Player) \ ∅ = {1, 2, 3}) ∧
      (({1, 2, 3} : Finset Player) \ {1} = {2, 3}) ∧
      (({1, 2, 3} : Finset Player) \ {2} = {1, 3}) ∧
      (({1, 2, 3} : Finset Player) \ {3} = {1, 2}) ∧
      (({1, 2, 3} : Finset Player) \ {1, 2} = {3}) ∧
      (({1, 2, 3} : Finset Player) \ {1, 3} = {2}) ∧
      (({1, 2, 3} : Finset Player) \ {2, 3} = {1}) ∧
      (({1, 2, 3} : Finset Player) \ {1, 2, 3} = ∅) := by
  decide

theorem opponentComplement_one :
    (({0, 2, 3} : Finset Player) \ ∅ = {0, 2, 3}) ∧
      (({0, 2, 3} : Finset Player) \ {0} = {2, 3}) ∧
      (({0, 2, 3} : Finset Player) \ {2} = {0, 3}) ∧
      (({0, 2, 3} : Finset Player) \ {3} = {0, 2}) ∧
      (({0, 2, 3} : Finset Player) \ {0, 2} = {3}) ∧
      (({0, 2, 3} : Finset Player) \ {0, 3} = {2}) ∧
      (({0, 2, 3} : Finset Player) \ {2, 3} = {0}) ∧
      (({0, 2, 3} : Finset Player) \ {0, 2, 3} = ∅) := by
  decide

theorem opponentComplement_two :
    (({0, 1, 3} : Finset Player) \ ∅ = {0, 1, 3}) ∧
      (({0, 1, 3} : Finset Player) \ {0} = {1, 3}) ∧
      (({0, 1, 3} : Finset Player) \ {1} = {0, 3}) ∧
      (({0, 1, 3} : Finset Player) \ {3} = {0, 1}) ∧
      (({0, 1, 3} : Finset Player) \ {0, 1} = {3}) ∧
      (({0, 1, 3} : Finset Player) \ {0, 3} = {1}) ∧
      (({0, 1, 3} : Finset Player) \ {1, 3} = {0}) ∧
      (({0, 1, 3} : Finset Player) \ {0, 1, 3} = ∅) := by
  decide

theorem opponentComplement_three :
    (({0, 1, 2} : Finset Player) \ ∅ = {0, 1, 2}) ∧
      (({0, 1, 2} : Finset Player) \ {0} = {1, 2}) ∧
      (({0, 1, 2} : Finset Player) \ {1} = {0, 2}) ∧
      (({0, 1, 2} : Finset Player) \ {2} = {0, 1}) ∧
      (({0, 1, 2} : Finset Player) \ {0, 1} = {2}) ∧
      (({0, 1, 2} : Finset Player) \ {0, 2} = {1}) ∧
      (({0, 1, 2} : Finset Player) \ {1, 2} = {0}) ∧
      (({0, 1, 2} : Finset Player) \ {0, 1, 2} = ∅) := by
  decide

/-! ## The owner probe reads off the marked collision entry -/

/-- Player `0`'s endpoint difference along the solo-owner probe is exactly
`sharpScale` times the owner's Quit probability.  Every opponent coalition
containing `1` or `2` carries zero mass, and the empty coalition contributes
nothing because `sharpCapLimit` is the solo vector. -/
theorem quittingRootEndpointDifference_soloOwnerRoot_zero
    (R singletonLevel level : ℝ) (hzero : 0 ≤ level) (hone : level ≤ 1) :
    quittingRootEndpointDifference (sharpReward R singletonLevel)
        (sharpCapLimit singletonLevel)
        (soloOwnerRoot level hzero hone) 0 =
      level / 100 := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  unfold quittingOpponentCoalitionMass quittingEndpointInsertionToggle
    quittingStageCoalitionPayoff
  rw [show Finset.univ.erase (0 : Player) = {1, 2, 3} by decide]
  rw [show ({1, 2, 3} : Finset Player).powerset =
    {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
  obtain ⟨e0, e1, e2, e3, e12, e13, e23, -⟩ := opponentComplement_zero
  simp +decide [e0, e1, e2, e3, e12, e13, e23, soloOwnerRoot,
    sharpCapLimit, sharpReward, sharpActivePassive, sharpActiveGain,
    indicator, sharpScale]
  ring

/-- **The oracle.**  No positive solo-owner probe is an exact root against
`sharpCapLimit`: player `0` is playing pure Continue while its endpoint
difference is `level / 100 > 0`. -/
theorem not_isεQuittingRootNash_soloOwnerRoot
    (R singletonLevel level : ℝ) (hpos : 0 < level) (hone : level ≤ 1) :
    ¬ IsεQuittingRootNash (sharpReward R singletonLevel)
        (sharpCapLimit singletonLevel) 0 (soloOwnerRoot level hpos.le hone) := by
  intro hnash
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      (sharpReward R singletonLevel) (sharpCapLimit singletonLevel)
      (soloOwnerRoot level hpos.le hone)).mpr hnash
  have hzero : ((soloOwnerRoot level hpos.le hone 0) true).toReal = 0 := by
    simp
  have hnonpos := quittingRootEndpointDifference_nonpos_of_quitProbability_eq_zero
    (sharpReward R singletonLevel) (sharpCapLimit singletonLevel)
    (soloOwnerRoot level hpos.le hone) 0 hendpoint hzero
  rw [quittingRootEndpointDifference_soloOwnerRoot_zero] at hnonpos
  linarith

/-! ## The endpoint difference at the solo cap is linear -/

/-- Product root with the given Quit probabilities. -/
def productRoot (hazard : Player → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) : Player → PMF Bool :=
  fun who ↦ bernoulliBool (hazard who) (hzero who) (hone who)

/-- The collision form of the sharp table: row `who` is
`∑ other, (reward {who, other} who - reward {other} who) * hazard other`.
Its coefficients involve neither `R` nor the singleton level. -/
def collisionForm (hazard : Player → ℝ) (who : Player) : ℝ :=
  ![hazard 1 - 2 * hazard 2 + (1 / 100) * hazard 3,
    hazard 0 - 2 * hazard 2,
    (2 / 5) * (hazard 0 + hazard 1) - (39 / 100) * hazard 3,
    -hazard 0 - hazard 1 + hazard 2] who

@[simp] theorem collisionForm_zero (hazard : Player → ℝ) :
    collisionForm hazard 0 =
      hazard 1 - 2 * hazard 2 + (1 / 100) * hazard 3 := rfl

@[simp] theorem collisionForm_one (hazard : Player → ℝ) :
    collisionForm hazard 1 = hazard 0 - 2 * hazard 2 := rfl

@[simp] theorem collisionForm_two (hazard : Player → ℝ) :
    collisionForm hazard 2 =
      (2 / 5) * (hazard 0 + hazard 1) - (39 / 100) * hazard 3 := rfl

@[simp] theorem collisionForm_three (hazard : Player → ℝ) :
    collisionForm hazard 3 = -hazard 0 - hazard 1 + hazard 2 := rfl

theorem quittingRootEndpointDifference_productRoot_zero
    (R singletonLevel : ℝ) (hazard : Player → ℝ)
    (hzero : ∀ who, 0 ≤ hazard who) (hone : ∀ who, hazard who ≤ 1) :
    quittingRootEndpointDifference (sharpReward R singletonLevel)
        (sharpCapLimit singletonLevel) (productRoot hazard hzero hone) 0 =
      collisionForm hazard 0 := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  unfold quittingOpponentCoalitionMass quittingEndpointInsertionToggle
    quittingStageCoalitionPayoff
  rw [show Finset.univ.erase (0 : Player) = {1, 2, 3} by decide]
  rw [show ({1, 2, 3} : Finset Player).powerset =
    {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
  obtain ⟨e0, e1, e2, e3, e12, e13, e23, -⟩ := opponentComplement_zero
  simp +decide [e0, e1, e2, e3, e12, e13, e23, productRoot,
    collisionForm, sharpCapLimit, sharpReward, sharpActivePassive,
    sharpActiveGain, indicator, sharpScale]
  ring

theorem quittingRootEndpointDifference_productRoot_one
    (R singletonLevel : ℝ) (hazard : Player → ℝ)
    (hzero : ∀ who, 0 ≤ hazard who) (hone : ∀ who, hazard who ≤ 1) :
    quittingRootEndpointDifference (sharpReward R singletonLevel)
        (sharpCapLimit singletonLevel) (productRoot hazard hzero hone) 1 =
      collisionForm hazard 1 := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  unfold quittingOpponentCoalitionMass quittingEndpointInsertionToggle
    quittingStageCoalitionPayoff
  rw [show Finset.univ.erase (1 : Player) = {0, 2, 3} by decide]
  rw [show ({0, 2, 3} : Finset Player).powerset =
    {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
  obtain ⟨e0, e1, e2, e3, e12, e13, e23, -⟩ := opponentComplement_one
  simp +decide [e0, e1, e2, e3, e12, e13, e23, productRoot,
    collisionForm, sharpCapLimit, sharpReward, sharpActivePassive,
    sharpActiveGain, indicator, sharpScale]
  ring

theorem quittingRootEndpointDifference_productRoot_two
    (R singletonLevel : ℝ) (hazard : Player → ℝ)
    (hzero : ∀ who, 0 ≤ hazard who) (hone : ∀ who, hazard who ≤ 1) :
    quittingRootEndpointDifference (sharpReward R singletonLevel)
        (sharpCapLimit singletonLevel) (productRoot hazard hzero hone) 2 =
      collisionForm hazard 2 := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  unfold quittingOpponentCoalitionMass quittingEndpointInsertionToggle
    quittingStageCoalitionPayoff
  rw [show Finset.univ.erase (2 : Player) = {0, 1, 3} by decide]
  rw [show ({0, 1, 3} : Finset Player).powerset =
    {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
  obtain ⟨e0, e1, e2, e3, e12, e13, e23, -⟩ := opponentComplement_two
  simp +decide [e0, e1, e2, e3, e12, e13, e23, productRoot,
    collisionForm, sharpCapLimit, sharpReward, sharpActivePassive,
    sharpActiveGain, indicator, sharpLoss]
  ring

theorem quittingRootEndpointDifference_productRoot_three
    (R singletonLevel : ℝ) (hazard : Player → ℝ)
    (hzero : ∀ who, 0 ≤ hazard who) (hone : ∀ who, hazard who ≤ 1) :
    quittingRootEndpointDifference (sharpReward R singletonLevel)
        (sharpCapLimit singletonLevel) (productRoot hazard hzero hone) 3 =
      collisionForm hazard 3 := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  unfold quittingOpponentCoalitionMass quittingEndpointInsertionToggle
    quittingStageCoalitionPayoff
  rw [show Finset.univ.erase (3 : Player) = {0, 1, 2} by decide]
  rw [show ({0, 1, 2} : Finset Player).powerset =
    {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
  obtain ⟨e0, e1, e2, e3, e12, e13, e23, -⟩ := opponentComplement_three
  simp +decide [e0, e1, e2, e3, e12, e13, e23, productRoot,
    collisionForm, sharpCapLimit, sharpReward, sharpSpectatorPassive,
    indicator]
  ring

/-- **The linear collapse.**  Against `sharpCapLimit`, which is the table's own
solo vector, the endpoint difference of any product root is the homogeneous
linear `collisionForm` of its hazards, at every `R` and every singleton
level. -/
theorem quittingRootEndpointDifference_productRoot_eq_collisionForm
    (R singletonLevel : ℝ) (hazard : Player → ℝ)
    (hzero : ∀ who, 0 ≤ hazard who) (hone : ∀ who, hazard who ≤ 1)
    (who : Player) :
    quittingRootEndpointDifference (sharpReward R singletonLevel)
        (sharpCapLimit singletonLevel) (productRoot hazard hzero hone) who =
      collisionForm hazard who := by
  fin_cases who
  · exact quittingRootEndpointDifference_productRoot_zero R singletonLevel
      hazard hzero hone
  · exact quittingRootEndpointDifference_productRoot_one R singletonLevel
      hazard hzero hone
  · exact quittingRootEndpointDifference_productRoot_two R singletonLevel
      hazard hzero hone
  · exact quittingRootEndpointDifference_productRoot_three R singletonLevel
      hazard hzero hone

/-! ## What an exact root against the solo cap satisfies coordinatewise -/

@[simp] theorem productRoot_quitProbability
    (hazard : Player → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) (who : Player) :
    ((productRoot hazard hzero hone who) true).toReal = hazard who := by
  simp [productRoot]

@[simp] theorem productRoot_continueProbability
    (hazard : Player → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) (who : Player) :
    ((productRoot hazard hzero hone who) false).toReal = 1 - hazard who := by
  simp [productRoot]

/-- **The finiteness step.**  A coordinate carrying the two exact endpoint
inequalities is pinned to one of three states.  Multiplying the inequalities
gives `level * (1 - level) * gain ^ 2 ≤ 0`, whose three factors are each
nonnegative, so one of them vanishes.  Applied at four coordinates this is
what reduces the exact-root problem against a solo cap to finitely many
activity patterns. -/
theorem eq_zero_or_eq_one_or_gain_eq_zero {level gain : ℝ}
    (hzero : 0 ≤ level) (hone : level ≤ 1)
    (hcontinue : (1 - level) * gain ≤ 0) (hquit : 0 ≤ level * gain) :
    level = 0 ∨ level = 1 ∨ gain = 0 := by
  have hnonpos : level * (1 - level) * gain ^ 2 ≤ 0 := by nlinarith
  have hnonneg : 0 ≤ level * (1 - level) * gain ^ 2 :=
    mul_nonneg (mul_nonneg hzero (by linarith)) (sq_nonneg gain)
  have hvanish : level * (1 - level) * gain ^ 2 = 0 := le_antisymm hnonpos hnonneg
  rcases mul_eq_zero.mp hvanish with hpair | hsquare
  · rcases mul_eq_zero.mp hpair with hlevel | hcomplement
    · exact Or.inl hlevel
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsquare))

variable {R singletonLevel : ℝ} {hazard : Player → ℝ}
  {hzero : ∀ who, 0 ≤ hazard who} {hone : ∀ who, hazard who ≤ 1}

/-- The two exact endpoint inequalities, read through the linear collapse. -/
theorem collisionForm_endpoint_of_isNash
    (hnash : IsεQuittingRootNash (sharpReward R singletonLevel)
      (sharpCapLimit singletonLevel) 0 (productRoot hazard hzero hone))
    (who : Player) :
    (1 - hazard who) * collisionForm hazard who ≤ 0 ∧
      0 ≤ hazard who * collisionForm hazard who := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      (sharpReward R singletonLevel) (sharpCapLimit singletonLevel)
      (productRoot hazard hzero hone)).mpr hnash who
  rw [quittingRootEndpointDifference_productRoot_eq_collisionForm] at hendpoint
  simpa using hendpoint

/-- Each coordinate of an exact root against the solo cap is Continue, Quit,
or indifferent under `collisionForm`. -/
theorem hazard_trichotomy_of_isNash
    (hnash : IsεQuittingRootNash (sharpReward R singletonLevel)
      (sharpCapLimit singletonLevel) 0 (productRoot hazard hzero hone))
    (who : Player) :
    hazard who = 0 ∨ hazard who = 1 ∨ collisionForm hazard who = 0 :=
  let hendpoint := collisionForm_endpoint_of_isNash hnash who
  eq_zero_or_eq_one_or_gain_eq_zero (hzero who) (hone who)
    hendpoint.1 hendpoint.2

/-- A pure-Continue coordinate of an exact root has nonpositive collision
form. -/
theorem collisionForm_nonpos_of_hazard_eq_zero
    (hnash : IsεQuittingRootNash (sharpReward R singletonLevel)
      (sharpCapLimit singletonLevel) 0 (productRoot hazard hzero hone))
    {who : Player} (hpure : hazard who = 0) :
    collisionForm hazard who ≤ 0 := by
  have hendpoint := (collisionForm_endpoint_of_isNash hnash who).1
  rw [hpure] at hendpoint
  linarith

/-- A pure-Quit coordinate of an exact root has nonnegative collision form. -/
theorem collisionForm_nonneg_of_hazard_eq_one
    (hnash : IsεQuittingRootNash (sharpReward R singletonLevel)
      (sharpCapLimit singletonLevel) 0 (productRoot hazard hzero hone))
    {who : Player} (hpure : hazard who = 1) :
    0 ≤ collisionForm hazard who := by
  have hendpoint := (collisionForm_endpoint_of_isNash hnash who).2
  rw [hpure] at hendpoint
  linarith

/-! ## The owner-inactive slice -/

/-- On the slice where the owner does not quit, an exact root against the solo
cap is all Continue.  Player `2`'s trichotomy splits the slice three ways: two
of the branches collapse the active pair immediately, and the pure-Quit branch
runs out through players `1`, `0` and `3`.

`hazard_eq_zero_of_isNash` subsumes this.  The slice is kept because its chain
is short and independent of the owner coordinate. -/
theorem hazard_eq_zero_of_isNash_of_owner_eq_zero
    (hnash : IsεQuittingRootNash (sharpReward R singletonLevel)
      (sharpCapLimit singletonLevel) 0 (productRoot hazard hzero hone))
    (howner : hazard 3 = 0) (who : Player) :
    hazard who = 0 := by
  have hzero0 := hzero 0
  have hzero1 := hzero 1
  have hzero2 := hzero 2
  have hone0 := hone 0
  have howner3 := collisionForm_nonpos_of_hazard_eq_zero hnash howner
  rw [collisionForm_three] at howner3
  have hactive : hazard 0 = 0 ∧ hazard 1 = 0 := by
    rcases hazard_trichotomy_of_isNash hnash 2 with hmid | hmid | hmid
    · have hslack := collisionForm_nonpos_of_hazard_eq_zero hnash hmid
      rw [collisionForm_two, howner] at hslack
      constructor <;> linarith
    · exfalso
      have hsecond : hazard 1 = 0 := by
        rcases hazard_trichotomy_of_isNash hnash 1 with hone' | hone' | hone'
        · exact hone'
        · have := collisionForm_nonneg_of_hazard_eq_one hnash hone'
          rw [collisionForm_one, hmid] at this
          linarith
        · rw [collisionForm_one, hmid] at hone'
          linarith
      have hfirst : hazard 0 = 0 := by
        rcases hazard_trichotomy_of_isNash hnash 0 with hzero' | hzero' | hzero'
        · exact hzero'
        · have := collisionForm_nonneg_of_hazard_eq_one hnash hzero'
          rw [collisionForm_zero, hmid, hsecond, howner] at this
          linarith
        · rw [collisionForm_zero, hmid, hsecond, howner] at hzero'
          linarith
      rw [hfirst, hsecond, hmid] at howner3
      linarith
    · rw [collisionForm_two, howner] at hmid
      constructor <;> linarith
  have hthird : hazard 2 = 0 := by
    rw [hactive.1, hactive.2] at howner3
    linarith [hzero 2]
  fin_cases who
  · exact hactive.1
  · exact hactive.2
  · exact hthird
  · exact howner

/-! ## Every exact root against the solo cap is all Continue -/

/-- **The enumeration.**  An exact root against `sharpCapLimit` has every
hazard zero.  Player `2`'s trichotomy splits into a pure-Continue branch that
kills the active pair through player `3`, a pure-Quit branch that runs out of
room at player `2`'s own condition, and an indifferent branch carrying
`(2 / 5) * (hazard 0 + hazard 1) = (39 / 100) * hazard 3`, which is then split
again at players `1`, `0` and `3`.  Every leaf is a linear infeasibility over
the rationals. -/
theorem hazard_eq_zero_of_isNash
    (hnash : IsεQuittingRootNash (sharpReward R singletonLevel)
      (sharpCapLimit singletonLevel) 0 (productRoot hazard hzero hone))
    (who : Player) :
    hazard who = 0 := by
  have b0 := hzero 0
  have b1 := hzero 1
  have b2 := hzero 2
  have b3 := hzero 3
  have u3 := hone 3
  have low : ∀ i : Player, hazard i = 0 → collisionForm hazard i ≤ 0 :=
    fun i hpure ↦ collisionForm_nonpos_of_hazard_eq_zero hnash hpure
  have high : ∀ i : Player, hazard i = 1 → 0 ≤ collisionForm hazard i :=
    fun i hpure ↦ collisionForm_nonneg_of_hazard_eq_one hnash hpure
  have tri := hazard_trichotomy_of_isNash hnash
  have hall : hazard 0 = 0 ∧ hazard 1 = 0 ∧ hazard 2 = 0 ∧ hazard 3 = 0 := by
    rcases tri 2 with hmid | hmid | hmid
    · -- Player `2` plays pure Continue.
      have hpair : hazard 0 = 0 ∧ hazard 1 = 0 := by
        rcases tri 3 with hown | hown | hown
        · have hslack := low 2 hmid
          rw [collisionForm_two, hown] at hslack
          exact ⟨by linarith, by linarith⟩
        · have hslack := high 3 hown
          rw [collisionForm_three, hmid] at hslack
          exact ⟨by linarith, by linarith⟩
        · rw [collisionForm_three, hmid] at hown
          exact ⟨by linarith, by linarith⟩
      have hown : hazard 3 = 0 := by
        have hslack := low 0 hpair.1
        rw [collisionForm_zero, hpair.2, hmid] at hslack
        linarith
      exact ⟨hpair.1, hpair.2, hmid, hown⟩
    · -- Player `2` plays pure Quit.
      exfalso
      have hsecond : hazard 1 = 0 := by
        rcases tri 1 with h | h | h
        · exact h
        · have hslack := high 1 h
          rw [collisionForm_one, hmid] at hslack
          linarith [hone 0]
        · rw [collisionForm_one, hmid] at h
          linarith [hone 0]
      have hfirst : hazard 0 = 0 := by
        rcases tri 0 with h | h | h
        · exact h
        · have hslack := high 0 h
          rw [collisionForm_zero, hsecond, hmid] at hslack
          linarith
        · rw [collisionForm_zero, hsecond, hmid] at h
          linarith
      have hown : hazard 3 = 0 := by
        have hslack := high 2 hmid
        rw [collisionForm_two, hfirst, hsecond] at hslack
        linarith
      have hslack := low 3 hown
      rw [collisionForm_three, hfirst, hsecond, hmid] at hslack
      linarith
    · -- Player `2` is indifferent.
      rw [collisionForm_two] at hmid
      rcases tri 1 with h1 | h1 | h1
      · have hg1 := low 1 h1
        rw [collisionForm_one] at hg1
        rcases tri 0 with h0 | h0 | h0
        · have hown : hazard 3 = 0 := by rw [h0, h1] at hmid; linarith
          have hthird : hazard 2 = 0 := by
            have hslack := low 3 hown
            rw [collisionForm_three, h0, h1] at hslack
            linarith
          exact ⟨h0, h1, hthird, hown⟩
        · exfalso
          have hslack := high 0 h0
          rw [collisionForm_zero, h1] at hslack
          rw [h0] at hg1
          linarith
        · rw [collisionForm_zero, h1] at h0
          rw [h1] at hmid
          have hthird : hazard 2 = 0 := by linarith
          have hown : hazard 3 = 0 := by linarith
          have hfirst : hazard 0 = 0 := by linarith
          exact ⟨hfirst, h1, hthird, hown⟩
      · exfalso
        rw [h1] at hmid
        linarith
      · rw [collisionForm_one] at h1
        rcases tri 0 with h0 | h0 | h0
        · have hthird : hazard 2 = 0 := by rw [h0] at h1; linarith
          have hslack := low 0 h0
          rw [collisionForm_zero, hthird] at hslack
          have hsecond : hazard 1 = 0 := by linarith
          have hown : hazard 3 = 0 := by linarith
          exact ⟨h0, hsecond, hthird, hown⟩
        · exfalso
          rw [h0] at hmid
          linarith [hzero 1]
        · rw [collisionForm_zero] at h0
          rcases tri 3 with hown | hown | hown
          · have hfirst : hazard 0 = 0 := by rw [hown] at hmid h0; linarith
            have hthird : hazard 2 = 0 := by rw [hown] at h0; linarith
            have hsecond : hazard 1 = 0 := by rw [hown] at hmid; linarith
            exact ⟨hfirst, hsecond, hthird, hown⟩
          · exfalso
            have hslack := high 3 hown
            rw [collisionForm_three] at hslack
            rw [hown] at hmid h0
            linarith
          · rw [collisionForm_three] at hown
            have hzero3 : hazard 3 = 0 := by linarith
            have hfirst : hazard 0 = 0 := by rw [hzero3] at hmid h0; linarith
            have hthird : hazard 2 = 0 := by rw [hzero3] at h0; linarith
            have hsecond : hazard 1 = 0 := by rw [hzero3] at hmid; linarith
            exact ⟨hfirst, hsecond, hthird, hzero3⟩
  fin_cases who
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2

/-! ## Existence and uniqueness of all Continue -/

/-- A Boolean marginal is determined by its Quit mass. -/
theorem pmfBool_eq_of_quitProbability_eq {first second : PMF Bool}
    (hquit : (first true).toReal = (second true).toReal) : first = second := by
  apply Math.ProbabilityMassFunction.toVector_injective
  funext value
  cases value
  · have hfirst := (Math.ProbabilityMassFunction.toVector_mem_stdSimplex first).2
    have hsecond := (Math.ProbabilityMassFunction.toVector_mem_stdSimplex second).2
    rw [Fintype.sum_bool] at hfirst hsecond
    have htrue : Math.ProbabilityMassFunction.toVector first true =
      Math.ProbabilityMassFunction.toVector second true := hquit
    linarith
  · exact hquit

/-- Every root is the product root of its own Quit rates. -/
theorem eq_productRoot (candidate : Player → PMF Bool)
    (hzeroRate : ∀ who, 0 ≤ (candidate who true).toReal)
    (honeRate : ∀ who, (candidate who true).toReal ≤ 1) :
    candidate =
      productRoot (fun who ↦ (candidate who true).toReal) hzeroRate honeRate := by
  funext who
  exact pmfBool_eq_of_quitProbability_eq (by simp [productRoot])

/-- **All Continue is an exact root Nash equilibrium at the solo cap.** -/
theorem quittingAllContinueRoot_isNash (R singletonLevel : ℝ) :
    IsεQuittingRootNash (sharpReward R singletonLevel)
      (sharpCapLimit singletonLevel) 0
      (quittingAllContinueRoot : Player → PMF Bool) := by
  apply quittingAllContinueRoot_isZeroNash_of_singleton_le
  intro who
  rw [sharpCapLimit_eq_solo R singletonLevel who]

/-- **All Continue is the only exact root against the solo cap**, at every `R`
and every singleton level.  This is uniqueness at that cap as a theorem about
`sharpReward`, not as an assumed hypothesis. -/
theorem eq_allContinueRoot_of_isNash (candidate : Player → PMF Bool)
    (hnash : IsεQuittingRootNash (sharpReward R singletonLevel)
      (sharpCapLimit singletonLevel) 0 candidate) :
    candidate = (quittingAllContinueRoot : Player → PMF Bool) := by
  have hzeroRate : ∀ who : Player, 0 ≤ (candidate who true).toReal :=
    fun _ ↦ ENNReal.toReal_nonneg
  have honeRate : ∀ who : Player, (candidate who true).toReal ≤ 1 := by
    intro who
    have hsum := quittingRoot_continueProbability_add_quitProbability candidate who
    have hcontinue : 0 ≤ (candidate who false).toReal := ENNReal.toReal_nonneg
    linarith
  have hproduct := eq_productRoot candidate hzeroRate honeRate
  rw [hproduct] at hnash ⊢
  funext who
  refine pmfBool_eq_of_quitProbability_eq ?_
  have hvanish := hazard_eq_zero_of_isNash hnash who
  simp [productRoot, quittingAllContinueRoot, hvanish]

/-- Consequently every exact root against the solo cap has zero total Quit
rate, so no exact root there is positive.  A `Regression`-style container for
`sharpReward` cannot satisfy a `limitRoot_positive` field against this cap. -/
theorem not_sum_quittingRootQuitRates_pos (candidate : Player → PMF Bool)
    (hnash : IsεQuittingRootNash (sharpReward R singletonLevel)
      (sharpCapLimit singletonLevel) 0 candidate) :
    ¬ 0 < ∑ who, quittingRootQuitRates candidate who := by
  rw [eq_allContinueRoot_of_isNash candidate hnash]
  simp [quittingRootQuitRates, quittingAllContinueRoot]

/-- **The exact root Nash equilibrium at the solo cap exists uniquely.** -/
theorem existsUnique_isQuittingRootNash (R singletonLevel : ℝ) :
    ∃! candidate : Player → PMF Bool,
      IsεQuittingRootNash (sharpReward R singletonLevel)
        (sharpCapLimit singletonLevel) 0 candidate := by
  refine ⟨quittingAllContinueRoot,
    quittingAllContinueRoot_isNash R singletonLevel, ?_⟩
  intro candidate hnash
  exact eq_allContinueRoot_of_isNash candidate hnash

end FinFourOwnerRiskyCapLimitRootUniqueness

end GameTheory
