/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.FinFourHopfConcreteChambers
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity

/-!
# Exact roots of the sharp four-player table at its solo cap

`GameTheory.FinFourHopfConcreteChambers.sharpReward R singletonLevel` is
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

This file stops there.  It does not decide which activity patterns are
feasible, so it does not establish that all Continue is the only exact root
against this cap.  `not_isεQuittingRootNash_soloOwnerRoot` excludes one
one-parameter family and nothing wider.  Nothing here concerns other tables,
other caps, or any ray.
-/

noncomputable section

namespace GameTheory

namespace FinFourSharpCapLimitRootUniqueness

open FinFourHopfConcreteChambers
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

end FinFourSharpCapLimitRootUniqueness

end GameTheory
