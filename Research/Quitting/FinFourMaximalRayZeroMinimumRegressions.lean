/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.MaximalRayZeroMinimumActiveRegression
import Research.Quitting.FinFourProducerAtlas.Source
import UniformEquilibrium.Quitting.Classification.Existence.SureExitChambers
import MathUE.SummableChargeSurvival
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Fin4 maximal-ray regressions fenced at zero minimum

This file gives the two spectator reward completions and the certificate
surface for checking an actual maximal-prefix ray.  Every regression stores
an actual `QuittingForwardExactCapTail`, its equality to the canonical
maximal root, the limiting all-Continue behavior, and a positive exact root
at the same limiting cap.  The zero-solo theorem then proves that none of
these certificates can be attached to a positive-minimum Fin4 source.

The structures below are regression checkers.  They do not manufacture the
infinite recurrence certificate from a positive-minimum atlas source.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct Set
open QuittingSureSetOwnerRepair

namespace FinFourMaximalRayZeroMinimumRegressions

abbrev Player := Fin 4

def interaction (who owner : Player) : ℝ :=
  ![![0, 1, -2, 0], ![1, 0, -2, 0],
    ![2 / 5, 2 / 5, 0, 0], ![0, 0, 0, 0]] who owner

def passive (who owner : Player) : ℝ := -interaction who owner / 2

def activeBaseReward
    (terminal : {S : Finset Player // S.Nonempty}) (who : Player) : ℝ :=
  (∑ owner ∈ terminal.val.erase who, passive who owner) +
    if who ∈ terminal.val then
      ∑ owner ∈ terminal.val.erase who, interaction who owner
    else 0

def pairCoalition : Finset Player := {0, 3}

def firstPaidCoalition : Finset Player := {0, 1, 3}

def secondPaidCoalition : Finset Player := {0, 2, 3}

/-- Rational spectator row `|T|` off the spectator and `|T|-1` after it
joins, with singleton value zero. -/
def rationalSpectatorReward (terminal : Finset Player) : ℝ :=
  if terminal = {3} then 0
  else if 3 ∈ terminal then ((terminal.erase 3).card : ℝ) - 1
  else terminal.card

/-- The rational completion, parameterized by its rational paid amount. -/
def rationalReward (d : ℝ)
    (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who ↦
    if who = 3 then rationalSpectatorReward terminal.val
    else if 3 ∈ terminal.val then
      if terminal.val = pairCoalition then
        if who = 0 then d else 0
      else if terminal.val = firstPaidCoalition ∧ who = 1 then d
      else if terminal.val = secondPaidCoalition ∧ who = 2 then d
      else 0
    else activeBaseReward terminal who

/-- Audited concrete rational scale. -/
def rationalScale : ℝ := 1 / 100

theorem rationalScale_pos : 0 < rationalScale := by
  norm_num [rationalScale]

theorem rationalReward_singleton_eq_zero (who : Player) :
    rationalReward rationalScale (quittingSingletonTerminal who) who = 0 := by
  fin_cases who <;>
    simp +decide [rationalReward, rationalSpectatorReward,
      activeBaseReward, passive, interaction, quittingSingletonTerminal]

/-- Spectator coefficients of the full-binding completion. -/
def fullBindingSpectatorCoefficient (R : ℝ) : Player → ℝ :=
  ![R, -R - 1, 0, 0]

def fullBindingSpectatorReward (R : ℝ) (terminal : Finset Player) : ℝ :=
  if terminal = {3} then 0
  else (∑ owner ∈ terminal.erase 3, fullBindingSpectatorCoefficient R owner) -
    if 3 ∈ terminal then 1 else 0

/-- Fixed-real full-binding completion.  Only the spectator row differs from
the rational table. -/
def fullBindingReward (R d : ℝ)
    (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who ↦
    if who = 3 then fullBindingSpectatorReward R terminal.val
    else rationalReward d terminal who

theorem fullBindingReward_singleton_eq_zero (R : ℝ) (who : Player) :
    fullBindingReward R rationalScale (quittingSingletonTerminal who) who = 0 := by
  fin_cases who <;>
    simp +decide [fullBindingReward, fullBindingSpectatorReward,
      rationalReward,
      activeBaseReward, passive, interaction, quittingSingletonTerminal]

def rayCap (a b spectator : ℝ) : Payoff Player :=
  ![a, a, b, spectator]

def activeSurvival (root : Player → PMF Bool) : ℝ :=
  (root 0 false).toReal * (root 1 false).toReal * (root 2 false).toReal

def activeAbsorption (root : Player → PMF Bool) : ℝ :=
  1 - activeSurvival root

def activePlayers : Finset Player := {0, 1, 2}

@[simp] theorem univ_erase_spectator :
    Finset.univ.erase (3 : Player) = activePlayers := by decide

@[simp] theorem activePlayers_sdiff_zero : activePlayers \ {0} = {1, 2} := by decide
@[simp] theorem activePlayers_sdiff_one : activePlayers \ {1} = {0, 2} := by decide
@[simp] theorem activePlayers_sdiff_two : activePlayers \ {2} = {0, 1} := by decide
@[simp] theorem activePlayers_sdiff_zero_one : activePlayers \ {0, 1} = {2} := by decide
@[simp] theorem activePlayers_sdiff_zero_two : activePlayers \ {0, 2} = {1} := by decide
@[simp] theorem activePlayers_sdiff_one_two : activePlayers \ {1, 2} = {0} := by decide
@[simp] theorem activePlayers_sdiff_all : activePlayers \ {0, 1, 2} = ∅ := by decide

@[simp] theorem one_two_sdiff_zero_one :
    ({1, 2} : Finset Player) \ {0, 1} = {2} := by decide
@[simp] theorem one_two_sdiff_zero_two :
    ({1, 2} : Finset Player) \ {0, 2} = {1} := by decide

@[simp] theorem literal_active_sdiff_zero :
    ({0, 1, 2} : Finset Player) \ {0} = {1, 2} := by decide
@[simp] theorem literal_active_sdiff_one :
    ({0, 1, 2} : Finset Player) \ {1} = {0, 2} := by decide
@[simp] theorem literal_active_sdiff_two :
    ({0, 1, 2} : Finset Player) \ {2} = {0, 1} := by decide

theorem activeSurvival_nonneg (root : Player → PMF Bool) :
    0 ≤ activeSurvival root := by
  unfold activeSurvival
  positivity

theorem activeSurvival_le_one (root : Player → PMF Bool) :
    activeSurvival root ≤ 1 := by
  have h0 := pmfBool_false_toReal (root 0)
  have h1 := pmfBool_false_toReal (root 1)
  have h2 := pmfBool_false_toReal (root 2)
  have h0n : 0 ≤ (root 0 true).toReal := ENNReal.toReal_nonneg
  have h1n : 0 ≤ (root 1 true).toReal := ENNReal.toReal_nonneg
  have h2n : 0 ≤ (root 2 true).toReal := ENNReal.toReal_nonneg
  have hf0 : 0 ≤ (root 0 false).toReal := ENNReal.toReal_nonneg
  have hf1 : 0 ≤ (root 1 false).toReal := ENNReal.toReal_nonneg
  have hf2 : 0 ≤ (root 2 false).toReal := ENNReal.toReal_nonneg
  have hf0le : (root 0 false).toReal ≤ 1 := by linarith
  have hf1le : (root 1 false).toReal ≤ 1 := by linarith
  have hf2le : (root 2 false).toReal ≤ 1 := by linarith
  have h01nonneg : 0 ≤ (root 0 false).toReal * (root 1 false).toReal :=
    mul_nonneg hf0 hf1
  have h01 : (root 0 false).toReal * (root 1 false).toReal ≤ 1 := by
    nlinarith [mul_nonneg h0n h1n]
  unfold activeSurvival
  have hdrop : (root 0 false).toReal * (root 1 false).toReal *
      (root 2 false).toReal ≤
        (root 0 false).toReal * (root 1 false).toReal := by
    nlinarith [mul_nonneg h01nonneg (sub_nonneg.mpr hf2le)]
  exact hdrop.trans h01

theorem rationalReward_spectator_endpointDifference
    (d a b spectator : ℝ) (root : Player → PMF Bool) :
    quittingRootEndpointDifference (rationalReward d) (rayCap a b spectator)
        root 3 =
      -activeAbsorption root - spectator * activeSurvival root := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  rw [show ((Finset.univ.erase (3 : Player)).powerset) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
  simp +decide [quittingOpponentCoalitionMass,
    quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    rationalReward, rationalSpectatorReward, rayCap,
    activeAbsorption, activeSurvival, activePlayers, pmfBool_false_toReal]
  ring

theorem fullBindingReward_spectator_endpointDifference
    (R d a b spectator : ℝ) (root : Player → PMF Bool) :
    quittingRootEndpointDifference (fullBindingReward R d)
        (rayCap a b spectator) root 3 =
      -activeAbsorption root - spectator * activeSurvival root := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  rw [show ((Finset.univ.erase (3 : Player)).powerset) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
  simp +decide [quittingOpponentCoalitionMass,
    quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    fullBindingReward, fullBindingSpectatorReward, rayCap,
    activeAbsorption, activeSurvival, activePlayers, pmfBool_false_toReal]
  ring

theorem spectator_endpointDifference_neg
    (root : Player → PMF Bool) {spectator : ℝ} (hspectator : 0 < spectator) :
    -activeAbsorption root - spectator * activeSurvival root < 0 := by
  unfold activeAbsorption
  have hsurvival0 := activeSurvival_nonneg root
  have hsurvival1 := activeSurvival_le_one root
  by_cases hzero : activeSurvival root = 0
  · rw [hzero]
    norm_num
  · have hpositive : 0 < activeSurvival root :=
      lt_of_le_of_ne hsurvival0 (Ne.symm hzero)
    nlinarith [mul_pos hspectator hpositive]

theorem rationalReward_spectator_quitRate_eq_zero_of_isZeroNash
    (d a b spectator : ℝ) (hspectator : 0 < spectator)
    (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash (rationalReward d) (rayCap a b spectator)
      0 root) :
    (root 3 true).toReal = 0 := by
  have hendpoint :=
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ root).2
      hnash) 3
  have hquit := hendpoint.2
  rw [rationalReward_spectator_endpointDifference] at hquit
  have hneg := spectator_endpointDifference_neg root hspectator
  have hrate : 0 ≤ (root 3 true).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem fullBindingReward_spectator_quitRate_eq_zero_of_isZeroNash
    (R d a b spectator : ℝ) (hspectator : 0 < spectator)
    (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash (fullBindingReward R d)
      (rayCap a b spectator) 0 root) :
    (root 3 true).toReal = 0 := by
  have hendpoint :=
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ root).2
      hnash) 3
  have hquit := hendpoint.2
  rw [fullBindingReward_spectator_endpointDifference] at hquit
  have hneg := spectator_endpointDifference_neg root hspectator
  have hrate : 0 ≤ (root 3 true).toReal := ENNReal.toReal_nonneg
  nlinarith

namespace LiftedActiveRoot

def hazard {a b : ℝ}
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b) :
    Player → ℝ := ![data.t, data.t, data.z, 0]

theorem hazard_nonneg {a b : ℝ}
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (who : Player) : 0 ≤ hazard data who := by
  fin_cases who <;>
    simp [hazard, (data.t_pos ha).le, data.z_pos.le]

theorem hazard_le_one {a b : ℝ}
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (who : Player) : hazard data who ≤ 1 := by
  have hz : data.z < 1 := data.z_lt_half.trans (by norm_num)
  fin_cases who <;>
    simp [hazard, (data.t_lt_one ha).le, hz.le]

def root {a b : ℝ}
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) : Player → PMF Bool :=
  rootOfHazard (hazard data) (hazard_nonneg data ha) (hazard_le_one data ha)

@[simp] theorem root_true {a b : ℝ}
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (who : Player) :
    (root data ha who true).toReal = hazard data who := by
  simp [root, rootOfHazard]

@[simp] theorem root_false {a b : ℝ}
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (who : Player) :
    (root data ha who false).toReal = 1 - hazard data who := by
  simp [root, rootOfHazard, pmfBool_false_toReal]

end LiftedActiveRoot

theorem rationalReward_liftedActive_endpointDifference
    (d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (who : Fin 3) :
    quittingRootEndpointDifference (rationalReward d) (rayCap a b spectator)
        (LiftedActiveRoot.root data ha) who.castSucc =
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
        data.hazard who := by
  fin_cases who
  · change quittingRootEndpointDifference (rationalReward d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 0 =
        MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
          data.hazard 0
    rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
    rw [show ((Finset.univ.erase (0 : Player)).powerset) =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      rationalReward, activeBaseReward, passive, interaction, rayCap,
      LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.cap,
      MaximalRayZeroMinimumActiveRegression.interaction,
      MaximalRayZeroMinimumActiveRegression.FullRootData.hazard,
      Fin.sum_univ_three, pmfBool_false_toReal,
      show (Finset.univ.erase (0 : Player)) = {1, 2, 3} by decide,
      show ({1, 2, 3} : Finset Player) \ {1} = {2, 3} by decide,
      show ({1, 2, 3} : Finset Player) \ {1, 2} = {3} by decide,
      show ({1, 2, 3} : Finset Player) \ {2} = {1, 3} by decide,
      show (Finset.univ.erase (0 : Fin 3)) = {1, 2} by decide]
    ring
  · change quittingRootEndpointDifference (rationalReward d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 1 =
        MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
          data.hazard 1
    rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
    rw [show ((Finset.univ.erase (1 : Player)).powerset) =
      {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      rationalReward, activeBaseReward, passive, interaction, rayCap,
      LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.cap,
      MaximalRayZeroMinimumActiveRegression.interaction,
      MaximalRayZeroMinimumActiveRegression.FullRootData.hazard,
      Fin.sum_univ_three, pmfBool_false_toReal,
      show (Finset.univ.erase (1 : Player)) = {0, 2, 3} by decide,
      show ({0, 2, 3} : Finset Player) \ {0} = {2, 3} by decide,
      show ({0, 2, 3} : Finset Player) \ {0, 2} = {3} by decide,
      show ({0, 2, 3} : Finset Player) \ {2} = {0, 3} by decide,
      show (Finset.univ.erase (1 : Fin 3)) = {0, 2} by decide]
    ring
  · change quittingRootEndpointDifference (rationalReward d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 2 =
        MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
          data.hazard 2
    rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
    rw [show ((Finset.univ.erase (2 : Player)).powerset) =
      {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      rationalReward, activeBaseReward, passive, interaction, rayCap,
      LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.cap,
      MaximalRayZeroMinimumActiveRegression.interaction,
      MaximalRayZeroMinimumActiveRegression.FullRootData.hazard,
      Fin.sum_univ_three, pmfBool_false_toReal,
      show (Finset.univ.erase (2 : Player)) = {0, 1, 3} by decide,
      show ({0, 1, 3} : Finset Player) \ {0} = {1, 3} by decide,
      show ({0, 1, 3} : Finset Player) \ {1} = {0, 3} by decide,
      show ({0, 1, 3} : Finset Player) \ {0, 1} = {3} by decide,
      show (Finset.univ.erase (2 : Fin 3)) = {0, 1} by decide]
    ring

theorem fullBindingReward_active_endpointDifference_eq_rational
    (R d : ℝ) (tail : Payoff Player) (root : Player → PMF Bool)
    (who : Player) (hwho : who ≠ 3) :
    quittingRootEndpointDifference (fullBindingReward R d) tail root who =
      quittingRootEndpointDifference (rationalReward d) tail root who := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle,
    quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  apply Finset.sum_congr rfl
  intro coalition _
  congr 1
  have hinsert : (insert who coalition).Nonempty := Finset.insert_nonempty _ _
  by_cases hcoalition : coalition.Nonempty <;>
    simp [quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      fullBindingReward, hwho, hinsert, hcoalition]

theorem fullBindingReward_liftedActive_endpointDifference
    (R d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (who : Fin 3) :
    quittingRootEndpointDifference (fullBindingReward R d)
        (rayCap a b spectator) (LiftedActiveRoot.root data ha) who.castSucc =
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
        data.hazard who := by
  rw [fullBindingReward_active_endpointDifference_eq_rational _ _ _ _ _
    (by fin_cases who <;> decide)]
  exact rationalReward_liftedActive_endpointDifference d a b spectator data ha who

namespace LiftedActiveRoot

theorem rationalReward_active_endpoint_eq_zero
    (d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (who : Player) (hwho : who ≠ 3) :
    quittingRootEndpointDifference (rationalReward d) (rayCap a b spectator)
        (root data ha) who = 0 := by
  have hactive : who = 0 ∨ who = 1 ∨ who = 2 := by
    fin_cases who <;> simp_all
  rcases hactive with rfl | rfl | rfl
  · simpa using (rationalReward_liftedActive_endpointDifference d a b spectator
      data ha (0 : Fin 3)).trans (data.endpointPolynomial_eq_zero ha 0)
  · simpa using (rationalReward_liftedActive_endpointDifference d a b spectator
      data ha (1 : Fin 3)).trans (data.endpointPolynomial_eq_zero ha 1)
  · simpa using (rationalReward_liftedActive_endpointDifference d a b spectator
      data ha (2 : Fin 3)).trans (data.endpointPolynomial_eq_zero ha 2)

theorem fullBindingReward_active_endpoint_eq_zero
    (R d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (who : Player) (hwho : who ≠ 3) :
    quittingRootEndpointDifference (fullBindingReward R d)
        (rayCap a b spectator) (root data ha) who = 0 := by
  have hactive : who = 0 ∨ who = 1 ∨ who = 2 := by
    fin_cases who <;> simp_all
  rcases hactive with rfl | rfl | rfl
  · simpa using (fullBindingReward_liftedActive_endpointDifference R d a b
      spectator data ha (0 : Fin 3)).trans (data.endpointPolynomial_eq_zero ha 0)
  · simpa using (fullBindingReward_liftedActive_endpointDifference R d a b
      spectator data ha (1 : Fin 3)).trans (data.endpointPolynomial_eq_zero ha 1)
  · simpa using (fullBindingReward_liftedActive_endpointDifference R d a b
      spectator data ha (2 : Fin 3)).trans (data.endpointPolynomial_eq_zero ha 2)

theorem rationalReward_exactNash
    (d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (hspectator : 0 < spectator) :
    IsεQuittingRootNash (rationalReward d) (rayCap a b spectator) 0
      (root data ha) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  by_cases hwho : who = 3
  · subst who
    rw [rationalReward_spectator_endpointDifference]
    have hneg := spectator_endpointDifference_neg (root data ha) hspectator
    constructor
    · exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hneg.le
    · simp [root, hazard, rootOfHazard]
  · rw [rationalReward_active_endpoint_eq_zero d a b spectator data ha who hwho]
    simp

theorem fullBindingReward_exactNash
    (R d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (hspectator : 0 < spectator) :
    IsεQuittingRootNash (fullBindingReward R d) (rayCap a b spectator) 0
      (root data ha) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  by_cases hwho : who = 3
  · subst who
    rw [fullBindingReward_spectator_endpointDifference]
    have hneg := spectator_endpointDifference_neg (root data ha) hspectator
    constructor
    · exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hneg.le
    · simp [root, hazard, rootOfHazard]
  · rw [fullBindingReward_active_endpoint_eq_zero R d a b spectator data ha
      who hwho]
    simp

end LiftedActiveRoot

def activeRestriction (root : Player → PMF Bool) : Fin 3 → PMF Bool :=
  fun who ↦ root who.castSucc

theorem rationalReward_activeRestriction_endpointDifference
    (d a b spectator : ℝ) (root : Player → PMF Bool)
    (hspectator : (root 3 true).toReal = 0) (who : Fin 3) :
    quittingRootEndpointDifference (rationalReward d) (rayCap a b spectator)
        root who.castSucc =
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
        (hazardOfRoot (activeRestriction root)) who := by
  fin_cases who
  · change quittingRootEndpointDifference (rationalReward d)
      (rayCap a b spectator) root 0 =
        MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
          (hazardOfRoot (activeRestriction root)) 0
    rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
    rw [show ((Finset.univ.erase (0 : Player)).powerset) =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      rationalReward, activeBaseReward, passive, interaction, rayCap,
      activeRestriction, hazardOfRoot,
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.cap,
      MaximalRayZeroMinimumActiveRegression.interaction,
      Fin.sum_univ_three, pmfBool_false_toReal, hspectator,
      show (Finset.univ.erase (0 : Player)) = {1, 2, 3} by decide,
      show ({1, 2, 3} : Finset Player) \ {1} = {2, 3} by decide,
      show ({1, 2, 3} : Finset Player) \ {1, 2} = {3} by decide,
      show ({1, 2, 3} : Finset Player) \ {2} = {1, 3} by decide,
      show (Finset.univ.erase (0 : Fin 3)) = {1, 2} by decide]
    ring
  · change quittingRootEndpointDifference (rationalReward d)
      (rayCap a b spectator) root 1 =
        MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
          (hazardOfRoot (activeRestriction root)) 1
    rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
    rw [show ((Finset.univ.erase (1 : Player)).powerset) =
      {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      rationalReward, activeBaseReward, passive, interaction, rayCap,
      activeRestriction, hazardOfRoot,
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.cap,
      MaximalRayZeroMinimumActiveRegression.interaction,
      Fin.sum_univ_three, pmfBool_false_toReal, hspectator,
      show (Finset.univ.erase (1 : Player)) = {0, 2, 3} by decide,
      show ({0, 2, 3} : Finset Player) \ {0} = {2, 3} by decide,
      show ({0, 2, 3} : Finset Player) \ {0, 2} = {3} by decide,
      show ({0, 2, 3} : Finset Player) \ {2} = {0, 3} by decide,
      show (Finset.univ.erase (1 : Fin 3)) = {0, 2} by decide]
    ring
  · change quittingRootEndpointDifference (rationalReward d)
      (rayCap a b spectator) root 2 =
        MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
          (hazardOfRoot (activeRestriction root)) 2
    rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
    rw [show ((Finset.univ.erase (2 : Player)).powerset) =
      {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      rationalReward, activeBaseReward, passive, interaction, rayCap,
      activeRestriction, hazardOfRoot,
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.cap,
      MaximalRayZeroMinimumActiveRegression.interaction,
      Fin.sum_univ_three, pmfBool_false_toReal, hspectator,
      show (Finset.univ.erase (2 : Player)) = {0, 1, 3} by decide,
      show ({0, 1, 3} : Finset Player) \ {0} = {1, 3} by decide,
      show ({0, 1, 3} : Finset Player) \ {1} = {0, 3} by decide,
      show ({0, 1, 3} : Finset Player) \ {0, 1} = {3} by decide,
      show (Finset.univ.erase (2 : Fin 3)) = {0, 1} by decide]
    ring

theorem fullBindingReward_activeRestriction_endpointDifference
    (R d a b spectator : ℝ) (root : Player → PMF Bool)
    (hspectator : (root 3 true).toReal = 0) (who : Fin 3) :
    quittingRootEndpointDifference (fullBindingReward R d)
        (rayCap a b spectator) root who.castSucc =
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
        (hazardOfRoot (activeRestriction root)) who := by
  rw [fullBindingReward_active_endpointDifference_eq_rational _ _ _ _ _
    (by fin_cases who <;> decide)]
  exact rationalReward_activeRestriction_endpointDifference d a b spectator root
    hspectator who

theorem activeRestriction_endpointDifference
    (a b : ℝ) (root : Player → PMF Bool) (who : Fin 3) :
    quittingRootEndpointDifference MaximalRayZeroMinimumActiveRegression.reward
        (MaximalRayZeroMinimumActiveRegression.cap a b)
        (activeRestriction root) who =
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b
        (hazardOfRoot (activeRestriction root)) who := by
  let hazard := hazardOfRoot (activeRestriction root)
  let rebuilt := MaximalRayZeroMinimumActiveRegression.root hazard
    (hazardOfRoot_nonneg _) (hazardOfRoot_le_one _)
  have hrebuilt : rebuilt = activeRestriction root := by
    calc
      rebuilt = rootOfHazard hazard (hazardOfRoot_nonneg _)
          (hazardOfRoot_le_one _) := rfl
      _ = activeRestriction root := rootOfHazard_hazardOfRoot _
  calc
    quittingRootEndpointDifference MaximalRayZeroMinimumActiveRegression.reward
        (MaximalRayZeroMinimumActiveRegression.cap a b)
        (activeRestriction root) who =
      quittingRootEndpointDifference MaximalRayZeroMinimumActiveRegression.reward
        (MaximalRayZeroMinimumActiveRegression.cap a b) rebuilt who := by
          rw [hrebuilt]
    _ = MaximalRayZeroMinimumActiveRegression.endpointPolynomial a b hazard who := by
      simpa [rebuilt] using
        MaximalRayZeroMinimumActiveRegression.endpointDifference_eq_endpointPolynomial
          a b hazard (hazardOfRoot_nonneg _) (hazardOfRoot_le_one _) who
    _ = _ := rfl

theorem activeRestriction_exactNash_of_rationalReward
    (d a b spectator : ℝ) (root : Player → PMF Bool)
    (hspectator : (root 3 true).toReal = 0)
    (hnash : IsεQuittingRootNash (rationalReward d) (rayCap a b spectator)
      0 root) :
    IsεQuittingRootNash MaximalRayZeroMinimumActiveRegression.reward
      (MaximalRayZeroMinimumActiveRegression.cap a b) 0
        (activeRestriction root) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ root).2 hnash
  intro who
  simpa [activeRestriction,
    activeRestriction_endpointDifference a b root who,
    rationalReward_activeRestriction_endpointDifference d a b spectator root
      hspectator who] using hendpoint who.castSucc

theorem activeRestriction_exactNash_of_fullBindingReward
    (R d a b spectator : ℝ) (root : Player → PMF Bool)
    (hspectator : (root 3 true).toReal = 0)
    (hnash : IsεQuittingRootNash (fullBindingReward R d)
      (rayCap a b spectator) 0 root) :
    IsεQuittingRootNash MaximalRayZeroMinimumActiveRegression.reward
      (MaximalRayZeroMinimumActiveRegression.cap a b) 0
        (activeRestriction root) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ root).2 hnash
  intro who
  simpa [activeRestriction,
    activeRestriction_endpointDifference a b root who,
    fullBindingReward_activeRestriction_endpointDifference R d a b spectator root
      hspectator who] using hendpoint who.castSucc

theorem quittingRootAbsorptionMass_eq_activeRestriction_of_spectator_zero
    (root : Player → PMF Bool) (hspectator : (root 3 true).toReal = 0) :
    quittingRootAbsorptionMass root =
      quittingRootAbsorptionMass (activeRestriction root) := by
  rw [quittingRootAbsorptionMass, quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_four, Fin.prod_univ_three]
  simp [activeRestriction, pmfBool_false_toReal, hspectator]

theorem LiftedActiveRoot.activeRestriction_root_eq_productRoot
    {a b : ℝ}
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) :
    activeRestriction (LiftedActiveRoot.root data ha) = data.productRoot ha := by
  funext who
  fin_cases who <;> apply PMF.ext <;> intro action <;> cases action <;>
    simp [activeRestriction, LiftedActiveRoot.root, LiftedActiveRoot.hazard,
      MaximalRayZeroMinimumActiveRegression.FullRootData.productRoot,
      MaximalRayZeroMinimumActiveRegression.FullRootData.hazard,
      MaximalRayZeroMinimumActiveRegression.root, rootOfHazard]

theorem eq_liftedActiveRoot_of_activeRestriction_eq
    {a b : ℝ}
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (root : Player → PMF Bool)
    (hspectator : (root 3 true).toReal = 0)
    (hactive : activeRestriction root = data.productRoot ha) :
    root = LiftedActiveRoot.root data ha := by
  funext who
  by_cases hwho : who = 3
  · subst who
    rw [eq_pure_false_of_true_toReal_eq_zero (root 3) hspectator,
      eq_pure_false_of_true_toReal_eq_zero
        (LiftedActiveRoot.root data ha 3)]
    simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard]
  · have hactiveWho : who = 0 ∨ who = 1 ∨ who = 2 := by
      fin_cases who <;> simp_all
    rcases hactiveWho with rfl | rfl | rfl
    · simpa [activeRestriction] using congrFun
        (hactive.trans
          (LiftedActiveRoot.activeRestriction_root_eq_productRoot data ha).symm)
          (0 : Fin 3)
    · simpa [activeRestriction] using congrFun
        (hactive.trans
          (LiftedActiveRoot.activeRestriction_root_eq_productRoot data ha).symm)
          (1 : Fin 3)
    · simpa [activeRestriction] using congrFun
        (hactive.trans
          (LiftedActiveRoot.activeRestriction_root_eq_productRoot data ha).symm)
          (2 : Fin 3)

theorem rationalReward_eq_liftedActiveRoot_of_absorption_ge
    (d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (hb : 0 < b) (hspectator : 0 < spectator)
    (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash (rationalReward d) (rayCap a b spectator)
      0 root)
    (hge : quittingRootAbsorptionMass (LiftedActiveRoot.root data ha) ≤
      quittingRootAbsorptionMass root) :
    root = LiftedActiveRoot.root data ha := by
  have hrootSpectator :=
    rationalReward_spectator_quitRate_eq_zero_of_isZeroNash d a b spectator
      hspectator root hnash
  have hliftSpectator :
      ((LiftedActiveRoot.root data ha 3) true).toReal = 0 := by
    simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard]
  have hactiveNash := activeRestriction_exactNash_of_rationalReward
    d a b spectator root hrootSpectator hnash
  have hactiveGe :
      quittingRootAbsorptionMass (data.productRoot ha) ≤
        quittingRootAbsorptionMass (activeRestriction root) := by
    rw [← LiftedActiveRoot.activeRestriction_root_eq_productRoot data ha,
      ← quittingRootAbsorptionMass_eq_activeRestriction_of_spectator_zero
        (LiftedActiveRoot.root data ha) hliftSpectator,
      ← quittingRootAbsorptionMass_eq_activeRestriction_of_spectator_zero
        root hrootSpectator]
    exact hge
  have hactiveEq := data.eq_productRoot_of_absorption_ge ha hb
    (activeRestriction root) hactiveNash hactiveGe
  exact eq_liftedActiveRoot_of_activeRestriction_eq data ha root
    hrootSpectator hactiveEq

theorem fullBindingReward_eq_liftedActiveRoot_of_absorption_ge
    (R d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (hb : 0 < b) (hspectator : 0 < spectator)
    (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash (fullBindingReward R d)
      (rayCap a b spectator) 0 root)
    (hge : quittingRootAbsorptionMass (LiftedActiveRoot.root data ha) ≤
      quittingRootAbsorptionMass root) :
    root = LiftedActiveRoot.root data ha := by
  have hrootSpectator :=
    fullBindingReward_spectator_quitRate_eq_zero_of_isZeroNash R d a b spectator
      hspectator root hnash
  have hliftSpectator :
      ((LiftedActiveRoot.root data ha 3) true).toReal = 0 := by
    simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard]
  have hactiveNash := activeRestriction_exactNash_of_fullBindingReward
    R d a b spectator root hrootSpectator hnash
  have hactiveGe :
      quittingRootAbsorptionMass (data.productRoot ha) ≤
        quittingRootAbsorptionMass (activeRestriction root) := by
    rw [← LiftedActiveRoot.activeRestriction_root_eq_productRoot data ha,
      ← quittingRootAbsorptionMass_eq_activeRestriction_of_spectator_zero
        (LiftedActiveRoot.root data ha) hliftSpectator,
      ← quittingRootAbsorptionMass_eq_activeRestriction_of_spectator_zero
        root hrootSpectator]
    exact hge
  have hactiveEq := data.eq_productRoot_of_absorption_ge ha hb
    (activeRestriction root) hactiveNash hactiveGe
  exact eq_liftedActiveRoot_of_activeRestriction_eq data ha root
    hrootSpectator hactiveEq

theorem rationalReward_maximalAbsorptionCapRoot_eq_liftedActiveRoot
    (d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (hb : 0 < b) (hspectator : 0 < spectator) :
    quittingMaximalAbsorptionCapRoot (rationalReward d) (rayCap a b spectator) =
      LiftedActiveRoot.root data ha := by
  let selected := quittingMaximalAbsorptionCapRoot (rationalReward d)
    (rayCap a b spectator)
  have hnash : IsεQuittingRootNash (rationalReward d) (rayCap a b spectator)
      0 selected := quittingMaximalAbsorptionCapRoot_exactNash _ _
  have hge := quittingMaximalAbsorptionCapRoot_maximal
    (rationalReward d) (rayCap a b spectator)
      (LiftedActiveRoot.root data ha)
        (LiftedActiveRoot.rationalReward_exactNash d a b spectator data ha
          hspectator)
  exact rationalReward_eq_liftedActiveRoot_of_absorption_ge d a b spectator data
    ha hb hspectator selected hnash hge

theorem fullBindingReward_maximalAbsorptionCapRoot_eq_liftedActiveRoot
    (R d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (hb : 0 < b) (hspectator : 0 < spectator) :
    quittingMaximalAbsorptionCapRoot (fullBindingReward R d)
        (rayCap a b spectator) = LiftedActiveRoot.root data ha := by
  let selected := quittingMaximalAbsorptionCapRoot (fullBindingReward R d)
    (rayCap a b spectator)
  have hnash : IsεQuittingRootNash (fullBindingReward R d)
      (rayCap a b spectator) 0 selected :=
    quittingMaximalAbsorptionCapRoot_exactNash _ _
  have hge := quittingMaximalAbsorptionCapRoot_maximal
    (fullBindingReward R d) (rayCap a b spectator)
      (LiftedActiveRoot.root data ha)
        (LiftedActiveRoot.fullBindingReward_exactNash R d a b spectator data ha
          hspectator)
  exact fullBindingReward_eq_liftedActiveRoot_of_absorption_ge R d a b spectator
    data ha hb hspectator selected hnash hge

theorem fullBindingReward_active_successorPayoff_eq_rational
    (R d : ℝ) (tail : Payoff Player) (root : Player → PMF Bool)
    (who : Player) (hwho : who ≠ 3) :
    quittingRootSuccessorPayoff (fullBindingReward R d) tail root who =
      quittingRootSuccessorPayoff (rationalReward d) tail root who := by
  rw [quittingRootSuccessorPayoff, quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_sum_coalitionMass,
    quittingRootExpectedPayoff_eq_sum_coalitionMass]
  apply Finset.sum_congr rfl
  intro coalition _
  congr 1
  by_cases hcoalition : coalition.Nonempty <;>
    simp [quittingStageCoalitionPayoff, fullBindingReward, hwho, hcoalition]

theorem LiftedActiveRoot.rationalReward_successorPayoff
    (d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (hspectator : 0 < spectator) :
    quittingRootSuccessorPayoff (rationalReward d) (rayCap a b spectator)
        (LiftedActiveRoot.root data ha) =
      rayCap ((1 / 2 : ℝ) * a * (1 - data.t) * (1 - data.z))
        ((1 / 2 : ℝ) * b * (1 - data.t) ^ 2)
        (2 * data.t + data.z +
          (1 - data.t) ^ 2 * (1 - data.z) * spectator) := by
  have hnash := LiftedActiveRoot.rationalReward_exactNash
    d a b spectator data ha hspectator
  funext who
  fin_cases who
  · change quittingRootSuccessorPayoff (rationalReward d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 0 =
        (1 / 2 : ℝ) * a * (1 - data.t) * (1 - data.z)
    have hendpoint :=
      LiftedActiveRoot.rationalReward_active_endpoint_eq_zero
        d a b spectator data ha 0 (by decide)
    have hsame : quittingRootQuitPayoff (rationalReward d)
        (rayCap a b spectator) (LiftedActiveRoot.root data ha) 0 =
      quittingRootContinuePayoff (rationalReward d)
        (rayCap a b spectator) (LiftedActiveRoot.root data ha) 0 :=
      sub_eq_zero.mp hendpoint
    rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash _ _ _ _ hnash,
      hsame, max_self,
      quittingRootContinuePayoff_eq_sum_opponentCoalitionMass]
    rw [show ((Finset.univ.erase (0 : Player)).powerset) =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingStageCoalitionPayoff, rationalReward, activeBaseReward,
      passive, interaction, rayCap, LiftedActiveRoot.root,
      LiftedActiveRoot.hazard, rootOfHazard, pmfBool_false_toReal,
      show (Finset.univ.erase (0 : Player)) = {1, 2, 3} by decide,
      show ({1, 2, 3} : Finset Player) \ {1} = {2, 3} by decide,
      show ({1, 2, 3} : Finset Player) \ {1, 2} = {3} by decide,
      show ({1, 2, 3} : Finset Player) \ {2} = {1, 3} by decide]
    have hpoly := data.endpointPolynomial_eq_zero ha (0 : Fin 3)
    simp [MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.FullRootData.hazard,
      MaximalRayZeroMinimumActiveRegression.cap,
      MaximalRayZeroMinimumActiveRegression.interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (0 : Fin 3)) = {1, 2} by decide] at hpoly
    ring_nf at hpoly ⊢
    linear_combination (-1 / 2) * hpoly
  · change quittingRootSuccessorPayoff (rationalReward d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 1 =
        (1 / 2 : ℝ) * a * (1 - data.t) * (1 - data.z)
    have hendpoint :=
      LiftedActiveRoot.rationalReward_active_endpoint_eq_zero
        d a b spectator data ha 1 (by decide)
    have hsame : quittingRootQuitPayoff (rationalReward d)
        (rayCap a b spectator) (LiftedActiveRoot.root data ha) 1 =
      quittingRootContinuePayoff (rationalReward d)
        (rayCap a b spectator) (LiftedActiveRoot.root data ha) 1 :=
      sub_eq_zero.mp hendpoint
    rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash _ _ _ _ hnash,
      hsame, max_self,
      quittingRootContinuePayoff_eq_sum_opponentCoalitionMass]
    rw [show ((Finset.univ.erase (1 : Player)).powerset) =
      {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingStageCoalitionPayoff, rationalReward, activeBaseReward,
      passive, interaction, rayCap, LiftedActiveRoot.root,
      LiftedActiveRoot.hazard, rootOfHazard, pmfBool_false_toReal,
      show (Finset.univ.erase (1 : Player)) = {0, 2, 3} by decide,
      show ({0, 2, 3} : Finset Player) \ {0} = {2, 3} by decide,
      show ({0, 2, 3} : Finset Player) \ {0, 2} = {3} by decide,
      show ({0, 2, 3} : Finset Player) \ {2} = {0, 3} by decide]
    have hpoly := data.endpointPolynomial_eq_zero ha (1 : Fin 3)
    simp [MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.FullRootData.hazard,
      MaximalRayZeroMinimumActiveRegression.cap,
      MaximalRayZeroMinimumActiveRegression.interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (1 : Fin 3)) = {0, 2} by decide] at hpoly
    ring_nf at hpoly ⊢
    linear_combination (-1 / 2) * hpoly
  · change quittingRootSuccessorPayoff (rationalReward d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 2 =
        (1 / 2 : ℝ) * b * (1 - data.t) ^ 2
    have hendpoint :=
      LiftedActiveRoot.rationalReward_active_endpoint_eq_zero
        d a b spectator data ha 2 (by decide)
    have hsame : quittingRootQuitPayoff (rationalReward d)
        (rayCap a b spectator) (LiftedActiveRoot.root data ha) 2 =
      quittingRootContinuePayoff (rationalReward d)
        (rayCap a b spectator) (LiftedActiveRoot.root data ha) 2 :=
      sub_eq_zero.mp hendpoint
    rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash _ _ _ _ hnash,
      hsame, max_self,
      quittingRootContinuePayoff_eq_sum_opponentCoalitionMass]
    rw [show ((Finset.univ.erase (2 : Player)).powerset) =
      {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingStageCoalitionPayoff, rationalReward, activeBaseReward,
      passive, interaction, rayCap, LiftedActiveRoot.root,
      LiftedActiveRoot.hazard, rootOfHazard, pmfBool_false_toReal,
      show (Finset.univ.erase (2 : Player)) = {0, 1, 3} by decide,
      show ({0, 1, 3} : Finset Player) \ {0} = {1, 3} by decide,
      show ({0, 1, 3} : Finset Player) \ {1} = {0, 3} by decide,
      show ({0, 1, 3} : Finset Player) \ {0, 1} = {3} by decide]
    have hpoly := data.endpointPolynomial_eq_zero ha (2 : Fin 3)
    simp [MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.FullRootData.hazard,
      MaximalRayZeroMinimumActiveRegression.cap,
      MaximalRayZeroMinimumActiveRegression.interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (2 : Fin 3)) = {0, 1} by decide] at hpoly
    ring_nf at hpoly ⊢
    linear_combination (-1 / 2) * hpoly
  · change quittingRootSuccessorPayoff (rationalReward d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 3 =
        2 * data.t + data.z +
          (1 - data.t) ^ 2 * (1 - data.z) * spectator
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard]
    rw [quittingRootContinuePayoff_eq_sum_opponentCoalitionMass]
    rw [show ((Finset.univ.erase (3 : Player)).powerset) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingStageCoalitionPayoff, rationalReward, rationalSpectatorReward,
      rayCap, rootOfHazard, pmfBool_false_toReal, activePlayers]
    ring

theorem LiftedActiveRoot.fullBindingReward_successorPayoff
    (R d a b spectator : ℝ)
    (data : MaximalRayZeroMinimumActiveRegression.FullRootData a b)
    (ha : 0 < a) (hspectator : 0 < spectator) :
    quittingRootSuccessorPayoff (fullBindingReward R d) (rayCap a b spectator)
        (LiftedActiveRoot.root data ha) =
      rayCap ((1 / 2 : ℝ) * a * (1 - data.t) * (1 - data.z))
        ((1 / 2 : ℝ) * b * (1 - data.t) ^ 2)
        ((1 - data.t) ^ 2 * (1 - data.z) * spectator - data.t) := by
  funext who
  fin_cases who
  · change quittingRootSuccessorPayoff (fullBindingReward R d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 0 =
        (1 / 2 : ℝ) * a * (1 - data.t) * (1 - data.z)
    rw [fullBindingReward_active_successorPayoff_eq_rational _ _ _ _ _
      (by decide)]
    simpa [rayCap] using congrFun
      (LiftedActiveRoot.rationalReward_successorPayoff d a b spectator data ha
        hspectator) 0
  · change quittingRootSuccessorPayoff (fullBindingReward R d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 1 =
        (1 / 2 : ℝ) * a * (1 - data.t) * (1 - data.z)
    rw [fullBindingReward_active_successorPayoff_eq_rational _ _ _ _ _
      (by decide)]
    simpa [rayCap] using congrFun
      (LiftedActiveRoot.rationalReward_successorPayoff d a b spectator data ha
        hspectator) 1
  · change quittingRootSuccessorPayoff (fullBindingReward R d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 2 =
        (1 / 2 : ℝ) * b * (1 - data.t) ^ 2
    rw [fullBindingReward_active_successorPayoff_eq_rational _ _ _ _ _
      (by decide)]
    simpa [rayCap] using congrFun
      (LiftedActiveRoot.rationalReward_successorPayoff d a b spectator data ha
        hspectator) 2
  · change quittingRootSuccessorPayoff (fullBindingReward R d)
      (rayCap a b spectator) (LiftedActiveRoot.root data ha) 3 =
        (1 - data.t) ^ 2 * (1 - data.z) * spectator - data.t
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard]
    rw [quittingRootContinuePayoff_eq_sum_opponentCoalitionMass]
    rw [show ((Finset.univ.erase (3 : Player)).powerset) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingStageCoalitionPayoff, fullBindingReward,
      fullBindingSpectatorReward, fullBindingSpectatorCoefficient, rayCap,
      rootOfHazard, pmfBool_false_toReal, activePlayers]
    ring

/-- Literal local singleton-to-pair attachment.  Both profiles use one common
post-date continuation, so the tail agreement is definitional. -/
structure LocalForcedPairFragment
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) where
  continuation : (quittingGame reward).BehaviorProfile
  singletonOwner : Player
  markedOwner : Player
  payer : Player
  packetOwner : Player
  singletonOwner_eq_packetOwner : singletonOwner = packetOwner
  packetOwner_ne_markedOwner : packetOwner ≠ markedOwner
  payer_ne_markedOwner : payer ≠ markedOwner
  payer_ne_packetOwner : payer ≠ packetOwner
  singletonProfile : (quittingGame reward).BehaviorProfile
  pairProfile : (quittingGame reward).BehaviorProfile
  singletonProfile_eq : singletonProfile =
    quittingRootThenContinuationProfile reward
      (quittingPureSetRoot {singletonOwner}) continuation
  pairProfile_eq : pairProfile =
    quittingRootThenContinuationProfile reward
      (quittingPureSetRoot {markedOwner, packetOwner}) continuation
  marked_gain : 0 <
    reward ⟨{markedOwner, packetOwner}, by simp⟩ markedOwner -
      reward (quittingSingletonTerminal singletonOwner) markedOwner
  marked_pair_debt_eq_zero :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward pairProfile) markedOwner = 0
  payer_gain : 0 <
    reward ⟨{markedOwner, packetOwner, payer}, by simp⟩ payer -
      reward ⟨{markedOwner, packetOwner}, by simp⟩ payer

/-- The rational table has the literal paid pair fragment at scale `1/100`.
The marked owner is `0`, packet owner `3`, and payer `1`. -/
def rationalLocalForcedPairFragment :
    LocalForcedPairFragment (rationalReward rationalScale) where
  continuation := quittingAlwaysContinueProfile _
  singletonOwner := 3
  markedOwner := 0
  payer := 1
  packetOwner := 3
  singletonOwner_eq_packetOwner := rfl
  packetOwner_ne_markedOwner := by decide
  payer_ne_markedOwner := by decide
  payer_ne_packetOwner := by decide
  singletonProfile := quittingRootThenContinuationProfile _
    (quittingPureSetRoot {3}) (quittingAlwaysContinueProfile _)
  pairProfile := quittingRootThenContinuationProfile _
    (quittingPureSetRoot {0, 3}) (quittingAlwaysContinueProfile _)
  singletonProfile_eq := rfl
  pairProfile_eq := rfl
  marked_gain := by
    simp +decide [rationalReward, rationalScale]
  marked_pair_debt_eq_zero := by
    rw [quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      _ {0, 3} (by decide)]
    simp +decide [quittingTerminalSemanticDebt, quittingSetReward,
      rationalReward, rationalScale]
  payer_gain := by
    simp +decide [rationalReward, rationalScale]

/-- The full-binding completion keeps exactly the same active local pair
fragment. -/
def fullBindingLocalForcedPairFragment (R : ℝ) :
    LocalForcedPairFragment (fullBindingReward R rationalScale) where
  continuation := quittingAlwaysContinueProfile _
  singletonOwner := 3
  markedOwner := 0
  payer := 1
  packetOwner := 3
  singletonOwner_eq_packetOwner := rfl
  packetOwner_ne_markedOwner := by decide
  payer_ne_markedOwner := by decide
  payer_ne_packetOwner := by decide
  singletonProfile := quittingRootThenContinuationProfile _
    (quittingPureSetRoot {3}) (quittingAlwaysContinueProfile _)
  pairProfile := quittingRootThenContinuationProfile _
    (quittingPureSetRoot {0, 3}) (quittingAlwaysContinueProfile _)
  singletonProfile_eq := rfl
  pairProfile_eq := rfl
  marked_gain := by
    simp +decide [fullBindingReward, rationalReward, rationalScale]
  marked_pair_debt_eq_zero := by
    rw [quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      _ {0, 3} (by decide)]
    simp +decide [quittingTerminalSemanticDebt, quittingSetReward,
      fullBindingReward, rationalReward, rationalScale]
  payer_gain := by
    simp +decide [fullBindingReward, rationalReward, rationalScale]

namespace LocalForcedPairFragment

variable {reward : {S : Finset Player // S.Nonempty} → Payoff Player}

/-- The literal pair carried by the fragment. -/
def pairTerminal (fragment : LocalForcedPairFragment reward) :
    {S : Finset Player // S.Nonempty} :=
  ⟨{fragment.markedOwner, fragment.packetOwner}, by simp⟩

/-- The pair profile is the literal one-date Quit update of the singleton
profile at its initial root. -/
theorem pairProfile_eq_forcedUpdate
    (fragment : LocalForcedPairFragment reward) :
    fragment.pairProfile =
      quittingLiteralOneDateProfile reward fragment.singletonProfile
        fragment.markedOwner 0 true := by
  rw [fragment.pairProfile_eq, fragment.singletonProfile_eq,
    fragment.singletonOwner_eq_packetOwner]
  funext player time history
  by_cases hplayer : player = fragment.markedOwner
  · subst player
    cases time with
    | zero =>
        simp [quittingLiteralOneDateProfile, quittingLiteralOneDateOverride,
          quittingRootThenContinuationProfile, quittingPureSetRoot,
          quittingSetAction, Ne.symm fragment.packetOwner_ne_markedOwner]
        rfl
    | succ time =>
        simp [quittingLiteralOneDateProfile, quittingLiteralOneDateOverride,
          quittingRootThenContinuationProfile]
  · cases time with
    | zero =>
        simp [quittingLiteralOneDateProfile,
          quittingRootThenContinuationProfile, quittingPureSetRoot,
          quittingSetAction, hplayer]
    | succ time =>
        simp [quittingLiteralOneDateProfile,
          quittingRootThenContinuationProfile, hplayer]

/-- The displayed pure pair has full unconditional mass at its literal date. -/
theorem pairStageMass_eq_one
    (fragment : LocalForcedPairFragment reward) :
    quittingStageCoalitionMass reward fragment.pairProfile 0
      fragment.pairTerminal = 1 := by
  rw [fragment.pairProfile_eq,
    quittingStageCoalitionMass_rootThenContinuation_zero]
  exact quittingRootCoalitionMass_pureCoalitionAction_eq_one _

/-- Both literal siblings have exactly the stored continuation after their
common initial date. -/
theorem singleton_postDateSpine_eq
    (fragment : LocalForcedPairFragment reward) :
    quittingAllContinueProfileSpine reward fragment.singletonProfile 1 =
      fragment.continuation := by
  rw [fragment.singletonProfile_eq]
  change quittingProfileAllContinueContinuation reward
      (quittingRootThenContinuationProfile reward _ fragment.continuation) =
    fragment.continuation
  exact shiftProfile_quittingRootThenContinuationProfile
    reward _ fragment.continuation quittingAllContinueAction

/-- The pair sibling has the same complete post-date behavioral spine. -/
theorem pair_postDateSpine_eq
    (fragment : LocalForcedPairFragment reward) :
    quittingAllContinueProfileSpine reward fragment.pairProfile 1 =
      fragment.continuation := by
  rw [fragment.pairProfile_eq]
  change quittingProfileAllContinueContinuation reward
      (quittingRootThenContinuationProfile reward _ fragment.continuation) =
    fragment.continuation
  exact shiftProfile_quittingRootThenContinuationProfile
    reward _ fragment.continuation quittingAllContinueAction

/-- The two siblings share their complete behavioral tail after the literal
singleton-to-pair update. -/
theorem postDateSpines_eq
    (fragment : LocalForcedPairFragment reward) :
    quittingAllContinueProfileSpine reward fragment.singletonProfile 1 =
      quittingAllContinueProfileSpine reward fragment.pairProfile 1 := by
  rw [fragment.singleton_postDateSpine_eq, fragment.pair_postDateSpine_eq]

/-- Exact prescribed-payoff vector at the pure pair. -/
theorem pair_terminalPayoff_eq
    (fragment : LocalForcedPairFragment reward) :
    quittingTerminalPayoff reward fragment.pairProfile =
      quittingSetReward reward fragment.pairTerminal.val := by
  rw [fragment.pairProfile_eq]
  exact funext fun who =>
    quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
      fragment.pairTerminal.val (by simp [pairTerminal]) fragment.continuation who

/-- Exact unrestricted behavioral best-response vector at the pure pair. -/
theorem pair_bestResponse_eq
    (fragment : LocalForcedPairFragment reward) :
    quittingContinuationBestResponseValue reward fragment.pairProfile =
      fun who => max
        (quittingSetReward reward (insert who fragment.pairTerminal.val) who)
        (quittingSetReward reward (fragment.pairTerminal.val.erase who) who) := by
  have hpair :=
    quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      reward {fragment.markedOwner, fragment.packetOwner}
      (by
        have hne : fragment.markedOwner ≠ fragment.packetOwner :=
          Ne.symm fragment.packetOwner_ne_markedOwner
        simp [hne]) fragment.continuation
  rw [fragment.pairProfile_eq]
  change (quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward
        (quittingPureSetRoot {fragment.markedOwner, fragment.packetOwner})
        fragment.continuation)).2 = _
  simpa [pairTerminal] using congrArg Prod.snd hpair

/-- Exact full coordinate-debt vector at the pure pair. -/
theorem pair_debt_eq
    (fragment : LocalForcedPairFragment reward) :
    (fun who => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward fragment.pairProfile) who) =
      fun who =>
        max
          (quittingSetReward reward (insert who fragment.pairTerminal.val) who)
          (quittingSetReward reward (fragment.pairTerminal.val.erase who) who) -
        quittingSetReward reward fragment.pairTerminal.val who := by
  funext who
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward fragment.pairProfile who -
      quittingTerminalPayoff reward fragment.pairProfile who = _
  rw [congrFun fragment.pair_bestResponse_eq who,
    congrFun fragment.pair_terminalPayoff_eq who]

/-- The stored payer is outside the literal pair. -/
theorem payer_not_mem_pairTerminal
    (fragment : LocalForcedPairFragment reward) :
    fragment.payer ∉ fragment.pairTerminal.val := by
  simp [pairTerminal, fragment.payer_ne_markedOwner,
    fragment.payer_ne_packetOwner]

/-- At the literal pair, the distinct payer's debt is exactly its stored
positive pair-to-triple gain. -/
theorem payer_pairDebt_eq_gain
    (fragment : LocalForcedPairFragment reward) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward fragment.pairProfile)
          fragment.payer =
      reward
          ⟨{fragment.markedOwner, fragment.packetOwner, fragment.payer},
            by simp⟩ fragment.payer -
        reward ⟨{fragment.markedOwner, fragment.packetOwner}, by simp⟩
          fragment.payer := by
  rw [congrFun fragment.pair_debt_eq fragment.payer]
  have hnotmem := fragment.payer_not_mem_pairTerminal
  have hgain := fragment.payer_gain
  simp only [pairTerminal] at hnotmem ⊢
  rw [Finset.erase_eq_of_notMem hnotmem]
  have hinsert :
      insert fragment.payer
          ({fragment.markedOwner, fragment.packetOwner} : Finset Player) =
        ({fragment.markedOwner, fragment.packetOwner, fragment.payer} :
          Finset Player) := by
    ext who
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have htriple : quittingSetReward reward
        {fragment.markedOwner, fragment.packetOwner, fragment.payer}
          fragment.payer =
      reward
          ⟨{fragment.markedOwner, fragment.packetOwner, fragment.payer},
            by simp⟩ fragment.payer :=
    quittingSetReward_of_nonempty reward (by simp) fragment.payer
  have hpair : quittingSetReward reward
        {fragment.markedOwner, fragment.packetOwner} fragment.payer =
      reward ⟨{fragment.markedOwner, fragment.packetOwner}, by simp⟩
        fragment.payer :=
    quittingSetReward_of_nonempty reward (by simp) fragment.payer
  rw [hinsert, htriple, hpair, max_eq_left (by linarith)]

/-- The literal pair has a positive debt at a payer distinct from both pair
members. -/
theorem distinctPayer_pairDebt_pos
    (fragment : LocalForcedPairFragment reward) :
    0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward fragment.pairProfile)
        fragment.payer := by
  rw [fragment.payer_pairDebt_eq_gain]
  exact fragment.payer_gain

end LocalForcedPairFragment

def rationalSourcePair : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair (rationalReward rationalScale)
    rationalLocalForcedPairFragment.pairProfile

theorem rationalSourcePair_mem :
    rationalSourcePair ∈
      quittingTerminalSemanticCarrier (rationalReward rationalScale) :=
  quittingTerminalSemanticPair_mem_carrier _ _

theorem rationalSourcePair_cap_eq :
    rationalSourcePair.2 = rayCap rationalScale rationalScale 1 := by
  rw [rationalSourcePair, rationalLocalForcedPairFragment.pairProfile_eq]
  change (quittingTerminalSemanticPair (rationalReward rationalScale)
    (quittingRootThenContinuationProfile (rationalReward rationalScale)
      (quittingPureSetRoot {0, 3})
        (quittingAlwaysContinueProfile _))).2 = _
  rw [
    quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      _ {0, 3} (by decide)]
  funext who
  fin_cases who <;>
    simp +decide [quittingSetReward, rationalReward,
      rationalSpectatorReward, rationalScale, rayCap]

def fullBindingSourcePair (R : ℝ) : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair (fullBindingReward R rationalScale)
    (fullBindingLocalForcedPairFragment R).pairProfile

theorem fullBindingSourcePair_mem (R : ℝ) :
    fullBindingSourcePair R ∈
      quittingTerminalSemanticCarrier (fullBindingReward R rationalScale) :=
  quittingTerminalSemanticPair_mem_carrier _ _

theorem fullBindingSourcePair_cap_eq (R : ℝ) :
    (fullBindingSourcePair R).2 = rayCap rationalScale rationalScale R := by
  rw [fullBindingSourcePair,
    (fullBindingLocalForcedPairFragment R).pairProfile_eq]
  change (quittingTerminalSemanticPair (fullBindingReward R rationalScale)
    (quittingRootThenContinuationProfile (fullBindingReward R rationalScale)
      (quittingPureSetRoot {0, 3})
        (quittingAlwaysContinueProfile _))).2 = _
  rw [
    quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      _ {0, 3} (by decide)]
  funext who
  fin_cases who <;>
    simp +decide [quittingSetReward, fullBindingReward,
      fullBindingSpectatorReward, fullBindingSpectatorCoefficient,
      rationalReward, rationalScale, rayCap]

theorem rationalScale_lt_fiftieth : rationalScale < 1 / 50 := by
  norm_num [rationalScale]

def activeState (time : ℕ) :
    MaximalRayZeroMinimumActiveRegression.ConeState rationalScale :=
  MaximalRayZeroMinimumActiveRegression.coneOrbit rationalScale
    rationalScale_pos rationalScale_lt_fiftieth time

def activeData (time : ℕ) :
    MaximalRayZeroMinimumActiveRegression.FullRootData
      (activeState time).a (activeState time).b :=
  (activeState time).fullRootData rationalScale_lt_fiftieth

def activeRowSurvival (time : ℕ) : ℝ :=
  (1 - (activeData time).t) ^ 2 * (1 - (activeData time).z)

theorem activeRowSurvival_pos (time : ℕ) : 0 < activeRowSurvival time := by
  unfold activeRowSurvival
  have ht := (activeData time).t_lt_one (activeState time).a_pos
  have hz := (activeData time).z_lt_half.trans (by norm_num : (1 / 2 : ℝ) < 1)
  exact mul_pos (sq_pos_of_pos (sub_pos.mpr ht)) (sub_pos.mpr hz)

theorem activeRowSurvival_le_one (time : ℕ) : activeRowSurvival time ≤ 1 := by
  unfold activeRowSurvival
  have ht0 := (activeData time).t_pos (activeState time).a_pos
  have ht1 := (activeData time).t_lt_one (activeState time).a_pos
  have hz0 := (activeData time).z_pos
  have hz1 := (activeData time).z_lt_half.trans (by norm_num : (1 / 2 : ℝ) < 1)
  have hsquare : (1 - (activeData time).t) ^ 2 ≤ 1 := by nlinarith
  have hzfactor : 1 - (activeData time).z ≤ 1 := by linarith
  have hsquare0 : 0 ≤ (1 - (activeData time).t) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hzfactor hsquare0]

def rationalSpectatorCap : ℕ → ℝ
  | 0 => 1
  | time + 1 =>
      2 * (activeData time).t + (activeData time).z +
        activeRowSurvival time * rationalSpectatorCap time

@[simp] theorem rationalSpectatorCap_zero : rationalSpectatorCap 0 = 1 := rfl

@[simp] theorem rationalSpectatorCap_succ (time : ℕ) :
    rationalSpectatorCap (time + 1) =
      2 * (activeData time).t + (activeData time).z +
        activeRowSurvival time * rationalSpectatorCap time := rfl

theorem rationalSpectatorCap_pos (time : ℕ) : 0 < rationalSpectatorCap time := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [rationalSpectatorCap_succ]
      have ht := (activeData time).t_pos (activeState time).a_pos
      have hz := (activeData time).z_pos
      have hs := activeRowSurvival_pos time
      positivity

def rationalSemanticOrbit : ℕ → QuittingTerminalSemanticPair Player :=
  quittingMaximalCapSemanticPrefixOrbit (rationalReward rationalScale)
    rationalSourcePair

theorem rationalSemanticOrbit_mem (time : ℕ) :
    rationalSemanticOrbit time ∈
      quittingTerminalSemanticCarrier (rationalReward rationalScale) :=
  quittingMaximalCapSemanticPrefixOrbit_mem_carrier _ _ rationalSourcePair_mem time

theorem rationalSemanticOrbit_cap_eq (time : ℕ) :
    (rationalSemanticOrbit time).2 =
      rayCap (activeState time).a (activeState time).b
        (rationalSpectatorCap time) := by
  induction time with
  | zero =>
      simpa [rationalSemanticOrbit, activeState,
        MaximalRayZeroMinimumActiveRegression.initialConeState] using
          rationalSourcePair_cap_eq
  | succ time ih =>
      have hroot : quittingMaximalCapSemanticRoot (rationalReward rationalScale)
          (rationalSemanticOrbit time) =
        LiftedActiveRoot.root (activeData time) (activeState time).a_pos := by
        unfold quittingMaximalCapSemanticRoot
        rw [ih]
        exact rationalReward_maximalAbsorptionCapRoot_eq_liftedActiveRoot
          rationalScale (activeState time).a (activeState time).b
            (rationalSpectatorCap time) (activeData time)
              (activeState time).a_pos (activeState time).b_pos
                (rationalSpectatorCap_pos time)
      rw [show rationalSemanticOrbit (time + 1) =
        quittingTerminalSemanticPrefix (rationalReward rationalScale)
          (quittingMaximalCapSemanticRoot (rationalReward rationalScale)
            (rationalSemanticOrbit time)) (rationalSemanticOrbit time) by rfl]
      rw [quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
        (rationalSemanticOrbit time)
          (quittingMaximalCapSemanticRoot (rationalReward rationalScale)
            (rationalSemanticOrbit time))
          (quittingMaximalCapSemanticRoot_exactNash _ _), hroot, ih,
        LiftedActiveRoot.rationalReward_successorPayoff rationalScale
          (activeState time).a (activeState time).b
            (rationalSpectatorCap time) (activeData time)
              (activeState time).a_pos (rationalSpectatorCap_pos time)]
      rfl

def activeTotalHazard (time : ℕ) : ℝ :=
  2 * (activeData time).t + (activeData time).z

theorem activeTotalHazard_pos (time : ℕ) : 0 < activeTotalHazard time := by
  unfold activeTotalHazard
  linarith [(activeData time).t_pos (activeState time).a_pos,
    (activeData time).z_pos]

theorem activeTotalHazard_summable : Summable activeTotalHazard := by
  let orbit := MaximalRayZeroMinimumActiveRegression.explicitRecurrence
    rationalScale rationalScale_pos rationalScale_lt_fiftieth
  have hsum := orbit.summable_totalHazard
  apply hsum.congr
  intro time
  rfl

theorem one_sub_activeRowSurvival_le_activeTotalHazard (time : ℕ) :
    1 - activeRowSurvival time ≤ activeTotalHazard time := by
  have hunion := Math.one_sub_prod_one_sub_le_sum
    (activeData time).hazard Finset.univ
      (fun who _ ↦ (activeData time).hazard_nonneg (activeState time).a_pos who)
      (fun who _ ↦ (activeData time).hazard_le_one (activeState time).a_pos who)
  simp [activeRowSurvival, activeTotalHazard,
    MaximalRayZeroMinimumActiveRegression.FullRootData.hazard,
    Fin.prod_univ_three, Fin.sum_univ_three] at hunion ⊢
  nlinarith

/-- Active absorption in the common three-player product row. -/
def activeRowAbsorption (time : ℕ) : ℝ := 1 - activeRowSurvival time

theorem activeRowAbsorption_nonneg (time : ℕ) : 0 ≤ activeRowAbsorption time := by
  unfold activeRowAbsorption
  linarith [activeRowSurvival_le_one time]

theorem activeRowAbsorption_lt_one (time : ℕ) : activeRowAbsorption time < 1 := by
  unfold activeRowAbsorption
  linarith [activeRowSurvival_pos time]

theorem activeRowAbsorption_summable : Summable activeRowAbsorption :=
  activeTotalHazard_summable.of_nonneg_of_le activeRowAbsorption_nonneg
    one_sub_activeRowSurvival_le_activeTotalHazard

/-- Finite active survival product through the first `time` rows. -/
def fullBindingSurvivalProduct (time : ℕ) : ℝ :=
  ∏ date ∈ Finset.range time, activeRowSurvival date

@[simp] theorem fullBindingSurvivalProduct_zero :
    fullBindingSurvivalProduct 0 = 1 := by
  simp [fullBindingSurvivalProduct]

theorem fullBindingSurvivalProduct_succ (time : ℕ) :
    fullBindingSurvivalProduct (time + 1) =
      fullBindingSurvivalProduct time * activeRowSurvival time := by
  simp [fullBindingSurvivalProduct, Finset.prod_range_succ]

theorem fullBindingSurvivalProduct_pos (time : ℕ) :
    0 < fullBindingSurvivalProduct time := by
  exact Finset.prod_pos fun date _ ↦ activeRowSurvival_pos date

theorem fullBindingSurvivalProduct_le_one (time : ℕ) :
    fullBindingSurvivalProduct time ≤ 1 := by
  exact Finset.prod_le_one
    (fun date _ ↦ (activeRowSurvival_pos date).le)
    (fun date _ ↦ activeRowSurvival_le_one date)

theorem exists_pos_le_fullBindingSurvivalProduct :
    ∃ lower : ℝ, 0 < lower ∧
      ∀ time, lower ≤ fullBindingSurvivalProduct time := by
  obtain ⟨lower, hlower, hbound⟩ :=
    Math.exists_pos_le_prod_one_sub_of_summable activeRowAbsorption
      activeRowAbsorption_nonneg activeRowAbsorption_lt_one
        activeRowAbsorption_summable
  refine ⟨lower, hlower, fun time ↦ ?_⟩
  simpa [fullBindingSurvivalProduct, activeRowAbsorption] using hbound time

def fullBindingSurvivalLower : ℝ :=
  Classical.choose exists_pos_le_fullBindingSurvivalProduct

theorem fullBindingSurvivalLower_pos : 0 < fullBindingSurvivalLower :=
  (Classical.choose_spec exists_pos_le_fullBindingSurvivalProduct).1

theorem fullBindingSurvivalLower_le (time : ℕ) :
    fullBindingSurvivalLower ≤ fullBindingSurvivalProduct time :=
  (Classical.choose_spec exists_pos_le_fullBindingSurvivalProduct).2 time

theorem activeData_t_summable : Summable (fun time ↦ (activeData time).t) := by
  let orbit := MaximalRayZeroMinimumActiveRegression.explicitRecurrence
    rationalScale rationalScale_pos rationalScale_lt_fiftieth
  have hsum := orbit.summable_t
  simpa [orbit, activeData, activeState,
    MaximalRayZeroMinimumActiveRegression.explicitRecurrence] using hsum

theorem activeData_t_tsum_le :
    (∑' time, (activeData time).t) ≤ 1 / 40 := by
  let orbit := MaximalRayZeroMinimumActiveRegression.explicitRecurrence
    rationalScale rationalScale_pos rationalScale_lt_fiftieth
  let major : ℕ → ℝ := fun time ↦
    (5 / 4 : ℝ) * rationalScale * (1 / 2 : ℝ) ^ time
  have hmajorSummable : Summable major := by
    exact (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
        ((5 / 4 : ℝ) * rationalScale)
  have hle : ∀ time, (activeData time).t ≤ major time := by
    intro time
    change orbit.t time ≤
      (5 / 4 : ℝ) * rationalScale * (1 / 2 : ℝ) ^ time
    calc
      orbit.t time ≤ (5 / 4 : ℝ) * orbit.b time :=
        orbit.t_le_five_fourths_b time
      _ ≤ (5 / 4 : ℝ) *
          (orbit.b 0 * (1 / 2 : ℝ) ^ time) :=
        mul_le_mul_of_nonneg_left (orbit.b_le_geometric time) (by norm_num)
      _ = major time := by
        simp [major, orbit,
          MaximalRayZeroMinimumActiveRegression.explicitRecurrence,
          MaximalRayZeroMinimumActiveRegression.initialConeState]
        ring
  have htsum := Summable.tsum_le_tsum hle activeData_t_summable
    hmajorSummable
  calc
    (∑' time, (activeData time).t) ≤ ∑' time, major time := htsum
    _ = 1 / 40 := by
      rw [show (∑' time : ℕ, major time) =
        ((5 / 4 : ℝ) * rationalScale) *
          ∑' time : ℕ, (1 / 2 : ℝ) ^ time by
            simp [major, tsum_mul_left]]
      rw [tsum_geometric_of_norm_lt_one (by norm_num)]
      norm_num [rationalScale]

theorem activeRowAbsorption_tsum_le :
    (∑' time, activeRowAbsorption time) ≤ 3 / 40 := by
  have hthreeSummable : Summable (fun time ↦ 3 * (activeData time).t) :=
    activeData_t_summable.mul_left 3
  have hle : ∀ time, activeRowAbsorption time ≤ 3 * (activeData time).t := by
    intro time
    calc
      activeRowAbsorption time ≤ activeTotalHazard time :=
        one_sub_activeRowSurvival_le_activeTotalHazard time
      _ ≤ 3 * (activeData time).t := by
        unfold activeTotalHazard
        linarith [(activeData time).z_lt_t (activeState time).a_pos]
  calc
    (∑' time, activeRowAbsorption time) ≤
        ∑' time, 3 * (activeData time).t :=
      Summable.tsum_le_tsum hle activeRowAbsorption_summable hthreeSummable
    _ = 3 * ∑' time, (activeData time).t := tsum_mul_left
    _ ≤ 3 * (1 / 40 : ℝ) :=
      mul_le_mul_of_nonneg_left activeData_t_tsum_le (by norm_num)
    _ = 3 / 40 := by ring

theorem thirtySeven_fortieth_le_fullBindingSurvivalProduct (time : ℕ) :
    (37 / 40 : ℝ) ≤ fullBindingSurvivalProduct time := by
  have hfinite := activeRowAbsorption_summable.sum_le_tsum
    (Finset.range time) (fun date _ ↦ activeRowAbsorption_nonneg date)
  have hproduct := Math.one_sub_sum_range_le_prod_one_sub
    activeRowAbsorption activeRowAbsorption_nonneg
      (fun date ↦ (activeRowAbsorption_lt_one date).le) 0 time
  calc
    (37 / 40 : ℝ) ≤ 1 - ∑ date ∈ Finset.range time,
        activeRowAbsorption date := by
      linarith [hfinite.trans activeRowAbsorption_tsum_le]
    _ ≤ fullBindingSurvivalProduct time := by
      simpa [fullBindingSurvivalProduct, activeRowAbsorption,
        Nat.zero_add] using hproduct

/-- Normalized spectator charge used to tune the full-binding completion. -/
def fullBindingSpectatorCharge (time : ℕ) : ℝ :=
  (activeData time).t / fullBindingSurvivalProduct (time + 1)

theorem fullBindingSpectatorCharge_pos (time : ℕ) :
    0 < fullBindingSpectatorCharge time :=
  div_pos ((activeData time).t_pos (activeState time).a_pos)
    (fullBindingSurvivalProduct_pos (time + 1))

theorem fullBindingSpectatorCharge_summable :
    Summable fullBindingSpectatorCharge := by
  have hmajor : Summable (fun time ↦
      (fullBindingSurvivalLower)⁻¹ * (activeData time).t) :=
    activeData_t_summable.mul_left _
  apply hmajor.of_nonneg_of_le
  · exact fun time ↦ (fullBindingSpectatorCharge_pos time).le
  · intro time
    have hlower := fullBindingSurvivalLower_le (time + 1)
    have hlowerPos := fullBindingSurvivalLower_pos
    have hproductPos := fullBindingSurvivalProduct_pos (time + 1)
    have ht0 := ((activeData time).t_pos (activeState time).a_pos).le
    rw [fullBindingSpectatorCharge, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ hproductPos hlowerPos).2 hlower) ht0

/-- Fixed real spectator coordinate of the full-binding completion. -/
def fullBindingInitialCap : ℝ := ∑' time, fullBindingSpectatorCharge time

theorem fullBindingInitialCap_pos : 0 < fullBindingInitialCap := by
  have hle := fullBindingSpectatorCharge_summable.le_tsum 0
    (fun time _ ↦ (fullBindingSpectatorCharge_pos time).le)
  exact (fullBindingSpectatorCharge_pos 0).trans_le
    (by simpa [fullBindingInitialCap] using hle)

theorem fullBindingInitialCap_le : fullBindingInitialCap ≤ 1 / 37 := by
  have hmajorSummable : Summable (fun time ↦
      (40 / 37 : ℝ) * (activeData time).t) :=
    activeData_t_summable.mul_left _
  have hle : ∀ time, fullBindingSpectatorCharge time ≤
      (40 / 37 : ℝ) * (activeData time).t := by
    intro time
    have hproduct := thirtySeven_fortieth_le_fullBindingSurvivalProduct
      (time + 1)
    have hproductPos := fullBindingSurvivalProduct_pos (time + 1)
    have ht0 := ((activeData time).t_pos (activeState time).a_pos).le
    rw [fullBindingSpectatorCharge, div_eq_inv_mul]
    have hinv : (fullBindingSurvivalProduct (time + 1))⁻¹ ≤ 40 / 37 := by
      rw [show (40 / 37 : ℝ) = ((37 / 40 : ℝ))⁻¹ by norm_num]
      exact (inv_le_inv₀ hproductPos (by norm_num)).2 hproduct
    exact mul_le_mul_of_nonneg_right hinv ht0
  calc
    fullBindingInitialCap ≤
        ∑' time, (40 / 37 : ℝ) * (activeData time).t := by
      exact Summable.tsum_le_tsum hle fullBindingSpectatorCharge_summable
        hmajorSummable
    _ = (40 / 37 : ℝ) * ∑' time, (activeData time).t := tsum_mul_left
    _ ≤ (40 / 37 : ℝ) * (1 / 40 : ℝ) :=
      mul_le_mul_of_nonneg_left activeData_t_tsum_le (by norm_num)
    _ = 1 / 37 := by norm_num

/-- Closed-form positive solution of the spectator renewal recurrence. -/
def fullBindingSpectatorCap (time : ℕ) : ℝ :=
  fullBindingSurvivalProduct time *
    ∑' offset, fullBindingSpectatorCharge (time + offset)

@[simp] theorem fullBindingSpectatorCap_zero :
    fullBindingSpectatorCap 0 = fullBindingInitialCap := by
  simp [fullBindingSpectatorCap, fullBindingInitialCap]

theorem fullBindingSpectatorCap_pos (time : ℕ) :
    0 < fullBindingSpectatorCap time := by
  have hshift : Summable (fun offset ↦
      fullBindingSpectatorCharge (time + offset)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff time).2 fullBindingSpectatorCharge_summable
  have hle := hshift.le_tsum 0
    (fun offset _ ↦ (fullBindingSpectatorCharge_pos (time + offset)).le)
  have htail : 0 < ∑' offset,
      fullBindingSpectatorCharge (time + offset) :=
    (fullBindingSpectatorCharge_pos time).trans_le (by simpa using hle)
  exact mul_pos (fullBindingSurvivalProduct_pos time) htail

theorem fullBindingSpectatorCap_succ (time : ℕ) :
    fullBindingSpectatorCap (time + 1) =
      activeRowSurvival time * fullBindingSpectatorCap time -
        (activeData time).t := by
  have hshift : Summable (fun offset ↦
      fullBindingSpectatorCharge (time + offset)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff time).2 fullBindingSpectatorCharge_summable
  have hsplit := hshift.sum_add_tsum_nat_add 1
  have hsurvival := activeRowSurvival_pos time
  have hproduct := fullBindingSurvivalProduct_pos time
  rw [fullBindingSpectatorCap, fullBindingSpectatorCap,
    fullBindingSurvivalProduct_succ]
  have htail : (∑' offset, fullBindingSpectatorCharge (time + offset)) =
      fullBindingSpectatorCharge time +
        ∑' offset, fullBindingSpectatorCharge (time + 1 + offset) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm
  rw [htail, fullBindingSpectatorCharge,
    fullBindingSurvivalProduct_succ]
  field_simp [hsurvival.ne', hproduct.ne']
  ring

theorem fullBindingSpectatorCap_le_chargeTail (time : ℕ) :
    fullBindingSpectatorCap time ≤
      ∑' offset, fullBindingSpectatorCharge (time + offset) := by
  have htail0 : 0 ≤ ∑' offset,
      fullBindingSpectatorCharge (time + offset) := by
    exact tsum_nonneg fun _ ↦ (fullBindingSpectatorCharge_pos _).le
  unfold fullBindingSpectatorCap
  exact mul_le_of_le_one_left htail0 (fullBindingSurvivalProduct_le_one time)

theorem fullBindingSpectatorCap_tendsto_zero :
    Tendsto fullBindingSpectatorCap atTop (nhds 0) := by
  have htail : Tendsto (fun time ↦
      ∑' offset, fullBindingSpectatorCharge (offset + time)) atTop (nhds 0) :=
    tendsto_sum_nat_add fullBindingSpectatorCharge
  have htail' : Tendsto (fun time ↦
      ∑' offset, fullBindingSpectatorCharge (time + offset)) atTop (nhds 0) := by
    simpa [Nat.add_comm] using htail
  apply squeeze_zero'
  · exact Eventually.of_forall fun time ↦ (fullBindingSpectatorCap_pos time).le
  · exact Eventually.of_forall fullBindingSpectatorCap_le_chargeTail
  · exact htail'

theorem activeState_a_tendsto_zero :
    Tendsto (fun time ↦ (activeState time).a) atTop (nhds 0) := by
  let orbit := MaximalRayZeroMinimumActiveRegression.explicitRecurrence
    rationalScale rationalScale_pos rationalScale_lt_fiftieth
  have h := orbit.tendsto_a_zero
  simpa [orbit, activeState,
    MaximalRayZeroMinimumActiveRegression.explicitRecurrence] using h

theorem activeState_b_tendsto_zero :
    Tendsto (fun time ↦ (activeState time).b) atTop (nhds 0) := by
  let orbit := MaximalRayZeroMinimumActiveRegression.explicitRecurrence
    rationalScale rationalScale_pos rationalScale_lt_fiftieth
  have h := orbit.tendsto_b_zero
  simpa [orbit, activeState,
    MaximalRayZeroMinimumActiveRegression.explicitRecurrence] using h

theorem activeData_t_tendsto_zero :
    Tendsto (fun time ↦ (activeData time).t) atTop (nhds 0) := by
  let orbit := MaximalRayZeroMinimumActiveRegression.explicitRecurrence
    rationalScale rationalScale_pos rationalScale_lt_fiftieth
  have h := orbit.tendsto_t_zero
  simpa [orbit, activeData, activeState,
    MaximalRayZeroMinimumActiveRegression.explicitRecurrence] using h

theorem activeData_z_tendsto_zero :
    Tendsto (fun time ↦ (activeData time).z) atTop (nhds 0) := by
  let orbit := MaximalRayZeroMinimumActiveRegression.explicitRecurrence
    rationalScale rationalScale_pos rationalScale_lt_fiftieth
  have h := orbit.tendsto_z_zero
  simpa [orbit, activeData, activeState,
    MaximalRayZeroMinimumActiveRegression.explicitRecurrence] using h

/-- Canonical semantic orbit of the tuned full-binding completion. -/
def fullBindingSemanticOrbit : ℕ → QuittingTerminalSemanticPair Player :=
  quittingMaximalCapSemanticPrefixOrbit
    (fullBindingReward fullBindingInitialCap rationalScale)
      (fullBindingSourcePair fullBindingInitialCap)

theorem fullBindingSemanticOrbit_mem (time : ℕ) :
    fullBindingSemanticOrbit time ∈ quittingTerminalSemanticCarrier
      (fullBindingReward fullBindingInitialCap rationalScale) :=
  quittingMaximalCapSemanticPrefixOrbit_mem_carrier _ _
    (fullBindingSourcePair_mem fullBindingInitialCap) time

theorem fullBindingSemanticOrbit_cap_eq (time : ℕ) :
    (fullBindingSemanticOrbit time).2 =
      rayCap (activeState time).a (activeState time).b
        (fullBindingSpectatorCap time) := by
  induction time with
  | zero =>
      simpa [fullBindingSemanticOrbit, activeState,
        MaximalRayZeroMinimumActiveRegression.initialConeState] using
          fullBindingSourcePair_cap_eq fullBindingInitialCap
  | succ time ih =>
      have hroot : quittingMaximalCapSemanticRoot
          (fullBindingReward fullBindingInitialCap rationalScale)
            (fullBindingSemanticOrbit time) =
        LiftedActiveRoot.root (activeData time) (activeState time).a_pos := by
        unfold quittingMaximalCapSemanticRoot
        rw [ih]
        exact fullBindingReward_maximalAbsorptionCapRoot_eq_liftedActiveRoot
          fullBindingInitialCap rationalScale (activeState time).a
            (activeState time).b (fullBindingSpectatorCap time)
              (activeData time) (activeState time).a_pos
                (activeState time).b_pos (fullBindingSpectatorCap_pos time)
      rw [show fullBindingSemanticOrbit (time + 1) =
        quittingTerminalSemanticPrefix
          (fullBindingReward fullBindingInitialCap rationalScale)
            (quittingMaximalCapSemanticRoot
              (fullBindingReward fullBindingInitialCap rationalScale)
                (fullBindingSemanticOrbit time))
                  (fullBindingSemanticOrbit time) by rfl]
      rw [quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
        (fullBindingSemanticOrbit time)
          (quittingMaximalCapSemanticRoot
            (fullBindingReward fullBindingInitialCap rationalScale)
              (fullBindingSemanticOrbit time))
          (quittingMaximalCapSemanticRoot_exactNash _ _), hroot, ih,
        LiftedActiveRoot.fullBindingReward_successorPayoff fullBindingInitialCap
          rationalScale (activeState time).a (activeState time).b
            (fullBindingSpectatorCap time) (activeData time)
              (activeState time).a_pos (fullBindingSpectatorCap_pos time),
        fullBindingSpectatorCap_succ]
      rfl

theorem fullBindingCanonicalRoot_eq (time : ℕ) :
    quittingMaximalCapSemanticRoot
        (fullBindingReward fullBindingInitialCap rationalScale)
          (fullBindingSemanticOrbit time) =
      LiftedActiveRoot.root (activeData time) (activeState time).a_pos := by
  unfold quittingMaximalCapSemanticRoot
  rw [fullBindingSemanticOrbit_cap_eq]
  exact fullBindingReward_maximalAbsorptionCapRoot_eq_liftedActiveRoot
    fullBindingInitialCap rationalScale (activeState time).a
      (activeState time).b (fullBindingSpectatorCap time) (activeData time)
        (activeState time).a_pos (activeState time).b_pos
          (fullBindingSpectatorCap_pos time)

theorem fullBindingCanonicalRoot_absorption_summable :
    Summable (fun time ↦ quittingRootAbsorptionMass
      (quittingMaximalCapSemanticRoot
        (fullBindingReward fullBindingInitialCap rationalScale)
          (fullBindingSemanticOrbit time))) := by
  apply activeTotalHazard_summable.of_nonneg_of_le
  · intro time
    exact quittingRootAbsorptionMass_nonneg _
  · intro time
    rw [fullBindingCanonicalRoot_eq]
    have hle := quittingRootAbsorptionMass_le_sum_quitRates
      (LiftedActiveRoot.root (activeData time) (activeState time).a_pos)
    calc
      quittingRootAbsorptionMass
          (LiftedActiveRoot.root (activeData time) (activeState time).a_pos) ≤
          (activeData time).t + (activeData time).t +
            (activeData time).z := by
        simpa [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
          quittingRootQuitRates, Fin.sum_univ_four] using hle
      _ = activeTotalHazard time := by
        unfold activeTotalHazard
        ring

theorem fullBindingCanonicalRoot_totalHazard_pos (time : ℕ) :
    0 < ∑ who, quittingRootQuitRates
      (quittingMaximalCapSemanticRoot
        (fullBindingReward fullBindingInitialCap rationalScale)
          (fullBindingSemanticOrbit time)) who := by
  rw [fullBindingCanonicalRoot_eq]
  simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
    quittingRootQuitRates, Fin.sum_univ_four]
  have hpositive := activeTotalHazard_pos time
  unfold activeTotalHazard at hpositive
  nlinarith

theorem fullBindingCanonicalRoot_quitRate_tendsto_zero (who : Player) :
    Tendsto (fun time ↦ quittingRootQuitRates
      (quittingMaximalCapSemanticRoot
        (fullBindingReward fullBindingInitialCap rationalScale)
          (fullBindingSemanticOrbit time)) who) atTop (nhds 0) := by
  simp_rw [fullBindingCanonicalRoot_eq]
  fin_cases who
  · simpa [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates] using activeData_t_tendsto_zero
  · simpa [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates] using activeData_t_tendsto_zero
  · simpa [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates] using activeData_z_tendsto_zero
  · simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates]

def fullBindingForwardExactCapTail :
    QuittingForwardExactCapTail
      (fullBindingReward fullBindingInitialCap rationalScale) where
  pair := fullBindingSemanticOrbit
  root := fun time ↦ quittingMaximalCapSemanticRoot
    (fullBindingReward fullBindingInitialCap rationalScale)
      (fullBindingSemanticOrbit time)
  pair_mem := fullBindingSemanticOrbit_mem
  exactNash := fun time ↦ quittingMaximalCapSemanticRoot_exactNash _ _
  forward := fun _ ↦ rfl
  absorption_summable := fullBindingCanonicalRoot_absorption_summable
  totalHazard_pos := fullBindingCanonicalRoot_totalHazard_pos
  capLimit := 0
  cap_tendsto := by
    intro who
    fin_cases who
    · simpa [fullBindingSemanticOrbit_cap_eq, rayCap] using
        activeState_a_tendsto_zero
    · simpa [fullBindingSemanticOrbit_cap_eq, rayCap] using
        activeState_a_tendsto_zero
    · simpa [fullBindingSemanticOrbit_cap_eq, rayCap] using
        activeState_b_tendsto_zero
    · simpa [fullBindingSemanticOrbit_cap_eq, rayCap] using
        fullBindingSpectatorCap_tendsto_zero
  singleton_le_capLimit := by
    intro who
    rw [fullBindingReward_singleton_eq_zero]
    exact le_rfl

theorem rationalSpectatorCap_le_rewardBound (time : ℕ) :
    rationalSpectatorCap time ≤
      quittingRewardBound (rationalReward rationalScale) := by
  have hbox := quittingTerminalSemanticCarrier_mem_box
    (rationalReward rationalScale) (rationalSemanticOrbit time)
      (abs_reward_le_quittingRewardBound _) (rationalSemanticOrbit_mem time)
  have hupper := hbox.2.2 (3 : Player)
  rw [rationalSemanticOrbit_cap_eq] at hupper
  simpa [rayCap] using hupper

theorem summable_abs_rationalSpectatorCap_succ_sub :
    Summable (fun time ↦
      |rationalSpectatorCap (time + 1) - rationalSpectatorCap time|) := by
  let bound := quittingRewardBound (rationalReward rationalScale)
  have hbound0 : 0 ≤ bound := quittingRewardBound_nonneg _
  have hmajor : Summable (fun time ↦ (1 + bound) * activeTotalHazard time) :=
    activeTotalHazard_summable.mul_left (1 + bound)
  apply hmajor.of_nonneg_of_le (fun _ ↦ abs_nonneg _)
  intro time
  have hq0 := (activeTotalHazard_pos time).le
  have hs0 := (activeRowSurvival_pos time).le
  have hs1 := activeRowSurvival_le_one time
  have hc0 := (rationalSpectatorCap_pos time).le
  have hcBound : rationalSpectatorCap time ≤ bound :=
    rationalSpectatorCap_le_rewardBound time
  have habs := one_sub_activeRowSurvival_le_activeTotalHazard time
  rw [rationalSpectatorCap_succ]
  change |activeTotalHazard time + activeRowSurvival time *
      rationalSpectatorCap time - rationalSpectatorCap time| ≤ _
  calc
    |activeTotalHazard time + activeRowSurvival time *
        rationalSpectatorCap time - rationalSpectatorCap time| =
        |activeTotalHazard time +
          (activeRowSurvival time - 1) * rationalSpectatorCap time| := by ring
    _ ≤ |activeTotalHazard time| +
        |(activeRowSurvival time - 1) * rationalSpectatorCap time| :=
      abs_add_le _ _
    _ = activeTotalHazard time +
        (1 - activeRowSurvival time) * rationalSpectatorCap time := by
      rw [abs_of_nonneg hq0, abs_mul, abs_of_nonpos (by linarith),
        abs_of_nonneg hc0]
      ring
    _ ≤ activeTotalHazard time + (1 - activeRowSurvival time) * bound := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hcBound (sub_nonneg.mpr hs1))
    _ ≤ (1 + bound) * activeTotalHazard time := by
      nlinarith [mul_le_mul_of_nonneg_right habs hbound0]

theorem exists_rationalSpectatorCap_limit :
    ∃ limit : ℝ, Tendsto rationalSpectatorCap atTop (nhds limit) := by
  have hdist : Summable (fun time ↦
      dist (rationalSpectatorCap time) (rationalSpectatorCap time.succ)) := by
    simpa [Real.dist_eq, abs_sub_comm, Nat.succ_eq_add_one] using
      summable_abs_rationalSpectatorCap_succ_sub
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)

def rationalSpectatorLimit : ℝ :=
  Classical.choose exists_rationalSpectatorCap_limit

theorem rationalSpectatorCap_tendsto :
    Tendsto rationalSpectatorCap atTop (nhds rationalSpectatorLimit) :=
  Classical.choose_spec exists_rationalSpectatorCap_limit

theorem one_le_rationalSpectatorCap (time : ℕ) :
    1 ≤ rationalSpectatorCap time := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [rationalSpectatorCap_succ]
      have habs := one_sub_activeRowSurvival_le_activeTotalHazard time
      change 1 ≤ activeTotalHazard time +
        activeRowSurvival time * rationalSpectatorCap time
      have hs0 := (activeRowSurvival_pos time).le
      nlinarith [mul_le_mul_of_nonneg_left ih hs0]

theorem one_le_rationalSpectatorLimit : 1 ≤ rationalSpectatorLimit :=
  ge_of_tendsto' rationalSpectatorCap_tendsto one_le_rationalSpectatorCap

theorem rationalCanonicalRoot_eq (time : ℕ) :
    quittingMaximalCapSemanticRoot (rationalReward rationalScale)
        (rationalSemanticOrbit time) =
      LiftedActiveRoot.root (activeData time) (activeState time).a_pos := by
  unfold quittingMaximalCapSemanticRoot
  rw [rationalSemanticOrbit_cap_eq]
  exact rationalReward_maximalAbsorptionCapRoot_eq_liftedActiveRoot
    rationalScale (activeState time).a (activeState time).b
      (rationalSpectatorCap time) (activeData time)
        (activeState time).a_pos (activeState time).b_pos
          (rationalSpectatorCap_pos time)

theorem rationalCanonicalRoot_absorption_summable :
    Summable (fun time ↦ quittingRootAbsorptionMass
      (quittingMaximalCapSemanticRoot (rationalReward rationalScale)
        (rationalSemanticOrbit time))) := by
  apply activeTotalHazard_summable.of_nonneg_of_le
  · intro time
    exact quittingRootAbsorptionMass_nonneg _
  · intro time
    rw [rationalCanonicalRoot_eq]
    have hle := quittingRootAbsorptionMass_le_sum_quitRates
      (LiftedActiveRoot.root (activeData time) (activeState time).a_pos)
    calc
      quittingRootAbsorptionMass
          (LiftedActiveRoot.root (activeData time) (activeState time).a_pos) ≤
          (activeData time).t + (activeData time).t +
            (activeData time).z := by
        simpa [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
          quittingRootQuitRates, Fin.sum_univ_four] using hle
      _ = activeTotalHazard time := by
        unfold activeTotalHazard
        ring

theorem rationalCanonicalRoot_totalHazard_pos (time : ℕ) :
    0 < ∑ who, quittingRootQuitRates
      (quittingMaximalCapSemanticRoot (rationalReward rationalScale)
        (rationalSemanticOrbit time)) who := by
  rw [rationalCanonicalRoot_eq]
  simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
    quittingRootQuitRates, Fin.sum_univ_four]
  have hpositive := activeTotalHazard_pos time
  unfold activeTotalHazard at hpositive
  nlinarith

theorem rationalCanonicalRoot_quitRate_tendsto_zero (who : Player) :
    Tendsto (fun time ↦ quittingRootQuitRates
      (quittingMaximalCapSemanticRoot (rationalReward rationalScale)
        (rationalSemanticOrbit time)) who) atTop (nhds 0) := by
  simp_rw [rationalCanonicalRoot_eq]
  fin_cases who
  · simpa [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates] using
      activeData_t_tendsto_zero
  · simpa [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates] using
      activeData_t_tendsto_zero
  · simpa [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates] using
      activeData_z_tendsto_zero
  · simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates]

def rationalForwardExactCapTail :
    QuittingForwardExactCapTail (rationalReward rationalScale) where
  pair := rationalSemanticOrbit
  root := fun time ↦ quittingMaximalCapSemanticRoot
    (rationalReward rationalScale) (rationalSemanticOrbit time)
  pair_mem := rationalSemanticOrbit_mem
  exactNash := fun time ↦ quittingMaximalCapSemanticRoot_exactNash _ _
  forward := fun _ ↦ rfl
  absorption_summable := rationalCanonicalRoot_absorption_summable
  totalHazard_pos := rationalCanonicalRoot_totalHazard_pos
  capLimit := ![0, 0, 0, rationalSpectatorLimit]
  cap_tendsto := by
    intro who
    fin_cases who
    · simpa [rationalSemanticOrbit_cap_eq, rayCap] using activeState_a_tendsto_zero
    · simpa [rationalSemanticOrbit_cap_eq, rayCap] using activeState_a_tendsto_zero
    · simpa [rationalSemanticOrbit_cap_eq, rayCap] using activeState_b_tendsto_zero
    · simpa [rationalSemanticOrbit_cap_eq, rayCap] using
        rationalSpectatorCap_tendsto
  singleton_le_capLimit := by
    intro who
    fin_cases who
    · simpa using (rationalReward_singleton_eq_zero (0 : Player)).le
    · simpa using (rationalReward_singleton_eq_zero (1 : Player)).le
    · simpa using (rationalReward_singleton_eq_zero (2 : Player)).le
    · change rationalReward rationalScale (quittingSingletonTerminal 3) 3 ≤
        rationalSpectatorLimit
      rw [rationalReward_singleton_eq_zero]
      linarith [one_le_rationalSpectatorLimit]

/-- A positive exact root at the limiting cap.  It is not the limit of the
selected ray roots, whose Quit probabilities tend to zero. -/
def rationalLimitRoot : Player → PMF Bool :=
  rootOfHazard ![0, 0, (1 / 2 : ℝ), 0]
    (by intro who; fin_cases who <;> simp)
    (by intro who; fin_cases who <;> norm_num)

@[simp] theorem rationalLimitRoot_true (who : Player) :
    (rationalLimitRoot who true).toReal = ![0, 0, (1 / 2 : ℝ), 0] who := by
  simp [rationalLimitRoot, rootOfHazard]

theorem rationalLimitRoot_exactNash :
    IsεQuittingRootNash (rationalReward rationalScale)
      rationalForwardExactCapTail.capLimit 0 rationalLimitRoot := by
  change IsεQuittingRootNash (rationalReward rationalScale)
    (rayCap 0 0 rationalSpectatorLimit) 0 rationalLimitRoot
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  have hspectator : (rationalLimitRoot 3 true).toReal = 0 := by simp
  fin_cases who
  · change (rationalLimitRoot 0 false).toReal *
        quittingRootEndpointDifference (rationalReward rationalScale)
          (rayCap 0 0 rationalSpectatorLimit) rationalLimitRoot 0 ≤ 0 ∧
      -0 ≤ (rationalLimitRoot 0 true).toReal *
        quittingRootEndpointDifference (rationalReward rationalScale)
          (rayCap 0 0 rationalSpectatorLimit) rationalLimitRoot 0
    rw [show (0 : Player) = (0 : Fin 3).castSucc by rfl]
    rw [rationalReward_activeRestriction_endpointDifference rationalScale 0 0
      rationalSpectatorLimit rationalLimitRoot hspectator (0 : Fin 3)]
    norm_num [rationalForwardExactCapTail,
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.interaction,
      MaximalRayZeroMinimumActiveRegression.cap, hazardOfRoot,
      activeRestriction, rationalLimitRoot, rootOfHazard,
      Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      show (2 : Fin 3).castSucc = (2 : Player) by rfl]
  · change (rationalLimitRoot 1 false).toReal *
        quittingRootEndpointDifference (rationalReward rationalScale)
          (rayCap 0 0 rationalSpectatorLimit) rationalLimitRoot 1 ≤ 0 ∧
      -0 ≤ (rationalLimitRoot 1 true).toReal *
        quittingRootEndpointDifference (rationalReward rationalScale)
          (rayCap 0 0 rationalSpectatorLimit) rationalLimitRoot 1
    rw [show (1 : Player) = (1 : Fin 3).castSucc by rfl]
    rw [rationalReward_activeRestriction_endpointDifference rationalScale 0 0
      rationalSpectatorLimit rationalLimitRoot hspectator (1 : Fin 3)]
    norm_num [rationalForwardExactCapTail,
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.interaction,
      MaximalRayZeroMinimumActiveRegression.cap, hazardOfRoot,
      activeRestriction, rationalLimitRoot, rootOfHazard,
      Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      show (2 : Fin 3).castSucc = (2 : Player) by rfl]
  · change (rationalLimitRoot 2 false).toReal *
        quittingRootEndpointDifference (rationalReward rationalScale)
          (rayCap 0 0 rationalSpectatorLimit) rationalLimitRoot 2 ≤ 0 ∧
      -0 ≤ (rationalLimitRoot 2 true).toReal *
        quittingRootEndpointDifference (rationalReward rationalScale)
          (rayCap 0 0 rationalSpectatorLimit) rationalLimitRoot 2
    rw [show (2 : Player) = (2 : Fin 3).castSucc by rfl]
    rw [rationalReward_activeRestriction_endpointDifference rationalScale 0 0
      rationalSpectatorLimit rationalLimitRoot hspectator (2 : Fin 3)]
    norm_num [rationalForwardExactCapTail,
      MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.interaction,
      MaximalRayZeroMinimumActiveRegression.cap, hazardOfRoot,
      activeRestriction, rationalLimitRoot, rootOfHazard,
      Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      show (2 : Fin 3).castSucc = (2 : Player) by rfl]
  · change (rationalLimitRoot 3 false).toReal *
        quittingRootEndpointDifference (rationalReward rationalScale)
          (rayCap 0 0 rationalSpectatorLimit) rationalLimitRoot 3 ≤ 0 ∧
      -0 ≤ (rationalLimitRoot 3 true).toReal *
        quittingRootEndpointDifference (rationalReward rationalScale)
          (rayCap 0 0 rationalSpectatorLimit) rationalLimitRoot 3
    rw [rationalReward_spectator_endpointDifference]
    have hneg := spectator_endpointDifference_neg rationalLimitRoot
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) one_le_rationalSpectatorLimit)
    constructor
    · exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hneg.le
    · simp [rationalLimitRoot, rootOfHazard]

theorem rationalLimitRoot_positive :
    0 < ∑ who, quittingRootQuitRates rationalLimitRoot who := by
  simp [quittingRootQuitRates, Fin.sum_univ_four, rationalLimitRoot,
    rootOfHazard]

theorem fullBindingLimitRoot_exactNash :
    IsεQuittingRootNash
      (fullBindingReward fullBindingInitialCap rationalScale)
        fullBindingForwardExactCapTail.capLimit 0 rationalLimitRoot := by
  rw [show fullBindingForwardExactCapTail.capLimit = rayCap 0 0 0 by
    funext who
    fin_cases who <;> rfl]
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  have hspectator : (rationalLimitRoot 3 true).toReal = 0 := by simp
  fin_cases who
  · change (rationalLimitRoot 0 false).toReal *
        quittingRootEndpointDifference
          (fullBindingReward fullBindingInitialCap rationalScale)
            (rayCap 0 0 0) rationalLimitRoot 0 ≤ 0 ∧
      -0 ≤ (rationalLimitRoot 0 true).toReal *
        quittingRootEndpointDifference
          (fullBindingReward fullBindingInitialCap rationalScale)
            (rayCap 0 0 0) rationalLimitRoot 0
    rw [show (0 : Player) = (0 : Fin 3).castSucc by rfl]
    rw [fullBindingReward_activeRestriction_endpointDifference
      fullBindingInitialCap rationalScale 0 0 0 rationalLimitRoot
        hspectator (0 : Fin 3)]
    norm_num [MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.interaction,
      MaximalRayZeroMinimumActiveRegression.cap, hazardOfRoot,
      activeRestriction, rationalLimitRoot, rootOfHazard,
      Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      show (2 : Fin 3).castSucc = (2 : Player) by rfl]
  · change (rationalLimitRoot 1 false).toReal *
        quittingRootEndpointDifference
          (fullBindingReward fullBindingInitialCap rationalScale)
            (rayCap 0 0 0) rationalLimitRoot 1 ≤ 0 ∧
      -0 ≤ (rationalLimitRoot 1 true).toReal *
        quittingRootEndpointDifference
          (fullBindingReward fullBindingInitialCap rationalScale)
            (rayCap 0 0 0) rationalLimitRoot 1
    rw [show (1 : Player) = (1 : Fin 3).castSucc by rfl]
    rw [fullBindingReward_activeRestriction_endpointDifference
      fullBindingInitialCap rationalScale 0 0 0 rationalLimitRoot
        hspectator (1 : Fin 3)]
    norm_num [MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.interaction,
      MaximalRayZeroMinimumActiveRegression.cap, hazardOfRoot,
      activeRestriction, rationalLimitRoot, rootOfHazard,
      Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      show (2 : Fin 3).castSucc = (2 : Player) by rfl]
  · change (rationalLimitRoot 2 false).toReal *
        quittingRootEndpointDifference
          (fullBindingReward fullBindingInitialCap rationalScale)
            (rayCap 0 0 0) rationalLimitRoot 2 ≤ 0 ∧
      -0 ≤ (rationalLimitRoot 2 true).toReal *
        quittingRootEndpointDifference
          (fullBindingReward fullBindingInitialCap rationalScale)
            (rayCap 0 0 0) rationalLimitRoot 2
    rw [show (2 : Player) = (2 : Fin 3).castSucc by rfl]
    rw [fullBindingReward_activeRestriction_endpointDifference
      fullBindingInitialCap rationalScale 0 0 0 rationalLimitRoot
        hspectator (2 : Fin 3)]
    norm_num [MaximalRayZeroMinimumActiveRegression.endpointPolynomial,
      MaximalRayZeroMinimumActiveRegression.interaction,
      MaximalRayZeroMinimumActiveRegression.cap, hazardOfRoot,
      activeRestriction, rationalLimitRoot, rootOfHazard,
      Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      show (2 : Fin 3).castSucc = (2 : Player) by rfl]
  · change (rationalLimitRoot 3 false).toReal *
        quittingRootEndpointDifference
          (fullBindingReward fullBindingInitialCap rationalScale)
            (rayCap 0 0 0) rationalLimitRoot 3 ≤ 0 ∧
      -0 ≤ (rationalLimitRoot 3 true).toReal *
        quittingRootEndpointDifference
          (fullBindingReward fullBindingInitialCap rationalScale)
            (rayCap 0 0 0) rationalLimitRoot 3
    rw [fullBindingReward_spectator_endpointDifference]
    norm_num [activeAbsorption, activeSurvival, rationalLimitRoot,
      rootOfHazard, pmfBool_false_toReal, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- Provenance-rich regression around an actual forward semantic ray. -/
structure Regression
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) where
  ray : QuittingForwardExactCapTail reward
  canonical_root : ∀ time,
    ray.root time = quittingMaximalCapSemanticRoot reward (ray.pair time)
  root_quit_tendsto_zero : ∀ who,
    Tendsto (fun time ↦ quittingRootQuitRates (ray.root time) who)
      atTop (nhds 0)
  limitRoot : Player → PMF Bool
  limitRoot_exactNash : IsεQuittingRootNash reward ray.capLimit 0 limitRoot
  limitRoot_positive : 0 < ∑ who, quittingRootQuitRates limitRoot who
  fragment : LocalForcedPairFragment reward
  pair_zero_eq_fragment : ray.pair 0 =
    quittingTerminalSemanticPair reward fragment.pairProfile
  zero_solo : ∀ who,
    reward (quittingSingletonTerminal who) who = 0

/-- The actual rational regression, including a positive exact root at its
limiting cap. -/
def rationalRegression : Regression (rationalReward rationalScale) where
  ray := rationalForwardExactCapTail
  canonical_root := fun _ ↦ rfl
  root_quit_tendsto_zero := rationalCanonicalRoot_quitRate_tendsto_zero
  limitRoot := rationalLimitRoot
  limitRoot_exactNash := rationalLimitRoot_exactNash
  limitRoot_positive := rationalLimitRoot_positive
  fragment := rationalLocalForcedPairFragment
  pair_zero_eq_fragment := rfl
  zero_solo := rationalReward_singleton_eq_zero

/-- The actual fixed-real full-binding regression before ballistic packaging. -/
def fullBindingRegression : Regression
    (fullBindingReward fullBindingInitialCap rationalScale) where
  ray := fullBindingForwardExactCapTail
  canonical_root := fun _ ↦ rfl
  root_quit_tendsto_zero := fullBindingCanonicalRoot_quitRate_tendsto_zero
  limitRoot := rationalLimitRoot
  limitRoot_exactNash := fullBindingLimitRoot_exactNash
  limitRoot_positive := rationalLimitRoot_positive
  fragment := fullBindingLocalForcedPairFragment fullBindingInitialCap
  pair_zero_eq_fragment := rfl
  zero_solo := fullBindingReward_singleton_eq_zero _

theorem activeTotalHazard_succ_div_tendsto_half :
    Tendsto (fun time ↦ activeTotalHazard (time + 1) /
      activeTotalHazard time) atTop (nhds (1 / 2 : ℝ)) := by
  let orbit := MaximalRayZeroMinimumActiveRegression.explicitRecurrence
    rationalScale rationalScale_pos rationalScale_lt_fiftieth
  have hratio := orbit.totalHazard_succ_div_tendsto_half
  simpa [orbit, activeTotalHazard, activeData, activeState,
    MaximalRayZeroMinimumActiveRegression.Recurrence.totalHazard,
    MaximalRayZeroMinimumActiveRegression.explicitRecurrence] using hratio

theorem activeRenewalRatio_tendsto_half :
    Tendsto (fun time ↦ activeTotalHazard time /
      ∑' offset, activeTotalHazard (time + offset)) atTop
      (nhds (1 / 2 : ℝ)) :=
  MaximalRayZeroMinimumActiveRegression.Recurrence.tendsto_self_div_tailSum_half_of_ratio
    activeTotalHazard
    activeTotalHazard_pos activeTotalHazard_summable
    activeTotalHazard_succ_div_tendsto_half

theorem fullBindingRenewalRatio_tendsto_half :
    Tendsto fullBindingForwardExactCapTail.renewalRatio atTop
      (nhds (1 / 2 : ℝ)) := by
  convert activeRenewalRatio_tendsto_half using 1
  funext time
  unfold QuittingForwardExactCapTail.renewalRatio
    QuittingForwardExactCapTail.tailMass
    QuittingForwardExactCapTail.totalHazard
  congr 1
  · change (∑ who, quittingRootQuitRates
        (quittingMaximalCapSemanticRoot
          (fullBindingReward fullBindingInitialCap rationalScale)
            (fullBindingSemanticOrbit time)) who) = activeTotalHazard time
    rw [fullBindingCanonicalRoot_eq]
    simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates, Fin.sum_univ_four, activeTotalHazard]
    ring
  · congr 1
    funext offset
    change (∑ who, quittingRootQuitRates
        (quittingMaximalCapSemanticRoot
          (fullBindingReward fullBindingInitialCap rationalScale)
            (fullBindingSemanticOrbit (time + offset))) who) =
      activeTotalHazard (time + offset)
    rw [fullBindingCanonicalRoot_eq]
    simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
      quittingRootQuitRates, Fin.sum_univ_four, activeTotalHazard]
    ring

namespace Regression

/-- The initial selected root is exactly the maximal selector at the literal
pair carried by the local fragment. -/
theorem root_zero_eq_fragment
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) :
    regression.ray.root 0 = quittingMaximalCapSemanticRoot reward
      (quittingTerminalSemanticPair reward regression.fragment.pairProfile) := by
  rw [regression.canonical_root, regression.pair_zero_eq_fragment]

/-- Literal all-Never semantic pair. -/
def neverPair
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (_regression : Regression reward) : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair reward (quittingAlwaysContinueProfile reward)

theorem neverPair_eq_zero
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) :
    regression.neverPair = ((0 : Payoff Player), (0 : Payoff Player)) := by
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_quittingAlwaysContinue reward who
  · funext who
    rw [show regression.neverPair.2 who =
        quittingContinuationBestResponseValue reward
          (quittingAlwaysContinueProfile reward) who by rfl,
      quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      regression.zero_solo who]
    norm_num

theorem neverPair_mem
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) :
    regression.neverPair ∈ quittingTerminalSemanticCarrier reward := by
  apply subset_closure
  exact ⟨quittingAlwaysContinueProfile reward, rfl⟩

theorem neverPair_debtSum_eq_zero
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) :
    quittingTerminalSemanticDebtSum regression.neverPair = 0 := by
  rw [regression.neverPair_eq_zero]
  simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt]

/-- The regression table is literally in the zero-solo class. -/
theorem isZeroSolo
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) : IsQuittingZeroSolo reward := by
  intro who
  rw [regression.zero_solo who]

/-- The all-Never profile is an exact terminal Nash profile for every stored
zero-minimum regression table. -/
theorem neverTerminalNash
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingAlwaysContinueProfile reward) :=
  isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo reward
    regression.isZeroSolo

/-- The literal all-Never prescribed payoff is the zero vector. -/
theorem neverTerminalPayoff_eq_zero
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (_regression : Regression reward) :
    quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) =
      (0 : Payoff Player) :=
  funext fun who => quittingTerminalPayoff_quittingAlwaysContinue reward who

/-- The zero-debt all-Never semantic point is a global minimum on the whole
terminal-semantic carrier. -/
theorem neverPair_globalMinimum
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward)
    (candidate : QuittingTerminalSemanticPair Player)
    (hcandidate : candidate ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticDebtSum regression.neverPair ≤
      quittingTerminalSemanticDebtSum candidate := by
  rw [regression.neverPair_debtSum_eq_zero]
  exact Finset.sum_nonneg fun who _ =>
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hcandidate who

/-- The all-Never zero payoff is a literal behavioral uniform-equilibrium
payoff for every stored regression table. -/
theorem neverUniformEquilibriumPayoff
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (0 : Payoff Player) :=
  quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo
    reward regression.isZeroSolo

/-- Zero debt at the literal all-Never pair rules out every positive-minimum
Fin4 source for the same reward table. -/
theorem not_nonempty_minimumAtomProducer
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (regression : Regression reward) (bound : ℝ) :
    ¬ Nonempty (FinFourMinimumAtomProducer reward bound) := by
  rintro ⟨source⟩
  have hminimum := source.minimum regression.neverPair regression.neverPair_mem
  rw [regression.neverPair_debtSum_eq_zero] at hminimum
  linarith [source.minimumDebt_pos]

end Regression

/-- Owner `2` is a literal pure singleton chamber for the rational table. -/
theorem rationalPureSingletonChamber :
    QuittingPureSingletonChamber (rationalReward rationalScale) (2 : Player) where
  owner_no_leave := by
    simp +decide [quittingSoloReward, rationalReward,
      activeBaseReward, passive, interaction]
  outsider_no_join := by
    intro other hother
    fin_cases other <;>
      simp_all +decide [quittingSingletonCollisionReward, quittingSoloReward,
        rationalReward, rationalSpectatorReward, activeBaseReward, passive,
        interaction]

/-- The rational regression table therefore has a literal behavioral
uniform-equilibrium payoff at the pure singleton owned by player `2`. -/
theorem rationalPureSingleton_uniformEquilibriumPayoff :
    (quittingGame (rationalReward rationalScale)).IsUniformEquilibriumPayoff none
      (quittingSetReward (rationalReward rationalScale) ({2} : Finset Player)) :=
  rationalPureSingletonChamber.uniformEquilibriumPayoff

/-- Owner `2` remains a pure singleton chamber for every full-binding
spectator completion. -/
theorem fullBindingPureSingletonChamber (R : ℝ) :
    QuittingPureSingletonChamber
      (fullBindingReward R rationalScale) (2 : Player) where
  owner_no_leave := by
    simp +decide [quittingSoloReward, fullBindingReward, rationalReward,
      activeBaseReward, passive, interaction]
  outsider_no_join := by
    intro other hother
    fin_cases other <;>
      simp_all +decide [quittingSingletonCollisionReward, quittingSoloReward,
        fullBindingReward, fullBindingSpectatorReward,
        fullBindingSpectatorCoefficient, rationalReward,
        activeBaseReward, passive, interaction]

/-- Every full-binding regression table has the corresponding literal
behavioral uniform-equilibrium payoff at the same pure singleton. -/
theorem fullBindingPureSingleton_uniformEquilibriumPayoff (R : ℝ) :
    (quittingGame (fullBindingReward R rationalScale)).IsUniformEquilibriumPayoff
      none
      (quittingSetReward (fullBindingReward R rationalScale)
        ({2} : Finset Player)) :=
  (fullBindingPureSingletonChamber R).uniformEquilibriumPayoff

/-- Rational card-three completion certificate. -/
structure RationalCardThree where
  regression : Regression (rationalReward rationalScale)
  binding_eq : regression.ray.bindingFinset = {0, 1, 2}
  current_support : ∀ time who,
    0 < quittingRootQuitRates (regression.ray.root time) who ↔ who ≠ 3

/-- Fully constructed rational card-three maximal-ray regression. -/
def rationalCardThree : RationalCardThree where
  regression := rationalRegression
  binding_eq := by
    ext who
    fin_cases who <;>
      simp [rationalRegression, rationalForwardExactCapTail,
        QuittingForwardExactCapTail.bindingFinset,
        rationalReward_singleton_eq_zero]
    exact ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) one_le_rationalSpectatorLimit)
  current_support := by
    intro time who
    rw [show rationalRegression.ray.root time =
        LiftedActiveRoot.root (activeData time) (activeState time).a_pos by
      exact rationalCanonicalRoot_eq time]
    fin_cases who <;>
      simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
        quittingRootQuitRates,
        (activeData time).t_pos (activeState time).a_pos,
        (activeData time).z_pos]

namespace RationalCardThree

theorem binding_card (certificate : RationalCardThree) :
    certificate.regression.ray.bindingFinset.card = 3 := by
  rw [certificate.binding_eq]
  decide

theorem currentSupport_eq (certificate : RationalCardThree) (time : ℕ) :
    Finset.univ.filter (fun who ↦
      0 < quittingRootQuitRates (certificate.regression.ray.root time) who) =
      {0, 1, 2} := by
  ext who
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [certificate.current_support]
  fin_cases who <;> simp

theorem currentSupport_card (certificate : RationalCardThree) (time : ℕ) :
    (Finset.univ.filter (fun who ↦
      0 < quittingRootQuitRates
        (certificate.regression.ray.root time) who)).card = 3 := by
  rw [certificate.currentSupport_eq]
  decide

end RationalCardThree

/-- Fixed-real full-binding, partial-current-support, ballistic completion
certificate. -/
structure FullBindingBallistic where
  R : ℝ
  R_pos : 0 < R
  regression : Regression (fullBindingReward R rationalScale)
  binding_eq : regression.ray.bindingFinset = Finset.univ
  current_support : ∀ time who,
    0 < quittingRootQuitRates (regression.ray.root time) who ↔ who ≠ 3
  renewalRatio_tendsto_half : Tendsto regression.ray.renewalRatio
    atTop (nhds (1 / 2 : ℝ))

/-- Fully constructed full-binding, partial-support ballistic regression. -/
def fullBindingBallistic : FullBindingBallistic where
  R := fullBindingInitialCap
  R_pos := fullBindingInitialCap_pos
  regression := fullBindingRegression
  binding_eq := by
    ext who
    simp [fullBindingRegression, fullBindingForwardExactCapTail,
      QuittingForwardExactCapTail.bindingFinset,
      fullBindingReward_singleton_eq_zero]
  current_support := by
    intro time who
    rw [show fullBindingRegression.ray.root time =
        LiftedActiveRoot.root (activeData time) (activeState time).a_pos by
      exact fullBindingCanonicalRoot_eq time]
    fin_cases who <;>
      simp [LiftedActiveRoot.root, LiftedActiveRoot.hazard, rootOfHazard,
        quittingRootQuitRates,
        (activeData time).t_pos (activeState time).a_pos,
        (activeData time).z_pos]
  renewalRatio_tendsto_half := fullBindingRenewalRatio_tendsto_half

namespace FullBindingBallistic

theorem binding_card (certificate : FullBindingBallistic) :
    certificate.regression.ray.bindingFinset.card = 4 := by
  rw [certificate.binding_eq]
  simp

theorem currentSupport_card
    (certificate : FullBindingBallistic) (time : ℕ) :
    (Finset.univ.filter (fun who ↦
      0 < quittingRootQuitRates
        (certificate.regression.ray.root time) who)).card = 3 := by
  have heq : Finset.univ.filter (fun who ↦
      0 < quittingRootQuitRates
        (certificate.regression.ray.root time) who) =
      {0, 1, 2} := by
    ext who
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [certificate.current_support]
    fin_cases who <;> simp
  rw [heq]
  decide

end FullBindingBallistic

end FinFourMaximalRayZeroMinimumRegressions

end GameTheory
