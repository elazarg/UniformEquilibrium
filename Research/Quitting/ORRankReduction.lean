/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.Basic
import Math.PMFProduct.CoalitionMass
import Mathlib.Tactic

/-!
# Local OR rank reduction for five-player quitting roots

This experiment formalizes the exact local compiler suggested by the
five-cycle reset geometry.

At one independent product root, merge a spectator button and a host button
by OR.  Conditional averaging of the three active hidden causes preserves:

* the push-forward prescribed outcome law;
* the prescribed value of every retained payoff coordinate; and
* both pure unilateral action values, hence best-response debt, for every
  player other than the merged host.

Thus `5 -> 4` has an exact local `1 + 3` form.  The common-product survival
calculus places all slope mismatch in the host coordinate.  The hidden-cause
law satisfies an exact rank-one determinant, which shows why one fixed
interior conditional law covers only one host marginal.

The file also proves three pieces of the exceptional five-cycle geometry:

* the pentagon and pentagram merger schedules retain exactly `3/5` of every
  debt vector on their protected triples, hence `3/4` of uniform audit after
  four-player normalization;
* consecutive merger edges have one host, two stable auditors, and one
  endpoint-exchange role; and
* the two quotient charts differ by the Weyl reflection swapping the path
  endpoints, while the two transfer roots contract exactly.

## Deliberate fence

Nothing here constructs one fixed four-player quitting reward table for all
target profiles.  The conditional target rewards depend on the source root
unless the hidden-cause law is constant or degenerate.  Nor does the
phase-average `3/4` bound commute an infimum over five different target
tables.  Consequently this file does not inhabit
`RandomDeviationAudit.UniformScoreReduction` and does not prove cardinal
reduction.  The remaining producer is fixed-table, profilewise
stationarization (or a positive charge for its failure).
-/

noncomputable section

namespace Research.QuittingORRankReduction

open GameTheory
open scoped BigOperators

/-! ## The hidden two-button OR experiment -/

/-- Quit probability of the OR of two independent Bernoulli buttons. -/
def orQuit (spectatorQuit hostQuit : ℝ) : ℝ :=
  spectatorQuit + hostQuit - spectatorQuit * hostQuit

/-- Expectation of a scalar payoff over two independent Boolean buttons.
The first Boolean is the spectator and the second is the host. -/
def pairExpectation (spectatorQuit hostQuit : ℝ)
    (value : Bool → Bool → ℝ) : ℝ :=
  (1 - spectatorQuit) * (1 - hostQuit) * value false false +
    spectatorQuit * (1 - hostQuit) * value true false +
    (1 - spectatorQuit) * hostQuit * value false true +
    spectatorQuit * hostQuit * value true true

/-- Expectation over the single OR button. -/
def orExpectation (spectatorQuit hostQuit : ℝ)
    (value : Bool → ℝ) : ℝ :=
  (1 - orQuit spectatorQuit hostQuit) * value false +
    orQuit spectatorQuit hostQuit * value true

theorem one_sub_orQuit (spectatorQuit hostQuit : ℝ) :
    1 - orQuit spectatorQuit hostQuit =
      (1 - spectatorQuit) * (1 - hostQuit) := by
  unfold orQuit
  ring

/-- The OR button has exactly the push-forward law of the two independent
buttons.  This test-function formulation is the complete finite-law
statement. -/
theorem pairExpectation_comp_or
    (spectatorQuit hostQuit : ℝ) (value : Bool → ℝ) :
    pairExpectation spectatorQuit hostQuit
        (fun spectator host => value (spectator || host)) =
      orExpectation spectatorQuit hostQuit value := by
  simp [pairExpectation, orExpectation, orQuit]
  ring

/-- Conditional reward of the merged button.  On the active OR atom it is
the weighted mean of spectator-only, host-only, and joint activation. -/
def orConditionalReward (spectatorQuit hostQuit : ℝ)
    (value : Bool → Bool → ℝ) (merged : Bool) : ℝ :=
  if merged then
    (spectatorQuit * (1 - hostQuit) * value true false +
      (1 - spectatorQuit) * hostQuit * value false true +
      spectatorQuit * hostQuit * value true true) /
        orQuit spectatorQuit hostQuit
  else
    value false false

/-- Conditional averaging preserves the prescribed scalar value exactly at
every nondegenerate OR root. -/
theorem pairExpectation_eq_orExpectation_conditional
    (spectatorQuit hostQuit : ℝ) (value : Bool → Bool → ℝ)
    (hactive : orQuit spectatorQuit hostQuit ≠ 0) :
    pairExpectation spectatorQuit hostQuit value =
      orExpectation spectatorQuit hostQuit
        (orConditionalReward spectatorQuit hostQuit value) := by
  unfold pairExpectation
  simp only [orExpectation, orConditionalReward, Bool.false_eq_true, ↓reduceIte]
  rw [one_sub_orQuit]
  field_simp [hactive]
  ring

/-! ## Exact preservation of a protected unilateral audit -/

/-- Source action value for a protected player.  Its own Boolean action is
outside the hidden spectator/host experiment. -/
def protectedSourceActionValue (spectatorQuit hostQuit : ℝ)
    (value : Bool → Bool → Bool → ℝ) (own : Bool) : ℝ :=
  pairExpectation spectatorQuit hostQuit (value own)

/-- Target action value after replacing spectator/host by their OR button. -/
def protectedTargetActionValue (spectatorQuit hostQuit : ℝ)
    (value : Bool → Bool → Bool → ℝ) (own : Bool) : ℝ :=
  orExpectation spectatorQuit hostQuit
    (orConditionalReward spectatorQuit hostQuit (value own))

theorem protectedActionValue_eq
    (spectatorQuit hostQuit : ℝ)
    (value : Bool → Bool → Bool → ℝ)
    (hactive : orQuit spectatorQuit hostQuit ≠ 0) (own : Bool) :
    protectedSourceActionValue spectatorQuit hostQuit value own =
      protectedTargetActionValue spectatorQuit hostQuit value own := by
  exact pairExpectation_eq_orExpectation_conditional
    spectatorQuit hostQuit (value own) hactive

/-- Prescribed mixture of Continue (`false`) and Quit (`true`). -/
def prescribedBinaryValue (ownQuit : ℝ) (value : Bool → ℝ) : ℝ :=
  (1 - ownQuit) * value false + ownQuit * value true

/-- Best value among the two pure endpoint actions. -/
def bestBinaryValue (value : Bool → ℝ) : ℝ :=
  max (value false) (value true)

/-- One-row endpoint debt. -/
def binaryDebt (ownQuit : ℝ) (value : Bool → ℝ) : ℝ :=
  bestBinaryValue value - prescribedBinaryValue ownQuit value

theorem protectedPrescribedValue_eq
    (spectatorQuit hostQuit ownQuit : ℝ)
    (value : Bool → Bool → Bool → ℝ)
    (hactive : orQuit spectatorQuit hostQuit ≠ 0) :
    prescribedBinaryValue ownQuit
        (protectedSourceActionValue spectatorQuit hostQuit value) =
      prescribedBinaryValue ownQuit
        (protectedTargetActionValue spectatorQuit hostQuit value) := by
  unfold prescribedBinaryValue
  rw [protectedActionValue_eq spectatorQuit hostQuit value hactive false,
    protectedActionValue_eq spectatorQuit hostQuit value hactive true]

theorem protectedBestValue_eq
    (spectatorQuit hostQuit : ℝ)
    (value : Bool → Bool → Bool → ℝ)
    (hactive : orQuit spectatorQuit hostQuit ≠ 0) :
    bestBinaryValue
        (protectedSourceActionValue spectatorQuit hostQuit value) =
      bestBinaryValue
        (protectedTargetActionValue spectatorQuit hostQuit value) := by
  unfold bestBinaryValue
  rw [protectedActionValue_eq spectatorQuit hostQuit value hactive false,
    protectedActionValue_eq spectatorQuit hostQuit value hactive true]

/-- **Protected-audit theorem.**  OR compression preserves the complete
one-row unilateral endpoint debt of every non-host player. -/
theorem protectedDebt_eq
    (spectatorQuit hostQuit ownQuit : ℝ)
    (value : Bool → Bool → Bool → ℝ)
    (hactive : orQuit spectatorQuit hostQuit ≠ 0) :
    binaryDebt ownQuit
        (protectedSourceActionValue spectatorQuit hostQuit value) =
      binaryDebt ownQuit
        (protectedTargetActionValue spectatorQuit hostQuit value) := by
  unfold binaryDebt
  rw [protectedBestValue_eq spectatorQuit hostQuit value hactive,
    protectedPrescribedValue_eq spectatorQuit hostQuit ownQuit value hactive]

/-- The three protected coordinates of a `1 + 3` compression, bundled as one
debt vector. -/
def threeProtectedSourceDebt
    (spectatorQuit hostQuit : ℝ) (ownQuit : Fin 3 → ℝ)
    (value : Fin 3 → Bool → Bool → Bool → ℝ) : Fin 3 → ℝ :=
  fun who => binaryDebt (ownQuit who)
    (protectedSourceActionValue spectatorQuit hostQuit (value who))

def threeProtectedTargetDebt
    (spectatorQuit hostQuit : ℝ) (ownQuit : Fin 3 → ℝ)
    (value : Fin 3 → Bool → Bool → Bool → ℝ) : Fin 3 → ℝ :=
  fun who => binaryDebt (ownQuit who)
    (protectedTargetActionValue spectatorQuit hostQuit (value who))

/-- **Exact local `1 + 3` theorem.**  One OR host may be exceptional, but
all three other unilateral endpoint debts are preserved simultaneously. -/
theorem threeProtectedDebt_eq
    (spectatorQuit hostQuit : ℝ) (ownQuit : Fin 3 → ℝ)
    (value : Fin 3 → Bool → Bool → Bool → ℝ)
    (hactive : orQuit spectatorQuit hostQuit ≠ 0) :
    threeProtectedSourceDebt spectatorQuit hostQuit ownQuit value =
      threeProtectedTargetDebt spectatorQuit hostQuit ownQuit value := by
  funext who
  exact protectedDebt_eq spectatorQuit hostQuit (ownQuit who) (value who)
    hactive

theorem sum_threeProtectedDebt_eq
    (spectatorQuit hostQuit : ℝ) (ownQuit : Fin 3 → ℝ)
    (value : Fin 3 → Bool → Bool → Bool → ℝ)
    (hactive : orQuit spectatorQuit hostQuit ≠ 0) :
    ∑ who, threeProtectedSourceDebt spectatorQuit hostQuit ownQuit value who =
      ∑ who, threeProtectedTargetDebt spectatorQuit hostQuit ownQuit value who := by
  rw [threeProtectedDebt_eq spectatorQuit hostQuit ownQuit value hactive]

/-! ## Retained boundary holonomy is an exact semigroup quotient -/

variable {ι κ : Type}

/-- Forget boundary-holonomy coordinates outside the image of `embedding`. -/
def restrictBoundaryHolonomy (embedding : κ → ι)
    (holonomy : QuittingBoundaryHolonomy ι) :
    QuittingBoundaryHolonomy κ where
  prescribed who := holonomy.prescribed (embedding who)
  bestResponse who := holonomy.bestResponse (embedding who)

@[simp] theorem restrictBoundaryHolonomy_mul
    (embedding : κ → ι) (outer inner : QuittingBoundaryHolonomy ι) :
    restrictBoundaryHolonomy embedding (outer * inner) =
      restrictBoundaryHolonomy embedding outer *
        restrictBoundaryHolonomy embedding inner := by
  rfl

@[simp] theorem restrictBoundaryHolonomy_gap
    (embedding : κ → ι) (holonomy : QuittingBoundaryHolonomy ι)
    (who : κ) (debt terminalValue : ℝ) :
    (restrictBoundaryHolonomy embedding holonomy).gap who debt terminalValue =
      holonomy.gap (embedding who) debt terminalValue := by
  rfl

/-! ## The common-product survival mismatch is one host coordinate -/

/-- Cumulative Continue factors for spectator, host, exchange, and the two
stable auditors. -/
structure FiveContinueFactors where
  spectator : ℝ
  host : ℝ
  exchange : ℝ
  auditorA : ℝ
  auditorB : ℝ

namespace FiveContinueFactors

def sourcePrescribed (C : FiveContinueFactors) : ℝ :=
  C.spectator * C.host * C.exchange * C.auditorA * C.auditorB

def targetPrescribed (C : FiveContinueFactors) : ℝ :=
  (C.spectator * C.host) * C.exchange * C.auditorA * C.auditorB

def sourceExchangeSlope (C : FiveContinueFactors) : ℝ :=
  C.spectator * C.host * C.auditorA * C.auditorB

def targetExchangeSlope (C : FiveContinueFactors) : ℝ :=
  (C.spectator * C.host) * C.auditorA * C.auditorB

def sourceAuditorASlope (C : FiveContinueFactors) : ℝ :=
  C.spectator * C.host * C.exchange * C.auditorB

def targetAuditorASlope (C : FiveContinueFactors) : ℝ :=
  (C.spectator * C.host) * C.exchange * C.auditorB

def sourceAuditorBSlope (C : FiveContinueFactors) : ℝ :=
  C.spectator * C.host * C.exchange * C.auditorA

def targetAuditorBSlope (C : FiveContinueFactors) : ℝ :=
  (C.spectator * C.host) * C.exchange * C.auditorA

def sourceHostSlope (C : FiveContinueFactors) : ℝ :=
  C.spectator * C.exchange * C.auditorA * C.auditorB

def targetHostSlope (C : FiveContinueFactors) : ℝ :=
  C.exchange * C.auditorA * C.auditorB

theorem targetPrescribed_eq_source (C : FiveContinueFactors) :
    C.targetPrescribed = C.sourcePrescribed := by
  simp [targetPrescribed, sourcePrescribed]

theorem targetExchangeSlope_eq_source (C : FiveContinueFactors) :
    C.targetExchangeSlope = C.sourceExchangeSlope := by
  simp [targetExchangeSlope, sourceExchangeSlope]

theorem targetAuditorASlope_eq_source (C : FiveContinueFactors) :
    C.targetAuditorASlope = C.sourceAuditorASlope := by
  simp [targetAuditorASlope, sourceAuditorASlope]

theorem targetAuditorBSlope_eq_source (C : FiveContinueFactors) :
    C.targetAuditorBSlope = C.sourceAuditorBSlope := by
  simp [targetAuditorBSlope, sourceAuditorBSlope]

/-- The exceptional host loses precisely the spectator survival factor. -/
theorem spectator_mul_targetHostSlope_eq_source
    (C : FiveContinueFactors) :
    C.spectator * C.targetHostSlope = C.sourceHostSlope := by
  simp only [targetHostSlope, sourceHostSlope]
  ring

end FiveContinueFactors

/-! ## Independence curvature of the hidden-cause law -/

def hiddenNeither (spectatorQuit hostQuit : ℝ) : ℝ :=
  (1 - spectatorQuit) * (1 - hostQuit)

def hiddenSpectatorOnly (spectatorQuit hostQuit : ℝ) : ℝ :=
  spectatorQuit * (1 - hostQuit)

def hiddenHostOnly (spectatorQuit hostQuit : ℝ) : ℝ :=
  (1 - spectatorQuit) * hostQuit

def hiddenJoint (spectatorQuit hostQuit : ℝ) : ℝ :=
  spectatorQuit * hostQuit

/-- The four hidden atoms of two independent buttons have rank one. -/
theorem hidden_independence_determinant
    (spectatorQuit hostQuit : ℝ) :
    hiddenNeither spectatorQuit hostQuit *
        hiddenJoint spectatorQuit hostQuit =
      hiddenSpectatorOnly spectatorQuit hostQuit *
        hiddenHostOnly spectatorQuit hostQuit := by
  simp only [hiddenNeither, hiddenJoint, hiddenSpectatorOnly, hiddenHostOnly]
  ring

/-- In merged coordinates, independence is the displayed slice equation. -/
theorem merged_independence_equation
    (spectatorQuit hostQuit : ℝ)
    (_hactive : orQuit spectatorQuit hostQuit ≠ 0) :
    (1 - orQuit spectatorQuit hostQuit) *
        (hiddenJoint spectatorQuit hostQuit /
          orQuit spectatorQuit hostQuit) =
      orQuit spectatorQuit hostQuit *
        (hiddenSpectatorOnly spectatorQuit hostQuit /
          orQuit spectatorQuit hostQuit) *
        (hiddenHostOnly spectatorQuit hostQuit /
          orQuit spectatorQuit hostQuit) := by
  unfold hiddenJoint hiddenSpectatorOnly hiddenHostOnly orQuit
  field_simp [_hactive]
  ring

/-- A fixed interior conditional three-cause law determines the merged host
marginal uniquely. -/
theorem hostMarginal_eq_of_independence
    (merged spectatorOnly hostOnly joint : ℝ)
    (hdenom : joint + spectatorOnly * hostOnly ≠ 0)
    (hindependence : (1 - merged) * joint =
      merged * spectatorOnly * hostOnly) :
    merged = joint / (joint + spectatorOnly * hostOnly) := by
  apply (eq_div_iff hdenom).2
  nlinarith

theorem hostMarginal_unique_of_fixed_hiddenLaw
    (first second spectatorOnly hostOnly joint : ℝ)
    (hdenom : joint + spectatorOnly * hostOnly ≠ 0)
    (hfirst : (1 - first) * joint =
      first * spectatorOnly * hostOnly)
    (hsecond : (1 - second) * joint =
      second * spectatorOnly * hostOnly) :
    first = second := by
  rw [hostMarginal_eq_of_independence first spectatorOnly hostOnly joint
      hdenom hfirst,
    hostMarginal_eq_of_independence second spectatorOnly hostOnly joint
      hdenom hsecond]

/-- If the joint hidden cause vanishes at a positive merged marginal, an
independent lift has at most one positive singleton cause: this is the exact
deletion degeneration. -/
theorem deletionDegeneration_of_joint_eq_zero
    (merged spectatorOnly hostOnly joint : ℝ)
    (hmerged : merged ≠ 0) (hjoint : joint = 0)
    (hindependence : (1 - merged) * joint =
      merged * spectatorOnly * hostOnly) :
    spectatorOnly = 0 ∨ hostOnly = 0 := by
  rw [hjoint, mul_zero] at hindependence
  have hproduct : spectatorOnly * hostOnly = 0 := by
    have hfactor : merged * (spectatorOnly * hostOnly) = 0 := by
      simpa [mul_assoc] using hindependence.symm
    exact (mul_eq_zero.mp hfactor).resolve_left hmerged
  exact mul_eq_zero.mp hproduct

/-! ## Balanced five-cycle merger designs -/

/-- Total five-coordinate debt. -/
def totalFiveDebt (debt : Fin 5 → ℝ) : ℝ :=
  ∑ who, debt who

/-- Protected debt after merging edge `{t,t+1}` of the pentagon. -/
def pentagonProtectedDebt (debt : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![debt 2 + debt 3 + debt 4,
    debt 0 + debt 3 + debt 4,
    debt 0 + debt 1 + debt 4,
    debt 0 + debt 1 + debt 2,
    debt 1 + debt 2 + debt 3]

/-- Protected debt after merging edge `{t,t+2}` of the pentagram. -/
def pentagramProtectedDebt (debt : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![debt 1 + debt 3 + debt 4,
    debt 0 + debt 2 + debt 4,
    debt 0 + debt 1 + debt 3,
    debt 1 + debt 2 + debt 4,
    debt 0 + debt 2 + debt 3]

/-- Every debt coordinate is protected in exactly three pentagon phases. -/
theorem sum_pentagonProtectedDebt (debt : Fin 5 → ℝ) :
    ∑ phase, pentagonProtectedDebt debt phase = 3 * totalFiveDebt debt := by
  simp [pentagonProtectedDebt, totalFiveDebt, Fin.sum_univ_succ]
  ring

/-- Every debt coordinate is protected in exactly three pentagram phases. -/
theorem sum_pentagramProtectedDebt (debt : Fin 5 → ℝ) :
    ∑ phase, pentagramProtectedDebt debt phase = 3 * totalFiveDebt debt := by
  simp [pentagramProtectedDebt, totalFiveDebt, Fin.sum_univ_succ]
  ring

def sourceUniformAudit (debt : Fin 5 → ℝ) : ℝ :=
  totalFiveDebt debt / 5

def targetUniformAudit (retained hostDebt : ℝ) : ℝ :=
  (retained + hostDebt) / 4

def fivePhaseAverage (score : Fin 5 → ℝ) : ℝ :=
  (∑ phase, score phase) / 5

/-- The pentagon merger schedule retains at least `3/4` of the source
uniform audit, using only nonnegativity of each exceptional host debt. -/
theorem three_fourths_sourceAudit_le_pentagonAverage
    (debt hostDebt : Fin 5 → ℝ)
    (hhost : ∀ phase, 0 ≤ hostDebt phase) :
    (3 / 4 : ℝ) * sourceUniformAudit debt ≤
      fivePhaseAverage (fun phase =>
        targetUniformAudit (pentagonProtectedDebt debt phase)
          (hostDebt phase)) := by
  have hhostSum : 0 ≤ ∑ phase, hostDebt phase :=
    Finset.sum_nonneg fun phase _ => hhost phase
  have hscore :
      fivePhaseAverage (fun phase =>
          targetUniformAudit (pentagonProtectedDebt debt phase)
            (hostDebt phase)) =
        (3 * totalFiveDebt debt + ∑ phase, hostDebt phase) / 20 := by
    simp [fivePhaseAverage, targetUniformAudit, totalFiveDebt,
      pentagonProtectedDebt, Fin.sum_univ_succ]
    ring
  rw [hscore]
  unfold sourceUniformAudit
  nlinarith

/-- The complementary pentagram schedule has the same exact factor. -/
theorem three_fourths_sourceAudit_le_pentagramAverage
    (debt hostDebt : Fin 5 → ℝ)
    (hhost : ∀ phase, 0 ≤ hostDebt phase) :
    (3 / 4 : ℝ) * sourceUniformAudit debt ≤
      fivePhaseAverage (fun phase =>
        targetUniformAudit (pentagramProtectedDebt debt phase)
          (hostDebt phase)) := by
  have hhostSum : 0 ≤ ∑ phase, hostDebt phase :=
    Finset.sum_nonneg fun phase _ => hhost phase
  have hscore :
      fivePhaseAverage (fun phase =>
          targetUniformAudit (pentagramProtectedDebt debt phase)
            (hostDebt phase)) =
        (3 * totalFiveDebt debt + ∑ phase, hostDebt phase) / 20 := by
    simp [fivePhaseAverage, targetUniformAudit, totalFiveDebt,
      pentagramProtectedDebt, Fin.sum_univ_succ]
    ring
  rw [hscore]
  unfold sourceUniformAudit
  nlinarith

/-! ## Consecutive quotient charts and root reflection -/

/-- First chart: merge source labels `0,1`; retain `2,3,4` as `X,A,B`. -/
def firstChartRole : Fin 5 → Fin 4 :=
  ![0, 0, 1, 2, 3]

/-- Consecutive chart: merge source labels `1,2`; retain `0,3,4`. -/
def secondChartRole : Fin 5 → Fin 4 :=
  ![1, 0, 0, 2, 3]

/-- Weyl reflection swapping the two endpoints of `0 -> 1 -> 2`. -/
def endpointSwap : Fin 5 → Fin 5 :=
  ![2, 1, 0, 3, 4]

@[simp] theorem endpointSwap_involutive (who : Fin 5) :
    endpointSwap (endpointSwap who) = who := by
  fin_cases who <;> rfl

/-- The two four-role charts differ by exactly the endpoint reflection. -/
theorem secondChartRole_eq_firstChartRole_endpointSwap (who : Fin 5) :
    secondChartRole who = firstChartRole (endpointSwap who) := by
  fin_cases who <;> rfl

def firstChartCoalition (coalition : Finset (Fin 5)) : Finset (Fin 4) :=
  coalition.image firstChartRole

def secondChartCoalition (coalition : Finset (Fin 5)) : Finset (Fin 4) :=
  coalition.image secondChartRole

def reflectCoalition (coalition : Finset (Fin 5)) : Finset (Fin 5) :=
  coalition.image endpointSwap

/-- Exact commutative quotient diagram `pi₂ = pi₁ o tau`. -/
theorem secondChartCoalition_eq_firstChartCoalition_reflect
    (coalition : Finset (Fin 5)) :
    secondChartCoalition coalition =
      firstChartCoalition (reflectCoalition coalition) := by
  unfold secondChartCoalition firstChartCoalition reflectCoalition
  rw [Finset.image_image]
  apply Finset.image_congr
  intro who hwho
  exact secondChartRole_eq_firstChartRole_endpointSwap who

/-- Signed coordinate root for a directed debt transfer. -/
def transferRoot (source target : Fin 5) (who : Fin 5) : ℝ :=
  if who = target then 1 else if who = source then -1 else 0

/-- The common host cancels under two-edge root contraction. -/
theorem two_edge_transferRoot_contraction :
    (fun who => transferRoot 0 1 who + transferRoot 1 2 who) =
      transferRoot 0 2 := by
  funext who
  fin_cases who <;> simp [transferRoot]

/-- The endpoint reflection reverses the contracted root. -/
theorem endpointSwap_reverses_contractedRoot (who : Fin 5) :
    transferRoot 0 2 (endpointSwap who) = -transferRoot 0 2 who := by
  fin_cases who <;> simp [transferRoot, endpointSwap]

def reflectCoordinate (value : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun who => value (endpointSwap who)

def reflectionEven (value : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun who => (value who + reflectCoordinate value who) / 2

def reflectionOdd (value : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun who => (value who - reflectCoordinate value who) / 2

theorem reflectionEven_add_reflectionOdd (value : Fin 5 → ℝ) :
    (fun who => reflectionEven value who + reflectionOdd value who) = value := by
  funext who
  simp only [reflectionEven, reflectionOdd]
  ring

theorem reflectCoordinate_reflectionEven (value : Fin 5 → ℝ) :
    reflectCoordinate (reflectionEven value) = reflectionEven value := by
  funext who
  simp [reflectCoordinate, reflectionEven]
  ring

theorem reflectCoordinate_reflectionOdd (value : Fin 5 → ℝ) :
    reflectCoordinate (reflectionOdd value) =
      fun who => -reflectionOdd value who := by
  funext who
  simp [reflectCoordinate, reflectionOdd]
  ring

end Research.QuittingORRankReduction
