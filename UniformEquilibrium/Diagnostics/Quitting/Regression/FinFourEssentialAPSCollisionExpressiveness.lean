/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Regression.FinFourEssentialAPSSummableThirdMode
import UniformEquilibrium.Quitting.EssentialAPS.SingletonDataCongruence
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Collision expressiveness beyond singleton essential-APS data

Two complete reward tables share the singleton table and hence every
singleton-data essential-APS object formalized in the companion modules.
Completion A has an exact unrestricted-behavior all-Quit equilibrium.
Completion B instead has all Continue as its unique exact product root against
the common cap.  The forced singleton APS path remains an exact Bellman path
under Completion B but is not asserted to be Nash.
-/

noncomputable section

namespace GameTheory
namespace FinFourEssentialAPSCollisionExpressiveness

open Filter Math.ProbabilityMassFunction StochasticGame
open FinFourEssentialAPSCarrier
open FinFourEssentialAPSSummableThirdMode
open QuittingSureSetOwnerRepair

/-- The insertion-toggle matrix used by Completion B. -/
def collisionCoefficient (who other : Player) : ℝ :=
  if who.val = 0 then
    if other.val = 0 then 0 else if other.val = 1 then -2
      else if other.val = 2 then -2 else 1
  else if who.val = 1 then
    if other.val = 0 then 1 else if other.val = 1 then 0
      else if other.val = 2 then -2 else -2
  else if who.val = 2 then
    if other.val = 0 then 1 else if other.val = 1 then 1
      else if other.val = 2 then 0 else -2
  else
    if other.val = 0 then -2 else if other.val = 1 then 1
      else if other.val = 2 then 1 else 0

/-- The base payoff against a nonempty opponent coalition: its singleton row
when the coalition is a singleton, and the common level otherwise. -/
def opponentCoalitionBase (coalition : Finset Player) (who : Player) : ℝ :=
  if coalition.card = 1 then
    ∑ other ∈ coalition, singletonReward other who
  else 1

/-- Completion B, including all nonsingleton collision payoffs. -/
def completionBReward
    (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player := fun who =>
  if who ∈ terminal.1 then
    let opponents := terminal.1.erase who
    if opponents = ∅ then 1
    else opponentCoalitionBase opponents who +
      ∑ other ∈ opponents, collisionCoefficient who other
  else opponentCoalitionBase terminal.1 who

@[simp] theorem completionBReward_singleton (quitter : Player) :
    completionBReward (quittingSingletonTerminal quitter) = singletonReward quitter := by
  funext who
  fin_cases quitter <;> fin_cases who <;>
    norm_num +decide [completionBReward, opponentCoalitionBase,
      collisionCoefficient, singletonReward, quittingSingletonTerminal]

@[simp] theorem quittingSoloReward_completionBReward (quitter : Player) :
    quittingSoloReward completionBReward quitter = singletonReward quitter := by
  rw [quittingSoloReward]
  exact completionBReward_singleton quitter

/-- The two completions have literally identical singleton terminal data. -/
theorem completionA_completionB_sameSingletonData :
    HaveSameQuittingSingletonRewards completionAReward completionBReward := by
  intro quitter
  rw [quittingSoloReward_completionAReward, quittingSoloReward_completionBReward]

/-- Completion A's grand-coalition stationary exit is an exact Nash profile
against every unilateral behavioral strategy, not merely every stationary
or endpoint deviation. -/
theorem completionA_allQuit_isExactBehavioralNash :
    (quittingGame completionAReward).IsεAsymptoticNash
      (quittingTerminalPayoff completionAReward) 0
      (quittingStationaryProfile completionAReward
        (quittingPureSetRoot (Finset.univ : Finset Player))) := by
  rw [isεAsymptoticNash_pureSetRoot_univ_iff]
  intro who
  fin_cases who <;>
    norm_num +decide [quittingSetReward, completionAReward,
      singletonReward, baseline]

/-- Product root with prescribed Quit probabilities. -/
def productRoot (hazard : Player → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) : Player → PMF Bool :=
  fun who => bernoulliBool (hazard who) (hzero who) (hone who)

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

/-- Completion B's endpoint difference is the homogeneous insertion-toggle
linear form. -/
def collisionForm (hazard : Player → ℝ) (who : Player) : ℝ :=
  ![-2 * hazard 1 - 2 * hazard 2 + hazard 3,
    hazard 0 - 2 * hazard 2 - 2 * hazard 3,
    hazard 0 + hazard 1 - 2 * hazard 3,
    -2 * hazard 0 + hazard 1 + hazard 2] who

private theorem opponentComplement_zero :
    (({1, 2, 3} : Finset Player) \ ∅ = {1, 2, 3}) ∧
      (({1, 2, 3} : Finset Player) \ {1} = {2, 3}) ∧
      (({1, 2, 3} : Finset Player) \ {2} = {1, 3}) ∧
      (({1, 2, 3} : Finset Player) \ {3} = {1, 2}) ∧
      (({1, 2, 3} : Finset Player) \ {1, 2} = {3}) ∧
      (({1, 2, 3} : Finset Player) \ {1, 3} = {2}) ∧
      (({1, 2, 3} : Finset Player) \ {2, 3} = {1}) ∧
      (({1, 2, 3} : Finset Player) \ {1, 2, 3} = ∅) := by decide

private theorem opponentComplement_one :
    (({0, 2, 3} : Finset Player) \ ∅ = {0, 2, 3}) ∧
      (({0, 2, 3} : Finset Player) \ {0} = {2, 3}) ∧
      (({0, 2, 3} : Finset Player) \ {2} = {0, 3}) ∧
      (({0, 2, 3} : Finset Player) \ {3} = {0, 2}) ∧
      (({0, 2, 3} : Finset Player) \ {0, 2} = {3}) ∧
      (({0, 2, 3} : Finset Player) \ {0, 3} = {2}) ∧
      (({0, 2, 3} : Finset Player) \ {2, 3} = {0}) ∧
      (({0, 2, 3} : Finset Player) \ {0, 2, 3} = ∅) := by decide

private theorem opponentComplement_two :
    (({0, 1, 3} : Finset Player) \ ∅ = {0, 1, 3}) ∧
      (({0, 1, 3} : Finset Player) \ {0} = {1, 3}) ∧
      (({0, 1, 3} : Finset Player) \ {1} = {0, 3}) ∧
      (({0, 1, 3} : Finset Player) \ {3} = {0, 1}) ∧
      (({0, 1, 3} : Finset Player) \ {0, 1} = {3}) ∧
      (({0, 1, 3} : Finset Player) \ {0, 3} = {1}) ∧
      (({0, 1, 3} : Finset Player) \ {1, 3} = {0}) ∧
      (({0, 1, 3} : Finset Player) \ {0, 1, 3} = ∅) := by decide

private theorem opponentComplement_three :
    (({0, 1, 2} : Finset Player) \ ∅ = {0, 1, 2}) ∧
      (({0, 1, 2} : Finset Player) \ {0} = {1, 2}) ∧
      (({0, 1, 2} : Finset Player) \ {1} = {0, 2}) ∧
      (({0, 1, 2} : Finset Player) \ {2} = {0, 1}) ∧
      (({0, 1, 2} : Finset Player) \ {0, 1} = {2}) ∧
      (({0, 1, 2} : Finset Player) \ {0, 2} = {1}) ∧
      (({0, 1, 2} : Finset Player) \ {1, 2} = {0}) ∧
      (({0, 1, 2} : Finset Player) \ {0, 1, 2} = ∅) := by decide

theorem quittingRootEndpointDifference_productRoot_zero
    (hazard : Player → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) :
    quittingRootEndpointDifference completionBReward baseline
      (productRoot hazard hzero hone) 0 = collisionForm hazard 0 := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  unfold quittingOpponentCoalitionMass quittingEndpointInsertionToggle
    quittingStageCoalitionPayoff
  rw [show Finset.univ.erase (0 : Player) = {1, 2, 3} by decide]
  rw [show ({1, 2, 3} : Finset Player).powerset =
    {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
  obtain ⟨e0, e1, e2, e3, e12, e13, e23, -⟩ := opponentComplement_zero
  simp +decide [e0, e1, e2, e3, e12, e13, e23,
    productRoot, collisionForm, completionBReward,
    opponentCoalitionBase, collisionCoefficient, baseline, singletonReward]
  ring

theorem quittingRootEndpointDifference_productRoot_one
    (hazard : Player → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) :
    quittingRootEndpointDifference completionBReward baseline
      (productRoot hazard hzero hone) 1 = collisionForm hazard 1 := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  unfold quittingOpponentCoalitionMass quittingEndpointInsertionToggle
    quittingStageCoalitionPayoff
  rw [show Finset.univ.erase (1 : Player) = {0, 2, 3} by decide]
  rw [show ({0, 2, 3} : Finset Player).powerset =
    {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
  obtain ⟨e0, e1, e2, e3, e12, e13, e23, -⟩ := opponentComplement_one
  simp +decide [e0, e1, e2, e3, e12, e13, e23,
    productRoot, collisionForm, completionBReward,
    opponentCoalitionBase, collisionCoefficient, baseline, singletonReward]
  ring

theorem quittingRootEndpointDifference_productRoot_two
    (hazard : Player → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) :
    quittingRootEndpointDifference completionBReward baseline
      (productRoot hazard hzero hone) 2 = collisionForm hazard 2 := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  unfold quittingOpponentCoalitionMass quittingEndpointInsertionToggle
    quittingStageCoalitionPayoff
  rw [show Finset.univ.erase (2 : Player) = {0, 1, 3} by decide]
  rw [show ({0, 1, 3} : Finset Player).powerset =
    {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
  obtain ⟨e0, e1, e2, e3, e12, e13, e23, -⟩ := opponentComplement_two
  simp +decide [e0, e1, e2, e3, e12, e13, e23,
    productRoot, collisionForm, completionBReward,
    opponentCoalitionBase, collisionCoefficient, baseline, singletonReward]
  ring

theorem quittingRootEndpointDifference_productRoot_three
    (hazard : Player → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) :
    quittingRootEndpointDifference completionBReward baseline
      (productRoot hazard hzero hone) 3 = collisionForm hazard 3 := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  unfold quittingOpponentCoalitionMass quittingEndpointInsertionToggle
    quittingStageCoalitionPayoff
  rw [show Finset.univ.erase (3 : Player) = {0, 1, 2} by decide]
  rw [show ({0, 1, 2} : Finset Player).powerset =
    {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
  obtain ⟨e0, e1, e2, e3, e12, e13, e23, -⟩ := opponentComplement_three
  simp +decide [e0, e1, e2, e3, e12, e13, e23,
    productRoot, collisionForm, completionBReward,
    opponentCoalitionBase, collisionCoefficient, baseline, singletonReward]
  ring

theorem quittingRootEndpointDifference_productRoot_eq_collisionForm
    (hazard : Player → ℝ) (hzero : ∀ who, 0 ≤ hazard who)
    (hone : ∀ who, hazard who ≤ 1) (who : Player) :
    quittingRootEndpointDifference completionBReward baseline
      (productRoot hazard hzero hone) who = collisionForm hazard who := by
  fin_cases who
  · exact quittingRootEndpointDifference_productRoot_zero hazard hzero hone
  · exact quittingRootEndpointDifference_productRoot_one hazard hzero hone
  · exact quittingRootEndpointDifference_productRoot_two hazard hzero hone
  · exact quittingRootEndpointDifference_productRoot_three hazard hzero hone

theorem collisionForm_endpoint_of_isNash
    {hazard : Player → ℝ} {hzero : ∀ who, 0 ≤ hazard who}
    {hone : ∀ who, hazard who ≤ 1}
    (hnash : IsεQuittingRootNash completionBReward baseline 0
      (productRoot hazard hzero hone)) (who : Player) :
    (1 - hazard who) * collisionForm hazard who ≤ 0 ∧
      0 ≤ hazard who * collisionForm hazard who := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      completionBReward baseline (productRoot hazard hzero hone)).mpr hnash who
  rw [quittingRootEndpointDifference_productRoot_eq_collisionForm] at hendpoint
  simpa using hendpoint

/-- The aggregate diagonal pairing is the negative sum of all six unordered
pair products. -/
theorem sum_hazard_mul_collisionForm (hazard : Player → ℝ) :
    (∑ who, hazard who * collisionForm hazard who) =
      -(hazard 0 * hazard 1 + hazard 0 * hazard 2 + hazard 0 * hazard 3 +
        hazard 1 * hazard 2 + hazard 1 * hazard 3 + hazard 2 * hazard 3) := by
  simp [collisionForm, Fin.sum_univ_succ]
  ring

/-- Nash complementarity and the negative-pair aggregate force every two
distinct Quit probabilities to have zero product. -/
theorem pair_products_eq_zero_of_isNash
    {hazard : Player → ℝ} {hzero : ∀ who, 0 ≤ hazard who}
    {hone : ∀ who, hazard who ≤ 1}
    (hnash : IsεQuittingRootNash completionBReward baseline 0
      (productRoot hazard hzero hone)) :
    hazard 0 * hazard 1 = 0 ∧ hazard 0 * hazard 2 = 0 ∧
      hazard 0 * hazard 3 = 0 ∧ hazard 1 * hazard 2 = 0 ∧
      hazard 1 * hazard 3 = 0 ∧ hazard 2 * hazard 3 = 0 := by
  have hn0 := (collisionForm_endpoint_of_isNash hnash (0 : Player)).2
  have hn1 := (collisionForm_endpoint_of_isNash hnash (1 : Player)).2
  have hn2 := (collisionForm_endpoint_of_isNash hnash (2 : Player)).2
  have hn3 := (collisionForm_endpoint_of_isNash hnash (3 : Player)).2
  have hsum : 0 ≤ ∑ who, hazard who * collisionForm hazard who := by
    simp [Fin.sum_univ_succ]
    linarith
  rw [sum_hazard_mul_collisionForm] at hsum
  have hp01 : 0 ≤ hazard 0 * hazard 1 := mul_nonneg (hzero 0) (hzero 1)
  have hp02 : 0 ≤ hazard 0 * hazard 2 := mul_nonneg (hzero 0) (hzero 2)
  have hp03 : 0 ≤ hazard 0 * hazard 3 := mul_nonneg (hzero 0) (hzero 3)
  have hp12 : 0 ≤ hazard 1 * hazard 2 := mul_nonneg (hzero 1) (hzero 2)
  have hp13 : 0 ≤ hazard 1 * hazard 3 := mul_nonneg (hzero 1) (hzero 3)
  have hp23 : 0 ≤ hazard 2 * hazard 3 := mul_nonneg (hzero 2) (hzero 3)
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Every prescribed Quit probability in a Completion-B exact root against
the common cap is zero. -/
theorem hazard_eq_zero_of_isNash
    {hazard : Player → ℝ} {hzero : ∀ who, 0 ≤ hazard who}
    {hone : ∀ who, hazard who ≤ 1}
    (hnash : IsεQuittingRootNash completionBReward baseline 0
      (productRoot hazard hzero hone)) (who : Player) :
    hazard who = 0 := by
  obtain ⟨hp01, hp02, hp03, hp12, hp13, hp23⟩ :=
    pair_products_eq_zero_of_isNash hnash
  have endpoint := collisionForm_endpoint_of_isNash hnash
  fin_cases who
  · by_contra hne
    have hpos : 0 < hazard 0 := lt_of_le_of_ne (hzero 0) (Ne.symm hne)
    have hz1 : hazard 1 = 0 := (mul_eq_zero.mp hp01).resolve_left hne
    have hz2 : hazard 2 = 0 := (mul_eq_zero.mp hp02).resolve_left hne
    have hz3 : hazard 3 = 0 := (mul_eq_zero.mp hp03).resolve_left hne
    have hbad := (endpoint (1 : Player)).1
    simp [collisionForm, hz1, hz2, hz3] at hbad
    linarith
  · by_contra hne
    have hpos : 0 < hazard 1 := lt_of_le_of_ne (hzero 1) (Ne.symm hne)
    have hz0 : hazard 0 = 0 := (mul_eq_zero.mp hp01).resolve_right hne
    have hz2 : hazard 2 = 0 := (mul_eq_zero.mp hp12).resolve_left hne
    have hz3 : hazard 3 = 0 := (mul_eq_zero.mp hp13).resolve_left hne
    have hbad := (endpoint (2 : Player)).1
    simp [collisionForm, hz0, hz2, hz3] at hbad
    linarith
  · by_contra hne
    have hpos : 0 < hazard 2 := lt_of_le_of_ne (hzero 2) (Ne.symm hne)
    have hz0 : hazard 0 = 0 := (mul_eq_zero.mp hp02).resolve_right hne
    have hz1 : hazard 1 = 0 := (mul_eq_zero.mp hp12).resolve_right hne
    have hz3 : hazard 3 = 0 := (mul_eq_zero.mp hp23).resolve_left hne
    have hbad := (endpoint (3 : Player)).1
    simp [collisionForm, hz0, hz1, hz3] at hbad
    linarith
  · by_contra hne
    have hpos : 0 < hazard 3 := lt_of_le_of_ne (hzero 3) (Ne.symm hne)
    have hz0 : hazard 0 = 0 := (mul_eq_zero.mp hp03).resolve_right hne
    have hz1 : hazard 1 = 0 := (mul_eq_zero.mp hp13).resolve_right hne
    have hz2 : hazard 2 = 0 := (mul_eq_zero.mp hp23).resolve_right hne
    have hbad := (endpoint (0 : Player)).1
    simp [collisionForm, hz0, hz1, hz2] at hbad
    linarith

/-- A Boolean marginal is determined by its Quit probability. -/
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

theorem eq_productRoot (candidate : Player → PMF Bool)
    (hzero : ∀ who, 0 ≤ (candidate who true).toReal)
    (hone : ∀ who, (candidate who true).toReal ≤ 1) :
    candidate = productRoot (fun who => (candidate who true).toReal) hzero hone := by
  funext who
  exact pmfBool_eq_of_quitProbability_eq (by simp [productRoot])

/-- All Continue is an exact Completion-B root against the common cap. -/
theorem completionB_allContinueRoot_isNash :
    IsεQuittingRootNash completionBReward baseline 0
      (quittingAllContinueRoot : Player → PMF Bool) := by
  apply quittingAllContinueRoot_isZeroNash_of_singleton_le
  intro who
  rw [completionBReward_singleton]
  fin_cases who <;> norm_num [baseline, singletonReward]

/-- All Continue is the unique exact Completion-B product root against the
common cap.  No claim is made about other caps. -/
theorem eq_allContinueRoot_of_completionB_isNash
    (candidate : Player → PMF Bool)
    (hnash : IsεQuittingRootNash completionBReward baseline 0 candidate) :
    candidate = (quittingAllContinueRoot : Player → PMF Bool) := by
  have hzero : ∀ who : Player, 0 ≤ (candidate who true).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hone : ∀ who : Player, (candidate who true).toReal ≤ 1 := by
    intro who
    have hsum := quittingRoot_continueProbability_add_quitProbability candidate who
    have hcontinue : 0 ≤ (candidate who false).toReal := ENNReal.toReal_nonneg
    linarith
  have hproduct := eq_productRoot candidate hzero hone
  rw [hproduct] at hnash ⊢
  funext who
  apply pmfBool_eq_of_quitProbability_eq
  simp [productRoot, quittingAllContinueRoot, hazard_eq_zero_of_isNash hnash who]

theorem completionB_existsUnique_exactRootAgainstBaseline :
    ∃! candidate : Player → PMF Bool,
      IsεQuittingRootNash completionBReward baseline 0 candidate := by
  refine ⟨quittingAllContinueRoot, completionB_allContinueRoot_isNash, ?_⟩
  intro candidate hnash
  exact eq_allContinueRoot_of_completionB_isNash candidate hnash

/-- The same grand-coalition root is exact for Completion A against the
common cap. -/
theorem completionA_allQuitRoot_isNashAgainstBaseline :
    IsεQuittingRootNash completionAReward baseline 0
      (quittingPureSetRoot (Finset.univ : Finset Player)) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  have herase : ((Finset.univ : Finset Player).erase who).Nonempty := by
    fin_cases who <;> decide
  simp [quittingPureSetRoot, QuittingSureSetOwnerRepair.quittingSetAction]
  unfold quittingRootEndpointDifference
  rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      baseline Finset.univ who herase,
    quittingRootQuitPayoff_pureSetRoot_eq_insert]
  fin_cases who <;>
    norm_num +decide [quittingSetReward, completionAReward,
      baseline, singletonReward]

/-- The carrier-restricted greatest families are literally equal under the
two completions. -/
theorem completionA_completionB_greatestFamily_eq :
    quittingEssentialAPSGreatestFamily completionAReward carrier =
      quittingEssentialAPSGreatestFamily completionBReward carrier :=
  completionA_completionB_sameSingletonData.essentialAPSGreatestFamily_eq carrier

/-- Completion B has the same literal greatest family, namely the displayed
carrier. -/
theorem completionB_greatestFamily_eq_carrier :
    quittingEssentialAPSGreatestFamily completionBReward carrier = carrier := by
  rw [← completionA_completionB_greatestFamily_eq]
  exact greatestFamily_eq_carrier

/-- The exact strict Flesch graph is unchanged under Completion B. -/
theorem completionB_fleschSuccessor_iff (owner successor : Player) :
    QuittingFleschSuccessor completionBReward owner successor ↔
      (owner = 0 ∧ successor = 1) ∨
      (owner = 1 ∧ successor = 2) ∨
      (owner = 2 ∧ successor = 0) := by
  rw [← completionA_completionB_sameSingletonData.fleschSuccessor_iff]
  exact fleschSuccessor_iff owner successor

/-- The same literal positive summable execution is an infinite essential-APS
run for Completion B. -/
theorem completionB_isInfiniteRun {initial : ℝ}
    (hinitial : initial ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    IsQuittingEssentialAPSInfiniteRun completionBReward
      (quittingEssentialAPSGreatestFamily completionBReward carrier)
      executionOwner (valueZero initial) (executionMass initial)
      (executionValue initial) := by
  rw [← completionA_completionB_greatestFamily_eq]
  exact (completionA_completionB_sameSingletonData.essentialAPSInfiniteRun_iff
    (quittingEssentialAPSGreatestFamily completionAReward carrier)
    executionOwner (valueZero initial) (executionMass initial)
    (executionValue initial)).mp (isInfiniteRun hinitial)

/-- Completion B preserves the exact Bellman identities because the displayed
roots have only one possible quitter.  This is not a Nash theorem. -/
theorem completionB_executionValue_bellman {initial : ℝ}
    (hinitial : initial ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ∀ time, executionValue initial time =
      quittingRootSuccessorPayoff completionBReward
        (executionValue initial (time + 1)) (executionRoots hinitial time) := by
  exact (completionB_isInfiniteRun hinitial).policy_singletonRoots
    (executionMass_nonneg hinitial)
    (fun time => (executionMass_le_one_quarter hinitial time).trans (by norm_num))

/-- Completion B's Bellman path with its literal terminal semantics. -/
def completionBSummableExactValueTail {initial : ℝ}
    (hinitial : initial ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    QuittingSummableExactValueTail completionBReward where
  roots := executionRoots hinitial
  value := executionValue initial
  boundary := baseline
  bellman := completionB_executionValue_bellman hinitial
  value_tendsto := executionValue_tendsto_baseline hinitial
  absorption_summable := by
    simpa using summable_executionMass hinitial

/-- Completion B's literal late-suffix terminal payoffs tend to zero. -/
theorem completionB_terminalPayoff_tendsto_zero {initial : ℝ}
    (hinitial : initial ∈ Set.Icc (0 : ℝ) (1 / 2)) (who : Player) :
    Filter.Tendsto (fun start => quittingTerminalPayoff completionBReward
      ((completionBSummableExactValueTail hinitial).suffixProfile start) who)
      Filter.atTop (nhds 0) :=
  (completionBSummableExactValueTail hinitial).terminalPayoff_tendsto_zero who

/-- Completion B's unrestricted behavioral suffix exploitability tends to
one. -/
theorem completionB_suffixGain_tendsto_one {initial : ℝ}
    (hinitial : initial ∈ Set.Icc (0 : ℝ) (1 / 2)) (who : Player) :
    Filter.Tendsto
      (fun start => (completionBSummableExactValueTail hinitial).suffixGain start who)
      Filter.atTop (nhds 1) := by
  have hgain :=
    (completionBSummableExactValueTail hinitial).suffixGain_tendsto_max_solo who
  fin_cases who <;>
    norm_num +decide [completionBReward, opponentCoalitionBase,
      collisionCoefficient, singletonReward, quittingSingletonTerminal] at hgain ⊢
  all_goals exact hgain

/-- Every positive displayed APS root fails exact Nash against the common
cap in Completion B, even though it satisfies its Bellman annotation. -/
theorem completionB_executionRoots_not_nashAgainstBaseline {initial : ℝ}
    (hinitial : initial ∈ Set.Ioc (0 : ℝ) (1 / 2)) (time : ℕ) :
    ¬ IsεQuittingRootNash completionBReward baseline 0
      (executionRoots ⟨hinitial.1.le, hinitial.2⟩ time) := by
  intro hnash
  have heq := eq_allContinueRoot_of_completionB_isNash _ hnash
  have habs := congrArg quittingRootAbsorptionMass heq
  rw [executionRoots_absorptionMass] at habs
  have hpositive := executionMass_positive hinitial time
  rw [quittingRootAbsorptionMass_allContinueRoot] at habs
  linarith

/-- Literal collision-expressiveness capstone: identical singleton APS data
coexist with opposite exact root behavior at the same cap. -/
theorem sameSingletonData_opposite_exactRootBehavior :
    HaveSameQuittingSingletonRewards completionAReward completionBReward ∧
      quittingEssentialAPSGreatestFamily completionAReward carrier =
        quittingEssentialAPSGreatestFamily completionBReward carrier ∧
      IsεQuittingRootNash completionAReward baseline 0
        (quittingPureSetRoot (Finset.univ : Finset Player)) ∧
      (∃! candidate : Player → PMF Bool,
        IsεQuittingRootNash completionBReward baseline 0 candidate) := by
  exact ⟨completionA_completionB_sameSingletonData,
    completionA_completionB_greatestFamily_eq,
    completionA_allQuitRoot_isNashAgainstBaseline,
    completionB_existsUnique_exactRootAgainstBaseline⟩

/-- Full concrete expressiveness no-go.  The shared singleton essential-APS
execution is positive and summable in both complete games.  Completion A has
an unrestricted-behavior all-Quit equilibrium, whereas Completion B has a
unique all-Continue exact root at the common cap and none of the positive
displayed Bellman roots is Nash there.  This theorem asserts neither a source
chronology nor a uniform-equilibrium conclusion for Completion B. -/
theorem essentialAPS_singletonData_does_not_determine_collisionRootBehavior :
    HaveSameQuittingSingletonRewards completionAReward completionBReward ∧
      quittingEssentialAPSGreatestFamily completionAReward carrier = carrier ∧
      quittingEssentialAPSGreatestFamily completionBReward carrier = carrier ∧
      (quittingGame completionAReward).IsεAsymptoticNash
        (quittingTerminalPayoff completionAReward) 0
        (quittingStationaryProfile completionAReward
          (quittingPureSetRoot (Finset.univ : Finset Player))) ∧
      IsεQuittingRootNash completionAReward baseline 0
        (quittingPureSetRoot (Finset.univ : Finset Player)) ∧
      (∃! candidate : Player → PMF Bool,
        IsεQuittingRootNash completionBReward baseline 0 candidate) ∧
      ∃ (initial : ℝ) (hinitial : initial ∈ Set.Ioc (0 : ℝ) (1 / 2)),
        IsQuittingEssentialAPSInfiniteRun completionAReward
          (quittingEssentialAPSGreatestFamily completionAReward carrier)
          executionOwner (valueZero initial) (executionMass initial)
          (executionValue initial) ∧
        IsQuittingEssentialAPSInfiniteRun completionBReward
          (quittingEssentialAPSGreatestFamily completionBReward carrier)
          executionOwner (valueZero initial) (executionMass initial)
          (executionValue initial) ∧
        Summable (executionMass initial) ∧
        (∀ time, 0 < executionMass initial time ∧
          ¬ IsεQuittingRootNash completionBReward baseline 0
            (executionRoots ⟨hinitial.1.le, hinitial.2⟩ time)) := by
  refine ⟨completionA_completionB_sameSingletonData, greatestFamily_eq_carrier,
    completionB_greatestFamily_eq_carrier, completionA_allQuit_isExactBehavioralNash,
    completionA_allQuitRoot_isNashAgainstBaseline,
    completionB_existsUnique_exactRootAgainstBaseline, 1 / 4, by norm_num,
    isInfiniteRun (by norm_num), completionB_isInfiniteRun (by norm_num),
    summable_executionMass (by norm_num), ?_⟩
  intro time
  exact ⟨executionMass_positive (by norm_num) time,
    completionB_executionRoots_not_nashAgainstBaseline (by norm_num) time⟩

end FinFourEssentialAPSCollisionExpressiveness
end GameTheory
