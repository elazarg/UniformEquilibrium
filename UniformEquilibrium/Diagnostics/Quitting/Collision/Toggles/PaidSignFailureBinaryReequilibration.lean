/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargePersistentBaseDeletionAdapter
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PurePaidBaseLeaveDescent
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness

/-!
# Binary re-equilibration after a paid pure-base sign failure

This file isolates the exact finite two-by-two repair forced when deleting a
paid persistent player reverses one retained pure best response.  Equality
faces remain pure; the only interior case is the strict matching-pennies
chamber.  The semantic capstone below uses the literal quitting root and the
singleton-base all-behavior compiler.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability
open Math.ProbabilityMassFunction
open QuittingSureSetOwnerRepair

/-- The three exhaustive faces selected by the paid sign-failure signs.
The first Boolean coordinate is the deleted player's new Quit action; the
second records whether the retained player switches from its old action. -/
inductive PaidSignFailureBinarySelection (join switch : Bool → ℝ) : Type
  | absentSwitched (hjoin : join true ≤ 0)
  | presentSwitched (hjoin : 0 < join true) (hswitch : switch true = 0)
  | strictMixed (hjoin : 0 < join true) (hswitch : switch true < 0)

namespace PaidSignFailureBinarySelection

variable {join switch : Bool → ℝ}

/-- Quit rate of the formerly deleted player. -/
def firstRate : PaidSignFailureBinarySelection join switch → ℝ
  | .absentSwitched _ => 0
  | .presentSwitched _ _ => 1
  | .strictMixed _ _ => binaryMixedFirstRate switch

/-- Probability that the retained player switches from its old action. -/
def secondRate : PaidSignFailureBinarySelection join switch → ℝ
  | .absentSwitched _ => 1
  | .presentSwitched _ _ => 1
  | .strictMixed _ _ => binaryMixedSecondRate join

/-- Division-free normalizing denominator. -/
def denominator : PaidSignFailureBinarySelection join switch → ℝ
  | .absentSwitched _ => 1
  | .presentSwitched _ _ => 1
  | .strictMixed _ _ => binaryClearedDenominator join switch

/-- Division-free mass of a pure cell. -/
def weight : PaidSignFailureBinarySelection join switch → Bool → Bool → ℝ
  | .absentSwitched _, first, second =>
      if first = false ∧ second = true then 1 else 0
  | .presentSwitched _ _, first, second =>
      if first = true ∧ second = true then 1 else 0
  | .strictMixed _ _, false, false => -switch true * join true
  | .strictMixed _ _, true, false => switch false * join true
  | .strictMixed _ _, false, true => switch true * join false
  | .strictMixed _ _, true, true => -switch false * join false

/-- Explicit four-cell weighted sum, avoiding any ordering convention on
Boolean enumeration. -/
def weightedSum (selection : PaidSignFailureBinarySelection join switch)
    (observable : Bool → Bool → ℝ) : ℝ :=
  selection.weight false false * observable false false +
    selection.weight true false * observable true false +
    selection.weight false true * observable false true +
    selection.weight true true * observable true true

/-- Source signs imply the exact three-face selection, with equality assigned
to the two pure boundary cases. -/
theorem exists_of_sourceSigns
    {gamma : ℝ} (_hgamma : 0 < gamma)
    (_hjoinOld : join false ≤ -gamma)
    (_hswitchCleared : 0 < switch false)
    (hswitchPresent : switch true ≤ 0) :
    Nonempty (PaidSignFailureBinarySelection join switch) := by
  by_cases hjoinNew : join true ≤ 0
  · exact ⟨.absentSwitched hjoinNew⟩
  · have hjoinNewPos : 0 < join true := lt_of_not_ge hjoinNew
    by_cases hswitchNew : switch true = 0
    · exact ⟨.presentSwitched hjoinNewPos hswitchNew⟩
    · exact ⟨.strictMixed hjoinNewPos
        (lt_of_le_of_ne hswitchPresent hswitchNew)⟩

/-- Every selected face is an exact product Nash point. -/
theorem isBinaryDifferenceNash
    (selection : PaidSignFailureBinarySelection join switch)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hjoinOld : join false ≤ -gamma)
    (hswitchCleared : 0 < switch false) :
    IsBinaryDifferenceNash join switch selection.firstRate
      selection.secondRate := by
  cases selection with
  | absentSwitched hjoin =>
      exact (isBinaryDifferenceNash_pure_iff join switch false true).2 <| by
        simpa [IsPureBinaryDifferenceNash] using
          And.intro hjoin hswitchCleared.le
  | presentSwitched hjoin hswitch =>
      exact (isBinaryDifferenceNash_pure_iff join switch true true).2 <| by
        simpa [IsPureBinaryDifferenceNash, hswitch] using
          And.intro hjoin.le hswitch.ge
  | strictMixed hjoin hswitch =>
      apply isBinaryDifferenceNash_mixed
      exact Or.inr ⟨hjoin, lt_of_le_of_lt hjoinOld (neg_neg_of_pos hgamma),
        hswitchCleared, hswitch⟩

/-- The selected denominator is strictly positive. -/
theorem denominator_pos
    (selection : PaidSignFailureBinarySelection join switch)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hjoinOld : join false ≤ -gamma)
    (hswitchCleared : 0 < switch false) :
    0 < selection.denominator := by
  cases selection with
  | absentSwitched _ => simp [denominator]
  | presentSwitched _ _ => simp [denominator]
  | strictMixed hjoin hswitch =>
      apply binaryClearedDenominator_pos
      exact Or.inr ⟨hjoin, lt_of_le_of_lt hjoinOld (neg_neg_of_pos hgamma),
        hswitchCleared, hswitch⟩

/-- The four displayed weights sum to the selected denominator. -/
theorem sum_weight
    (selection : PaidSignFailureBinarySelection join switch) :
    selection.weightedSum (fun _ _ => 1) = selection.denominator := by
  cases selection with
  | absentSwitched _ => simp [weightedSum, weight, denominator]
  | presentSwitched _ _ => simp [weightedSum, weight, denominator]
  | strictMixed _ _ =>
      simp [weightedSum, weight, denominator, binaryClearedDenominator]
      ring

/-- Every selected weight is nonnegative; in the strict mixed chamber every
one is positive. -/
theorem weight_nonneg
    (selection : PaidSignFailureBinarySelection join switch)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hjoinOld : join false ≤ -gamma)
    (hswitchCleared : 0 < switch false)
    (first second : Bool) :
    0 ≤ selection.weight first second := by
  cases selection with
  | absentSwitched hjoin =>
      by_cases hcell : first = false ∧ second = true <;> simp [weight, hcell]
  | presentSwitched hjoin hswitch =>
      by_cases hcell : first = true ∧ second = true <;> simp [weight, hcell]
  | strictMixed hjoin hswitch =>
      have hjoinOldNeg : join false < 0 :=
        lt_of_le_of_lt hjoinOld (neg_neg_of_pos hgamma)
      have h00 : 0 < -switch true * join true :=
        mul_pos (neg_pos.mpr hswitch) hjoin
      have h01 : 0 < switch true * join false :=
        mul_pos_of_neg_of_neg hswitch hjoinOldNeg
      have h10 : 0 < switch false * join true :=
        mul_pos hswitchCleared hjoin
      have h11 : 0 < -switch false * join false :=
        mul_pos_of_neg_of_neg (neg_neg_of_pos hswitchCleared) hjoinOldNeg
      cases first <;> cases second
      · simpa [weight] using h00.le
      · simpa [weight] using h01.le
      · simpa [weight] using h10.le
      · simpa [weight] using h11.le

theorem weight_pos_of_strictMixed
    (hjoin : 0 < join true) (hswitch : switch true < 0)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hjoinOld : join false ≤ -gamma)
    (hswitchCleared : 0 < switch false)
    (first second : Bool) :
    0 < (strictMixed hjoin hswitch :
      PaidSignFailureBinarySelection join switch).weight first second := by
  have hjoinOldNeg : join false < 0 :=
    lt_of_le_of_lt hjoinOld (neg_neg_of_pos hgamma)
  have h00 : 0 < -switch true * join true :=
    mul_pos (neg_pos.mpr hswitch) hjoin
  have h01 : 0 < switch true * join false :=
    mul_pos_of_neg_of_neg hswitch hjoinOldNeg
  have h10 : 0 < switch false * join true :=
    mul_pos hswitchCleared hjoin
  have h11 : 0 < -switch false * join false :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos hswitchCleared) hjoinOldNeg
  cases first <;> cases second
  · simpa [weight] using h00
  · simpa [weight] using h01
  · simpa [weight] using h10
  · simpa [weight] using h11

/-- The selected weights are the exact independent product law. -/
theorem denominator_mul_binaryProductExpectation
    (selection : PaidSignFailureBinarySelection join switch)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hjoinOld : join false ≤ -gamma)
    (hswitchCleared : 0 < switch false)
    (observable : Bool → Bool → ℝ) :
      selection.denominator * binaryProductExpectation observable
        selection.firstRate selection.secondRate =
      selection.weightedSum observable := by
  cases selection with
  | absentSwitched hjoin =>
      simp [denominator, firstRate, secondRate, weightedSum, weight,
        binaryProductExpectation]
  | presentSwitched hjoin hswitch =>
      simp [denominator, firstRate, secondRate, weightedSum, weight,
        binaryProductExpectation]
  | strictMixed hjoin hswitch =>
      have orientation : IsStrictMatchingPenniesOrientation join switch :=
        Or.inr ⟨hjoin, lt_of_le_of_lt hjoinOld (neg_neg_of_pos hgamma),
          hswitchCleared, hswitch⟩
      rw [denominator, firstRate, secondRate,
        binaryProductExpectation_mixed orientation]
      have hden := binaryClearedDenominator_pos orientation
      field_simp [ne_of_gt hden]
      simp only [weightedSum, weight, binaryClearedObservable]

end PaidSignFailureBinarySelection

/-! ## Literal quitting-root adapter -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual Quit rate when `switchRate` is the probability of taking the
opposite of `oldAction`. -/
def paidSignFailureActualQuitRate (oldAction : Bool) (switchRate : ℝ) : ℝ :=
  if oldAction then 1 - switchRate else switchRate

theorem paidSignFailureActualQuitRate_mem_Icc
    (oldAction : Bool) {switchRate : ℝ}
    (hswitchRate : switchRate ∈ Set.Icc (0 : ℝ) 1) :
    paidSignFailureActualQuitRate oldAction switchRate ∈ Set.Icc (0 : ℝ) 1 := by
  cases oldAction
  · simpa [paidSignFailureActualQuitRate] using hswitchRate
  · constructor <;> simp [paidSignFailureActualQuitRate] <;>
      linarith [hswitchRate.1, hswitchRate.2]

/-- Bernoulli quitting law whose encoded switch probability is `switchRate`. -/
def paidSignFailureActualLaw (oldAction : Bool) (switchRate : ℝ)
    (hswitchRate : switchRate ∈ Set.Icc (0 : ℝ) 1) : PMF Bool :=
  bernoulliBool (paidSignFailureActualQuitRate oldAction switchRate)
    (paidSignFailureActualQuitRate_mem_Icc oldAction hswitchRate).1
    (paidSignFailureActualQuitRate_mem_Icc oldAction hswitchRate).2

@[simp] theorem paidSignFailureActualLaw_true_toReal
    (oldAction : Bool) (switchRate : ℝ)
    (hswitchRate : switchRate ∈ Set.Icc (0 : ℝ) 1) :
    (paidSignFailureActualLaw oldAction switchRate hswitchRate true).toReal =
      paidSignFailureActualQuitRate oldAction switchRate := by
  exact bernoulliBool_true_toReal _ _ _

/-- Re-equilibrated actual quitting root, obtained from an arbitrary
background by replacing the two active marginals. -/
def paidSignFailureRoot (background : ι → PMF Bool) (first second : ι)
    (oldAction : Bool) (firstRate switchRate : ℝ)
    (hfirstRate : firstRate ∈ Set.Icc (0 : ℝ) 1)
    (hswitchRate : switchRate ∈ Set.Icc (0 : ℝ) 1) : ι → PMF Bool :=
  Function.update
    (Function.update background first
      (bernoulliBool firstRate hfirstRate.1 hfirstRate.2))
    second (paidSignFailureActualLaw oldAction switchRate hswitchRate)

/-- The first player's Quit-minus-Continue row, indexed by the retained
player's encoded old/switch action. -/
def paidSignFailureJoinRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (background : ι → PMF Bool) (first second : ι)
    (oldAction : Bool) (switched : Bool) : ℝ :=
  quittingRootEndpointDifference reward 0
    (Function.update background second (PMF.pure (Bool.xor oldAction switched)))
    first

/-- The retained player's switch-minus-old payoff row, indexed by the first
player's Continue/Quit action. -/
def paidSignFailureSwitchRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (background : ι → PMF Bool) (first second : ι)
    (oldAction : Bool) (firstAction : Bool) : ℝ :=
  let quitDifference := quittingRootEndpointDifference reward 0
    (Function.update background first (PMF.pure firstAction)) second
  if oldAction then -quitDifference else quitDifference

/-- Four pure endpoint cells for any observer of the two active marginals. -/
def paidSignFailureObserverCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (background : ι → PMF Bool)
    (first second observer : ι) (oldAction : Bool)
    (firstAction switched : Bool) : ℝ :=
  quittingRootEndpointDifference reward tail
    (Function.update
      (Function.update background first (PMF.pure firstAction))
      second (PMF.pure (Bool.xor oldAction switched))) observer

/-- Endpoint differences ignore the displayed player's own input marginal. -/
theorem quittingRootEndpointDifference_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (law : PMF Bool) :
    quittingRootEndpointDifference reward tail
        (Function.update root who law) who =
      quittingRootEndpointDifference reward tail root who := by
  have hquit :
      Function.update (Function.update root who law) who (PMF.pure true) =
        Function.update root who (PMF.pure true) := by
    funext other
    by_cases hother : other = who <;> simp [Function.update, hother]
  have hcontinue :
      Function.update (Function.update root who law) who (PMF.pure false) =
        Function.update root who (PMF.pure false) := by
    funext other
    by_cases hother : other = who <;> simp [Function.update, hother]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [hquit, hcontinue]

/-- Endpoint differences depend only on the opponents' marginals. -/
theorem quittingRootEndpointDifference_congr_opponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {firstRoot secondRoot : ι → PMF Bool} (who : ι)
    (hagrees : ∀ other, other ≠ who → firstRoot other = secondRoot other) :
    quittingRootEndpointDifference reward tail firstRoot who =
      quittingRootEndpointDifference reward tail secondRoot who := by
  have hquit : Function.update firstRoot who (PMF.pure true) =
      Function.update secondRoot who (PMF.pure true) := by
    funext other
    by_cases hother : other = who
    · subst other
      simp
    · simp [Function.update, hother, hagrees other hother]
  have hcontinue : Function.update firstRoot who (PMF.pure false) =
      Function.update secondRoot who (PMF.pure false) := by
    funext other
    by_cases hother : other = who
    · subst other
      simp
    · simp [Function.update, hother, hagrees other hother]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [hquit, hcontinue]

/-- An observer sees exactly the product expectation of the four encoded pure
cells.  This is the actual-root adapter behind the numerator `N`. -/
theorem quittingRootEndpointDifference_paidSignFailureRoot_observer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (background : ι → PMF Bool)
    {first second observer : ι}
    (hobserverFirst : observer ≠ first)
    (hobserverSecond : observer ≠ second)
    (hfirstSecond : first ≠ second) (oldAction : Bool)
    (firstRate switchRate : ℝ)
    (hfirstRate : firstRate ∈ Set.Icc (0 : ℝ) 1)
    (hswitchRate : switchRate ∈ Set.Icc (0 : ℝ) 1) :
    quittingRootEndpointDifference reward tail
        (paidSignFailureRoot background first second oldAction
          firstRate switchRate hfirstRate hswitchRate) observer =
      binaryProductExpectation
        (paidSignFailureObserverCell reward tail background first second
          observer oldAction) firstRate switchRate := by
  let root := paidSignFailureRoot background first second oldAction
    firstRate switchRate hfirstRate hswitchRate
  rw [quittingRootEndpointDifference_eq_twoOpponentProduct reward tail root
    hobserverFirst hobserverSecond hfirstSecond]
  have hpure (firstAction secondAction : Bool) :
      quittingRootEndpointDifference reward tail
          (Function.update
            (Function.update root first (PMF.pure firstAction))
            second (PMF.pure secondAction)) observer =
        quittingRootEndpointDifference reward tail
          (Function.update
            (Function.update background first (PMF.pure firstAction))
            second (PMF.pure secondAction)) observer := by
    apply quittingRootEndpointDifference_congr_opponents
    intro other hother
    by_cases hotherFirst : other = first
    · subst other
      simp [hfirstSecond]
    · by_cases hotherSecond : other = second
      · subst other
        simp
      · simp [root, paidSignFailureRoot, Function.update,
          hotherFirst, hotherSecond]
  simp only [binaryProductExpectation]
  rw [hpure false false, hpure true false, hpure false true, hpure true true]
  have hrootFirst : (root first true).toReal = firstRate := by
    simp [root, paidSignFailureRoot, hfirstSecond]
  have hrootSecond : (root second true).toReal =
      paidSignFailureActualQuitRate oldAction switchRate := by
    simp [root, paidSignFailureRoot]
  rw [hrootFirst, hrootSecond]
  cases oldAction
  · simp [paidSignFailureActualQuitRate, paidSignFailureObserverCell]
  · simp [paidSignFailureActualQuitRate, paidSignFailureObserverCell]
    ring

/-- Division-free observer numerator at the selected product law. -/
theorem PaidSignFailureBinarySelection.denominator_mul_observerEndpoint
    {join switch : Bool → ℝ}
    (selection : PaidSignFailureBinarySelection join switch)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hjoinOld : join false ≤ -gamma)
    (hswitchCleared : 0 < switch false)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (background : ι → PMF Bool)
    {first second observer : ι}
    (hobserverFirst : observer ≠ first)
    (hobserverSecond : observer ≠ second)
    (hfirstSecond : first ≠ second) (oldAction : Bool) :
    let hnash := selection.isBinaryDifferenceNash hgamma hjoinOld
      hswitchCleared
    let root := paidSignFailureRoot background first second oldAction
      selection.firstRate selection.secondRate hnash.1 hnash.2.1
    selection.denominator *
        quittingRootEndpointDifference reward tail root observer =
      selection.weightedSum
        (paidSignFailureObserverCell reward tail background first second
          observer oldAction) := by
  intro hnash root
  rw [quittingRootEndpointDifference_paidSignFailureRoot_observer
    reward tail background hobserverFirst hobserverSecond hfirstSecond]
  exact selection.denominator_mul_binaryProductExpectation
    hgamma hjoinOld hswitchCleared _

/-- At a sure-Quit owner, its floor excess is the negative endpoint
difference when Continue is priced by the punishment value. -/
theorem quittingSingletonBaseOwnerFloorExcess_eq_neg_endpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (root : ι → PMF Bool)
    (howner : root owner = PMF.pure true) :
    quittingSingletonBaseOwnerFloorExcess reward owner root =
      -quittingRootEndpointDifference reward
        (fun _ => quittingPunishmentValue reward owner) root owner := by
  have hmass : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter howner
  have hzero := quittingRootExpectedPayoff_eq_absorbingContribution_add
    reward 0 root owner
  have htail := quittingRootExpectedPayoff_eq_absorbingContribution_add
    reward (fun _ => quittingPunishmentValue reward owner) root owner
  have hquit : quittingRootQuitPayoff reward
      (fun _ => quittingPunishmentValue reward owner) root owner =
      quittingRootExpectedPayoff reward
        (fun _ => quittingPunishmentValue reward owner) root owner := by
    unfold quittingRootQuitPayoff
    rw [← howner, Function.update_eq_self]
  rw [quittingSingletonBaseOwnerFloorExcess,
    quittingRootEndpointDifference, hquit, hzero, htail, hmass]
  simp

/-- Punishment-priced owner cell in the same four-cell coordinates. -/
def paidSignFailureOwnerFloorCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (background : ι → PMF Bool) (owner first second : ι)
    (oldAction : Bool) (firstAction switched : Bool) : ℝ :=
  quittingSingletonBaseOwnerFloorExcess reward owner
    (Function.update
      (Function.update background first (PMF.pure firstAction))
      second (PMF.pure (Bool.xor oldAction switched)))

/-- Division-free owner-floor numerator, including the punishment-priced
all-free-Continue cell. -/
theorem PaidSignFailureBinarySelection.denominator_mul_ownerFloorExcess
    {join switch : Bool → ℝ}
    (selection : PaidSignFailureBinarySelection join switch)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hjoinOld : join false ≤ -gamma)
    (hswitchCleared : 0 < switch false)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (background : ι → PMF Bool) {owner first second : ι}
    (hownerFirst : owner ≠ first) (hownerSecond : owner ≠ second)
    (hfirstSecond : first ≠ second)
    (hbackgroundOwner : background owner = PMF.pure true)
    (oldAction : Bool) :
    let hnash := selection.isBinaryDifferenceNash hgamma hjoinOld
      hswitchCleared
    let root := paidSignFailureRoot background first second oldAction
      selection.firstRate selection.secondRate hnash.1 hnash.2.1
    selection.denominator *
        quittingSingletonBaseOwnerFloorExcess reward owner root =
      selection.weightedSum
        (paidSignFailureOwnerFloorCell reward background owner first second
          oldAction) := by
  intro hnash root
  have hrootOwner : root owner = PMF.pure true := by
    simp [root, paidSignFailureRoot, hownerFirst, hownerSecond,
      hbackgroundOwner]
  rw [quittingSingletonBaseOwnerFloorExcess_eq_neg_endpointDifference
    reward owner root hrootOwner]
  have hobserver := selection.denominator_mul_observerEndpoint
    hgamma hjoinOld hswitchCleared reward
      (fun _ => quittingPunishmentValue reward owner) background
      hownerFirst hownerSecond hfirstSecond oldAction
  change selection.denominator *
      quittingRootEndpointDifference reward
        (fun _ => quittingPunishmentValue reward owner) root owner = _
    at hobserver
  rw [show selection.denominator *
      -quittingRootEndpointDifference reward
        (fun _ => quittingPunishmentValue reward owner) root owner =
      -(selection.denominator *
        quittingRootEndpointDifference reward
          (fun _ => quittingPunishmentValue reward owner) root owner) by ring,
    hobserver]
  have hcell (firstAction switched : Bool) :
      paidSignFailureOwnerFloorCell reward background owner first second
          oldAction firstAction switched =
        -paidSignFailureObserverCell reward
          (fun _ => quittingPunishmentValue reward owner) background
          first second owner oldAction firstAction switched := by
    apply quittingSingletonBaseOwnerFloorExcess_eq_neg_endpointDifference
    simp [hownerFirst, hownerSecond, hbackgroundOwner]
  simp only [PaidSignFailureBinarySelection.weightedSum]
  rw [hcell false false, hcell true false, hcell false true, hcell true true]
  ring

/-- Updating an opponent after the displayed player's irrelevant input
marginal gives the same endpoint row as updating that opponent directly. -/
theorem quittingRootEndpointDifference_update_other_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {who other : ι}
    (hne : who ≠ other) (ownLaw otherLaw : PMF Bool) :
    quittingRootEndpointDifference reward tail
        (Function.update (Function.update root who ownLaw) other otherLaw) who =
      quittingRootEndpointDifference reward tail
        (Function.update root other otherLaw) who := by
  rw [Function.update_comm hne]
  exact quittingRootEndpointDifference_update_self
    reward tail (Function.update root other otherLaw) who ownLaw

/-- The actual first-player endpoint difference is the abstract binary row
evaluated at the encoded switch probability. -/
theorem quittingRootEndpointDifference_paidSignFailureRoot_first
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (background : ι → PMF Bool) {first second : ι}
    (hfirstSecond : first ≠ second) (oldAction : Bool)
    (firstRate switchRate : ℝ)
    (hfirstRate : firstRate ∈ Set.Icc (0 : ℝ) 1)
    (hswitchRate : switchRate ∈ Set.Icc (0 : ℝ) 1) :
    quittingRootEndpointDifference reward 0
        (paidSignFailureRoot background first second oldAction
          firstRate switchRate hfirstRate hswitchRate) first =
      binaryFirstDifference
        (paidSignFailureJoinRow reward background first second oldAction)
        switchRate := by
  let root := paidSignFailureRoot background first second oldAction
    firstRate switchRate hfirstRate hswitchRate
  have hpure (action : Bool) :
      quittingRootEndpointDifference reward 0
          (Function.update root second (PMF.pure action)) first =
        quittingRootEndpointDifference reward 0
          (Function.update background second (PMF.pure action)) first := by
    apply quittingRootEndpointDifference_congr_opponents
    intro other hother
    by_cases hotherSecond : other = second
    · subst other
      simp
    · simp [root, paidSignFailureRoot, Function.update, hother,
        hotherSecond]
  rw [quittingRootEndpointDifference_eq_opponentMix
    reward 0 root hfirstSecond]
  rw [hpure true, hpure false]
  cases oldAction
  · simp [root, paidSignFailureRoot, paidSignFailureActualLaw,
      paidSignFailureActualQuitRate, paidSignFailureJoinRow,
      binaryFirstDifference]
    ring
  · simp [root, paidSignFailureRoot, paidSignFailureActualLaw,
      paidSignFailureActualQuitRate, paidSignFailureJoinRow,
      binaryFirstDifference]

/-- The selected binary Nash condition gives the literal first player's
endpoint complementarity at the re-equilibrated quitting root. -/
theorem paidSignFailureRoot_first_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (background : ι → PMF Bool) {first second : ι}
    (hfirstSecond : first ≠ second) (oldAction : Bool)
    (firstRate switchRate : ℝ)
    (hfirstRate : firstRate ∈ Set.Icc (0 : ℝ) 1)
    (hswitchRate : switchRate ∈ Set.Icc (0 : ℝ) 1)
    (hnash : IsBinaryDifferenceNash
      (paidSignFailureJoinRow reward background first second oldAction)
      (paidSignFailureSwitchRow reward background first second oldAction)
      firstRate switchRate) :
    let root := paidSignFailureRoot background first second oldAction
      firstRate switchRate hfirstRate hswitchRate
    (root first false).toReal *
          quittingRootEndpointDifference reward 0 root first ≤ 0 ∧
      0 ≤ (root first true).toReal *
          quittingRootEndpointDifference reward 0 root first := by
  intro root
  have hdiff := quittingRootEndpointDifference_paidSignFailureRoot_first
    reward background hfirstSecond oldAction firstRate switchRate
      hfirstRate hswitchRate
  have hfirst := And.intro hnash.2.2.1 hnash.2.2.2.1
  have hfalseMass : (root first false).toReal = 1 - firstRate := by
    simp [root, paidSignFailureRoot, hfirstSecond]
  have htrueMass : (root first true).toReal = firstRate := by
    simp [root, paidSignFailureRoot, hfirstSecond]
  rw [hfalseMass, htrueMass, hdiff]
  exact hfirst

/-- The actual retained-player endpoint complementarity is exactly the
abstract switch-coordinate complementarity, including reversal when its old
action was Quit. -/
theorem paidSignFailureRoot_second_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (background : ι → PMF Bool) {first second : ι}
    (hfirstSecond : first ≠ second) (oldAction : Bool)
    (firstRate switchRate : ℝ)
    (hfirstRate : firstRate ∈ Set.Icc (0 : ℝ) 1)
    (hswitchRate : switchRate ∈ Set.Icc (0 : ℝ) 1)
    (hnash : IsBinaryDifferenceNash
      (paidSignFailureJoinRow reward background first second oldAction)
      (paidSignFailureSwitchRow reward background first second oldAction)
      firstRate switchRate) :
    let root := paidSignFailureRoot background first second oldAction
      firstRate switchRate hfirstRate hswitchRate
    (root second false).toReal *
          quittingRootEndpointDifference reward 0 root second ≤ 0 ∧
      0 ≤ (root second true).toReal *
          quittingRootEndpointDifference reward 0 root second := by
  intro root
  have hpure (action : Bool) :
      quittingRootEndpointDifference reward 0
          (Function.update root first (PMF.pure action)) second =
        quittingRootEndpointDifference reward 0
          (Function.update background first (PMF.pure action)) second := by
    apply quittingRootEndpointDifference_congr_opponents
    intro other hother
    by_cases hotherFirst : other = first
    · subst other
      simp
    · simp [root, paidSignFailureRoot, Function.update, hother,
        hotherFirst]
  have hdiff : quittingRootEndpointDifference reward 0 root second =
      if oldAction then
        -binarySecondDifference
          (paidSignFailureSwitchRow reward background first second oldAction)
          firstRate
      else
        binarySecondDifference
          (paidSignFailureSwitchRow reward background first second oldAction)
          firstRate := by
    rw [quittingRootEndpointDifference_eq_opponentMix
      reward 0 root hfirstSecond.symm]
    rw [hpure true, hpure false]
    cases oldAction
    · simp [root, paidSignFailureRoot, paidSignFailureActualLaw,
        paidSignFailureActualQuitRate, paidSignFailureSwitchRow,
        binarySecondDifference, hfirstSecond]
      ring
    · simp [root, paidSignFailureRoot, paidSignFailureActualLaw,
        paidSignFailureActualQuitRate, paidSignFailureSwitchRow,
        binarySecondDifference, hfirstSecond]
  have hsecond := hnash.2.2.2.2
  cases oldAction
  · have hfalseMass : (root second false).toReal = 1 - switchRate := by
      simp [root, paidSignFailureRoot, paidSignFailureActualLaw,
        paidSignFailureActualQuitRate]
    have htrueMass : (root second true).toReal = switchRate := by
      simp [root, paidSignFailureRoot, paidSignFailureActualLaw,
        paidSignFailureActualQuitRate]
    rw [hfalseMass, htrueMass, hdiff]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hsecond
  · have hfalseMass : (root second false).toReal = switchRate := by
      simp [root, paidSignFailureRoot, paidSignFailureActualLaw,
        paidSignFailureActualQuitRate]
    have htrueMass : (root second true).toReal = 1 - switchRate := by
      simp [root, paidSignFailureRoot, paidSignFailureActualLaw,
        paidSignFailureActualQuitRate]
    rw [hfalseMass, htrueMass, hdiff]
    simp only [↓reduceIte]
    constructor <;> nlinarith [hsecond.1, hsecond.2]

/-- With a sure-Quit owner, the concrete owner excess is exactly the semantic
punishment-floor inequality used by the singleton-base certificate. -/
theorem quittingSingletonBaseOwnerFloorExcess_nonpos_iff_of_owner_quits
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (root : ι → PMF Bool)
    (howner : root owner = PMF.pure true) :
    quittingSingletonBaseOwnerFloorExcess reward owner root ≤ 0 ↔
      quittingStationaryFixedOpponentsContinueReward reward root owner +
        quittingStationaryFixedOpponentsContinueMass root owner *
          quittingPunishmentValue reward owner ≤
        quittingRootAbsorbingContribution reward root owner := by
  have hcontinueMass : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter howner
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
    reward (fun _ => root) owner
      (fun _ => quittingPunishmentValue reward owner) 0
  have htarget := quittingRootExpectedPayoff_eq_absorbingContribution_add
    reward 0 root owner
  rw [quittingSingletonBaseOwnerFloorExcess, hcontinue, htarget,
    hcontinueMass]
  simp [quittingStationaryFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass,
    quittingFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueMass]

/-! ## Four-player semantic dispatch -/

/-- **Paid sign-failure ordered alternative.**  For four explicitly covered
players, the finite selection either satisfies the last free-player and
owner-floor tests and closes through the singleton-base all-behavior compiler,
or its literal normalized tests have one of the three strict residual signs.

The coverage hypothesis is essential: four distinct named players alone do
not exclude additional outsiders. -/
theorem exists_uniformPayoff_or_paidSignFailure_residual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (background : ι → PMF Bool)
    (owner first second remaining : ι)
    (oldAction remainingAction : Bool)
    (hownerFirst : owner ≠ first) (hownerSecond : owner ≠ second)
    (_hownerRemaining : owner ≠ remaining)
    (hfirstSecond : first ≠ second)
    (hfirstRemaining : first ≠ remaining)
    (hsecondRemaining : second ≠ remaining)
    (hcover : ∀ who, who = owner ∨ who = first ∨
      who = second ∨ who = remaining)
    (hbackgroundOwner : background owner = PMF.pure true)
    (hbackgroundRemaining : background remaining = PMF.pure remainingAction)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hjoinOld :
      paidSignFailureJoinRow reward background first second oldAction false ≤
        -gamma)
    (hswitchCleared : 0 <
      paidSignFailureSwitchRow reward background first second oldAction false)
    (hswitchPresent :
      paidSignFailureSwitchRow reward background first second oldAction true ≤
        0) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ selection : PaidSignFailureBinarySelection
          (paidSignFailureJoinRow reward background first second oldAction)
          (paidSignFailureSwitchRow reward background first second oldAction),
        let hnash := selection.isBinaryDifferenceNash hgamma hjoinOld
          hswitchCleared
        let root := paidSignFailureRoot background first second oldAction
          selection.firstRate selection.secondRate hnash.1 hnash.2.1
        let remainingNumerator := selection.denominator *
          quittingRootEndpointDifference reward 0 root remaining
        let ownerNumerator := selection.denominator *
          quittingSingletonBaseOwnerFloorExcess reward owner root
        (remainingAction = false ∧ 0 < remainingNumerator) ∨
          (remainingAction = true ∧ remainingNumerator < 0) ∨
          0 < ownerNumerator := by
  let join := paidSignFailureJoinRow reward background first second oldAction
  let switch := paidSignFailureSwitchRow reward background first second oldAction
  obtain ⟨selection⟩ :=
    PaidSignFailureBinarySelection.exists_of_sourceSigns
      hgamma hjoinOld hswitchCleared hswitchPresent
  let hnash : IsBinaryDifferenceNash join switch
      selection.firstRate selection.secondRate :=
    selection.isBinaryDifferenceNash hgamma hjoinOld hswitchCleared
  let root := paidSignFailureRoot background first second oldAction
    selection.firstRate selection.secondRate hnash.1 hnash.2.1
  let remainingNumerator := selection.denominator *
    quittingRootEndpointDifference reward 0 root remaining
  let ownerNumerator := selection.denominator *
    quittingSingletonBaseOwnerFloorExcess reward owner root
  have hdenominator : 0 < selection.denominator :=
    selection.denominator_pos hgamma hjoinOld hswitchCleared
  by_cases haccepted :
      (if remainingAction then 0 ≤ remainingNumerator
        else remainingNumerator ≤ 0) ∧ ownerNumerator ≤ 0
  · left
    have hrootOwner : root owner = PMF.pure true := by
      simp [root, paidSignFailureRoot, hownerFirst, hownerSecond,
        hbackgroundOwner]
    have hrootRemaining : root remaining = PMF.pure remainingAction := by
      simp [root, paidSignFailureRoot, hfirstRemaining.symm,
        hsecondRemaining.symm, hbackgroundRemaining]
    have hfloorExcess :
        quittingSingletonBaseOwnerFloorExcess reward owner root ≤ 0 := by
      dsimp only [ownerNumerator] at haccepted
      nlinarith [haccepted.2]
    let certificate : QuittingSingletonBaseCertificate reward owner root := {
      owner_quits := hrootOwner
      other_endpointNash := by
        intro who hwho
        rcases hcover who with howner | hfirst | hsecond | hremaining
        · exact (hwho howner).elim
        · subst who
          exact paidSignFailureRoot_first_endpointNash reward background
            hfirstSecond oldAction selection.firstRate selection.secondRate
              hnash.1 hnash.2.1 hnash
        · subst who
          exact paidSignFailureRoot_second_endpointNash reward background
            hfirstSecond oldAction selection.firstRate selection.secondRate
              hnash.1 hnash.2.1 hnash
        · subst who
          have hremainingSign :
              if remainingAction then
                0 ≤ quittingRootEndpointDifference reward 0 root remaining
              else
                quittingRootEndpointDifference reward 0 root remaining ≤ 0 := by
            dsimp only [remainingNumerator] at haccepted
            cases remainingAction
            · simp only [Bool.false_eq_true, ↓reduceIte] at haccepted ⊢
              nlinarith [haccepted.1]
            · simp only [↓reduceIte] at haccepted ⊢
              nlinarith [haccepted.1]
          cases remainingAction
          · simp [hrootRemaining]
            simpa using hremainingSign
          · simp [hrootRemaining]
            simpa using hremainingSign
      owner_floor_balance :=
        (quittingSingletonBaseOwnerFloorExcess_nonpos_iff_of_owner_quits
          reward owner root hrootOwner).1 hfloorExcess }
    exact ⟨quittingRootAbsorbingContribution reward root,
      certificate.isUniformEquilibriumPayoff⟩
  · right
    refine ⟨selection, ?_⟩
    dsimp only
    change (remainingAction = false ∧ 0 < remainingNumerator) ∨
      (remainingAction = true ∧ remainingNumerator < 0) ∨
      0 < ownerNumerator
    by_cases howner : ownerNumerator ≤ 0
    · have hremaining : ¬(if remainingAction then
          0 ≤ remainingNumerator else remainingNumerator ≤ 0) := by
        intro hsign
        exact haccepted ⟨hsign, howner⟩
      cases remainingAction
      · exact Or.inl ⟨rfl, lt_of_not_ge hremaining⟩
      · exact Or.inr (Or.inl ⟨rfl, lt_of_not_ge hremaining⟩)
    · exact Or.inr (Or.inr (lt_of_not_ge howner))

/-- A terminal exploitability witness excludes the accepted arm, leaving the
literal finite sign residual and no hidden strategy-class restriction. -/
theorem QuittingTerminalExploitabilityWitness.exists_paidSignFailure_residual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (background : ι → PMF Bool)
    (owner first second remaining : ι)
    (oldAction remainingAction : Bool)
    (hownerFirst : owner ≠ first) (hownerSecond : owner ≠ second)
    (hownerRemaining : owner ≠ remaining)
    (hfirstSecond : first ≠ second)
    (hfirstRemaining : first ≠ remaining)
    (hsecondRemaining : second ≠ remaining)
    (hcover : ∀ who, who = owner ∨ who = first ∨
      who = second ∨ who = remaining)
    (hbackgroundOwner : background owner = PMF.pure true)
    (hbackgroundRemaining : background remaining = PMF.pure remainingAction)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hjoinOld :
      paidSignFailureJoinRow reward background first second oldAction false ≤
        -gamma)
    (hswitchCleared : 0 <
      paidSignFailureSwitchRow reward background first second oldAction false)
    (hswitchPresent :
      paidSignFailureSwitchRow reward background first second oldAction true ≤
        0) :
    ∃ selection : PaidSignFailureBinarySelection
        (paidSignFailureJoinRow reward background first second oldAction)
        (paidSignFailureSwitchRow reward background first second oldAction),
      let hnash := selection.isBinaryDifferenceNash hgamma hjoinOld
        hswitchCleared
      let root := paidSignFailureRoot background first second oldAction
        selection.firstRate selection.secondRate hnash.1 hnash.2.1
      let remainingNumerator := selection.denominator *
        quittingRootEndpointDifference reward 0 root remaining
      let ownerNumerator := selection.denominator *
        quittingSingletonBaseOwnerFloorExcess reward owner root
      (remainingAction = false ∧ 0 < remainingNumerator) ∨
        (remainingAction = true ∧ remainingNumerator < 0) ∨
        0 < ownerNumerator := by
  rcases exists_uniformPayoff_or_paidSignFailure_residual reward background
      owner first second remaining oldAction remainingAction
      hownerFirst hownerSecond hownerRemaining hfirstSecond hfirstRemaining
      hsecondRemaining hcover hbackgroundOwner hbackgroundRemaining gamma
      hgamma hjoinOld hswitchCleared hswitchPresent with huniform | hresidual
  · exact (witness.not_exists_uniformEquilibriumPayoff huniform).elim
  · exact hresidual

/-! ## Source-native pure-paid adapter -/

/-- A failed first retained sign in the source-native pure-paid packet gives
exactly the three sign hypotheses used by the binary re-equilibration. -/
theorem PurePaidBaseLeaveSource.firstFailure_paidSignFailure_sourceSigns
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {gamma : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits gamma)
    (hfailure : if firstQuits then
        purePaidDeletedFirstDifference reward owner first second secondQuits < 0
      else
        0 < purePaidDeletedFirstDifference reward owner first second
          secondQuits) :
    let background := quittingPureSetRoot
      (purePaidDeletedCoalition owner first second firstQuits secondQuits)
    paidSignFailureJoinRow reward background paid first firstQuits false ≤
        -gamma ∧
      0 < paidSignFailureSwitchRow reward background paid first
        firstQuits false ∧
      paidSignFailureSwitchRow reward background paid first
        firstQuits true ≤ 0 := by
  intro background
  have hfirstOld : Function.update background first (PMF.pure firstQuits) =
      background := by
    cases firstQuits
    · simp [background,
        erase_first_purePaidDeletedCoalition source.owner_ne_first
          source.first_ne_second]
    · simp [background,
        insert_first_purePaidDeletedCoalition source.owner_ne_first
          source.first_ne_second]
  have hpaidAbsent : Function.update background paid (PMF.pure false) =
      background := by
    rw [show Function.update background paid (PMF.pure false) =
        quittingPureSetRoot
          ((purePaidDeletedCoalition owner first second firstQuits
            secondQuits).erase paid) by
      exact update_quittingPureSetRoot_false _ paid]
    rw [Finset.erase_eq_of_notMem
      (paid_not_mem_purePaidDeletedCoalition source.paid_ne_owner
        source.paid_ne_first source.paid_ne_second firstQuits secondQuits)]
  have hpaidPresent : Function.update background paid (PMF.pure true) =
      quittingPureSetRoot
        (purePaidOriginalCoalition paid owner first second
          firstQuits secondQuits) := by
    rw [show Function.update background paid (PMF.pure true) =
        quittingPureSetRoot
          (insert paid (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) by
      exact update_quittingPureSetRoot_true _ paid]
    rfl
  have hjoinOld :
      paidSignFailureJoinRow reward background paid first firstQuits false ≤
        -gamma := by
    rw [paidSignFailureJoinRow]
    simp only [Bool.xor_false]
    rw [hfirstOld,
      quittingRootEndpointDifference_purePaidDeleted_paid reward
        source.paid_ne_owner source.paid_ne_first source.paid_ne_second]
    linarith [source.paidLeave]
  have hdeletedEndpoint :
      quittingRootEndpointDifference reward 0 background first =
        purePaidDeletedFirstDifference reward owner first second
          secondQuits := by
    exact quittingRootEndpointDifference_purePaidDeleted_first reward
      source.owner_ne_first source.first_ne_second firstQuits secondQuits
  have hswitchCleared : 0 <
      paidSignFailureSwitchRow reward background paid first
        firstQuits false := by
    rw [paidSignFailureSwitchRow]
    simp only [hpaidAbsent, hdeletedEndpoint]
    cases firstQuits <;> simp_all
  have horiginalEndpoint :
      quittingRootEndpointDifference reward 0
          (Function.update background paid (PMF.pure true)) first =
        quittingSetReward reward
            (purePaidOriginalCoalition paid owner first second true
              secondQuits) first -
          quittingSetReward reward
            (purePaidOriginalCoalition paid owner first second false
              secondQuits) first := by
    rw [hpaidPresent, quittingRootEndpointDifference]
    have hinsertFirst :
        insert first (purePaidOriginalCoalition paid owner first second
          firstQuits secondQuits) =
          purePaidOriginalCoalition paid owner first second true
            secondQuits := by
      rw [purePaidOriginalCoalition_eq_insert,
        purePaidOriginalCoalition_eq_insert,
        Finset.insert_comm first paid,
        insert_first_purePaidDeletedCoalition source.owner_ne_first
          source.first_ne_second]
    have heraseFirst :
        (purePaidOriginalCoalition paid owner first second
          firstQuits secondQuits).erase first =
          purePaidOriginalCoalition paid owner first second false
            secondQuits := by
      rw [purePaidOriginalCoalition_eq_insert,
        purePaidOriginalCoalition_eq_insert,
        Finset.erase_insert_of_ne source.paid_ne_first,
        erase_first_purePaidDeletedCoalition source.owner_ne_first
          source.first_ne_second]
    have herase :
        ((purePaidOriginalCoalition paid owner first second
          firstQuits secondQuits).erase first).Nonempty := by
      refine ⟨owner, Finset.mem_erase.mpr ⟨source.owner_ne_first, ?_⟩⟩
      simp [purePaidOriginalCoalition, purePaidDeletedCoalition]
    rw [quittingRootQuitPayoff_pureSetRoot_eq_insert,
      quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
        (0 : Payoff ι) _ first herase,
      hinsertFirst, heraseFirst]
  have hswitchPresent :
      paidSignFailureSwitchRow reward background paid first
        firstQuits true ≤ 0 := by
    rw [paidSignFailureSwitchRow]
    simp only [horiginalEndpoint]
    have horiginal := source.originalPureNash.1
    cases firstQuits <;> simp_all
  exact ⟨hjoinOld, hswitchCleared, hswitchPresent⟩

omit [Fintype ι] in
theorem purePaidRetainedSet_swap
    (first second : ι) (firstQuits secondQuits : Bool) :
    purePaidRetainedSet second first secondQuits firstQuits =
      purePaidRetainedSet first second firstQuits secondQuits := by
  cases firstQuits <;> cases secondQuits <;>
    simp [purePaidRetainedSet, Finset.union_comm]

omit [Fintype ι] in
theorem purePaidDeletedCoalition_swap
    (owner first second : ι) (firstQuits secondQuits : Bool) :
    purePaidDeletedCoalition owner second first secondQuits firstQuits =
      purePaidDeletedCoalition owner first second firstQuits secondQuits := by
  simp [purePaidDeletedCoalition, purePaidRetainedSet_swap]

omit [Fintype ι] in
theorem purePaidOriginalCoalition_swap
    (paid owner first second : ι) (firstQuits secondQuits : Bool) :
    purePaidOriginalCoalition paid owner second first secondQuits firstQuits =
      purePaidOriginalCoalition paid owner first second
        firstQuits secondQuits := by
  simp [purePaidOriginalCoalition, purePaidDeletedCoalition_swap]

omit [Fintype ι] in
/-- Exchange the two free labels of a source-native paid pure packet. -/
theorem PurePaidBaseLeaveSource.swapFree
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {gamma : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits gamma) :
    PurePaidBaseLeaveSource reward paid owner second first
      secondQuits firstQuits gamma := by
  refine {
    paid_ne_owner := source.paid_ne_owner
    paid_ne_first := source.paid_ne_second
    paid_ne_second := source.paid_ne_first
    owner_ne_first := source.owner_ne_second
    owner_ne_second := source.owner_ne_first
    first_ne_second := source.first_ne_second.symm
    exhaust := ?_
    originalPureNash := ?_
    gamma_pos := source.gamma_pos
    paidLeave := ?_ }
  · intro who
    rcases source.exhaust who with hpaid | howner | hfirst | hsecond
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl howner)
    · exact Or.inr (Or.inr (Or.inr hfirst))
    · exact Or.inr (Or.inr (Or.inl hsecond))
  · have hfirstRow :
        (fun action ↦
          quittingSetReward reward
              (purePaidOriginalCoalition paid owner second first true action)
              second -
            quittingSetReward reward
              (purePaidOriginalCoalition paid owner second first false action)
              second) =
          (fun action ↦
            quittingSetReward reward
                (purePaidOriginalCoalition paid owner first second action true)
                second -
              quittingSetReward reward
                (purePaidOriginalCoalition paid owner first second action false)
                second) := by
      funext action
      rw [purePaidOriginalCoalition_swap paid owner first second action true,
        purePaidOriginalCoalition_swap paid owner first second action false]
    have hsecondRow :
        (fun action ↦
          quittingSetReward reward
              (purePaidOriginalCoalition paid owner second first action true)
              first -
            quittingSetReward reward
              (purePaidOriginalCoalition paid owner second first action false)
              first) =
          (fun action ↦
            quittingSetReward reward
                (purePaidOriginalCoalition paid owner first second true action)
                first -
              quittingSetReward reward
                (purePaidOriginalCoalition paid owner first second false action)
                first) := by
      funext action
      rw [purePaidOriginalCoalition_swap paid owner first second true action,
        purePaidOriginalCoalition_swap paid owner first second false action]
    rw [hfirstRow, hsecondRow]
    exact And.intro source.originalPureNash.2 source.originalPureNash.1
  · rw [purePaidDeletedCoalition_swap owner first second firstQuits secondQuits,
      purePaidOriginalCoalition_swap paid owner first second firstQuits
        secondQuits]
    exact source.paidLeave

/-- The symmetric failed retained sign has the same exact source adapter. -/
theorem PurePaidBaseLeaveSource.secondFailure_paidSignFailure_sourceSigns
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {gamma : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits gamma)
    (hfailure : if secondQuits then
        purePaidDeletedSecondDifference reward owner first second firstQuits < 0
      else
        0 < purePaidDeletedSecondDifference reward owner first second
          firstQuits) :
    let background := quittingPureSetRoot
      (purePaidDeletedCoalition owner second first secondQuits firstQuits)
    paidSignFailureJoinRow reward background paid second secondQuits false ≤
        -gamma ∧
      0 < paidSignFailureSwitchRow reward background paid second
        secondQuits false ∧
      paidSignFailureSwitchRow reward background paid second
        secondQuits true ≤ 0 := by
  apply source.swapFree.firstFailure_paidSignFailure_sourceSigns
  simpa [purePaidDeletedFirstDifference, purePaidDeletedSecondDifference,
    purePaidDeletedCoalition_swap] using hfailure

end GameTheory
