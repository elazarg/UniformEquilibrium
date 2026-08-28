/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.ConstrainedAffineNormalWork
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import UniformEquilibrium.Quitting.Root.FaceGeometry

/-!
# Constrained-root normal work and minimum leakage

This module isolates the exact local algebra of a root whose Quit marginal is
constrained below by a coordinatewise floor.  The root certificate is a
literal complementarity interface; no existence theorem is smuggled into the
definition.  Prefixing an actual semantic tail remains actual, but the local
ledger supplies no orientation or cancellation of the repayment entering the
other coordinates.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Exact coordinatewise complementarity for affine optimization on
`[lower who, 1]`.  The two product equalities are the literal lower- and
upper-face KKT conditions; existence is a separate compact-game question. -/
def IsQuittingLowerBoundConstrainedRoot
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail lower : Payoff iota) (root : iota → PMF Bool) : Prop :=
  (∀ who, lower who ≤ (root who true).toReal) ∧
  ∀ who,
    (root who false).toReal *
        max (quittingRootEndpointDifference reward tail root who) 0 = 0 ∧
      ((root who true).toReal - lower who) *
        max (-quittingRootEndpointDifference reward tail root who) 0 = 0

/-- Lower-face normal work left by the constrained optimum when the
unconstrained endpoint slope points toward Continue. -/
def quittingLowerFaceNormalWork
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail lower : Payoff iota) (root : iota → PMF Bool)
    (who : iota) : ℝ :=
  lower who * max (-quittingRootEndpointDifference reward tail root who) 0

/-- The part of inherited cap debt shielded by the old positive endpoint
advantage. -/
def quittingInheritedCapShield
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) (who : iota) : ℝ :=
  min
    (quittingRootOpponentContinueMass root who *
      quittingTerminalSemanticDebt pair who)
    (max (quittingRootEndpointDifference reward pair.1 root who) 0)

/-- The constrained literal coordinate defect is exactly its lower-face
normal work. -/
theorem constrainedRootCoordinateNashDefect_eq_normalWork
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail lower : Payoff iota) (root : iota → PMF Bool)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward tail lower root)
    (who : iota) :
    quittingRootCoordinateNashDefect reward tail root who =
      quittingLowerFaceNormalWork reward tail lower root who := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hcontinue : 1 - (root who true).toReal =
      (root who false).toReal := by linarith
  unfold quittingLowerFaceNormalWork
  rw [← hcontinue]
  exact Math.affineBinaryDefect_eq_lowerFaceNormalWork
    (lower who) (root who true).toReal
      (quittingRootEndpointDifference reward tail root who)
      (by rw [hcontinue]; exact (hroot.2 who).1) (hroot.2 who).2

/-- Exact inherited-cap surcharge: transported tail debt minus the amount
shielded by the old positive literal endpoint gap. -/
theorem quittingRootContinuationOptionSurcharge_eq_inherited_sub_shield
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) (who : iota)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingRootContinuationOptionSurcharge reward pair root who =
      quittingRootOpponentContinueMass root who *
          quittingTerminalSemanticDebt pair who -
        quittingInheritedCapShield reward pair root who := by
  rw [quittingRootContinuationOptionSurcharge_eq_max_increment]
  exact Math.max_add_sub_max_eq_addend_sub_min _ _ _
    (mul_nonneg (quittingRootOpponentContinueMass_nonneg root who)
      (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who))

/-- Coordinatewise constrained normal-work decomposition of the literal
prefixed semantic debt. -/
theorem constrainedRoot_terminalDebt_eq_normalWork_add_inherited_sub_shield
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward pair.1 lower root)
    (who : iota) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingLowerFaceNormalWork reward pair.1 lower root who +
        quittingRootOpponentContinueMass root who *
          quittingTerminalSemanticDebt pair who -
        quittingInheritedCapShield reward pair root who := by
  rw [quittingTerminalSemanticDebt_prefix_eq_literalDefect_add_surcharge,
    constrainedRootCoordinateNashDefect_eq_normalWork
      reward pair.1 lower root hroot who,
    quittingRootContinuationOptionSurcharge_eq_inherited_sub_shield
      reward pair root who hpair]
  ring

/-- Total lower-face normal work. -/
def quittingTotalLowerFaceNormalWork
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail lower : Payoff iota) (root : iota → PMF Bool) : ℝ :=
  ∑ who, quittingLowerFaceNormalWork reward tail lower root who

/-- Exact total ledger.  The three terms on the right are respectively the
change in excess over any reference level, killed inherited debt, and the
positive-gap shield. -/
theorem constrainedRoot_totalNormalWork_eq_excessChange_add_killed_add_shield
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward pair.1 lower root)
    (reference : ℝ) :
    quittingTotalLowerFaceNormalWork reward pair.1 lower root =
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) - reference) -
        (quittingTerminalSemanticDebtSum pair - reference) +
      ∑ who, (1 - quittingRootOpponentContinueMass root who) *
        quittingTerminalSemanticDebt pair who +
      ∑ who, quittingInheritedCapShield reward pair root who := by
  unfold quittingTotalLowerFaceNormalWork
    quittingTerminalSemanticDebtSum
  simp_rw [constrainedRoot_terminalDebt_eq_normalWork_add_inherited_sub_shield
    reward pair lower root hpair hroot]
  simp_rw [sub_mul, one_mul]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- A scalar lower floor is seen by every deleted-player clock when each
player has some distinct coordinate carrying at least that floor. -/
def IsQuittingLowerFloorCovered
    (lower : Payoff iota) (floor : ℝ) : Prop :=
  ∀ who, ∃ other, other ≠ who ∧ floor ≤ lower other

/-- Values of the lower floor away from one deleted coordinate. -/
def quittingOtherLowerValues [Nontrivial iota]
    (lower : Payoff iota) (who : iota) : Finset ℝ :=
  (Finset.univ.erase who).image lower

theorem quittingOtherLowerValues_nonempty [Nontrivial iota]
    (lower : Payoff iota) (who : iota) :
    (quittingOtherLowerValues lower who).Nonempty := by
  obtain ⟨other, hother⟩ := exists_ne who
  exact ⟨lower other, Finset.mem_image.mpr
    ⟨other, by simp [hother], rfl⟩⟩

/-- Largest lower floor visible away from `who`. -/
def quittingOtherLowerMaximum [Nontrivial iota]
    (lower : Payoff iota) (who : iota) : ℝ :=
  (quittingOtherLowerValues lower who).max'
    (quittingOtherLowerValues_nonempty lower who)

/-- Packet scalar `κ(lower) = min_i max_{j ≠ i} lower_j`. -/
def quittingLowerFloorKappa [Nontrivial iota]
    (lower : Payoff iota) : ℝ :=
  ((Finset.univ : Finset iota).image
      (quittingOtherLowerMaximum lower)).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- The finite min-max value literally covers every deleted coordinate. -/
theorem lowerFloorCovered_quittingLowerFloorKappa [Nontrivial iota]
    (lower : Payoff iota) :
    IsQuittingLowerFloorCovered lower
      (quittingLowerFloorKappa lower) := by
  intro who
  have hkappa : quittingLowerFloorKappa lower ≤
      quittingOtherLowerMaximum lower who := by
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨who, Finset.mem_univ who, rfl⟩
  have hmaximum := Finset.max'_mem
    (quittingOtherLowerValues lower who)
      (quittingOtherLowerValues_nonempty lower who)
  obtain ⟨other, hother, hvalue⟩ := Finset.mem_image.mp hmaximum
  refine ⟨other, Finset.ne_of_mem_erase hother, ?_⟩
  rw [hvalue]
  exact hkappa

/-- Nonnegative component floors make the packet scalar nonnegative. -/
theorem quittingLowerFloorKappa_nonneg [Nontrivial iota]
    (lower : Payoff iota) (hlower0 : ∀ who, 0 ≤ lower who) :
    0 ≤ quittingLowerFloorKappa lower := by
  apply Finset.le_min'
  intro maximum hmaximum
  obtain ⟨who, _, rfl⟩ := Finset.mem_image.mp hmaximum
  have hmember := Finset.max'_mem
    (quittingOtherLowerValues lower who)
      (quittingOtherLowerValues_nonempty lower who)
  obtain ⟨other, _, hvalue⟩ := Finset.mem_image.mp hmember
  change 0 ≤ (quittingOtherLowerValues lower who).max' _
  rw [← hvalue]
  exact hlower0 other

/-- Floor coverage and the root's literal marginal floors bound every killed
deleted-clock fraction. -/
theorem floor_le_one_sub_opponentContinueMass
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail lower : Payoff iota) (root : iota → PMF Bool)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward tail lower root)
    {floor : ℝ} (hcovered : IsQuittingLowerFloorCovered lower floor)
    (who : iota) :
    floor ≤ 1 - quittingRootOpponentContinueMass root who := by
  obtain ⟨other, hne, hfloor⟩ := hcovered who
  have hquit := quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne
    root hne
  rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass]
  linarith [hfloor.trans (hroot.1 other), hquit]

/-- Near a global positive debt floor, covered constrained clocks must spend
first-order total normal work. -/
theorem nearMinimum_totalNormalWork_ge_floor_mul_minimum_sub_excess
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward pair.1 lower root)
    (minimum floor : ℝ)
    (hfloor : 0 ≤ floor)
    (hpairMinimum : minimum ≤ quittingTerminalSemanticDebtSum pair)
    (hprefixMinimum : minimum ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward root pair))
    (hcovered : IsQuittingLowerFloorCovered lower floor) :
    floor * minimum -
        (quittingTerminalSemanticDebtSum pair - minimum) ≤
      quittingTotalLowerFaceNormalWork reward pair.1 lower root := by
  have hledger :=
    constrainedRoot_totalNormalWork_eq_excessChange_add_killed_add_shield
      reward pair lower root hpair hroot minimum
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hkilled : floor * quittingTerminalSemanticDebtSum pair ≤
      ∑ who, (1 - quittingRootOpponentContinueMass root who) *
        quittingTerminalSemanticDebt pair who := by
    unfold quittingTerminalSemanticDebtSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun who _ =>
      mul_le_mul_of_nonneg_right
        (floor_le_one_sub_opponentContinueMass
          reward pair.1 lower root hroot hcovered who) (hdebt who)
  have hshield : 0 ≤
      ∑ who, quittingInheritedCapShield reward pair root who := by
    apply Finset.sum_nonneg
    intro who _
    exact le_min
      (mul_nonneg (quittingRootOpponentContinueMass_nonneg root who)
        (hdebt who)) (le_max_right _ _)
  nlinarith

/-- Literal `κ(lower)` specialization of the covered-floor lower bound. -/
theorem nearMinimum_totalNormalWork_ge_kappa_mul_minimum_sub_excess
    [Nontrivial iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward pair.1 lower root)
    (hlower0 : ∀ who, 0 ≤ lower who)
    (minimum : ℝ)
    (hpairMinimum : minimum ≤ quittingTerminalSemanticDebtSum pair)
    (hprefixMinimum : minimum ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward root pair)) :
    quittingLowerFloorKappa lower * minimum -
        (quittingTerminalSemanticDebtSum pair - minimum) ≤
      quittingTotalLowerFaceNormalWork reward pair.1 lower root := by
  exact nearMinimum_totalNormalWork_ge_floor_mul_minimum_sub_excess
    reward pair lower root hpair hroot minimum
      (quittingLowerFloorKappa lower)
      (quittingLowerFloorKappa_nonneg lower hlower0)
      hpairMinimum hprefixMinimum
      (lowerFloorCovered_quittingLowerFloorKappa lower)

omit [Fintype iota] in
/-- Two displayed floor coordinates cover every deleted-player clock. -/
theorem lowerFloorCovered_of_two
    (lower : Payoff iota) {floor : ℝ} {first second : iota}
    (hne : first ≠ second)
    (hfirst : floor ≤ lower first) (hsecond : floor ≤ lower second) :
    IsQuittingLowerFloorCovered lower floor := by
  intro who
  by_cases hwho : first = who
  · exact ⟨second, by simpa [hwho] using hne.symm, hsecond⟩
  · exact ⟨first, hwho, hfirst⟩

/-- Any scalar covered away from every deleted coordinate lies below the
literal finite min--max floor `κ(lower)`. -/
theorem floor_le_quittingLowerFloorKappa_of_covered [Nontrivial iota]
    (lower : Payoff iota) {floor : ℝ}
    (hcovered : IsQuittingLowerFloorCovered lower floor) :
    floor ≤ quittingLowerFloorKappa lower := by
  apply Finset.le_min'
  intro maximum hmaximum
  obtain ⟨who, _, rfl⟩ := Finset.mem_image.mp hmaximum
  obtain ⟨other, hother, hfloor⟩ := hcovered who
  exact hfloor.trans (Finset.le_max'
    (quittingOtherLowerValues lower who) (lower other)
      (Finset.mem_image.mpr ⟨other, by simp [hother], rfl⟩))

/-- Two distinct coordinates at floor `floor` give the packet's displayed
lower bound `floor ≤ κ(lower)`. -/
theorem floor_le_quittingLowerFloorKappa_of_two [Nontrivial iota]
    (lower : Payoff iota) {floor : ℝ} {first second : iota}
    (hne : first ≠ second)
    (hfirst : floor ≤ lower first) (hsecond : floor ≤ lower second) :
    floor ≤ quittingLowerFloorKappa lower := by
  exact floor_le_quittingLowerFloorKappa_of_covered lower
    (lowerFloorCovered_of_two lower hne hfirst hsecond)

/-! ## Binding-floor removal and exact repayment -/

/-- A strictly negative endpoint gap binds the constrained Quit marginal at
its declared lower face. -/
theorem constrainedRoot_quitProbability_eq_lower_of_gap_neg
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail lower : Payoff iota) (root : iota → PMF Bool)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward tail lower root)
    (who : iota)
    (hgap : quittingRootEndpointDifference reward tail root who < 0) :
    (root who true).toReal = lower who := by
  have hpositive : 0 <
      max (-quittingRootEndpointDifference reward tail root who) 0 := by
    rw [max_eq_left]
    · linarith
    · linarith
  have hnormal := (hroot.2 who).2
  rcases mul_eq_zero.mp hnormal with hdifference | hmaximum
  · exact sub_eq_zero.mp hdifference
  · exact False.elim (hpositive.ne' hmaximum)

/-- Removing a binding lower-face Quit marginal raises the mover's literal
prefixed payoff by exactly its normal work. -/
theorem lowerFaceRemoval_payoffGain_eq_normalWork
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (continuation : (quittingGame reward).BehaviorProfile)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      lower root)
    (who : iota)
    (hgap : quittingRootEndpointDifference reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      root who < 0) :
    quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward
            (Function.update root who (PMF.pure false)) continuation) who -
        quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) who =
      quittingLowerFaceNormalWork reward
        (fun player ↦ quittingTerminalPayoff reward continuation player)
        lower root who := by
  rw [quittingTerminalPayoff_rootThenContinuation_eq,
    quittingTerminalPayoff_rootThenContinuation_eq]
  have hchange := quittingRootExpectedPayoff_update_sub_successorPayoff
    reward (fun player ↦ quittingTerminalPayoff reward continuation player)
      root who (PMF.pure false)
  have hchange' :
      quittingRootExpectedPayoff reward
            (fun player ↦ quittingTerminalPayoff reward continuation player)
            (Function.update root who (PMF.pure false)) who -
          quittingRootExpectedPayoff reward
            (fun player ↦ quittingTerminalPayoff reward continuation player)
            root who =
        -(root who true).toReal *
          quittingRootEndpointDifference reward
            (fun player ↦ quittingTerminalPayoff reward continuation player)
            root who := by
    simpa [quittingRootSuccessorPayoff, PMF.pure_apply] using hchange
  rw [constrainedRoot_quitProbability_eq_lower_of_gap_neg
    reward _ lower root hroot who hgap] at hchange'
  unfold quittingLowerFaceNormalWork
  rw [max_eq_left (by linarith :
    0 ≤ -quittingRootEndpointDifference reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      root who)]
  linarith [hchange']

/-- The two literal root-prefix profiles in a lower-face removal differ only
in the mover's complete behavior strategy. -/
theorem update_rootThenContinuation_eq_forceContinue
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : iota → PMF Bool) (who : iota) :
    Function.update
        (quittingRootThenContinuationProfile reward root continuation) who
        ((quittingRootThenContinuationProfile reward
          (Function.update root who (PMF.pure false)) continuation) who) =
      quittingRootThenContinuationProfile reward
        (Function.update root who (PMF.pure false)) continuation := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    simp
  · simp [Function.update_of_ne hplayer,
      quittingRootThenContinuationProfile]

/-- The binding mover's semantic debt falls by exactly its normal work under
the literal self-strategy removal. -/
theorem lowerFaceRemoval_moverDebt_eq_sub_normalWork
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (continuation : (quittingGame reward).BehaviorProfile)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      lower root)
    (who : iota)
    (hgap : quittingRootEndpointDifference reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      root who < 0) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward
            (Function.update root who (PMF.pure false)) continuation)) who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root continuation)) who -
        quittingLowerFaceNormalWork reward
          (fun player ↦ quittingTerminalPayoff reward continuation player)
          lower root who := by
  let source := quittingRootThenContinuationProfile reward root continuation
  let target := quittingRootThenContinuationProfile reward
    (Function.update root who (PMF.pure false)) continuation
  have hupdate : Function.update source who (target who) = target := by
    exact update_rootThenContinuation_eq_forceContinue
      reward continuation root who
  have hdebt := quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward source who (target who)
  rw [hupdate] at hdebt
  rw [hdebt, lowerFaceRemoval_payoffGain_eq_normalWork
    reward continuation lower root hroot who hgap]

/-- Global minimality forces the exact complementary repayment account after
a binding lower-face removal.  This is an aggregate signed identity and does
not select or orient a recipient. -/
theorem lowerFaceRemoval_otherDebtChange_sum_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (continuation : (quittingGame reward).BehaviorProfile)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      lower root)
    (who : iota)
    (hgap : quittingRootEndpointDifference reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      root who < 0) :
    let source := quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward root continuation)
    let target := quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward
        (Function.update root who (PMF.pure false)) continuation)
    ∑ other ∈ Finset.univ.erase who,
        (quittingTerminalSemanticDebt target other -
          quittingTerminalSemanticDebt source other) =
      quittingTerminalSemanticDebtSum target -
        quittingTerminalSemanticDebtSum source +
      quittingLowerFaceNormalWork reward
        (fun player ↦ quittingTerminalPayoff reward continuation player)
        lower root who := by
  dsimp only
  have hmover := lowerFaceRemoval_moverDebt_eq_sub_normalWork
    reward continuation lower root hroot who hgap
  unfold quittingTerminalSemanticDebtSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
  simp only [Finset.sum_sub_distrib]
  linarith

/-- Minimum-fiber consequence of the exact account: complementary debt
increase is at least work minus the source's excess over the minimum. -/
theorem lowerFaceRemoval_work_sub_excess_le_otherDebtChange_sum
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (continuation : (quittingGame reward).BehaviorProfile)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      lower root)
    (who : iota)
    (hgap : quittingRootEndpointDifference reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      root who < 0)
    (minimum : ℝ)
    (htarget : minimum ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward
          (Function.update root who (PMF.pure false)) continuation))) :
    quittingLowerFaceNormalWork reward
          (fun player ↦ quittingTerminalPayoff reward continuation player)
          lower root who -
        (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root continuation)) -
          minimum) ≤
      ∑ other ∈ Finset.univ.erase who,
        (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward
                (Function.update root who (PMF.pure false)) continuation)) other -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward root continuation))
            other) := by
  rw [lowerFaceRemoval_otherDebtChange_sum_eq
    reward continuation lower root hroot who hgap]
  linarith

/-- Some distinct coordinate receives at least the average signed repayment.
No nonnegativity or label orientation of the remaining coordinate changes is
assumed. -/
theorem exists_other_lowerFaceRemoval_averageRepayment
    [Nontrivial iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (continuation : (quittingGame reward).BehaviorProfile)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      lower root)
    (who : iota)
    (hgap : quittingRootEndpointDifference reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      root who < 0)
    (minimum : ℝ)
    (htarget : minimum ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward
          (Function.update root who (PMF.pure false)) continuation))) :
    ∃ other, other ≠ who ∧
      (quittingLowerFaceNormalWork reward
            (fun player ↦ quittingTerminalPayoff reward continuation player)
            lower root who -
          (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward root continuation)) -
            minimum)) /
          ((Finset.univ.erase who).card : ℝ) ≤
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward
                (Function.update root who (PMF.pure false)) continuation))
            other -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward root continuation))
            other := by
  let recipients := Finset.univ.erase who
  have hrecipients : recipients.Nonempty := by
    obtain ⟨other, hother⟩ := exists_ne who
    exact ⟨other, by simp [recipients, hother]⟩
  have hcardPos : 0 < (recipients.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hrecipients
  have hsum := lowerFaceRemoval_work_sub_excess_le_otherDebtChange_sum
    reward continuation lower root hroot who hgap minimum htarget
  change _ ≤ Finset.sum recipients (fun other =>
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward
            (Function.update root who (PMF.pure false)) continuation)) other -
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward root continuation))
        other) at hsum
  have haverageSum :
      ∑ _other ∈ recipients,
          (quittingLowerFaceNormalWork reward
                (fun player ↦ quittingTerminalPayoff reward continuation player)
                lower root who -
              (quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (quittingRootThenContinuationProfile reward root continuation)) -
                minimum)) /
            (recipients.card : ℝ) ≤
        Finset.sum recipients (fun other =>
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingRootThenContinuationProfile reward
                  (Function.update root who (PMF.pure false)) continuation))
              other -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingRootThenContinuationProfile reward root continuation))
              other) := by
    rw [Finset.sum_const, nsmul_eq_mul,
      mul_div_cancel₀ _ hcardPos.ne']
    exact hsum
  obtain ⟨other, hother, haverage⟩ :=
    Finset.exists_le_of_sum_le hrecipients haverageSum
  exact ⟨other, Finset.ne_of_mem_erase hother, by
    simpa [recipients] using haverage⟩

/-- If the mover is the source's only debtor and work strictly exceeds the
source excess, the average-repayment coordinate is a genuine new positive
target debt.  This is the precise support-entry consequence of the aggregate
ledger; without the unique-debtor hypothesis it would only orient a signed
change, not the target debt itself. -/
theorem lowerFaceRemoval_exists_supportEntry_of_uniqueDebtor
    [Nontrivial iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (continuation : (quittingGame reward).BehaviorProfile)
    (lower : Payoff iota) (root : iota → PMF Bool)
    (hroot : IsQuittingLowerBoundConstrainedRoot reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      lower root)
    (who : iota)
    (hgap : quittingRootEndpointDifference reward
      (fun player ↦ quittingTerminalPayoff reward continuation player)
      root who < 0)
    (minimum : ℝ)
    (htarget : minimum ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward
          (Function.update root who (PMF.pure false)) continuation)))
    (hunique : ∀ other, other ≠ who →
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward root continuation))
        other = 0)
    (hrepayment :
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root continuation)) -
        minimum <
      quittingLowerFaceNormalWork reward
        (fun player ↦ quittingTerminalPayoff reward continuation player)
        lower root who) :
    ∃ other, other ≠ who ∧
      0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward
            (Function.update root who (PMF.pure false)) continuation)) other ∧
      (quittingLowerFaceNormalWork reward
            (fun player ↦ quittingTerminalPayoff reward continuation player)
            lower root who -
          (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward root continuation)) -
            minimum)) /
          ((Finset.univ.erase who).card : ℝ) ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward
              (Function.update root who (PMF.pure false)) continuation)) other := by
  obtain ⟨other, hother, haverage⟩ :=
    exists_other_lowerFaceRemoval_averageRepayment
      reward continuation lower root hroot who hgap minimum htarget
  have hcard : 0 < ((Finset.univ.erase who).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨other, by simpa using hother⟩
  have hsourceZero := hunique other hother
  have hlowerPositive : 0 <
      (quittingLowerFaceNormalWork reward
            (fun player ↦ quittingTerminalPayoff reward continuation player)
            lower root who -
          (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward root continuation)) -
            minimum)) /
        ((Finset.univ.erase who).card : ℝ) := by
    exact div_pos (by linarith) hcard
  refine ⟨other, hother, ?_, ?_⟩
  · rw [hsourceZero] at haverage
    linarith
  · simpa [hsourceZero] using haverage

/-! ## Finite backward blocks and signed cut balance -/

/-- The exact row ledger telescopes along any supplied finite backward block.
This is a flat sum of conditional row work, not a reach-weighted charge. -/
theorem constrainedRoot_finiteBackwardBlock_telescope
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : ℕ → QuittingTerminalSemanticPair iota)
    (lower : ℕ → Payoff iota) (root : ℕ → iota → PMF Bool)
    (hcarrier : ∀ time,
      pair (time + 1) ∈ quittingTerminalSemanticCarrier reward)
    (hroot : ∀ time,
      IsQuittingLowerBoundConstrainedRoot reward
        (pair (time + 1)).1 (lower time) (root time))
    (hstep : ∀ time,
      pair time = quittingTerminalSemanticPrefix reward
        (root time) (pair (time + 1)))
    (reference : ℝ) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
        quittingTotalLowerFaceNormalWork reward
          (pair (time + 1)).1 (lower time) (root time)) =
      (quittingTerminalSemanticDebtSum (pair 0) - reference) -
        (quittingTerminalSemanticDebtSum (pair horizon) - reference) +
      ∑ time ∈ Finset.range horizon,
        ∑ who, (1 - quittingRootOpponentContinueMass (root time) who) *
          quittingTerminalSemanticDebt (pair (time + 1)) who +
      ∑ time ∈ Finset.range horizon,
        ∑ who, quittingInheritedCapShield reward
          (pair (time + 1)) (root time) who := by
  apply Math.sum_range_work_eq_excess_telescope
    (work := fun time => quittingTotalLowerFaceNormalWork reward
      (pair (time + 1)).1 (lower time) (root time))
    (excess := fun time =>
      quittingTerminalSemanticDebtSum (pair time) - reference)
    (killed := fun time =>
      ∑ who, (1 - quittingRootOpponentContinueMass (root time) who) *
        quittingTerminalSemanticDebt (pair (time + 1)) who)
    (shield := fun time =>
      ∑ who, quittingInheritedCapShield reward
        (pair (time + 1)) (root time) who)
  intro time
  have hledger :=
    constrainedRoot_totalNormalWork_eq_excessChange_add_killed_add_shield
      reward (pair (time + 1)) (lower time) (root time)
        (hcarrier time) (hroot time) reference
  rw [← hstep time] at hledger
  exact hledger

/-- Every finite sequence of literal own-strategy replacements satisfies the
exact signed cut balance.  This theorem preserves actual behavioral profiles,
but it does not orient any complementary debt change. -/
theorem actualOwnStrategyRemoval_finiteDebtCutBalance
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ℕ → iota)
    (hupdate : ∀ time,
      Function.update (profile time) (mover time)
          (profile (time + 1) (mover time)) =
        profile (time + 1))
    (labels : Finset iota) (horizon : ℕ) :
    Finset.sum labels (fun player =>
      quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profile horizon)) player -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profile 0)) player) =
      -(∑ time ∈ Finset.range horizon,
          if mover time ∈ labels then
            quittingTerminalPayoff reward (profile (time + 1)) (mover time) -
              quittingTerminalPayoff reward (profile time) (mover time)
          else 0) +
        ∑ time ∈ Finset.range horizon,
          Finset.sum (labels.erase (mover time)) (fun player =>
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward (profile (time + 1)))
                player -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward (profile time)) player) := by
  apply Math.finiteDebtCutBalance
    (debt := fun time player => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (profile time)) player)
    (mover := mover)
    (work := fun time =>
      quittingTerminalPayoff reward (profile (time + 1)) (mover time) -
        quittingTerminalPayoff reward (profile time) (mover time))
  intro time
  have hdebt := quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward (profile time) (mover time) (profile (time + 1) (mover time))
  rw [hupdate time] at hdebt
  exact hdebt

end GameTheory
