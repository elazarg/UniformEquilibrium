/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMacroscopicAtomNashProvenance
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseProductRescaling

/-!
# Terminal-semantic collision rank reduction

This Research module charges every coalition of rank at least two through the
whole collision event, avoiding a factor for the number of coalitions. At a
positive minimum semantic debt, exact Nash provenance then forces a product
root to have at most one positive Quit marginal.

The conclusions reduce the active rank of one root. They do not reduce the
cardinality of the ambient player type and do not establish an unconditional
pair-only reduction.
-/

noncomputable section

namespace Research.Quitting.TerminalSemanticCollisionRankReduction

open scoped BigOperators
open GameTheory Finset Math.PMFProduct

/-! ## Aggregate collision energy -/

section CollisionEnergy

variable {Player : Type} [Fintype Player] [DecidableEq Player]

/-- Collision is contained in every player's opponent-absorption event.
This aggregate inclusion is stronger than charging each coalition and then
summing: no number-of-coalitions factor is introduced. -/
theorem collisionMass_le_opponentAbsorption
    (root : Player → PMF Bool) (owner : Player) :
    quittingRootCollisionMass root ≤
      quittingRootOpponentAbsorptionMass root owner := by
  let rate : Player → ℝ := quittingRootQuitRates root
  have hrate0 : ∀ who, 0 ≤ rate who := fun _ ↦ ENNReal.toReal_nonneg
  have hrate1 : ∀ who, rate who ≤ 1 := fun who ↦
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  let others : Finset Player := Finset.univ.erase owner
  have hownerNot : owner ∉ others := by simp [others]
  have huniv : (Finset.univ : Finset Player) = insert owner others := by
    exact (Finset.insert_erase (Finset.mem_univ owner)).symm
  have hcollisionRest0 : 0 ≤ collisionMassFormulaOn rate others :=
    collisionMassFormulaOn_nonneg rate others
      (fun who _ ↦ hrate0 who) (fun who _ ↦ hrate1 who)
  have habsorptionRest0 :
      0 ≤ 1 - ∏ who ∈ others, (1 - rate who) := by
    exact sub_nonneg.mpr (Finset.prod_le_one
      (fun who _ ↦ sub_nonneg.mpr (hrate1 who))
      (fun who _ ↦ by linarith [hrate0 who]))
  have hcollisionRestLe : collisionMassFormulaOn rate others ≤
      1 - ∏ who ∈ others, (1 - rate who) := by
    unfold collisionMassFormulaOn
    have hsingle0 : 0 ≤ ∑ who ∈ others,
        rate who * ∏ other ∈ others.erase who, (1 - rate other) := by
      exact Finset.sum_nonneg fun who hwho ↦ mul_nonneg (hrate0 who)
        (Finset.prod_nonneg fun other hother ↦
          sub_nonneg.mpr (hrate1 other))
    linarith
  have hformula : collisionMass rate =
      (1 - rate owner) * collisionMassFormulaOn rate others +
        rate owner * (1 - ∏ who ∈ others, (1 - rate who)) := by
    rw [collisionMass_eq_one_sub_continueMass_sub_singletonMass]
    change collisionMassFormulaOn rate Finset.univ = _
    rw [huniv, collisionMassFormulaOn_insert rate hownerNot]
  have hbound : collisionMass rate ≤
      1 - ∏ who ∈ others, (1 - rate who) := by
    rw [hformula]
    calc
      (1 - rate owner) * collisionMassFormulaOn rate others +
          rate owner * (1 - ∏ who ∈ others, (1 - rate who)) ≤
        (1 - rate owner) *
            (1 - ∏ who ∈ others, (1 - rate who)) +
          rate owner * (1 - ∏ who ∈ others, (1 - rate who)) := by
            gcongr
            exact sub_nonneg.mpr (hrate1 owner)
      _ = 1 - ∏ who ∈ others, (1 - rate who) := by ring
  rw [_root_.GameTheory.quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  simpa only [quittingRootCollisionMass, rate, others,
    quittingRootQuitRates] using hbound

/-- Abstract rank-blind collision charge. -/
theorem collisionMass_mul_debtSum_le_opponentCharge
    (root : Player → PMF Bool) (debt : Player → ℝ)
    (hdebt : ∀ who, 0 ≤ debt who) :
    quittingRootCollisionMass root * (∑ who, debt who) ≤
      ∑ who, quittingRootOpponentAbsorptionMass root who * debt who := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun who _ ↦
    mul_le_mul_of_nonneg_right
      (collisionMass_le_opponentAbsorption root who) (hdebt who)

/-- Two positive Quit marginals force strictly positive collision mass. -/
theorem collisionMass_pos_of_two_positive
    (root : Player → PMF Bool) {first second : Player}
    (hne : first ≠ second)
    (hfirst : 0 < (root first true).toReal)
    (hsecond : 0 < (root second true).toReal) :
    0 < quittingRootCollisionMass root := by
  classical
  let rate : Player → ℝ := quittingRootQuitRates root
  let support : Finset Player := Finset.univ.filter fun who ↦ 0 < rate who
  have hrate0 : ∀ who, 0 ≤ rate who := fun _ ↦ ENNReal.toReal_nonneg
  have hrate1 : ∀ who, rate who ≤ 1 := fun who ↦
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  have hfirstMem : first ∈ support := by
    simp [support, rate, quittingRootQuitRates, hfirst]
  have hsecondMem : second ∈ support := by
    simp [support, rate, quittingRootQuitRates, hsecond]
  have hcard : 2 ≤ support.card := by
    have hsubset : ({first, second} : Finset Player) ⊆ support := by
      intro who hwho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
      rcases hwho with rfl | rfl
      · exact hfirstMem
      · exact hsecondMem
    have hpairCard : ({first, second} : Finset Player).card = 2 := by
      simp [hne]
    rw [← hpairCard]
    exact Finset.card_le_card hsubset
  have hinside : 0 < ∏ who ∈ support, rate who := by
    exact Finset.prod_pos fun who hwho ↦
      (Finset.mem_filter.mp hwho).2
  have houtside : 0 < ∏ who ∈ supportᶜ, (1 - rate who) := by
    apply Finset.prod_pos
    intro who hwho
    have hnot : who ∉ support := by simpa using hwho
    have hzero : rate who = 0 := by
      have hnpos : ¬ 0 < rate who := by
        simpa [support] using hnot
      exact le_antisymm (le_of_not_gt hnpos) (hrate0 who)
    simp [hzero]
  have hcoalition : 0 < coalitionMass rate support := by
    unfold coalitionMass
    exact mul_pos hinside houtside
  have hmem : support ∈ Finset.univ.filter
      (fun coalition : Finset Player ↦ 2 ≤ coalition.card) := by
    simp [hcard]
  have hterms : ∀ coalition ∈
      Finset.univ.filter (fun coalition : Finset Player ↦ 2 ≤ coalition.card),
      0 ≤ coalitionMass rate coalition := by
    intro coalition _
    unfold coalitionMass
    exact mul_nonneg
      (Finset.prod_nonneg fun who _ ↦ hrate0 who)
      (Finset.prod_nonneg fun who _ ↦ sub_nonneg.mpr (hrate1 who))
  have hle : coalitionMass rate support ≤ collisionMass rate := by
    exact Finset.single_le_sum hterms hmem
  exact hcoalition.trans_le (by
    simpa [quittingRootCollisionMass, rate] using hle)

/-- Collision-freeness is a genuine rank-one statement about one product
root: any two positive Quit marginals name the same player.  It is not a
reduction in the cardinality of the ambient player type. -/
theorem atMostOnePositive_of_collisionMass_eq_zero
    (root : Player → PMF Bool)
    (hzero : quittingRootCollisionMass root = 0)
    {first second : Player}
    (hfirst : 0 < (root first true).toReal)
    (hsecond : 0 < (root second true).toReal) :
    first = second := by
  by_contra hne
  have hpos := collisionMass_pos_of_two_positive root hne hfirst hsecond
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **Aggregate minimum-debt inequality.** All coalition ranks at least two
are charged once by one collision scalar. -/
theorem collisionMass_mul_minimumDebt_le_tailExcess_add_totalDefect
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (minimum tail : QuittingTerminalSemanticPair Player)
    (root : Player → PMF Bool)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward) :
    quittingRootCollisionMass root *
        quittingTerminalSemanticDebtSum minimum ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        quittingRootTotalNashDefect reward tail.1 root := by
  have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward htail
  have hcollision0 := quittingRootCollisionMass_nonneg root
  have hminimumLeTail := hminimum tail htail
  have htoTail :
      quittingRootCollisionMass root *
          quittingTerminalSemanticDebtSum minimum ≤
        quittingRootCollisionMass root *
          quittingTerminalSemanticDebtSum tail :=
    mul_le_mul_of_nonneg_left hminimumLeTail hcollision0
  have htoCharge := collisionMass_mul_debtSum_le_opponentCharge root
    (fun who ↦ quittingTerminalSemanticDebt tail who) htailDebt
  have hcharge :=
    minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect
      reward minimum tail root hminimumCarrier hminimum htail
  exact htoTail.trans (htoCharge.trans hcharge)

/-- `ε`-Nash specialization of the aggregate collision charge. -/
theorem collisionMass_mul_minimumDebt_le_tailExcess_add_card_mul_nashError
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (minimum tail : QuittingTerminalSemanticPair Player)
    (root : Player → PMF Bool) (ε : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward tail.1 ε root) :
    quittingRootCollisionMass root *
        quittingTerminalSemanticDebtSum minimum ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        Fintype.card Player * ε := by
  have haggregate :=
    collisionMass_mul_minimumDebt_le_tailExcess_add_totalDefect
      minimum tail root hminimumCarrier hminimum htail
  have hdefect :=
    quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
      reward tail.1 root ε hnash
  linarith

/-- Exact Nash at a positive minimum semantic point has at most one active
quitter. -/
theorem minimumExactNash_atMostOnePositiveQuitter
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (minimum : QuittingTerminalSemanticPair Player)
    (root : Player → PMF Bool)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hnash : IsεQuittingRootNash reward minimum.1 0 root)
    {first second : Player}
    (hfirst : 0 < (root first true).toReal)
    (hsecond : 0 < (root second true).toReal) :
    first = second := by
  have hcollisionZero :=
    (minimumTerminalSemantic_exactNash_criticalFace
      (reward := reward) minimum root hminimumCarrier hminimum
        hpositive hnash).1
  exact atMostOnePositive_of_collisionMass_eq_zero root hcollisionZero
    hfirst hsecond

end CollisionEnergy

end Research.Quitting.TerminalSemanticCollisionRankReduction
