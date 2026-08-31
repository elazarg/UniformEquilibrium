/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawFiniteCapClock

/-!
# An all-proper Fin4 cap-switch regression

This file isolates the finite-support regression behind the cap-switch
boundary.  Its exact counterfactual stopping-law menu has first-order cap
curvature although every fixed response has only a smaller bilinear square.
Every displayed law is proper, so the actual finite-splice cemetery product
is zero.

The regression has no positive-minimum property and is not a counterexample
to uniform equilibrium or to the finite-quitting conjecture.
-/

noncomputable section

namespace GameTheory
namespace FinFourCapSwitchAllProper

open Math Math.Probability Math.ProbabilityMassFunction
open Math.Probability.DiscreteHazard

abbrev Player := Fin 4

private theorem finFour_inf_univ (value : Player → WithTop ℕ) :
    Finset.univ.inf value =
      min (value 0) (min (value 1) (min (value 2) (value 3))) := by
  apply le_antisymm
  · apply le_min
    · exact Finset.inf_le (Finset.mem_univ 0)
    · apply le_min
      · exact Finset.inf_le (Finset.mem_univ 1)
      · apply le_min
        · exact Finset.inf_le (Finset.mem_univ 2)
        · exact Finset.inf_le (Finset.mem_univ 3)
  · apply Finset.le_inf
    intro player _
    fin_cases player
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))

private theorem withTop_min_coe (first second : ℕ) :
    min (first : WithTop ℕ) (second : WithTop ℕ) =
      ((min first second : ℕ) : WithTop ℕ) := by
  simp [min_def]

private theorem withTop_min_top_coe (value : ℕ) :
    min (⊤ : WithTop ℕ) (value : WithTop ℕ) = value := by
  exact min_eq_right le_top

def observer : Player := 0
def firstMover : Player := 1
def secondMover : Player := 2
def blocker : Player := 3

/-- The fixed reward table used by the regression. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal player ↦
    if player = observer ∧
        ((observer ∈ terminal.1 ∧ firstMover ∈ terminal.1 ∧
            blocker ∉ terminal.1) ∨
          (secondMover ∈ terminal.1 ∧ observer ∉ terminal.1 ∧
            blocker ∉ terminal.1))
    then 1 else 0

def terminalValue : QuittingTerminalOutcome Player → ℝ
  | none => 0
  | some terminal => reward terminal observer

private theorem terminalValue_quittingFirstStoppingOutcome
    (times : Player → Option ℕ) :
    terminalValue (quittingFirstStoppingOutcome times) =
      if
          (quittingStoppingTimeValue (times observer) =
              quittingEarliestStoppingValue times ∧
            quittingStoppingTimeValue (times firstMover) =
              quittingEarliestStoppingValue times ∧
            quittingStoppingTimeValue (times blocker) ≠
              quittingEarliestStoppingValue times) ∨
          (quittingStoppingTimeValue (times secondMover) =
              quittingEarliestStoppingValue times ∧
            quittingStoppingTimeValue (times observer) ≠
              quittingEarliestStoppingValue times ∧
            quittingStoppingTimeValue (times blocker) ≠
              quittingEarliestStoppingValue times)
        then 1 else 0 := by
  by_cases htop : quittingEarliestStoppingValue times = ⊤
  · have hall (player : Player) :
        quittingStoppingTimeValue (times player) = ⊤ := by
      have hle := Finset.inf_le
        (f := fun who ↦ quittingStoppingTimeValue (times who))
        (Finset.mem_univ player)
      rw [← quittingEarliestStoppingValue, htop] at hle
      exact top_unique hle
    simp [terminalValue, quittingFirstStoppingOutcome, htop, hall]
  · rw [show quittingFirstStoppingOutcome times =
        some ⟨quittingEarliestStoppingCoalition times,
          quittingEarliestStoppingCoalition_nonempty times⟩ by
      simp [quittingFirstStoppingOutcome, htop]]
    simp [terminalValue, reward, quittingEarliestStoppingCoalition]

/-- A two-point complete stopping law, selecting `target` with probability
`weight`. -/
def twoPointLaw (source target : Option ℕ) (weight : ℝ)
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1) : PMF (Option ℕ) :=
  (mixtureCoin weight hweight0 hweight1).bind fun choose ↦
    PMF.pure (if choose then target else source)

private theorem expect_mixtureCoin (weight : ℝ)
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (value : Bool → ℝ) :
    expect (mixtureCoin weight hweight0 hweight1) value =
      (1 - weight) * value false + weight * value true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp [add_comm]

private theorem expect_mixtureCoin_bind_pure {A : Type*} [Finite A]
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (choice : Bool → A) (value : A → ℝ) :
    expect ((mixtureCoin weight hweight0 hweight1).bind
        fun selected ↦ PMF.pure (choice selected)) value =
      (1 - weight) * value (choice false) + weight * value (choice true) := by
  rw [expect_bind, expect_mixtureCoin]
  simp

def mark (n : ℕ) : ℕ := n
def specialTime (n : ℕ) : ℕ := 2 * n
def blockerTime (n : ℕ) : ℕ := 2 * n + n ^ 3
def secondSourceTime (n : ℕ) : ℕ := blockerTime n + 1

def lambda (n : ℕ) : ℝ := 1 / (n : ℝ)
def delta (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 3

private theorem lambda_nonneg (n : ℕ) : 0 ≤ lambda n := by
  unfold lambda
  positivity

private theorem lambda_le_one (n : ℕ) (hn : 2 ≤ n) : lambda n ≤ 1 := by
  unfold lambda
  exact (div_le_one (by exact_mod_cast (show 0 < n by omega))).2
    (by exact_mod_cast (show 1 ≤ n by omega))

private theorem delta_nonneg (n : ℕ) (hn : 2 ≤ n) : 0 ≤ delta n := by
  have _hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold delta
  positivity

private theorem delta_le_one (n : ℕ) (hn : 2 ≤ n) : delta n ≤ 1 := by
  unfold delta
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnReal
  exact (div_le_one (by positivity)).2 hpow

/-- The first mover's proper source law: a small atom at the moving response
date and the remaining mass simultaneous with the blocker. -/
def firstSourceLaw (n : ℕ) (hn : 2 ≤ n) : PMF (Option ℕ) :=
  twoPointLaw (some (blockerTime n)) (some (specialTime n)) (delta n)
    (delta_nonneg n hn) (delta_le_one n hn)

/-- Literal reset law for either mover. -/
def resetTargetLaw (n : ℕ) : PMF (Option ℕ) := PMF.pure (some (mark n))

def firstLaw (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : PMF (Option ℕ) :=
  (mixtureCoin x hx0 hx1).bind fun choose ↦
    if choose then resetTargetLaw n else firstSourceLaw n hn

def secondLaw (n : ℕ) (y : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : PMF (Option ℕ) :=
  twoPointLaw (some (secondSourceTime n)) (some (mark n)) y hy0 hy1

def laws (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : Player → PMF (Option ℕ)
  | 0 => PMF.pure none
  | 1 => firstLaw n hn x hx0 hx1
  | 2 => secondLaw n y hy0 hy1
  | 3 => PMF.pure (some (blockerTime n))

private def baseTimes (n : ℕ) : Player → Option ℕ
  | 0 => none
  | 1 => some (blockerTime n)
  | 2 => some (secondSourceTime n)
  | 3 => some (blockerTime n)

private def baseLaws (n : ℕ) : Player → PMF (Option ℕ) :=
  fun player ↦ PMF.pure (baseTimes n player)

private theorem laws_eq_update_baseLaws
    (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    laws n hn x y hx0 hx1 hy0 hy1 =
      Function.update
        (Function.update (baseLaws n) firstMover
          (firstLaw n hn x hx0 hx1))
        secondMover (secondLaw n y hy0 hy1) := by
  funext player
  fin_cases player <;>
    simp [laws, baseLaws, baseTimes, firstMover, secondMover]

private theorem counterfactualOutcomeLaw_eq_nestedCoins
    (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (time : Option ℕ) :
    quittingCounterfactualOutcomeLaw
        (laws n hn x y hx0 hx1 hy0 hy1)
        (QuittingStoppingIntervention.pureTime observer time) =
      (mixtureCoin y hy0 hy1).bind fun secondReset ↦
        (mixtureCoin x hx0 hx1).bind fun firstReset ↦
          (mixtureCoin (delta n) (delta_nonneg n hn)
            (delta_le_one n hn)).bind fun sourceSpecial ↦
            PMF.pure (quittingFirstStoppingOutcome
              ![time,
                if firstReset then some (mark n)
                else if sourceSpecial then some (specialTime n)
                else some (blockerTime n),
                if secondReset then some (mark n)
                  else some (secondSourceTime n),
                some (blockerTime n)]) := by
  rw [laws_eq_update_baseLaws]
  rw [quittingCounterfactualOutcomeLaw_update_eq_bind]
  · unfold secondLaw twoPointLaw
    rw [PMF.bind_bind]
    congr 1
    funext secondReset
    simp only [PMF.pure_bind]
    rw [quittingCounterfactualOutcomeLaw_update_eq_bind]
    · unfold firstLaw
      rw [PMF.bind_bind]
      congr 1
      funext firstReset
      split
      · simp only [resetTargetLaw, PMF.pure_bind]
        change quittingCounterfactualOutcomeLaw
            (fun player ↦ PMF.pure (baseTimes n player)) _ = _
        rw [quittingCounterfactualOutcomeLaw_pure]
        rw [PMF.bind_const]
        congr 2
        funext player
        fin_cases player <;>
          simp [baseTimes, QuittingStoppingIntervention.applyTimes,
            QuittingStoppingIntervention.insert,
            QuittingStoppingIntervention.pureTime, observer, firstMover,
            secondMover]
      · unfold firstSourceLaw twoPointLaw
        rw [PMF.bind_bind]
        congr 1
        funext sourceSpecial
        simp only [PMF.pure_bind]
        change quittingCounterfactualOutcomeLaw
            (fun player ↦ PMF.pure (baseTimes n player)) _ = _
        rw [quittingCounterfactualOutcomeLaw_pure]
        congr 2
        funext player
        fin_cases player <;>
          simp [baseTimes, QuittingStoppingIntervention.applyTimes,
            QuittingStoppingIntervention.insert,
            QuittingStoppingIntervention.pureTime, observer, firstMover,
            secondMover]
    · simp [QuittingStoppingIntervention.insert,
        QuittingStoppingIntervention.pureTime, observer, firstMover, secondMover]
  · simp [QuittingStoppingIntervention.pureTime, observer, secondMover]

/-- The exact pure-time menu of the finite-support regression. -/
def menuFormula (n : ℕ) (x y : ℝ) (time : Option ℕ) : ℝ :=
  match time with
  | none => y
  | some date =>
      if date < mark n then 0
      else if date = mark n then x
      else if date = specialTime n then
        y + (1 - x) * (1 - y) * delta n
      else y

theorem quittingCounterfactualPureTimeValue_eq_menuFormula
    (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (time : Option ℕ) :
    quittingCounterfactualPureTimeValue
        (laws n hn x y hx0 hx1 hy0 hy1) observer time terminalValue =
      menuFormula n x y time := by
  have hmarkSpecial : mark n < specialTime n := by
    unfold mark specialTime
    omega
  have hspecialBlocker : specialTime n < blockerTime n := by
    unfold specialTime blockerTime
    have hnPow : 0 < n ^ 3 := Nat.pow_pos (by omega)
    omega
  have hblockerSecond : blockerTime n < secondSourceTime n := by
    simp [secondSourceTime]
  have hmarkBlocker : mark n < blockerTime n :=
    hmarkSpecial.trans hspecialBlocker
  have hmarkSecond : mark n < secondSourceTime n :=
    hmarkBlocker.trans hblockerSecond
  have hspecialSecond : specialTime n < secondSourceTime n :=
    hspecialBlocker.trans hblockerSecond
  have hnotSpecialMark : ¬specialTime n ≤ mark n :=
    Nat.not_le_of_lt hmarkSpecial
  have hnotBlockerSpecial : ¬blockerTime n ≤ specialTime n :=
    Nat.not_le_of_lt hspecialBlocker
  have hnotSecondBlocker : ¬secondSourceTime n ≤ blockerTime n :=
    Nat.not_le_of_lt hblockerSecond
  have hnotBlockerMark : ¬blockerTime n ≤ mark n :=
    Nat.not_le_of_lt hmarkBlocker
  have hnotSecondMark : ¬secondSourceTime n ≤ mark n :=
    Nat.not_le_of_lt hmarkSecond
  have hnotSecondSpecial : ¬secondSourceTime n ≤ specialTime n :=
    Nat.not_le_of_lt hspecialSecond
  have hsecondNeMark : secondSourceTime n ≠ mark n := ne_of_gt hmarkSecond
  have hblockerNeMark : blockerTime n ≠ mark n := ne_of_gt hmarkBlocker
  have hsecondNeSpecial : secondSourceTime n ≠ specialTime n :=
    ne_of_gt hspecialSecond
  have hblockerNeSpecial : blockerTime n ≠ specialTime n :=
    ne_of_gt hspecialBlocker
  unfold quittingCounterfactualPureTimeValue quittingCounterfactualExpectedValue
  rw [counterfactualOutcomeLaw_eq_nestedCoins]
  rw [expect_bind]
  rw [expect_mixtureCoin]
  simp_rw [expect_bind]
  simp_rw [expect_mixtureCoin]
  cases time with
  | none =>
      simp (disch := omega) [*, menuFormula,
        terminalValue_quittingFirstStoppingOutcome,
        quittingEarliestStoppingValue, quittingStoppingTimeValue,
        finFour_inf_univ, withTop_min_coe, withTop_min_top_coe,
        observer, firstMover, secondMover, blocker]
  | some date =>
      simp only [menuFormula]
      by_cases hbefore : date < mark n
      · have hdateSpecial : date ≠ specialTime n := by omega
        have hdateMark : date ≠ mark n := by omega
        have hdateBlocker : date ≠ blockerTime n := by omega
        have hspecialDate : specialTime n ≠ date := hdateSpecial.symm
        have hmarkDate : mark n ≠ date := hdateMark.symm
        have hblockerDate : blockerTime n ≠ date := hdateBlocker.symm
        simp (disch := omega) [*,
          terminalValue_quittingFirstStoppingOutcome,
          quittingEarliestStoppingValue, quittingStoppingTimeValue,
          finFour_inf_univ, withTop_min_coe,
          observer, firstMover, secondMover, blocker]
      · by_cases hmark : date = mark n
        · subst date
          have hspecialNeMark : specialTime n ≠ mark n :=
            ne_of_gt hmarkSpecial
          have hblockerNeMark : blockerTime n ≠ mark n :=
            ne_of_gt hmarkBlocker
          (simp (disch := omega) [*, terminalValue_quittingFirstStoppingOutcome,
            quittingEarliestStoppingValue, quittingStoppingTimeValue,
            finFour_inf_univ, withTop_min_coe, observer, firstMover,
            secondMover, blocker]; ring)
        · by_cases hspecial : date = specialTime n
          · subst date
            have hmarkNeSpecial : mark n ≠ specialTime n :=
              ne_of_lt hmarkSpecial
            have hblockerNeSpecial : blockerTime n ≠ specialTime n :=
              ne_of_gt hspecialBlocker
            (simp (disch := omega) [*,
              terminalValue_quittingFirstStoppingOutcome,
              quittingEarliestStoppingValue, quittingStoppingTimeValue,
              finFour_inf_univ, withTop_min_coe,
              observer, firstMover, secondMover, blocker]; ring)
          · have hdateMark' : date ≠ mark n := hmark
            have hmarkDate : mark n ≠ date := hdateMark'.symm
            have hdateSpecial : date ≠ specialTime n := hspecial
            have hspecialDate : specialTime n ≠ date := hdateSpecial.symm
            have hblockerImpossible :
                ¬ ((date ≤ blockerTime n ∧ blockerTime n ≤ date ∧
                      date < blockerTime n) ∨
                    (secondSourceTime n = min date (blockerTime n) ∧
                      blockerTime n < date ∧ date < blockerTime n)) := by
              omega
            have hspecialImpossible :
                ¬ ((date ≤ specialTime n ∧ specialTime n ≤ date ∧
                      blockerTime n ≠ min date (specialTime n)) ∨
                    (secondSourceTime n = min date (specialTime n) ∧
                      specialTime n < date ∧
                      blockerTime n ≠ min date (specialTime n))) := by
              rw [not_or]
              constructor
              · rintro ⟨hle, hge, -⟩
                exact hspecial (Nat.le_antisymm hle hge)
              · rintro ⟨heq, hlt, -⟩
                rw [min_eq_right (Nat.le_of_lt hlt)] at heq
                exact hsecondNeSpecial heq
            simp (disch := omega) [*,
              terminalValue_quittingFirstStoppingOutcome,
              quittingEarliestStoppingValue, quittingStoppingTimeValue,
              finFour_inf_univ, withTop_min_coe,
              observer, firstMover, secondMover, blocker]

@[simp] theorem firstSourceLaw_none_toReal (n : ℕ) (hn : 2 ≤ n) :
    (firstSourceLaw n hn none).toReal = 0 := by
  unfold firstSourceLaw twoPointLaw
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum,
    Fintype.sum_bool]
  simp

@[simp] theorem firstLaw_none_toReal (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (firstLaw n hn x hx0 hx1 none).toReal = 0 := by
  unfold firstLaw
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum,
    Fintype.sum_bool]
  simp [resetTargetLaw]

@[simp] theorem secondLaw_none_toReal (n : ℕ) (y : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (secondLaw n y hy0 hy1 none).toReal = 0 := by
  unfold secondLaw twoPointLaw
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum,
    Fintype.sum_bool]
  simp

/-- Every opponent marginal in every source, face, or full endpoint is proper. -/
theorem laws_none_toReal_of_ne_observer (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (player : Player)
    (hplayer : player ≠ observer) :
    (laws n hn x y hx0 hx1 hy0 hy1 player none).toReal = 0 := by
  fin_cases player <;> simp_all [laws, observer]

/-- The scalar cap formula isolated from the exact menu calculation. -/
def capFormula (n : ℕ) (x y : ℝ) : ℝ :=
  max x (y + (1 - x) * (1 - y) * delta n)

private theorem menuFormula_le_capFormula
    (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy1 : y ≤ 1) (time : Option ℕ) :
    menuFormula n x y time ≤ capFormula n x y := by
  have hproduct : 0 ≤ (1 - x) * (1 - y) * delta n := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hy1))
      (delta_nonneg n hn)
  have hx : x ≤ capFormula n x y := le_max_left _ _
  have hspecial : y + (1 - x) * (1 - y) * delta n ≤
      capFormula n x y := le_max_right _ _
  have hy : y ≤ capFormula n x y :=
    (le_add_of_nonneg_right hproduct).trans hspecial
  have hzero : 0 ≤ capFormula n x y := hx0.trans hx
  cases time with
  | none => exact hy
  | some date =>
      simp only [menuFormula]
      split_ifs <;> assumption

/-- The literal pure-time counterfactual cap is exactly the displayed
two-response menu formula. -/
theorem quittingCounterfactualPureTimeCap_eq_capFormula
    (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingCounterfactualPureTimeCap
        (laws n hn x y hx0 hx1 hy0 hy1) observer terminalValue =
      capFormula n x y := by
  let values : Set ℝ := Set.range fun time : Option ℕ ↦
    quittingCounterfactualPureTimeValue
      (laws n hn x y hx0 hx1 hy0 hy1) observer time terminalValue
  have hbounded : BddAbove values := by
    refine ⟨capFormula n x y, ?_⟩
    rintro value ⟨time, rfl⟩
    change quittingCounterfactualPureTimeValue
      (laws n hn x y hx0 hx1 hy0 hy1) observer time terminalValue ≤ _
    rw [quittingCounterfactualPureTimeValue_eq_menuFormula]
    exact menuFormula_le_capFormula n hn x y hx0 hx1 hy1 time
  unfold quittingCounterfactualPureTimeCap
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨time, rfl⟩
    change quittingCounterfactualPureTimeValue
      (laws n hn x y hx0 hx1 hy0 hy1) observer time terminalValue ≤ _
    rw [quittingCounterfactualPureTimeValue_eq_menuFormula]
    exact menuFormula_le_capFormula n hn x y hx0 hx1 hy1 time
  · apply max_le
    · apply le_csSup hbounded
      refine ⟨some (mark n), ?_⟩
      change quittingCounterfactualPureTimeValue
        (laws n hn x y hx0 hx1 hy0 hy1) observer (some (mark n)) terminalValue = _
      rw [quittingCounterfactualPureTimeValue_eq_menuFormula]
      simp [menuFormula]
    · apply le_csSup hbounded
      refine ⟨some (specialTime n), ?_⟩
      change quittingCounterfactualPureTimeValue
        (laws n hn x y hx0 hx1 hy0 hy1) observer
          (some (specialTime n)) terminalValue = _
      rw [quittingCounterfactualPureTimeValue_eq_menuFormula]
      simp [menuFormula, show ¬specialTime n < mark n by
        unfold specialTime mark
        omega, show specialTime n ≠ mark n by
        unfold specialTime mark
        omega]

/-- The four cap corners have the packet's exact signed square whenever
`0 < delta < lambda < 1`. -/
theorem capFormula_square
    (n : ℕ) (hn : 2 ≤ n) :
    capFormula n (lambda n) (lambda n) -
          capFormula n (lambda n) 0 -
        capFormula n 0 (lambda n) + capFormula n 0 0 =
      -lambda n + (1 - lambda n + (lambda n) ^ 2) * delta n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlambda0 : 0 < lambda n := by
    unfold lambda
    positivity
  have hlambda1 : lambda n < 1 := by
    unfold lambda
    exact (div_lt_one hn0).2 (by exact_mod_cast (show 1 < n by omega))
  have hdelta0 : 0 < delta n := by
    unfold delta
    positivity
  have hdeltaLambda : delta n < lambda n := by
    unfold delta lambda
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 3) hn0]
    have hnSq : (1 : ℝ) < (n : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) < n by exact_mod_cast (show 1 < n by omega)]
    nlinarith
  have h00 : capFormula n 0 0 = delta n := by
    simp [capFormula, hdelta0.le]
  have h10 : capFormula n (lambda n) 0 = lambda n := by
    unfold capFormula
    rw [max_eq_left]
    nlinarith [mul_le_mul_of_nonneg_right
      (sub_le_self 1 hlambda0.le) hdelta0.le]
  have h01 : capFormula n 0 (lambda n) =
      lambda n + (1 - lambda n) * delta n := by
    unfold capFormula
    rw [max_eq_right]
    · ring
    · have hone : 0 ≤ 1 - lambda n := sub_nonneg.2 hlambda1.le
      positivity
  have h11 : capFormula n (lambda n) (lambda n) =
      lambda n + (1 - lambda n) ^ 2 * delta n := by
    unfold capFormula
    rw [max_eq_right]
    · ring_nf
    · have hterm : 0 ≤ (1 - lambda n) ^ 2 * delta n := by positivity
      nlinarith
  rw [h00, h10, h01, h11]
  ring

/-- The actual counterfactual pure-time caps have the same signed square as
the scalar menu formula. -/
theorem quittingCounterfactualPureTimeCap_square
    (n : ℕ) (hn : 2 ≤ n) :
    quittingCounterfactualPureTimeCap
          (laws n hn (lambda n) (lambda n)
            (lambda_nonneg n) (lambda_le_one n hn)
            (lambda_nonneg n) (lambda_le_one n hn)) observer terminalValue -
        quittingCounterfactualPureTimeCap
          (laws n hn (lambda n) 0
            (lambda_nonneg n) (lambda_le_one n hn) (by positivity) (by norm_num))
          observer terminalValue -
      quittingCounterfactualPureTimeCap
          (laws n hn 0 (lambda n)
            (by positivity) (by norm_num)
            (lambda_nonneg n) (lambda_le_one n hn)) observer terminalValue +
        quittingCounterfactualPureTimeCap
          (laws n hn 0 0 (by positivity) (by norm_num) (by positivity) (by norm_num))
          observer terminalValue =
      -lambda n + (1 - lambda n + (lambda n) ^ 2) * delta n := by
  rw [quittingCounterfactualPureTimeCap_eq_capFormula,
    quittingCounterfactualPureTimeCap_eq_capFormula,
    quittingCounterfactualPureTimeCap_eq_capFormula,
    quittingCounterfactualPureTimeCap_eq_capFormula]
  exact capFormula_square n hn

/-- Every fixed-response square in the active source window has the smaller
exact scale `delta * lambda^2`. -/
theorem fixedResponse_square_eq (n : ℕ) :
    (lambda n + (1 - lambda n) ^ 2 * delta n) -
          ((1 - lambda n) * delta n) -
        (lambda n + (1 - lambda n) * delta n) + delta n =
      delta n * (lambda n) ^ 2 := by
  ring

/-- The exact terminal finite-splice product vanishes against arbitrary root
sequences for every displayed opponent law. -/
theorem finiteSplice_terminalProduct_eq_zero
    (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (roots : ℕ → Player → PMF Bool) (mover responseObserver : Player)
    (hmover : mover ≠ FinFourCapSwitchAllProper.observer) :
    (laws n hn x y hx0 hx1 hy0 hy1 mover none).toReal *
      quittingPairDeletedSurvivalLimit
        roots mover responseObserver 0 = 0 := by
  rw [laws_none_toReal_of_ne_observer _ _ _ _ _ _ _ _ _ hmover]
  simp

private def reconstructedHazard
    (law : PMF (Option ℕ)) : ℕ → PMF Bool :=
  (StoppingLaw.toScalarHazard law).toBoolean

private theorem quittingHazardNeverMass_reconstructedHazard
    (law : PMF (Option ℕ)) :
    quittingHazardNeverMass (reconstructedHazard law) = (law none).toReal := by
  simp [reconstructedHazard, quittingHazardNeverMass,
    StoppingLaw.toScalarHazard_neverMass]

/-- Reconstructing any displayed opponent law as a Boolean hazard gives a
finite-splice error tending to zero against every root sequence. -/
theorem tendsto_quittingFiniteSpliceError_reconstructedHazard_zero
    (n : ℕ) (hn : 2 ≤ n) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (roots : ℕ → Player → PMF Bool) (mover : Player)
    (hmover : mover ≠ observer) :
    Filter.Tendsto (fun cutoff ↦
        quittingFiniteSpliceError roots mover
          (reconstructedHazard (laws n hn x y hx0 hx1 hy0 hy1 mover)) cutoff)
      Filter.atTop (nhds 0) := by
  apply tendsto_quittingFiniteSpliceError_zero_of_neverMass_zero
  rw [quittingHazardNeverMass_reconstructedHazard]
  exact laws_none_toReal_of_ne_observer n hn x y hx0 hx1 hy0 hy1 mover hmover

end FinFourCapSwitchAllProper
end GameTheory
