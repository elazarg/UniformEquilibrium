import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterAnchorQuantile
import UniformEquilibrium.Quitting.Paths.FirstStoppingOutcomeCoalition

/-! # The actual anchor split and its finite active row

Only Boolean observations at one date are finite. The underlying laws retain
all their unbounded tails and Never atoms.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.DiscreteHazard.StoppingLaw Math.PMFProduct

def activePayoff (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![q 0 + 2 * (1 - q 0) * q 2, q 1 * (2 * q 0 - 1), q 2 * (2 * q 1 - 1)]

def activeQuitPayoff (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![1, 2 * q 0 - 1, 2 * q 1 - 1]

def activeContinuePayoff (q : Fin 3 → ℝ) : Fin 3 → ℝ := ![2 * q 2, 0, 0]

def activeEndpointPayoff (q : Fin 3 → ℝ) (who : Fin 3) (quit : Bool) : ℝ :=
  if quit then activeQuitPayoff q who else activeContinuePayoff q who

theorem activePayoff_update_endpoint (q : Fin 3 → ℝ) (who : Fin 3) (quit : Bool) :
    activePayoff (Function.update q who (if quit then 1 else 0)) who =
      activeEndpointPayoff q who quit := by
  fin_cases who <;> cases quit <;>
    simp [activePayoff, activeEndpointPayoff, activeQuitPayoff, activeContinuePayoff]

def dateCoin (law : PMF (Option ℕ)) (cutoff : ℕ) : PMF Bool :=
  law.map (fun choice => decide (choice = some cutoff))

@[simp] theorem dateCoin_true (law : PMF (Option ℕ)) (cutoff : ℕ) :
    dateCoin law cutoff true = law (some cutoff) := by
  classical
  rw [dateCoin, PMF.map_apply, tsum_eq_single (some cutoff)]
  · simp
  · intro other hother
    simp [hother]

theorem dateCoin_false_toReal (law : PMF (Option ℕ)) (cutoff : ℕ) :
    (dateCoin law cutoff false).toReal = 1 - finiteMass law cutoff := by
  have hsum := pmf_toReal_sum_one (dateCoin law cutoff)
  simp only [Fintype.sum_bool, dateCoin_true] at hsum
  unfold finiteMass
  linarith

/-- The date-K row contributes only when the anchor stops at date K. -/
def activeRowPayoff (actions : Fin 4 → Bool) (who : Fin 3) : ℝ :=
  if actions 3 then
    ![if actions 0 then 1 else 2 * if actions 2 then 1 else 0,
      (2 * (if actions 0 then 1 else 0) - 1) * if actions 1 then 1 else 0,
      (2 * (if actions 1 then 1 else 0) - 1) * if actions 2 then 1 else 0] who
  else 0

theorem activeRowPayoff_abs_le_two (actions : Fin 4 → Bool) (who : Fin 3) :
    |activeRowPayoff actions who| ≤ 2 := by
  fin_cases who <;> cases hzero : actions 0 <;> cases hone : actions 1 <;>
    cases htwo : actions 2 <;> cases hthree : actions 3 <;>
    norm_num [activeRowPayoff, hzero, hone, htwo, hthree]

/-- Exact finite-observation computation under arbitrary independent clocks. -/
theorem expected_activeRowPayoff (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (active : Fin 3) :
    expect (pmfPi laws) (fun times =>
        activeRowPayoff (fun who => decide (times who = some cutoff)) active) =
      finiteMass (laws 3) cutoff *
        activePayoff (fun who => finiteMass (laws who.castSucc) cutoff) active := by
  classical
  have hpush := pmfPi_push_coordwise laws
    (fun _ choice => decide (choice = some cutoff))
  have hexpect := congrArg (fun distribution =>
    expect distribution (fun actions => activeRowPayoff actions active)) hpush
  simp only [pushforward, expect_map] at hexpect
  change expect (pmfPi laws) (fun times =>
      activeRowPayoff (fun who => decide (times who = some cutoff)) active) =
    expect (pmfPi (fun who => dateCoin (laws who) cutoff))
      (fun actions => activeRowPayoff actions active) at hexpect
  rw [hexpect, expect_pmfPi_fin4]
  fin_cases active <;>
    simp [expect_eq_sum, activeRowPayoff, activePayoff,
      dateCoin_false_toReal, finiteMass] <;> ring

private theorem stoppingValue_lt_of_lt_survive (choice : Option ℕ) (first cutoff : ℕ)
    (hearlier : first < cutoff) (hsurvive : survivesUntil cutoff choice) :
    quittingStoppingTimeValue (some first) < quittingStoppingTimeValue choice := by
  cases choice with
  | none => simp [quittingStoppingTimeValue]
  | some time =>
      have htime : cutoff ≤ time := hsurvive
      simpa [quittingStoppingTimeValue] using hearlier.trans_le htime

private theorem stoppingValue_gt_of_survive_ne (choice : Option ℕ) (cutoff : ℕ)
    (hsurvive : survivesUntil cutoff choice) (hne : choice ≠ some cutoff) :
    quittingStoppingTimeValue (some cutoff) < quittingStoppingTimeValue choice := by
  cases choice with
  | none => simp [quittingStoppingTimeValue]
  | some time =>
      have htime : cutoff ≤ time := hsurvive
      have htimeNe : time ≠ cutoff := by simpa using hne
      have hstrict : cutoff < time := by omega
      simpa [quittingStoppingTimeValue] using hstrict

/-- With all active clocks surviving to K, an earlier anchor gives only {3};
an anchor at K gives exactly the displayed row, including all ties. -/
theorem clockPayoff_eq_activeRow_of_anchor_not_after
    (times : Fin 4 → Option ℕ) (cutoff : ℕ) (active : Fin 3)
    (hsurvive : ∀ who : Fin 3, survivesUntil cutoff (times who.castSucc))
    (hanchor : ¬survivesUntil (cutoff + 1) (times 3)) :
    clockPayoff times active.castSucc =
      activeRowPayoff (fun who => decide (times who = some cutoff)) active := by
  classical
  cases hanchorTime : times 3 with
  | none => simp [hanchorTime, survivesUntil] at hanchor
  | some anchorTime =>
      have hdate : anchorTime ≤ cutoff := by
        simpa [hanchorTime, survivesUntil, Nat.lt_succ_iff] using hanchor
      by_cases heq : anchorTime = cutoff
      · subst anchorTime
        let coalition := Finset.univ.filter (fun who => times who = some cutoff)
        have hnonempty : coalition.Nonempty := ⟨3, by simp [coalition, hanchorTime]⟩
        have hinside : ∀ who ∈ coalition, times who = some cutoff := by
          intro who hwho
          simpa [coalition] using hwho
        have houtside : ∀ who ∉ coalition,
            quittingStoppingTimeValue (some cutoff) < quittingStoppingTimeValue (times who) := by
          intro who hwho
          have hne : times who ≠ some cutoff := by simpa [coalition] using hwho
          fin_cases who
          · exact stoppingValue_gt_of_survive_ne _ _ (hsurvive 0) hne
          · exact stoppingValue_gt_of_survive_ne _ _ (hsurvive 1) hne
          · exact stoppingValue_gt_of_survive_ne _ _ (hsurvive 2) hne
          · exact (hne hanchorTime).elim
        have houtcome := quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
          times coalition hnonempty cutoff hinside houtside
        fin_cases active <;>
          simp [clockPayoff, houtcome, quittingTerminalOutcomeReward, reward,
            coalition, activeRowPayoff, hanchorTime]
      · have hearlier : anchorTime < cutoff := lt_of_le_of_ne hdate heq
        have hinside : ∀ who ∈ ({3} : Finset (Fin 4)), times who = some anchorTime := by
          intro who hwho
          have heqWho : who = 3 := by simpa using hwho
          simpa [heqWho] using hanchorTime
        have houtside : ∀ who ∉ ({3} : Finset (Fin 4)),
            quittingStoppingTimeValue (some anchorTime) <
              quittingStoppingTimeValue (times who) := by
          intro who hwho
          fin_cases who
          · exact stoppingValue_lt_of_lt_survive _ _ _ hearlier (hsurvive 0)
          · exact stoppingValue_lt_of_lt_survive _ _ _ hearlier (hsurvive 1)
          · exact stoppingValue_lt_of_lt_survive _ _ _ hearlier (hsurvive 2)
          · simp at hwho
        have houtcome := quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
          times {3} (Finset.singleton_nonempty 3) anchorTime hinside houtside
        fin_cases active <;>
          simp [clockPayoff, houtcome, quittingTerminalOutcomeReward, reward,
            activeRowPayoff, hanchorTime, heq]

/-- Hidden anchor tails contribute at most twice their actual probability.
Every active survival premise concerns support of the supplied complete law. -/
theorem abs_expectedPayoff_sub_anchor_row_le
    (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ) (active : Fin 3)
    (hsurvive : ∀ who : Fin 3, ∀ choice, laws who.castSucc choice ≠ 0 →
      survivesUntil cutoff choice) :
    |quittingStoppingLawExpectedPayoff reward laws active.castSucc -
        finiteMass (laws 3) cutoff *
          activePayoff (fun who => finiteMass (laws who.castSucc) cutoff) active| ≤
      2 * survival (laws 3) (cutoff + 1) := by
  classical
  rw [expectedPayoff_eq_expect_clocks, ← expected_activeRowPayoff]
  let event : Set (Fin 4 → Option ℕ) := {times | survivesUntil (cutoff + 1) (times 3)}
  have hbound := abs_expect_sub_le_mul_pmfMass_of_support (pmfPi laws)
    (fun times => clockPayoff times active.castSucc)
    (fun times => activeRowPayoff (fun who => decide (times who = some cutoff)) active)
    event (bound := 2) (observableBound := 2) (by norm_num)
    (fun times => clockPayoff_abs_le_two times active.castSucc)
    (fun times => activeRowPayoff_abs_le_two _ active) (by
      intro times htimes
      by_cases hevent : times ∈ event
      · have hne : times 3 ≠ some cutoff := by
          intro heq
          have htail := hevent
          change survivesUntil (cutoff + 1) (times 3) at htail
          rw [heq] at htail
          exact Nat.not_succ_le_self cutoff htail
        rw [Set.indicator_of_mem hevent]
        simp only [mul_one]
        simpa [activeRowPayoff, hne] using clockPayoff_abs_le_two times active.castSucc
      · rw [Set.indicator_of_notMem hevent, mul_zero]
        have hsupport : ∀ who : Fin 3, survivesUntil cutoff (times who.castSucc) := by
          intro who
          exact hsurvive who _ (pmfPi_coordinate_ne_zero laws times who.castSucc htimes)
        have hnotAfter : ¬survivesUntil (cutoff + 1) (times 3) := hevent
        rw [clockPayoff_eq_activeRow_of_anchor_not_after
          times cutoff active hsupport hnotAfter, sub_self, abs_zero])
  change _ ≤ 2 * (pmfMass (pmfPi laws)
    (fun times => survivesUntil (cutoff + 1) (times 3))).toReal at hbound
  rw [pmfMass_pmfPi_coord_arbitrary laws 3 (survivesUntil (cutoff + 1)),
    pmfMass_survivesUntil_toReal] at hbound
  exact hbound

end GameTheory.AdaptiveChildCenter
