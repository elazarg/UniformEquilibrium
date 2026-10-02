import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterAnchorRow

/-! # Actual conditional payoff and endpoint estimates at a first quantile

The prescribed comparison conditions three active marginals. A common actual
endpoint replacement conditions only its two active opponents, yielding the
distinct constants 14 and 10. No finite-support premise or cap attainment is used.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.DiscreteHazard.StoppingLaw Math.PMFProduct

theorem active_ne_anchor (active : Fin 3) : active.castSucc ≠ (3 : Fin 4) := by
  intro heq
  have hvalue := congrArg Fin.val heq
  change active.val = 3 at hvalue
  omega

/-- Actual active laws conditioned to survive to the absolute cutoff; the
anchor's law is retained literally. -/
def conditionActive (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff) :
    Fin 4 → PMF (Option ℕ) :=
  ![conditionAt (laws 0) cutoff (hpositive 0),
    conditionAt (laws 1) cutoff (hpositive 1),
    conditionAt (laws 2) cutoff (hpositive 2), laws 3]

@[simp] theorem conditionActive_anchor (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff) :
    conditionActive laws cutoff hpositive 3 = laws 3 := by
  rfl

theorem conditionActive_active (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    (active : Fin 3) :
    conditionActive laws cutoff hpositive active.castSucc =
      conditionAt (laws active.castSucc) cutoff (hpositive active) := by
  fin_cases active <;> rfl

/-- These are the actual conditional probabilities, with unmodified dates. -/
def conditionalProbabilities (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ) : Fin 3 → ℝ :=
  fun active => finiteMass (laws active.castSucc) cutoff / survival (laws active.castSucc) cutoff

theorem conditionActive_finiteMass (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    (active : Fin 3) :
    finiteMass (conditionActive laws cutoff hpositive active.castSucc) cutoff =
      conditionalProbabilities laws cutoff active := by
  rw [conditionActive_active, conditionAt_finiteMass _ _ _ _ le_rfl]
  rfl

theorem conditionalProbabilities_bounds (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    (active : Fin 3) :
    0 ≤ conditionalProbabilities laws cutoff active ∧
      conditionalProbabilities laws cutoff active ≤ 1 := by
  rw [← conditionActive_finiteMass laws cutoff hpositive active]
  refine ⟨finiteMass_nonneg _ _, ?_⟩
  unfold finiteMass
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)

theorem conditionActive_support (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff) :
    ∀ active : Fin 3, ∀ choice,
      conditionActive laws cutoff hpositive active.castSucc choice ≠ 0 →
        survivesUntil cutoff choice := by
  intro active choice hchoice
  rw [conditionActive_active] at hchoice
  exact conditionAt_support _ _ _
    (((conditionAt (laws active.castSucc) cutoff (hpositive active)).mem_support_iff choice).2
      hchoice)

theorem conditioning_distance_sum_le (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    {accuracy : ℝ} (hbefore : ∀ active : Fin 3,
      1 - survival (laws active.castSucc) cutoff ≤ accuracy) :
    ∑ who, pmfOperationalDistance (laws who)
      (conditionActive laws cutoff hpositive who) ≤ 6 * accuracy := by
  have hcoordinate : ∀ active : Fin 3,
      pmfOperationalDistance (laws active.castSucc)
        (conditionActive laws cutoff hpositive active.castSucc) ≤ 2 * accuracy := by
    intro active
    rw [conditionActive_active]
    change 2 * pmfGeneralTV _ _ ≤ 2 * accuracy
    rw [pmfGeneralTV_conditionAt]
    linarith [hbefore active]
  have hzero := hcoordinate 0
  have hone := hcoordinate 1
  have htwo := hcoordinate 2
  change pmfOperationalDistance (laws 0) (conditionActive laws cutoff hpositive 0) ≤
    2 * accuracy at hzero
  change pmfOperationalDistance (laws 1) (conditionActive laws cutoff hpositive 1) ≤
    2 * accuracy at hone
  change pmfOperationalDistance (laws 2) (conditionActive laws cutoff hpositive 2) ≤
    2 * accuracy at htwo
  have hanchor : pmfOperationalDistance (laws 3)
      (conditionActive laws cutoff hpositive 3) = 0 := by
    rw [conditionActive_anchor, pmfOperationalDistance_self]
  rw [Fin.sum_univ_four, hanchor]
  nlinarith

theorem conditioning_opponent_distance_sum_le
    (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    {accuracy : ℝ} (hbefore : ∀ active : Fin 3,
      1 - survival (laws active.castSucc) cutoff ≤ accuracy) (active : Fin 3) :
    ∑ who ∈ Finset.univ.erase active.castSucc,
      pmfOperationalDistance (laws who) (conditionActive laws cutoff hpositive who) ≤
        4 * accuracy := by
  have hcoordinate : ∀ active : Fin 3,
      pmfOperationalDistance (laws active.castSucc)
        (conditionActive laws cutoff hpositive active.castSucc) ≤ 2 * accuracy := by
    intro active
    rw [conditionActive_active]
    change 2 * pmfGeneralTV _ _ ≤ 2 * accuracy
    rw [pmfGeneralTV_conditionAt]
    linarith [hbefore active]
  have hzero := hcoordinate 0
  have hone := hcoordinate 1
  have htwo := hcoordinate 2
  change pmfOperationalDistance (laws 0) (conditionActive laws cutoff hpositive 0) ≤
    2 * accuracy at hzero
  change pmfOperationalDistance (laws 1) (conditionActive laws cutoff hpositive 1) ≤
    2 * accuracy at hone
  change pmfOperationalDistance (laws 2) (conditionActive laws cutoff hpositive 2) ≤
    2 * accuracy at htwo
  have hanchor : pmfOperationalDistance (laws 3)
      (conditionActive laws cutoff hpositive 3) = 0 := by
    rw [conditionActive_anchor, pmfOperationalDistance_self]
  fin_cases active
  · change ∑ who ∈ Finset.univ.erase (0 : Fin 4),
        pmfOperationalDistance (laws who) (conditionActive laws cutoff hpositive who) ≤
          4 * accuracy
    have herase : (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} := by decide
    rw [herase, Finset.sum_insert (by decide : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
      Finset.sum_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))),
      Finset.sum_singleton, hanchor]
    nlinarith
  · change ∑ who ∈ Finset.univ.erase (1 : Fin 4),
        pmfOperationalDistance (laws who) (conditionActive laws cutoff hpositive who) ≤
          4 * accuracy
    have herase : (Finset.univ.erase (1 : Fin 4)) = {0, 2, 3} := by decide
    rw [herase, Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
      Finset.sum_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))),
      Finset.sum_singleton, hanchor]
    nlinarith
  · change ∑ who ∈ Finset.univ.erase (2 : Fin 4),
        pmfOperationalDistance (laws who) (conditionActive laws cutoff hpositive who) ≤
          4 * accuracy
    have herase : (Finset.univ.erase (2 : Fin 4)) = {0, 1, 3} := by decide
    rw [herase, Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({1, 3} : Finset (Fin 4))),
      Finset.sum_insert (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))),
      Finset.sum_singleton, hanchor]
    nlinarith

/-- Conditioning prescribed active play costs at most 12 times accuracy. -/
theorem abs_expectedPayoff_sub_conditionActive_le
    (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    {accuracy : ℝ} (hbefore : ∀ active : Fin 3,
      1 - survival (laws active.castSucc) cutoff ≤ accuracy) (who : Fin 4) :
    |quittingStoppingLawExpectedPayoff reward laws who -
        quittingStoppingLawExpectedPayoff reward
          (conditionActive laws cutoff hpositive) who| ≤ 12 * accuracy := by
  have hpayoff := abs_quittingStoppingLawExpectedPayoff_sub_le_terminalOutcomeDistance
    reward laws (conditionActive laws cutoff hpositive) who reward_abs_le_two
  have houtcome := quittingTerminalOutcomeOperationalDistance_le_sum
    laws (conditionActive laws cutoff hpositive)
  have hsum := conditioning_distance_sum_le laws cutoff hpositive hbefore
  exact hpayoff.trans (by nlinarith)

/-- A common endpoint replacement excludes its own marginal from the bill. -/
theorem abs_expectedPayoff_update_sub_conditionActive_le
    (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    {accuracy : ℝ} (hbefore : ∀ active : Fin 3,
      1 - survival (laws active.castSucc) cutoff ≤ accuracy)
    (active : Fin 3) (replacement : PMF (Option ℕ)) :
    |quittingStoppingLawExpectedPayoff reward
          (Function.update laws active.castSucc replacement) active.castSucc -
        quittingStoppingLawExpectedPayoff reward
          (Function.update (conditionActive laws cutoff hpositive)
            active.castSucc replacement) active.castSucc| ≤ 8 * accuracy := by
  have hpayoff := abs_quittingStoppingLawExpectedPayoff_update_same_sub_le_opponents
    reward laws (conditionActive laws cutoff hpositive)
    active.castSucc replacement reward_abs_le_two
  have hsum := conditioning_opponent_distance_sum_le laws cutoff hpositive hbefore active
  exact hpayoff.trans (by nlinarith)

def endpointLaw (cutoff : ℕ) (quit : Bool) : PMF (Option ℕ) :=
  PMF.pure (if quit then some cutoff else none)

theorem endpointLaw_support (cutoff : ℕ) (quit : Bool) (choice : Option ℕ)
    (hchoice : endpointLaw cutoff quit choice ≠ 0) : survivesUntil cutoff choice := by
  have heq : choice = if quit then some cutoff else none := by
    by_contra hne
    exact hchoice (by simp [endpointLaw, PMF.pure_apply, hne])
  rw [heq]
  cases quit <;> simp [survivesUntil]

@[simp] theorem endpointLaw_finiteMass (cutoff : ℕ) (quit : Bool) :
    finiteMass (endpointLaw cutoff quit) cutoff = if quit then 1 else 0 := by
  cases quit <;> simp [endpointLaw, finiteMass]

theorem conditionActive_update_endpoint_support
    (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    (active : Fin 3) (quit : Bool) :
    ∀ who : Fin 3, ∀ choice,
      Function.update (conditionActive laws cutoff hpositive)
        active.castSucc (endpointLaw cutoff quit) who.castSucc choice ≠ 0 →
          survivesUntil cutoff choice := by
  intro who choice hchoice
  by_cases hwho : who = active
  · subst who
    rw [Function.update_self] at hchoice
    exact endpointLaw_support cutoff quit choice hchoice
  · have hcast : who.castSucc ≠ active.castSucc := by simpa using hwho
    rw [Function.update_of_ne hcast] at hchoice
    exact conditionActive_support laws cutoff hpositive who choice hchoice

theorem conditionActive_update_endpoint_probabilities
    (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    (active : Fin 3) (quit : Bool) :
    (fun who : Fin 3 => finiteMass
        (Function.update (conditionActive laws cutoff hpositive)
          active.castSucc (endpointLaw cutoff quit) who.castSucc) cutoff) =
      Function.update (conditionalProbabilities laws cutoff) active (if quit then 1 else 0) := by
  funext who
  by_cases hwho : who = active
  · subst who
    simp
  · have hcast : who.castSucc ≠ active.castSucc := by simpa using hwho
    rw [Function.update_of_ne hcast, Function.update_of_ne hwho,
      conditionActive_finiteMass]

theorem abs_conditionActivePayoff_sub_anchor_activePayoff_le
    (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    {accuracy : ℝ} (htail : survival (laws 3) (cutoff + 1) ≤ accuracy) (active : Fin 3) :
    |quittingStoppingLawExpectedPayoff reward
          (conditionActive laws cutoff hpositive) active.castSucc -
        finiteMass (laws 3) cutoff * activePayoff (conditionalProbabilities laws cutoff) active|
      ≤ 2 * accuracy := by
  have hrow := abs_expectedPayoff_sub_anchor_row_le
    (conditionActive laws cutoff hpositive) cutoff active
    (conditionActive_support laws cutoff hpositive)
  have hprob : (fun who : Fin 3 =>
      finiteMass (conditionActive laws cutoff hpositive who.castSucc) cutoff) =
        conditionalProbabilities laws cutoff := by
    funext who
    exact conditionActive_finiteMass laws cutoff hpositive who
  simp only [conditionActive_anchor, hprob] at hrow
  exact hrow.trans (mul_le_mul_of_nonneg_left htail (by norm_num))

theorem abs_conditionActiveEndpointPayoff_sub_anchor_endpointPayoff_le
    (laws : Fin 4 → PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3, 0 < survival (laws active.castSucc) cutoff)
    {accuracy : ℝ} (htail : survival (laws 3) (cutoff + 1) ≤ accuracy)
    (active : Fin 3) (quit : Bool) :
    |quittingStoppingLawExpectedPayoff reward
          (Function.update (conditionActive laws cutoff hpositive)
            active.castSucc (endpointLaw cutoff quit)) active.castSucc -
        finiteMass (laws 3) cutoff *
          activeEndpointPayoff (conditionalProbabilities laws cutoff) active quit| ≤
      2 * accuracy := by
  have hrow := abs_expectedPayoff_sub_anchor_row_le
    (Function.update (conditionActive laws cutoff hpositive)
      active.castSucc (endpointLaw cutoff quit)) cutoff active
    (conditionActive_update_endpoint_support laws cutoff hpositive active quit)
  simp only [Function.update_of_ne (Ne.symm (active_ne_anchor active)), conditionActive_anchor,
    conditionActive_update_endpoint_probabilities, activePayoff_update_endpoint] at hrow
  exact hrow.trans (mul_le_mul_of_nonneg_left htail (by norm_num))

/-- The 14-accuracy estimate concerns the original actual prescribed payoff. -/
theorem actual_prescribed_payoff_estimate
    (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3,
      0 < survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff)
    {accuracy : ℝ} (hbefore : ∀ active : Fin 3,
      1 - survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff ≤ accuracy)
    (htail : survival (quittingBehaviorStoppingLaws reward parent 3) (cutoff + 1) ≤ accuracy)
    (active : Fin 3) :
    |quittingTerminalPayoff reward parent active.castSucc -
        finiteMass (quittingBehaviorStoppingLaws reward parent 3) cutoff *
          activePayoff (conditionalProbabilities
            (quittingBehaviorStoppingLaws reward parent) cutoff) active| ≤ 14 * accuracy := by
  rw [← quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff]
  have hcondition := abs_expectedPayoff_sub_conditionActive_le
    (quittingBehaviorStoppingLaws reward parent) cutoff hpositive hbefore active.castSucc
  have hrow := abs_conditionActivePayoff_sub_anchor_activePayoff_le
    (quittingBehaviorStoppingLaws reward parent) cutoff hpositive htail active
  exact (abs_sub_le _ (quittingStoppingLawExpectedPayoff reward
    (conditionActive (quittingBehaviorStoppingLaws reward parent) cutoff hpositive)
    active.castSucc) _).trans (by linarith)

/-- Both actual replacements, Quit at K and Never, have the 10-accuracy estimate. -/
theorem actual_endpoint_payoff_estimate
    (parent : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (hpositive : ∀ active : Fin 3,
      0 < survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff)
    {accuracy : ℝ} (hbefore : ∀ active : Fin 3,
      1 - survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff ≤ accuracy)
    (htail : survival (quittingBehaviorStoppingLaws reward parent 3) (cutoff + 1) ≤ accuracy)
    (active : Fin 3) (quit : Bool) :
    |quittingTerminalPayoff reward (Function.update parent active.castSucc
          (quittingStoppingLawBehaviorStrategy reward active.castSucc
            (endpointLaw cutoff quit))) active.castSucc -
        finiteMass (quittingBehaviorStoppingLaws reward parent 3) cutoff *
          activeEndpointPayoff (conditionalProbabilities
            (quittingBehaviorStoppingLaws reward parent) cutoff) active quit| ≤ 10 * accuracy := by
  rw [terminalPayoff_update_reconstructed_law]
  have hcondition := abs_expectedPayoff_update_sub_conditionActive_le
    (quittingBehaviorStoppingLaws reward parent) cutoff hpositive hbefore
    active (endpointLaw cutoff quit)
  have hrow := abs_conditionActiveEndpointPayoff_sub_anchor_endpointPayoff_le
    (quittingBehaviorStoppingLaws reward parent) cutoff hpositive htail active quit
  exact (abs_sub_le _ (quittingStoppingLawExpectedPayoff reward
    (Function.update
      (conditionActive (quittingBehaviorStoppingLaws reward parent) cutoff hpositive)
      active.castSucc (endpointLaw cutoff quit)) active.castSucc) _).trans (by linarith)

/-- The error and square-root scale produce the actual date and all payoff
comparisons internally. No selected favorable quantile is an input field. -/
theorem exists_actual_quantile_payoff_estimates
    (parent : (quittingGame reward).BehaviorProfile) {error accuracy : ℝ}
    (herror : quittingTerminalExploitability reward parent ≤ error)
    (haccuracy : 0 < accuracy) (haccuracyOne : accuracy < 1)
    (hscale : error ≤ accuracy ^ 2) :
    ∃ cutoff,
      (∀ active : Fin 3,
        0 < survival (quittingBehaviorStoppingLaws reward parent active.castSucc) cutoff) ∧
      stoppingLawFirstCrossing? (quittingBehaviorStoppingLaws reward parent 3)
        (1 - accuracy) = some cutoff ∧
      (∀ active : Fin 3,
        |quittingTerminalPayoff reward parent active.castSucc -
          finiteMass (quittingBehaviorStoppingLaws reward parent 3) cutoff *
            activePayoff (conditionalProbabilities
              (quittingBehaviorStoppingLaws reward parent) cutoff) active| ≤ 14 * accuracy) ∧
      (∀ active : Fin 3, ∀ quit : Bool,
        |quittingTerminalPayoff reward (Function.update parent active.castSucc
            (quittingStoppingLawBehaviorStrategy reward active.castSucc (endpointLaw cutoff quit)))
            active.castSucc -
          finiteMass (quittingBehaviorStoppingLaws reward parent 3) cutoff *
            activeEndpointPayoff (conditionalProbabilities
              (quittingBehaviorStoppingLaws reward parent) cutoff) active quit| ≤
          10 * accuracy) := by
  obtain ⟨cutoff, hfirst, _, htail, hactive⟩ :=
    exists_actual_quantile_source parent herror haccuracy haccuracyOne hscale
  have hpositive := fun active => (hactive active).2.2.2
  have hbefore := fun active => (hactive active).2.1
  refine ⟨cutoff, hpositive, hfirst, ?_, ?_⟩
  · intro active
    exact actual_prescribed_payoff_estimate parent cutoff hpositive hbefore htail active
  · intro active quit
    exact actual_endpoint_payoff_estimate parent cutoff hpositive hbefore htail active quit

end GameTheory.AdaptiveChildCenter
