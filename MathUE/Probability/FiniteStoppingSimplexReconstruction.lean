import MathUE.Probability.StoppingLawReconstruction
import MathUE.ProbabilityMassFunction.FiniteStoppingTimeMenu
import MathUE.ProbabilityMassFunction.Simplex
import Mathlib.Topology.Algebra.Field

/-! # Conditional hazards of finite stopping simplices

The law and hazard are the canonical finite-simplex PMF, finite stopping-time
inclusion, and stopping-law reconstruction. Positive Never mass makes the
conditional decoder continuous and strictly below one at every date. This
does not assert equilibrium-component continuation or Nash correspondence
between a finite normal-form game and its behavioral realization.
-/

noncomputable section

open scoped BigOperators

namespace Math.Probability.FiniteStoppingSimplex

open DiscreteHazard

variable {deadline : ℕ}

/-- Include the canonical finite simplex PMF in the complete stopping-time space. -/
def law (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline))) : PMF (Option ℕ) :=
  ((Math.ProbabilityMassFunction.stdSimplexEquiv
    (α := Option (Fin deadline))).symm simplex).map
      (finiteStoppingTimeDecode deadline)

/-- The finite-date coordinate vector, extended by zero after the deadline. -/
def mass (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline))) (time : ℕ) : ℝ :=
  if htime : time < deadline then simplex.weights (some ⟨time, htime⟩) else 0

private theorem decode_injective (deadline : ℕ) :
    Function.Injective (finiteStoppingTimeDecode deadline) :=
  Option.map_injective Fin.val_injective

private theorem law_decode
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)))
    (action : Option (Fin deadline)) :
    law simplex (finiteStoppingTimeDecode deadline action) =
      ((Math.ProbabilityMassFunction.stdSimplexEquiv
        (α := Option (Fin deadline))).symm simplex) action := by
  rw [law, PMF.map_apply, tsum_eq_single action]
  · simp
  · intro other hother
    have hne : finiteStoppingTimeDecode deadline action ≠
        finiteStoppingTimeDecode deadline other := by
      intro hequal
      exact hother ((decode_injective deadline hequal).symm)
    exact ite_eq_right hne

/-- Mapping the finite simplex law preserves its Never coordinate exactly. -/
theorem law_none_toReal
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline))) :
    (law simplex none).toReal = simplex.weights none := by
  have hequal := law_decode simplex none
  change law simplex none = _ at hequal
  rw [hequal, Math.ProbabilityMassFunction.stdSimplexEquiv_symm_apply,
    Math.ProbabilityMassFunction.ofVector_toReal]

/-- Every finite atom is its actual simplex coordinate or zero beyond the deadline. -/
theorem finiteMass_eq_mass
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline))) (time : ℕ) :
    StoppingLaw.finiteMass (law simplex) time = mass simplex time := by
  by_cases htime : time < deadline
  · have hequal := law_decode simplex (some ⟨time, htime⟩)
    change law simplex (some time) = _ at hequal
    rw [StoppingLaw.finiteMass, hequal,
      Math.ProbabilityMassFunction.stdSimplexEquiv_symm_apply,
      Math.ProbabilityMassFunction.ofVector_toReal]
    simp only [mass, htime, dite_eq_left]
  · have hzero : law simplex (some time) = 0 := by
      rw [law, PMF.map_apply]
      rw [ENNReal.tsum_eq_zero]
      intro action
      cases action with
      | none => simp [finiteStoppingTimeDecode]
      | some date =>
          have hne : time ≠ date.val :=
            ne_of_gt (date.isLt.trans_le (Nat.le_of_not_gt htime))
          simp [finiteStoppingTimeDecode, hne]
    simp [StoppingLaw.finiteMass, hzero, mass, htime]

/-- The actual surviving mass is one minus the finite simplex prefix. -/
theorem survival_eq_one_sub_prefix
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline))) (time : ℕ) :
    StoppingLaw.survival (law simplex) time =
      1 - ∑ date ∈ Finset.range time, mass simplex date := by
  simp only [StoppingLaw.survival, finiteMass_eq_mass]

/-- The actual surviving mass dominates the retained Never coordinate. -/
theorem none_weight_le_survival
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline))) (time : ℕ) :
    simplex.weights none ≤ StoppingLaw.survival (law simplex) time := by
  have hbound := ScalarHazard.neverMass_le_survival
    (StoppingLaw.toScalarHazard (law simplex)) time
  simpa only [StoppingLaw.toScalarHazard_neverMass,
    StoppingLaw.toScalarHazard_survival, law_none_toReal] using hbound

/-- Positive Never mass prevents every conditional denominator from vanishing. -/
theorem survival_pos
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)))
    (hnone : 0 < simplex.weights none) (time : ℕ) :
    0 < StoppingLaw.survival (law simplex) time :=
  hnone.trans_le (none_weight_le_survival simplex time)

/-- The literal conditional quotient, including the exhausted-prefix branch. -/
theorem stop_eq_conditional
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline))) (time : ℕ) :
    (StoppingLaw.toScalarHazard (law simplex)).stop time =
      if (1 - ∑ date ∈ Finset.range time, mass simplex date) = 0 then 0
      else mass simplex time /
        (1 - ∑ date ∈ Finset.range time, mass simplex date) := by
  simp only [StoppingLaw.toScalarHazard, survival_eq_one_sub_prefix, finiteMass_eq_mass]

/-- With retained Never mass, the decoder is exactly the paper's conditional ratio. -/
theorem stop_eq_div
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)))
    (hnone : 0 < simplex.weights none) (time : ℕ) :
    (StoppingLaw.toScalarHazard (law simplex)).stop time =
      mass simplex time / StoppingLaw.survival (law simplex) time := by
  simp [StoppingLaw.toScalarHazard, (survival_pos simplex hnone time).ne',
    finiteMass_eq_mass]

/-- Every decoded finite hazard is strictly below one on the positive-Never domain. -/
theorem stop_lt_one
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)))
    (hnone : 0 < simplex.weights none) (time : ℕ) :
    (StoppingLaw.toScalarHazard (law simplex)).stop time < 1 := by
  rw [stop_eq_div simplex hnone time]
  apply (div_lt_one (survival_pos simplex hnone time)).2
  have hnext := survival_pos simplex hnone (time + 1)
  rw [StoppingLaw.survival_succ, finiteMass_eq_mass] at hnext
  linarith

/-- At the exact finite deadline, survival is the retained Never atom. -/
theorem survival_deadline_eq_none
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline))) :
    StoppingLaw.survival (law simplex) deadline = simplex.weights none := by
  have htotal := StoppingLaw.none_add_tsum_finiteMass (law simplex)
  have hsum :
      (∑' time, StoppingLaw.finiteMass (law simplex) time) =
        ∑ time ∈ Finset.range deadline, StoppingLaw.finiteMass (law simplex) time := by
    apply tsum_eq_sum
    intro time htime
    have hlate : ¬time < deadline := by simpa only [Finset.mem_range] using htime
    rw [finiteMass_eq_mass]
    simp [mass, hlate]
  rw [hsum, law_none_toReal] at htotal
  unfold StoppingLaw.survival
  linarith

/-- The canonical decoder is literally quiet at and after its finite deadline. -/
theorem stop_eq_zero_of_le
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)))
    {time : ℕ} (htime : deadline ≤ time) :
    (StoppingLaw.toScalarHazard (law simplex)).stop time = 0 := by
  have hmass : StoppingLaw.finiteMass (law simplex) time = 0 := by
    rw [finiteMass_eq_mass]
    exact dite_eq_right (Nat.not_lt_of_ge htime)
  simp only [StoppingLaw.toScalarHazard, hmass, zero_div, ite_self]

/-- No decoded finite row quits surely exactly when the Never atom is positive. -/
theorem none_pos_iff_stop_lt_one
    (simplex : Convexity.StdSimplex ℝ (Option (Fin deadline))) :
    0 < simplex.weights none ↔
      ∀ time : Fin deadline, (StoppingLaw.toScalarHazard (law simplex)).stop time.val < 1 := by
  constructor
  · intro hnone time
    exact stop_lt_one simplex hnone time.val
  · intro hstop
    have hproduct :
        0 < ∏ time ∈ Finset.range deadline,
          (1 - (StoppingLaw.toScalarHazard (law simplex)).stop time) :=
      Finset.prod_pos fun time htime => sub_pos.mpr
        (hstop ⟨time, Finset.mem_range.mp htime⟩)
    have hsurvival :
        0 < (StoppingLaw.toScalarHazard (law simplex)).survival 0 deadline := by
      simpa only [ScalarHazard.survival, Math.survivalProduct, Nat.zero_add] using hproduct
    simpa only [StoppingLaw.toScalarHazard_survival, survival_deadline_eq_none]
      using hsurvival

private theorem continuous_weight (action : Option (Fin deadline)) :
    Continuous (fun simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)) =>
      simplex.weights action) :=
  (continuous_apply action).comp
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
      (Option (Fin deadline))).continuous

/-- Finite date masses vary continuously, including zero coordinates and empty calendars. -/
theorem continuous_mass (time : ℕ) :
    Continuous (fun simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)) =>
      mass simplex time) := by
  by_cases htime : time < deadline
  · simpa only [mass, htime, dite_eq_left] using
      continuous_weight (some ⟨time, htime⟩)
  · simp only [mass, htime, ↓reduceDIte]
    exact continuous_const

/-- Incoming surviving mass varies continuously on the entire finite simplex. -/
theorem continuous_survival (time : ℕ) :
    Continuous (fun simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)) =>
      StoppingLaw.survival (law simplex) time) := by
  simp_rw [survival_eq_one_sub_prefix]
  exact continuous_const.sub
    (continuous_finsetSum (Finset.range time) fun date _ => continuous_mass date)

/-- The canonical conditional hazard is continuous wherever Never mass is positive. -/
theorem continuousOn_stop (time : ℕ) :
    ContinuousOn
      (fun simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)) =>
        (StoppingLaw.toScalarHazard (law simplex)).stop time)
      {simplex | 0 < simplex.weights none} := by
  have hquotient : ContinuousOn
      (fun simplex : Convexity.StdSimplex ℝ (Option (Fin deadline)) =>
        mass simplex time / StoppingLaw.survival (law simplex) time)
      {simplex | 0 < simplex.weights none} :=
    (continuous_mass time).continuousOn.div (continuous_survival time).continuousOn
      (fun simplex hsimplex => (survival_pos simplex hsimplex time).ne')
  exact hquotient.congr fun simplex hsimplex => stop_eq_div simplex hsimplex time

end Math.Probability.FiniteStoppingSimplex
