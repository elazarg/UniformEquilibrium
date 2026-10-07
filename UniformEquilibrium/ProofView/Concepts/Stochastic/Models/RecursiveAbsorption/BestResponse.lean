import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.StationaryPayoff
import MathUE.PMFProduct.Bool
import MathUE.GeometricMinimumRecurrence
import UniformEquilibrium.Certificates.Adaptive.Certificate

/-!
# Behavioral best responses against stationary recursive absorption play

The stationary input is a family of actual independent action PMFs. A pure
response fixes one player's live action and retains the opponent's stationary
PMF. Its payoff below is the literal expected pathwise liminf under the actual
play law, identified with the checked stationary ratio rather than supplied
as a separate numerical payoff oracle.

The one-step continuation calculation is valid for arbitrary finite action
sets and zero absorption probabilities. One actual pure stationary response
dominates every behavioral deviation from every initial state. If its maximal
pure value is negative, a strictly positive minimum pure absorption hazard is
derived and forces the actual live-state probability to vanish. No fictitious
zero-payoff action or nonnegative floor is added to the best-response value.
-/

noncomputable section

open _root_.Math.Probability Math.PMFProduct Filter
open scoped Topology

namespace GameTheory.RecursiveAbsorption

variable {I J : Type}

/-- An actual pure stationary response to the given stationary action family. -/
def pureStationaryResponse (D : Data I J) (actions : ∀ who, PMF (Action I J who))
    (who : Bool) (action : Action I J who) : (game D).BehaviorProfile :=
  (game D).stationaryBehaviorProfile (Function.update actions who (PMF.pure action))

variable [Fintype I] [Fintype J]

/-- The literal expected-pathwise-liminf value of a pure stationary response. -/
def pureStationaryResponsePayoff (D : Data I J) (actions : ∀ who, PMF (Action I J who))
    (who : Bool) (action : Action I J who) : ℝ :=
  liminfPayoff D none (pureStationaryResponse D actions who action) who

/-- The one-step absorption mass of the actual pure stationary response. -/
def pureResponseAbsorptionMass (D : Data I J) (actions : ∀ who, PMF (Action I J who))
    (who : Bool) (action : Action I J who) : ℝ :=
  absorptionMass D ((Function.update actions who (PMF.pure action)) false)
    ((Function.update actions who (PMF.pure action)) true)

omit [Fintype I] [Fintype J] in
private theorem stationaryProfile_eq_stationaryActions (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) :
    stationaryProfile D (actions false) (actions true) =
      (game D).stationaryBehaviorProfile actions := by
  have heta : mixedAction (actions false) (actions true) = actions := by
    funext who
    cases who <;> rfl
  unfold stationaryProfile
  rw [heta]

/-- The checked stationary ratio identity for an arbitrary actual stationary action family. -/
theorem liminfPayoff_stationaryActions_none (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) :
    liminfPayoff D none ((game D).stationaryBehaviorProfile actions) who =
      stationaryPayoff D (actions false) (actions true) who := by
  rw [← stationaryProfile_eq_stationaryActions]
  exact liminfPayoff_stationary_none D (actions false) (actions true) who

/-- A pure response's actual payoff reconstructs its actual absorption-weighted numerator. -/
theorem pureStationaryResponsePayoff_mul_mass (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) (action : Action I J who) :
    pureStationaryResponsePayoff D actions who action *
        pureResponseAbsorptionMass D actions who action =
      absorbingContribution D ((Function.update actions who (PMF.pure action)) false)
        ((Function.update actions who (PMF.pure action)) true) who := by
  unfold pureStationaryResponsePayoff pureStationaryResponse pureResponseAbsorptionMass
  have hpayoff := liminfPayoff_stationaryActions_none D
    (Function.update actions who (PMF.pure action)) who
  exact (congrArg (fun value => value * absorptionMass D
      ((Function.update actions who (PMF.pure action)) false)
      ((Function.update actions who (PMF.pure action)) true)) hpayoff).trans
    (stationaryPayoff_mul_absorptionMass D _ _ who)

private def responsePotential (D : Data I J) (who : Bool) (value : ℝ) :
    (game D).State → ℝ :=
  fun state => match state with
    | none => value
    | some pair => D.reward pair.1 pair.2 who

private theorem expect_stationaryTransition_responsePotential (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) (value : ℝ) :
    expect (pmfPi actions) (fun action =>
        expect ((game D).transition none action) (responsePotential D who value)) =
      (1 - absorptionMass D (actions false) (actions true)) * value +
        absorbingContribution D (actions false) (actions true) who := by
  rw [expect_pmfPi_boolFamily]
  have hpoint (i : I) (j : J) :
      expect ((game D).transition none (jointAction i j)) (responsePotential D who value) =
        value - value * (D.absorption i j : ℝ) +
          (D.absorption i j : ℝ) * D.reward i j who := by
    calc
      _ = (1 - (D.absorption i j : ℝ)) * (responsePotential D who value) none +
          (D.absorption i j : ℝ) * (responsePotential D who value) (some (i, j)) :=
        expect_transition_none D (jointAction i j) (responsePotential D who value)
      _ = _ := by
        change (1 - (D.absorption i j : ℝ)) * value +
          (D.absorption i j : ℝ) * D.reward i j who = _
        ring
  change expect (actions false) (fun i => expect (actions true) (fun j =>
      expect ((game D).transition none (jointAction i j)) (responsePotential D who value))) = _
  simp_rw [hpoint, expect_add, expect_sub, expect_const, expect_const_mul]
  change value - value * absorptionMass D (actions false) (actions true) +
    absorbingContribution D (actions false) (actions true) who = _
  ring

private theorem pureResponse_transition_le (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) (value : ℝ)
    (hvalue : ∀ action, pureStationaryResponsePayoff D actions who action ≤ value)
    (action : Action I J who) :
    expect (pmfPi (Function.update actions who (PMF.pure action))) (fun joint =>
      expect ((game D).transition none joint) (responsePotential D who value)) ≤ value := by
  rw [expect_stationaryTransition_responsePotential]
  have hweighted := mul_le_mul_of_nonneg_right (hvalue action)
    (absorptionMass_nonneg D
      ((Function.update actions who (PMF.pure action)) false)
      ((Function.update actions who (PMF.pure action)) true))
  change pureStationaryResponsePayoff D actions who action *
      pureResponseAbsorptionMass D actions who action ≤
    value * pureResponseAbsorptionMass D actions who action at hweighted
  rw [pureStationaryResponsePayoff_mul_mass] at hweighted
  change absorbingContribution D ((Function.update actions who (PMF.pure action)) false)
    ((Function.update actions who (PMF.pure action)) true) who ≤
    value * absorptionMass D ((Function.update actions who (PMF.pure action)) false)
      ((Function.update actions who (PMF.pure action)) true) at hweighted
  linarith

private def liveValue : Option (I × J) → ℝ :=
  fun state => match state with
    | none => 1
    | some _ => 0

private theorem expect_deviationAction_le (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool)
    (deviation : (game D).BehaviorStrategy who) {time : ℕ} (history : (game D).Hist time)
    (f : (game D).JointAct → ℝ) (value : ℝ)
    (hvalue : ∀ action, expect (pmfPi (Function.update actions who (PMF.pure action))) f ≤ value) :
    expect ((game D).stageActionDist
      (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) history) f ≤
      value := by
  rw [(game D).stageActionDist_update_stationaryBehaviorProfile actions]
  change expect (pmfPi (A := Action I J)
    (Function.update actions who (deviation time history))) f ≤ value
  rw [pmfPi_update_bind (A := Action I J) actions who (deviation time history)]
  calc
    _ = expect (deviation time history) (fun action =>
        expect (pmfPi (Function.update actions who (PMF.pure action))) f) :=
      expect_bind (deviation time history : PMF (Action I J who))
        (fun action => pmfPi (A := Action I J) (Function.update actions who (PMF.pure action))) f
    _ ≤ expect (deviation time history) (fun _ => value) := expect_mono _ _ _ hvalue
    _ = value := expect_const _ _

private theorem responsePotential_continuation_le (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) (value : ℝ)
    (hvalue : ∀ action, pureStationaryResponsePayoff D actions who action ≤ value)
    (deviation : (game D).BehaviorStrategy who) {time : ℕ} (history : (game D).Hist time) :
    expect ((game D).stageActionDist
        (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) history)
      (fun action => expect ((game D).transition history.2 action)
        (responsePotential D who value)) ≤ responsePotential D who value history.2 := by
  cases history.2 with
  | none =>
      exact expect_deviationAction_le D actions who deviation history _ value
        (pureResponse_transition_le D actions who value hvalue)
  | some pair =>
      have hpoint (action : (game D).JointAct) :
          expect ((game D).transition (some pair) action) (responsePotential D who value) =
            responsePotential D who value (some pair) :=
        expect_transition_some D pair action (responsePotential D who value)
      change expect _ (fun action => expect ((game D).transition (some pair) action)
        (responsePotential D who value)) ≤ responsePotential D who value (some pair)
      simp_rw [hpoint]
      exact le_of_eq (expect_const _ _)

private theorem expectedHistoryValue_responsePotential_antitone (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) (value : ℝ)
    (hvalue : ∀ action, pureStationaryResponsePayoff D actions who action ≤ value)
    (deviation : (game D).BehaviorStrategy who) (time : ℕ) :
    (game D).expectedHistoryValue
        (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) none
        (fun _ history => responsePotential D who value history.2) (time + 1) ≤
      (game D).expectedHistoryValue
        (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) none
        (fun _ history => responsePotential D who value history.2) time := by
  rw [(game D).expectedHistoryValue_succ
    (Function.update ((game D).stationaryBehaviorProfile actions) who deviation)
    (none : (game D).State) (fun _ history => responsePotential D who value history.2) time]
  unfold StochasticGame.expectedHistoryValue StochasticGame.historyContinuationEU
  exact expect_mono _ _ _ (responsePotential_continuation_le D actions who value hvalue deviation)

private theorem expectedHistoryValue_responsePotential_eq (D : Data I J)
    (profile : (game D).BehaviorProfile) (who : Bool) (value : ℝ) (time : ℕ) :
    (game D).expectedHistoryValue profile none
        (fun _ history => responsePotential D who value history.2) time =
      (game D).expectedStagePayoff profile none time who +
        value * (game D).expectedStateValue profile none time liveValue := by
  have hpoint (history : (game D).Hist time) :
      responsePotential D who value history.2 =
        (game D).stageEUAt profile history who + value * liveValue history.2 := by
    cases hstate : history.2 with
    | none =>
        simp only [StochasticGame.stageEUAt, hstate, stagePayoff_none, expect_const,
          responsePotential, liveValue, mul_one, zero_add]
    | some pair =>
        simp only [StochasticGame.stageEUAt, hstate, stagePayoff_some, expect_const,
          responsePotential, liveValue, mul_zero, add_zero]
  unfold StochasticGame.expectedHistoryValue StochasticGame.expectedStagePayoff
    StochasticGame.expectedStateValue
  simp_rw [hpoint, expect_add, expect_const_mul]

private theorem pureStationaryResponsePayoff_eq_zero_of_mass_eq_zero (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) (action : Action I J who)
    (hzero : pureResponseAbsorptionMass D actions who action = 0) :
    pureStationaryResponsePayoff D actions who action = 0 := by
  unfold pureStationaryResponsePayoff pureStationaryResponse
  change absorptionMass D ((Function.update actions who (PMF.pure action)) false)
    ((Function.update actions who (PMF.pure action)) true) = 0 at hzero
  calc
    _ = stationaryPayoff D ((Function.update actions who (PMF.pure action)) false)
        ((Function.update actions who (PMF.pure action)) true) who :=
      liminfPayoff_stationaryActions_none D (Function.update actions who (PMF.pure action)) who
    _ = 0 := by rw [stationaryPayoff, hzero, div_zero]

private theorem exists_positive_pure_hazard_floor_of_negative_cap (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) (value : ℝ)
    (hvalue : ∀ action, pureStationaryResponsePayoff D actions who action ≤ value)
    (hnegative : value < 0) :
    ∃ floor : ℝ, 0 < floor ∧ floor ≤ 1 ∧
      ∀ action, floor ≤ pureResponseAbsorptionMass D actions who action := by
  classical
  have hpositive : ∀ action, 0 < pureResponseAbsorptionMass D actions who action := by
    intro action
    have hnonneg := absorptionMass_nonneg D
      ((Function.update actions who (PMF.pure action)) false)
      ((Function.update actions who (PMF.pure action)) true)
    change 0 ≤ pureResponseAbsorptionMass D actions who action at hnonneg
    by_contra hnot
    have hzero := le_antisymm (le_of_not_gt hnot) hnonneg
    have hpayoff := pureStationaryResponsePayoff_eq_zero_of_mass_eq_zero
      D actions who action hzero
    have hcap := hvalue action
    rw [hpayoff] at hcap
    exact (not_le_of_gt hnegative) hcap
  obtain ⟨anchor, _⟩ := (actions who).support_nonempty
  obtain ⟨least, _, hleast⟩ := Finset.exists_min_image Finset.univ
    (pureResponseAbsorptionMass D actions who) ⟨anchor, Finset.mem_univ anchor⟩
  refine ⟨pureResponseAbsorptionMass D actions who least, hpositive least, ?_, ?_⟩
  · exact absorptionMass_le_one D
      ((Function.update actions who (PMF.pure least)) false)
      ((Function.update actions who (PMF.pure least)) true)
  · exact fun action => hleast action (Finset.mem_univ action)

private theorem expect_stationaryTransition_liveValue (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) :
    expect (pmfPi actions) (fun action =>
        expect ((game D).transition none action) liveValue) =
      1 - absorptionMass D (actions false) (actions true) := by
  have hpoint (i : I) (j : J) :
      expect ((game D).transition none (jointAction i j)) liveValue =
        1 - (D.absorption i j : ℝ) := by
    calc
      _ = (1 - (D.absorption i j : ℝ)) * liveValue none +
          (D.absorption i j : ℝ) * liveValue (some (i, j)) :=
        expect_transition_none D (jointAction i j) liveValue
      _ = _ := by simp only [liveValue, mul_one, mul_zero, add_zero]
  rw [expect_pmfPi_boolFamily]
  change expect (actions false) (fun i => expect (actions true) (fun j =>
      expect ((game D).transition none (jointAction i j)) liveValue)) = _
  simp only [hpoint, expect_sub, expect_const, absorptionMass]

private theorem liveValue_continuation_le (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool)
    (deviation : (game D).BehaviorStrategy who) (floor : ℝ)
    (hfloor : ∀ action, floor ≤ pureResponseAbsorptionMass D actions who action)
    {time : ℕ} (history : (game D).Hist time) :
    expect ((game D).stageActionDist
        (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) history)
      (fun action => expect ((game D).transition history.2 action) liveValue) ≤
        (1 - floor) * liveValue history.2 := by
  cases history.2 with
  | none =>
      have hnone : liveValue (none : Option (I × J)) = 1 := rfl
      rw [hnone, mul_one]
      change expect _ (fun action => expect ((game D).transition none action) liveValue) ≤
        1 - floor
      apply expect_deviationAction_le D actions who deviation history _ (1 - floor)
      intro action
      calc
        _ = 1 - pureResponseAbsorptionMass D actions who action :=
          expect_stationaryTransition_liveValue D (Function.update actions who (PMF.pure action))
        _ ≤ 1 - floor := sub_le_sub_left (hfloor action) 1
  | some pair =>
      have hsome : liveValue (some pair) = 0 := rfl
      rw [hsome, mul_zero]
      have hpoint (action : (game D).JointAct) :
          expect ((game D).transition (some pair) action) liveValue = 0 :=
        expect_transition_some D pair action liveValue
      change expect _ (fun action => expect ((game D).transition (some pair) action) liveValue) ≤ 0
      simp_rw [hpoint]
      exact le_of_eq (expect_const _ _)

private def deviationLiveMass (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool)
    (deviation : (game D).BehaviorStrategy who) (time : ℕ) : ℝ :=
  (game D).expectedStateValue
    (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) none time liveValue

omit [Fintype I] [Fintype J] in
private theorem deviationLiveMass_nonneg (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool)
    (deviation : (game D).BehaviorStrategy who) (time : ℕ) :
    0 ≤ deviationLiveMass D actions who deviation time := by
  apply expect_nonneg
  intro history
  cases history.2 <;> simp only [liveValue, zero_le_one, le_refl]

private theorem tendsto_deviationLiveMass_zero_of_hazard_floor (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool)
    (deviation : (game D).BehaviorStrategy who) (floor : ℝ)
    (hpositive : 0 < floor) (hupper : floor ≤ 1)
    (hfloor : ∀ action, floor ≤ pureResponseAbsorptionMass D actions who action) :
    Tendsto (deviationLiveMass D actions who deviation) atTop (𝓝 0) := by
  have hratio : 0 ≤ 1 - floor := sub_nonneg.mpr hupper
  have hratio_lt : 1 - floor < 1 := by linarith
  have hzero : deviationLiveMass D actions who deviation 0 = 1 :=
    (game D).expectedStateValue_zero
      (Function.update ((game D).stationaryBehaviorProfile actions) who deviation)
      (none : (game D).State) liveValue
  have hstep (time : ℕ) : deviationLiveMass D actions who deviation (time + 1) ≤
      (1 - floor) * deviationLiveMass D actions who deviation time := by
    unfold deviationLiveMass
    rw [(game D).expectedStateValue_succ
      (Function.update ((game D).stationaryBehaviorProfile actions) who deviation)
      (none : (game D).State) time liveValue]
    calc
      _ ≤ expect ((game D).histDist
          (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) none time)
        (fun history => (1 - floor) * liveValue history.2) :=
          expect_mono _ _ _ (liveValue_continuation_le D actions who deviation floor hfloor)
      _ = _ := expect_const_mul _ _ _
  have henvelope := _root_.Math.sequence_le_geometric_of_step
    (deviationLiveMass D actions who deviation) 1 (1 - floor) hratio (le_of_eq hzero) hstep
  exact _root_.Math.tendsto_zero_of_sequence_le_geometric
    (deviationLiveMass D actions who deviation) 1 (1 - floor)
    (deviationLiveMass_nonneg D actions who deviation) hratio hratio_lt henvelope

private theorem liminfPayoff_deviation_le_of_pure_cap (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) (value : ℝ)
    (hvalue : ∀ action, pureStationaryResponsePayoff D actions who action ≤ value)
    (deviation : (game D).BehaviorStrategy who) :
    liminfPayoff D none
      (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) who ≤ value := by
  let profile := Function.update ((game D).stationaryBehaviorProfile actions) who deviation
  let potential : (game D).HistoryPotential :=
    fun _ history => responsePotential D who value history.2
  let error : ℕ → ℝ := fun time =>
    max (-value) 0 * deviationLiveMass D actions who deviation time
  have herror : Tendsto error atTop (𝓝 0) := by
    by_cases hnonneg : 0 ≤ value
    · have hmax : max (-value) 0 = 0 := max_eq_right (by linarith)
      simp only [error, hmax, zero_mul]
      exact tendsto_const_nhds
    · obtain ⟨floor, hpositive, hupper, hfloor⟩ :=
        exists_positive_pure_hazard_floor_of_negative_cap D actions who value hvalue
          (lt_of_not_ge hnonneg)
      have hlive := tendsto_deviationLiveMass_zero_of_hazard_floor
        D actions who deviation floor hpositive hupper hfloor
      simpa only [mul_zero] using hlive.const_mul (max (-value) 0)
  have hmono (time : ℕ) : (game D).expectedHistoryValue profile none potential (time + 1) ≤
      (game D).expectedHistoryValue profile none potential time :=
    expectedHistoryValue_responsePotential_antitone D actions who value hvalue deviation time
  have hstage (time : ℕ) : (game D).expectedStagePayoff profile none time who ≤
      (game D).expectedHistoryValue profile none potential time + error time := by
    have heq := expectedHistoryValue_responsePotential_eq D profile who value time
    have hcomp := mul_le_mul_of_nonneg_right (le_max_left (-value) 0)
      (deviationLiveMass_nonneg D actions who deviation time)
    change -value * (game D).expectedStateValue profile none time liveValue ≤ error time at hcomp
    change (game D).expectedStagePayoff profile none time who ≤
      (game D).expectedHistoryValue profile none
        (fun _ history => responsePotential D who value history.2) time + error time
    linarith
  have hfinite {horizon : ℕ} (hpositive : 0 < horizon) :
      (game D).finiteAveragePayoff none horizon profile who ≤
        value + (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon, error time := by
    have hcap := (game D).finiteAveragePayoff_le_of_expectedHistoryValue_supermartingale_ge
      profile none who potential error hmono hstage hpositive
    rw [(game D).expectedHistoryValue_zero profile (none : (game D).State) potential] at hcap
    exact hcap
  have hlimit : Tendsto (fun horizon : ℕ =>
      value + (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon, error time)
      atTop (𝓝 value) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror.cesaro
  apply le_of_tendsto_of_tendsto
    (tendsto_finiteAveragePayoff_liminfPayoff D profile none who) hlimit
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with horizon hpositive
  exact hfinite hpositive

/-- One actual pure stationary response dominates all behavioral deviations at every initial state.
The maximizing action is chosen once, before both the deviation and the initial state. -/
theorem exists_pure_stationary_bestResponse (D : Data I J)
    (actions : ∀ who, PMF (Action I J who)) (who : Bool) :
    ∃ action : Action I J who, ∀ deviation : (game D).BehaviorStrategy who,
      ∀ initial : (game D).State,
        liminfPayoff D initial
          (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) who ≤
        liminfPayoff D initial (pureStationaryResponse D actions who action) who := by
  classical
  obtain ⟨anchor, _⟩ := (actions who).support_nonempty
  obtain ⟨action, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (pureStationaryResponsePayoff D actions who) ⟨anchor, Finset.mem_univ anchor⟩
  refine ⟨action, ?_⟩
  intro deviation initial
  cases initial with
  | none =>
      exact liminfPayoff_deviation_le_of_pure_cap D actions who
        (pureStationaryResponsePayoff D actions who action)
        (fun other => hmax other (Finset.mem_univ other)) deviation
  | some pair =>
      exact le_of_eq ((liminfPayoff_some D
        (Function.update ((game D).stationaryBehaviorProfile actions) who deviation) pair who).trans
        (liminfPayoff_some D (pureStationaryResponse D actions who action) pair who).symm)

end GameTheory.RecursiveAbsorption
