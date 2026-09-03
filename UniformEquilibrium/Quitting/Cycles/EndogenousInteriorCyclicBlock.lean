/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import FixedPointTheorems.brouwer
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile
import UniformEquilibrium.Quitting.Root.NashDefect

/-!
# Endogenous interior approximate-Nash cyclic blocks

A continuous interior binary response and the one-stage Bellman map are solved
simultaneously on the finite hazard/value box.  Brouwer therefore supplies,
for every positive error and every positive finite period, a cyclic product
word with strictly interior hazards, exact Bellman return, and the requested
local Nash error.  The exponential response also records the exact odds law
needed to compare hazards whose endpoint gaps stay uniformly separated.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct Math.ProbabilityMassFunction Set Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-! ## A continuous interior binary approximate response -/

/-- The logistic binary response at positive temperature `error`.
Positive temperature keeps the response strictly between zero and one. -/
def interiorBinaryApproximateResponse
    (error quitValue continueValue : ℝ) : ℝ :=
  Real.exp ((quitValue - continueValue) / error) /
    (1 + Real.exp ((quitValue - continueValue) / error))

private theorem interiorBinaryApproximateResponse_denominator_pos
    (error quitValue continueValue : ℝ) :
    0 < 1 + Real.exp ((quitValue - continueValue) / error) := by
  positivity

/-- The softened binary response is continuous in both endpoint values. -/
theorem continuous_interiorBinaryApproximateResponse
    (error : ℝ) :
    Continuous fun point : ℝ × ℝ ↦
      interiorBinaryApproximateResponse error point.1 point.2 := by
  unfold interiorBinaryApproximateResponse
  have hexp : Continuous fun point : ℝ × ℝ ↦
      Real.exp ((point.1 - point.2) / error) :=
    Real.continuous_exp.comp ((continuous_fst.sub continuous_snd).div_const error)
  apply hexp.div (continuous_const.add hexp)
  · intro point
    exact ne_of_gt
      (interiorBinaryApproximateResponse_denominator_pos
        error point.1 point.2)

/-- A positive smoothing error gives positive Quit probability. -/
theorem interiorBinaryApproximateResponse_pos
    (error quitValue continueValue : ℝ) :
    0 < interiorBinaryApproximateResponse error quitValue continueValue := by
  apply div_pos
  · exact Real.exp_pos _
  · exact interiorBinaryApproximateResponse_denominator_pos
      error quitValue continueValue

/-- A positive smoothing error leaves positive Continue probability. -/
theorem interiorBinaryApproximateResponse_lt_one
    (error quitValue continueValue : ℝ) :
    interiorBinaryApproximateResponse error quitValue continueValue < 1 := by
  apply (div_lt_one
    (interiorBinaryApproximateResponse_denominator_pos
      error quitValue continueValue)).2
  linarith [Real.exp_pos ((quitValue - continueValue) / error)]

/-- Exchanging the endpoint values complements the logistic response. -/
theorem interiorBinaryApproximateResponse_swap
    {error : ℝ} (herror : 0 < error) (quitValue continueValue : ℝ) :
    interiorBinaryApproximateResponse error continueValue quitValue =
      1 - interiorBinaryApproximateResponse error quitValue continueValue := by
  unfold interiorBinaryApproximateResponse
  have herrorNe : error ≠ 0 := ne_of_gt herror
  have hexpNe : Real.exp ((quitValue - continueValue) / error) ≠ 0 :=
    Real.exp_ne_zero _
  rw [show (continueValue - quitValue) / error =
      -((quitValue - continueValue) / error) by field_simp; ring,
    Real.exp_neg]
  field_simp [hexpNe]
  ring

/-- The odds of the logistic response are the exponential endpoint-gap ratio. -/
theorem interiorBinaryApproximateResponse_odds
    (error quitValue continueValue : ℝ) :
    interiorBinaryApproximateResponse error quitValue continueValue /
        (1 - interiorBinaryApproximateResponse error quitValue continueValue) =
      Real.exp ((quitValue - continueValue) / error) := by
  unfold interiorBinaryApproximateResponse
  have hexpPos := Real.exp_pos ((quitValue - continueValue) / error)
  field_simp [ne_of_gt hexpPos]
  ring

/-- If two nonnegative Continue advantages are separated by `separation`,
the response at the larger advantage is exponentially smaller. -/
theorem interiorBinaryApproximateResponse_ratio_le_exp_of_separated_continueAdvantages
    {error : ℝ} (herror : 0 < error)
    (quitHigh continueHigh quitLow continueLow separation : ℝ)
    (hlow : quitLow ≤ continueLow)
    (hseparated : continueLow - quitLow + separation ≤
      continueHigh - quitHigh) :
    interiorBinaryApproximateResponse error quitHigh continueHigh /
        interiorBinaryApproximateResponse error quitLow continueLow ≤
      2 * Real.exp (-separation / error) := by
  let highExponent := (quitHigh - continueHigh) / error
  let lowExponent := (quitLow - continueLow) / error
  have hhighExpPos : 0 < Real.exp highExponent := Real.exp_pos _
  have hlowExpPos : 0 < Real.exp lowExponent := Real.exp_pos _
  have hhighDenPos : 0 < 1 + Real.exp highExponent := by positivity
  have hlowDenPos : 0 < 1 + Real.exp lowExponent := by positivity
  have hlowExpLeOne : Real.exp lowExponent ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith)
      (le_of_lt herror)
  have hfactorNonnegative :
      0 ≤ (1 + Real.exp lowExponent) / (1 + Real.exp highExponent) := by
    positivity
  have hfactorLe :
      (1 + Real.exp lowExponent) / (1 + Real.exp highExponent) ≤ 2 := by
    apply (div_le_iff₀ hhighDenPos).2
    nlinarith [Real.exp_pos highExponent]
  have hexponent : highExponent - lowExponent ≤ -separation / error := by
    dsimp [highExponent, lowExponent]
    rw [← sub_div]
    apply (div_le_div_iff_of_pos_right herror).2
    linarith
  have hexpComparison :
      Real.exp highExponent / Real.exp lowExponent ≤
        Real.exp (-separation / error) := by
    rw [← Real.exp_sub, Real.exp_le_exp]
    exact hexponent
  have hratio :
      interiorBinaryApproximateResponse error quitHigh continueHigh /
          interiorBinaryApproximateResponse error quitLow continueLow =
        (Real.exp highExponent / Real.exp lowExponent) *
          ((1 + Real.exp lowExponent) / (1 + Real.exp highExponent)) := by
    dsimp [highExponent, lowExponent]
    unfold interiorBinaryApproximateResponse
    field_simp [ne_of_gt hhighExpPos, ne_of_gt hlowExpPos,
      ne_of_gt hhighDenPos, ne_of_gt hlowDenPos]
  rw [hratio]
  nlinarith [mul_le_mul hexpComparison hfactorLe hfactorNonnegative
    (Real.exp_nonneg (-separation / error))]

/-- Along positive temperatures tending to zero, a fixed positive separation
between two nonnegative Continue advantages makes their response ratio vanish. -/
theorem tendsto_interiorBinaryApproximateResponse_ratio_zero_of_separated_continueAdvantages
    (error quitHigh continueHigh quitLow continueLow : ℕ → ℝ)
    {separation : ℝ} (hseparation : 0 < separation)
    (herrorPos : ∀ index, 0 < error index)
    (herrorZero : Tendsto error atTop (𝓝 0))
    (hlow : ∀ᶠ index in atTop, quitLow index ≤ continueLow index)
    (hseparated : ∀ᶠ index in atTop,
      continueLow index - quitLow index + separation ≤
        continueHigh index - quitHigh index) :
    Tendsto (fun index ↦
      interiorBinaryApproximateResponse (error index)
          (quitHigh index) (continueHigh index) /
        interiorBinaryApproximateResponse (error index)
          (quitLow index) (continueLow index)) atTop (𝓝 0) := by
  have herrorWithin : Tendsto error atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within error herrorZero
      (Eventually.of_forall herrorPos)
  have hinverse : Tendsto (fun index ↦ (error index)⁻¹) atTop atTop := by
    simpa [Pi.inv_def] using herrorWithin.inv_tendsto_nhdsGT_zero
  have hscaled : Tendsto (fun index ↦ separation * (error index)⁻¹)
      atTop atTop := hinverse.const_mul_atTop hseparation
  have hexponential : Tendsto
      (fun index ↦ Real.exp (-(separation * (error index)⁻¹)))
      atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  have hupper : Tendsto
      (fun index ↦ 2 * Real.exp (-separation / error index))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, neg_mul, mul_zero] using
      tendsto_const_nhds.mul hexponential
  apply squeeze_zero'
  · exact Eventually.of_forall fun index ↦ div_nonneg
      (interiorBinaryApproximateResponse_pos _ _ _).le
      (interiorBinaryApproximateResponse_pos _ _ _).le
  · filter_upwards [hlow, hseparated] with index hlowIndex hseparatedIndex
    exact interiorBinaryApproximateResponse_ratio_le_exp_of_separated_continueAdvantages
      (herrorPos index) _ _ _ _ separation hlowIndex hseparatedIndex
  · exact hupper

private theorem nonnegative_gap_logistic_loss_le
    {error gap : ℝ} (herror : 0 < error) :
    gap / (1 + Real.exp (gap / error)) ≤ error := by
  have hscaled : gap / error ≤ Real.exp (gap / error) := by
    linarith [Real.add_one_le_exp (gap / error)]
  have hgapBound : gap ≤ error * Real.exp (gap / error) := by
    calc
      gap = error * (gap / error) := by field_simp
      _ ≤ error * Real.exp (gap / error) :=
        mul_le_mul_of_nonneg_left hscaled (le_of_lt herror)
  apply (div_le_iff₀ (by positivity : 0 < 1 + Real.exp (gap / error))).2
  nlinarith [Real.exp_pos (gap / error)]

/-- Mixing the two endpoint values with the softened response loses at most
`error` relative to the better endpoint. -/
theorem binaryEndpointDefect_interiorBinaryApproximateResponse_le
    {error : ℝ} (herror : 0 < error) (quitValue continueValue : ℝ) :
    max quitValue continueValue -
        (interiorBinaryApproximateResponse error quitValue continueValue *
            quitValue +
          (1 - interiorBinaryApproximateResponse
            error quitValue continueValue) * continueValue) ≤ error := by
  have hdenominator := interiorBinaryApproximateResponse_denominator_pos
    error quitValue continueValue
  by_cases hdifference : 0 ≤ quitValue - continueValue
  · have hcontinueQuit : continueValue ≤ quitValue := by linarith
    rw [max_eq_left hcontinueQuit]
    have hidentity :
        quitValue -
            (interiorBinaryApproximateResponse error quitValue continueValue *
                quitValue +
              (1 - interiorBinaryApproximateResponse
                error quitValue continueValue) * continueValue) =
          (quitValue - continueValue) /
            (1 + Real.exp ((quitValue - continueValue) / error)) := by
      rw [interiorBinaryApproximateResponse]
      field_simp [ne_of_gt hdenominator]
      ring
    rw [hidentity]
    exact nonnegative_gap_logistic_loss_le herror
  · have hnegative : quitValue - continueValue ≤ 0 := le_of_not_ge hdifference
    have hquitContinue : quitValue ≤ continueValue := by linarith
    rw [max_eq_right hquitContinue]
    have hresponse :
        interiorBinaryApproximateResponse error quitValue continueValue =
          1 - interiorBinaryApproximateResponse error continueValue quitValue := by
      linarith [interiorBinaryApproximateResponse_swap
        herror quitValue continueValue]
    have hdenominatorSwapped :=
      interiorBinaryApproximateResponse_denominator_pos
        error continueValue quitValue
    have hidentity :
        continueValue -
            ((1 - interiorBinaryApproximateResponse
                error continueValue quitValue) * quitValue +
              interiorBinaryApproximateResponse
                error continueValue quitValue * continueValue) =
          (continueValue - quitValue) /
            (1 + Real.exp ((continueValue - quitValue) / error)) := by
      rw [interiorBinaryApproximateResponse]
      field_simp [ne_of_gt hdenominatorSwapped]
      ring
    calc
      continueValue -
          (interiorBinaryApproximateResponse error quitValue continueValue *
              quitValue +
            (1 - interiorBinaryApproximateResponse
              error quitValue continueValue) * continueValue) =
          continueValue -
            ((1 - interiorBinaryApproximateResponse
                error continueValue quitValue) * quitValue +
              interiorBinaryApproximateResponse
                error continueValue quitValue * continueValue) := by
            rw [hresponse]
            ring
      _ = (continueValue - quitValue) /
            (1 + Real.exp ((continueValue - quitValue) / error)) := hidentity
      _ ≤ error := nonnegative_gap_logistic_loss_le herror

/-! ## The simultaneous hazard/value map -/

/-- One-stage Bellman payoff written entirely in real hazard coordinates. -/
def quittingHazardBellmanPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : ι → ℝ) (tail : Payoff ι) : Payoff ι :=
  fun who ↦
    hazard who * sigmaValue (weightOfReward reward) hazard who +
      (1 - hazard who) *
        gammaValue (weightOfReward reward) hazard who (tail who)

/-- The real-coordinate Bellman payoff agrees with the product-root
successor payoff whenever the hazards are probabilities. -/
theorem quittingHazardBellmanPayoff_eq_rootSuccessorPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : ι → ℝ) (tail : Payoff ι)
    (hzero : ∀ who, 0 ≤ hazard who) (hone : ∀ who, hazard who ≤ 1) :
    quittingHazardBellmanPayoff reward hazard tail =
      quittingRootSuccessorPayoff reward tail
        (rootOfHazard hazard hzero hone) := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue,
    hazardOfRoot_rootOfHazard]
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (rootOfHazard hazard hzero hone) who
  have hquit : ((rootOfHazard hazard hzero hone) who true).toReal =
      hazard who := by
    change hazardOfRoot (rootOfHazard hazard hzero hone) who = hazard who
    rw [hazardOfRoot_rootOfHazard]
  rw [hquit] at hsum ⊢
  have hcontinue : ((rootOfHazard hazard hzero hone) who false).toReal =
      1 - hazard who := by
    linarith
  rw [hcontinue]
  rfl

/-- The real-coordinate Bellman payoff is jointly continuous in hazards and
the continuation vector. -/
theorem continuous_quittingHazardBellmanPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous fun point : (ι → ℝ) × Payoff ι ↦
      quittingHazardBellmanPayoff reward point.1 point.2 := by
  apply continuous_pi
  intro who
  let hazardMap : (ι → ℝ) × Payoff ι → (ι → ℝ) := fun point ↦ point.1
  have hhazard : Continuous hazardMap := continuous_fst
  have hquit := (continuous_sigmaValue (weightOfReward reward) who).comp hhazard
  have hexcluded :=
    (continuous_excludedValue (weightOfReward reward) who).comp hhazard
  have hcontinueMass := (continuous_continueMassExcl who).comp hhazard
  have htail : Continuous fun point : (ι → ℝ) × Payoff ι ↦ point.2 who :=
    (continuous_apply who).comp continuous_snd
  unfold quittingHazardBellmanPayoff gammaValue
  exact (((continuous_apply who).comp hhazard).mul hquit).add
    ((continuous_const.sub ((continuous_apply who).comp hhazard)).mul
      (hexcluded.add (hcontinueMass.mul htail)))

/-- Ambient finite-dimensional data for one periodic hazard/value word. -/
abbrev QuittingCyclicHazardValuePoint (ι : Type) (period : ℕ) :=
  (Fin period → ι → ℝ) × (Fin period → Payoff ι)

/-- The simultaneous fixed-point box: probability hazards and reward-bounded
phase values. -/
def quittingCyclicHazardValueBox
    (ι : Type) (period : ℕ) (bound : ℝ) :
    Set (QuittingCyclicHazardValuePoint ι period) :=
  Icc ((fun _ _ ↦ (0 : ℝ)), (fun _ _ ↦ -bound))
    ((fun _ _ ↦ (1 : ℝ)), (fun _ _ ↦ bound))

/-- Simultaneous softened response and Bellman update. -/
def quittingCyclicSoftBellmanMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℝ)
    (point : QuittingCyclicHazardValuePoint ι (m + 1)) :
    QuittingCyclicHazardValuePoint ι (m + 1) :=
  (fun phase who ↦
      interiorBinaryApproximateResponse error
        (sigmaValue (weightOfReward reward) (point.1 phase) who)
        (gammaValue (weightOfReward reward) (point.1 phase) who
          (point.2 (finRotate (m + 1) phase) who)),
    fun phase ↦ quittingHazardBellmanPayoff reward (point.1 phase)
      (point.2 (finRotate (m + 1) phase)))

/-- The simultaneous softened response/Bellman update is continuous. -/
theorem continuous_quittingCyclicSoftBellmanMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℝ) :
    Continuous (quittingCyclicSoftBellmanMap (m := m) reward error) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro phase
    apply continuous_pi
    intro who
    let phaseHazard : QuittingCyclicHazardValuePoint ι (m + 1) → ι → ℝ :=
      fun point ↦ point.1 phase
    let nextValue : QuittingCyclicHazardValuePoint ι (m + 1) → ℝ :=
      fun point ↦ point.2 (finRotate (m + 1) phase) who
    have hphaseHazard : Continuous phaseHazard :=
      (continuous_apply phase).comp continuous_fst
    have hnextValue : Continuous nextValue :=
      (continuous_apply who).comp
        ((continuous_apply (finRotate (m + 1) phase)).comp continuous_snd)
    have hquit : Continuous fun point ↦
        sigmaValue (weightOfReward reward) (phaseHazard point) who :=
      (continuous_sigmaValue (weightOfReward reward) who).comp hphaseHazard
    have hcontinue : Continuous fun point ↦
        gammaValue (weightOfReward reward) (phaseHazard point) who
          (nextValue point) := by
      unfold gammaValue
      exact ((continuous_excludedValue (weightOfReward reward) who).comp
        hphaseHazard).add
          (((continuous_continueMassExcl who).comp hphaseHazard).mul hnextValue)
    exact (continuous_interiorBinaryApproximateResponse error).comp
      (hquit.prodMk hcontinue)
  · apply continuous_pi
    intro phase
    let phaseHazard : QuittingCyclicHazardValuePoint ι (m + 1) → ι → ℝ :=
      fun point ↦ point.1 phase
    let nextPayoff : QuittingCyclicHazardValuePoint ι (m + 1) → Payoff ι :=
      fun point ↦ point.2 (finRotate (m + 1) phase)
    have hphaseHazard : Continuous phaseHazard :=
      (continuous_apply phase).comp continuous_fst
    have hnextPayoff : Continuous nextPayoff :=
      (continuous_apply (finRotate (m + 1) phase)).comp continuous_snd
    exact (continuous_quittingHazardBellmanPayoff reward).comp
      (hphaseHazard.prodMk hnextPayoff)

private theorem quittingCyclicSoftBellmanMap_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℝ)
    (point : QuittingCyclicHazardValuePoint ι (m + 1))
    (hpoint : point ∈ quittingCyclicHazardValueBox ι (m + 1)
      (quittingRewardBound reward)) :
    quittingCyclicSoftBellmanMap reward error point ∈
      quittingCyclicHazardValueBox ι (m + 1)
        (quittingRewardBound reward) := by
  let updated := quittingCyclicSoftBellmanMap reward error point
  have hhazardZero : ∀ phase who, 0 ≤ point.1 phase who :=
    fun phase who ↦ hpoint.1.1 phase who
  have hhazardOne : ∀ phase who, point.1 phase who ≤ 1 :=
    fun phase who ↦ hpoint.2.1 phase who
  have htailBound : ∀ phase who,
      |point.2 phase who| ≤ quittingRewardBound reward := by
    intro phase who
    exact abs_le.mpr ⟨hpoint.1.2 phase who, hpoint.2.2 phase who⟩
  change
    ((fun _ _ ↦ (0 : ℝ)),
        (fun _ _ ↦ -quittingRewardBound reward)) ≤ updated ∧
      updated ≤
        ((fun _ _ ↦ (1 : ℝ)),
          (fun _ _ ↦ quittingRewardBound reward))
  constructor
  · constructor
    · intro phase who
      exact (interiorBinaryApproximateResponse_pos _ _ _).le
    · intro phase who
      change -quittingRewardBound reward ≤
        quittingHazardBellmanPayoff reward (point.1 phase)
          (point.2 (finRotate (m + 1) phase)) who
      rw [quittingHazardBellmanPayoff_eq_rootSuccessorPayoff reward
        (point.1 phase) (point.2 (finRotate (m + 1) phase))
        (hhazardZero phase) (hhazardOne phase)]
      exact neg_le_of_abs_le
        (abs_quittingRootExpectedPayoff_le_bound reward
          (point.2 (finRotate (m + 1) phase))
          (rootOfHazard (point.1 phase) (hhazardZero phase)
            (hhazardOne phase)) who
          (abs_reward_le_quittingRewardBound reward)
          (htailBound (finRotate (m + 1) phase)))
  · constructor
    · intro phase who
      exact (interiorBinaryApproximateResponse_lt_one _ _ _).le
    · intro phase who
      change quittingHazardBellmanPayoff reward (point.1 phase)
          (point.2 (finRotate (m + 1) phase)) who ≤
        quittingRewardBound reward
      rw [quittingHazardBellmanPayoff_eq_rootSuccessorPayoff reward
        (point.1 phase) (point.2 (finRotate (m + 1) phase))
        (hhazardZero phase) (hhazardOne phase)]
      exact le_of_abs_le
        (abs_quittingRootExpectedPayoff_le_bound reward
          (point.2 (finRotate (m + 1) phase))
          (rootOfHazard (point.1 phase) (hhazardZero phase)
            (hhazardOne phase)) who
          (abs_reward_le_quittingRewardBound reward)
          (htailBound (finRotate (m + 1) phase)))

/-! ## The cyclic block and its producer -/

/-- Continue payoff minus Quit payoff for one player at one phase of a
cyclic Bellman word. -/
def quittingCyclicEndpointContinueAdvantage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin (m + 1) → ι → PMF Bool)
    (value : Fin (m + 1) → Payoff ι)
    (phase : Fin (m + 1)) (who : ι) : ℝ :=
  quittingRootContinuePayoff reward
      (value (finRotate (m + 1) phase)) (cycle phase) who -
    quittingRootQuitPayoff reward
      (value (finRotate (m + 1) phase)) (cycle phase) who

/-- A finite cyclic word with interior product roots, exact Bellman return,
reward-bounded phase values, and local approximate Nash at every phase. -/
structure InteriorApproximateNashCyclicBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (m : ℕ) (error : ℝ) where
  cycle : Fin (m + 1) → ι → PMF Bool
  value : Fin (m + 1) → Payoff ι
  quitProbability_pos : ∀ phase who, 0 < (cycle phase who true).toReal
  continueProbability_pos : ∀ phase who, 0 < (cycle phase who false).toReal
  value_bound : ∀ phase who, |value phase who| ≤ quittingRewardBound reward
  quitProbability_eq_response : ∀ phase who,
    (cycle phase who true).toReal =
      interiorBinaryApproximateResponse error
        (quittingRootQuitPayoff reward
          (value (finRotate (m + 1) phase)) (cycle phase) who)
        (quittingRootContinuePayoff reward
          (value (finRotate (m + 1) phase)) (cycle phase) who)
  bellman : ∀ phase,
    value phase = quittingRootSuccessorPayoff reward
      (value (finRotate (m + 1) phase)) (cycle phase)
  rootNash : ∀ phase,
    IsεQuittingRootNash reward
      (value (finRotate (m + 1) phase)) error (cycle phase)

/-- The Quit-to-Continue odds in a produced cyclic block are the exponential
of the negative Continue advantage divided by the local error. -/
theorem InteriorApproximateNashCyclicBlock.quitProbability_odds_eq_exp
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (phase : Fin (m + 1)) (who : ι) :
    (block.cycle phase who true).toReal /
        (1 - (block.cycle phase who true).toReal) =
      Real.exp
        (-quittingCyclicEndpointContinueAdvantage reward block.cycle
          block.value phase who / error) := by
  rw [block.quitProbability_eq_response]
  rw [interiorBinaryApproximateResponse_odds]
  unfold quittingCyclicEndpointContinueAdvantage
  congr 2
  ring

/-- For produced cyclic blocks at one fixed phase, a positive uniform
separation between two nonnegative Continue advantages makes the associated
Quit-probability ratio tend to zero as the local error vanishes. -/
theorem tendsto_cyclicBlock_quitProbability_ratio_zero_of_separated_continueAdvantages
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℕ → ℝ) (herrorPos : ∀ index, 0 < error index)
    (herrorZero : Tendsto error atTop (𝓝 0))
    (block : ∀ index, InteriorApproximateNashCyclicBlock
      reward m (error index))
    (phase : Fin (m + 1)) (high low : ι)
    {separation : ℝ} (hseparation : 0 < separation)
    (hlow : ∀ᶠ index in atTop,
      0 ≤ quittingCyclicEndpointContinueAdvantage reward
        (block index).cycle (block index).value phase low)
    (hseparated : ∀ᶠ index in atTop,
      quittingCyclicEndpointContinueAdvantage reward
          (block index).cycle (block index).value phase low + separation ≤
        quittingCyclicEndpointContinueAdvantage reward
          (block index).cycle (block index).value phase high) :
    Tendsto (fun index ↦
      ((block index).cycle phase high true).toReal /
        ((block index).cycle phase low true).toReal) atTop (𝓝 0) := by
  let quitPayoff : ℕ → ι → ℝ := fun index who ↦
    quittingRootQuitPayoff reward
      ((block index).value (finRotate (m + 1) phase))
      ((block index).cycle phase) who
  let continuePayoff : ℕ → ι → ℝ := fun index who ↦
    quittingRootContinuePayoff reward
      ((block index).value (finRotate (m + 1) phase))
      ((block index).cycle phase) who
  have hresponseRatio :=
    tendsto_interiorBinaryApproximateResponse_ratio_zero_of_separated_continueAdvantages
      error (fun index ↦ quitPayoff index high)
      (fun index ↦ continuePayoff index high)
      (fun index ↦ quitPayoff index low)
      (fun index ↦ continuePayoff index low)
      hseparation herrorPos herrorZero
      (by
        filter_upwards [hlow] with index hlowIndex
        simpa [quittingCyclicEndpointContinueAdvantage, quitPayoff,
          continuePayoff] using hlowIndex)
      (by
        filter_upwards [hseparated] with index hseparatedIndex
        simpa [quittingCyclicEndpointContinueAdvantage, quitPayoff,
          continuePayoff] using hseparatedIndex)
  apply hresponseRatio.congr'
  exact Eventually.of_forall fun index ↦ by
    change interiorBinaryApproximateResponse (error index)
          (quitPayoff index high) (continuePayoff index high) /
        interiorBinaryApproximateResponse (error index)
          (quitPayoff index low) (continuePayoff index low) =
      ((block index).cycle phase high true).toReal /
        ((block index).cycle phase low true).toReal
    rw [(block index).quitProbability_eq_response phase high,
      (block index).quitProbability_eq_response phase low]

/-- Brouwer produces an interior approximate-Nash cyclic Bellman block for
every positive local error and every positive finite period `m + 1`. -/
theorem nonempty_interiorApproximateNashCyclicBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℝ) (herror : 0 < error) :
    Nonempty (InteriorApproximateNashCyclicBlock reward m error) := by
  let bound := quittingRewardBound reward
  let box := quittingCyclicHazardValueBox ι (m + 1) bound
  have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
  have hboxConvex : Convex ℝ box := convex_Icc _ _
  have hboxCompact : IsCompact box := isCompact_Icc
  have hboxNonempty : box.Nonempty := by
    refine ⟨((fun _ _ ↦ (0 : ℝ)), (fun _ _ ↦ (0 : ℝ))), ?_⟩
    change
      ((fun _ _ ↦ (0 : ℝ)), (fun _ _ ↦ -bound)) ≤
          ((fun _ _ ↦ (0 : ℝ)), (fun _ _ ↦ (0 : ℝ))) ∧
        ((fun _ _ ↦ (0 : ℝ)), (fun _ _ ↦ (0 : ℝ))) ≤
          ((fun _ _ ↦ (1 : ℝ)), (fun _ _ ↦ bound))
    exact ⟨⟨fun _ _ ↦ le_rfl, fun _ _ ↦ neg_nonpos.mpr hbound⟩,
      ⟨fun _ _ ↦ zero_le_one, fun _ _ ↦ hbound⟩⟩
  let selfMap : box → box := fun point ↦
    ⟨quittingCyclicSoftBellmanMap reward error point.1,
      quittingCyclicSoftBellmanMap_mem_box reward error point.1 point.2⟩
  have hselfMap : Continuous selfMap := by
    apply continuous_induced_rng.2
    exact (continuous_quittingCyclicSoftBellmanMap reward error).comp
      continuous_subtype_val
  obtain ⟨point, hfixed⟩ :=
    brouwer_fixed_point box hboxConvex hboxCompact hboxNonempty
      ⟨selfMap, hselfMap⟩
  have hmap : quittingCyclicSoftBellmanMap reward error point.1 = point.1 :=
    congrArg Subtype.val hfixed
  let hazard := point.1.1
  let value := point.1.2
  have hhazardZero : ∀ phase who, 0 ≤ hazard phase who :=
    fun phase who ↦ point.2.1.1 phase who
  have hhazardOne : ∀ phase who, hazard phase who ≤ 1 :=
    fun phase who ↦ point.2.2.1 phase who
  let cycle : Fin (m + 1) → ι → PMF Bool :=
    fun phase ↦ rootOfHazard (hazard phase)
      (hhazardZero phase) (hhazardOne phase)
  have hresponse : ∀ phase who,
      interiorBinaryApproximateResponse error
          (sigmaValue (weightOfReward reward) (hazard phase) who)
          (gammaValue (weightOfReward reward) (hazard phase) who
            (value (finRotate (m + 1) phase) who)) =
        hazard phase who := by
    intro phase who
    exact congrFun (congrFun (congrArg Prod.fst hmap) phase) who
  have hbellman : ∀ phase,
      quittingHazardBellmanPayoff reward (hazard phase)
          (value (finRotate (m + 1) phase)) = value phase := by
    intro phase
    exact congrFun (congrArg Prod.snd hmap) phase
  refine ⟨{
    cycle := cycle
    value := value
    quitProbability_pos := ?_
    continueProbability_pos := ?_
    value_bound := ?_
    quitProbability_eq_response := ?_
    bellman := ?_
    rootNash := ?_ }⟩
  · intro phase who
    change 0 < hazardOfRoot
      (rootOfHazard (hazard phase) (hhazardZero phase)
        (hhazardOne phase)) who
    rw [hazardOfRoot_rootOfHazard]
    rw [← hresponse phase who]
    exact interiorBinaryApproximateResponse_pos _ _ _
  · intro phase who
    have hlt : hazard phase who < 1 := by
      rw [← hresponse phase who]
      exact interiorBinaryApproximateResponse_lt_one _ _ _
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (cycle phase) who
    have hquit : ((cycle phase) who true).toReal = hazard phase who := by
      change hazardOfRoot (rootOfHazard (hazard phase)
        (hhazardZero phase) (hhazardOne phase)) who = hazard phase who
      rw [hazardOfRoot_rootOfHazard]
    rw [hquit] at hsum
    linarith
  · intro phase who
    exact abs_le.mpr ⟨point.2.1.2 phase who, point.2.2.2 phase who⟩
  · intro phase who
    change hazardOfRoot
        (rootOfHazard (hazard phase) (hhazardZero phase)
          (hhazardOne phase)) who =
      interiorBinaryApproximateResponse error
        (quittingRootQuitPayoff reward
          (value (finRotate (m + 1) phase)) (cycle phase) who)
        (quittingRootContinuePayoff reward
          (value (finRotate (m + 1) phase)) (cycle phase) who)
    rw [hazardOfRoot_rootOfHazard,
      quittingRootQuitPayoff_eq_sigmaValue,
      quittingRootContinuePayoff_eq_gammaValue,
      hazardOfRoot_rootOfHazard]
    exact (hresponse phase who).symm
  · intro phase
    rw [← hbellman phase]
    exact quittingHazardBellmanPayoff_eq_rootSuccessorPayoff reward
      (hazard phase) (value (finRotate (m + 1) phase))
      (hhazardZero phase) (hhazardOne phase)
  · intro phase
    apply (isεQuittingRootNash_iff_coordinateNashDefect_le
      reward (value (finRotate (m + 1) phase)) error (cycle phase)).2
    intro who
    have hdefect := binaryEndpointDefect_interiorBinaryApproximateResponse_le
      herror
      (sigmaValue (weightOfReward reward) (hazard phase) who)
      (gammaValue (weightOfReward reward) (hazard phase) who
        (value (finRotate (m + 1) phase) who))
    rw [hresponse phase who] at hdefect
    unfold quittingRootCoordinateNashDefect
    rw [quittingRootQuitPayoff_eq_sigmaValue,
      quittingRootContinuePayoff_eq_gammaValue,
      hazardOfRoot_rootOfHazard,
      ← quittingHazardBellmanPayoff_eq_rootSuccessorPayoff reward
        (hazard phase) (value (finRotate (m + 1) phase))
        (hhazardZero phase) (hhazardOne phase)]
    exact hdefect

end GameTheory
