import UniformEquilibrium.Quitting.Paths.CommonCalendarTesterPool
import MathUE.Analysis.CompactMinimumEnvelope

/-! # Internally attained smoothing minima with their own actual tester weights -/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingCommonCalendarSmoothMaximum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (temperature : ℝ)
    (point : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) : ℝ :=
  Math.FiniteLogSumExp.smoothMax temperature
    (quittingCommonCalendarTesterGain reward deadline pool point)

/-- The weights are computed from this SAME actual profile's gains. -/
def quittingCommonCalendarTesterWeights
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (temperature : ℝ)
    (point : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    QuittingCommonCalendarTester ι pool → ℝ :=
  Math.FiniteLogSumExp.weight temperature
    (quittingCommonCalendarTesterGain reward deadline pool point)

theorem quittingCommonCalendarPartition_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (temperature : ℝ)
    (point : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    0 < Math.FiniteLogSumExp.partition temperature
      (quittingCommonCalendarTesterGain reward deadline pool point) :=
  Math.FiniteLogSumExp.partition_pos temperature _

theorem quittingCommonCalendarTesterWeights_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (temperature : ℝ)
    (point : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (tester : QuittingCommonCalendarTester ι pool) :
    0 < quittingCommonCalendarTesterWeights reward deadline pool temperature point tester :=
  Math.FiniteLogSumExp.weight_pos temperature _ tester

theorem sum_quittingCommonCalendarTesterWeights
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (temperature : ℝ)
    (point : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    (∑ tester, quittingCommonCalendarTesterWeights
      reward deadline pool temperature point tester) = 1 :=
  Math.FiniteLogSumExp.sum_weight temperature _

theorem continuous_quittingCommonCalendarSmoothMaximum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (temperature : ℝ) :
    Continuous (fun point : MixedSimplex ι
        (fun _ => QuittingFiniteDeadlineTimingAction deadline) =>
      quittingCommonCalendarSmoothMaximum reward deadline pool temperature point) := by
  have hpartition : Continuous (fun point : MixedSimplex ι
      (fun _ => QuittingFiniteDeadlineTimingAction deadline) =>
      Math.FiniteLogSumExp.partition temperature
        (quittingCommonCalendarTesterGain reward deadline pool point)) := by
    unfold Math.FiniteLogSumExp.partition
    exact continuous_finsetSum _ fun tester _ =>
      Real.continuous_exp.comp
        ((continuous_quittingCommonCalendarTesterGain reward deadline pool tester).div_const
          temperature)
  exact continuous_const.mul
    (hpartition.log (fun point =>
      (quittingCommonCalendarPartition_pos reward deadline pool temperature point).ne'))

/-- The actual compact minimum value, using the canonical minimum-envelope owner. -/
def quittingCommonCalendarSmoothMinimumValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (temperature : ℝ) : ℝ :=
  Math.CompactMinimumEnvelope.minimum
    (fun parameter (point : MixedSimplex ι
        (fun _ => QuittingFiniteDeadlineTimingAction deadline)) =>
      quittingCommonCalendarSmoothMaximum reward deadline pool parameter point) temperature

/-- Compactness selects an actual independent simplex point; no minimizing profile is an input. -/
theorem exists_quittingCommonCalendarSmoothMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (temperature : ℝ) :
    ∃ point : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline),
      quittingCommonCalendarSmoothMaximum reward deadline pool temperature point =
        quittingCommonCalendarSmoothMinimumValue reward deadline pool temperature ∧
      IsMinOn (quittingCommonCalendarSmoothMaximum reward deadline pool temperature)
        Set.univ point := by
  let : Nonempty (MixedSimplex ι
      (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :=
    ⟨fun _ => Math.ProbabilityMassFunction.stdSimplexEquiv (PMF.pure none)⟩
  exact Math.CompactMinimumEnvelope.exists_minimizer
    (fun parameter point => quittingCommonCalendarSmoothMaximum
      reward deadline pool parameter point) temperature
    (continuous_quittingCommonCalendarSmoothMaximum reward deadline pool temperature)

variable [Nonempty ι]

/-- The finite smooth objective sandwiches the actual unrestricted behavioral exploitability. -/
theorem quittingCommonCalendarSmoothMaximum_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (hpool : deadline ≤ pool) {temperature : ℝ} (htemperature : 0 < temperature)
    (point : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    quittingTerminalExploitability reward
        (quittingStoppingLawProfile reward (quittingFiniteCalendarDecodedLaws point)) ≤
      quittingCommonCalendarSmoothMaximum reward deadline pool temperature point ∧
    quittingCommonCalendarSmoothMaximum reward deadline pool temperature point ≤
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (quittingFiniteCalendarDecodedLaws point)) +
        temperature * Real.log (Fintype.card (QuittingCommonCalendarTester ι pool) : ℝ) := by
  have hmaximum := maximum_quittingCommonCalendarTesterGain_eq_exploitability
    reward deadline pool hpool point
  constructor
  · rw [← hmaximum]
    exact Math.FiniteLogSumExp.maximum_le_smoothMax htemperature _
  · rw [← hmaximum]
    exact Math.FiniteLogSumExp.smoothMax_le_maximum_add_log_card htemperature _

theorem quittingCommonCalendarWeightedInactivity_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline pool : ℕ)
    (hpool : deadline ≤ pool) {temperature : ℝ} (htemperature : 0 < temperature)
    (point : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    ∑ tester, quittingCommonCalendarTesterWeights reward deadline pool temperature point tester *
        (quittingTerminalExploitability reward
            (quittingStoppingLawProfile reward (quittingFiniteCalendarDecodedLaws point)) -
          quittingCommonCalendarTesterGain reward deadline pool point tester) ≤
      temperature * Real.log (Fintype.card (QuittingCommonCalendarTester ι pool) : ℝ) := by
  rw [← maximum_quittingCommonCalendarTesterGain_eq_exploitability
    reward deadline pool hpool point]
  exact Math.FiniteLogSumExp.inactivity_le_temperature_log_card htemperature _

/-- Source window facade: construct the literal common pool endpoint `2 * clock + 1`
internally, then select ONE actual minimizing point together with its OWN weights.
Native profile dates remain zero through deadline-1; Never stays a separate tester.
This produces no tilted parameter, pressure sign or enlarged-calendar competitor estimate. -/
theorem exists_quittingCommonWindowSmoothMinimum_with_weights
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (clock : ℕ)
    {deadline : ℕ} (hdeadline : deadline ≤ 2 * clock)
    {temperature : ℝ} (htemperature : 0 < temperature) :
    ∃ (point : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
      (weights : QuittingCommonCalendarTester ι (2 * clock + 1) → ℝ),
      weights = quittingCommonCalendarTesterWeights reward deadline (2 * clock + 1)
        temperature point ∧
      IsMinOn (quittingCommonCalendarSmoothMaximum reward deadline (2 * clock + 1)
        temperature) Set.univ point ∧
      quittingCommonCalendarSmoothMaximum reward deadline (2 * clock + 1) temperature point =
        quittingCommonCalendarSmoothMinimumValue reward deadline (2 * clock + 1) temperature ∧
      (∀ tester, 0 < weights tester) ∧
      (∑ tester, weights tester) = 1 ∧
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (quittingFiniteCalendarDecodedLaws point)) ≤
        quittingCommonCalendarSmoothMaximum reward deadline (2 * clock + 1) temperature point ∧
      quittingCommonCalendarSmoothMaximum reward deadline (2 * clock + 1) temperature point ≤
        quittingTerminalExploitability reward
            (quittingStoppingLawProfile reward (quittingFiniteCalendarDecodedLaws point)) +
          temperature *
            Real.log (Fintype.card (QuittingCommonCalendarTester ι (2 * clock + 1)) : ℝ) ∧
      (∑ tester, weights tester *
        (quittingTerminalExploitability reward
            (quittingStoppingLawProfile reward (quittingFiniteCalendarDecodedLaws point)) -
          quittingCommonCalendarTesterGain reward deadline (2 * clock + 1) point tester)) ≤
        temperature *
          Real.log (Fintype.card (QuittingCommonCalendarTester ι (2 * clock + 1)) : ℝ) := by
  have hpool : deadline ≤ 2 * clock + 1 := hdeadline.trans (Nat.le_succ _)
  obtain ⟨point, hvalue, hpoint⟩ :=
    exists_quittingCommonCalendarSmoothMinimum reward deadline (2 * clock + 1) temperature
  obtain ⟨hlower, hupper⟩ := quittingCommonCalendarSmoothMaximum_bounds
    reward deadline (2 * clock + 1) hpool htemperature point
  exact ⟨point, quittingCommonCalendarTesterWeights reward deadline (2 * clock + 1)
      temperature point, rfl, hpoint, hvalue,
    quittingCommonCalendarTesterWeights_pos reward deadline (2 * clock + 1) temperature point,
    sum_quittingCommonCalendarTesterWeights reward deadline (2 * clock + 1) temperature point,
    hlower, hupper, quittingCommonCalendarWeightedInactivity_le
      reward deadline (2 * clock + 1) hpool htemperature point⟩

end GameTheory
