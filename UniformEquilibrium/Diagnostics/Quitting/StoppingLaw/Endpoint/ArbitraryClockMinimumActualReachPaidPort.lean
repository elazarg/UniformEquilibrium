import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualReachPaidFirstDisagreement
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ArbitraryClockMinimumPurification
import UniformEquilibrium.Diagnostics.Quitting.PureTimeMinimumPaidPort

/-!
# Off-minimum actual-reach paid port from an arbitrary-clock minimum source

The supplied source is one actual realizing sequence for a positive global
minimum of terminal semantic debt.  The conclusion retains one literal
finite replacement ancestry from that sequence and a source-supported paid
first-disagreement row.  It is not a chronology or a downstream consumer.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal quantitative output at one descendant strictly above a supplied
positive global minimum. -/
structure QuittingOffMinimumActualReachPaidPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (original : ℕ → (quittingGame reward).BehaviorProfile)
    (minimumDebt M : ℝ) where
  sourceIndex : ℕ
  target : (quittingGame reward).BehaviorProfile
  ancestry : IsQuittingBehaviorReplacementAncestry
    (original sourceIndex) target
  offMinimum : minimumDebt < quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward target)
  observer : ι
  observerDebtFloor : minimumDebt / Fintype.card ι ≤
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward target) observer
  row : QuittingPaidFirstDisagreementRow reward target observer
    ((minimumDebt / Fintype.card ι) / 4)
  paidGainFloor : minimumDebt / (4 * Fintype.card ι) ≤
    row.liveMass * row.reachedGain
  sourceSupport : row.sourceWitness ∈
    (quittingBehaviorStoppingLaw reward (target observer)).support
  ownSurvivalFloor : minimumDebt / Fintype.card ι ≤
    4 * M * quittingHazardSurvival
      (quittingBehaviorLiveHazard reward (target observer)) row.start
  opponentLiveFloor : minimumDebt / Fintype.card ι ≤
    8 * M * row.liveMass
  jointReachFloor :
    (minimumDebt / Fintype.card ι) *
        (minimumDebt / Fintype.card ι) ≤
      32 * M * M *
        quittingSurvivalPrefix
          (quittingProfileLiveRoot reward target) row.start

/-- One literal off-minimum unilateral-replacement descendant carries the
fixed debt, paid-gain, source-support, and actual-reach passport. -/
theorem replacementAncestry_exists_offMinimumActualReachPaidPort
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (original : ℕ → (quittingGame reward).BehaviorProfile)
    (minimumDebt M : ℝ) (hminimumPositive : 0 < minimumDebt)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (sourceIndex : ℕ)
    (target : (quittingGame reward).BehaviorProfile)
    (hancestry : IsQuittingBehaviorReplacementAncestry
      (original sourceIndex) target)
    (hoff : minimumDebt < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward target)) :
    ∃ port : QuittingOffMinimumActualReachPaidPort
        reward original minimumDebt M,
      port.sourceIndex = sourceIndex ∧ port.target = target := by
  let pair := quittingTerminalSemanticPair reward target
  have htargetPositive : 0 < quittingTerminalSemanticDebtSum pair :=
    hminimumPositive.trans (by simpa only [pair] using hoff)
  obtain ⟨observer, haverage⟩ :=
    exists_quittingTerminalSemanticDebt_ge_average pair htargetPositive
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hminimumAverage : minimumDebt / Fintype.card ι <
      quittingTerminalSemanticDebtSum pair / Fintype.card ι :=
    div_lt_div_of_pos_right (by simpa only [pair] using hoff) hcard
  have hdebt : minimumDebt / Fintype.card ι ≤
      quittingTerminalSemanticDebt pair observer :=
    hminimumAverage.le.trans haverage
  have hdebtLiteral : minimumDebt / Fintype.card ι ≤
      quittingContinuationBestResponseValue reward target observer -
        quittingTerminalPayoff reward target observer := by
    simpa only [pair, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair] using hdebt
  have hdeltaPositive : 0 < minimumDebt / Fintype.card ι :=
    div_pos hminimumPositive hcard
  obtain ⟨row, hsupport, hown, hlive, hjoint⟩ :=
    positiveDebt_exists_actualJointReach_paidRow_mem_support
      reward target observer M (minimumDebt / Fintype.card ι)
        hreward hdeltaPositive hdebtLiteral
  have hgainNormalization : minimumDebt / (4 * Fintype.card ι) =
      minimumDebt / Fintype.card ι / 4 := by
    rw [div_div]
    congr 1
    ring
  refine ⟨{
    sourceIndex := sourceIndex
    target := target
    ancestry := hancestry
    offMinimum := hoff
    observer := observer
    observerDebtFloor := by simpa only [pair] using hdebt
    row := row
    paidGainFloor := by
      rw [hgainNormalization]
      exact row.gain_le_paid
    sourceSupport := hsupport
    ownSurvivalFloor := hown
    opponentLiveFloor := hlive
    jointReachFloor := hjoint }, rfl, rfl⟩

/-- A supplied actual sequence realizing a positive global debt minimum has a
literal off-minimum descendant with the fixed debt, paid-gain, and actual
reach passport. -/
theorem minimumRealizingSequence_exists_offMinimumActualReachPaidPort
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hprofiles : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (𝓝 minimum))
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (QuittingOffMinimumActualReachPaidPort reward profiles
      (quittingTerminalSemanticDebtSum minimum) M) := by
  have hdebt : Tendsto
      (fun n => quittingTerminalDebtSum reward (profiles n)) atTop
      (𝓝 (quittingTerminalSemanticDebtSum minimum)) := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        hprofiles
    change Tendsto
      (fun n => quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n))) atTop
      (𝓝 (quittingTerminalSemanticDebtSum minimum))
    simpa only [Function.comp_def] using hcontinuous
  rcases minimumRealizingSequence_purify_or_offMinimum reward
      (quittingTerminalSemanticDebtSum minimum) hminimum profiles hdebt with
    ⟨sourceIndex, times, hancestry, hpureMinimum⟩ |
      ⟨sourceIndex, target, hancestry, hoff⟩
  · obtain ⟨targetTimes, hpureAncestry, observer, response, hoff,
        _hcap, _haverage, _hstrict, _row, _hsource, _hreceiving⟩ :=
      pureTimeMinimum_exists_offMinimumPaidPort reward
        (quittingTerminalSemanticDebtSum minimum) hminimum hpositive
          times hpureMinimum
    let target := quittingPureTimeProfileBehavior reward targetTimes
    have hbehaviorAncestry : IsQuittingBehaviorReplacementAncestry
        (profiles sourceIndex) target :=
      hancestry.trans
        (isQuittingBehaviorReplacementAncestry_pureTimeProfileBehavior
          hpureAncestry)
    obtain ⟨port, _, _⟩ :=
      replacementAncestry_exists_offMinimumActualReachPaidPort reward profiles
      (quittingTerminalSemanticDebtSum minimum) M hpositive hreward
      sourceIndex target hbehaviorAncestry (by simpa only [target] using hoff)
    exact ⟨port⟩
  · obtain ⟨port, _, _⟩ :=
      replacementAncestry_exists_offMinimumActualReachPaidPort reward profiles
      (quittingTerminalSemanticDebtSum minimum) M hpositive hreward
      sourceIndex target hancestry hoff
    exact ⟨port⟩

/-- Direct actual-source adapter: compactness supplies a global minimizer and
an exact realizing sequence; positivity of that selected minimum is the only
additional branch premise. -/
theorem exists_minimumRealizingSequence_offMinimumActualReachPaidPort
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ minimum ∈ quittingTerminalSemanticCarrier reward,
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) →
      0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ (minimum : QuittingTerminalSemanticPair ι)
        (profiles : ℕ → (quittingGame reward).BehaviorProfile),
      minimum ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (𝓝 minimum) ∧
      Nonempty (QuittingOffMinimumActualReachPaidPort reward profiles
        (quittingTerminalSemanticDebtSum minimum) M) := by
  obtain ⟨minimum, profiles, hminimumMem, hminimum, hprofiles, _hdebt,
      _hexploit⟩ :=
    exists_profile_sequence_tendsto_minimumTerminalSemanticDebt reward
  refine ⟨minimum, profiles, hminimumMem, hminimum, hprofiles, ?_⟩
  exact minimumRealizingSequence_exists_offMinimumActualReachPaidPort
    reward minimum hminimum
      (hpositive minimum hminimumMem hminimum) profiles hprofiles M hreward

/-- Positive global terminal-debt infimum directly selects a compact minimum,
one retained realizing sequence, and its off-minimum actual-reach paid port. -/
theorem exists_minimumRealizingSequence_offMinimumActualReachPaidPort_of_debtSumInf_pos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward) :
    ∃ (minimum : QuittingTerminalSemanticPair ι)
        (profiles : ℕ → (quittingGame reward).BehaviorProfile),
      minimum ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      quittingTerminalSemanticDebtSum minimum =
        quittingTerminalDebtSumInf reward ∧
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (𝓝 minimum) ∧
      Nonempty (QuittingOffMinimumActualReachPaidPort reward profiles
        (quittingTerminalDebtSumInf reward) M) := by
  obtain ⟨minimum, profiles, hminimumMem, hminimum, hprofiles, _hdebt,
      _hexploit⟩ :=
    exists_profile_sequence_tendsto_minimumTerminalSemanticDebt reward
  have hminimumValue : quittingTerminalSemanticDebtSum minimum =
      quittingTerminalDebtSumInf reward :=
    (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      minimum hminimumMem hminimum).symm
  have hport := minimumRealizingSequence_exists_offMinimumActualReachPaidPort
    reward minimum hminimum (hminimumValue ▸ hinf) profiles hprofiles M hreward
  exact ⟨minimum, profiles, hminimumMem, hminimum, hminimumValue, hprofiles,
    by simpa only [hminimumValue] using hport⟩

end GameTheory
