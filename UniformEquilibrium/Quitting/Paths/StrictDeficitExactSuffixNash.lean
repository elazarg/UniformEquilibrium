import UniformEquilibrium.Quitting.Cycles.PeriodicFiniteReplyPrefix
import UniformEquilibrium.Quitting.Paths.ReversePrefixStoppingLaw
import UniformEquilibrium.Quitting.Paths.StrictDeficitExactSuffixDiagonal
import UniformEquilibrium.Quitting.Punishment.FinitePureReplyValue

/-! # Literal response transport for strict-deficit reverse prefixes -/

noncomputable section

namespace GameTheory

open Filter _root_.Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The checked exact-word recursion is literally a reverse prefix of its
selected roots; fixed suffixes therefore come from one producer. -/
theorem quittingStrictDeficitExactWords_eq_reversePrefixRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (depth : ℕ) :
    quittingStrictDeficitExactWords reward gap depth =
      quittingReversePrefixRootStack
        (quittingStrictDeficitExactWordNextRoot reward gap) depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [quittingStrictDeficitExactWords_succ,
        quittingReversePrefixRootStack_succ, ← ih]
      rfl

/-- At each date inside the finite word, the actual live root is the same
reverse-selected root used in the compactness construction. -/
theorem quittingProfileLiveRoot_strictDeficitExactWord_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (depth time : ℕ) (htime : time < depth) :
    quittingProfileLiveRoot reward
        (quittingLiteralRootStackProfile reward
          (quittingStrictDeficitExactWords reward gap depth)
          (quittingAlwaysContinueProfile reward)) time =
      quittingStrictDeficitExactWordNextRoot reward gap
        (depth - time - 1) := by
  rw [quittingStrictDeficitExactWords_eq_reversePrefixRootStack]
  exact quittingProfileLiveRoot_reversePrefixProfile_eq reward
    (quittingStrictDeficitExactWordNextRoot reward gap)
    (fun _ => quittingAlwaysContinueProfile reward) depth time htime

/-- At a common selected depth, the row seen at literal suffix `suffix` and
date `time` is a root from the same reverse-prefix exact word. -/
def quittingStrictDeficitLiteralSuffixRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (centers : ℕ → ℕ) (rank suffix time : ℕ) : ι → PMF Bool :=
  quittingStrictDeficitExactWordNextRoot reward gap
    (centers rank - (suffix + time))

/-- Every fixed pure finite response payoff of the *actual* selected word
converges to that response against the corresponding infinite literal suffix.
The same `centers` witnesses every suffix; no cap-continuity assertion is used. -/
theorem tendsto_strictDeficitExactWord_literalSuffix_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (centers : ℕ → ℕ) (hcenters : StrictMono centers)
    (roots : ℕ → ι → PMF Bool)
    (hrows : ∀ time, Tendsto
      (fun rank => quittingSimplexOfRoot
        (quittingStrictDeficitExactWordNextRoot reward gap
          (centers rank - time))) atTop
      (nhds (quittingSimplexOfRoot (roots time))))
    (suffix : ℕ) (who : ι) (date : ℕ) :
    Tendsto (fun rank => quittingTerminalPayoff reward
      (Function.update
        (quittingLiteralRootStackProfile reward
          (quittingStrictDeficitExactWords reward gap
            (centers rank + 1 - suffix))
          (quittingAlwaysContinueProfile reward)) who
        (quittingPureTimeBehaviorStrategy reward who (some date))) who)
      atTop
      (nhds (quittingRootSequencePureTimeTerminalValue reward
        (fun time => roots (suffix + time)) who (some date) 0)) := by
  have hselected := tendsto_quittingPureTimeTerminalValue_some_of_simplexRows
    reward
    (fun rank time =>
      quittingStrictDeficitLiteralSuffixRows reward gap centers rank suffix time)
    (fun time => roots (suffix + time)) who date
    (fun time => by
      simpa only [quittingStrictDeficitLiteralSuffixRows] using
        hrows (suffix + time))
  apply hselected.congr'
  filter_upwards [hcenters.tendsto_atTop.eventually
    (eventually_ge_atTop (suffix + date))] with rank hlarge
  let depth := centers rank + 1 - suffix
  have hroot : ∀ time ≤ date,
      quittingProfileLiveRoot reward
          (quittingLiteralRootStackProfile reward
            (quittingStrictDeficitExactWords reward gap depth)
            (quittingAlwaysContinueProfile reward)) time =
        quittingStrictDeficitLiteralSuffixRows reward gap centers
          rank suffix time := by
    intro time htime
    rw [quittingProfileLiveRoot_strictDeficitExactWord_eq
      reward gap depth time (by dsimp [depth]; omega)]
    unfold quittingStrictDeficitLiteralSuffixRows depth
    congr 1
    omega
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  exact quittingRootSequencePureTimeTerminalValue_some_congr reward
    _ _ who date (fun time htime => (hroot time htime).symm)

/-- Every actual behavioral response is bounded by prescribed terminal payoff
plus the complete semantic debt. No cap is assumed to be attained. -/
theorem quittingTerminalPayoff_update_le_add_semanticDebtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward (Function.update profile who deviation) who ≤
      quittingTerminalPayoff reward profile who +
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) := by
  have hcap : quittingTerminalPayoff reward
      (Function.update profile who deviation) who ≤
        quittingContinuationBestResponseValue reward profile who :=
    le_csSup (bddAbove_range_quittingTerminalPayoff_update reward profile who)
      ⟨deviation, rfl⟩
  have hdebt : quittingTerminalDeviationDebt reward profile who ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun other _ => quittingTerminalDeviationDebt_nonneg reward profile other)
      (Finset.mem_univ who)
  unfold quittingTerminalDeviationDebt at hdebt
  linarith

/-- Vanishing complete debt and literal fixed-date continuity bound every
finite pure response at every limit suffix by that suffix's prescribed value. -/
theorem quittingStrictDeficitExactSuffix_finitePureTime_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S who, |reward S who| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (centers : ℕ → ℕ) (hcenters : StrictMono centers)
    (hrows : ∀ time, Tendsto
      (fun rank => quittingSimplexOfRoot
        (quittingStrictDeficitExactWordNextRoot reward gap
          (centers rank - time))) atTop
      (nhds (quittingSimplexOfRoot (roots time))))
    (hvalues : ∀ time, Tendsto
      (fun rank => quittingStrictDeficitExactWordValue reward gap
        (centers rank + 1 - time)) atTop (nhds (value time)))
    (hterminal : ∀ time, value time =
      fun who => quittingRootSequenceTerminalValue reward roots who time)
    (suffix : ℕ) (who : ι) (date : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward
        (fun time => roots (suffix + time)) who (some date) 0 ≤
      quittingRootSequenceTerminalValue reward roots who suffix := by
  have hpure := tendsto_strictDeficitExactWord_literalSuffix_pureTime
    reward gap centers hcenters roots hrows suffix who date
  have hvalue : Tendsto (fun rank =>
      quittingStrictDeficitExactWordValue reward gap
        (centers rank + 1 - suffix) who) atTop (nhds (value suffix who)) :=
    ((continuous_apply who).tendsto (value suffix)).comp (hvalues suffix)
  have hdebt := tendsto_strictDeficitExactWordDebt_literalSuffix
    reward hgap hreward hdeficit centers hcenters suffix
  have hbound (rank : ℕ) : quittingTerminalPayoff reward
      (Function.update
        (quittingLiteralRootStackProfile reward
          (quittingStrictDeficitExactWords reward gap
            (centers rank + 1 - suffix))
          (quittingAlwaysContinueProfile reward)) who
        (quittingPureTimeBehaviorStrategy reward who (some date))) who ≤
      quittingStrictDeficitExactWordValue reward gap
        (centers rank + 1 - suffix) who +
      quittingStrictDeficitExactWordDebt reward gap
        (centers rank + 1 - suffix) := by
    exact quittingTerminalPayoff_update_le_add_semanticDebtSum reward
      (quittingLiteralRootStackProfile reward
        (quittingStrictDeficitExactWords reward gap
          (centers rank + 1 - suffix))
        (quittingAlwaysContinueProfile reward)) who
      (quittingPureTimeBehaviorStrategy reward who (some date))
  have hlim := le_of_tendsto_of_tendsto' hpure (hvalue.add hdebt) hbound
  have hcoordinate := congrFun (hterminal suffix) who
  simpa only [add_zero, hcoordinate] using hlim

/-- The same reverse-prefix limit is exact terminal Nash at *every* literal
suffix. Nonnegative singleton rewards let the checked late-finite-response
theorem dominate Never; pure-time extremality then covers all behaviors. -/
theorem quittingStrictDeficitExactSuffix_isZeroAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S who, |reward S who| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap)
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (centers : ℕ → ℕ) (hcenters : StrictMono centers)
    (hrows : ∀ time, Tendsto
      (fun rank => quittingSimplexOfRoot
        (quittingStrictDeficitExactWordNextRoot reward gap
          (centers rank - time))) atTop
      (nhds (quittingSimplexOfRoot (roots time))))
    (hvalues : ∀ time, Tendsto
      (fun rank => quittingStrictDeficitExactWordValue reward gap
        (centers rank + 1 - time)) atTop (nhds (value time)))
    (hterminal : ∀ time, value time =
      fun who => quittingRootSequenceTerminalValue reward roots who time)
    (suffix : ℕ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingRootSequenceProfile reward roots suffix) := by
  let profile := quittingRootSequenceProfile reward roots suffix
  have hcap (who : ι) :
      quittingContinuationBestResponseValue reward profile who ≤
        quittingTerminalPayoff reward profile who := by
    rw [quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg
      reward profile who (hsolo who)]
    unfold quittingFinitePureReplyValue
    apply ciSup_le
    intro date
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    have hroot : quittingProfileLiveRoot reward profile =
        fun time => roots (suffix + time) := by
      funext time player
      rfl
    rw [hroot]
    exact quittingStrictDeficitExactSuffix_finitePureTime_le
      reward hgap hreward hdeficit roots value centers hcenters
      hrows hvalues hterminal suffix who date
  intro who deviation
  have hresponse : quittingTerminalPayoff reward
      (Function.update profile who deviation) who ≤
        quittingContinuationBestResponseValue reward profile who :=
    le_csSup (bddAbove_range_quittingTerminalPayoff_update reward profile who)
      ⟨deviation, rfl⟩
  dsimp only [profile] at hresponse ⊢
  linarith [hcap who]

/-- Strict finite-word payoff deficit and nonnegative singleton rewards yield
one actual infinite reverse-prefix limit. Its *same* rows are exact terminal
Nash at every suffix, and its initial terminal payoff is uniform. -/
theorem exists_strictDeficitExactSuffix_allTerminalNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S who, |reward S who| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap)
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who) :
    ∃ (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
      (centers : ℕ → ℕ),
      StrictMono centers ∧
      (∀ time, Tendsto
        (fun rank => quittingSimplexOfRoot
          (quittingStrictDeficitExactWordNextRoot reward gap
            (centers rank - time))) atTop
        (nhds (quittingSimplexOfRoot (roots time)))) ∧
      (∀ time, Tendsto
        (fun rank => quittingStrictDeficitExactWordValue reward gap
          (centers rank + 1 - time)) atTop (nhds (value time))) ∧
      (∀ time, value time =
        fun who => quittingRootSequenceTerminalValue reward roots who time) ∧
      (∀ suffix, (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingRootSequenceProfile reward roots suffix)) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) := by
  obtain ⟨roots, value, centers, hcenters, hrows, hvalues, _, _, hterminal⟩ :=
    exists_strictDeficitExactSuffix_payoffDiagonal
      reward hgap hreward hdeficit
  have hnash : ∀ suffix, (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingRootSequenceProfile reward roots suffix) := by
    intro suffix
    exact quittingStrictDeficitExactSuffix_isZeroAsymptoticNash
      reward hgap hreward hdeficit hsolo roots value centers
      hcenters hrows hvalues hterminal suffix
  have hpayoff : quittingTerminalPayoff reward
      (quittingRootSequenceProfile reward roots 0) = value 0 := by
    funext who
    exact (congrFun (hterminal 0) who).symm
  refine ⟨roots, value, centers, hcenters, hrows, hvalues,
    hterminal, hnash, ?_⟩
  rw [← hpayoff]
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward (quittingRootSequenceProfile reward roots 0) (hnash 0)

end GameTheory
