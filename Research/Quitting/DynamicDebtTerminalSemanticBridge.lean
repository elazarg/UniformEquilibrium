/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCapCarrier
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtChains
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Exact dynamic debt is terminal semantic debt

This experiment closes a semantic identification which is needed before the
fixed-port stopping-law geometry can interact with the production exact-`D`
state space.

Take a finite prescribed chain of length `cutoff`, with zero terminal value,
and extend its roots by all-Continue forever.  The finite dynamic-debt
coordinate uses the terminal cap

`max 0 (reward (singleton who) who)`.

That cap is not an artificial estimate: it is exactly the unrestricted
behavioral best-response envelope of the all-Continue suffix.  Consequently,
the finite dynamic debt at the entrance is exactly the literal infinite-game
best-response gap of the executable all-Continue extension.  The final theorem
specializes this statement to the production finite Nash--Bellman chains.

The positive-length assumption is only needed by the current phase-switch
holonomy evaluator.  The zero-length case is elementary and irrelevant to a
nonempty finite block.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## An all-Continue completion is literally the original root sequence -/

omit [Fintype ι] [DecidableEq ι] in
theorem quittingPhaseSwitchRoots_allContinue_eq_of_allContinue_from
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingPhaseSwitchRoots roots (fun _ => quittingAllContinueRoot) cutoff =
      roots := by
  funext time
  by_cases htime : time < cutoff
  · rw [quittingPhaseSwitchRoots_of_lt roots _ htime]
  · rw [quittingPhaseSwitchRoots_of_le roots _ (Nat.not_lt.mp htime),
      htail time (Nat.not_lt.mp htime)]

/-! ## Generic exact semantic bridge -/

/-- For any positive finite exact policy completed by all-Continue, its
entrance dynamic debt is exactly the terminal semantic debt of the resulting
infinite behavior profile. -/
theorem quittingFiniteDynamicDebt_eq_terminalSemanticDebt_of_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingFiniteDynamicDebt reward roots who (fun time => value time who)
        (quittingPositiveSingletonDebtCap reward who) 0 cutoff =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingInfinitePathProfile reward roots)) who := by
  let never : ℕ → ι → PMF Bool := fun _ => quittingAllContinueRoot
  let cap : ℝ := max 0 (reward (quittingSingletonTerminal who) who)
  have hphaseRoots :
      quittingPhaseSwitchRoots roots never cutoff = roots := by
    exact quittingPhaseSwitchRoots_allContinue_eq_of_allContinue_from
      roots cutoff htail
  have hphaseProfile :
      quittingPhaseSwitchProfile reward roots never cutoff =
        quittingInfinitePathProfile reward roots := by
    unfold quittingPhaseSwitchProfile quittingInfinitePathProfile
    rw [hphaseRoots]
  have htailBest :
      QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary reward never who =
        cap := by
    unfold QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary
    simpa [never, cap, quittingElementaryCapRoots] using
      (quittingRootSequenceBestResponseValue_elementaryCap_never
        (ι := ι) reward who hM hreward)
  have hlength : cutoff - 1 + 1 = cutoff :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcutoff))
  have hbest :=
    quittingPhaseSwitch_bestResponseAt_eq_continuationBestResponse
      reward roots never cutoff hcutoff who hM hreward
  rw [hphaseProfile] at hbest
  unfold QuittingBoundaryHolonomy.boundaryEnvelopeAt at hbest
  rw [quittingFiniteBoundaryHolonomy_bestResponse_eval, hlength,
    htailBest] at hbest
  have hterminalWho : value cutoff who = 0 := congrFun hterminal who
  have hdynamic :=
    prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse
      reward roots who (fun time => value time who)
        (quittingPositiveSingletonDebtCap reward who) 0 cutoff
  have hdynamic' :
      value 0 who +
          quittingFiniteDynamicDebt reward roots who
            (fun time => value time who)
            (quittingPositiveSingletonDebtCap reward who) 0 cutoff =
        quittingFiniteTerminalBestResponseValue reward roots who cap 0 cutoff := by
    simpa [quittingPositiveSingletonDebtCap, cap, hterminalWho] using hdynamic
  have hprescribed :
      quittingTerminalPayoff reward
          (quittingInfinitePathProfile reward roots) who = value 0 who := by
    exact congrFun
      (quittingTerminalPayoff_finiteExactChainProfile
        reward roots value cutoff htail hterminal hpolicy) who
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  dsimp
  linarith

/-- Time-translated form of the bridge.  It identifies the exact dynamic debt
at an arbitrary entrance `start` with the literal semantic debt of the
continuation profile seen from that entrance. -/
theorem quittingFiniteDynamicDebt_eq_terminalSemanticDebt_suffix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (start fuel : ℕ) (hfuel : 0 < fuel)
    (htail : ∀ time, start + fuel ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value (start + fuel) = 0)
    (hpolicy : ∀ time, start ≤ time → time < start + fuel →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingFiniteDynamicDebt reward roots who (fun time => value time who)
        (quittingPositiveSingletonDebtCap reward who) start fuel =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward roots start)) who := by
  let shiftedRoots : ℕ → ι → PMF Bool := fun time => roots (start + time)
  let shiftedValue : ℕ → Payoff ι := fun time => value (start + time)
  have hshiftTail : ∀ time, fuel ≤ time →
      shiftedRoots time = (quittingAllContinueRoot : ι → PMF Bool) := by
    intro time htime
    exact htail (start + time) (Nat.add_le_add_left htime start)
  have hshiftTerminal : shiftedValue fuel = 0 := by
    simpa [shiftedValue] using hterminal
  have hshiftPolicy : ∀ time, time < fuel →
      shiftedValue time = quittingRootSuccessorPayoff reward
        (shiftedValue (time + 1)) (shiftedRoots time) := by
    intro time htime
    apply hpolicy (start + time)
    · omega
    · omega
  have hzero :=
    quittingFiniteDynamicDebt_eq_terminalSemanticDebt_of_allContinue
      reward shiftedRoots shiftedValue fuel hfuel hshiftTail hshiftTerminal
        hshiftPolicy who hM hreward
  rw [quittingFiniteDynamicDebt_shift reward roots who
    (fun time => value time who)
    (quittingPositiveSingletonDebtCap reward who) start fuel]
  rw [quittingRootSequenceProfile_eq_shift reward roots start]
  exact hzero

/-! ## Production finite-chain specialization -/

/-- On every positive-length production zero-boundary Nash--Bellman chain,
the exact-`D` entrance annotation is the literal infinite terminal semantic
debt of its executable all-Continue extension. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_zero_eq_terminalSemanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingInfinitePathProfile reward
            (quittingFiniteNashBellmanPathRoots cutoff path))) who := by
  unfold quittingFiniteNashBellmanPathDynamicDebt
  simpa using
    (quittingFiniteDynamicDebt_eq_terminalSemanticDebt_of_allContinue
      reward
      (quittingFiniteNashBellmanPathRoots cutoff path)
      (quittingFiniteNashBellmanPathValue cutoff path)
      cutoff hcutoff
      (quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
        cutoff path)
      (quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
        reward cutoff path hpath)
      (quittingFiniteNashBellmanPathValue_eq_successor
        reward cutoff path hpath)
      who (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward))

/-- Every nonterminal displayed exact-`D` coordinate of a production chain is
the literal semantic debt of the executable continuation profile starting at
that same displayed time.  Thus the entire annotated path, not just its first
coordinate, has an infinite-game semantic interpretation. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt_suffix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who time =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward
            (quittingFiniteNashBellmanPathRoots cutoff path) time)) who := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let value := quittingFiniteNashBellmanPathValue cutoff path
  have hsum : time + (cutoff - time) = cutoff :=
    Nat.add_sub_of_le htime.le
  have hsuffix :=
    quittingFiniteDynamicDebt_eq_terminalSemanticDebt_suffix
      reward roots value time (cutoff - time) (Nat.sub_pos_of_lt htime)
      (fun later hlater => by
        apply quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
          cutoff path later
        simpa [hsum] using hlater)
      (by
        simpa [value, hsum] using
          (quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
            reward cutoff path hpath))
      (fun later htimeLater hlater => by
        apply quittingFiniteNashBellmanPathValue_eq_successor
          reward cutoff path hpath later
        simpa [hsum] using hlater)
      who (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  simpa [quittingFiniteNashBellmanPathDynamicDebt, roots, value] using hsuffix

/-- The padded terminal coordinate has the same interpretation.  At the
cutoff the continuation is all-Continue, its prescribed payoff is zero, and
its unrestricted behavioral envelope is exactly the singleton-or-Never cap. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_cutoff_eq_terminalSemanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who cutoff =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward
            (quittingFiniteNashBellmanPathRoots cutoff path) cutoff)) who := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  have hprofile :
      quittingRootSequenceProfile reward roots cutoff =
        quittingAlwaysContinueProfile reward := by
    funext player time history
    unfold quittingRootSequenceProfile quittingAlwaysContinueProfile
      StochasticGame.stationaryBehaviorProfile
    dsimp [roots]
    rw [quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
      cutoff path (cutoff + time) (Nat.le_add_right cutoff time)]
    rfl
  have hbest :
      quittingContinuationBestResponseValue reward
          (quittingAlwaysContinueProfile reward) who =
        quittingPositiveSingletonDebtCap reward who := by
    rw [← quittingRootSequenceProfile_quittingAllContinueRoot_zero_eq reward]
    simpa [quittingRootSequenceBestResponseValue, quittingElementaryCapRoots,
      quittingPositiveSingletonDebtCap] using
      (quittingRootSequenceBestResponseValue_elementaryCap_never
        (ι := ι) reward who (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward))
  unfold quittingFiniteNashBellmanPathDynamicDebt
  rw [Nat.sub_self]
  simp only [quittingFiniteDynamicDebt_zero]
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  dsimp
  rw [hprofile, hbest, quittingTerminalPayoff_quittingAlwaysContinue, sub_zero]

/-- Uniform all-times form: every displayed production debt coordinate,
including the padded cutoff coordinate, is exactly the terminal semantic debt
of its executable restarted suffix. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) (time : ℕ) (htime : time ≤ cutoff) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who time =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward
            (quittingFiniteNashBellmanPathRoots cutoff path) time)) who := by
  by_cases hlt : time < cutoff
  · exact
      quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt_suffix
        reward cutoff path hpath who time hlt
  · have heq : time = cutoff := Nat.le_antisymm htime (Nat.not_lt.mp hlt)
    subst time
    exact
      quittingFiniteNashBellmanPathDynamicDebt_cutoff_eq_terminalSemanticDebt
        reward cutoff path who

/-! ## Full production-port identification -/

/-- Raw-root presentation of the payoff/root/debt terminal port.  This is the
same tuple used by the stopping-law fixed-port experiment, restated here to
keep the Lean experiments independently compilable. -/
abbrev QuittingRawTerminalPort (ι : Type) [Fintype ι] :=
  (Payoff ι × (ι → PMF Bool)) × Payoff ι

/-- The raw terminal port of one executable behavioral continuation. -/
def quittingRawTerminalPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    QuittingRawTerminalPort ι :=
  ((fun observer => quittingTerminalPayoff reward profile observer,
      quittingProfileLiveRoot reward profile 0),
    fun observer => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) observer)

/-- Forget the simplex presentation of a production exact-`D` point and expose
its root as the raw Boolean PMF family used by behavioral terminal ports. -/
def quittingDebtPointRawTerminalPort (point : QuittingDebtPoint ι) :
    QuittingRawTerminalPort ι :=
  ((point.1.1, quittingRootOfSimplex point.1.2), point.2)

omit [DecidableEq ι] in
/-- Exposing the simplex root as its PMF family loses no production state. -/
theorem quittingDebtPointRawTerminalPort_injective :
    Function.Injective
      (quittingDebtPointRawTerminalPort (ι := ι)) := by
  intro x y hxy
  have hvalue : x.1.1 = y.1.1 :=
    congrArg (fun port : QuittingRawTerminalPort ι => port.1.1) hxy
  have hrootRaw : quittingRootOfSimplex x.1.2 =
      quittingRootOfSimplex y.1.2 :=
    congrArg (fun port : QuittingRawTerminalPort ι => port.1.2) hxy
  have hroot : x.1.2 = y.1.2 := by
    funext who
    apply (Math.ProbabilityMassFunction.stdSimplexEquiv
      (α := Bool)).symm.injective
    change quittingRootOfSimplex x.1.2 who =
      quittingRootOfSimplex y.1.2 who
    exact congrFun hrootRaw who
  have hdebt : x.2 = y.2 :=
    congrArg (fun port : QuittingRawTerminalPort ι => port.2) hxy
  exact Prod.ext (Prod.ext hvalue hroot) hdebt

/-- Before the padded terminal row, the complete behavioral terminal port of
the restarted executable suffix is exactly the raw-root presentation of the
production exact-`D` point: prescribed payoff, live product root, and every
player's debt coordinate all agree literally. -/
theorem quittingBehaviorTerminalPort_suffix_eq_dynamicDebtPointRawPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) (htime : time < cutoff) :
    quittingRawTerminalPort reward
        (quittingRootSequenceProfile reward
          (quittingFiniteNashBellmanPathRoots cutoff path) time) =
      quittingDebtPointRawTerminalPort
        (quittingFiniteNashBellmanPathDynamicDebtPoint
          reward cutoff path time) := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let value := quittingFiniteNashBellmanPathValue cutoff path
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_finite_zeroBoundary
      reward roots value cutoff
      (quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
        cutoff path)
      (quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
        reward cutoff path hpath)
      (quittingFiniteNashBellmanPathValue_eq_successor
        reward cutoff path hpath)
  have hpayoff :
      (fun observer => quittingTerminalPayoff reward
        (quittingRootSequenceProfile reward roots time) observer) =
        (path ⟨time, Nat.lt_succ_of_lt htime⟩).1 := by
    funext observer
    change quittingRootSequenceTerminalValue reward roots observer time = _
    rw [← congrFun (hselected time htime.le) observer]
    exact congrFun
      (quittingFiniteNashBellmanPathValue_of_lt cutoff path time htime)
      observer
  have hroot :
      quittingProfileLiveRoot reward
          (quittingRootSequenceProfile reward roots time) 0 =
        quittingRootOfSimplex
          (path ⟨time, Nat.lt_succ_of_lt htime⟩).2 := by
    change roots time = _
    exact quittingFiniteNashBellmanPathRoots_of_lt cutoff path time htime
  have hdebt :
      (fun observer => quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward roots time)) observer) =
        fun observer => quittingFiniteNashBellmanPathDynamicDebt
          reward cutoff path observer time := by
    funext observer
    exact
      (quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt_suffix
        reward cutoff path hpath observer time htime).symm
  unfold quittingRawTerminalPort quittingDebtPointRawTerminalPort
    quittingFiniteNashBellmanPathDynamicDebtPoint
  rw [dif_pos htime.le]
  dsimp only
  rw [hpayoff, hroot, hdebt]

/-- Exact classification of preterminal production suffixes: two restarted
behavioral continuations have the same payoff/root/debt port if and only if
their production exact-`D` points are equal.  The two paths and their cutoffs
may be different. -/
theorem quittingDynamicDebtPoint_eq_iff_rawTerminalPort_suffix_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoffA cutoffB : ℕ)
    (pathA : QuittingFiniteNashBellmanPath ι cutoffA)
    (pathB : QuittingFiniteNashBellmanPath ι cutoffB)
    (hpathA : pathA ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoffA)
    (hpathB : pathB ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoffB)
    (timeA timeB : ℕ) (htimeA : timeA < cutoffA)
    (htimeB : timeB < cutoffB) :
    quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoffA pathA timeA =
      quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoffB pathB timeB ↔
    quittingRawTerminalPort reward
        (quittingRootSequenceProfile reward
          (quittingFiniteNashBellmanPathRoots cutoffA pathA) timeA) =
      quittingRawTerminalPort reward
        (quittingRootSequenceProfile reward
          (quittingFiniteNashBellmanPathRoots cutoffB pathB) timeB) := by
  rw [quittingBehaviorTerminalPort_suffix_eq_dynamicDebtPointRawPort
      reward cutoffA pathA hpathA timeA htimeA,
    quittingBehaviorTerminalPort_suffix_eq_dynamicDebtPointRawPort
      reward cutoffB pathB hpathB timeB htimeB]
  constructor
  · exact fun h => congrArg quittingDebtPointRawTerminalPort h
  · intro h
    exact (quittingDebtPointRawTerminalPort_injective (ι := ι)) h

end GameTheory
