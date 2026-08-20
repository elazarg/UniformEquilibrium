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
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile
import UniformEquilibrium.Quitting.Debt.Dynamic.SemanticChronology

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

/-! ## Generic exact semantic bridge -/

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
  simpa [quittingInfinitePathProfile] using
    (_root_.GameTheory.quittingFiniteDynamicDebt_eq_terminalSemanticDebt_suffix_completion
      reward
      (quittingFiniteNashBellmanPathRoots cutoff path)
      (quittingFiniteNashBellmanPathValue cutoff path)
      0 cutoff hcutoff
      (fun time htime => by
        apply quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
        simpa using htime)
      (by
        simpa using quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
          reward cutoff path hpath)
      (fun time _ htime => by
        exact quittingFiniteNashBellmanPathValue_eq_successor
          reward cutoff path hpath time (by simpa using htime))
      who)

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
        (ι := ι) reward who)
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
      _root_.GameTheory.quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt_completion
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
      (_root_.GameTheory.quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt_completion
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
