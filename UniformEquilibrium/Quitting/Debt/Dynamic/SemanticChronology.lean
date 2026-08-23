/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.LiveMass
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCapCarrier
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtChains
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile

/-!
# Terminal-semantic chronology of exact dynamic debt

The augmented pair `(value, value + debt)` of every exact dynamic-debt edge
obeys the literal terminal-semantic prefix equation.  The displayed root is
an exact Nash root against the successor prescribed value.

For a finite zero-boundary exact Nash--Bellman chain, each preterminal row is
the semantic pair of its executable all-Continue completion.  These identities
are independent of any terminal exploitability witness or projective-limit selection.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame Math.Probability Math.ProbabilityMassFunction
open Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Every exact-D edge is a literal semantic prefix -/

/-- Forget the displayed simplex root and augment prescribed value by exact
dynamic debt. -/
def quittingDynamicDebtSemanticPair (point : QuittingDebtPoint ι) :
    QuittingTerminalSemanticPair ι :=
  (point.1.1, quittingDynamicDebtCap point)

omit [DecidableEq ι] in
@[simp]
theorem quittingDynamicDebtSemanticPair_debt
    (point : QuittingDebtPoint ι) (who : ι) :
    quittingTerminalSemanticDebt (quittingDynamicDebtSemanticPair point) who =
      point.2 who := by
  simp [quittingDynamicDebtSemanticPair, quittingTerminalSemanticDebt,
    quittingDynamicDebtCap_apply]

omit [DecidableEq ι] in
/-- Semanticization is continuous; in particular it may be applied after a
fixed-time projective limit. -/
theorem continuous_quittingDynamicDebtSemanticPair :
    Continuous (quittingDynamicDebtSemanticPair :
      QuittingDebtPoint ι → QuittingTerminalSemanticPair ι) := by
  exact (continuous_fst.comp continuous_fst).prodMk
    continuous_quittingDynamicDebtCap

/-- Exact algebraic bridge: every dynamic-debt edge becomes precisely the
terminal-semantic prefix of its successor.  Nonnegativity is not needed for
this identity. -/
theorem quittingDynamicDebtSemanticPair_eq_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor) :
    quittingDynamicDebtSemanticPair current =
      quittingTerminalSemanticPrefix reward
        (quittingRootOfSimplex current.1.2)
        (quittingDynamicDebtSemanticPair successor) := by
  apply Prod.ext
  · exact hedge.1.1
  · funext who
    change quittingDynamicDebtCap current who =
      max
        (quittingRootQuitPayoff reward successor.1.1
          (quittingRootOfSimplex current.1.2) who)
        (quittingRootContinuePayoff reward
          (Function.update successor.1.1 who
            (quittingDynamicDebtCap successor who))
          (quittingRootOfSimplex current.1.2) who)
    rw [quittingDynamicDebtCap_eq_max_endpoints reward current successor hedge who,
      quittingDynamicDebtCap_apply,
      quittingRootContinuePayoff_update_add]
    unfold quittingRootOpponentContinueMass
    rw [quittingDebtOpponentContinueMass_eq_stationary]

/-- The root on an exact dynamic-debt edge is exact Nash against the
successor's prescribed value. -/
theorem quittingDynamicDebtEdge_exactNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor) :
    IsεQuittingRootNash reward successor.1.1 0
      (quittingRootOfSimplex current.1.2) := by
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward successor.1.1 (quittingRootOfSimplex current.1.2)).mp hedge.1.2

/-- Provenance-preserving edge package.  A boxed/nonnegative successor is a
semantic successor with nonnegative debt, and the edge supplies both the
literal prefix identity and exact root Nash. -/
theorem quittingDynamicDebtEdge_semanticPrefixChronology
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hsuccessorDebt : ∀ who, 0 ≤ successor.2 who) :
    quittingDynamicDebtSemanticPair current =
        quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex current.1.2)
          (quittingDynamicDebtSemanticPair successor) ∧
      IsεQuittingRootNash reward
        (quittingDynamicDebtSemanticPair successor).1 0
          (quittingRootOfSimplex current.1.2) ∧
      ∀ who, 0 ≤ quittingTerminalSemanticDebt
        (quittingDynamicDebtSemanticPair successor) who := by
  exact ⟨quittingDynamicDebtSemanticPair_eq_prefix
      reward current successor hedge,
    quittingDynamicDebtEdge_exactNash reward current successor hedge,
    fun who => by simpa using hsuccessorDebt who⟩

/-- Time-translated semantic identification of the finite dynamic debt of a
zero-boundary exact policy completed by all-Continue. -/
theorem quittingFiniteDynamicDebt_eq_terminalSemanticDebt_suffix_completion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (start fuel : ℕ) (hfuel : 0 < fuel)
    (htail : ∀ time, start + fuel ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value (start + fuel) = 0)
    (hpolicy : ∀ time, start ≤ time → time < start + fuel →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (who : ι) :
    quittingFiniteDynamicDebt reward roots who (fun time => value time who)
        (quittingPositiveSingletonDebtCap reward who) start fuel =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward roots start)) who := by
  let shiftedRoots : ℕ → ι → PMF Bool := fun time => roots (start + time)
  let shiftedValue : ℕ → Payoff ι := fun time => value (start + time)
  let never : ℕ → ι → PMF Bool := fun _ => quittingAllContinueRoot
  let cap : ℝ := max 0 (reward (quittingSingletonTerminal who) who)
  have hshiftTail : ∀ time, fuel ≤ time →
      shiftedRoots time = (quittingAllContinueRoot : ι → PMF Bool) := by
    intro time htime
    exact htail (start + time) (Nat.add_le_add_left htime start)
  have hphaseRoots :
      quittingPhaseSwitchRoots shiftedRoots never fuel = shiftedRoots := by
    exact quittingPhaseSwitchRoots_allContinue_eq_of_allContinue_from
      shiftedRoots fuel hshiftTail
  have hphaseProfile :
      quittingPhaseSwitchProfile reward shiftedRoots never fuel =
        quittingInfinitePathProfile reward shiftedRoots := by
    unfold quittingPhaseSwitchProfile quittingInfinitePathProfile
    rw [hphaseRoots]
  have htailBest :
      QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary reward never who =
        cap := by
    unfold QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary
    simpa [never, cap, quittingElementaryCapRoots] using
      (quittingRootSequenceBestResponseValue_elementaryCap_never
        (ι := ι) reward who)
  have hlength : fuel - 1 + 1 = fuel :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hfuel))
  have hbest :=
    quittingPhaseSwitch_bestResponseAt_eq_continuationBestResponse
      reward shiftedRoots never fuel hfuel who
  rw [hphaseProfile] at hbest
  unfold QuittingBoundaryHolonomy.boundaryEnvelopeAt at hbest
  rw [quittingFiniteBoundaryHolonomy_bestResponse_eval, hlength,
    htailBest] at hbest
  have hshiftTerminal : shiftedValue fuel = 0 := by
    simpa [shiftedValue] using hterminal
  have hterminalWho : shiftedValue fuel who = 0 := congrFun hshiftTerminal who
  have hdynamic :=
    prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse
      reward shiftedRoots who (fun time => shiftedValue time who)
        (quittingPositiveSingletonDebtCap reward who) 0 fuel
  have hdynamic' :
      shiftedValue 0 who +
          quittingFiniteDynamicDebt reward shiftedRoots who
            (fun time => shiftedValue time who)
            (quittingPositiveSingletonDebtCap reward who) 0 fuel =
        quittingFiniteTerminalBestResponseValue reward shiftedRoots who cap
          0 fuel := by
    simpa [quittingPositiveSingletonDebtCap, cap, hterminalWho] using hdynamic
  have hshiftPolicy : ∀ time, time < fuel →
      shiftedValue time = quittingRootSuccessorPayoff reward
        (shiftedValue (time + 1)) (shiftedRoots time) := by
    intro time htime
    apply hpolicy (start + time)
    · omega
    · omega
  have hprescribed :
      quittingTerminalPayoff reward
          (quittingInfinitePathProfile reward shiftedRoots) who =
        shiftedValue 0 who := by
    exact congrFun
      (quittingTerminalPayoff_finiteExactChainProfile
        reward shiftedRoots shiftedValue fuel hshiftTail hshiftTerminal
          hshiftPolicy) who
  have hzero :
      quittingFiniteDynamicDebt reward shiftedRoots who
          (fun time => shiftedValue time who)
          (quittingPositiveSingletonDebtCap reward who) 0 fuel =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingInfinitePathProfile reward shiftedRoots)) who := by
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    dsimp
    linarith
  rw [quittingFiniteDynamicDebt_shift reward roots who
    (fun time => value time who)
    (quittingPositiveSingletonDebtCap reward who) start fuel]
  rw [quittingRootSequenceProfile_eq_shift reward roots start]
  exact hzero

/-- Every preterminal production debt coordinate is the literal semantic
debt of the executable continuation restarted at that row. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt_completion
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
    quittingFiniteDynamicDebt_eq_terminalSemanticDebt_suffix_completion
      reward roots value time (cutoff - time) (Nat.sub_pos_of_lt htime)
      (fun later hlater => by
        apply quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
          cutoff path later
        simpa [hsum] using hlater)
      (by
        simpa [value, hsum] using
          (quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
            reward cutoff path hpath))
      (fun later _htimeLater hlater => by
        apply quittingFiniteNashBellmanPathValue_eq_successor
          reward cutoff path hpath later
        simpa [hsum] using hlater)
      who
  simpa [quittingFiniteNashBellmanPathDynamicDebt, roots, value] using hsuffix

/-- At every preterminal row, semanticization of the production exact-D
point is literally the terminal semantic pair of the restarted executable
all-Continue completion. -/
theorem quittingFiniteNashBellmanPathDynamicDebtSemanticPair_eq_completion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) (htime : time < cutoff) :
    quittingDynamicDebtSemanticPair
        (quittingFiniteNashBellmanPathDynamicDebtPoint
          reward cutoff path time) =
      quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingFiniteNashBellmanPathRoots cutoff path) time) := by
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
  have hdebt : ∀ observer,
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path observer time =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRootSequenceProfile reward roots time)) observer := by
    intro observer
    exact quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt_completion
      reward cutoff path hpath observer time htime
  unfold quittingDynamicDebtSemanticPair
    quittingFiniteNashBellmanPathDynamicDebtPoint
  rw [dif_pos htime.le]
  apply Prod.ext
  · exact hpayoff.symm
  · funext observer
    change quittingDynamicDebtCap
        ((path ⟨time, Nat.lt_succ_of_lt htime⟩,
          fun who => quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path who time) : QuittingDebtPoint ι) observer =
      quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward roots time) observer
    rw [quittingDynamicDebtCap_apply]
    change (path ⟨time, Nat.lt_succ_of_lt htime⟩).1 observer +
        quittingFiniteNashBellmanPathDynamicDebt reward cutoff path observer time =
      quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward roots time) observer
    rw [← hpayoff]
    have h := hdebt observer
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at h
    dsimp at h
    linarith

end GameTheory
