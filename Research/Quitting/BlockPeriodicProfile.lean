/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium
import Research.Quitting.PeriodicRootResponseSystem

/-!
# Periodic block profiles with fixed hazards

Fix a period `m + 1` and, at each phase `k`, a hazard vector
`hazard k : ι → ℝ` with values in `[0, 1]`.  The *block profile* lets every
player quit at phase `k` with probability `hazard k i`, independently, and
repeats the schedule forever.  A player outside the phase's block is the case
`hazard k i = 0`; a sure quitter is `hazard k i = 1`.  Several players may move
at the same stage.

Write `P_k(S) = coalitionMass (hazard k) S` for the probability that exactly
the coalition `S` quits at phase `k`, and `s_k = continueMass (hazard k)` for
the probability that nobody does.  Rewards are read through
`weightOfReward`, which extends the coalition reward by zero at the empty
coalition, so a sum over all of `Finset ι` is a sum over the nonempty
coalitions.

Three systems are recorded.

* The **on-path value system** `IsQuittingBlockOnPathValue`:
  `U k i = ∑ S, P_k(S) r_i(S) + s_k * U (k+1) i`.  The cycle's terminal value
  solves it, and under one-turn opponent absorption it is the only solution.
* The **deviator's system** `IsQuittingBlockResponseSolution`:
  `W k i = max (sigmaValue …) (gammaValue … (W (k+1) i))`, where `sigmaValue`
  averages the deviator's quit-now reward over the co-quitters realized at the
  *same* stage and `gammaValue` is its continue branch.  The quit branch is
  `r_i({i})` only when no opponent of `i` moves at phase `k`.
* The **producer** `IsQuittingBlockCertificate`: a bounded, periodic, exactly
  Nash block system with one absorbing phase and nonnegative solo rewards makes
  its displayed origin row a uniform-equilibrium payoff.

## Main definitions

* `quittingBlockCycle` — the periodic family of product rows
* `IsQuittingBlockOnPathValue`, `IsQuittingBlockResponseSolution`
* `IsQuittingBlockCertificate`

## Main results

* `isQuittingBlockOnPathValue_cyclicTerminalValue`,
  `eq_cyclicTerminalValue_of_isQuittingBlockOnPathValue`
* `isQuittingCyclicResponseSolution_of_isQuittingBlockResponseSolution`
* `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`
* `QuittingCounterexampleRegime.exists_quittingBlockResponse_gain`
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Coalition form of one product row -/

/-- **The one-stage value of a product row.**  The row pays each nonempty
coalition its own reward, weighted by the coalition's mass, and pays the
declared tail on the event that nobody quits. -/
theorem quittingRootSuccessorPayoff_eq_coalitionSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who =
      (∑ S : Finset ι,
          coalitionMass (hazardOfRoot root) S * weightOfReward reward S who) +
        continueMass (hazardOfRoot root) * tail who := by
  rw [quittingRootSuccessorPayoff, quittingRootExpectedPayoff_eq_sum_coalitionMass]
  have hsplit : ∀ S : Finset ι,
      coalitionMass (hazardOfRoot root) S *
          quittingStageCoalitionPayoff reward tail S who =
        coalitionMass (hazardOfRoot root) S * weightOfReward reward S who +
          (if S = ∅ then continueMass (hazardOfRoot root) * tail who else 0) := by
    intro S
    by_cases hS : S = ∅
    · subst hS
      rw [if_pos rfl, coalitionMass_empty]
      simp [quittingStageCoalitionPayoff, weightOfReward]
    · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      rw [if_neg hS]
      simp [quittingStageCoalitionPayoff, weightOfReward, hne]
  rw [Finset.sum_congr rfl (fun S _ ↦ hsplit S), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq' Finset.univ (∅ : Finset ι)
    (fun _ ↦ continueMass (hazardOfRoot root) * tail who)]
  simp

/-- The same value read over the powerset of an active set. -/
theorem quittingRootSuccessorPayoff_eq_activeCoalitionSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (active : Finset ι) (root : ι → PMF Bool)
    (hroot : IsQuittingActiveRoot active root) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who =
      (∑ S ∈ active.powerset,
          coalitionMass (hazardOfRoot root) S * weightOfReward reward S who) +
        continueMass (hazardOfRoot root) * tail who := by
  rw [quittingRootSuccessorPayoff_eq_coalitionSum]
  congr 1
  refine (Finset.sum_subset (Finset.subset_univ active.powerset) ?_).symm
  intro S _ hS
  rw [coalitionMass_eq_zero_of_not_subset_active hroot (by simpa using hS), zero_mul]

/-! ## The block profile -/

variable (hazard : Fin (m + 1) → ι → ℝ)

/-- A hazard of zero is the pure Continue law, so a player outside a phase's
block is the case `hazard k i = 0`. -/
theorem quittingHazardCoin_zero (h0 : (0 : ℝ) ≤ 0) (h1 : (0 : ℝ) ≤ 1) :
    quittingHazardCoin 0 h0 h1 = PMF.pure false := by
  refine PMF.ext fun action ↦ ?_
  cases action <;> simp [quittingHazardCoin, PMF.ofFintype_apply]

/-- The periodic family of product rows of a hazard schedule: at phase `k`
each player quits with probability `hazard k i`, independently. -/
def quittingBlockCycle (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1) :
    Fin (m + 1) → ι → PMF Bool :=
  fun k ↦ rootOfHazard (hazard k) (h0 k) (h1 k)

variable {hazard}

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem hazardOfRoot_quittingBlockCycle
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1) (k : Fin (m + 1)) :
    hazardOfRoot (quittingBlockCycle hazard h0 h1 k) = hazard k :=
  hazardOfRoot_rootOfHazard (hazard k) (h0 k) (h1 k)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingBlockCycle_true
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1) (k : Fin (m + 1))
    (who : ι) :
    (quittingBlockCycle hazard h0 h1 k who true).toReal = hazard k who := by
  rw [quittingBlockCycle, rootOfHazard, quittingHazardCoin_true_toReal]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingBlockCycle_false
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1) (k : Fin (m + 1))
    (who : ι) :
    (quittingBlockCycle hazard h0 h1 k who false).toReal = 1 - hazard k who := by
  rw [quittingBlockCycle, rootOfHazard, quittingHazardCoin_false_toReal]

omit [DecidableEq ι] in
/-- The one-stage joint survival probability of a block row is the
continuation mass of its hazard vector. -/
theorem quittingStationaryContinueMass_quittingBlockCycle
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1) (k : Fin (m + 1)) :
    quittingStationaryContinueMass (quittingBlockCycle hazard h0 h1 k) =
      continueMass (hazard k) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability, continueMass]
  exact Finset.prod_congr rfl fun who _ ↦ quittingBlockCycle_false h0 h1 k who

/-! ## The on-path value system -/

/-- **The phase-value system of a block profile.**  At each phase the value is
the coalition-weighted reward of the quitters realized now plus the survival
probability times the next phase's value. -/
def IsQuittingBlockOnPathValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : Fin (m + 1) → ι → ℝ) (U : Fin (m + 1) → Payoff ι) : Prop :=
  ∀ (k : Fin (m + 1)) (who : ι),
    U k who =
      (∑ S : Finset ι, coalitionMass (hazard k) S * weightOfReward reward S who) +
        continueMass (hazard k) * U (finRotate (m + 1) k) who

/-- A phase-value family solves the block system exactly when it solves the
root policy recursion of the block cycle. -/
theorem isQuittingBlockOnPathValue_iff_rootSuccessorPayoff
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    (U : Fin (m + 1) → Payoff ι) :
    IsQuittingBlockOnPathValue reward hazard U ↔
      ∀ k : Fin (m + 1), U k = quittingRootSuccessorPayoff reward
        (U (finRotate (m + 1) k)) (quittingBlockCycle hazard h0 h1 k) := by
  constructor
  · intro hU k
    funext who
    rw [quittingRootSuccessorPayoff_eq_coalitionSum,
      hazardOfRoot_quittingBlockCycle h0 h1]
    exact hU k who
  · intro hU k who
    have hk := congrFun (hU k) who
    rwa [quittingRootSuccessorPayoff_eq_coalitionSum,
      hazardOfRoot_quittingBlockCycle h0 h1] at hk

/-- **The block cycle's terminal value solves the phase-value system.** -/
theorem isQuittingBlockOnPathValue_cyclicTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1) :
    IsQuittingBlockOnPathValue reward hazard
      (quittingCyclicTerminalValue reward (quittingBlockCycle hazard h0 h1)) :=
  (isQuittingBlockOnPathValue_iff_rootSuccessorPayoff h0 h1 _).mpr
    (quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward
      (quittingBlockCycle hazard h0 h1))

/-- **Uniqueness of the phase values.**  If every player's opponents absorb
with positive probability over one turn, the block system has exactly one
solution, the cycle's terminal value. -/
theorem eq_cyclicTerminalValue_of_isQuittingBlockOnPathValue
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    {U : Fin (m + 1) → Payoff ι} (hU : IsQuittingBlockOnPathValue reward hazard U)
    (hcontracts : ∀ who, (∏ k : Fin (m + 1),
      quittingStationaryFixedOpponentsContinueMass
        (quittingBlockCycle hazard h0 h1 k) who) < 1) :
    U = quittingCyclicTerminalValue reward (quittingBlockCycle hazard h0 h1) :=
  eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff reward _ U
    ((isQuittingBlockOnPathValue_iff_rootSuccessorPayoff h0 h1 U).mp hU) hcontracts

omit [DecidableEq ι] in
/-- The one-turn joint survival probability of a block cycle. -/
theorem prod_quittingStationaryContinueMass_quittingBlockCycle
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1) :
    (∏ k : Fin (m + 1),
        quittingStationaryContinueMass (quittingBlockCycle hazard h0 h1 k)) =
      ∏ k : Fin (m + 1), continueMass (hazard k) :=
  Finset.prod_congr rfl fun k _ ↦
    quittingStationaryContinueMass_quittingBlockCycle h0 h1 k

/-- **Uniqueness of the phase values under joint absorption.**  If the block
profile fails to survive a whole turn with positive probability, the phase-value
system has exactly one solution. -/
theorem eq_cyclicTerminalValue_of_isQuittingBlockOnPathValue_of_absorbing
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    {U : Fin (m + 1) → Payoff ι} (hU : IsQuittingBlockOnPathValue reward hazard U)
    (habsorb : (∏ k : Fin (m + 1), continueMass (hazard k)) < 1) :
    U = quittingCyclicTerminalValue reward (quittingBlockCycle hazard h0 h1) := by
  refine eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing reward _ U
    ((isQuittingBlockOnPathValue_iff_rootSuccessorPayoff h0 h1 U).mp hU) ?_
  rw [prod_quittingStationaryContinueMass_quittingBlockCycle]
  exact habsorb

/-! ## The deviator's system -/

/-- **The deviator's max-linear system in coalition form.**  The quit branch
`sigmaValue` averages the deviator's reward over the co-quitters realized at
the same stage; the continue branch `gammaValue` collects the other players'
absorbing rewards and carries the next phase's value on the survival event. -/
def IsQuittingBlockResponseSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : Fin (m + 1) → ι → ℝ) (W : Fin (m + 1) → Payoff ι) : Prop :=
  ∀ (k : Fin (m + 1)) (who : ι),
    W k who =
      max (sigmaValue (weightOfReward reward) (hazard k) who)
        (gammaValue (weightOfReward reward) (hazard k) who
          (W (finRotate (m + 1) k) who))

/-- **The coalition form of the deviator's system is the abstract one.** -/
theorem isQuittingCyclicResponseSolution_of_isQuittingBlockResponseSolution
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    {W : Fin (m + 1) → Payoff ι}
    (hW : IsQuittingBlockResponseSolution reward hazard W) :
    IsQuittingCyclicResponseSolution reward (quittingBlockCycle hazard h0 h1) W := by
  intro k who
  rw [quittingRootQuitPayoff_eq_sigmaValue, quittingRootContinuePayoff_eq_gammaValue,
    hazardOfRoot_quittingBlockCycle h0 h1]
  exact hW k who

/-- The one-stage endpoint difference of a block row is the coalition-form
gain of its hazard vector. -/
theorem quittingRootEndpointDifference_quittingBlockCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    (tail : Payoff ι) (k : Fin (m + 1)) (who : ι) :
    quittingRootEndpointDifference reward tail (quittingBlockCycle hazard h0 h1 k)
        who =
      gainValue (weightOfReward reward) (hazard k) who (tail who) := by
  rw [quittingRootEndpointDifference, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue, hazardOfRoot_quittingBlockCycle h0 h1,
    gainValue]

/-- **The exact finite best-response statistic is capped by a coalition-form
response solution.** -/
theorem quittingCyclicResponseCap_le_of_isQuittingBlockResponseSolution
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    {W : Fin (m + 1) → Payoff ι}
    (hW : IsQuittingBlockResponseSolution reward hazard W) (phase : Fin (m + 1))
    (who : ι)
    (hcontract : (∏ k : Fin (m + 1),
      quittingStationaryFixedOpponentsContinueMass
        (quittingBlockCycle hazard h0 h1 k) who) < 1) :
    quittingCyclicResponseCap reward (quittingBlockCycle hazard h0 h1) phase who ≤
      W phase who :=
  quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution
    (isQuittingCyclicResponseSolution_of_isQuittingBlockResponseSolution h0 h1 hW)
    phase who hcontract

/-! ## The producer -/

/-- The stage of a displayed row reduced modulo the period. -/
def quittingPeriodicStage (m : ℕ) (stage : Fin (m + 2)) : Fin (m + 1) :=
  ⟨stage.1 % (m + 1), Nat.mod_lt _ m.succ_pos⟩

@[simp] theorem quittingPeriodicStage_castSucc (k : Fin (m + 1)) :
    quittingPeriodicStage m (Fin.castSucc k) = k :=
  Fin.ext (Nat.mod_eq_of_lt k.2)

/-- The Nash--Bellman path of a block profile with displayed values `U`. -/
def quittingBlockPath (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    (U : Fin (m + 2) → Payoff ι) : QuittingFiniteNashBellmanPath ι (m + 1) :=
  fun stage ↦
    (U stage,
      fun who ↦ stdSimplexEquiv
        (quittingBlockCycle hazard h0 h1 (quittingPeriodicStage m stage) who))

omit [DecidableEq ι] in
theorem quittingRootOfSimplex_quittingBlockPath
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    (U : Fin (m + 2) → Payoff ι) (k : Fin (m + 1)) :
    quittingRootOfSimplex (quittingBlockPath h0 h1 U (Fin.castSucc k)).2 =
      quittingBlockCycle hazard h0 h1 k := by
  funext who
  show (stdSimplexEquiv (α := Bool)).symm
      (stdSimplexEquiv
        (quittingBlockCycle hazard h0 h1
          (quittingPeriodicStage m (Fin.castSucc k)) who)) = _
  rw [quittingPeriodicStage_castSucc, (stdSimplexEquiv (α := Bool)).symm_apply_apply]

variable (reward)

/-- **The finite obligations of a block profile.**  The value recursion, the
exact one-stage complementarity of every hazard against its coalition-form
gain, periodicity, boundedness, one absorbing phase, and nonnegative solo
rewards. -/
structure IsQuittingBlockCertificate
    (hazard : Fin (m + 1) → ι → ℝ) (U : Fin (m + 2) → Payoff ι) : Prop where
  /-- Every hazard is a probability. -/
  hazard_nonneg : ∀ k i, 0 ≤ hazard k i
  /-- Every hazard is a probability. -/
  hazard_le_one : ∀ k i, hazard k i ≤ 1
  /-- Every displayed value fits inside the canonical reward box. -/
  box : ∀ (stage : Fin (m + 2)) (who : ι),
    |U stage who| ≤ quittingRewardBound reward
  /-- The displayed path closes up. -/
  last : U (Fin.last (m + 1)) = U 0
  /-- The phase-value recursion. -/
  succ : ∀ (k : Fin (m + 1)) (who : ι),
    U (Fin.castSucc k) who =
      (∑ S : Finset ι, coalitionMass (hazard k) S * weightOfReward reward S who) +
        continueMass (hazard k) * U (Fin.succ k) who
  /-- Exact one-stage complementarity: a player quitting with positive
  probability does not lose by it, and a player continuing with positive
  probability does not gain by quitting. -/
  gain : ∀ (k : Fin (m + 1)) (who : ι),
    (1 - hazard k who) *
        gainValue (weightOfReward reward) (hazard k) who (U (Fin.succ k) who) ≤ 0 ∧
      0 ≤ hazard k who *
        gainValue (weightOfReward reward) (hazard k) who (U (Fin.succ k) who)
  /-- Some phase absorbs with positive probability. -/
  absorb : ∃ k : Fin (m + 1), continueMass (hazard k) < 1
  /-- Every player's own solo reward is nonnegative. -/
  solo : ∀ who : ι, 0 ≤ reward (quittingSingletonTerminal who) who

variable {reward}

/-- **Certificate from the root-level obligations.**  The value recursion and
the exact one-stage Nash condition may be supplied in their abstract root form
instead of in coalition form. -/
theorem isQuittingBlockCertificate_of_root
    {hazard : Fin (m + 1) → ι → ℝ} (h0 : ∀ k i, 0 ≤ hazard k i)
    (h1 : ∀ k i, hazard k i ≤ 1) {U : Fin (m + 2) → Payoff ι}
    (hbox : ∀ (stage : Fin (m + 2)) (who : ι),
      |U stage who| ≤ quittingRewardBound reward)
    (hlast : U (Fin.last (m + 1)) = U 0)
    (hsucc : ∀ k : Fin (m + 1), U (Fin.castSucc k) =
      quittingRootSuccessorPayoff reward (U (Fin.succ k))
        (quittingBlockCycle hazard h0 h1 k))
    (hnash : ∀ k : Fin (m + 1), IsεQuittingRootEndpointNash reward (U (Fin.succ k)) 0
      (quittingBlockCycle hazard h0 h1 k))
    (habsorb : ∃ k : Fin (m + 1), continueMass (hazard k) < 1)
    (hsolo : ∀ who : ι, 0 ≤ reward (quittingSingletonTerminal who) who) :
    IsQuittingBlockCertificate reward hazard U := by
  refine ⟨h0, h1, hbox, hlast, ?_, ?_, habsorb, hsolo⟩
  · intro k who
    have hk := congrFun (hsucc k) who
    rwa [quittingRootSuccessorPayoff_eq_coalitionSum,
      hazardOfRoot_quittingBlockCycle h0 h1] at hk
  · intro k who
    have hk := hnash k who
    rwa [quittingRootEndpointDifference_quittingBlockCycle reward h0 h1,
      quittingBlockCycle_false, quittingBlockCycle_true, neg_zero] at hk

/-- A certified block profile is an absorbing exact cyclic continuation block
for its displayed origin row. -/
theorem isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate
    {U : Fin (m + 2) → Payoff ι}
    (hcert : IsQuittingBlockCertificate reward hazard U) :
    IsQuittingCyclicContinuationBlock reward (U 0) (m + 1)
      (quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U) := by
  set h0 := hcert.hazard_nonneg
  set h1 := hcert.hazard_le_one
  refine ⟨⟨?_, hcert.last, ?_⟩, rfl, ?_⟩
  · intro stage
    exact ⟨fun who ↦ neg_le_of_abs_le (hcert.box stage who),
      fun who ↦ le_of_abs_le (hcert.box stage who)⟩
  · intro k
    refine ⟨?_, ?_⟩
    · show U (Fin.castSucc k) =
        quittingRootSuccessorPayoff reward (U (Fin.succ k))
          (quittingRootOfSimplex (quittingBlockPath h0 h1 U (Fin.castSucc k)).2)
      rw [quittingRootOfSimplex_quittingBlockPath]
      funext who
      rw [quittingRootSuccessorPayoff_eq_coalitionSum,
        hazardOfRoot_quittingBlockCycle h0 h1]
      exact hcert.succ k who
    · show IsεQuittingRootEndpointNash reward (U (Fin.succ k)) 0
        (quittingRootOfSimplex (quittingBlockPath h0 h1 U (Fin.castSucc k)).2)
      rw [quittingRootOfSimplex_quittingBlockPath]
      intro who
      rw [quittingRootEndpointDifference_quittingBlockCycle reward h0 h1,
        quittingBlockCycle_false, quittingBlockCycle_true, neg_zero]
      exact hcert.gain k who
  · obtain ⟨k, hk⟩ := hcert.absorb
    refine ⟨k, ?_⟩
    rw [quittingRootOfSimplex_quittingBlockPath, quittingRootAbsorptionMass,
      quittingStationaryContinueMass_quittingBlockCycle]
    linarith

/-- **A certified block profile realizes its origin row as a
uniform-equilibrium payoff.**  The deviation class is all behavior strategies,
not stopping times. -/
theorem isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
    {U : Fin (m + 2) → Payoff ι}
    (hcert : IsQuittingBlockCertificate reward hazard U) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (U 0) :=
  isUniformEquilibriumPayoff_terminal_of_admissible_quittingCyclicContinuationBlock
    reward (U 0) m (quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U)
    (isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate hcert)
    (fun who ↦ Or.inr (hcert.solo who))

/-- A table carrying a certified block profile lies in no counterexample
regime. -/
theorem isEmpty_counterexampleRegime_of_isQuittingBlockCertificate
    {U : Fin (m + 2) → Payoff ι}
    (hcert : IsQuittingBlockCertificate reward hazard U) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  ⟨fun regime ↦ regime.not_exists_uniformEquilibriumPayoff
    ⟨U 0, isUniformEquilibriumPayoff_of_isQuittingBlockCertificate hcert⟩⟩

/-! ## The necessary condition -/

namespace QuittingCounterexampleRegime

/-- **Every periodic block profile is exposed at the full terminal gap.**  A
counterexample regime leaves some player a gain of at least its terminal gap
over the block profile's on-path value, measured by the exact finite
best-response statistic. -/
theorem exists_quittingBlockCap_gain
    (regime : QuittingCounterexampleRegime reward)
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    (phase : Fin (m + 1)) {U : Fin (m + 1) → Payoff ι}
    (hU : IsQuittingBlockOnPathValue reward hazard U)
    (habsorb : (∏ k : Fin (m + 1), continueMass (hazard k)) < 1) :
    ∃ who, U phase who + regime.terminalGap ≤
      quittingCyclicResponseCap reward (quittingBlockCycle hazard h0 h1) phase
        who := by
  obtain ⟨who, hgain⟩ := regime.exists_quittingCyclicCap_gain
    (quittingBlockCycle hazard h0 h1) phase
  refine ⟨who, ?_⟩
  rwa [eq_cyclicTerminalValue_of_isQuittingBlockOnPathValue_of_absorbing h0 h1 hU
    habsorb]

/-- **Every periodic block profile is exposed at the full terminal gap.**  A
counterexample regime forces some player's response value to exceed the block
profile's on-path value by at least the regime's terminal gap. -/
theorem exists_quittingBlockResponse_gain
    (regime : QuittingCounterexampleRegime reward)
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    (phase : Fin (m + 1)) {U W : Fin (m + 1) → Payoff ι}
    (hU : IsQuittingBlockOnPathValue reward hazard U)
    (hW : IsQuittingBlockResponseSolution reward hazard W)
    (hcontracts : ∀ who, (∏ k : Fin (m + 1),
      quittingStationaryFixedOpponentsContinueMass
        (quittingBlockCycle hazard h0 h1 k) who) < 1) :
    ∃ who, U phase who + regime.terminalGap ≤ W phase who := by
  have hvalue := eq_cyclicTerminalValue_of_isQuittingBlockOnPathValue h0 h1 hU
    hcontracts
  obtain ⟨who, hgain⟩ := regime.exists_quittingCyclicResponse_gain
    (quittingBlockCycle hazard h0 h1) phase
    (isQuittingCyclicResponseSolution_of_isQuittingBlockResponseSolution h0 h1 hW)
    hcontracts
  refine ⟨who, ?_⟩
  rwa [hvalue]

end QuittingCounterexampleRegime

end GameTheory
