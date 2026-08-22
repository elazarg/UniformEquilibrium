/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalDebtShadowing

/-!
# Exact chronological data of a root schedule

Every executable product-root sequence has a canonical chronological debt
datum: at each live time use the literal prescribed payoff and best-response
debt of the reached tail.  Both one-stage defects are then exactly zero.  A
singleton-root constructor is provided as a specialization.

This construction is semantic bookkeeping, not a small-debt producer.  In
particular its initial debt is the actual terminal exploitability of the root
sequence.  Applied to a schedule assembled from frozen reset profiles, it does
not identify that debt with a sum of frozen reset chords.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingChronologicalDebtData

/-- The canonical chronological datum of an arbitrary executable product-root
sequence. -/
def exactOfRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) : QuittingChronologicalDebtData ι :=
  let pair := fun time ↦ quittingTerminalSemanticPair reward
    (quittingRootSequenceProfile reward roots time)
  { roots := roots
    prescribed := fun time ↦ (pair time).1
    debt := fun time who ↦ quittingTerminalSemanticDebt (pair time) who
    secant := fun _ _ ↦ 0 }

@[simp]
theorem exactOfRoots_root
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (exactOfRoots reward roots).root time = roots time := rfl

@[simp]
theorem exactOfRoots_semanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (exactOfRoots reward roots).semanticPair reward time =
      quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward roots time) := rfl

@[simp]
theorem exactOfRoots_prescribed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (exactOfRoots reward roots).prescribed time =
      ((exactOfRoots reward roots).semanticPair reward time).1 := by
  rw [exactOfRoots_semanticPair]
  rfl

@[simp]
theorem exactOfRoots_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) :
    (exactOfRoots reward roots).debt time who =
      quittingTerminalSemanticDebt
        ((exactOfRoots reward roots).semanticPair reward time) who := by
  rw [exactOfRoots_semanticPair]
  rfl

@[simp]
theorem exactOfRoots_candidateSuccessorPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (exactOfRoots reward roots).candidateSuccessorPair time =
      (exactOfRoots reward roots).semanticPair reward (time + 1) := by
  apply Prod.ext
  · rfl
  · funext who
    rw [exactOfRoots_semanticPair]
    simp [exactOfRoots, candidateSuccessorPair,
      quittingTerminalSemanticDebt]

/-- Literal reached-tail values have zero prescribed-payoff defect. -/
@[simp]
theorem exactOfRoots_prescribedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (exactOfRoots reward roots).prescribedDefect reward time = 0 := by
  funext who
  rw [prescribedDefect, exactOfRoots_candidateSuccessorPair,
    ← semanticPair_eq_prefix]
  simp

/-- Literal reached-tail debts have zero direct Bellman defect. -/
@[simp]
theorem exactOfRoots_directDebtDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (exactOfRoots reward roots).directDebtDefect reward time = 0 := by
  funext who
  rw [directDebtDefect, exactOfRoots_candidateSuccessorPair,
    ← semanticPair_eq_prefix]
  simp

/-- Its debt is the actual nonnegative unilateral terminal exploitability of
every reached tail. -/
theorem exactOfRoots_debt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) :
    0 ≤ (exactOfRoots reward roots).debt time who := by
  exact quittingTerminalDeviationDebt_nonneg reward
    (quittingRootSequenceProfile reward roots time) who

@[simp]
theorem exactOfRoots_secant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) :
    (exactOfRoots reward roots).secant time who = 0 := rfl

/-- The zero secant is generated because candidate and actual successor caps
coincide exactly. -/
theorem exactOfRoots_secant_generated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) :
    ((exactOfRoots reward roots).semanticPair reward time).2 who -
        (quittingTerminalSemanticPrefix reward (roots time)
          ((exactOfRoots reward roots).candidateSuccessorPair time)).2 who =
      (exactOfRoots reward roots).secant time who *
        (((exactOfRoots reward roots).semanticPair reward (time + 1)).2 who -
          ((exactOfRoots reward roots).candidateSuccessorPair time).2 who) := by
  rw [exactOfRoots_candidateSuccessorPair,
    QuittingChronologicalDebtData.semanticPair_eq_prefix]
  simp

/-- Exact prescribed forcing has zero discrepancy on every finite suffix. -/
theorem exactOfRoots_prescribedDiscrepancy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start length : ℕ) :
    |∑ offset ∈ Finset.range length,
      (exactOfRoots reward roots).prescribedDefect reward
        (start + offset) who| = 0 := by
  simp

/-- Exact direct debt forcing has zero generated-secant adverse sum on every
finite suffix. -/
theorem exactOfRoots_adverseDirectForcing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start length : ℕ) :
    -∑ offset ∈ Finset.range length,
      Math.survivalProduct
          (fun time ↦ (exactOfRoots reward roots).secant time who)
          start offset *
        (exactOfRoots reward roots).directDebtDefect reward
          (start + offset) who = 0 := by
  simp

/-- Literal prescribed tails are bounded by the canonical reward bound. -/
theorem exactOfRoots_prescribed_bounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) :
    ∀ time who,
      |(exactOfRoots reward roots).prescribed time who| ≤
        quittingRewardBound reward := by
  intro time who
  exact abs_quittingTerminalPayoff_le_quittingRewardBound reward
    (quittingRootSequenceProfile reward roots time) who

/-- Literal terminal debts are bounded by twice the canonical reward bound.
-/
theorem exactOfRoots_debt_bounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) :
    ∀ time who,
      |(exactOfRoots reward roots).debt time who| ≤
        2 * quittingRewardBound reward := by
  intro time who
  rw [exactOfRoots_debt, quittingTerminalSemanticDebt]
  refine (abs_sub _ _).trans ?_
  have hbest := abs_quittingContinuationBestResponseValue_le reward
    (quittingRootSequenceProfile reward roots time) who
    (abs_reward_le_quittingRewardBound reward)
  have hpayoff := abs_quittingTerminalPayoff_le_quittingRewardBound reward
    (quittingRootSequenceProfile reward roots time) who
  dsimp only [exactOfRoots_semanticPair, quittingTerminalSemanticPair]
  linarith

/-- The canonical chronological datum of an executable singleton root
schedule.  Its candidate pair at every time is the literal semantic pair of
that reached tail. -/
def exactOfSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (marginal : ℕ → PMF Bool) :
    QuittingChronologicalDebtData ι :=
  exactOfRoots reward
    (fun time ↦ quittingSoloMixedRoot (owner time) (marginal time))

@[simp]
theorem exactOfSingleton_root
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (marginal : ℕ → PMF Bool) (time : ℕ) :
    (exactOfSingleton reward owner marginal).root time =
      quittingSoloMixedRoot (owner time) (marginal time) := rfl

@[simp]
theorem exactOfSingleton_semanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (marginal : ℕ → PMF Bool) (time : ℕ) :
    (exactOfSingleton reward owner marginal).semanticPair reward time =
      quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (fun stage ↦ quittingSoloMixedRoot (owner stage) (marginal stage))
          time) := rfl

@[simp]
theorem exactOfSingleton_prescribed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (marginal : ℕ → PMF Bool) (time : ℕ) :
    (exactOfSingleton reward owner marginal).prescribed time =
      ((exactOfSingleton reward owner marginal).semanticPair reward time).1 := by
  rw [exactOfSingleton_semanticPair]
  rfl

@[simp]
theorem exactOfSingleton_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (marginal : ℕ → PMF Bool) (time : ℕ) (who : ι) :
    (exactOfSingleton reward owner marginal).debt time who =
      quittingTerminalSemanticDebt
        ((exactOfSingleton reward owner marginal).semanticPair reward time)
        who := by
  rw [exactOfSingleton_semanticPair]
  rfl

@[simp]
theorem exactOfSingleton_candidateSuccessorPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (marginal : ℕ → PMF Bool) (time : ℕ) :
    (exactOfSingleton reward owner marginal).candidateSuccessorPair time =
      (exactOfSingleton reward owner marginal).semanticPair reward
        (time + 1) := by
  apply Prod.ext
  · rfl
  · funext who
    rw [exactOfSingleton_semanticPair]
    simp [exactOfSingleton, candidateSuccessorPair,
      quittingTerminalSemanticDebt]

/-- Literal reached-tail values have zero prescribed-payoff defect. -/
@[simp]
theorem exactOfSingleton_prescribedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (marginal : ℕ → PMF Bool) (time : ℕ) :
    (exactOfSingleton reward owner marginal).prescribedDefect reward time = 0 := by
  funext who
  rw [prescribedDefect, exactOfSingleton_candidateSuccessorPair,
    ← semanticPair_eq_prefix]
  simp

/-- Literal reached-tail debts have zero direct Bellman defect. -/
@[simp]
theorem exactOfSingleton_directDebtDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (marginal : ℕ → PMF Bool) (time : ℕ) :
    (exactOfSingleton reward owner marginal).directDebtDefect reward time = 0 := by
  funext who
  rw [directDebtDefect, exactOfSingleton_candidateSuccessorPair,
    ← semanticPair_eq_prefix]
  simp

/-- The canonical datum's debt is the actual nonnegative unilateral terminal
exploitability of every reached tail. -/
theorem exactOfSingleton_debt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (marginal : ℕ → PMF Bool) (time : ℕ) (who : ι) :
    0 ≤ (exactOfSingleton reward owner marginal).debt time who := by
  exact quittingTerminalDeviationDebt_nonneg reward
    (quittingRootSequenceProfile reward
      (fun stage ↦ quittingSoloMixedRoot (owner stage) (marginal stage)) time)
    who

end QuittingChronologicalDebtData

end GameTheory
