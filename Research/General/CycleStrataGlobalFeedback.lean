/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.EndpointBackwardStability
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium
import GameTheory.Concepts.Stochastic.Models.Quitting.UniformPayoffExistenceClosure

/-!
# Exact-cycle strata: global backward error with cyclic feedback

This experiment advances beyond the fixed-tail theorem in
`Root.EndpointBackwardStability`.  The row theorem says that an own-set shift
`d i` translates player `i`'s endpoint gap by `d i` while the continuation is
held fixed.  On a cycle the continuation is *not* fixed: changing the common
terminal table changes every phase value and those corrections feed around
the cycle.

For a fixed cycle of product roots, write `a t i` for the change in player
`i`'s displayed value after applying the one common own-set shift `d`.  The two
identities proved here are

```
a t i = q t * a (t+1) i + p t i * d i
g' t i = g t i + d i - c t i * a (t+1) i,
```

where `q t` is joint all-continue mass, `p t i` is player `i`'s quit
probability, and `c t i` is the probability that all opponents of `i`
continue.  The first identity is policy feedback; the second is the corrected
endpoint gap.  Together they give a finite cyclic linear
complementarity/interval feasibility system.  In particular, exactifying
each phase against its old fixed tail does not solve the global problem.

The file also distinguishes two strata:

* `IsRawExactQuittingCycle` asks only for exact cyclic policy recursion and
  exact root Nash;
* `IsSolvedExactQuittingCycle` additionally asks for absorption and the
  landed admissibility condition required by the behavioral compiler.

Only the latter is a certified solved stratum.  No density claim is made.
The landed reward-perturbation closure theorem says that density of such
solved tables would imply existence of a uniform-equilibrium payoff for every
quitting table, but proving that density remains the substantive open step.
-/


noncomputable section

namespace GameTheory
namespace CycleStrataExperiment

open StochasticGame Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The two strata -/

/-- Raw exact cyclic complementarity.  This does *not* by itself certify an
equilibrium against infinite behavioral deviations. -/
def IsRawExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι) : Prop :=
  (∀ phase, value phase = quittingRootSuccessorPayoff reward
      (value (finRotate K phase)) (cycle phase)) ∧
    ∀ phase, IsεQuittingRootNash reward
      (value (finRotate K phase)) 0 (cycle phase)

/-- The stratum accepted by the existing cyclic behavioral compiler: raw
exactness plus genuine absorption and deviation admissibility. -/
def IsSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι) : Prop :=
  IsRawExactQuittingCycle reward cycle value ∧
    (∏ phase : Fin K, quittingStationaryContinueMass (cycle phase)) < 1 ∧
    IsQuittingCycleAdmissible reward cycle

theorem isZeroAsymptoticNash_of_isSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (h : IsSolvedExactQuittingCycle reward cycle value) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  exact isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_admissible
    reward cycle value phase h.1.1 h.1.2 h.2.1 h.2.2

/-- A table in the solved stratum really does have a uniform-equilibrium
payoff.  This is why density must be formulated using `IsSolvedExactQuittingCycle`
rather than raw cyclic complementarity. -/
theorem exists_uniformEquilibriumPayoff_of_isSolvedExactQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (h : IsSolvedExactQuittingCycle reward cycle value) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  exact ⟨quittingCyclicBehaviorProfile reward cycle phase,
    (isZeroAsymptoticNash_of_isSolvedExactQuittingCycle
      reward cycle value phase h).mono hε.le⟩

/-- **The exact density consumer.**  If every reward-table neighborhood
contains a table carrying some solved finite cycle, payoff-perturbation
closure proves a uniform-equilibrium payoff for the original table.  The
theorem assumes density; it does not establish it. -/
theorem exists_uniformEquilibriumPayoff_of_arbitrarily_close_solvedCycles
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hdense : ∀ η : ℝ, 0 < η →
      ∃ nearby : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ S who, |nearby S who - reward S who| ≤ η) ∧
          ∃ K : ℕ, ∃ _ : Fin K,
            ∃ cycle : Fin K → ι → PMF Bool, ∃ value : Fin K → Payoff ι,
              IsSolvedExactQuittingCycle nearby cycle value) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards reward
  intro η hη
  obtain ⟨nearby, hnearby, K, phase, cycle, value, hsolved⟩ := hdense η hη
  exact ⟨nearby, hnearby,
    exists_uniformEquilibriumPayoff_of_isSolvedExactQuittingCycle
      nearby cycle value phase hsolved⟩

/-! ## One-stage identities with continuation feedback -/

/-- Changing the tail by `correction` translates the endpoint gap by minus
the deleted (opponent-only) survival mass times the selected coordinate of
that correction. -/
theorem quittingRootEndpointDifference_tail_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail correction : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward
        (fun i ↦ tail i + correction i) root who =
      quittingRootEndpointDifference reward tail root who -
        quittingStationaryFixedOpponentsContinueMass root who * correction who := by
  have hquit := quittingRootSuccessorPayoff_sub_eq_continueMass_mul reward
    (fun i ↦ tail i + correction i) tail
    (Function.update root who (PMF.pure true)) who
  have hcontinue := quittingRootSuccessorPayoff_sub_eq_continueMass_mul reward
    (fun i ↦ tail i + correction i) tail
    (Function.update root who (PMF.pure false)) who
  change quittingRootQuitPayoff reward (fun i ↦ tail i + correction i) root who -
      quittingRootQuitPayoff reward tail root who = _ at hquit
  change quittingRootContinuePayoff reward (fun i ↦ tail i + correction i) root who -
      quittingRootContinuePayoff reward tail root who = _ at hcontinue
  rw [quittingStationaryContinueMass_update_pure_true_eq_zero] at hquit
  change quittingRootContinuePayoff reward
      (fun i ↦ tail i + correction i) root who -
        quittingRootContinuePayoff reward tail root who =
      quittingStationaryFixedOpponentsContinueMass root who *
        ((tail who + correction who) - tail who) at hcontinue
  unfold quittingRootEndpointDifference
  rw [show (tail who + correction who) - tail who = correction who by ring] at hcontinue
  linarith

/-- **Global endpoint-gap identity.**  Under one common own-set table shift,
and allowing the cyclic continuation value to move by `correction`, the
fixed-tail `+ d who` translation acquires the feedback term
`- c⁻ᵢ * correction who`. -/
theorem quittingRootEndpointDifference_ownShiftReward_tail_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail correction : Payoff ι) (root : ι → PMF Bool)
    (d : ι → ℝ) (who : ι) :
    quittingRootEndpointDifference (ownShiftReward reward d)
        (fun i ↦ tail i + correction i) root who =
      quittingRootEndpointDifference reward tail root who + d who -
        quittingStationaryFixedOpponentsContinueMass root who * correction who := by
  rw [quittingRootEndpointDifference_tail_add,
    quittingRootEndpointDifference_ownShiftReward]

/-- At a fixed root, changing the common table and the tail changes the
prescribed successor value by exactly
`quitProbability * d + jointContinueMass * correction`. -/
theorem quittingRootSuccessorPayoff_ownShiftReward_tail_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail correction : Payoff ι) (root : ι → PMF Bool)
    (d : ι → ℝ) (who : ι) :
    quittingRootSuccessorPayoff (ownShiftReward reward d)
        (fun i ↦ tail i + correction i) root who =
      quittingRootSuccessorPayoff reward tail root who +
        (root who true).toReal * d who +
        quittingStationaryContinueMass root * correction who := by
  have htail := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    (ownShiftReward reward d) (fun i ↦ tail i + correction i) tail root who
  have hshift :
      quittingRootSuccessorPayoff (ownShiftReward reward d) tail root who =
        quittingRootSuccessorPayoff reward tail root who +
          (root who true).toReal * d who := by
    rw [quittingRootSuccessorPayoff_eq_endpointMix,
      quittingRootSuccessorPayoff_eq_endpointMix,
      quittingRootQuitPayoff_ownShiftReward,
      quittingRootContinuePayoff_ownShiftReward]
    ring
  rw [show (tail who + correction who) - tail who = correction who by ring] at htail
  linarith

/-! ## Necessary and sufficient global linear system -/

/-- The affine value-feedback recurrence induced by an own-set table shift. -/
def SatisfiesOwnShiftFeedbackRecurrence
    (cycle : Fin K → ι → PMF Bool) (d : ι → ℝ)
    (correction : Fin K → Payoff ι) : Prop :=
  ∀ phase who,
    correction phase who =
      quittingStationaryContinueMass (cycle phase) *
          correction (finRotate K phase) who +
        ((cycle phase who) true).toReal * d who

/-- Exact cyclic policy recursion for the shifted table and corrected values. -/
def IsOwnShiftPolicyCorrection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι) : Prop :=
  ∀ phase,
    (fun who ↦ value phase who + correction phase who) =
      quittingRootSuccessorPayoff (ownShiftReward reward d)
        (fun who ↦ value (finRotate K phase) who +
          correction (finRotate K phase) who)
        (cycle phase)

/-- **Policy-feedback consistency iff the finite cyclic linear recurrence.**
This is the missing global counterpart of the fixed-tail row theorem. -/
theorem isOwnShiftPolicyCorrection_iff_feedbackRecurrence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι)
    (hpolicy : ∀ phase, value phase = quittingRootSuccessorPayoff reward
      (value (finRotate K phase)) (cycle phase)) :
    IsOwnShiftPolicyCorrection reward cycle value d correction ↔
      SatisfiesOwnShiftFeedbackRecurrence cycle d correction := by
  constructor
  · intro h phase who
    have hnew := congrFun (h phase) who
    have hold := congrFun (hpolicy phase) who
    rw [quittingRootSuccessorPayoff_ownShiftReward_tail_add] at hnew
    linarith
  · intro h phase
    funext who
    have hold := congrFun (hpolicy phase) who
    rw [quittingRootSuccessorPayoff_ownShiftReward_tail_add]
    rw [h phase who, hold]
    ring

/-- The corrected endpoint gap written entirely in the finite feedback
variables. -/
def ownShiftCorrectedGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι)
    (phase : Fin K) (who : ι) : ℝ :=
  quittingRootEndpointDifference reward (value (finRotate K phase))
      (cycle phase) who + d who -
    quittingStationaryFixedOpponentsContinueMass (cycle phase) who *
      correction (finRotate K phase) who

theorem ownShiftCorrectedGap_eq_endpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι)
    (phase : Fin K) (who : ι) :
    ownShiftCorrectedGap reward cycle value d correction phase who =
      quittingRootEndpointDifference (ownShiftReward reward d)
        (fun i ↦ value (finRotate K phase) i +
          correction (finRotate K phase) i)
        (cycle phase) who := by
  rw [quittingRootEndpointDifference_ownShiftReward_tail_add]
  rfl

/-- The complete finite feasibility predicate for globally exactifying one
supplied root/value cycle by a common own-set perturbation.  Equalities are
required at mixed coordinates; the same pair of inequalities automatically
becomes the correct one-sided condition at pure coordinates. -/
def OwnShiftExactificationSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι) : Prop :=
  SatisfiesOwnShiftFeedbackRecurrence cycle d correction ∧
    ∀ phase who,
      (cycle phase who false).toReal *
          ownShiftCorrectedGap reward cycle value d correction phase who ≤ 0 ∧
        0 ≤ (cycle phase who true).toReal *
          ownShiftCorrectedGap reward cycle value d correction phase who

/-- **Necessary and sufficient global exactification system.**  Assuming the
supplied values already evaluate the original cycle, a common shift and a
value correction exactify the whole cyclic policy iff they solve the explicit
finite recurrence plus complementarity inequalities above. -/
theorem ownShiftExactificationSystem_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (d : ι → ℝ) (correction : Fin K → Payoff ι)
    (hpolicy : ∀ phase, value phase = quittingRootSuccessorPayoff reward
      (value (finRotate K phase)) (cycle phase)) :
    OwnShiftExactificationSystem reward cycle value d correction ↔
      IsOwnShiftPolicyCorrection reward cycle value d correction ∧
        ∀ phase, IsεQuittingRootEndpointNash (ownShiftReward reward d)
          (fun who ↦ value (finRotate K phase) who +
            correction (finRotate K phase) who)
          0 (cycle phase) := by
  rw [isOwnShiftPolicyCorrection_iff_feedbackRecurrence
    reward cycle value d correction hpolicy]
  constructor
  · rintro ⟨hfeedback, hnash⟩
    refine ⟨hfeedback, fun phase who ↦ ?_⟩
    rw [← ownShiftCorrectedGap_eq_endpointDifference
      reward cycle value d correction phase who]
    simpa using hnash phase who
  · rintro ⟨hfeedback, hnash⟩
    refine ⟨hfeedback, fun phase who ↦ ?_⟩
    have h := hnash phase who
    rw [← ownShiftCorrectedGap_eq_endpointDifference
      reward cycle value d correction phase who] at h
    simpa using h

/-! ## Exact phase-conflict regressions -/

/-- Two frozen-tail phases can be exactified independently: their demanded
shifts may simply disagree. -/
theorem twoPhases_independently_exactifiable :
    ∃ d₀ d₁ : ℝ, (1 + d₀ = 0) ∧ (-1 + d₁ = 0) := by
  exact ⟨-1, 1, by norm_num, by norm_num⟩

/-- The same two demands cannot be met by one common table shift, even before
cyclic value feedback is imposed. -/
theorem twoPhases_not_exactifiable_by_common_shift :
    ¬ ∃ d : ℝ, (1 + d = 0) ∧ (-1 + d = 0) := by
  rintro ⟨d, h₀, h₁⟩
  linarith

/-- With a two-phase half-survival feedback recurrence, allowing the cyclic
values to recompute still does not reconcile the opposing phase demands. -/
theorem twoPhase_halfSurvival_feedback_conflict :
    ¬ ∃ d a₀ a₁ : ℝ,
      a₀ = (1 / 2 : ℝ) * a₁ + (1 / 2 : ℝ) * d ∧
      a₁ = (1 / 2 : ℝ) * a₀ + (1 / 2 : ℝ) * d ∧
      1 + d - a₁ = 0 ∧
      -1 + d - a₀ = 0 := by
  rintro ⟨d, a₀, a₁, h₀, h₁, hg₀, hg₁⟩
  linarith

/-- Exact half-residual lower bound for the elementary handoff conflict.
If two phases demand shifts `0` and `-1`, every common frozen-tail shift leaves
at least half of the original unit defect. -/
theorem commonShift_halfResidual_lowerBound (d : ℝ) :
    (1 / 2 : ℝ) ≤ max |d| |1 + d| := by
  have htriangle : (1 : ℝ) ≤ |d| + |1 + d| := by
    calc
      (1 : ℝ) = |(1 + d) - d| := by norm_num
      _ ≤ |1 + d| + |d| := abs_sub _ _
      _ = |d| + |1 + d| := add_comm _ _
  have h₀ := le_max_left |d| |1 + d|
  have h₁ := le_max_right |d| |1 + d|
  linarith

theorem commonShift_halfResidual_attained :
    max |(-1 / 2 : ℝ)| |1 + (-1 / 2 : ℝ)| = 1 / 2 := by
  norm_num

end CycleStrataExperiment
end GameTheory
