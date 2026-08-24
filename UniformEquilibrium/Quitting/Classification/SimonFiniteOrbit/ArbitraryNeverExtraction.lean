/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.ReachedPrefixCompactification
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import UniformEquilibrium.Quitting.Classification.Existence.WellSupportedAbsorbingSequence
import UniformEquilibrium.Quitting.Paths.JointSurvivalSelection

/-!
# Reached-prefix extraction with an arbitrary payoff at never

The quitting-game model used by Ashkenazi--Golan--Krasikov--Rainer--Solan
allows a playerwise payoff when play never terminates.  The production
reached-prefix extraction uses the repository normalization in which that
payoff is zero.  This file gives the quantified semantic adapter between the
two models and then applies the checked finite-prefix compactification.

The translation subtracts each player's never payoff from all of that
player's terminal rewards.  It changes every prescribed and unilaterally
deviating payoff by the same constant, so it preserves the full behavioral
approximate-Nash inequality at the same error.  Thus this is not a stationary
or pure-time restriction.

The resulting alternative is deliberately weaker than the three branches of
AGKRS Theorem 3.4.  Its low-survival disjunct still needs a source-matched
stationary or instant-punishment adapter.  Its compact disjunct is an exact
support-Bellman spine, but the selected values have not been identified with
the terminal payoffs of its infinite suffixes and the spine has not been
shown completely absorbing.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Approximate-equilibrium existence for a quitting payoff table with its
explicit payoff at never, using arbitrary behavioral profiles and deviations.
-/
def QuittingPayoffTable.ApproximateEquilibriumExistence
    (table : QuittingPayoffTable ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ profile : (quittingGame table.terminal).BehaviorProfile,
    (quittingGame table.terminal).IsεAsymptoticNash
      table.terminalPayoff ε profile

/-- Arbitrary-never approximate-equilibrium existence is exactly the
root-sequence existence statement for the normalized zero-never reward.

Both directions retain arbitrary behavioral deviations: the first equivalence
is the table translation, and the second is the checked live-root adapter.
-/
theorem QuittingPayoffTable.approximateEquilibriumExistence_iff_zeroNever
    (table : QuittingPayoffTable ι) :
    table.ApproximateEquilibriumExistence ↔
      QuittingApproximateEquilibriumExistence table.zeroNeverReward := by
  rw [quittingApproximateEquilibriumExistence_iff_behavior]
  constructor
  · intro hexists ε hε
    obtain ⟨profile, hnash⟩ := hexists ε hε
    exact ⟨profile, (table.isεAsymptoticNash_iff ε profile).1 hnash⟩
  · intro hexists ε hε
    obtain ⟨profile, hnash⟩ := hexists ε hε
    exact ⟨profile, (table.isεAsymptoticNash_iff ε profile).2 hnash⟩

end QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A bounded exact support-Bellman spine becomes an actual well-supported
absorbing sequence once its joint survival vanishes after every restart.

The all-tail survival condition does two jobs: its time-zero instance is
complete absorption, and Bellman uniqueness identifies every displayed
successor value with the corresponding root-sequence terminal payoff.  This
is the exact semantic bridge from the compact spine to the pointwise S.3
witness; it does not assert that compactification supplies the survival
condition.
-/
theorem
    quittingWellSupportedAbsorbingSequenceAt_of_boundedSupportBellmanSpine_of_jointSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {M δ : ℝ}
    (hsurvival : ∀ start,
      Filter.Tendsto (quittingJointSurvivalWeight roots start)
        Filter.atTop (nhds 0))
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ time who, |value time who| ≤ M)
    (hbellman : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hsupport : ∀ time, IsQuittingRootSupportApproxNash reward
      (value (time + 1)) δ (roots time)) :
    QuittingWellSupportedAbsorbingSequenceAt reward δ := by
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_jointSurvival_tendsto_zero
      reward roots value hsurvival hreward hvalue hbellman
  refine ⟨roots, ?_, ?_⟩
  · unfold IsCompletelyAbsorbing
    have heq : quittingSurvivalPrefix roots =
        quittingJointSurvivalWeight roots 0 := by
      funext fuel
      rw [quittingJointSurvivalWeight_eq_prod]
      simp [quittingSurvivalPrefix]
    rw [heq]
    exact hsurvival 0
  · intro time
    have htail : value (time + 1) =
        quittingRootSequenceTailVector reward roots (time + 1) := by
      funext who
      exact congrFun (hselected (time + 1)) who
    rw [← htail]
    exact hsupport time

namespace QuittingLCPClassification

/-- **Source-faithful compactification from the AGKRS hypothesis.**  At every
positive support tolerance and reach floor, arbitrary-never behavioral
approximate equilibria produce either an actual normalized source prefix
whose survival crosses below the floor, or a uniformly payoff-bounded exact
support-Bellman spine.

The reward bound is canonical.  The two residual semantic obligations in the
module documentation are not conclusions of this theorem.
-/
theorem QuittingPayoffTable.lowSurvivalPrefix_or_exists_boundedSupportBellmanSpine
    (table : QuittingPayoffTable ι)
    (hequilibrium : table.ApproximateEquilibriumExistence)
    (δ u : ℝ) (hδ : 0 < δ) (hu : 0 < u) :
    (∃ horizon,
      QuittingLowSurvivalApproximatePrefixAt table.zeroNeverReward u
        (u * quittingSimonReachedPrefixThreshold δ *
          quittingSimonReachedPrefixDisplacement
            (ι := ι) (quittingRewardBound table.zeroNeverReward) δ horizon / 2)
        horizon) ∨
      ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
        (∀ time who,
          |value time who| ≤ quittingRewardBound table.zeroNeverReward) ∧
        (∀ time, value time = quittingRootSuccessorPayoff table.zeroNeverReward
          (value (time + 1)) (roots time)) ∧
        ∀ time, IsQuittingRootSupportApproxNash table.zeroNeverReward
          (value (time + 1)) δ (roots time) := by
  apply
    lowSurvivalPrefix_or_exists_bounded_supportBellmanSpine_of_approximateEquilibriumExistence
      table.zeroNeverReward
      ((table.approximateEquilibriumExistence_iff_zeroNever).1 hequilibrium)
      (quittingRewardBound table.zeroNeverReward) δ u
      (quittingRewardBound_nonneg table.zeroNeverReward) hδ hu
  exact abs_reward_le_quittingRewardBound table.zeroNeverReward

end QuittingLCPClassification
end GameTheory
