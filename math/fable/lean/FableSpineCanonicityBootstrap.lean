/-
A persistent bounded exact spine is automatically canonical.

This file formalizes sections 2 and 3 of the note
`SOCIAL_WEIGHT_REVIEW__PERSISTENT_SPINE_QUANTIFIER_AND_CAPACITY_AUDIT`.

The checked counterexample-side all-summability theorem is stated for
`IsCanonicalExactQuittingNashBellmanSpine`, whose first field pins the value
cube to the canonical reward bound `quittingRewardBound reward`.  A spine
supplied with some other finite bound `K` therefore looks, at first sight, to
be outside its domain.  Section 2 of the note removes that apparent quantifier
gap under persistence, and section 3 composes the result.

The bootstrap.  Let `value` and `roots` satisfy the exact Bellman recursion
and exact root Nash, with `|value t i| ≤ K` for some finite `K`, and suppose
one fixed player's marginal Quit stream is nonsummable.  Each marginal is
dominated pointwise by the one-row absorption mass, so the absorption stream
is nonsummable too, hence the joint survival product vanishes from every
suffix start.  Bounded Bellman transversality, run with the common bound
`max K (quittingRewardBound reward)`, then identifies every `value t` with the
terminal value of the root schedule beginning at `t`.  That terminal value is
a subprobability mixture of finite terminal rewards, so it already lies in the
canonical reward cube.  The supplied spine is canonical after all.

The composition.  For a bounded `Fin 4` table with no uniform-equilibrium
payoff, every bounded exact Nash--Bellman spine — with an arbitrary
spine-dependent bound, not the canonical one in advance — has every marginal
Quit-hazard stream summable, hence no persistent marginal.

Scope.  No source, minimum, law, or punishment-normality hypothesis enters the
bootstrap.  Nothing here strengthens the all-summability theorem on its
canonical domain, and nothing here constructs a spine: both statements
constrain spines that are supplied.
-/
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockMonopoly
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchDeviationCap
import UniformEquilibrium.Quitting.Paths.JointSurvivalSelection
import UniformEquilibrium.Quitting.Paths.PersistentDeletedClockTwoLabel
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportHardNashBellmanSpine

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Section 2: persistence upgrades an arbitrary bound to the canonical one -/

omit [DecidableEq ι] in
/-- **Marginal to absorption.**  A player's displayed Quit probability never
exceeds the one-row absorption mass, so a nonsummable marginal forces a
nonsummable absorption stream. -/
theorem not_summable_quittingRootAbsorptionMass_of_persistentMarginal
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hpersist : ¬ Summable (quittingMarginalQuitHazard roots owner)) :
    ¬ Summable (fun time ↦ quittingRootAbsorptionMass (roots time)) := by
  intro hsummable
  refine hpersist (Summable.of_nonneg_of_le
    (fun time ↦ quittingMarginalQuitHazard_nonneg roots owner time)
    (fun time ↦ ?_) hsummable)
  exact quittingRoot_quitProbability_le_absorptionMass (roots time) owner

/-- Nonsummability is inherited by every suffix reindexing. -/
private theorem not_summable_shift (f : ℕ → ℝ) (start : ℕ)
    (hdiverges : ¬ Summable f) :
    ¬ Summable (fun offset ↦ f (start + offset)) := by
  intro hsuffix
  have hshift : Summable (fun offset ↦ f (offset + start)) := by
    simpa [Nat.add_comm] using hsuffix
  exact hdiverges ((summable_nat_add_iff start).1 hshift)

omit [DecidableEq ι] in
/-- A persistent marginal makes the joint survival product vanish from every
suffix start, which is the shape the bounded transversality theorem
consumes. -/
theorem tendsto_zero_quittingJointSurvivalWeight_of_persistentMarginal
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hpersist : ¬ Summable (quittingMarginalQuitHazard roots owner))
    (start : ℕ) :
    Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0) :=
  tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption roots start
    (not_summable_shift _ start
      (not_summable_quittingRootAbsorptionMass_of_persistentMarginal roots owner hpersist))

omit [DecidableEq ι] in
/-- **The persistent bounded exact spine is transversal.**  Under some finite
value bound, the exact Bellman recursion, and one nonsummable marginal, every
Bellman value equals the terminal value of the root schedule starting there. -/
theorem eq_quittingRootSequenceTerminalValue_of_bounded_exact_of_persistentMarginal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {bound : ℝ}
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (owner : ι)
    (hpersist : ¬ Summable (quittingMarginalQuitHazard roots owner)) :
    ∀ time, value time =
      fun who ↦ quittingRootSequenceTerminalValue reward roots who time := by
  have hcommonReward : ∀ terminal who,
      |reward terminal who| ≤ max bound (quittingRewardBound reward) :=
    fun terminal who ↦
      (abs_reward_le_quittingRewardBound reward terminal who).trans (le_max_right _ _)
  have hcommonValue : ∀ time who,
      |value time who| ≤ max bound (quittingRewardBound reward) :=
    fun time who ↦ (hvalueBound time who).trans (le_max_left _ _)
  exact
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_jointSurvival_tendsto_zero
      reward roots value
      (fun start ↦ tendsto_zero_quittingJointSurvivalWeight_of_persistentMarginal
        roots owner hpersist start)
      hcommonReward hcommonValue hpolicy

/-- **Section 2, the bootstrap.**  A bounded exact Nash--Bellman spine with an
arbitrary finite value bound and one persistent marginal satisfies the
canonical reward-cube bound, hence is an
`IsCanonicalExactQuittingNashBellmanSpine`. -/
theorem fableSpine_canonical_of_bounded_of_not_summable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {bound : ℝ}
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (owner : ι)
    (hpersist : ¬ Summable (quittingMarginalQuitHazard roots owner)) :
    IsCanonicalExactQuittingNashBellmanSpine reward value roots := by
  refine ⟨?_, hpolicy, hnash⟩
  have hterminal :=
    eq_quittingRootSequenceTerminalValue_of_bounded_exact_of_persistentMarginal
      reward value roots hvalueBound hpolicy owner hpersist
  intro time who
  rw [congrFun (hterminal time) who]
  exact abs_quittingRootSequenceTerminalValue_le reward roots who time
    (quittingRewardBound_nonneg reward) (abs_reward_le_quittingRewardBound reward)

/-! ## Section 3: the exact counterexample-side negation -/

/-- **Section 3, equation (5).**  For a bounded four-player table with no
uniform-equilibrium payoff, every marginal Quit-hazard stream of every bounded
exact Nash--Bellman spine is summable.  The spine's value bound is an
arbitrary finite `bound`; it need not be the canonical reward bound in
advance. -/
theorem finFour_all_marginalQuitHazards_summable_of_no_uniformPayoff_of_bounded_spine
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {rewardBound : ℝ} (hreward : ∀ S who, |reward S who| ≤ rewardBound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (value : ℕ → Payoff (Fin 4)) (roots : ℕ → Fin 4 → PMF Bool)
    {bound : ℝ}
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) :
    ∀ owner, Summable (quittingMarginalQuitHazard roots owner) := by
  intro owner
  by_contra hpersist
  have hcanonical := fableSpine_canonical_of_bounded_of_not_summable
    reward value roots hvalueBound hpolicy hnash owner hpersist
  exact hpersist
    (all_marginalQuitHazards_summable_of_no_uniformPayoff reward hreward hnot value roots
      hcanonical owner)

/-- The same statement in its persistence-facing form: no bounded exact
Nash--Bellman spine of a four-player table without a uniform-equilibrium
payoff has a persistent marginal. -/
theorem finFour_not_exists_persistentMarginal_of_bounded_exactSpine
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {rewardBound : ℝ} (hreward : ∀ S who, |reward S who| ≤ rewardBound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (value : ℕ → Payoff (Fin 4)) (roots : ℕ → Fin 4 → PMF Bool)
    {bound : ℝ}
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward (value (time + 1)) 0 (roots time)) :
    ¬ ∃ owner, ¬ Summable (quittingMarginalQuitHazard roots owner) := by
  rintro ⟨owner, hpersist⟩
  exact hpersist
    (finFour_all_marginalQuitHazards_summable_of_no_uniformPayoff_of_bounded_spine
      reward hreward hnot value roots hvalueBound hpolicy hnash owner)

end GameTheory
