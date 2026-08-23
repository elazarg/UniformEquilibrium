/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Capacity.InfiniteOrbitConsequences
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbitLimit

/-!
# Value convergence along infinite exact punishment-floor orbits

Inside a quitting terminal exploitability witness, every arbitrary infinite exact
punishment-floor Nash--Bellman orbit has summable absorption mass.  This
module derives the resulting limit geometry of the orbit's Bellman
annotations.

Each one-stage Bellman edge moves a bounded value coordinate by at most
twice the reward bound times the stage's absorption mass.  Summability of
those masses therefore makes every value coordinate a Cauchy sequence, so
the annotations converge coordinatewise to a single payoff vector.

The limit inherits three constraints.  It stays in the canonical compact
reward box.  It dominates the behavioral punishment floor, because every
finite truncation of the orbit is an exact punishment-floor prefix.  And it
dominates every player's own solo quitting reward: at each stage the pure
Quit endpoint is within twice the reward bound times the opponent-absorption
hazard of the solo reward, exact root Nash keeps that endpoint below the
successor annotation, and the opponent hazard vanishes because it is
dominated by the summable joint absorption mass.  The one-shot quit
deviation thus survives to the limit, which is simultaneously individually
rational and solo-undercut-free.

The values here are prescribed Bellman annotations, not realized payoffs of
any strategy profile.  No claim is made that the limit payoff is achieved by
play; identifying annotations with realized continuation payoffs is
precisely the separate realization problem.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness

/-- Every player's opponent-absorption hazard vanishes along every arbitrary
infinite exact punishment-floor orbit, being squeezed by the joint
absorption mass. -/
theorem infiniteOrbit_opponentAbsorptionMass_tendsto_zero
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) (who : ι) :
    Tendsto (fun time =>
        quittingRootOpponentAbsorptionMass (orbit.roots time) who)
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun time => quittingOpponentClockCharge_nonneg orbit.roots who time
  · exact fun time =>
      quittingRootOpponentAbsorptionMass_le_absorptionMass
        (orbit.roots time) who
  · exact witness.infiniteOrbit_absorptionMass_tendsto_zero orbit

/-- Coordinatewise absolute increments of the orbit annotations are
summable, by comparison with the summable absorption masses. -/
theorem infiniteOrbit_abs_value_succ_sub_summable
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) (who : ι) :
    Summable (fun time =>
      |orbit.value (time + 1) who - orbit.value time who|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun time => orbit.abs_value_succ_sub_le_two_mul_absorptionMass time who)
    ((witness.infiniteOrbit_absorptionMass_summable orbit).mul_left
      (2 * quittingRewardBound reward))

/-- **All-orbits value limit.**  Along every arbitrary infinite exact
punishment-floor orbit of a terminal exploitability witness, the Bellman annotations
converge coordinatewise to a single payoff vector.  The limit lies in the
canonical compact reward box, dominates the behavioral punishment floor, and
dominates every player's own solo reward: the one-shot quit deviation
survives passage to the limit because opponent absorption vanishes.

The annotations are prescribed Bellman values, not realized payoffs of any
strategy profile; no realization claim is made about the limit. -/
theorem infiniteOrbit_exists_value_limit
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    ∃ limit : Payoff ι,
      (∀ who, Tendsto (fun time => orbit.value time who) atTop
        (nhds (limit who))) ∧
      limit ∈ quittingPunishmentFloorForwardCarrier reward ∧
      (∀ who, quittingPunishmentValue reward who ≤ limit who) ∧
      (∀ who, quittingSoloReward reward who who ≤ limit who) := by
  have hconverge : ∀ who : ι, ∃ coordinateLimit : ℝ,
      Tendsto (fun time => orbit.value time who) atTop
        (nhds coordinateLimit) := by
    intro who
    have hdist : Summable (fun time =>
        dist (orbit.value time who) (orbit.value (time + 1) who)) := by
      simpa [Real.dist_eq, abs_sub_comm] using
        witness.infiniteOrbit_abs_value_succ_sub_summable orbit who
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  choose limit hlimit using hconverge
  refine ⟨limit, hlimit, ?_, ?_, ?_⟩
  · have hbox : ∀ time, orbit.value time ∈ Set.Icc
        (fun _ : ι => -quittingRewardBound reward)
        (fun _ : ι => quittingRewardBound reward) :=
      fun time => orbit.value_mem time
    have hlower : ∀ who, -quittingRewardBound reward ≤ limit who :=
      fun who => ge_of_tendsto' (hlimit who)
        (fun time => (hbox time).1 who)
    have hupper : ∀ who, limit who ≤ quittingRewardBound reward :=
      fun who => le_of_tendsto' (hlimit who)
        (fun time => (hbox time).2 who)
    exact Set.mem_Icc.mpr ⟨hlower, hupper⟩
  · exact fun who => ge_of_tendsto' (hlimit who)
      (fun time => orbit.punishmentValue_le_value time who)
  · intro who
    have hshift : Tendsto (fun time => orbit.value (time + 1) who) atTop
        (nhds (limit who)) := (hlimit who).comp (tendsto_add_atTop_nat 1)
    have hhazard : Tendsto (fun time =>
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (orbit.roots time) who)
        atTop (nhds 0) := by
      simpa using
        (witness.infiniteOrbit_opponentAbsorptionMass_tendsto_zero orbit
          who).const_mul (2 * quittingRewardBound reward)
    have hlower : Tendsto (fun time =>
        quittingSoloReward reward who who -
          2 * quittingRewardBound reward *
            quittingRootOpponentAbsorptionMass (orbit.roots time) who)
        atTop (nhds (quittingSoloReward reward who who)) := by
      simpa using tendsto_const_nhds.sub hhazard
    exact le_of_tendsto_of_tendsto' hlower hshift
      (fun time =>
        orbit.soloReward_sub_opponentHazard_le_value_succ time who)

/-!
# The all-Continue Nash--Bellman self-loop at the orbit limit

The quantitative variation bound and the structural self-loop are endpoints of
the same exact-orbit limit argument.  The annotations are prescribed Bellman
values, not realized payoffs of any strategy profile.
-/

/- Quantitative total variation along every arbitrary infinite exact
punishment-floor orbit. -/
theorem infiniteOrbit_tsum_abs_value_succ_sub_le
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) (who : ι) :
    ∑' time, |orbit.value (time + 1) who - orbit.value time who| ≤
      2 * quittingRewardBound reward *
        quittingPunishmentFloorPrefixChargeBound reward := by
  have h2M : (0 : ℝ) ≤ 2 * quittingRewardBound reward := by
    linarith [quittingRewardBound_nonneg reward]
  apply Real.tsum_le_of_sum_range_le (fun time => abs_nonneg _)
  intro horizon
  calc
    ∑ time ∈ Finset.range horizon,
        |orbit.value (time + 1) who - orbit.value time who| ≤
      ∑ time ∈ Finset.range horizon,
        2 * quittingRewardBound reward *
          quittingRootAbsorptionMass (orbit.roots time) :=
        Finset.sum_le_sum fun time _ =>
          orbit.abs_value_succ_sub_le_two_mul_absorptionMass time who
    _ = 2 * quittingRewardBound reward *
        orbit.partialAbsorption horizon := by
        simp only [QuittingPunishmentFloorInfiniteOrbit.partialAbsorption,
          Finset.mul_sum]
    _ ≤ 2 * quittingRewardBound reward *
        quittingPunishmentFloorPrefixChargeBound reward :=
        mul_le_mul_of_nonneg_left
          (witness.infiniteOrbit_partialAbsorption_le_prefixChargeBound
            orbit horizon) h2M

/-! **All-Continue Nash--Bellman self-loop at the limit.**  Along every
arbitrary infinite exact punishment-floor orbit of a terminal exploitability
witness, the coordinatewise limit of the Bellman annotations, paired with the
all-Continue simplex root, carries an exact Nash--Bellman edge from itself to
itself.  The limit is an annotation, not a realized strategy payoff. -/
theorem infiniteOrbit_exists_selfLoop_limit
    (witness : QuittingTerminalExploitabilityWitness reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    ∃ limit : Payoff ι,
      (∀ who, Tendsto (fun time => orbit.value time who) atTop
        (nhds (limit who))) ∧
      limit ∈ quittingPunishmentFloorForwardCarrier reward ∧
      (∀ who, quittingPunishmentValue reward who ≤ limit who) ∧
      IsQuittingNashBellmanEdge reward
        (limit, quittingAllContinueSimplexRoot)
        (limit, quittingAllContinueSimplexRoot) := by
  obtain ⟨limit, hlimit, hcarrier, hfloor, hsolo⟩ :=
    witness.infiniteOrbit_exists_value_limit orbit
  refine ⟨limit, hlimit, hcarrier, hfloor, ?_⟩
  constructor
  · change limit = quittingRootSuccessorPayoff reward limit
      (quittingRootOfSimplex quittingAllContinueSimplexRoot)
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      quittingRootSuccessorPayoff_allContinueRoot_eq]
  · change IsεQuittingRootEndpointNash reward limit 0
      (quittingRootOfSimplex quittingAllContinueSimplexRoot)
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    exact quittingAllContinueRoot_isZeroNash_of_singleton_le reward limit
      hsolo

end QuittingTerminalExploitabilityWitness

end GameTheory
