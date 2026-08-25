/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbitLimit
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbitSegment
import UniformEquilibrium.Quitting.Projective.CumulativeChargeNearReturn

/-!
# Cumulative-charge or all-Continue port for exact floor orbits

If the total absorption charge of an infinite exact punishment-floor orbit
diverges, compact recurrence supplies returned finite blocks with a fixed
cumulative charge and hence a uniform-equilibrium payoff.  If it is summable,
the bounded Bellman annotations converge and the roots converge
coordinatewise to all Continue; the limit is an exact floor-admissible
all-Continue self-loop.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingPunishmentFloorInfiniteOrbit

/-- Nonsummable absorption along one exact floor orbit gives cumulative-charge
payoff near-returns and therefore a uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_not_summable_absorption
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (hdiverges : ¬Summable (fun time =>
      quittingRootAbsorptionMass (orbit.roots time))) :
    ∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  letI : Nonempty iota := by
    rcases isEmpty_or_nonempty iota with hempty | hnonempty
    · letI : IsEmpty iota := hempty
      exfalso
      apply hdiverges
      have hzero : (fun time =>
          quittingRootAbsorptionMass (orbit.roots time)) = fun _ => 0 := by
        funext time
        have hroot : orbit.roots time = quittingAllContinueRoot := by
          funext who
          exact isEmptyElim who
        rw [hroot, quittingRootAbsorptionMass_allContinueRoot]
      rw [hzero]
      exact summable_zero
    · exact hnonempty
  apply quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos
    reward
  intro error herror
  have hhalfError : 0 < error / 2 := by linarith
  let charge : ℕ → ℝ := fun time =>
    quittingRootAbsorptionMass (orbit.roots time)
  obtain ⟨first, second, hfirstSecond, hclose, hgap⟩ :=
    Math.exists_close_pair_with_large_charge_gap_of_compact
      (quittingPunishmentFloorForwardCarrier reward)
      (quittingPunishmentFloorForwardCarrier_isCompact reward)
      orbit.value orbit.value_mem charge
      (fun time => orbit.absorptionMass_nonneg time) hdiverges
      (error / 2) 1 hhalfError
  have hfirstLe : first ≤ second := hfirstSecond.le
  let horizon := second - first
  have hhorizon : 0 < horizon := by
    dsimp only [horizon]
    omega
  let segment := orbit.toFiniteSegment first horizon
  have hsegmentCharge : 1 ≤ segment.charge := by
    have hsumSplit :
        (∑ time ∈ Finset.range second, charge time) =
          (∑ time ∈ Finset.range first, charge time) +
            ∑ offset ∈ Finset.range horizon, charge (first + offset) := by
      simpa [horizon, Nat.add_sub_of_le hfirstLe] using
        (Finset.sum_range_add charge first (second - first))
    rw [hsumSplit] at hgap
    have hblock : 1 ≤
        ∑ offset ∈ Finset.range horizon, charge (first + offset) := by
      linarith
    simpa [segment, QuittingPunishmentFloorFinitePrefix.charge,
      QuittingPunishmentFloorInfiniteOrbit.toFiniteSegment, charge] using
      hblock
  have hsegmentClose : ∀ who,
      |segment.value 0 who - segment.value segment.horizon who| ≤
        error / 2 := by
    intro who
    have hcoordinate :
        dist (orbit.value first who) (orbit.value second who) < error / 2 :=
      lt_of_le_of_lt (dist_le_pi_dist _ _ who) hclose
    have hend : first + horizon = second := by
      dsimp only [horizon]
      omega
    have hsegmentEnd : segment.value segment.horizon = orbit.value second := by
      change orbit.value (first + horizon) = orbit.value second
      rw [hend]
    rw [show segment.value 0 = orbit.value first by simp [segment],
      hsegmentEnd]
    simpa [Real.dist_eq] using hcoordinate.le
  apply exists_singleSeamProjectiveLasso_of_floorPrefix_cumulativePayoffNearReturn
    segment 1 (error / 2) error (by norm_num) hsegmentCharge
      (by linarith)
  · norm_num [div_eq_mul_inv]
  · exact hsegmentClose

/-- The complete summable side of an exact floor orbit. -/
structure SummableChargeAllContinuePort
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) where
  limit : Payoff iota
  absorption_summable : Summable (fun time =>
    quittingRootAbsorptionMass (orbit.roots time))
  value_tendsto : ∀ who,
    Tendsto (fun time => orbit.value time who) atTop (nhds (limit who))
  quit_tendsto_zero : ∀ who,
    Tendsto (fun time => (orbit.roots time who true).toReal)
      atTop (nhds 0)
  continue_tendsto_one : ∀ who,
    Tendsto (fun time => (orbit.roots time who false).toReal)
      atTop (nhds 1)
  limit_mem : limit ∈ quittingPunishmentFloorForwardCarrier reward
  punishment_le : ∀ who, quittingPunishmentValue reward who ≤ limit who
  singleton_le : ∀ who,
    reward (quittingSingletonTerminal who) who ≤ limit who
  selfLoop : IsQuittingNashBellmanEdge reward
    (limit, quittingAllContinueSimplexRoot)
    (limit, quittingAllContinueSimplexRoot)

/-- Summable absorption forces convergence to an exact floor-safe
all-Continue self-loop. -/
theorem nonempty_summableChargeAllContinuePort_of_summable_absorption
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (hsummable : Summable (fun time =>
      quittingRootAbsorptionMass (orbit.roots time))) :
    Nonempty (SummableChargeAllContinuePort orbit) := by
  have hvariation : ∀ who, Summable (fun time =>
      |orbit.value (time + 1) who - orbit.value time who|) := by
    intro who
    exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun time => orbit.abs_value_succ_sub_le_two_mul_absorptionMass time who)
      (hsummable.mul_left (2 * quittingRewardBound reward))
  have hconverge : ∀ who : iota, ∃ coordinateLimit : ℝ,
      Tendsto (fun time => orbit.value time who) atTop
        (nhds coordinateLimit) := by
    intro who
    have hdist : Summable (fun time =>
        dist (orbit.value time who) (orbit.value (time + 1) who)) := by
      simpa [Real.dist_eq, abs_sub_comm] using hvariation who
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  choose limit hlimit using hconverge
  have habsorptionZero : Tendsto (fun time =>
      quittingRootAbsorptionMass (orbit.roots time)) atTop (nhds 0) :=
    hsummable.tendsto_atTop_zero
  have hquit : ∀ who, Tendsto
      (fun time => (orbit.roots time who true).toReal) atTop (nhds 0) := by
    intro who
    apply squeeze_zero
    · exact fun time => orbit.quitProbability_nonneg time who
    · exact fun time => orbit.quitProbability_le_absorptionMass time who
    · exact habsorptionZero
  have hcontinue : ∀ who, Tendsto
      (fun time => (orbit.roots time who false).toReal) atTop (nhds 1) := by
    intro who
    have hidentity : (fun time => (orbit.roots time who false).toReal) =
        fun time => 1 - (orbit.roots time who true).toReal := by
      funext time
      linarith [quittingRoot_continueProbability_add_quitProbability
        (orbit.roots time) who]
    rw [hidentity]
    simpa using tendsto_const_nhds.sub (hquit who)
  have hcarrier : limit ∈ quittingPunishmentFloorForwardCarrier reward := by
    have hbox := fun time => orbit.value_mem time
    constructor
    · intro who
      exact ge_of_tendsto' (hlimit who) (fun time => (hbox time).1 who)
    · intro who
      exact le_of_tendsto' (hlimit who) (fun time => (hbox time).2 who)
  have hfloor : ∀ who, quittingPunishmentValue reward who ≤ limit who :=
    fun who => ge_of_tendsto' (hlimit who)
      (fun time => orbit.punishmentValue_le_value time who)
  have hsolo : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ limit who := by
    intro who
    have hshift : Tendsto (fun time => orbit.value (time + 1) who) atTop
        (nhds (limit who)) := (hlimit who).comp (tendsto_add_atTop_nat 1)
    have hopponent : Tendsto (fun time =>
        quittingRootOpponentAbsorptionMass (orbit.roots time) who)
        atTop (nhds 0) := by
      apply squeeze_zero
      · exact fun time => quittingOpponentClockCharge_nonneg orbit.roots who time
      · exact fun time =>
          quittingRootOpponentAbsorptionMass_le_absorptionMass
            (orbit.roots time) who
      · exact habsorptionZero
    have hlower : Tendsto (fun time =>
        quittingSoloReward reward who who -
          2 * quittingRewardBound reward *
            quittingRootOpponentAbsorptionMass (orbit.roots time) who)
        atTop (nhds (quittingSoloReward reward who who)) := by
      have hscaled := hopponent.const_mul (2 * quittingRewardBound reward)
      simpa using tendsto_const_nhds.sub hscaled
    exact le_of_tendsto_of_tendsto' hlower hshift
      (fun time => orbit.soloReward_sub_opponentHazard_le_value_succ time who)
  have hselfLoop : IsQuittingNashBellmanEdge reward
      (limit, quittingAllContinueSimplexRoot)
      (limit, quittingAllContinueSimplexRoot) := by
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
  exact ⟨{
    limit := limit
    absorption_summable := hsummable
    value_tendsto := hlimit
    quit_tendsto_zero := hquit
    continue_tendsto_one := hcontinue
    limit_mem := hcarrier
    punishment_le := hfloor
    singleton_le := hsolo
    selfLoop := hselfLoop }⟩

/-- Exact charge-or-stall dichotomy for every infinite punishment-floor
orbit. -/
theorem uniformPayoff_or_summableChargeAllContinuePort
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    (∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (SummableChargeAllContinuePort orbit) := by
  by_cases hsummable : Summable (fun time =>
      quittingRootAbsorptionMass (orbit.roots time))
  · exact Or.inr
      (nonempty_summableChargeAllContinuePort_of_summable_absorption
        orbit hsummable)
  · exact Or.inl
      (orbit.exists_uniformEquilibriumPayoff_of_not_summable_absorption
        hsummable)

end QuittingPunishmentFloorInfiniteOrbit

end GameTheory
