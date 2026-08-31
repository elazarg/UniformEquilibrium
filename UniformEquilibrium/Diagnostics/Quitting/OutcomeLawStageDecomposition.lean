/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration
import UniformEquilibrium.Quitting.Paths.LiveMassRecurrence
import UniformEquilibrium.Quitting.Paths.LiveTail
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.Stationary.LiveMass

/-
Stage decomposition of the terminal outcome law of a quitting game.

A behavior profile in a quitting game produces one terminal outcome law: a
mass for each finite quitting coalition and a residual Never mass.  Each of
the three coordinates of that law is a convergent series of per-date atoms,
and this file records the three summation identities in `HasSum` form.

A coalition coordinate is the chronological series of its stage atoms: the
probability of surviving to date `t` and absorbing at exactly that coalition
there.  Absorption at a coalition is monotone in the date and its finite
prefixes are exactly its prefix sums, so the limit is the sum.

The Never coordinate is complementary rather than additive, and its series is
the telescope of the survival sequence.  The stopping recurrence factors
`liveMass (t + 1)` as `liveMass t` times the stage's joint all-Continue mass,
which is the stationary all-Continue mass of the profile's live root at that
date.  Absorption at a root is one minus that mass, so each date contributes
`liveMass t - liveMass (t + 1)` and the prefix sums are `1 - liveMass n`.
Passing to the limit turns the total into one minus the Never mass.

The singleton specialization is the coalition series read through the exact
stage factorization: the singleton coordinate is the survival-weighted series
of the live root's exact singleton coalition masses.  This is the form a
per-player consumer reads, since it exposes the same live-root row that
carries a player's own quit rate.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The coalition coordinates -/

/-- A coalition coordinate of the terminal law is the sum of its chronological
stage atoms. -/
theorem terminalOutcomeChronology_hasSum_stageCoalitionMass_absorbedMassLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    HasSum (fun time => quittingStageCoalitionMass reward profile time terminal)
      (quittingAbsorbedMassLimit reward profile terminal) :=
  hasSum_quittingStageCoalitionMass reward profile terminal

/-- The same identity read off the terminal outcome law. -/
theorem terminalOutcomeChronology_terminalOutcomeMass_some_eq_tsum_stage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingTerminalOutcomeMass reward profile (some terminal) =
      ∑' time, quittingStageCoalitionMass reward profile time terminal := by
  have hlaw : quittingTerminalOutcomeMass reward profile (some terminal) =
      quittingAbsorbedMassLimit reward profile terminal := rfl
  rw [hlaw]
  exact
    ((terminalOutcomeChronology_hasSum_stageCoalitionMass_absorbedMassLimit reward profile
      terminal).tsum_eq).symm

/-! ## The Never coordinate -/

omit [DecidableEq ι] in
/-- The joint all-Continue mass of a stage is the stationary all-Continue mass
of the profile's live root at that stage. -/
private theorem terminalOutcomeChronology_jointContinueMass_eq_stationaryContinueMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingJointContinueMass reward profile time =
      quittingStationaryContinueMass
        (quittingProfileLiveRoot reward profile time) := by
  rw [quittingJointContinueMass_eq_product,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  rfl

omit [DecidableEq ι] in
/-- The per-date telescope step: the survival-weighted absorption mass of a
date is exactly the survival drop across that date. -/
private theorem terminalOutcomeChronology_liveMass_mul_rootAbsorptionMass_eq_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile time *
        quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward profile time) =
      quittingLiveMass reward profile time -
        quittingLiveMass reward profile (time + 1) := by
  have hsucc : quittingLiveMass reward profile (time + 1) =
      quittingLiveMass reward profile time *
        quittingStationaryContinueMass
          (quittingProfileLiveRoot reward profile time) := by
    rw [quittingLiveMass_succ,
      terminalOutcomeChronology_jointContinueMass_eq_stationaryContinueMass]
  rw [hsucc]
  unfold quittingRootAbsorptionMass
  ring

omit [DecidableEq ι] in
/-- Every prefix sum of the survival-weighted absorption series is the
complement of the survival probability at the cutoff. -/
private theorem terminalOutcomeChronology_sum_range_liveMass_mul_rootAbsorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    ∑ time ∈ Finset.range cutoff, quittingLiveMass reward profile time *
        quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward profile time) =
      1 - quittingLiveMass reward profile cutoff := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih,
        terminalOutcomeChronology_liveMass_mul_rootAbsorptionMass_eq_sub]
      ring

omit [DecidableEq ι] in
/-- The survival-weighted root absorption masses sum to the complement of the
Never coordinate of the terminal outcome law. -/
theorem terminalOutcomeChronology_hasSum_liveMass_mul_absorption_one_sub_neverMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    HasSum (fun time => quittingLiveMass reward profile time *
        quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward profile time))
      (1 - quittingTerminalOutcomeMass reward profile none) := by
  have hnonneg : ∀ time : ℕ, 0 ≤ quittingLiveMass reward profile time *
      quittingRootAbsorptionMass
        (quittingProfileLiveRoot reward profile time) :=
    fun time => mul_nonneg (quittingLiveMass_nonneg reward profile time)
      (quittingRootAbsorptionMass_nonneg _)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hlimit :
      Tendsto (fun cutoff => 1 - quittingLiveMass reward profile cutoff) atTop
        (𝓝 (1 - quittingTerminalOutcomeMass reward profile none)) :=
    Filter.Tendsto.const_sub 1 (tendsto_quittingLiveMass reward profile)
  simpa only [terminalOutcomeChronology_sum_range_liveMass_mul_rootAbsorptionMass reward profile]
    using hlimit

/-! ## The singleton coordinates -/

/-- The singleton coordinate of the terminal law is the survival-weighted
series of the live root's exact singleton coalition masses. -/
theorem terminalOutcomeChronology_hasSum_liveMass_mul_singletonCoalition_singletonLawMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    HasSum (fun time => quittingLiveMass reward profile time *
        quittingRootCoalitionMass (quittingProfileLiveRoot reward profile time)
          (quittingSingletonTerminal who).val)
      (quittingTerminalOutcomeMass reward profile
        (some (quittingSingletonTerminal who))) := by
  have hlaw : quittingTerminalOutcomeMass reward profile
      (some (quittingSingletonTerminal who)) =
      quittingAbsorbedMassLimit reward profile
        (quittingSingletonTerminal who) := rfl
  rw [hlaw]
  simpa only [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
    using terminalOutcomeChronology_hasSum_stageCoalitionMass_absorbedMassLimit reward profile
      (quittingSingletonTerminal who)

end GameTheory
