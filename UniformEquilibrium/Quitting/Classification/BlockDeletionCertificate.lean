/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.BlockDeletion
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile
import UniformEquilibrium.Quitting.Cycles.SoloPeriodicBlockCompiler

/-!
# Transporting a compiled survivor equilibrium through block deletion

`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean` carries a
uniform-equilibrium payoff of the survivor table back to the original table
without moving the survivors' coordinates.  The periodic-profile compilers of
`UniformEquilibrium/Quitting/Cycles/SoloPeriodicBlockCompiler.lean` and
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` produce such a
payoff in displayed form: the origin row of a finite value path certified by a
list of scalar obligations.

Composing them gives the original game a uniform-equilibrium payoff whose
survivor coordinates are the certificate's displayed origin row, an explicit
rational function of the table entries and hazards appearing in the
obligations.  Only the deleted players' coordinates remain implicit; they are a
subsequential limit of never-quit payoffs.

## Absorption

A certificate asserts one phase of positive absorption, so the periodic profile
it compiles has per-stage absorption bounded below along its whole orbit:
`quittingRootAbsorptionMass_quittingCyclicContinuationBlockProfile_soloPeriodicBlock`
and its block-certificate counterpart compute that absorption exactly, and
`pos_of_forall_absorptionMass_le_soloPeriodicBlockProfile` records that no
bound on it can be nonpositive.  A screen whose hypothesis asks a single player
deletion for survivor equilibria of arbitrarily small per-stage absorption
therefore cannot be fed by these compilers: their profiles absorb at a rate
fixed by the certificate, not by the accuracy demanded.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open SoloPeriodicBlockCompiler

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Compiled survivor payoffs -/

/-- **Block deletion over a certified single-quitter periodic survivor
profile.**  If every member of `B` passes the block gate and the survivor table
carries a single-quitter periodic certificate, the original game has a
uniform-equilibrium payoff whose value at every survivor is the certificate's
displayed origin row.

The deleted players' coordinates are not displayed: they are a subsequential
limit of never-quit payoffs of lifted approximate equilibria. -/
theorem exists_uniformEquilibriumPayoff_eq_soloPeriodicValue_of_blockDispensable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hgate : ∀ d ∈ B, QuittingBlockDispensable reward B d)
    {n : ℕ} {w : Fin (n + 1) → QuittingBlockSurvivor B}
    {marginal : Fin (n + 1) → PMF Bool}
    {value : Fin (n + 2) → Payoff (QuittingBlockSurvivor B)}
    (hcert : IsSoloPeriodicCertificate (quittingDeleteBlockReward reward B) w
      marginal value) :
    ∃ payoff : Payoff ι,
      (∀ who : QuittingBlockSurvivor B, payoff who.1 = value 0 who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable reward B
    hgate (value 0) (isUniformEquilibriumPayoff_of_soloPeriodicBlock hcert)

/-- **Block deletion over a certified block-periodic survivor profile.**  If
every member of `B` passes the block gate and the survivor table carries a
block certificate, the original game has a uniform-equilibrium payoff whose
value at every survivor is the certificate's displayed origin row.

Unlike the single-quitter certificate, the block certificate lets every
survivor randomize at every phase, so its obligations range over all coalition
masses of the survivor table. -/
theorem exists_uniformEquilibriumPayoff_eq_blockCertificateValue_of_blockDispensable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hgate : ∀ d ∈ B, QuittingBlockDispensable reward B d)
    {m : ℕ} {hazard : Fin (m + 1) → QuittingBlockSurvivor B → ℝ}
    {U : Fin (m + 2) → Payoff (QuittingBlockSurvivor B)}
    (hcert : IsQuittingBlockCertificate (quittingDeleteBlockReward reward B)
      hazard U) :
    ∃ payoff : Payoff ι,
      (∀ who : QuittingBlockSurvivor B, payoff who.1 = U 0 who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable reward B
    hgate (U 0) (isUniformEquilibriumPayoff_of_isQuittingBlockCertificate hcert)

/-! ## The absorption rate of a compiled periodic profile -/

/-- Every phase of a nonempty finite cycle is reached from every starting
phase. -/
theorem exists_quittingCyclicOrbit_eq {K : ℕ} (phase target : Fin K) :
    ∃ steps : ℕ, quittingCyclicOrbit phase steps = target := by
  refine ⟨target.1 + (K - phase.1), Fin.ext ?_⟩
  have hphase : phase.1 < K := phase.isLt
  have hsum : phase.1 + (target.1 + (K - phase.1)) = target.1 + K := by omega
  show (phase.1 + (target.1 + (K - phase.1))) % K = target.1
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt target.isLt]

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {n : ℕ}

/-- **The absorption rate of a compiled single-quitter periodic profile.**  At
every stage the profile absorbs with exactly the quitting probability of the
phase then scheduled. -/
theorem quittingRootAbsorptionMass_quittingCyclicContinuationBlockProfile_soloPeriodicBlock
    (w : Fin (n + 1) → ι) (marginal : Fin (n + 1) → PMF Bool)
    (value : Fin (n + 2) → Payoff ι) (phase : Fin (n + 1)) (time : ℕ) :
    quittingRootAbsorptionMass (quittingProfileLiveRoot reward
        (quittingCyclicContinuationBlockProfile reward n
          (soloPeriodicBlock w marginal value) phase) time) =
      (marginal (quittingCyclicOrbit phase time) true).toReal := by
  rw [quittingCyclicContinuationBlockProfile,
    quittingProfileLiveRoot_cyclicBehaviorProfile, quittingCyclicRootSequence,
    quittingCyclicContinuationBlockCycle,
    quittingRootOfSimplex_soloPeriodicBlock,
    quittingRootAbsorptionMass_soloMixedRoot]

/-- **No vanishing absorption from a single-quitter certificate.**  A bound on
the per-stage absorption of the profile compiled from a certified
single-quitter periodic block is positive, because the certificate schedules a
phase that quits with positive probability and the profile returns to that
phase from every starting phase. -/
theorem pos_of_forall_absorptionMass_le_soloPeriodicBlockProfile
    {w : Fin (n + 1) → ι} {marginal : Fin (n + 1) → PMF Bool}
    {value : Fin (n + 2) → Payoff ι}
    (hcert : IsSoloPeriodicCertificate reward w marginal value)
    (phase : Fin (n + 1)) {bound : ℝ}
    (hbound : ∀ time, quittingRootAbsorptionMass (quittingProfileLiveRoot reward
      (quittingCyclicContinuationBlockProfile reward n
        (soloPeriodicBlock w marginal value) phase) time) ≤ bound) :
    0 < bound := by
  obtain ⟨k, hk⟩ := hcert.absorb
  obtain ⟨time, htime⟩ := exists_quittingCyclicOrbit_eq phase k
  have hstage :=
    quittingRootAbsorptionMass_quittingCyclicContinuationBlockProfile_soloPeriodicBlock
      (reward := reward) w marginal value phase time
  rw [htime] at hstage
  have := hbound time
  linarith [hstage ▸ this]

variable {m : ℕ} {hazard : Fin (m + 1) → ι → ℝ}

omit [DecidableEq ι] in
/-- **The absorption rate of a compiled block-periodic profile.**  At every
stage the profile absorbs with exactly the joint quitting probability of the
phase then scheduled. -/
theorem quittingRootAbsorptionMass_quittingCyclicContinuationBlockProfile_quittingBlockPath
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    (U : Fin (m + 2) → Payoff ι) (phase : Fin (m + 1)) (time : ℕ) :
    quittingRootAbsorptionMass (quittingProfileLiveRoot reward
        (quittingCyclicContinuationBlockProfile reward m
          (quittingBlockPath h0 h1 U) phase) time) =
      1 - continueMass (hazard (quittingCyclicOrbit phase time)) := by
  rw [quittingCyclicContinuationBlockProfile,
    quittingProfileLiveRoot_cyclicBehaviorProfile, quittingCyclicRootSequence,
    quittingCyclicContinuationBlockCycle, quittingRootOfSimplex_quittingBlockPath,
    quittingRootAbsorptionMass, quittingStationaryContinueMass_quittingBlockCycle]

/-- **No vanishing absorption from a block certificate.**  A bound on the
per-stage absorption of the profile compiled from a certified block is
positive. -/
theorem pos_of_forall_absorptionMass_le_quittingBlockPathProfile
    {U : Fin (m + 2) → Payoff ι}
    (hcert : IsQuittingBlockCertificate reward hazard U) (phase : Fin (m + 1))
    {bound : ℝ}
    (hbound : ∀ time, quittingRootAbsorptionMass (quittingProfileLiveRoot reward
      (quittingCyclicContinuationBlockProfile reward m
        (quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U) phase)
          time) ≤ bound) :
    0 < bound := by
  obtain ⟨k, hk⟩ := hcert.absorb
  obtain ⟨time, htime⟩ := exists_quittingCyclicOrbit_eq phase k
  have hstage :=
    quittingRootAbsorptionMass_quittingCyclicContinuationBlockProfile_quittingBlockPath
      (reward := reward) hcert.hazard_nonneg hcert.hazard_le_one U phase time
  rw [htime] at hstage
  have := hbound time
  linarith [hstage ▸ this]

end GameTheory
