/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.AnchoredCyclicScreen
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium

/-!
# A finite certificate for single-quitter periodic profiles

A *single-quitter periodic profile* of period `n + 1` schedules one designated
quitter `w k` at each phase `k`; that player randomizes with a prescribed
Boolean law and everyone else continues.  This file turns a finite list of
scalar obligations on such a profile into a uniform-equilibrium payoff, by
assembling the profile into an absorbing exact cyclic continuation block and
handing that block to
`isUniformEquilibriumPayoff_terminal_of_admissible_quittingCyclicContinuationBlock`.

The obligations are, for a displayed value path `value` with `n + 2` rows:

* the value recursion `hsucc`, one two-term mixture per phase and player;
* the anchor `hanchor`, saying the scheduled quitter is exactly indifferent
  between its own solo row and its next-phase value;
* the join caps `hjoin`, saying no spectator gains by quitting alongside the
  scheduled quitter;
* periodicity `hlast`, boundedness `hbox`, one phase of positive absorption
  `habsorb`, and nonnegative solo rewards `hsolo`.

Only singleton rows and two-element collision rows of `reward` appear, so the
certificate says nothing about coalitions of size three or more.

## Main definitions

* `soloPeriodicPhase` — the stage index reduced modulo the period
* `soloPeriodicBlock` — the Nash--Bellman path of the profile

## Main results

* `isUniformEquilibriumPayoff_of_soloPeriodicBlock` — the displayed origin row
  is a uniform-equilibrium payoff
* `isEmpty_counterexampleRegime_of_soloPeriodicBlock` — such a table carries no
  `QuittingCounterexampleRegime`
-/

noncomputable section

namespace GameTheory
namespace SoloPeriodicBlockCompiler

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The phase of a displayed stage: the stage index reduced modulo the period.
The extra terminal stage therefore repeats the origin's root, which is the
component the cyclic block ignores. -/
def soloPeriodicPhase (n : ℕ) (stage : Fin (n + 2)) : Fin (n + 1) :=
  ⟨stage.1 % (n + 1), Nat.mod_lt _ n.succ_pos⟩

@[simp] theorem soloPeriodicPhase_castSucc (k : Fin (n + 1)) :
    soloPeriodicPhase n (Fin.castSucc k) = k :=
  Fin.ext (Nat.mod_eq_of_lt k.2)

/-- The Nash--Bellman path of a single-quitter periodic profile: stage `stage`
displays `value stage` together with the root in which `w (soloPeriodicPhase n
stage)` randomizes by its prescribed law and everyone else continues. -/
def soloPeriodicBlock (w : Fin (n + 1) → ι) (marginal : Fin (n + 1) → PMF Bool)
    (value : Fin (n + 2) → Payoff ι) :
    QuittingFiniteNashBellmanPath ι (n + 1) :=
  fun stage ↦
    (value stage,
      fun who ↦ stdSimplexEquiv
        (quittingSoloMixedRoot (w (soloPeriodicPhase n stage))
          (marginal (soloPeriodicPhase n stage)) who))

variable {w : Fin (n + 1) → ι} {marginal : Fin (n + 1) → PMF Bool}
  {value : Fin (n + 2) → Payoff ι}

@[simp] theorem soloPeriodicBlock_fst (stage : Fin (n + 2)) :
    (soloPeriodicBlock w marginal value stage).1 = value stage := rfl

/-- At a stage below the cutoff the block's root is the solo mixed root of that
phase's scheduled quitter. -/
theorem quittingRootOfSimplex_soloPeriodicBlock (k : Fin (n + 1)) :
    quittingRootOfSimplex (soloPeriodicBlock w marginal value (Fin.castSucc k)).2 =
      quittingSoloMixedRoot (w k) (marginal k) := by
  funext who
  show (stdSimplexEquiv (α := Bool)).symm
      (stdSimplexEquiv (quittingSoloMixedRoot
        (w (soloPeriodicPhase n (Fin.castSucc k)))
        (marginal (soloPeriodicPhase n (Fin.castSucc k))) who)) = _
  rw [soloPeriodicPhase_castSucc, (stdSimplexEquiv (α := Bool)).symm_apply_apply]

/-! ## The finite obligations -/

variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)

/-- The finite obligations of a single-quitter periodic profile, bundled so the
compiler below and its instances agree on their exact shape. -/
structure IsSoloPeriodicCertificate
    (w : Fin (n + 1) → ι) (marginal : Fin (n + 1) → PMF Bool)
    (value : Fin (n + 2) → Payoff ι) : Prop where
  /-- Every displayed value fits inside the canonical reward box. -/
  box : ∀ (stage : Fin (n + 2)) (who : ι),
    |value stage who| ≤ quittingRewardBound reward
  /-- The displayed path closes up: its last row repeats its origin. -/
  last : value (Fin.last (n + 1)) = value 0
  /-- The value recursion: at each phase the displayed value is the two-term
  mixture of the scheduled quitter's solo row and the next phase's value. -/
  succ : ∀ (k : Fin (n + 1)) (who : ι),
    value (Fin.castSucc k) who =
      (marginal k true).toReal * reward (quittingSingletonTerminal (w k)) who +
        (marginal k false).toReal * value (Fin.succ k) who
  /-- The anchor: at its own phase the scheduled quitter is exactly indifferent
  between its solo row and its next-phase value. -/
  anchor : ∀ k : Fin (n + 1),
    reward (quittingSingletonTerminal (w k)) (w k) = value (Fin.succ k) (w k)
  /-- The join caps: a spectator's one-stage deviation to Quit never beats the
  prescribed continuation. -/
  join : ∀ (k : Fin (n + 1)) (who : ι), who ≠ w k →
    (marginal k true).toReal *
          reward ⟨{w k, who}, Finset.insert_nonempty (w k) {who}⟩ who +
        (marginal k false).toReal * reward (quittingSingletonTerminal who) who ≤
      (marginal k true).toReal * reward (quittingSingletonTerminal (w k)) who +
        (marginal k false).toReal * value (Fin.succ k) who
  /-- Some phase absorbs with positive probability. -/
  absorb : ∃ k : Fin (n + 1), 0 < (marginal k true).toReal
  /-- Every player's own solo reward is nonnegative. -/
  solo : ∀ who : ι, 0 ≤ reward (quittingSingletonTerminal who) who

variable {reward}

/-! ## The compiler -/

/-- A certified single-quitter periodic profile is an absorbing exact cyclic
continuation block for its displayed origin row. -/
theorem isQuittingCyclicContinuationBlock_soloPeriodicBlock
    (hcert : IsSoloPeriodicCertificate reward w marginal value) :
    IsQuittingCyclicContinuationBlock reward (value 0) (n + 1)
      (soloPeriodicBlock w marginal value) := by
  refine ⟨⟨?_, hcert.last, ?_⟩, rfl, ?_⟩
  · intro stage
    refine ⟨fun who ↦ ?_, fun who ↦ ?_⟩
    · exact neg_le_of_abs_le (hcert.box stage who)
    · exact le_of_abs_le (hcert.box stage who)
  · intro k
    refine ⟨?_, ?_⟩
    · show value (Fin.castSucc k) =
        quittingRootSuccessorPayoff reward (value (Fin.succ k))
          (quittingRootOfSimplex (soloPeriodicBlock w marginal value
            (Fin.castSucc k)).2)
      rw [quittingRootOfSimplex_soloPeriodicBlock]
      funext who
      rw [quittingRootSuccessorPayoff_soloMixedRoot]
      exact hcert.succ k who
    · show IsεQuittingRootEndpointNash reward (value (Fin.succ k)) 0
        (quittingRootOfSimplex (soloPeriodicBlock w marginal value
          (Fin.castSucc k)).2)
      rw [quittingRootOfSimplex_soloPeriodicBlock]
      exact isZeroQuittingRootEndpointNash_soloMixedRoot reward
        (value (Fin.succ k)) (w k) (marginal k) (hcert.anchor k) (hcert.join k)
  · obtain ⟨k, hk⟩ := hcert.absorb
    refine ⟨k, ?_⟩
    rw [quittingRootOfSimplex_soloPeriodicBlock,
      quittingRootAbsorptionMass_soloMixedRoot]
    exact hk

/-- Nonnegative solo rewards make the profile's cycle admissible. -/
theorem isQuittingCycleAdmissible_soloPeriodicBlock
    (hcert : IsSoloPeriodicCertificate reward w marginal value) :
    IsQuittingCycleAdmissible reward
      (quittingCyclicContinuationBlockCycle n (soloPeriodicBlock w marginal value)) :=
  fun who ↦ Or.inr (hcert.solo who)

/-- **A certified single-quitter periodic profile realizes its origin row as a
uniform-equilibrium payoff.**  The deviation class is all behavior strategies,
not stopping times. -/
theorem isUniformEquilibriumPayoff_of_soloPeriodicBlock
    (hcert : IsSoloPeriodicCertificate reward w marginal value) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) :=
  isUniformEquilibriumPayoff_terminal_of_admissible_quittingCyclicContinuationBlock
    reward (value 0) n (soloPeriodicBlock w marginal value)
    (isQuittingCyclicContinuationBlock_soloPeriodicBlock hcert)
    (isQuittingCycleAdmissible_soloPeriodicBlock hcert)

/-- A table carrying a certified single-quitter periodic profile lies in no
counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_soloPeriodicBlock
    (hcert : IsSoloPeriodicCertificate reward w marginal value) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  ⟨fun regime ↦ regime.not_exists_uniformEquilibriumPayoff
    ⟨value 0, isUniformEquilibriumPayoff_of_soloPeriodicBlock hcert⟩⟩

end SoloPeriodicBlockCompiler
end GameTheory
