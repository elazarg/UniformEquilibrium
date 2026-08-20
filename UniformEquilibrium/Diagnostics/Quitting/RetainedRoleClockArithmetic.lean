/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.RetainedRoleClockArithmetic
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawRetentionChain

/-!
# Stopping-law adapters for retained-role clocks

This module connects the game-independent retained-role clock arithmetic to
the checked stopping-law retention interface.

For each supplied packet of `m+1` vertex labels, finite-interval retention of
one selected singleton incidence atom certifies that label throughout the
corresponding local chain. The generic arithmetic then caps the packet at
`m+2` roles and gives the density bound. This module does not derive the
supplied vertex labels from reset dynamics.
-/

namespace GameTheory

namespace RetainedRoleClockArithmetic

open StochasticGame Math.Probability Math.PMFProduct
open Math.CyclicKofNArithmetic
open Math.RetainedRoleClockArithmetic

noncomputable section

variable {ι Clock : Type} [Fintype ι] [DecidableEq ι]
variable [Fintype Clock]

/-! ## Stopping-law provenance of every packet -/

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [Fintype Clock] in
/-- Apply finite retention of the selected incidence atom separately at every
public clock phase. A positive common factor combines the unconditional `m+2`
cap for the supplied labels with positivity throughout each local chain. -/
theorem stoppingLaw_retainedRoleClock_packets
    (profiles : Clock → ℕ → (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 < factor)
    (edges : ℕ)
    (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) (time : Clock → ℕ)
    (hstep : ∀ clock, RetainsQuittingStageAtomOnInterval
      reward factor (profiles clock) 0 edges
        (quittingSingletonTerminal (incidenceLabel clock)) (time clock))
    (hpositive : ∀ clock,
      0 < quittingStageCoalitionMass reward (profiles clock 0) (time clock)
        (quittingSingletonTerminal (incidenceLabel clock))) :
    ∀ clock,
      (retainedRoleClock edges vertex incidenceLabel clock).card ≤ edges + 2 ∧
      ∀ chainPhase : Fin (edges + 1),
        factor ^ chainPhase.val *
            quittingStageCoalitionMass reward (profiles clock 0) (time clock)
              (quittingSingletonTerminal (incidenceLabel clock)) ≤
          quittingStageCoalitionMass reward
            (profiles clock chainPhase.val) (time clock)
              (quittingSingletonTerminal (incidenceLabel clock)) ∧
        incidenceLabel clock ∈ quittingPositiveSingletonStageSupport
          reward (profiles clock chainPhase.val) (time clock) := by
  intro clock
  refine ⟨retainedRoleClock_phaseLoad_le edges vertex incidenceLabel clock, ?_⟩
  intro chainPhase
  have hphaseLe : chainPhase.val ≤ edges := by
    exact Nat.le_sub_one_of_lt chainPhase.isLt
  have hphaseRetention :=
    RetainsQuittingStageAtomOnInterval.mono_steps
      reward factor (profiles clock) 0
        (quittingSingletonTerminal (incidenceLabel clock)) (time clock)
        (hstep clock) hphaseLe
  have hretained := factorPow_mul_stageCoalitionMass_le_of_resetChain
    reward (profiles clock) factor hfactor.le 0
      chainPhase.val (quittingSingletonTerminal (incidenceLabel clock))
        (time clock) hphaseRetention
  have hphase := stageCoalitionMass_pos_of_resetChain
    reward (profiles clock) factor hfactor 0
      chainPhase.val (quittingSingletonTerminal (incidenceLabel clock))
        (time clock) hphaseRetention (hpositive clock)
  constructor
  · simpa using hretained
  · simpa [quittingPositiveSingletonStageSupport] using hphase

/-- Combined stopping-law/arithmetic statement.  If those certified local
packets are uniformly distributed over players, their public clock obeys the
global density bound. -/
theorem stoppingLaw_retainedRoleClock_densityBound
    (profiles : Clock → ℕ → (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 < factor)
    (edges : ℕ)
    (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) (time : Clock → ℕ)
    (hstep : ∀ clock, RetainsQuittingStageAtomOnInterval
      reward factor (profiles clock) 0 edges
        (quittingSingletonTerminal (incidenceLabel clock)) (time clock))
    (hpositive : ∀ clock,
      0 < quittingStageCoalitionMass reward (profiles clock 0) (time clock)
        (quittingSingletonTerminal (incidenceLabel clock)))
    (r : ℕ)
    (hload : ∀ player,
      playerLoad (retainedRoleClock edges vertex incidenceLabel) player = r) :
    (∀ (clock : Clock) (chainPhase : Fin (edges + 1)),
      incidenceLabel clock ∈ quittingPositiveSingletonStageSupport
        reward (profiles clock chainPhase.val) (time clock)) ∧
    Fintype.card ι * r ≤ (edges + 2) * Fintype.card Clock := by
  have hpacket := stoppingLaw_retainedRoleClock_packets profiles factor hfactor
    edges vertex incidenceLabel time hstep hpositive
  exact ⟨fun clock chainPhase => (hpacket clock).2 chainPhase |>.2,
    population_mul_playerLoad_le_roleCap_mul_clockCard
      edges vertex incidenceLabel r hload⟩

end

end RetainedRoleClockArithmetic

end GameTheory
