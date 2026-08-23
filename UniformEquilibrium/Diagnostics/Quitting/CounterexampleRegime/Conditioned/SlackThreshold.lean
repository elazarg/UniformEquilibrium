/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Conditioned.NegativeTangent
import UniformEquilibrium.Quitting.Cycles.ConditionedSlackThreshold

/-!
# Conditioned punishment-slack threshold at a counterexample seam

This adapter combines the generic conditioned-slack threshold with a
counterexample seam's period-one tangent readout. An uncovered limiting
negative tangent forces the selected deliveries below punishment; on a
positive-mass coordinate, the same roots are eventually phase-exploitable.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleDynamicTailWitness

variable (seam : QuittingCounterexampleDynamicTailWitness regime)

namespace CounterexampleRegimePeriodOneTangentReadout

variable (readout : CounterexampleRegimePeriodOneTangentReadout seam)

/-- The selected root's honest period-one absorbing delivery converges to the
phantom boundary plus the extracted tangent.  This statement deliberately
uses the seam boundary: the abstract readout structure need not identify its
packet's stored boundary field definitionally with the seam limit. -/
theorem periodOneReadoutDelivery_tendsto_boundary_add_tangent (who : ι) :
    Tendsto (fun index ↦
      quittingWindowRestartDelivery reward
        (quittingPeriodOneRootSequence
          (seam.periodOneReadoutRoot readout.start index)) who 0 1)
      atTop (nhds (seam.limit.value who + readout.packet.tangent who)) := by
  have hstartSucc : Tendsto (fun index ↦ readout.start index + 1)
      atTop atTop :=
    Filter.tendsto_atTop_mono
      (fun index ↦ Nat.le_add_right (readout.start index) 1)
      readout.start_tendsto
  have hboundary : Tendsto
      (fun index ↦ (seam.tail (readout.start index + 1)).1.1 who)
      atTop (nhds (seam.limit.value who)) :=
    (seam.value_tendsto who).comp hstartSucc
  have hsum := (readout.tangent_tendsto who).add hboundary
  simpa [QuittingCounterexampleDynamicTailWitness.periodOneReadoutTangent,
    add_comm] using hsum

/-- The limiting delivery is punishment-rational exactly when the negative
tangent magnitude fits in the seam boundary's punishment slack. -/
theorem punishmentValue_le_boundary_add_tangent_iff_neg_tangent_le_slack
    (who : ι) :
    quittingPunishmentValue reward who ≤
        seam.limit.value who + readout.packet.tangent who ↔
      -readout.packet.tangent who ≤
        seam.limit.value who - quittingPunishmentValue reward who := by
  constructor <;> intro h <;> linarith

/-- **Limiting punishment threshold.**  A negative tangent is either covered
by the phantom boundary's punishment slack, or the selected repeated-root
deliveries eventually lie strictly below the punishment value. -/
theorem neg_tangent_le_punishmentSlack_or_eventually_delivery_lt_punishment
    (who : ι) :
    -readout.packet.tangent who ≤
        seam.limit.value who - quittingPunishmentValue reward who ∨
      ∀ᶠ index in atTop,
        quittingWindowRestartDelivery reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) who 0 1 <
          quittingPunishmentValue reward who := by
  by_cases hcovered : -readout.packet.tangent who ≤
      seam.limit.value who - quittingPunishmentValue reward who
  · exact Or.inl hcovered
  · right
    have hunderfloor :
        seam.limit.value who + readout.packet.tangent who <
          quittingPunishmentValue reward who := by
      linarith
    exact (readout.periodOneReadoutDelivery_tendsto_boundary_add_tangent
      seam who).eventually_lt_const hunderfloor

/-- On an active negative coordinate, insufficient punishment slack produces
the full double obstruction eventually: the repeated root is phase-
exploitable and its honest absorbing delivery is below punishment.  Repairing
this branch must therefore change the limiting delivery or the active support.
-/
theorem neg_tangent_le_punishmentSlack_or_eventually_phaseGain_and_underfloor
    (player : ι) (hmass : 0 < readout.packet.mass player)
    (hnegative : readout.packet.tangent player < 0) :
    -readout.packet.tangent player ≤
        seam.limit.value player - quittingPunishmentValue reward player ∨
      ∀ᶠ index in atTop,
        0 < quittingPeriodicWindowBestPhaseStop reward
              (quittingPeriodOneRootSequence
                (seam.periodOneReadoutRoot readout.start index)) player 1 -
            quittingWindowRestartDelivery reward
              (quittingPeriodOneRootSequence
                (seam.periodOneReadoutRoot readout.start index)) player 0 1 ∧
          quittingWindowRestartDelivery reward
              (quittingPeriodOneRootSequence
                (seam.periodOneReadoutRoot readout.start index)) player 0 1 <
            quittingPunishmentValue reward player := by
  rcases readout.neg_tangent_le_punishmentSlack_or_eventually_delivery_lt_punishment
      seam player with hcovered | hunderfloor
  · exact Or.inl hcovered
  · right
    exact (readout.eventually_phaseGain_of_mass_pos_of_tangent_neg
      seam player hmass hnegative).and hunderfloor

end CounterexampleRegimePeriodOneTangentReadout

end QuittingCounterexampleDynamicTailWitness

end GameTheory
