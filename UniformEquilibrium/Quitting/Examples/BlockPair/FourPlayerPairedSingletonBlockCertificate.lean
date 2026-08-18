/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonPeriodTwo

/-!
# The four-player alternating pair profile as a block certificate

`GameTheory.FourPlayerPairedSingleton` certifies a period-two profile of the
four-player boundary table in which players `0` and `2` randomize at the odd
phase and players `1` and `3` randomize at the even phase.  Two players move at
every stage, so the profile lies outside the single-quitter class.

This file writes that profile as a hazard schedule
`periodTwoHazard : Fin 2 → Player → ℝ`, identifies the resulting family of
product rows with the example's two displayed rows, and reads the example's
value recursion and one-stage Nash conditions as an
`IsQuittingBlockCertificate`.  Running the general block producer on that
certificate reproduces the example's uniform-equilibrium payoff.

The point of the file is the interface: it records that the general block
producer accepts a certified two-quitter period-two profile, and that the
payoff it returns is the same one.  It proves nothing new about the table.
-/

noncomputable section

namespace GameTheory
namespace FourPlayerPairedSingletonBlockCertificate

open FourPlayerPairedSingleton
open SolanVieilleBoundary (boundaryReward)
open Math.PMFProduct

/-! ## The hazard schedule -/

/-- The hazard schedule of the alternating pair profile: at the odd phase
players `0` and `2` quit with probabilities `1 - a` and `1 - b`, at the even
phase players `1` and `3` do. -/
def periodTwoHazard : Fin 2 → Player → ℝ :=
  ![![1 - periodTwoParameter, 0, 1 - periodTwoSecondary, 0],
    ![0, 1 - periodTwoParameter, 0, 1 - periodTwoSecondary]]

theorem periodTwoHazard_nonneg : ∀ k who, 0 ≤ periodTwoHazard k who := by
  have ha := periodTwoParameter_lt_one
  have hb := periodTwoSecondary_lt_one
  intro k who
  fin_cases k <;> fin_cases who <;> simp [periodTwoHazard] <;> linarith

theorem periodTwoHazard_le_one : ∀ k who, periodTwoHazard k who ≤ 1 := by
  have ha := periodTwoParameter_pos
  have hb := periodTwoSecondary_pos
  intro k who
  fin_cases k <;> fin_cases who <;> simp [periodTwoHazard] <;> linarith

/-- The block rows of the schedule are the example's two displayed rows. -/
theorem quittingBlockCycle_periodTwoHazard (k : Fin 2) :
    quittingBlockCycle periodTwoHazard periodTwoHazard_nonneg periodTwoHazard_le_one
        k =
      ![oddRoot, evenRoot] k := by
  funext who
  fin_cases k <;> fin_cases who <;>
    simp only [quittingBlockCycle, rootOfHazard, periodTwoHazard, oddRoot,
      evenRoot] <;>
    first
      | rfl
      | exact quittingHazardCoin_zero _ _

/-! ## The displayed values -/

/-- The displayed value path: the odd value, the even value, and the odd value
again. -/
def periodTwoValue : Fin 3 → Payoff Player := ![oddValue, evenValue, oddValue]

theorem abs_periodTwoValue_le (stage : Fin 3) (who : Player) :
    |periodTwoValue stage who| ≤ quittingRewardBound boundaryReward := by
  have hodd := oddPoint_mem_box
  have heven := evenPoint_mem_box
  obtain ⟨hoddLower, hoddUpper⟩ := hodd
  obtain ⟨hevenLower, hevenUpper⟩ := heven
  fin_cases stage
  · exact abs_le.mpr ⟨hoddLower who, hoddUpper who⟩
  · exact abs_le.mpr ⟨hevenLower who, hevenUpper who⟩
  · exact abs_le.mpr ⟨hoddLower who, hoddUpper who⟩

/-! ## The certificate -/

theorem periodTwo_isQuittingBlockCertificate :
    IsQuittingBlockCertificate boundaryReward periodTwoHazard periodTwoValue := by
  refine isQuittingBlockCertificate_of_root periodTwoHazard_nonneg
    periodTwoHazard_le_one abs_periodTwoValue_le rfl ?_ ?_ ?_ ?_
  · intro k
    rw [quittingBlockCycle_periodTwoHazard]
    fin_cases k
    · exact oddRoot_successor.symm
    · exact evenRoot_successor.symm
  · intro k
    rw [quittingBlockCycle_periodTwoHazard]
    fin_cases k
    · exact oddRoot_isZeroEndpointNash
    · exact evenRoot_isZeroEndpointNash
  · refine ⟨0, ?_⟩
    have hmass : continueMass (periodTwoHazard 0) =
        quittingStationaryContinueMass oddRoot := by
      rw [← quittingStationaryContinueMass_quittingBlockCycle periodTwoHazard_nonneg
        periodTwoHazard_le_one 0, quittingBlockCycle_periodTwoHazard]
      rfl
    rw [hmass, oddRoot_continueMass]
    nlinarith [periodTwoParameter_pos, periodTwoParameter_lt_one,
      periodTwoSecondary_pos, periodTwoSecondary_lt_one]
  · refine fun who ↦ Or.inr ?_
    fin_cases who <;> simp [boundaryReward, quittingSingletonTerminal]

/-! ## The payoff through the general producer -/

/-- **The general block producer returns the example's payoff.**  The
alternating pair profile is accepted by `IsQuittingBlockCertificate`, and the
payoff it yields is the example's odd-phase value. -/
theorem periodTwo_isUniformEquilibriumPayoff_via_block :
    (quittingGame boundaryReward).IsUniformEquilibriumPayoff none oddValue :=
  isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
    periodTwo_isQuittingBlockCertificate

end FourPlayerPairedSingletonBlockCertificate
end GameTheory
