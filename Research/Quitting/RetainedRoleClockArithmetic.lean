/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.StoppingLawRetentionChain
import Research.Quitting.CyclicKofNArithmetic

/-!
# Arithmetic of retained-role clocks

An `m`-edge stopping-law reset chain distinguishes at most `m+2` roles: its
`m+1` transfer vertices and one globally retained incidence label.  This file
counts a finite clock of such local packets.

If every ambient player occurs in exactly `r` packets, double counting gives

`N*r ≤ (m+2)*L`.

If every packet is saturated at `m+2` roles, equality holds and the reduced
denominator law applies:

`N / gcd(m+2,N) ∣ L`.

Thus global retention supplies the local `m+2` support bound, while balance
supplies the number-theoretic obstruction on how many reset packets a public
clock must contain.
-/

namespace GameTheory

namespace RetainedRoleClockArithmetic

open StochasticGame Math.Probability Math.PMFProduct
open CyclicKofNArithmetic
open scoped BigOperators

noncomputable section

variable {ι Clock : Type} [Fintype ι] [DecidableEq ι]
variable [Fintype Clock]

/-- A finite clock of local retained-role packets. -/
def retainedRoleClock (edges : ℕ)
    (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) : Clock → Finset ι :=
  fun phase => resetChainRoleSupport edges (vertex phase) (incidenceLabel phase)

omit [Fintype ι] [Fintype Clock] in
/-- Every packet in the clock has at most `m+2` roles. -/
theorem retainedRoleClock_phaseLoad_le
    (edges : ℕ) (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) (phase : Clock) :
    phaseLoad (retainedRoleClock edges vertex incidenceLabel) phase ≤
      edges + 2 := by
  exact resetChainRoleSupport_card_le edges
    (vertex phase) (incidenceLabel phase)

/-- **Unsaturated density bound.**  Uniform player load plus the local
`m+2` role cap gives `N*r ≤ (m+2)*L`. -/
theorem population_mul_playerLoad_le_roleCap_mul_clockCard
    (edges : ℕ) (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) (r : ℕ)
    (hload : ∀ player,
      playerLoad (retainedRoleClock edges vertex incidenceLabel) player = r) :
    Fintype.card ι * r ≤ (edges + 2) * Fintype.card Clock := by
  let roles := retainedRoleClock edges vertex incidenceLabel
  calc
    Fintype.card ι * r = ∑ _player : ι, r := by simp
    _ = ∑ player, playerLoad roles player := by
      apply Finset.sum_congr rfl
      intro player _
      exact (hload player).symm
    _ = ∑ phase, phaseLoad roles phase :=
      (sum_phaseLoad_eq_sum_playerLoad roles).symm
    _ ≤ ∑ _phase : Clock, (edges + 2) := by
      refine Finset.sum_le_sum (s := Finset.univ) ?_
      intro phase _
      exact retainedRoleClock_phaseLoad_le edges vertex incidenceLabel phase
    _ = (edges + 2) * Fintype.card Clock := by simp [mul_comm]

omit [Fintype ι] in
/-- Saturated retained-role clocks are balanced `(m+2)/N` schedules. -/
theorem retainedRoleClock_isBalanced_of_saturated
    (edges : ℕ) (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) (r : ℕ)
    (hsaturated : ∀ phase,
      (retainedRoleClock edges vertex incidenceLabel phase).card = edges + 2)
    (hload : ∀ player,
      playerLoad (retainedRoleClock edges vertex incidenceLabel) player = r) :
    IsBalanced (retainedRoleClock edges vertex incidenceLabel) (edges + 2) r := by
  exact ⟨hsaturated, hload⟩

/-- **Retained-role denominator theorem.**  A saturated balanced clock of
`m`-edge packets has phase count divisible by the reduced denominator of
`(m+2)/N`. -/
theorem reducedPopulation_dvd_retainedRoleClockCard
    (edges : ℕ) (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) (r : ℕ)
    (hι : 0 < Fintype.card ι)
    (hsaturated : ∀ phase,
      (retainedRoleClock edges vertex incidenceLabel phase).card = edges + 2)
    (hload : ∀ player,
      playerLoad (retainedRoleClock edges vertex incidenceLabel) player = r) :
    Fintype.card ι / (edges + 2).gcd (Fintype.card ι) ∣
      Fintype.card Clock := by
  exact (retainedRoleClock_isBalanced_of_saturated
    edges vertex incidenceLabel r hsaturated hload).reducedPopulation_dvd_card hι

/-- In the coprime case the retained-role clock needs at least one full
population cycle. -/
theorem population_le_retainedRoleClockCard_of_coprime
    (edges : ℕ) (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) (r : ℕ)
    (hClock : 0 < Fintype.card Clock)
    (hcoprime : Nat.Coprime (edges + 2) (Fintype.card ι))
    (hsaturated : ∀ phase,
      (retainedRoleClock edges vertex incidenceLabel phase).card = edges + 2)
    (hload : ∀ player,
      playerLoad (retainedRoleClock edges vertex incidenceLabel) player = r) :
    Fintype.card ι ≤ Fintype.card Clock := by
  exact IsBalanced.population_le_card_phase_of_coprime hClock hcoprime
    (retainedRoleClock_isBalanced_of_saturated
      edges vertex incidenceLabel r hsaturated hload)

/-! ## Stopping-law provenance of every packet -/

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [Fintype Clock] in
/-- Apply global half-retention separately at every public clock phase.  The
result certifies both the `m+2` local cap and one common positive singleton
incidence label throughout each local chain. -/
theorem stoppingLaw_retainedRoleClock_packets
    (profiles : Clock → ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ clock n,
      RetainsAllQuittingStageAtoms reward (1 / 2)
        (profiles clock n) (profiles clock (n + 1)))
    (edges : ℕ) (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) (time : Clock → ℕ)
    (hpositive : ∀ clock,
      0 < quittingStageCoalitionMass reward (profiles clock 0) (time clock)
        (quittingSingletonTerminal (incidenceLabel clock))) :
    ∀ clock,
      (retainedRoleClock edges vertex incidenceLabel clock).card ≤ edges + 2 ∧
      ∀ chainPhase : Fin (edges + 1),
        (1 / 2 : ℝ) ^ chainPhase.val *
            quittingStageCoalitionMass reward (profiles clock 0) (time clock)
              (quittingSingletonTerminal (incidenceLabel clock)) ≤
          quittingStageCoalitionMass reward
            (profiles clock chainPhase.val) (time clock)
              (quittingSingletonTerminal (incidenceLabel clock)) ∧
        incidenceLabel clock ∈ quittingPositiveSingletonStageSupport
          reward (profiles clock chainPhase.val) (time clock) := by
  intro clock
  exact resetChain_has_commonIncidence_rolePacket reward (profiles clock)
    (hstep clock) edges (vertex clock) (incidenceLabel clock)
      (time clock) (hpositive clock)

/-- Combined stopping-law/arithmetic statement.  If those certified local
packets are uniformly distributed over players, their public clock obeys the
global density bound. -/
theorem stoppingLaw_retainedRoleClock_densityBound
    (profiles : Clock → ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ clock n,
      RetainsAllQuittingStageAtoms reward (1 / 2)
        (profiles clock n) (profiles clock (n + 1)))
    (edges : ℕ) (vertex : Clock → Fin (edges + 1) → ι)
    (incidenceLabel : Clock → ι) (time : Clock → ℕ)
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
  have hpacket := stoppingLaw_retainedRoleClock_packets profiles hstep
    edges vertex incidenceLabel time hpositive
  exact ⟨fun clock chainPhase => (hpacket clock).2 chainPhase |>.2,
    population_mul_playerLoad_le_roleCap_mul_clockCard
      edges vertex incidenceLabel r hload⟩

end

end RetainedRoleClockArithmetic

end GameTheory
