/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Experiments.counterexample_search.RegularTournamentFiveSeed
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.AnchoredCyclicRenewal
import UniformEquilibrium.Quitting.Cycles.AnchoredCyclicRenewal
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Cycles.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium

/-!
# The hardened pentagon completion and its rational cyclic equilibrium

`RegularTournamentFiveSeed` pins the singleton rows of the regular
five-tournament geometry and completes every coalition of size at least two
by zero.  That realization is degenerate: all-quit is an exact equilibrium.
The *hardened completion* `H` below keeps the same singleton rows and
replaces the zero completion by

* adjacent pairs `{i, i+1}`: the winner `i` gets `0`, the beaten `i+1`
  gets `1`, outsiders get `2`;
* every other coalition of size at least two: members get `0`, outsiders
  get `2` (so the grand coalition pays the zero vector).

This file checks, by exact rational arithmetic, that `H` has the
uniform-equilibrium payoff `(1, 1, 1, 2, 2)`.  The witness is the
single-quitter periodic profile of `Research.Quitting.AnchoredCyclicScreen`
with period five, schedule `w = (0, 3, 1, 4, 2)`, and quit probability `1/2`
at every phase: one stage per phase, all data rational.

Every obligation is finite.  Five anchors say the scheduled quitter is
exactly indifferent; twenty spectator inequalities say no bystander wants to
join; one stage absorbs with probability `1/2`.  The repository's admissible
cyclic-continuation compiler turns that finite certificate into an exact
terminal Nash profile against *all* behavioral deviations, hence into a
uniform-equilibrium payoff.

Consequences recorded below: `H` carries no `QuittingCounterexampleRegime`,
and — through the anchored cyclic screen — its response cap never beats the
on-path renewal value.  This is a checked statement about one table, not a
general theorem about the pentagon geometry.

The two exclusions are obtained from disjoint inputs.
`hardened_isEmpty_counterexampleRegime` runs through the uniform-equilibrium
payoff and the terminal exploitability gap.
`hardened_isEmpty_counterexampleRegime_via_screen` instead solves two finite
systems on the same schedule with exact rational data: the twenty-five renewal
equations of `isAnchoredCyclicRenewalSolution_responseSolution`, which pin the
on-path value by uniqueness because survival around one pass is `(1/2) ^ 5`,
and the twenty-five max equations of
`isAnchoredCyclicResponseSolution_responseSolution`, which cap the exact
behavioral best response.  Its refusal branch is closed by the spectator
condition `exists_spectatorHazard`.  Neither the cyclic continuation block, its
admissibility, the uniform-equilibrium payoff, nor the profile's asymptotic
Nash property enters that route.
-/

noncomputable section

namespace GameTheory
namespace HardenedPentagonCyclicEquilibrium

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction
open RegularTournamentFiveSeed (Player singletonMatrix)

/-! ## The hardened completion -/

/-- The hardened completion `H` of the regular five-tournament singleton
geometry.  Singleton rows are the seed's; a member of a larger coalition is
paid `1` exactly when the coalition is the adjacent pair in which it is the
beaten player, and `0` otherwise; outsiders are paid `2`. -/
def hardenedReward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S who =>
    if S.1.card = 1 then 1 + ∑ owner ∈ S.1, singletonMatrix who owner
    else if who ∉ S.1 then 2
    else if S.1 = ({who - 1, who} : Finset Player) then 1
    else 0

/-- The hardened completion keeps the seed's singleton rows. -/
theorem hardenedReward_singleton (owner who : Player) :
    hardenedReward (quittingSingletonTerminal owner) who =
      1 + singletonMatrix who owner := by
  simp [hardenedReward, quittingSingletonTerminal]

/-- The joiner coordinate of a two-player collision row: a spectator who
joins the scheduled quitter is paid `1` exactly when it is that quitter's
tournament successor, and `0` otherwise. -/
theorem hardenedReward_pair (owner who : Player) (hne : who ≠ owner) :
    hardenedReward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who =
      if who = owner + 1 then 1 else 0 := by
  have hcard : ¬ ({owner, who} : Finset Player).card = 1 := by
    revert hne
    revert owner who
    decide
  have hmem : ¬ who ∉ ({owner, who} : Finset Player) := by simp
  have hkey : (({owner, who} : Finset Player) = {who - 1, who}) ↔
      who = owner + 1 := by
    revert hne
    revert owner who
    decide
  show (if _ then _ else if _ then (2 : ℝ) else if _ then 1 else 0) = _
  rw [if_neg hcard, if_neg hmem]
  by_cases hadj : who = owner + 1
  · rw [if_pos (hkey.mpr hadj), if_pos hadj]
  · rw [if_neg (fun h ↦ hadj (hkey.mp h)), if_neg hadj]

/-- Outsiders of a coalition of size at least two are paid two. -/
theorem hardenedReward_of_notMem (S : {S : Finset Player // S.Nonempty})
    (hcard : S.1.card ≠ 1) (who : Player) (hwho : who ∉ S.1) :
    hardenedReward S who = 2 := by
  show (if _ then _ else if _ then (2 : ℝ) else if _ then 1 else 0) = _
  rw [if_neg hcard, if_pos hwho]

/-- A member of a coalition of size at least two is paid zero unless that
coalition is the adjacent pair in which it is the beaten player. -/
theorem hardenedReward_of_mem (S : {S : Finset Player // S.Nonempty})
    (hcard : S.1.card ≠ 1) (who : Player) (hwho : who ∈ S.1)
    (hnotBeaten : S.1 ≠ ({who - 1, who} : Finset Player)) :
    hardenedReward S who = 0 := by
  show (if _ then _ else if _ then (2 : ℝ) else if _ then 1 else 0) = _
  rw [if_neg hcard, if_neg (by simpa using hwho), if_neg hnotBeaten]

/-- The grand coalition pays the zero vector. -/
theorem hardenedReward_univ (who : Player) :
    hardenedReward ⟨Finset.univ, Finset.univ_nonempty⟩ who = 0 := by
  refine hardenedReward_of_mem _ (by decide) who (Finset.mem_univ who) ?_
  intro hcontra
  have hcard := congrArg Finset.card hcontra
  revert hcard
  revert who
  decide

/-- Explicit singleton rows: `3` when `who` beats `owner`, `0` when `owner`
beats `who`, and `1` on the diagonal. -/
@[simp] theorem hardenedReward_singleton_entries (owner who : Player) :
    hardenedReward (quittingSingletonTerminal owner) who =
      ![![1, 3, 3, 0, 0], ![0, 1, 3, 3, 0], ![0, 0, 1, 3, 3],
        ![3, 0, 0, 1, 3], ![3, 3, 0, 0, 1]] who owner := by
  rw [hardenedReward_singleton, RegularTournamentFiveSeed.singletonMatrix_entries]
  fin_cases who <;> fin_cases owner <;> norm_num

/-! ## The rational cyclic certificate -/

/-- Temporal order of the designated quitters. -/
def schedule : Fin 5 → Player := ![0, 3, 1, 4, 2]

/-- The Boolean law with quit probability `1/2`. -/
def halfCoin : PMF Bool :=
  quittingHazardCoin (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem halfCoin_true : (halfCoin true).toReal = 1 / 2 := by
  simp [halfCoin]

@[simp] theorem halfCoin_false : (halfCoin false).toReal = 1 / 2 := by
  simp [halfCoin]
  norm_num

/-- Phase `k` of the profile: `schedule k` quits with probability `1/2`,
everyone else continues. -/
def phaseRoot (phase : Fin 5) : Player → PMF Bool :=
  quittingSoloMixedRoot (schedule phase) halfCoin

/-- The on-path continuation values, phase by phase. -/
def phaseValue : Fin 6 → Payoff Player :=
  ![![1, 1, 1, 2, 2], ![1, 2, 2, 1, 1], ![2, 1, 1, 1, 2],
    ![1, 1, 2, 2, 1], ![2, 2, 1, 1, 1], ![1, 1, 1, 2, 2]]

/-- The rational uniform-equilibrium payoff target. -/
def target : Payoff Player := ![1, 1, 1, 2, 2]

/-- Simplex coordinates of the six displayed block states; the last one
repeats phase zero. -/
def phaseSimplexRoot : Fin 6 → QuittingRootSimplex Player :=
  ![fun who ↦ stdSimplexEquiv (phaseRoot 0 who),
    fun who ↦ stdSimplexEquiv (phaseRoot 1 who),
    fun who ↦ stdSimplexEquiv (phaseRoot 2 who),
    fun who ↦ stdSimplexEquiv (phaseRoot 3 who),
    fun who ↦ stdSimplexEquiv (phaseRoot 4 who),
    fun who ↦ stdSimplexEquiv (phaseRoot 0 who)]

theorem quittingRootOfSimplex_phaseSimplexRoot (phase : Fin 5) :
    quittingRootOfSimplex (phaseSimplexRoot (Fin.castSucc phase)) =
      phaseRoot phase := by
  fin_cases phase <;>
    · funext who
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply _

/-- The exact cyclic continuation block of the hardened completion. -/
def hardenedBlock : QuittingFiniteNashBellmanPath Player 5 :=
  fun stage ↦ (phaseValue stage, phaseSimplexRoot stage)

/-! ### The twenty-five finite obligations -/

/-- **The five anchors.**  At its own phase the scheduled quitter is exactly
indifferent: quitting pays its solo row `1`, which is also its continuation
value at the next phase. -/
theorem anchor (phase : Fin 5) :
    hardenedReward (quittingSingletonTerminal (schedule phase))
        (schedule phase) =
      phaseValue (Fin.succ phase) (schedule phase) := by
  fin_cases phase <;> simp [schedule, phaseValue]

/-- **The twenty join caps.**  A spectator's one-stage deviation to Quit —
half the collision row, half its own solo row — never beats staying with the
prescribed mixture. -/
theorem joinCap (phase : Fin 5) (who : Player) (hne : who ≠ schedule phase) :
    (halfCoin true).toReal *
          hardenedReward
            ⟨{schedule phase, who},
              Finset.insert_nonempty (schedule phase) {who}⟩ who +
        (halfCoin false).toReal *
          hardenedReward (quittingSingletonTerminal who) who ≤
      (halfCoin true).toReal *
          hardenedReward (quittingSingletonTerminal (schedule phase)) who +
        (halfCoin false).toReal * phaseValue (Fin.succ phase) who := by
  rw [hardenedReward_pair (schedule phase) who hne]
  fin_cases phase <;> fin_cases who <;>
    simp_all [schedule, phaseValue] <;> norm_num

/-! ### The block is an absorbing exact Nash--Bellman cycle -/

theorem phaseRoot_successor (phase : Fin 5) :
    quittingRootSuccessorPayoff hardenedReward
        (phaseValue (Fin.succ phase)) (phaseRoot phase) =
      phaseValue (Fin.castSucc phase) := by
  funext who
  rw [phaseRoot, quittingRootSuccessorPayoff_soloMixedRoot]
  fin_cases phase <;> fin_cases who <;>
    simp [schedule, phaseValue] <;> norm_num

theorem phaseRoot_isZeroEndpointNash (phase : Fin 5) :
    IsεQuittingRootEndpointNash hardenedReward
      (phaseValue (Fin.succ phase)) 0 (phaseRoot phase) :=
  isZeroQuittingRootEndpointNash_soloMixedRoot hardenedReward
    (phaseValue (Fin.succ phase)) (schedule phase) halfCoin
    (anchor phase) (fun who hne ↦ joinCap phase who hne)

/-- Three is a lower bound for the canonical reward bound of the hardened
table, so every displayed value fits inside the Nash--Bellman box. -/
theorem three_le_hardenedRewardBound :
    (3 : ℝ) ≤ quittingRewardBound hardenedReward := by
  have hentry := abs_reward_le_quittingRewardBound hardenedReward
    (quittingSingletonTerminal (1 : Player)) (0 : Player)
  rw [hardenedReward_singleton_entries] at hentry
  norm_num at hentry
  exact hentry

theorem hardenedBlock_mem_box (stage : Fin 6) :
    hardenedBlock stage ∈
      quittingNashBellmanBox (quittingRewardBound hardenedReward) := by
  have hbound := three_le_hardenedRewardBound
  constructor <;> intro who <;>
    (fin_cases stage <;> fin_cases who <;>
      simp [hardenedBlock, phaseValue] <;> linarith)

/-- The displayed block is an absorbing exact cyclic continuation block for
the target `(1, 1, 1, 2, 2)`. -/
theorem hardenedBlock_isQuittingCyclicContinuationBlock :
    IsQuittingCyclicContinuationBlock hardenedReward target 5 hardenedBlock := by
  refine ⟨⟨hardenedBlock_mem_box, ?_, ?_⟩, ?_, ⟨0, ?_⟩⟩
  · rfl
  · intro stage
    refine ⟨?_, ?_⟩
    · show phaseValue (Fin.castSucc stage) =
        quittingRootSuccessorPayoff hardenedReward
          (phaseValue (Fin.succ stage))
          (quittingRootOfSimplex (phaseSimplexRoot (Fin.castSucc stage)))
      rw [quittingRootOfSimplex_phaseSimplexRoot, phaseRoot_successor]
    · show IsεQuittingRootEndpointNash hardenedReward
        (phaseValue (Fin.succ stage)) 0
        (quittingRootOfSimplex (phaseSimplexRoot (Fin.castSucc stage)))
      rw [quittingRootOfSimplex_phaseSimplexRoot]
      exact phaseRoot_isZeroEndpointNash stage
  · rfl
  · show 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex (phaseSimplexRoot (Fin.castSucc (0 : Fin 5))))
    rw [quittingRootOfSimplex_phaseSimplexRoot, phaseRoot,
      quittingRootAbsorptionMass_soloMixedRoot, halfCoin_true]
    norm_num

/-- Admissibility is immediate: every own-singleton payoff of the hardened
table equals one, so no deviation mismatch can survive. -/
theorem hardenedBlockCycle_isAdmissible :
    IsQuittingCycleAdmissible hardenedReward
      (quittingCyclicContinuationBlockCycle 4 hardenedBlock) := by
  intro who
  refine Or.inr ?_
  rw [hardenedReward_singleton_entries]
  fin_cases who <;> norm_num

/-! ## The headline -/

/-- **The hardened pentagon completion has the uniform-equilibrium payoff
`(1, 1, 1, 2, 2)`.**  The witness is the period-five single-quitter profile
with schedule `(0, 3, 1, 4, 2)` and quit probability `1/2`; the deviation
class is *all* behavior strategies, not just stopping times. -/
theorem hardened_isUniformEquilibriumPayoff :
    (quittingGame hardenedReward).IsUniformEquilibriumPayoff none target :=
  isUniformEquilibriumPayoff_terminal_of_admissible_quittingCyclicContinuationBlock
    hardenedReward target 4 hardenedBlock
    hardenedBlock_isQuittingCyclicContinuationBlock
    hardenedBlockCycle_isAdmissible

/-- **The hardened completion is in no counterexample regime.**  A terminal
exploitability gap is incompatible with an existing uniform-equilibrium
payoff. -/
theorem hardened_isEmpty_counterexampleRegime :
    IsEmpty (QuittingCounterexampleRegime hardenedReward) :=
  ⟨fun regime ↦
    quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      hardenedReward regime.terminalGap_pos regime.terminalExploitability
      ⟨target, hardened_isUniformEquilibriumPayoff⟩⟩

/-! ## Reading the certificate through the anchored cyclic screen -/

/-- The constant hazard `1/2`. -/
def hazard : Fin 5 → ℝ := fun _ ↦ 1 / 2

theorem hazard_nonneg (phase : Fin 5) : 0 ≤ hazard phase := by
  norm_num [hazard]

theorem hazard_le_one (phase : Fin 5) : hazard phase ≤ 1 := by
  norm_num [hazard]

/-- The block's rows are exactly the anchored cyclic cycle of
`(5, (0, 3, 1, 4, 2), 1/2)`. -/
theorem quittingCyclicContinuationBlockCycle_eq_anchoredCyclicCycle :
    quittingCyclicContinuationBlockCycle 4 hardenedBlock =
      quittingAnchoredCyclicCycle schedule hazard hazard_nonneg hazard_le_one := by
  funext phase
  rw [show quittingCyclicContinuationBlockCycle 4 hardenedBlock phase =
      quittingRootOfSimplex (phaseSimplexRoot (Fin.castSucc phase)) from rfl,
    quittingRootOfSimplex_phaseSimplexRoot]
  rfl

/-! ### The exact rational solution of the max-linear response system -/

/-- The candidate cap: the block's own phase values, read as a phase-indexed
family of real vectors. -/
def responseSolution : Fin 5 → Player → ℝ :=
  fun phase ↦ phaseValue (Fin.castSucc phase)

theorem responseSolution_start : responseSolution (quittingAnchoredCyclicStart 5)
    = target := rfl

/-- Survival around one full pass is `(1/2) ^ 5`, so the cycle absorbs. -/
theorem prod_one_sub_hazard : ∏ k : Fin 5, (1 - hazard k) = 1 / 32 := by
  rw [Fin.prod_univ_five]
  norm_num [hazard]

/-- **The twenty-five renewal equations.**  The displayed phase values solve
the anchored cyclic renewal system of this schedule. -/
theorem isAnchoredCyclicRenewalSolution_responseSolution :
    IsAnchoredCyclicRenewalSolution hardenedReward schedule hazard
      responseSolution := by
  intro phase who
  fin_cases phase <;> fin_cases who <;>
    simp [responseSolution, schedule, phaseValue, hazard] <;> norm_num

/-- **The twenty-five max equations.**  The same phase values solve the
max-linear response system: at every phase the Continue branch already attains
the value and the Quit branch never exceeds it. -/
theorem isAnchoredCyclicResponseSolution_responseSolution :
    IsAnchoredCyclicResponseSolution hardenedReward schedule hazard
      responseSolution := by
  intro phase who
  rw [quittingAnchoredCyclicQuitValue, quittingAnchoredCyclicContinueValue]
  fin_cases phase <;> fin_cases who <;>
    simp [responseSolution, schedule, phaseValue, hazard, hardenedReward_pair] <;>
    norm_num

/-- Every player sits out some phase carrying positive hazard, since the
schedule visits all five players and every hazard is `1/2`. -/
theorem exists_spectatorHazard (who : Player) :
    ∃ k, schedule k ≠ who ∧ 0 < hazard k := by
  refine ⟨if who = 0 then 1 else 0, ?_, by norm_num [hazard]⟩
  fin_cases who <;> decide

/-- The anchored cyclic on-path value of this schedule is the phase-value
family, by uniqueness of the renewal solution: survival around one pass is
`1/32`, so the renewal system is contracting. -/
theorem quittingAnchoredCyclicOnPathValue_eq_responseSolution :
    quittingAnchoredCyclicOnPathValue hardenedReward schedule hazard
        hazard_nonneg hazard_le_one = responseSolution :=
  eq_of_isAnchoredCyclicRenewalSolution
    (quittingAnchoredCyclicOnPathValue_isAnchoredCyclicRenewalSolution
      hardenedReward schedule hazard hazard_nonneg hazard_le_one)
    isAnchoredCyclicRenewalSolution_responseSolution
    (by rw [prod_one_sub_hazard]; norm_num)

/-- The anchored cyclic on-path value of this schedule is exactly the
rational target `(1, 1, 1, 2, 2)`. -/
theorem quittingAnchoredCyclicOnPathValue_eq_target :
    quittingAnchoredCyclicOnPathValue hardenedReward schedule hazard
        hazard_nonneg hazard_le_one (quittingAnchoredCyclicStart 5) = target := by
  rw [quittingAnchoredCyclicOnPathValue_eq_responseSolution,
    responseSolution_start]

/-- **The response cap, computed.**  The exact behavioral best-response
statistic of this profile is at most the solved max-linear system, hence at
most the rational target.  The inputs are the twenty-five max equations, the
spectator condition, and nothing else. -/
theorem quittingAnchoredCyclicResponseCap_le_target (who : Player) :
    quittingAnchoredCyclicResponseCap hardenedReward schedule hazard
        hazard_nonneg hazard_le_one who ≤ target who :=
  quittingAnchoredCyclicResponseCap_le_of_response_of_spectatorHazard schedule
    hazard hazard_nonneg hazard_le_one responseSolution
    isAnchoredCyclicResponseSolution_responseSolution who
    (exists_spectatorHazard who)

/-- The pentagon's anchored cyclic profile is asymptotic Nash at accuracy zero
for the terminal payoff: it is the profile of the certified cyclic
continuation block, read through the schedule identification. -/
theorem isεAsymptoticNash_anchoredCyclicProfile :
    (quittingGame hardenedReward).IsεAsymptoticNash
      (quittingTerminalPayoff hardenedReward) 0
      (quittingAnchoredCyclicProfile hardenedReward schedule hazard
        hazard_nonneg hazard_le_one) := by
  have hprofile : quittingAnchoredCyclicProfile hardenedReward schedule hazard
      hazard_nonneg hazard_le_one =
    quittingCyclicContinuationBlockProfile hardenedReward 4 hardenedBlock
      (quittingAnchoredCyclicStart 5) := by
    unfold quittingAnchoredCyclicProfile quittingCyclicContinuationBlockProfile
    rw [quittingCyclicContinuationBlockCycle_eq_anchoredCyclicCycle]
  rw [hprofile]
  exact isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile
    hardenedReward target 4 hardenedBlock
    hardenedBlock_isQuittingCyclicContinuationBlock
    hardenedBlockCycle_isAdmissible (quittingAnchoredCyclicStart 5)

/-- **The anchored cyclic screen is satisfied with slack zero.**  No player's
exact finite response cap beats the on-path renewal value of this schedule.
Both sides are supplied by the solved finite systems: the cap by
`quittingAnchoredCyclicResponseCap_le_target`, the on-path value by
`quittingAnchoredCyclicOnPathValue_eq_target`.  No asymptotic Nash property of
the profile enters. -/
theorem quittingAnchoredCyclicResponseCap_le_onPathValue (who : Player) :
    quittingAnchoredCyclicResponseCap hardenedReward schedule hazard
        hazard_nonneg hazard_le_one who ≤
      quittingAnchoredCyclicOnPathValue hardenedReward schedule hazard
        hazard_nonneg hazard_le_one (quittingAnchoredCyclicStart 5) who := by
  rw [quittingAnchoredCyclicOnPathValue_eq_target]
  exact quittingAnchoredCyclicResponseCap_le_target who

/-- The same exclusion obtained through the screen's contrapositive rather
than through the exploitability-gap incompatibility, and computed rather than
read off an equilibrium: the inputs are the twenty-five max equations, the
twenty-five renewal equations, the spectator condition, and the arithmetic
`(1/2) ^ 5 ≠ 1`. -/
theorem hardened_isEmpty_counterexampleRegime_via_screen :
    IsEmpty (QuittingCounterexampleRegime hardenedReward) :=
  isEmpty_of_anchoredCyclicResponseSolution_le schedule hazard hazard_nonneg
    hazard_le_one responseSolution
    isAnchoredCyclicResponseSolution_responseSolution exists_spectatorHazard
    fun who ↦ le_of_eq
      (congrFun (congrFun quittingAnchoredCyclicOnPathValue_eq_responseSolution
        (quittingAnchoredCyclicStart 5)) who).symm

end HardenedPentagonCyclicEquilibrium
end GameTheory
