/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Paths.OpponentActionMass
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile

/-!
# Question 175: the negative antitone owner has a Never floor

This experiment formalizes the boundary-sensitive part of the proposed
coalition-toggle/deletion answer to Question 175.  If an owner weakly loses
by joining every nonempty opponent quitting coalition, its solo reward lies
strictly below its punishment value, and that punishment value is nonpositive,
then literal `Never` earns at least the punishment value against every
nonstationary product plan.

The proof uses the stationary characterization of the punishment value only
row by row.  It forces each opponent-absorption row to carry the punishment
floor.  The live ledger then retains that floor even when positive survival
mass remains at infinity; this is where the nonpositive sign is essential.
-/

noncomputable section

namespace GameTheory
namespace Question175OwnerNeverFloor

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `owner` weakly loses by joining every already nonempty coalition of
opponent quitters. -/
def QuittingOwnerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Prop :=
  ∀ (quitters : Finset ι) (hquitters : quitters.Nonempty),
    owner ∉ quitters →
      reward
          ⟨insert owner quitters, Finset.insert_nonempty owner quitters⟩ owner ≤
        reward ⟨quitters, hquitters⟩ owner

/-- Join-antitonicity makes the Continue-minus-join terminal advantage
nonnegative on every action where the owner is forced to Continue. -/
theorem quittingTerminalOpponentAdvantage_nonneg_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hjoin : QuittingOwnerJoinAntitone reward owner)
    (action : ι → Bool) (howner : action owner = false) :
    0 ≤ quittingTerminalOpponentAdvantage reward owner action := by
  unfold quittingTerminalOpponentAdvantage quittingRootPayoff
  rw [quittingQuitters_update_true_of_apply_false]
  by_cases hquitters : (quittingQuitters action).Nonempty
  · simp only [dif_pos hquitters,
      dif_pos (Finset.insert_nonempty owner (quittingQuitters action))]
    apply sub_nonneg.mpr
    apply hjoin (quittingQuitters action) hquitters
    simp [quittingQuitters, howner]
  · have hempty : quittingQuitters action = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hquitters
    simp [hempty, quittingSingletonTerminal]

/-- The expected Continue-minus-join terminal advantage is nonnegative at
every product row. -/
theorem expect_quittingTerminalOpponentAdvantage_nonneg_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner) :
    0 ≤ expect (pmfPi (Function.update root owner (PMF.pure false)))
      (quittingTerminalOpponentAdvantage reward owner) := by
  rw [expect_eq_sum]
  apply Finset.sum_nonneg
  intro action _
  by_cases hmass :
      ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal = 0
  · change 0 ≤
      ((pmfPi (Function.update root owner (PMF.pure false))) action).toReal *
        quittingTerminalOpponentAdvantage reward owner action
    rw [hmass]
    simp
  · have hmassPos :
        0 < ((pmfPi (Function.update root owner
          (PMF.pure false))) action).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hmass)
    have hsupport : action ∈
        (pmfPi (Function.update root owner (PMF.pure false))).support := by
      rw [PMF.mem_support_iff]
      intro hzero
      rw [hzero, ENNReal.toReal_zero] at hmassPos
      exact (lt_irrefl 0 hmassPos).elim
    have howner :=
      action_eq_false_of_mem_support_pmfPi_update_pure_false
        root owner action hsupport
    exact mul_nonneg ENNReal.toReal_nonneg
      (quittingTerminalOpponentAdvantage_nonneg_of_ownerJoinAntitone
        reward owner hjoin action howner)

/-- Under the negative punishment gate, each presented opponent row carries
at least the punishment floor in its Continue-absorption branch. -/
theorem quittingPunishmentValue_mul_one_sub_continueMass_le_continueReward_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner) :
    (1 - quittingStationaryFixedOpponentsContinueMass root owner) *
        quittingPunishmentValue reward owner ≤
      quittingStationaryFixedOpponentsContinueReward reward root owner := by
  let mass := quittingStationaryFixedOpponentsContinueMass root owner
  let absorb := quittingStationaryFixedOpponentsContinueReward reward root owner
  let quitValue := quittingStationaryFixedOpponentsQuitValue reward root owner
  let chi := quittingPunishmentValue reward owner
  have hmass0 : 0 ≤ mass :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root owner
  have hmass1 : mass ≤ 1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one root owner
  by_cases hmassEq : mass = 1
  · have habsorb : absorb = 0 := by
      exact quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
        reward hmassEq
    simp [mass, absorb, hmassEq, habsorb]
  · have hmassLt : mass < 1 := lt_of_le_of_ne hmass1 hmassEq
    have hdenom : 0 < 1 - mass := by linarith
    by_contra hnot
    have habsorbLt : absorb < (1 - mass) * chi := lt_of_not_ge hnot
    have hrideLt : absorb / (1 - mass) < chi := by
      rw [div_lt_iff₀ hdenom]
      nlinarith
    have hexpect :=
      expect_quittingTerminalOpponentAdvantage_nonneg_of_ownerJoinAntitone
        reward root owner hjoin
    rw [expect_terminalOpponentAdvantage,
      quittingRootContinuePayoff_eq_fixedOpponents reward
        (fun _ ↦ root) owner
        (fun _ ↦ reward (quittingSingletonTerminal owner) owner) 0,
      quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
        (fun _ ↦ root) owner (0 : Payoff ι) 0] at hexpect
    change 0 ≤ absorb + mass *
        reward (quittingSingletonTerminal owner) owner - quitValue at hexpect
    have hquitLt : quitValue < chi := by
      nlinarith
    have hcap :=
      quittingPunishmentValue_le_stationaryUnilateralCap reward owner root
    rw [quittingStationaryUnilateralCap_eq_max_div] at hcap
    change chi ≤ max quitValue (absorb / (1 - mass)) at hcap
    linarith [max_lt hquitLt hrideLt]

/-- **Infinite-survival boundary theorem for Question 175.**  Against every
arbitrary nonstationary product plan, literal `Never` earns at least the
owner's punishment value under the negative join-antitone gate. -/
theorem quittingPunishmentValue_le_never_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    quittingPunishmentValue reward owner ≤
      quittingRootSequencePureTimeTerminalValue reward roots owner none 0 := by
  let chi := quittingPunishmentValue reward owner
  have hride : ∀ time,
      (1 - quittingFixedOpponentsContinueMass roots owner time) * chi ≤
        quittingFixedOpponentsContinueReward reward roots owner time := by
    intro time
    simpa [chi] using
      quittingPunishmentValue_mul_one_sub_continueMass_le_continueReward_of_ownerJoinAntitone
        reward (roots time) owner hjoin hsolo
  have hledger : ∀ fuel,
      chi ≤ quittingLiveLedgerAccum reward roots owner 0 fuel := by
    intro fuel
    have haccount := le_quittingLiveLedgerAccum_add_survival_mul
      reward roots owner chi fuel (fun time _ => hride time)
    have hsurvival := quittingOpponentSurvivalWeight_nonneg roots owner 0 fuel
    have htail :
        quittingOpponentSurvivalWeight roots owner 0 fuel * chi ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsurvival hchi
    linarith
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsto_quittingLiveLedgerAccum reward roots owner) hledger

/-- Restarting literal `Never` at a suffix is the same as shifting the
opponent root sequence and restarting at zero. -/
theorem quittingRootSequencePureTimeTerminalValue_none_eq_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots owner none start =
      quittingRootSequencePureTimeTerminalValue reward
        (fun time ↦ roots (start + time)) owner none 0 := by
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
  rw [quittingRootSequenceTerminalValue_eq_shift]
  congr 2

/-- Every deterministic finite quit time is weakly dominated by literal
`Never` under the negative join-antitone gate. -/
theorem quittingRootSequencePureTimeTerminalValue_le_never_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0)
    (quitTime : Option ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots owner quitTime 0 ≤
      quittingRootSequencePureTimeTerminalValue reward roots owner none 0 := by
  cases quitTime with
  | none => exact le_rfl
  | some time =>
      have hfloor : ∀ start,
          quittingPunishmentValue reward owner ≤
            quittingRootSequencePureTimeTerminalValue reward roots owner none
              start := by
        intro start
        rw [quittingRootSequencePureTimeTerminalValue_none_eq_shift]
        exact quittingPunishmentValue_le_never_of_ownerJoinAntitone
          reward (fun offset ↦ roots (start + offset)) owner hjoin hsolo hchi
      have hjoining :
          quittingOutsiderJoiningContribution reward (roots time) owner ≤ 0 := by
        unfold quittingOutsiderJoiningContribution
        have hexpect :=
          expect_quittingTerminalOpponentAdvantage_nonneg_of_ownerJoinAntitone
            reward (roots time) owner hjoin
        linarith
      have hcoefficient : 0 ≤
          1 - quittingRootAbsorptionMass
            (Function.update (roots time) owner (PMF.pure false)) := by
        unfold quittingRootAbsorptionMass
        nlinarith [quittingStationaryContinueMass_nonneg
          (Function.update (roots time) owner (PMF.pure false))]
      have htail : reward (quittingSingletonTerminal owner) owner -
          quittingRootSequencePureTimeTerminalValue reward roots owner none
            (time + 1) ≤ 0 := by
        have := hfloor (time + 1)
        linarith
      have hendpoint : quittingRootEndpointDifference reward
          (fun _ ↦ quittingRootSequencePureTimeTerminalValue
            reward roots owner none (time + 1))
          (roots time) owner ≤ 0 := by
        rw [quittingRootEndpointDifference_eq_outsiderNever]
        have hscaled := mul_nonpos_of_nonneg_of_nonpos hcoefficient htail
        linarith
      have hexact :=
        quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
          reward roots owner 0 time
      simp only [Nat.zero_add] at hexact
      have hreach := quittingOpponentSurvivalWeight_nonneg roots owner 0 time
      have hgain := mul_nonpos_of_nonneg_of_nonpos hreach hendpoint
      linarith

/-- **Full stopping-time theorem for Question 175.**  Literal `Never` is a
best response against every arbitrary behavioral opponent profile under the
negative join-antitone gate.  The arbitrary-deviation step is discharged by
behavioral pure-time extremality, so no stationary-deviation restriction is
present. -/
theorem quittingTerminalPayoff_update_le_never_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0)
    (deviation : (quittingGame reward).BehaviorStrategy owner) :
    quittingTerminalPayoff reward (Function.update profile owner deviation)
        owner ≤
      quittingTerminalPayoff reward
        (Function.update profile owner
          (quittingPureTimeBehaviorStrategy reward owner none)) owner := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward profile owner deviation hε
  have hpure :=
    quittingRootSequencePureTimeTerminalValue_le_never_of_ownerJoinAntitone
      reward (quittingProfileLiveRoot reward profile) owner hjoin hsolo hchi
        quitTime
  rw [← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
      reward profile owner quitTime,
    ← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
      reward profile owner none] at hpure
  linarith

end Question175OwnerNeverFloor
end GameTheory
