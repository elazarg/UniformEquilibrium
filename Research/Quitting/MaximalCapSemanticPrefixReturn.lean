/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ConcentratedCollisionFourRoleMonodromy
import Research.Quitting.MaximalCapSemanticPrefixOrbit
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailProfileAdapter

/-!
# Return packets and stalls on a maximal-cap semantic prefix ray

A family of literal marked rows may have varying behavioral tails while all
rows realize one terminal-semantic source.  Prefixing every row by the same
explicit maximal-cap root word gives a moving family on one scalar debt ray.

This file is source-independent.  It records the exact minimum-return packet
and the quantitative strict-limit stall.  It does not assert that the strict
stall has a downstream consumer or that any finite prefix is near-minimal.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct Math.ProbabilityMassFunction Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Iterated all-Continue spines compose additively. -/
theorem quittingAllContinueProfileSpine_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ℕ) :
    quittingAllContinueProfileSpine reward profile (first + second) =
      quittingAllContinueProfileSpine reward
        (quittingAllContinueProfileSpine reward profile first) second := by
  induction second with
  | zero => simp [quittingAllContinueProfileSpine]
  | succ second ih =>
      rw [Nat.add_succ]
      simp only [quittingAllContinueProfileSpine]
      rw [ih]

/-- Total debt on the autonomous maximal-cap semantic ray. -/
def quittingMaximalCapSemanticPrefixDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum
    (quittingMaximalCapSemanticPrefixOrbit reward source time)

/-- One-step absorption hazard of the autonomous maximal-cap semantic ray. -/
def quittingMaximalCapSemanticPrefixAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) : ℝ :=
  quittingRootAbsorptionMass
    (quittingMaximalCapSemanticRoot reward
      (quittingMaximalCapSemanticPrefixOrbit reward source time))

theorem quittingMaximalCapSemanticPrefixDebt_eq_survival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    quittingMaximalCapSemanticPrefixDebt reward source time =
      quittingMaximalCapSemanticPrefixSurvival reward source time *
        quittingTerminalSemanticDebtSum source :=
  quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq
    reward source time

theorem quittingMaximalCapSemanticPrefixSurvival_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) :
    Antitone (quittingMaximalCapSemanticPrefixSurvival reward source) := by
  apply antitone_nat_of_succ_le
  intro time
  rw [quittingMaximalCapSemanticPrefixSurvival_succ]
  exact mul_le_of_le_one_left
    (quittingMaximalCapSemanticPrefixSurvival_nonneg reward source time)
    (quittingStationaryContinueMass_le_one _)

theorem quittingMaximalCapSemanticPrefixDebt_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hsourceDebt : 0 ≤ quittingTerminalSemanticDebtSum source) :
    Antitone (quittingMaximalCapSemanticPrefixDebt reward source) := by
  intro first second hle
  simp only [quittingMaximalCapSemanticPrefixDebt_eq_survival_mul]
  exact mul_le_mul_of_nonneg_right
    (quittingMaximalCapSemanticPrefixSurvival_antitone reward source hle)
    hsourceDebt

/-- The scalar ray limit, defined as the infimum of its total debts. -/
def quittingMaximalCapSemanticPrefixDebtLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) : ℝ :=
  ⨅ time, quittingMaximalCapSemanticPrefixDebt reward source time

theorem quittingMaximalCapSemanticPrefixDebt_bddBelow_of_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) :
    BddBelow (Set.range
      (quittingMaximalCapSemanticPrefixDebt reward source)) := by
  refine ⟨quittingTerminalSemanticDebtSum minimum, ?_⟩
  rintro _ ⟨time, rfl⟩
  exact hminimum _
    (quittingMaximalCapSemanticPrefixOrbit_mem_carrier
      reward source hsource time)

theorem quittingMaximalCapSemanticPrefixDebt_tendsto_limit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hsourceDebt : 0 ≤ quittingTerminalSemanticDebtSum source) :
    Tendsto (quittingMaximalCapSemanticPrefixDebt reward source) atTop
      (nhds (quittingMaximalCapSemanticPrefixDebtLimit reward source)) := by
  apply tendsto_atTop_ciInf
    (quittingMaximalCapSemanticPrefixDebt_antitone
      reward source hsourceDebt)
  exact quittingMaximalCapSemanticPrefixDebt_bddBelow_of_minimum
    reward minimum source hminimum hsource

theorem minimumDebt_le_quittingMaximalCapSemanticPrefixDebtLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticDebtSum minimum ≤
      quittingMaximalCapSemanticPrefixDebtLimit reward source := by
  apply le_ciInf
  intro time
  exact hminimum _
    (quittingMaximalCapSemanticPrefixOrbit_mem_carrier
      reward source hsource time)

theorem quittingMaximalCapSemanticPrefixDebtLimit_le_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (time : ℕ) :
    quittingMaximalCapSemanticPrefixDebtLimit reward source ≤
      quittingMaximalCapSemanticPrefixDebt reward source time :=
  ciInf_le
    (quittingMaximalCapSemanticPrefixDebt_bddBelow_of_minimum
      reward minimum source hminimum hsource) time

theorem quittingMaximalCapSemanticPrefixSurvival_tendsto_limit_div
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) :
    Tendsto (quittingMaximalCapSemanticPrefixSurvival reward source) atTop
      (nhds (quittingMaximalCapSemanticPrefixDebtLimit reward source /
        quittingTerminalSemanticDebtSum source)) := by
  have hsourcePos : 0 < quittingTerminalSemanticDebtSum source :=
    hminimumPos.trans_le (hminimum source hsource)
  have hdebt := quittingMaximalCapSemanticPrefixDebt_tendsto_limit
    reward minimum source hminimum hsource hsourcePos.le
  have hdiv := hdebt.div_const (quittingTerminalSemanticDebtSum source)
  convert hdiv using 1
  funext time
  rw [quittingMaximalCapSemanticPrefixDebt_eq_survival_mul]
  field_simp

theorem quittingMaximalCapSemanticPrefixDebt_mul_absorption_eq_drop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (time : ℕ) :
    quittingMaximalCapSemanticPrefixDebt reward source time *
        quittingMaximalCapSemanticPrefixAbsorption reward source time =
      quittingMaximalCapSemanticPrefixDebt reward source time -
        quittingMaximalCapSemanticPrefixDebt reward source (time + 1) := by
  rw [quittingMaximalCapSemanticPrefixDebt_eq_survival_mul,
    quittingMaximalCapSemanticPrefixDebt_eq_survival_mul,
    quittingMaximalCapSemanticPrefixSurvival_succ]
  unfold quittingMaximalCapSemanticPrefixAbsorption
  unfold quittingRootAbsorptionMass
  ring

theorem sum_quittingMaximalCapSemanticPrefixDebt_mul_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
        quittingMaximalCapSemanticPrefixDebt reward source time *
          quittingMaximalCapSemanticPrefixAbsorption reward source time) =
      quittingTerminalSemanticDebtSum source -
        quittingMaximalCapSemanticPrefixDebt reward source horizon := by
  induction horizon with
  | zero => simp [quittingMaximalCapSemanticPrefixDebt]
  | succ horizon ih =>
      rw [Finset.sum_range_succ, ih,
        quittingMaximalCapSemanticPrefixDebt_mul_absorption_eq_drop]
      ring

theorem hasSum_quittingMaximalCapSemanticPrefixDebt_mul_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) :
    HasSum (fun time ↦
      quittingMaximalCapSemanticPrefixDebt reward source time *
        quittingMaximalCapSemanticPrefixAbsorption reward source time)
      (quittingTerminalSemanticDebtSum source -
        quittingMaximalCapSemanticPrefixDebtLimit reward source) := by
  have hsourceNonneg : 0 ≤ quittingTerminalSemanticDebtSum source :=
    Finset.sum_nonneg fun who _ ↦
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hsource who
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun time ↦
    mul_nonneg
      (by
        rw [quittingMaximalCapSemanticPrefixDebt_eq_survival_mul]
        exact mul_nonneg
          (quittingMaximalCapSemanticPrefixSurvival_nonneg reward source time)
          hsourceNonneg)
      (quittingRootAbsorptionMass_nonneg _)) _).2
  have hconst : Tendsto
      (fun _ : ℕ ↦ quittingTerminalSemanticDebtSum source) atTop
      (nhds (quittingTerminalSemanticDebtSum source)) :=
    tendsto_const_nhds
  have htendsto := hconst.sub
    (quittingMaximalCapSemanticPrefixDebt_tendsto_limit reward minimum source
      hminimum hsource hsourceNonneg)
  convert htendsto using 1
  funext horizon
  simpa only [quittingMaximalCapSemanticPrefixAbsorption] using
    (sum_quittingMaximalCapSemanticPrefixDebt_mul_absorption
      reward source horizon)

/-- A varying family of marked rows with one common semantic source. -/
structure QuittingCommonSemanticMarkedBaseFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (owner : ι) (terminal : {S : Finset ι // S.Nonempty}) where
  profiles : ℕ → (quittingGame reward).BehaviorProfile
  tails : ℕ → (quittingGame reward).BehaviorProfile
  source_eq : ∀ index,
    quittingTerminalSemanticPair reward (profiles index) = source
  postMarkSpine_eq : ∀ index,
    quittingAllContinueProfileSpine reward (profiles index) 1 = tails index
  stageMass_eq_one : ∀ index,
    quittingStageCoalitionMass reward (profiles index) 0 terminal = 1
  ownerDefect_eq_zero : ∀ index,
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward (tails index)).1
      (quittingProfileLiveRoot reward (profiles index) 0) owner = 0
  tailDebt_tendsto : Tendsto (fun index ↦
    quittingTerminalDebtSum reward (tails index)) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum))

namespace QuittingCommonSemanticMarkedBaseFamily

variable
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {minimum source : QuittingTerminalSemanticPair ι}
  {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}

/-- Put the `index`th marked row behind the first `index` roots of the one
common maximal-cap semantic ray. -/
def rayProfiles
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) : ℕ → (quittingGame reward).BehaviorProfile :=
  fun index ↦ quittingMaximalCapSemanticPrefixProfile reward source
    (family.profiles index) index

def rayMark
    (_family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) : ℕ → ℕ := id

def rayCutoff
    (_family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) : ℕ → ℕ := fun index ↦ index + 1

def rayScale
    (_family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) : ℕ → ℝ := fun index ↦ 1 / ((index : ℝ) + 1)

theorem rayScale_pos
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) (index : ℕ) :
    0 < family.rayScale index := by
  simp only [rayScale]
  positivity

theorem rayScale_tendsto_zero
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) :
    Tendsto family.rayScale atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem rayProfiles_semantic_eq
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) (index : ℕ) :
    quittingTerminalSemanticPair reward (family.rayProfiles index) =
      quittingMaximalCapSemanticPrefixOrbit reward source index :=
  quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
    reward source (family.profiles index) (family.source_eq index) index

theorem rayProfiles_spine_eq_base
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) (index : ℕ) :
    quittingAllContinueProfileSpine reward (family.rayProfiles index) index =
      family.profiles index :=
  quittingAllContinueProfileSpine_maximalCapSemanticPrefixProfile
    reward source (family.profiles index) index

theorem rayProfiles_postMarkSpine_eq_tail
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) (index : ℕ) :
    quittingAllContinueProfileSpine reward (family.rayProfiles index)
        (index + 1) =
      family.tails index := by
  rw [quittingAllContinueProfileSpine_add,
    family.rayProfiles_spine_eq_base, family.postMarkSpine_eq]

theorem rayProfiles_markedRoot_eq
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) (index : ℕ) :
    quittingProfileLiveRoot reward (family.rayProfiles index) index =
      quittingProfileLiveRoot reward (family.profiles index) 0 := by
  calc
    quittingProfileLiveRoot reward (family.rayProfiles index) index =
        quittingProfileLiveRoot reward
          (quittingAllContinueProfileSpine reward
            (family.rayProfiles index) index) 0 := by
      simpa using (quittingProfileLiveRoot_allContinueSpine reward
        (family.rayProfiles index) index 0).symm
    _ = quittingProfileLiveRoot reward (family.profiles index) 0 := by
      rw [family.rayProfiles_spine_eq_base]

theorem rayProfiles_stageMass_eq_survival
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) (index : ℕ) :
    quittingStageCoalitionMass reward (family.rayProfiles index) index
        terminal =
      quittingMaximalCapSemanticPrefixSurvival reward source index := by
  simpa only [rayProfiles, Nat.add_zero, family.stageMass_eq_one index,
    mul_one] using
    (quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add
      reward source (family.profiles index) index 0 terminal)

theorem rayProfiles_ownerDefect_eq_zero
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) (index : ℕ) :
    quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (family.rayProfiles index)
            (index + 1))).1
        (quittingProfileLiveRoot reward (family.rayProfiles index) index)
        owner = 0 := by
  rw [family.rayProfiles_postMarkSpine_eq_tail,
    family.rayProfiles_markedRoot_eq]
  exact family.ownerDefect_eq_zero index

theorem rayProfiles_wholeDebt_eq
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) (index : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (family.rayProfiles index)) =
      quittingMaximalCapSemanticPrefixDebt reward source index := by
  rw [family.rayProfiles_semantic_eq]
  rfl

theorem rayProfiles_tailDebt_tendsto_minimum
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal) :
    Tendsto (fun index ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (family.rayProfiles index)
          (index + 1)))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum)) := by
  convert family.tailDebt_tendsto using 1
  funext index
  rw [family.rayProfiles_postMarkSpine_eq_tail,
    quittingTerminalDebtSum_eq_terminalSemanticDebtSum]

/-- In the minimum-return arm, the diagonal ray family is one actual moving
concentrated packet with fixed resolution `D_* / D_0`. -/
def returnPacket
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) :
    QuittingReprojectionConcentratedPacket reward family.rayProfiles owner
      terminal family.rayCutoff family.rayScale where
  resolution := quittingTerminalSemanticDebtSum minimum /
    quittingTerminalSemanticDebtSum source
  resolution_pos := by
    exact div_pos hminimumPos (hminimumPos.trans_le (hminimum source hsource))
  subseq := id
  subseq_strictMono := strictMono_id
  mark := family.rayMark
  mark_lt := by intro rank; simp [rayMark, rayCutoff]
  stageMass := by
    intro rank
    simpa only [rayMark, id_eq, family.rayProfiles_stageMass_eq_survival] using
      (minimumDebt_div_sourceDebt_le_maximalCapSemanticPrefixSurvival
        reward minimum source hminimum hminimumPos hsource rank)
  semanticPrefix := by
    intro rank
    have hmass : 0 < quittingStageCoalitionMass reward
        (family.rayProfiles rank) rank terminal := by
      rw [family.rayProfiles_stageMass_eq_survival]
      exact quittingMaximalCapSemanticPrefixSurvival_pos_of_positiveMinimum
        reward minimum source hminimum hminimumPos hsource rank
    simpa only [rayMark, id_eq] using
      positive_stageCoalitionMass_has_semanticPrefixIncidence reward
        (family.rayProfiles rank) rank terminal hmass
  defect_tendsto := by
    have hzero : (fun rank ↦
        (quittingLiveMass reward (family.rayProfiles rank) rank *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward
                (family.rayProfiles rank) (rank + 1))).1
            (quittingProfileLiveRoot reward (family.rayProfiles rank) rank)
            owner) /
          family.rayScale rank) = fun _rank ↦ 0 := by
      funext rank
      rw [family.rayProfiles_ownerDefect_eq_zero, mul_zero, zero_div]
    simpa only [rayMark, id_eq, hzero] using
      (tendsto_const_nhds : Tendsto (fun _rank : ℕ ↦ (0 : ℝ)) atTop (nhds 0))

theorem returnPacket_resolution_eq
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) :
    (family.returnPacket hminimum hminimumPos hsource).resolution =
      quittingTerminalSemanticDebtSum minimum /
        quittingTerminalSemanticDebtSum source := rfl

theorem rayProfiles_wholeDebt_tendsto_minimum
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hreturn : quittingMaximalCapSemanticPrefixDebtLimit reward source =
      quittingTerminalSemanticDebtSum minimum) :
    Tendsto (fun index ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (family.rayProfiles index))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum)) := by
  have hsourceNonneg : 0 ≤ quittingTerminalSemanticDebtSum source :=
    Finset.sum_nonneg fun who _ ↦
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hsource who
  simpa only [family.rayProfiles_wholeDebt_eq, hreturn] using
    quittingMaximalCapSemanticPrefixDebt_tendsto_limit reward minimum source
      hminimum hsource hsourceNonneg

/-- The equality-arm moving packet reaches the checked limit-chord consumer;
the fixed positive tail escape cannot recur because the marked tails return
to the same minimum debt. -/
theorem nonempty_threeRoleLimitChord_of_return
    [Nonempty ι]
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hcollision : 1 < terminal.val.card)
    (hreturn : quittingMaximalCapSemanticPrefixDebtLimit reward source =
      quittingTerminalSemanticDebtSum minimum) :
    ∃ mover recipient,
      Nonempty (ConcentratedCollisionFourRole.ThreeRoleLimitChord reward
        minimum owner mover recipient
          (family.returnPacket hminimum hminimumPos hsource).resolution) := by
  let packet := family.returnPacket hminimum hminimumPos hsource
  have hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (ConcentratedCollisionFourRole.source reward
          (ConcentratedCollisionFourRole.packetProfile packet rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum)) := by
    simpa [packet, ConcentratedCollisionFourRole.packetProfile,
      ConcentratedCollisionFourRole.source, returnPacket] using
      family.rayProfiles_wholeDebt_tendsto_minimum hminimum hsource hreturn
  have hdispatch :=
    ConcentratedCollisionFourRole.packet_tailEscapeFrequently_or_threeRoleLimitChord
      minimum packet hminimumCarrier hminimum hminimumPos hcollision
        family.rayScale_pos family.rayScale_tendsto_zero hsourceDebt
  rcases hdispatch with hescape | hchord
  · have htail := family.rayProfiles_tailDebt_tendsto_minimum
    have hdiff : Tendsto (fun rank ↦
        quittingTerminalSemanticDebtSum
            (ConcentratedCollisionFourRole.tail reward
              (ConcentratedCollisionFourRole.packetProfile packet rank)
              (packet.mark rank)) -
          quittingTerminalSemanticDebtSum minimum) atTop (nhds 0) := by
      have hsub := htail.sub_const
        (quittingTerminalSemanticDebtSum minimum)
      simpa [packet, ConcentratedCollisionFourRole.packetProfile,
        ConcentratedCollisionFourRole.tail, returnPacket, rayMark] using hsub
    have hthreshold : 0 <
        packet.resolution * quittingTerminalSemanticDebtSum minimum / 2 :=
      div_pos (mul_pos packet.resolution_pos hminimumPos) (by norm_num)
    have hsmall : ∀ᶠ rank in atTop,
        ¬ ConcentratedCollisionFourRole.packetEscape minimum packet rank := by
      filter_upwards [hdiff.eventually_lt_const hthreshold] with rank hlt
      exact not_le_of_gt hlt
    exact (not_frequently.mpr hsmall hescape).elim
  · exact hchord

/-- The row-wise compiler itself is eventually in its executable transfer
arm in the minimum-return case. -/
theorem eventually_threeRoleTransfer_of_return
    [Nonempty ι]
    (family : QuittingCommonSemanticMarkedBaseFamily reward minimum source
      owner terminal)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hcollision : 1 < terminal.val.card)
    (hreturn : quittingMaximalCapSemanticPrefixDebtLimit reward source =
      quittingTerminalSemanticDebtSum minimum) :
    ∀ᶠ rank in atTop,
      Nonempty (ConcentratedCollisionFourRole.packetTransfer minimum
        (family.returnPacket hminimum hminimumPos hsource) rank) := by
  let packet := family.returnPacket hminimum hminimumPos hsource
  have hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (ConcentratedCollisionFourRole.source reward
          (ConcentratedCollisionFourRole.packetProfile packet rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum)) := by
    simpa [packet, ConcentratedCollisionFourRole.packetProfile,
      ConcentratedCollisionFourRole.source, returnPacket] using
      family.rayProfiles_wholeDebt_tendsto_minimum hminimum hsource hreturn
  have hdispatch :=
    ConcentratedCollisionFourRole.packet_eventually_tailEscape_or_threeRoleTransfer
      minimum packet hminimumCarrier hminimum hminimumPos hcollision
        family.rayScale_pos family.rayScale_tendsto_zero hsourceDebt
  have htail := family.rayProfiles_tailDebt_tendsto_minimum
  have hdiff : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
          (ConcentratedCollisionFourRole.tail reward
            (ConcentratedCollisionFourRole.packetProfile packet rank)
            (packet.mark rank)) -
        quittingTerminalSemanticDebtSum minimum) atTop (nhds 0) := by
    have hsub := htail.sub_const
      (quittingTerminalSemanticDebtSum minimum)
    simpa [packet, ConcentratedCollisionFourRole.packetProfile,
      ConcentratedCollisionFourRole.tail, returnPacket, rayMark] using hsub
  have hthreshold : 0 <
      packet.resolution * quittingTerminalSemanticDebtSum minimum / 2 :=
    div_pos (mul_pos packet.resolution_pos hminimumPos) (by norm_num)
  have hsmall : ∀ᶠ rank in atTop,
      ¬ ConcentratedCollisionFourRole.packetEscape minimum packet rank := by
    filter_upwards [hdiff.eventually_lt_const hthreshold] with rank hlt
    exact not_le_of_gt hlt
  filter_upwards [hdispatch, hsmall] with rank hrow hnot
  exact hrow.resolve_left hnot

end QuittingCommonSemanticMarkedBaseFamily

/-- The executable joint semantic/law point at one depth of the common
maximal-cap ray. -/
def quittingMaximalCapSemanticPrefixLawPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    QuittingTerminalSemanticLawPoint ι :=
  let profile :=
    quittingMaximalCapSemanticPrefixProfile reward source terminal time
  (quittingTerminalSemanticPair reward profile,
    quittingTerminalOutcomeMass reward profile)

/-- A joint semantic/law cluster of one executable realization of the common
ray.  It retains the exact scalar limit and the corresponding lower bound on
one shifted suffix atom. -/
structure QuittingMaximalCapSemanticPrefixRetainedLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (coalition : {S : Finset ι // S.Nonempty}) where
  cluster : QuittingTerminalSemanticLawPoint ι
  cluster_mem : cluster ∈ quittingTerminalSemanticLawCarrier reward
  debt_eq_limit : quittingTerminalSemanticDebtSum cluster.1 =
    quittingMaximalCapSemanticPrefixDebtLimit reward source
  atom_lower :
    quittingMaximalCapSemanticPrefixDebtLimit reward source /
          quittingTerminalSemanticDebtSum source *
        quittingStageCoalitionMass reward terminal stage coalition ≤
      cluster.2 (some coalition)
  atom_pos : 0 < cluster.2 (some coalition)
  allContinue_exactNash : IsεQuittingRootNash reward cluster.1.2 0
    (quittingAllContinueRoot : ι → PMF Bool)
  allContinue_or_supportEntry :
    (∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cluster.1.2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) ∨
      ∃ root : ι → PMF Bool,
        IsεQuittingRootNash reward cluster.1.2 0 root ∧
          0 < quittingRootAbsorptionMass root

/-- Every convergent subsequence of executable joint semantic/law points on
the common ray has debt exactly `L`, retains the sharp marked-atom lower bound
`L / D_0`, and has the all-Continue/support-entry limit alternative. -/
theorem quittingMaximalCapSemanticPrefixLawPoint_cluster_facts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source)
    (stage : ℕ) (coalition : {S : Finset ι // S.Nonempty})
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hatom : 0 < quittingStageCoalitionMass reward terminal stage coalition)
    (cluster : QuittingTerminalSemanticLawPoint ι)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq)
    (hpointLimit : Tendsto (fun rank ↦
      quittingMaximalCapSemanticPrefixLawPoint reward source terminal
        (subseq rank)) atTop (nhds cluster)) :
    cluster ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebtSum cluster.1 =
        quittingMaximalCapSemanticPrefixDebtLimit reward source ∧
      quittingMaximalCapSemanticPrefixDebtLimit reward source /
            quittingTerminalSemanticDebtSum source *
          quittingStageCoalitionMass reward terminal stage coalition ≤
        cluster.2 (some coalition) ∧
      0 < cluster.2 (some coalition) ∧
      IsεQuittingRootNash reward cluster.1.2 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      ((∀ root : ι → PMF Bool,
          IsεQuittingRootNash reward cluster.1.2 0 root →
            root = (quittingAllContinueRoot : ι → PMF Bool)) ∨
        ∃ root : ι → PMF Bool,
          IsεQuittingRootNash reward cluster.1.2 0 root ∧
            0 < quittingRootAbsorptionMass root) := by
  let profile : ℕ → (quittingGame reward).BehaviorProfile := fun time ↦
    quittingMaximalCapSemanticPrefixProfile reward source terminal time
  let root : ℕ → ι → PMF Bool := fun time ↦
    quittingMaximalCapSemanticRoot reward
      (quittingMaximalCapSemanticPrefixOrbit reward source time)
  let point : ℕ → QuittingTerminalSemanticLawPoint ι :=
    quittingMaximalCapSemanticPrefixLawPoint reward source terminal
  have hpointMem : ∀ time,
      point time ∈ quittingTerminalSemanticLawCarrier reward := fun time ↦
    quittingTerminalSemanticLawPoint_mem_carrier reward (profile time)
  have hrootAbsorption : Tendsto
      (fun time ↦ quittingRootAbsorptionMass (root time)) atTop (nhds 0) := by
    have hsum := summable_maximalCapPrefix_absorption reward minimum terminal
      hminimum hminimumPos
    have heq : (fun time ↦ quittingRootAbsorptionMass (root time)) =
        fun time ↦ quittingRootAbsorptionMass
          (quittingMaximalCapPrefixRoot reward
            (quittingMaximalCapPrefixProfile reward terminal time)) := by
      funext time
      apply congrArg quittingRootAbsorptionMass
      unfold root quittingMaximalCapSemanticRoot quittingMaximalCapPrefixRoot
      apply quittingMaximalAbsorptionCapRoot_eq_of_cap_eq reward
      rw [quittingMaximalCapPrefixProfile_eq_semanticPrefixProfile,
        hterminal]
      exact congrArg Prod.snd
        (quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
          reward source terminal hterminal time).symm
    rw [heq]
    exact hsum.tendsto_atTop_zero
  have hquit : ∀ who, Tendsto (fun time ↦ (root time who true).toReal)
      atTop (nhds 0) := by
    intro who
    apply squeeze_zero
    · exact fun _ ↦ ENNReal.toReal_nonneg
    · exact fun time ↦ quitProbability_le_quittingRootAbsorptionMass
        (root time) who
    · exact hrootAbsorption
  let simplexRoot : ℕ → QuittingRootSimplex ι :=
    fun time who ↦ stdSimplexEquiv (root time who)
  have hsimplexRoot : Tendsto simplexRoot atTop
      (nhds (quittingAllContinueSimplexRoot : QuittingRootSimplex ι)) := by
    rw [tendsto_pi_nhds]
    intro who
    rw [tendsto_subtype_rng, tendsto_pi_nhds]
    intro action
    have hcoordinate : ∀ time,
        ((simplexRoot time who : stdSimplex ℝ Bool) : Bool → ℝ) action =
          (root time who action).toReal := fun time ↦
      congrFun (coe_stdSimplexEquiv_apply (root time who)) action
    have hallCoordinate :
        (((quittingAllContinueSimplexRoot : QuittingRootSimplex ι) who :
          stdSimplex ℝ Bool) : Bool → ℝ) action =
            (PMF.pure false action).toReal :=
      congrFun (coe_stdSimplexEquiv_apply (PMF.pure false)) action
    have hbase : Tendsto (fun time ↦ (root time who action).toReal)
        atTop (nhds ((PMF.pure false action).toReal)) := by
      cases action with
      | true => simpa using hquit who
      | false =>
          have hidentity : (fun time ↦ (root time who false).toReal) =
              fun time ↦ 1 - (root time who true).toReal := by
            funext time
            linarith [quittingRoot_continueProbability_add_quitProbability
              (root time) who]
          rw [hidentity]
          simpa using tendsto_const_nhds.sub (hquit who)
    have hactual := hbase.congr'
      (Filter.Eventually.of_forall fun time ↦ (hcoordinate time).symm)
    convert hactual using 1
    · rfl
    · exact congrArg nhds hallCoordinate
  have hpointLimit' : Tendsto (fun rank ↦ point (subseq rank)) atTop
      (nhds cluster) := by
    simpa only [point] using hpointLimit
  have hcluster : cluster ∈ quittingTerminalSemanticLawCarrier reward :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).isClosed.mem_of_tendsto
      hpointLimit' (Filter.Eventually.of_forall fun rank ↦
        hpointMem (subseq rank))
  have hpairLimit : Tendsto (fun rank ↦ (point (subseq rank)).1) atTop
      (nhds cluster.1) :=
    continuous_fst.continuousAt.tendsto.comp hpointLimit'
  have hcapLimit : Tendsto (fun rank ↦ (point (subseq rank)).1.2) atTop
      (nhds cluster.1.2) :=
    continuous_snd.continuousAt.tendsto.comp hpairLimit
  have hrootLimit : Tendsto (fun rank ↦ simplexRoot (subseq rank)) atTop
      (nhds (quittingAllContinueSimplexRoot : QuittingRootSimplex ι)) :=
    hsimplexRoot.comp hsubseq.tendsto_atTop
  have hnashLimit : IsεQuittingRootEndpointNash reward cluster.1.2 0
      (quittingRootOfSimplex
        (quittingAllContinueSimplexRoot : QuittingRootSimplex ι)) := by
    apply isεQuittingRootEndpointNash_of_tendsto reward
      (fun _ : ℕ ↦ 0) (fun rank ↦ (point (subseq rank)).1.2)
      (fun rank ↦ simplexRoot (subseq rank)) tendsto_const_nhds
        hcapLimit hrootLimit
    filter_upwards [] with rank
    have hnash := quittingMaximalCapSemanticRoot_exactNash reward
      (quittingMaximalCapSemanticPrefixOrbit reward source (subseq rank))
    have hrootEq : quittingRootOfSimplex (simplexRoot (subseq rank)) =
        root (subseq rank) := by
      funext who
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
        (root (subseq rank) who)
    rw [hrootEq]
    have hpointEq : (point (subseq rank)).1 =
        quittingMaximalCapSemanticPrefixOrbit reward source
          (subseq rank) := by
      exact quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
        reward source terminal hterminal (subseq rank)
    rw [hpointEq]
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward _ 0 _).2 hnash
  have hdebtCluster : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum (point (subseq rank)).1) atTop
      (nhds (quittingTerminalSemanticDebtSum cluster.1)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hpairLimit
  have hsourcePos : 0 < quittingTerminalSemanticDebtSum source :=
    hminimumPos.trans_le (hminimum source hsource)
  have hdebtRay : Tendsto (fun rank ↦
      quittingMaximalCapSemanticPrefixDebt reward source (subseq rank)) atTop
      (nhds (quittingMaximalCapSemanticPrefixDebtLimit reward source)) :=
    (quittingMaximalCapSemanticPrefixDebt_tendsto_limit reward minimum source
      hminimum hsource hsourcePos.le).comp hsubseq.tendsto_atTop
  have hdebtEq : (fun rank ↦
      quittingTerminalSemanticDebtSum (point (subseq rank)).1) =
      fun rank ↦
        quittingMaximalCapSemanticPrefixDebt reward source (subseq rank) := by
    funext rank
    change quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapSemanticPrefixProfile reward source terminal
            (subseq rank))) = _
    rw [quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
      reward source terminal hterminal]
    rfl
  have hclusterDebt : quittingTerminalSemanticDebtSum cluster.1 =
      quittingMaximalCapSemanticPrefixDebtLimit reward source := by
    rw [hdebtEq] at hdebtCluster
    exact tendsto_nhds_unique hdebtCluster hdebtRay
  have hlawLimit : Tendsto (fun rank ↦
      (point (subseq rank)).2 (some coalition)) atTop
      (nhds (cluster.2 (some coalition))) :=
    ((continuous_apply (some coalition)).comp continuous_snd).continuousAt
      |>.tendsto.comp hpointLimit'
  let lower := quittingMaximalCapSemanticPrefixDebtLimit reward source /
      quittingTerminalSemanticDebtSum source *
        quittingStageCoalitionMass reward terminal stage coalition
  have hlower : ∀ time, lower ≤ (point time).2 (some coalition) := by
    intro time
    have hlimit := quittingMaximalCapSemanticPrefixDebtLimit_le_debt
      reward minimum source hminimum hsource time
    have hratio : quittingMaximalCapSemanticPrefixDebtLimit reward source /
          quittingTerminalSemanticDebtSum source ≤
        quittingMaximalCapSemanticPrefixSurvival reward source time := by
      apply (div_le_iff₀ hsourcePos).2
      rw [← quittingMaximalCapSemanticPrefixDebt_eq_survival_mul]
      exact hlimit
    have hscaled := mul_le_mul_of_nonneg_right hratio hatom.le
    have hstage :=
      quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add reward
        source terminal time stage coalition
    have hstageLaw := quittingStageCoalitionMass_le_terminalOutcomeMass reward
      (profile time) (time + stage) coalition
    exact hscaled.trans_eq hstage.symm |>.trans hstageLaw
  have hlawLower : lower ≤ cluster.2 (some coalition) :=
    ge_of_tendsto' hlawLimit fun rank ↦ hlower (subseq rank)
  have hlimitPos : 0 <
      quittingMaximalCapSemanticPrefixDebtLimit reward source :=
    hminimumPos.trans_le
      (minimumDebt_le_quittingMaximalCapSemanticPrefixDebtLimit reward
        minimum source hminimum hsource)
  have hlowerPos : 0 < lower :=
    mul_pos (div_pos hlimitPos hsourcePos) hatom
  have hnashAllContinue : IsεQuittingRootNash reward cluster.1.2 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    rw [← quittingRootOfSimplex_allContinueSimplexRoot]
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward cluster.1.2 0 _).1 hnashLimit
  have hsplit :
      (∀ candidate : ι → PMF Bool,
        IsεQuittingRootNash reward cluster.1.2 0 candidate →
          candidate = (quittingAllContinueRoot : ι → PMF Bool)) ∨
        ∃ candidate : ι → PMF Bool,
          IsεQuittingRootNash reward cluster.1.2 0 candidate ∧
            0 < quittingRootAbsorptionMass candidate := by
    by_cases hunique : ∀ candidate : ι → PMF Bool,
        IsεQuittingRootNash reward cluster.1.2 0 candidate →
          candidate = (quittingAllContinueRoot : ι → PMF Bool)
    · exact Or.inl hunique
    · right
      push Not at hunique
      obtain ⟨candidate, hnash, hne⟩ := hunique
      refine ⟨candidate, hnash, ?_⟩
      apply lt_of_le_of_ne (quittingRootAbsorptionMass_nonneg candidate)
      intro hzero
      apply hne
      have hcontinue : quittingStationaryContinueMass candidate = 1 := by
        unfold quittingRootAbsorptionMass at hzero
        linarith
      funext who
      simpa [quittingAllContinueRoot] using
        eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who
  exact ⟨hcluster, hclusterDebt, hlawLower, hlowerPos.trans_le hlawLower,
    hnashAllContinue, hsplit⟩

/-- Compactness selects a retained law; the universal cluster theorem supplies
all of its sharp facts. -/
theorem nonempty_quittingMaximalCapSemanticPrefixRetainedLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source)
    (stage : ℕ) (coalition : {S : Finset ι // S.Nonempty})
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hatom : 0 < quittingStageCoalitionMass reward terminal stage coalition) :
    Nonempty (QuittingMaximalCapSemanticPrefixRetainedLaw reward source
      terminal stage coalition) := by
  let point : ℕ → QuittingTerminalSemanticLawPoint ι :=
    quittingMaximalCapSemanticPrefixLawPoint reward source terminal
  have hpointMem : ∀ time,
      point time ∈ quittingTerminalSemanticLawCarrier reward := fun time ↦
    quittingTerminalSemanticLawPoint_mem_carrier reward
      (quittingMaximalCapSemanticPrefixProfile reward source terminal time)
  obtain ⟨cluster, _, subseq, hsubseq, hpointLimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq
      hpointMem
  have hfacts := quittingMaximalCapSemanticPrefixLawPoint_cluster_facts
    reward minimum source terminal hterminal stage coalition hminimum
      hminimumPos hsource hatom cluster subseq hsubseq (by
        simpa only [point, Function.comp_def] using hpointLimit)
  exact ⟨{
    cluster := cluster
    cluster_mem := hfacts.1
    debt_eq_limit := hfacts.2.1
    atom_lower := hfacts.2.2.1
    atom_pos := hfacts.2.2.2.1
    allContinue_exactNash := hfacts.2.2.2.2.1
    allContinue_or_supportEntry := hfacts.2.2.2.2.2
  }⟩

/-- Quantitative information retained in the strict scalar-ray arm. -/
structure QuittingMaximalCapSemanticPrefixRayStall
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source : QuittingTerminalSemanticPair ι) where
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  source_mem : source ∈ quittingTerminalSemanticCarrier reward
  minimum_global : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate
  minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum
  strict : quittingTerminalSemanticDebtSum minimum <
    quittingMaximalCapSemanticPrefixDebtLimit reward source

namespace QuittingMaximalCapSemanticPrefixRayStall

variable
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {minimum source : QuittingTerminalSemanticPair ι}

theorem sourceDebt_pos
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source) :
    0 < quittingTerminalSemanticDebtSum source :=
  stall.minimum_pos.trans_le (stall.minimum_global source stall.source_mem)

theorem debt_tendsto
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source) :
    Tendsto (quittingMaximalCapSemanticPrefixDebt reward source) atTop
      (nhds (quittingMaximalCapSemanticPrefixDebtLimit reward source)) :=
  quittingMaximalCapSemanticPrefixDebt_tendsto_limit reward minimum source
    stall.minimum_global stall.source_mem stall.sourceDebt_pos.le

theorem survival_tendsto
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source) :
    Tendsto (quittingMaximalCapSemanticPrefixSurvival reward source) atTop
      (nhds (quittingMaximalCapSemanticPrefixDebtLimit reward source /
        quittingTerminalSemanticDebtSum source)) :=
  quittingMaximalCapSemanticPrefixSurvival_tendsto_limit_div reward minimum
    source stall.minimum_global stall.minimum_pos stall.source_mem

theorem weightedAbsorption_hasSum
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source) :
    HasSum (fun time ↦
      quittingMaximalCapSemanticPrefixDebt reward source time *
        quittingMaximalCapSemanticPrefixAbsorption reward source time)
      (quittingTerminalSemanticDebtSum source -
        quittingMaximalCapSemanticPrefixDebtLimit reward source) :=
  hasSum_quittingMaximalCapSemanticPrefixDebt_mul_absorption reward minimum
    source stall.minimum_global stall.source_mem

theorem summable_absorption
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source) :
    Summable (quittingMaximalCapSemanticPrefixAbsorption reward source) := by
  have hsum := summable_maximalCapPrefix_absorption reward minimum terminal
    stall.minimum_global stall.minimum_pos
  apply hsum.congr
  intro time
  apply congrArg quittingRootAbsorptionMass
  unfold quittingMaximalCapSemanticRoot quittingMaximalCapPrefixRoot
  apply quittingMaximalAbsorptionCapRoot_eq_of_cap_eq reward
  have hsemantic :=
    quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
      reward source terminal hterminal time
  have hprofile := quittingMaximalCapPrefixProfile_eq_semanticPrefixProfile
    reward terminal time
  rw [hprofile, hterminal]
  exact congrArg Prod.snd hsemantic

theorem absorption_tsum_le_exact_debtDrop
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source) :
    ∑' time, quittingMaximalCapSemanticPrefixAbsorption reward source time ≤
      (quittingTerminalSemanticDebtSum source -
          quittingMaximalCapSemanticPrefixDebtLimit reward source) /
        quittingTerminalSemanticDebtSum minimum := by
  let absorption := quittingMaximalCapSemanticPrefixAbsorption reward source
  let weighted := fun time ↦
    quittingMaximalCapSemanticPrefixDebt reward source time * absorption time
  have habsorption : Summable absorption :=
    stall.summable_absorption terminal hterminal
  have hweighted : Summable weighted := stall.weightedAbsorption_hasSum.summable
  have hmajor : Summable (fun time ↦
      (1 / quittingTerminalSemanticDebtSum minimum) * weighted time) :=
    hweighted.mul_left _
  have hpoint : ∀ time, absorption time ≤
      (1 / quittingTerminalSemanticDebtSum minimum) * weighted time := by
    intro time
    have hminimumDebt := stall.minimum_global _
      (quittingMaximalCapSemanticPrefixOrbit_mem_carrier reward source
        stall.source_mem time)
    have habsorptionNonneg : 0 ≤ absorption time :=
      quittingRootAbsorptionMass_nonneg _
    dsimp only [weighted]
    have hinvNonneg : 0 ≤ 1 / quittingTerminalSemanticDebtSum minimum :=
      div_nonneg (by norm_num) stall.minimum_pos.le
    calc
      absorption time =
          (1 / quittingTerminalSemanticDebtSum minimum) *
            (quittingTerminalSemanticDebtSum minimum * absorption time) := by
              field_simp [stall.minimum_pos.ne']
      _ ≤ (1 / quittingTerminalSemanticDebtSum minimum) *
          (quittingMaximalCapSemanticPrefixDebt reward source time *
            absorption time) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hminimumDebt habsorptionNonneg)
          hinvNonneg
  have htsum := habsorption.tsum_le_tsum hpoint hmajor
  rw [hweighted.tsum_mul_left,
    stall.weightedAbsorption_hasSum.tsum_eq] at htsum
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htsum

/-- Infinite future absorption charge starting at a displayed ray depth. -/
def absorptionTailSum
    (_stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source)
    (start : ℕ) : ℝ :=
  ∑' offset, quittingMaximalCapSemanticPrefixAbsorption reward source
    (start + offset)

theorem absorptionTailSum_tendsto_zero
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source) :
    Tendsto stall.absorptionTailSum atTop (nhds 0) := by
  let absorption := quittingMaximalCapSemanticPrefixAbsorption reward source
  have hsum : Summable absorption := stall.summable_absorption terminal hterminal
  have hpartial : Tendsto (fun start ↦
      ∑ time ∈ Finset.range start, absorption time) atTop
      (nhds (∑' time, absorption time)) :=
    (hsum.hasSum_iff_tendsto_nat).1 hsum.hasSum
  have hconst : Tendsto
      (fun _ : ℕ ↦ ∑' time, absorption time) atTop
      (nhds (∑' time, absorption time)) := tendsto_const_nhds
  have hsub := hconst.sub hpartial
  have heq : stall.absorptionTailSum = fun start ↦
      (∑' time, absorption time) -
        ∑ time ∈ Finset.range start, absorption time := by
    funext start
    have hsplit := hsum.sum_add_tsum_nat_add start
    unfold absorptionTailSum
    have htailEq : (∑' offset, absorption (start + offset)) =
        ∑' offset, absorption (offset + start) := by
      apply tsum_congr
      intro offset
      rw [Nat.add_comm]
    rw [htailEq]
    linarith [hsplit]
  rw [heq]
  simpa using hsub

/-- Supremal future absorption charge from one depth, represented by the
nonnegative infinite tail sum. -/
def absorptionTailSup
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source)
    (start : ℕ) : ℝ := stall.absorptionTailSum start

theorem finiteAbsorptionTail_le_tailSup
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source)
    (start horizon : ℕ) :
    (∑ offset ∈ Finset.range horizon,
      quittingMaximalCapSemanticPrefixAbsorption reward source
        (start + offset)) ≤ stall.absorptionTailSup start := by
  unfold absorptionTailSup absorptionTailSum
  have hshift := (summable_nat_add_iff start).2
    (stall.summable_absorption terminal hterminal)
  have hbound := hshift.sum_le_tsum (Finset.range horizon)
    (fun offset _ ↦ quittingRootAbsorptionMass_nonneg _)
  simpa only [quittingMaximalCapSemanticPrefixAbsorption, Nat.add_comm] using
    hbound

theorem absorptionTailSup_tendsto_zero
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source) :
    Tendsto stall.absorptionTailSup atTop (nhds 0) := by
  exact stall.absorptionTailSum_tendsto_zero terminal hterminal

theorem absorption_tendsto_zero
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source) :
    Tendsto (quittingMaximalCapSemanticPrefixAbsorption reward source) atTop
      (nhds 0) :=
  (stall.summable_absorption terminal hterminal).tendsto_atTop_zero

theorem exists_retainedLaw_allContinue_or_supportEntry
    (stall : QuittingMaximalCapSemanticPrefixRayStall reward minimum source)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hterminal : quittingTerminalSemanticPair reward terminal = source)
    (stage : ℕ) (coalition : {S : Finset ι // S.Nonempty})
    (hatom : 0 < quittingStageCoalitionMass reward terminal stage coalition) :
    ∃ cluster : QuittingTerminalSemanticLawPoint ι,
      cluster ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebtSum minimum <
        quittingTerminalSemanticDebtSum cluster.1 ∧
      quittingTerminalSemanticDebtSum minimum /
            quittingTerminalSemanticDebtSum source *
          quittingStageCoalitionMass reward terminal stage coalition ≤
        cluster.2 (some coalition) ∧
      0 < cluster.2 (some coalition) ∧
      IsεQuittingRootNash reward cluster.1.2 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      ((∀ root : ι → PMF Bool,
          IsεQuittingRootNash reward cluster.1.2 0 root →
            root = (quittingAllContinueRoot : ι → PMF Bool)) ∨
        ∃ root : ι → PMF Bool,
          IsεQuittingRootNash reward cluster.1.2 0 root ∧
            0 < quittingRootAbsorptionMass root) := by
  let tolerance :=
    (quittingMaximalCapSemanticPrefixDebtLimit reward source -
      quittingTerminalSemanticDebtSum minimum) / 2
  have htolerance : 0 < tolerance := by
    dsimp only [tolerance]
    linarith [stall.strict]
  have hnoReturn : ∀ n,
      quittingTerminalSemanticDebtSum minimum + tolerance <
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal n)) := by
    intro n
    have hlimit := quittingMaximalCapSemanticPrefixDebtLimit_le_debt
      reward minimum source stall.minimum_global stall.source_mem n
    rw [quittingMaximalCapPrefixProfile_eq_semanticPrefixProfile,
      hterminal]
    have hsemantic :=
      quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
        reward source terminal hterminal n
    rw [hsemantic]
    change _ < quittingMaximalCapSemanticPrefixDebt reward source n
    exact (by dsimp only [tolerance]; linarith [stall.strict, hlimit])
  obtain ⟨cluster, hmem, hoff, hlaw, hlawPos, hnash, hsplit⟩ :=
    exists_offMinimum_retainedLaw_allContinue_or_supportEntry reward minimum
      terminal stage coalition tolerance stall.minimum_global
        stall.minimum_pos hatom hnoReturn
  refine ⟨cluster, hmem, ?_, ?_, hlawPos, hnash, hsplit⟩
  · linarith [hoff, htolerance]
  · simpa only [hterminal] using hlaw

end QuittingMaximalCapSemanticPrefixRayStall

end GameTheory
