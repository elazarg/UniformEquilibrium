/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.MaximalPrefixRayDichotomy
import UniformEquilibrium.Quitting.Paths.ReversePrefixStoppingLaw
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair

/-!
# Stopping-clock escape on the source-facing Fin4 maximal-prefix ray

This module applies the generic reverse-prefix stopping-law theorems to the
strict arm of a supplied Fin4 maximal-prefix packet.  It asserts no producer
for that packet, no consumer of the escaping clocks, and no uniform-equilibrium
conclusion.
-/

noncomputable section

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- The canonical maximal-cap root displayed at one autonomous orbit index. -/
def maximalPrefixRoots
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) : Fin 4 → PMF Bool :=
  quittingMaximalCapSemanticRoot reward
    (quittingMaximalCapSemanticPrefixOrbit reward packet.raySource index)

/-- The generic reverse-prefix word is the literal canonical maximal-prefix
word, including its outer-to-inner ordering. -/
theorem reversePrefixRootStack_eq_maximalPrefixRootStack
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (depth : ℕ) :
    quittingReversePrefixRootStack packet.maximalPrefixRoots depth =
      quittingMaximalCapSemanticPrefixRootStack reward packet.raySource depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [quittingReversePrefixRootStack_succ,
        quittingMaximalCapSemanticPrefixRootStack_succ]
      rw [ih]
      rfl

/-- The actual source-facing ray profile is the generic reverse-prefix profile
with the packet's varying pure-pair base as its tail. -/
theorem rayProfiles_eq_reversePrefixProfile
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (depth : ℕ) :
    packet.rayFamily.rayProfiles depth =
      quittingReversePrefixProfile reward packet.maximalPrefixRoots
        packet.rayBaseProfile depth := by
  change quittingMaximalCapSemanticPrefixProfile reward packet.raySource
      (packet.rayBaseProfile depth) depth = _
  unfold quittingMaximalCapSemanticPrefixProfile quittingReversePrefixProfile
  rw [packet.reversePrefixRootStack_eq_maximalPrefixRootStack]

/-- Every member of the sure pair has zero marginal Never mass in every
varying base profile, independently of the counterfactual post-pair tail. -/
theorem rayBaseProfile_pairMember_stoppingLaw_none_eq_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) {who : Fin 4}
    (hwho : who ∈ packet.rayTerminal.val) (depth : ℕ) :
    (quittingBehaviorStoppingLaw reward
        (packet.rayBaseProfile depth who) none).toReal = 0 := by
  rw [rayBaseProfile]
  change (quittingBehaviorStoppingLaw reward
      ((quittingLiteralRootStackProfile reward
        [quittingPureSetRoot packet.rayTerminal.val]
        (packet.rayTail depth)) who) none).toReal = 0
  rw [quittingBehaviorStoppingLaw_none_literalRootStackProfile_eq]
  simp [quittingLiteralRootStackOwnSurvival, quittingPureSetRoot,
    quittingSetAction, hwho]

/-- Root absorption along the autonomous maximal-prefix word vanishes in the
strict-stall arm. -/
theorem maximalPrefixRoots_absorption_tendsto_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (strict : MaximalPrefixRayStall packet) :
    Tendsto (fun index =>
      quittingRootAbsorptionMass (packet.maximalPrefixRoots index)) atTop
      (nhds 0) := by
  change Tendsto
    (quittingMaximalCapSemanticPrefixAbsorption reward packet.raySource)
    atTop (nhds 0)
  exact strict.stall.absorption_tendsto_zero (packet.rayBaseProfile 0)
    (packet.rayBaseProfile_semantic_eq 0)

/-- Every fixed finite marginal stopping-law head vanishes along the strict
maximal-prefix ray. -/
theorem maximalPrefixRay_finiteHead_tendsto_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (strict : MaximalPrefixRayStall packet)
    (who : Fin 4) (horizon : ℕ) :
    Tendsto (fun depth => stoppingLawFiniteHeadMass
      (quittingBehaviorStoppingLaw reward
        (packet.rayFamily.rayProfiles depth who)) horizon) atTop (nhds 0) := by
  rw [show (fun depth => stoppingLawFiniteHeadMass
      (quittingBehaviorStoppingLaw reward
        (packet.rayFamily.rayProfiles depth who)) horizon) =
      fun depth => stoppingLawFiniteHeadMass
        (quittingBehaviorStoppingLaw reward
          ((quittingReversePrefixProfile reward packet.maximalPrefixRoots
            packet.rayBaseProfile depth) who)) horizon by
    funext depth
    rw [packet.rayProfiles_eq_reversePrefixProfile]]
  exact quittingReversePrefix_finiteHead_tendsto_zero reward
    packet.maximalPrefixRoots packet.rayBaseProfile who
    (packet.maximalPrefixRoots_absorption_tendsto_zero strict) horizon

/-- The pair member's marginal Never coordinate is exactly zero along the
whole source-facing maximal-prefix ray. -/
theorem maximalPrefixRay_pairMember_stoppingLaw_none_eq_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) {who : Fin 4}
    (hwho : who ∈ packet.rayTerminal.val) (depth : ℕ) :
    (quittingBehaviorStoppingLaw reward
        (packet.rayFamily.rayProfiles depth who) none).toReal = 0 := by
  rw [packet.rayProfiles_eq_reversePrefixProfile]
  exact quittingReversePrefixStoppingLaw_none_eq_zero reward
    packet.maximalPrefixRoots packet.rayBaseProfile who
    (packet.rayBaseProfile_pairMember_stoppingLaw_none_eq_zero hwho) depth

/-- Every pair member's finite stopping clock escapes beyond each fixed
window with asymptotic mass one. -/
theorem maximalPrefixRay_pairMember_lateFiniteMass_tendsto_one
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (strict : MaximalPrefixRayStall packet)
    {who : Fin 4} (hwho : who ∈ packet.rayTerminal.val) (horizon : ℕ) :
    Tendsto (fun depth => stoppingLawLateFiniteMass
      (quittingBehaviorStoppingLaw reward
        (packet.rayFamily.rayProfiles depth who)) horizon) atTop (nhds 1) := by
  rw [show (fun depth => stoppingLawLateFiniteMass
      (quittingBehaviorStoppingLaw reward
        (packet.rayFamily.rayProfiles depth who)) horizon) =
      fun depth => stoppingLawLateFiniteMass
        (quittingBehaviorStoppingLaw reward
          ((quittingReversePrefixProfile reward packet.maximalPrefixRoots
            packet.rayBaseProfile depth) who)) horizon by
    funext depth
    rw [packet.rayProfiles_eq_reversePrefixProfile]]
  exact quittingReversePrefix_lateFiniteMass_tendsto_one reward
    packet.maximalPrefixRoots packet.rayBaseProfile who
    (packet.maximalPrefixRoots_absorption_tendsto_zero strict)
    (packet.rayBaseProfile_pairMember_stoppingLaw_none_eq_zero hwho) horizon

/-- Every pair member's marginal stopping law becomes maximally separated in
general total variation from any fixed actual stopping law. -/
theorem maximalPrefixRay_pairMember_pmfGeneralTV_tendsto_one
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (strict : MaximalPrefixRayStall packet)
    {who : Fin 4} (hwho : who ∈ packet.rayTerminal.val)
    (fixed : PMF (Option ℕ)) :
    Tendsto (fun depth => Math.Probability.pmfGeneralTV
      (quittingBehaviorStoppingLaw reward
        (packet.rayFamily.rayProfiles depth who)) fixed) atTop (nhds 1) := by
  rw [show (fun depth => Math.Probability.pmfGeneralTV
      (quittingBehaviorStoppingLaw reward
        (packet.rayFamily.rayProfiles depth who)) fixed) =
      fun depth => Math.Probability.pmfGeneralTV
        (quittingBehaviorStoppingLaw reward
          ((quittingReversePrefixProfile reward packet.maximalPrefixRoots
            packet.rayBaseProfile depth) who)) fixed by
    funext depth
    rw [packet.rayProfiles_eq_reversePrefixProfile]]
  exact quittingReversePrefix_pmfGeneralTV_tendsto_one reward
    packet.maximalPrefixRoots packet.rayBaseProfile who
    (packet.maximalPrefixRoots_absorption_tendsto_zero strict)
    (packet.rayBaseProfile_pairMember_stoppingLaw_none_eq_zero hwho) fixed

/-- The retained pair is still the terminal coalition at the shifted marked
date, with the exact maximal-prefix survival mass. -/
theorem maximalPrefixRay_pairStageMass_eq_survival
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (depth : ℕ) :
    quittingStageCoalitionMass reward (packet.rayFamily.rayProfiles depth)
        depth packet.rayTerminal =
      quittingMaximalCapSemanticPrefixSurvival reward packet.raySource depth :=
  packet.rayProfiles_stageMass_eq_survival depth

/-- The retained pair's shifted stage mass converges to the exact ray-limit
ratio. -/
theorem maximalPrefixRay_pairStageMass_tendsto_limitRatio
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Tendsto (fun depth => quittingStageCoalitionMass reward
      (packet.rayFamily.rayProfiles depth) depth packet.rayTerminal) atTop
      (nhds (packet.rayLimit /
        quittingTerminalSemanticDebtSum packet.raySource)) := by
  exact packet.rayMarkedMass_and_paidGainDensity_tendsto.1

/-- The positive global minimum-to-source ratio is a lower bound for the
retained pair's limiting shifted mass. -/
theorem minimumDebt_div_sourceDebt_le_pairStageMassLimit
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    quittingTerminalSemanticDebtSum source.point.1 /
          quittingTerminalSemanticDebtSum packet.raySource ≤
      packet.rayLimit /
        quittingTerminalSemanticDebtSum packet.raySource := by
  exact (div_le_div_iff_of_pos_right packet.raySourceDebt_pos).2
    packet.minimumDebt_le_rayLimit

/-- The strict arm's ray limit is strictly above the positive global
minimum. -/
theorem minimumDebt_lt_rayLimit
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (strict : MaximalPrefixRayStall packet) :
    quittingTerminalSemanticDebtSum source.point.1 < packet.rayLimit := by
  simpa only [rayLimit] using strict.stall.strict

/-- The ray limit is no larger than the source debt at depth zero. -/
theorem rayLimit_le_sourceDebt
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    packet.rayLimit ≤ quittingTerminalSemanticDebtSum packet.raySource := by
  have hlimit := quittingMaximalCapSemanticPrefixDebtLimit_le_debt reward
    source.point.1 packet.raySource source.minimum packet.raySource_mem 0
  simpa only [rayLimit, quittingMaximalCapSemanticPrefixDebt,
    quittingMaximalCapSemanticPrefixOrbit_zero] using hlimit

/-- The retained pair's limiting shifted mass is at most one. -/
theorem pairStageMassLimit_le_one
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    packet.rayLimit /
        quittingTerminalSemanticDebtSum packet.raySource ≤ 1 :=
  (div_le_one packet.raySourceDebt_pos).2 packet.rayLimit_le_sourceDebt

/-- The shifted pair mass has a strictly positive limiting value in the
strict-stall arm. -/
theorem pairStageMassLimit_pos
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (strict : MaximalPrefixRayStall packet) :
    0 < packet.rayLimit /
      quittingTerminalSemanticDebtSum packet.raySource := by
  exact div_pos (source.minimumDebt_pos.trans strict.stall.strict)
    packet.raySourceDebt_pos

/-- No cofinal subsequence of a pair member's displayed stopping laws can
converge in general total variation to an actual stopping law. -/
theorem maximalPrefixRay_pairMember_no_cofinal_pmfGeneralTV_convergent_subsequence
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (strict : MaximalPrefixRayStall packet)
    {who : Fin 4} (hwho : who ∈ packet.rayTerminal.val) :
    ¬ ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ∃ fixed : PMF (Option ℕ),
        Tendsto (fun index => Math.Probability.pmfGeneralTV
          (quittingBehaviorStoppingLaw reward
            (packet.rayFamily.rayProfiles (subsequence index) who)) fixed)
          atTop (nhds 0) := by
  rintro ⟨subsequence, hmono, fixed, hzero⟩
  have hone :=
    (packet.maximalPrefixRay_pairMember_pmfGeneralTV_tendsto_one
      strict hwho fixed).comp hmono.tendsto_atTop
  have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
  norm_num at this

/-- Complete strategic stopping-clock escape record for both members of the
fixed pair in a supplied strict maximal-prefix ray. -/
structure FinFourMaximalPrefixRayClockEscape
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (strict : MaximalPrefixRayStall packet) where
  finiteHead_tendsto_zero : ∀ who horizon,
    Tendsto (fun depth => stoppingLawFiniteHeadMass
      (quittingBehaviorStoppingLaw reward
        (packet.rayFamily.rayProfiles depth who)) horizon) atTop (nhds 0)
  pairMember_none_eq_zero : ∀ {who}, who ∈ packet.rayTerminal.val → ∀ depth,
    (quittingBehaviorStoppingLaw reward
      (packet.rayFamily.rayProfiles depth who) none).toReal = 0
  pairMember_lateFiniteMass_tendsto_one : ∀ {who},
    who ∈ packet.rayTerminal.val → ∀ horizon,
      Tendsto (fun depth => stoppingLawLateFiniteMass
        (quittingBehaviorStoppingLaw reward
          (packet.rayFamily.rayProfiles depth who)) horizon) atTop (nhds 1)
  pairMember_pmfGeneralTV_tendsto_one : ∀ {who},
    who ∈ packet.rayTerminal.val → ∀ fixed,
      Tendsto (fun depth => Math.Probability.pmfGeneralTV
        (quittingBehaviorStoppingLaw reward
          (packet.rayFamily.rayProfiles depth who)) fixed) atTop (nhds 1)
  pairMember_no_cofinal_pmfGeneralTV_convergent_subsequence : ∀ {who},
    who ∈ packet.rayTerminal.val →
      ¬ ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        ∃ fixed : PMF (Option ℕ),
          Tendsto (fun index => Math.Probability.pmfGeneralTV
            (quittingBehaviorStoppingLaw reward
              (packet.rayFamily.rayProfiles (subsequence index) who)) fixed)
            atTop (nhds 0)
  pairStageMass_tendsto_limitRatio :
    Tendsto (fun depth => quittingStageCoalitionMass reward
      (packet.rayFamily.rayProfiles depth) depth packet.rayTerminal) atTop
      (nhds (packet.rayLimit /
        quittingTerminalSemanticDebtSum packet.raySource))
  minimumRatio_le_pairStageMassLimit :
    quittingTerminalSemanticDebtSum source.point.1 /
          quittingTerminalSemanticDebtSum packet.raySource ≤
      packet.rayLimit /
        quittingTerminalSemanticDebtSum packet.raySource
  minimumDebt_lt_rayLimit :
    quittingTerminalSemanticDebtSum source.point.1 < packet.rayLimit
  pairStageMassLimit_pos :
    0 < packet.rayLimit /
      quittingTerminalSemanticDebtSum packet.raySource
  pairStageMassLimit_le_one :
    packet.rayLimit /
      quittingTerminalSemanticDebtSum packet.raySource ≤ 1

/-- Assemble the exact source-facing clock-escape boundary from a supplied
strict maximal-prefix ray. -/
theorem nonempty_finFourMaximalPrefixRayClockEscape
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (strict : MaximalPrefixRayStall packet) :
    Nonempty (FinFourMaximalPrefixRayClockEscape packet strict) := by
  exact ⟨{
    finiteHead_tendsto_zero :=
      packet.maximalPrefixRay_finiteHead_tendsto_zero strict
    pairMember_none_eq_zero :=
      packet.maximalPrefixRay_pairMember_stoppingLaw_none_eq_zero
    pairMember_lateFiniteMass_tendsto_one :=
      packet.maximalPrefixRay_pairMember_lateFiniteMass_tendsto_one strict
    pairMember_pmfGeneralTV_tendsto_one :=
      packet.maximalPrefixRay_pairMember_pmfGeneralTV_tendsto_one strict
    pairMember_no_cofinal_pmfGeneralTV_convergent_subsequence :=
      packet.maximalPrefixRay_pairMember_no_cofinal_pmfGeneralTV_convergent_subsequence
        strict
    pairStageMass_tendsto_limitRatio :=
      packet.maximalPrefixRay_pairStageMass_tendsto_limitRatio
    minimumRatio_le_pairStageMassLimit :=
      packet.minimumDebt_div_sourceDebt_le_pairStageMassLimit
    minimumDebt_lt_rayLimit := packet.minimumDebt_lt_rayLimit strict
    pairStageMassLimit_pos := packet.pairStageMassLimit_pos strict
    pairStageMassLimit_le_one := packet.pairStageMassLimit_le_one
  }⟩

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
