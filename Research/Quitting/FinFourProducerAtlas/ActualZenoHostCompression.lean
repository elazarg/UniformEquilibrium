/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.FullyScreenedFiniteClockClearing

/-!
# Positive-host compression for actual Fin4 Zeno descendants

Vanishing combined joint survival has an exhaustive literal classification:
either every player-deleted combined clock tends to zero, or one fixed host
has a positive deleted-survival floor on a strict subsequence and every other
deleted clock tends to zero there.  The positive-host arm clears only that
host from the arbitrary prefix word and applies the generic positive-stage
atom adapter at resolution `eta`.

The output retains the original normalized-return selection, raw Zeno rank,
fixed pair, source chronology, and complete postmark reference spine.  It is
not a minimum-fibre return, a renewable compression, or a terminal consumer.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {rho : ℝ}
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource rho}
  {data : FinFourNormalizedInertVanishingDensityBoundary packet}

/-- Operational positive-host alternative on one actual Zeno source.  The
same strict subsequence carries the host floor and the vanishing of every
other deleted clock. -/
structure FinFourActualZenoPositiveHost
    (zeno : FinFourActualZenoDeletedSurvivalSource data) where
  host : Fin 4
  eta : ℝ
  eta_pos : 0 < eta
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  host_floor : ∀ rank, eta ≤
    quittingLiteralRootStackOpponentSurvival
      (zeno.combinedWord (subsequence rank)) host

namespace FinFourActualZenoDeletedSurvivalSource

variable (zeno : FinFourActualZenoDeletedSurvivalSource data)

private theorem exists_pos_frequently_ge_of_not_tendsto_zero
    (f : ℕ → ℝ) (hnonneg : ∀ rank, 0 ≤ f rank)
    (hnot : ¬ Tendsto f atTop (nhds 0)) :
    ∃ eta, 0 < eta ∧ ∃ᶠ rank in atTop, eta ≤ f rank := by
  by_contra hnone
  push Not at hnone
  apply hnot
  rw [tendsto_order]
  constructor
  · intro lower hlower
    exact Eventually.of_forall fun rank ↦ hlower.trans_le (hnonneg rank)
  · intro upper hupper
    exact hnone upper hupper

/-- Exact source-level classification.  The former `not fully screened` arm
is strengthened to a fixed positive host and simultaneous screening of all
other players on the same strict subsequence. -/
theorem nonempty_positiveHost_or_fullyScreened :
    Nonempty (FinFourActualZenoPositiveHost zeno) ∨
      IsFinFourActualZenoFullyScreened zeno := by
  classical
  by_cases hscreened : IsFinFourActualZenoFullyScreened zeno
  · exact Or.inr hscreened
  · have hnotAll : ¬ ∀ who, Tendsto (fun rank ↦
        quittingLiteralRootStackOpponentSurvival
          (zeno.combinedWord rank) who) atTop (nhds 0) := hscreened
    push Not at hnotAll
    obtain ⟨host, hhostNot⟩ := hnotAll
    obtain ⟨eta, heta, hfrequent⟩ :=
      exists_pos_frequently_ge_of_not_tendsto_zero
        (fun rank ↦ quittingLiteralRootStackOpponentSurvival
          (zeno.combinedWord rank) host)
        (fun rank ↦
          quittingLiteralRootStackOpponentSurvival_nonneg
            (zeno.combinedWord rank) host) hhostNot
    obtain ⟨subsequence, hsubsequence, hfloor⟩ :=
      extraction_of_frequently_atTop hfrequent
    exact Or.inl ⟨{
      host := host
      eta := eta
      eta_pos := heta
      subsequence := subsequence
      subsequence_strictMono := hsubsequence
      host_floor := hfloor }⟩

end FinFourActualZenoDeletedSurvivalSource

namespace FinFourActualZenoPositiveHost

variable {zeno : FinFourActualZenoDeletedSurvivalSource data}
  (positive : FinFourActualZenoPositiveHost zeno)

/-- The literal Zeno row retained by the positive-host extraction. -/
def zenoRank (rank : ℕ) : ℕ := positive.subsequence rank

theorem zenoRank_strictMono : StrictMono positive.zenoRank :=
  positive.subsequence_strictMono

/-- Every other deleted clock vanishes automatically on the same host
subsequence.  It is a consequence, not an extra field of the positive-host
predicate. -/
theorem other_tendsto_zero (other : Fin 4) (hother : other ≠ positive.host) :
    Tendsto (fun rank ↦ quittingLiteralRootStackOpponentSurvival
      (zeno.combinedWord (positive.zenoRank rank)) other) atTop (nhds 0) := by
  have hjoint : Tendsto (fun rank ↦
      quittingLiteralRootStackJointSurvival
        (zeno.combinedWord (positive.zenoRank rank))) atTop (nhds 0) :=
    zeno.combinedJointSurvival_tendsto_zero.comp
      positive.zenoRank_strictMono.tendsto_atTop
  apply squeeze_zero'
  · exact Eventually.of_forall fun rank ↦
      quittingLiteralRootStackOpponentSurvival_nonneg
        (zeno.combinedWord (positive.zenoRank rank)) other
  · filter_upwards [] with rank
    apply (le_div_iff₀ positive.eta_pos).2
    calc
      quittingLiteralRootStackOpponentSurvival
            (zeno.combinedWord (positive.zenoRank rank)) other * positive.eta ≤
          quittingLiteralRootStackOpponentSurvival
              (zeno.combinedWord (positive.zenoRank rank)) positive.host *
            quittingLiteralRootStackOpponentSurvival
              (zeno.combinedWord (positive.zenoRank rank)) other := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (positive.host_floor rank)
          (quittingLiteralRootStackOpponentSurvival_nonneg _ other)
      _ ≤ quittingLiteralRootStackJointSurvival
            (zeno.combinedWord (positive.zenoRank rank)) :=
        mul_opponentSurvival_le_jointSurvival_of_ne _ hother.symm
  · simpa using hjoint.div_const positive.eta

/-- The operational positive-host arm is genuinely disjoint from full
screening. -/
theorem not_fullyScreened
    (positive : FinFourActualZenoPositiveHost zeno) :
    ¬ IsFinFourActualZenoFullyScreened zeno := by
  intro hscreened
  have hhostZero := (hscreened positive.host).comp
    positive.subsequence_strictMono.tendsto_atTop
  have hsmall := (tendsto_order.1 hhostZero).2 positive.eta positive.eta_pos
  obtain ⟨rank, hrank⟩ := hsmall.exists
  exact (not_lt_of_ge (positive.host_floor rank)) hrank

/-- The original normalized-return packet index behind a retained host row. -/
def packetIndex (rank : ℕ) : ℕ := zeno.packetIndex (positive.zenoRank rank)

/-- The original minimum-source chronology rank behind a retained host row. -/
def sourceRank (rank : ℕ) : ℕ := zeno.sourceRank (positive.zenoRank rank)

/-- Force the positive host to Continue throughout the complete actual
premark word, including both the arbitrary prefix and base chronology. -/
def forcedPremarkWord (rank : ℕ) : List (Fin 4 → PMF Bool) :=
  quittingLiteralRootStackForceContinue
    (zeno.combinedWord (positive.zenoRank rank)) positive.host

/-- The selected complete behavioral tail after the marked row. -/
def referenceTail (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  packet.base.referenceProfile (packet.subsequence (positive.packetIndex rank))

/-- The fixed pure marked pair followed literally by the selected reference
tail. -/
def markedContinuation (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (fun who ↦ PMF.pure (quittingCoalitionAction zeno.family.terminal.val who))
    (positive.referenceTail rank)

/-- The actual source-attached host-cleared row before choosing the host's
marked Boolean endpoint. -/
def endpointSourceProfile (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (positive.forcedPremarkWord rank)
    (positive.markedContinuation rank)

/-- The marked date in the reconstructed full-word descendant. -/
def endpointStage (rank : ℕ) : ℕ := (positive.forcedPremarkWord rank).length

theorem endpointStage_eq_mark (rank : ℕ) :
    positive.endpointStage rank = zeno.mark (positive.zenoRank rank) := by
  rw [endpointStage, forcedPremarkWord]
  simp only [quittingLiteralRootStackForceContinue, List.length_map]
  rw [FinFourActualZenoDeletedSurvivalSource.combinedWord,
    quittingCombinedPremarkWord_length, zeno.mark_eq]

/-- The host-cleared source reaches the pure marked pair with exactly the
combined host-deleted survival. -/
theorem endpointSourceStageMass_eq (rank : ℕ) :
    quittingStageCoalitionMass reward (positive.endpointSourceProfile rank)
        (positive.endpointStage rank) zeno.family.terminal =
      quittingLiteralRootStackOpponentSurvival
        (zeno.combinedWord (positive.zenoRank rank)) positive.host := by
  rw [endpointSourceProfile, endpointStage]
  have htransport := quittingStageCoalitionMass_literalRootStack_add_length
    reward (positive.forcedPremarkWord rank) (positive.markedContinuation rank)
      0 zeno.family.terminal
  simp only [Nat.add_zero] at htransport
  rw [htransport]
  change quittingLiteralRootStackJointSurvival
        (positive.forcedPremarkWord rank) *
      quittingStageCoalitionMass reward (positive.markedContinuation rank) 0
        zeno.family.terminal = _
  rw [forcedPremarkWord,
    quittingLiteralRootStackJointSurvival_forceContinue]
  have hmarked : quittingStageCoalitionMass reward
      (positive.markedContinuation rank) 0 zeno.family.terminal = 1 := by
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      quittingLiveMass_zero]
    change 1 * quittingRootCoalitionMass
      (fun who ↦ PMF.pure
        (quittingCoalitionAction zeno.family.terminal.val who))
      zeno.family.terminal.val = 1
    rw [quittingRootCoalitionMass_pureCoalitionAction_eq_one]
    norm_num
  rw [hmarked, mul_one]

/-- Literal positive-stage adapter for the positive host.  The requested
resolution is `eta` itself, with no loss from the base chronology. -/
theorem endpointAdapter (rank : ℕ) :
    QuittingStageAtomConcentratedPacketAdapter reward
      (positive.endpointSourceProfile rank) zeno.family.terminal positive.host
      (positive.endpointStage rank) positive.eta where
  sourceTerminal_ne_owner := by
    intro hsingleton
    have hcard := zeno.terminal_card
    rw [hsingleton, Finset.card_singleton] at hcard
    omega
  resolution_pos := positive.eta_pos
  resolution_le_sourceStageMass := by
    rw [positive.endpointSourceStageMass_eq rank]
    exact positive.host_floor rank

/-- The postmark tail of the host-cleared source is exactly the retained
reference profile. -/
theorem endpointSource_postMarkSpine_eq_reference (rank : ℕ) :
    quittingAllContinueProfileSpine reward (positive.endpointSourceProfile rank)
        (positive.endpointStage rank + 1) = positive.referenceTail rank := by
  rw [endpointSourceProfile, endpointStage,
    show (positive.forcedPremarkWord rank).length + 1 =
      (positive.forcedPremarkWord rank).length + 1 by rfl,
    QuittingMarkedPairDecoratedFamily.quittingAllContinueProfileSpine_add,
    quittingAllContinueProfileSpine_literalRootStackProfile_length]
  change quittingProfileAllContinueContinuation reward
      (positive.markedContinuation rank) = positive.referenceTail rank
  exact shiftProfile_quittingRootThenContinuationProfile reward _ _
    quittingAllContinueAction

/-- A further finite-label refinement fixes both the best Boolean endpoint
and its routed nonempty coalition. -/
structure FixedEndpoint where
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  action : Bool
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  action_eq : ∀ rank,
    (positive.endpointAdapter (refinement rank)).action = action
  terminal_eq : ∀ rank,
    (positive.endpointAdapter (refinement rank)).routedTerminal = terminal

/-- Finite pigeonhole produces a fixed endpoint/terminal without changing
the previously selected host or source. -/
theorem nonempty_fixedEndpoint : Nonempty positive.FixedEndpoint := by
  let label : ℕ → Bool × {S : Finset (Fin 4) // S.Nonempty} := fun rank ↦
    ((positive.endpointAdapter rank).action,
      (positive.endpointAdapter rank).routedTerminal)
  obtain ⟨fixed, hfixedInfinite⟩ := Finite.exists_infinite_fiber label
  have hfrequent : ∃ᶠ rank in atTop, label rank = fixed := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact Set.infinite_coe_iff.mp hfixedInfinite
  obtain ⟨refinement, hrefinement, hfixed⟩ :=
    extraction_of_frequently_atTop hfrequent
  exact ⟨{
    refinement := refinement
    refinement_strictMono := hrefinement
    action := fixed.1
    terminal := fixed.2
    action_eq := fun rank ↦ congrArg Prod.fst (hfixed rank)
    terminal_eq := fun rank ↦ congrArg Prod.snd (hfixed rank) }⟩

namespace FixedEndpoint

variable {positive : FinFourActualZenoPositiveHost zeno}
  (fixed : positive.FixedEndpoint)

/-- The original Zeno rank behind one fixed-label endpoint row. -/
def zenoRank (rank : ℕ) : ℕ := positive.zenoRank (fixed.refinement rank)

theorem zenoRank_strictMono : StrictMono fixed.zenoRank :=
  positive.zenoRank_strictMono.comp fixed.refinement_strictMono

def packetIndex (rank : ℕ) : ℕ := positive.packetIndex (fixed.refinement rank)

def sourceRank (rank : ℕ) : ℕ := positive.sourceRank (fixed.refinement rank)

theorem hostDeletedSurvival_floor (rank : ℕ) :
    positive.eta ≤ quittingLiteralRootStackOpponentSurvival
      (zeno.combinedWord (fixed.zenoRank rank)) positive.host :=
  positive.host_floor (fixed.refinement rank)

theorem otherDeletedSurvival_tendsto_zero (other : Fin 4)
    (hother : other ≠ positive.host) : Tendsto (fun rank ↦
      quittingLiteralRootStackOpponentSurvival
        (zeno.combinedWord (fixed.zenoRank rank)) other) atTop (nhds 0) := by
  exact (positive.other_tendsto_zero other hother).comp
    fixed.refinement_strictMono.tendsto_atTop

theorem adapter (rank : ℕ) :
    QuittingStageAtomConcentratedPacketAdapter reward
      (positive.endpointSourceProfile (fixed.refinement rank))
      zeno.family.terminal positive.host
      (positive.endpointStage (fixed.refinement rank)) positive.eta :=
  positive.endpointAdapter (fixed.refinement rank)

def profile (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  (fixed.adapter rank).targetProfile

def stage (rank : ℕ) : ℕ := positive.endpointStage (fixed.refinement rank)

theorem stage_eq_mark (rank : ℕ) :
    fixed.stage rank = zeno.mark (fixed.zenoRank rank) :=
  positive.endpointStage_eq_mark (fixed.refinement rank)

theorem fixed_action_eq (rank : ℕ) :
    (fixed.adapter rank).action = fixed.action :=
  fixed.action_eq rank

theorem fixed_terminal_eq (rank : ℕ) :
    (fixed.adapter rank).routedTerminal = fixed.terminal := fixed.terminal_eq rank

/-- The routed fixed terminal retains the full host floor `eta`. -/
theorem eta_le_markedMass (rank : ℕ) :
    positive.eta ≤ quittingStageCoalitionMass reward (fixed.profile rank)
      (fixed.stage rank) fixed.terminal := by
  rw [← fixed.terminal_eq rank]
  exact (fixed.adapter rank).resolution_le_targetStageMass

/-- The selected host has exact zero marked coordinate defect. -/
theorem markedHostDefect_eq_zero (rank : ℕ) :
    quittingRootCoordinateNashDefect reward (fixed.adapter rank).targetTail.1
      (quittingProfileLiveRoot reward (fixed.profile rank) (fixed.stage rank))
      positive.host = 0 :=
  (fixed.adapter rank).ownerMarkedDefect_eq_zero

/-- Every nonhost player's full behavior is unchanged by the marked endpoint
selection. -/
theorem profile_opponent_eq (rank : ℕ) (other : Fin 4)
    (hother : other ≠ positive.host) :
    fixed.profile rank other =
      positive.endpointSourceProfile (fixed.refinement rank) other :=
  (fixed.adapter rank).targetProfile_opponent_eq other hother

/-- The endpoint keeps the complete selected postmark behavioral profile,
not only its semantic projection. -/
theorem postMarkSpine_eq_reference (rank : ℕ) :
    quittingAllContinueProfileSpine reward (fixed.profile rank)
        (fixed.stage rank + 1) =
      packet.base.referenceProfile
        (packet.subsequence (positive.packetIndex (fixed.refinement rank))) := by
  rw [profile, stage]
  calc
    quittingAllContinueProfileSpine reward
          (fixed.adapter rank).targetProfile
          (positive.endpointStage (fixed.refinement rank) + 1) =
        quittingAllContinueProfileSpine reward
          (positive.endpointSourceProfile (fixed.refinement rank))
          (positive.endpointStage (fixed.refinement rank) + 1) :=
      quittingAllContinueProfileSpine_literalOneDateProfile_succ_eq _ _ _ _
    _ = positive.referenceTail (fixed.refinement rank) :=
      positive.endpointSource_postMarkSpine_eq_reference (fixed.refinement rank)
    _ = _ := rfl

/-- The fixed terminal is exactly the erase or insert route prescribed by
the fixed Boolean endpoint. -/
theorem terminal_erase_or_insert :
    (fixed.action = false ∧
        fixed.terminal.val = zeno.family.terminal.val.erase positive.host) ∨
      (fixed.action = true ∧
        fixed.terminal.val = insert positive.host zeno.family.terminal.val) := by
  rcases (fixed.adapter 0).routedTerminal_erase_or_insert with hroute | hroute
  · exact Or.inl ⟨(fixed.action_eq 0).symm.trans hroute.1,
      by rw [← fixed.terminal_eq 0]; exact hroute.2⟩
  · exact Or.inr ⟨(fixed.action_eq 0).symm.trans hroute.1,
      by rw [← fixed.terminal_eq 0]; exact hroute.2⟩

end FixedEndpoint

end FinFourActualZenoPositiveHost

namespace FinFourActualZenoDeletedSurvivalSource

variable (zeno : FinFourActualZenoDeletedSurvivalSource data)

/-- Logical normal form of the exact operational classification. -/
theorem nonempty_positiveHost_iff_not_fullyScreened :
    Nonempty (FinFourActualZenoPositiveHost zeno) ↔
      ¬ IsFinFourActualZenoFullyScreened zeno := by
  constructor
  · rintro ⟨positive⟩
    exact FinFourActualZenoPositiveHost.not_fullyScreened positive
  · intro hnot
    rcases zeno.nonempty_positiveHost_or_fullyScreened with hpositive | hscreened
    · exact hpositive
    · exact (hnot hscreened).elim

/-- Producer-facing classification: the positive arm already includes a
fixed action/terminal endpoint refinement. -/
theorem nonempty_fixedEndpoint_or_fullyScreened :
    (∃ positive : FinFourActualZenoPositiveHost zeno,
      Nonempty positive.FixedEndpoint) ∨
      IsFinFourActualZenoFullyScreened zeno := by
  rcases zeno.nonempty_positiveHost_or_fullyScreened with hpositive | hscreened
  · obtain ⟨positive⟩ := hpositive
    exact Or.inl ⟨positive, positive.nonempty_fixedEndpoint⟩
  · exact Or.inr hscreened

end FinFourActualZenoDeletedSurvivalSource

namespace FinFourNormalizedInertVanishingDensityBoundary

/-- Actual zero-mass normalized-return data yields the exhaustive operational
positive-host/full-screening split, without supplying either arm. -/
theorem nonempty_actualZeno_positiveHost_or_fullyScreened
    (data : FinFourNormalizedInertVanishingDensityBoundary packet)
    (hzero : data.boundary.limit.markedMass = 0) :
    ∃ zeno : FinFourActualZenoDeletedSurvivalSource data,
      Nonempty (FinFourActualZenoPositiveHost zeno) ∨
        IsFinFourActualZenoFullyScreened zeno := by
  obtain ⟨zeno⟩ := data.nonempty_actualZenoDeletedSurvivalSource hzero
  exact ⟨zeno, zeno.nonempty_positiveHost_or_fullyScreened⟩

/-- Actual zero-mass boundary data reaches the fixed endpoint producer in
the positive-host arm, while retaining the fully screened arm verbatim. -/
theorem nonempty_actualZeno_fixedEndpoint_or_fullyScreened
    (data : FinFourNormalizedInertVanishingDensityBoundary packet)
    (hzero : data.boundary.limit.markedMass = 0) :
    ∃ zeno : FinFourActualZenoDeletedSurvivalSource data,
      ((∃ positive : FinFourActualZenoPositiveHost zeno,
        Nonempty positive.FixedEndpoint) ∨
        IsFinFourActualZenoFullyScreened zeno) := by
  obtain ⟨zeno⟩ := data.nonempty_actualZenoDeletedSurvivalSource hzero
  exact ⟨zeno, zeno.nonempty_fixedEndpoint_or_fullyScreened⟩

/-- Literal source-attached capstone for the zero-mass boundary.  A positive
host supplies the fixed endpoint sequence above.  Otherwise the same actual
Zeno source supplies the existing finite-clearing family, whose rows expose
`concentratedPacket`, `resolution_eq`, and the branch-local `consumerResult`.

The positive-host endpoint is not assigned that consumer result, and this
theorem does not assert sibling coalescence, renewal, or a terminal uniform
equilibrium. -/
theorem nonempty_actualZeno_fixedEndpoint_or_clearingFamily
    (data : FinFourNormalizedInertVanishingDensityBoundary packet)
    (hzero : data.boundary.limit.markedMass = 0)
    (R : ℝ) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    ∃ zeno : FinFourActualZenoDeletedSurvivalSource data,
      ((∃ positive : FinFourActualZenoPositiveHost zeno,
        Nonempty positive.FixedEndpoint) ∨
        Nonempty (zeno.FullyScreenedClearingFamily R)) := by
  obtain ⟨zeno⟩ := data.nonempty_actualZenoDeletedSurvivalSource hzero
  refine ⟨zeno, ?_⟩
  rcases zeno.nonempty_fixedEndpoint_or_fullyScreened with
      hpositive | hscreened
  · exact Or.inl hpositive
  · exact Or.inr
      (zeno.nonempty_fullyScreenedClearingFamily hscreened R hR hreward)

end FinFourNormalizedInertVanishingDensityBoundary

end GameTheory
