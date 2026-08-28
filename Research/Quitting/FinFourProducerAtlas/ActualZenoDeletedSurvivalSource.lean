/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.CombinedDeletedSurvivalWord
import Research.Quitting.FinFourProducerAtlas.NormalizedInertVanishingDensityBoundary

/-!
# Actual Fin4 Zeno deleted-survival source

A zero-mass normalized boundary point lies in the closure of one fixed actual
forced-pair prefix orbit.  Sequential closure therefore supplies literal raw
descendants from that same selection.  This module retains their packet
indices, source chronology ranks, arbitrary words, comparison siblings,
complete whole/tail semantic laws, and postmark reference profiles.

The source is independent of finite-clock clearing.  Full screening is a
separate branch certificate on its combined words; when supplied, the base
pair floor transfers it to the arbitrary new words.  No infinite saturated
renewal chain or cofinality of the selected origin ranks is asserted.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {minimumSource : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource minimumSource}
  {rho : ℝ}
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource rho}

/-- One literal raw sequence converging to the zero-marked-mass boundary of
one fixed actual normalized-return selection. -/
structure FinFourActualZenoDeletedSurvivalSource
    (data : FinFourNormalizedInertVanishingDensityBoundary packet) where
  originRank : ℕ → ℕ
  newWord : ℕ → List (Fin 4 → PMF Bool)
  decorations_tendsto : Tendsto (fun rank =>
    data.selection.family.rawDecoration (originRank rank) (newWord rank))
    atTop (nhds data.boundary.limit)
  limit_markedMass_eq_zero : data.boundary.limit.markedMass = 0

namespace FinFourActualZenoDeletedSurvivalSource

variable {data : FinFourNormalizedInertVanishingDensityBoundary packet}
  (zeno : FinFourActualZenoDeletedSurvivalSource data)

/-- The fixed actual forced-pair family; it is selected once outside every
Zeno rank. -/
def family
    (_zeno : FinFourActualZenoDeletedSurvivalSource data) :
    QuittingMarkedPairDecoratedFamily reward :=
  data.selection.family

/-- The normalized-return packet index behind one literal row. -/
def packetIndex (rank : ℕ) : ℕ :=
  data.selection.packetIndex (zeno.originRank rank)

/-- The original minimum-source chronology rank behind one literal row. -/
def sourceRank (rank : ℕ) : ℕ :=
  data.selection.sourceRank (zeno.originRank rank)

/-- The immutable forced-pair target before adjoining the arbitrary word. -/
def baseProfile (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  zeno.family.profile (zeno.originRank rank)

/-- The immutable historical comparison sibling at the same source rank. -/
def baseSourceProfile (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  zeno.family.sourceProfile (zeno.originRank rank)

/-- The actual base marked date. -/
def baseMark (rank : ℕ) : ℕ :=
  zeno.family.mark (zeno.originRank rank)

/-- The actual target raw descendant. -/
def profile (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  zeno.family.descendantProfile (zeno.originRank rank) (zeno.newWord rank)

/-- The comparison descendant with the identical arbitrary word. -/
def sourceProfile (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  zeno.family.descendantSourceProfile
    (zeno.originRank rank) (zeno.newWord rank)

/-- The shifted actual marked date. -/
def mark (rank : ℕ) : ℕ :=
  zeno.family.descendantMark (zeno.originRank rank) (zeno.newWord rank)

/-- Every actual root before the marked pair, including both the arbitrary
new word and the originating base chronology. -/
def combinedWord (rank : ℕ) : List (Fin 4 → PMF Bool) :=
  quittingCombinedPremarkWord reward (zeno.newWord rank)
    (zeno.baseProfile rank) (zeno.baseMark rank)

/-- Roots already present in the selected base profile before its mark. -/
def baseWord (rank : ℕ) : List (Fin 4 → PMF Bool) :=
  quittingBehaviorProfilePremarkRoots reward
    (zeno.baseProfile rank) (zeno.baseMark rank)

theorem profile_eq_literalRootStack (rank : ℕ) :
    zeno.profile rank = quittingLiteralRootStackProfile reward
      (zeno.newWord rank) (zeno.baseProfile rank) := rfl

theorem sourceProfile_eq_literalRootStack (rank : ℕ) :
    zeno.sourceProfile rank = quittingLiteralRootStackProfile reward
      (zeno.newWord rank) (zeno.baseSourceProfile rank) := rfl

theorem mark_eq (rank : ℕ) :
    zeno.mark rank = (zeno.newWord rank).length + zeno.baseMark rank := rfl

/-- The fixed selected pair is literal at every rank. -/
theorem terminal_val :
    zeno.family.terminal.val =
      {returnSource.producer.owner, returnSource.forcedOwner} :=
  data.selection.terminal_val

theorem terminal_card : zeno.family.terminal.val.card = 2 :=
  data.selection.terminal_card

/-- The fixed selected marked owner is retained at every depth. -/
theorem markedOwner_eq :
    zeno.family.markedOwner = returnSource.forcedOwner :=
  data.selection.markedOwner_eq

/-- The complete postmark behavioral tail is the same selected reference
profile at the literal packet index. -/
theorem postMarkSpine_eq_reference (rank : ℕ) :
    quittingAllContinueProfileSpine reward (zeno.profile rank)
        (zeno.mark rank + 1) =
      packet.base.referenceProfile (packet.subsequence (zeno.packetIndex rank)) :=
  calc
    quittingAllContinueProfileSpine reward (zeno.profile rank)
          (zeno.mark rank + 1) =
        quittingAllContinueProfileSpine reward (zeno.baseProfile rank)
          (zeno.baseMark rank + 1) := by
      exact zeno.family.descendant_postMarkSpine_eq
        (zeno.originRank rank) (zeno.newWord rank)
    _ = packet.base.referenceProfile
          (packet.subsequence (zeno.packetIndex rank)) :=
      data.selection.postDateSpine_eq_reference (zeno.originRank rank)

/-- The forced pair's base marked mass equals its base live mass. -/
theorem baseMarkedMass_eq_liveMass (rank : ℕ) :
    quittingStageCoalitionMass reward (zeno.baseProfile rank)
        (zeno.baseMark rank) zeno.family.terminal =
      quittingLiveMass reward (zeno.baseProfile rank) (zeno.baseMark rank) := by
  unfold baseProfile baseMark family
  rw [FinFourNormalizedReturnSelection.profile_eq,
    FinFourNormalizedReturnSelection.mark_eq,
    FinFourNormalizedReturnSelection.terminal_eq]
  let index := data.selection.packetIndex (zeno.originRank rank)
  have hterminal : packet.movingTerminal =
      (packet.base.forcedAdapter
        (packet.subsequence index)).routedTerminal :=
    (packet.forcedTerminal_eq_movingTerminal index).symm
  rw [hterminal, packet.forcedPair_stageMass_eq_liveMass index,
    (packet.base.forcedAdapter
      (packet.subsequence index)).target_liveMass_eq_source]
  exact (quittingLiveMass_literalPureRootProfile_eq reward
    (packet.base.crossTailProfile (packet.subsequence index))
    (packet.base.endpoint (packet.subsequence index)).stage
    (quittingCoalitionAction minimumSource.atom.terminal.val)).symm

/-- The incoming resolution `rho` is a strict lower bound for the immutable
base live mass. -/
theorem rho_lt_baseLiveMass (rank : ℕ) :
    rho < quittingLiveMass reward (zeno.baseProfile rank) (zeno.baseMark rank) := by
  rw [← zeno.baseMarkedMass_eq_liveMass rank]
  exact data.selection.lambda_lt_markedMass (zeno.originRank rank)

/-- Every player-deleted base clock is bounded below by the same incoming
resolution. -/
theorem rho_lt_baseOpponentSurvival (rank : ℕ) (who : Fin 4) :
    rho < quittingLiteralRootStackOpponentSurvival (zeno.baseWord rank) who := by
  have hjoint : quittingLiteralRootStackJointSurvival (zeno.baseWord rank) =
      quittingLiveMass reward (zeno.baseProfile rank) (zeno.baseMark rank) :=
    quittingLiteralRootStackJointSurvival_premarkRoots_eq_liveMass
      reward (zeno.baseProfile rank) (zeno.baseMark rank)
  apply (zeno.rho_lt_baseLiveMass rank).trans_le
  rw [← hjoint]
  rw [quittingLiteralRootStackJointSurvival_eq_opponent_mul_own]
  exact mul_le_of_le_one_right
    (quittingLiteralRootStackOpponentSurvival_nonneg (zeno.baseWord rank) who)
    (quittingLiteralRootStackOwnSurvival_le_one (zeno.baseWord rank) who)

/-- The preceding theorem in the list-survival vocabulary. -/
theorem rho_le_baseOpponentSurvival (rank : ℕ) (who : Fin 4) :
    rho ≤ quittingLiteralRootStackOpponentSurvival (zeno.baseWord rank) who :=
  (zeno.rho_lt_baseOpponentSurvival rank who).le

/-- The full raw decorations, including whole and tail semantic/law data,
converge to the one stored boundary point. -/
theorem whole_tendsto : Tendsto (fun rank =>
    (zeno.family.rawDecoration (zeno.originRank rank)
      (zeno.newWord rank)).whole) atTop
      (nhds data.boundary.limit.whole) :=
  (continuous_fst.comp continuous_fst).tendsto data.boundary.limit |>.comp
    zeno.decorations_tendsto

theorem tail_tendsto : Tendsto (fun rank =>
    (zeno.family.rawDecoration (zeno.originRank rank)
      (zeno.newWord rank)).tail) atTop
      (nhds data.boundary.limit.tail) :=
  (continuous_snd.comp continuous_fst).tendsto data.boundary.limit |>.comp
    zeno.decorations_tendsto

/-- The literal marked mass tends to zero along the actual raw rows. -/
theorem markedMass_tendsto_zero : Tendsto (fun rank =>
    (zeno.family.rawDecoration (zeno.originRank rank)
      (zeno.newWord rank)).markedMass) atTop (nhds 0) := by
  have hprojection : Tendsto (fun rank =>
      (zeno.family.rawDecoration (zeno.originRank rank)
        (zeno.newWord rank)).markedMass) atTop
        (nhds data.boundary.limit.markedMass) := by
    exact ((continuous_fst.comp continuous_snd).tendsto
      data.boundary.limit).comp zeno.decorations_tendsto
  rw [zeno.limit_markedMass_eq_zero] at hprojection
  exact hprojection

/-- Combined joint survival is exactly the literal marked mass of the raw
descendant. -/
theorem combinedJointSurvival_eq_markedMass (rank : ℕ) :
    quittingLiteralRootStackJointSurvival (zeno.combinedWord rank) =
      (zeno.family.rawDecoration (zeno.originRank rank)
        (zeno.newWord rank)).markedMass := by
  rw [combinedWord, quittingCombinedPremarkWord_jointSurvival_eq,
    ← zeno.baseMarkedMass_eq_liveMass rank,
    zeno.family.rawDecoration_markedMass_eq_prefixSurvival_mul]
  rfl

theorem combinedJointSurvival_tendsto_zero : Tendsto (fun rank =>
    quittingLiteralRootStackJointSurvival (zeno.combinedWord rank))
      atTop (nhds 0) := by
  apply zeno.markedMass_tendsto_zero.congr'
  filter_upwards [] with rank
  exact (zeno.combinedJointSurvival_eq_markedMass rank).symm

end FinFourActualZenoDeletedSurvivalSource

namespace FinFourNormalizedInertVanishingDensityBoundary

/-- The zero-mass boundary arm internally yields literal actual raw rows from
the same fixed normalized-return selection. -/
theorem nonempty_actualZenoDeletedSurvivalSource
    (data : FinFourNormalizedInertVanishingDensityBoundary packet)
    (hzero : data.boundary.limit.markedMass = 0) :
    Nonempty (FinFourActualZenoDeletedSurvivalSource data) := by
  have hcarrier := data.boundary.limit_mem_carrier
  rw [QuittingMarkedPairDecoratedFamily.prefixOrbitCarrier,
    mem_closure_iff_seq_limit] at hcarrier
  obtain ⟨rows, hrows, hrowsTendsto⟩ := hcarrier
  choose originRank newWord horigin using hrows
  refine ⟨{
    originRank := originRank
    newWord := newWord
    decorations_tendsto := ?_
    limit_markedMass_eq_zero := hzero
  }⟩
  apply hrowsTendsto.congr'
  filter_upwards [] with rank
  exact (horigin rank).symm

end FinFourNormalizedInertVanishingDensityBoundary

/-! ## The fully screened branch passed to finite clearing -/

/-- A source-independent branch certificate: every combined player-deleted
clock vanishes. -/
def IsFinFourActualZenoFullyScreened
    {data : FinFourNormalizedInertVanishingDensityBoundary packet}
    (zeno : FinFourActualZenoDeletedSurvivalSource data) : Prop :=
  ∀ who, Tendsto (fun rank =>
    quittingLiteralRootStackOpponentSurvival (zeno.combinedWord rank) who)
      atTop (nhds 0)

namespace FinFourActualZenoDeletedSurvivalSource

variable {data : FinFourNormalizedInertVanishingDensityBoundary packet}
  (zeno : FinFourActualZenoDeletedSurvivalSource data)

/-- Combined full screening and the positive base pair floor imply full
screening of the arbitrary new words used by finite clock clearing. -/
theorem newWord_fullyScreened
    (hscreened : IsFinFourActualZenoFullyScreened zeno) :
    ∀ who, Tendsto (fun rank =>
      quittingLiteralRootStackOpponentSurvival (zeno.newWord rank) who)
        atTop (nhds 0) := by
  intro who
  have hcombined : Tendsto (fun rank =>
      quittingLiteralRootStackOpponentSurvival
        (zeno.newWord rank ++ zeno.baseWord rank) who) atTop (nhds 0) := by
    simpa only [combinedWord, quittingCombinedPremarkWord, baseWord] using
      hscreened who
  exact tendsto_prefixOpponentSurvival_zero_of_combined
    zeno.newWord zeno.baseWord who rho packet.lambda_pos
      (zeno.rho_le_baseOpponentSurvival · who) hcombined

/-- Eventual low-deleted-survival form consumed at an arbitrary positive
finite threshold. -/
theorem eventually_newWord_opponentSurvival_lt
    (hscreened : IsFinFourActualZenoFullyScreened zeno)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    ∀ᶠ rank in atTop, ∀ who,
      quittingLiteralRootStackOpponentSurvival (zeno.newWord rank) who <
        threshold := by
  apply Filter.eventually_all.mpr
  intro who
  exact (tendsto_order.1 (zeno.newWord_fullyScreened hscreened who)).2
    threshold hthreshold

end FinFourActualZenoDeletedSurvivalSource

end GameTheory
