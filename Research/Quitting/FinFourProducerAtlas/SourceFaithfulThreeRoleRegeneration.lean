/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.MinimumSingletonClockCompression
import Research.Quitting.FinFourProducerAtlas.ThreeRoleRegeneration
import Research.Quitting.SourceFaithfulMinimumLawCausalization

/-!
# Source-faithful regeneration at a Fin4 three-role endpoint law

The equality arm of a nonsingleton three-role endpoint retains a uniformly
positive routed stage atom along its literal target profiles and dates.  This
module causalizes exactly that supplied family.  The resulting minimum source
therefore exposes a chronology whose suffixes and marks are definitionally
the endpoint family, rather than an independently selected realization of the
same semantic law.

Only finite exact cap--Nash root words and cutoffs are newly selected.  No
rank orientation, paid cycle, observer rotation, or downstream response-menu
consumer is asserted.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open QuittingNonsingletonMinimumLawTransfer
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {profiles : ℕ → (quittingGame reward).BehaviorProfile}
  {owner : Fin 4} {marked : {S : Finset (Fin 4) // S.Nonempty}}
  {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
  {packet : QuittingReprojectionConcentratedPacket
    reward profiles owner marked cutoff scale}
  {mover recipient : Fin 4}

namespace ConcentratedCollisionThreeRoleEndpointLaw

/-- The literal target-profile family already retained by the endpoint law. -/
def sourceFaithfulTargetProfile
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  ConcentratedCollisionFourRole.targetProfile reward
    (ConcentratedCollisionFourRole.packetProfile packet
      (endpoint.ranks rank))
    (packet.mark (endpoint.ranks rank)) mover

/-- The literal marked-date family already retained by the endpoint law. -/
def sourceFaithfulTargetMark
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient) (rank : ℕ) : ℕ :=
  packet.mark (endpoint.ranks rank)

end ConcentratedCollisionThreeRoleEndpointLaw

/-- A same-minimum endpoint regeneration which retains the incoming endpoint
profiles and dates as the literal suffix family of its causalization.

Nonsingletonity is carried explicitly because it is exactly what turns the
source marked-stage floor into a routed target-stage floor. -/
structure FinFourSourceFaithfulMinimumTargetRegeneration
    (source : FinFourMinimumAtomProducer reward bound)
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient) where
  incoming_nonsingleton : 1 < marked.val.card
  causalization : QuittingSourceFaithfulMinimumCausalization
    endpoint.targetPoint endpoint.routedTerminal
    endpoint.sourceFaithfulTargetProfile endpoint.sourceFaithfulTargetMark
    packet.resolution

namespace FinFourSourceFaithfulMinimumTargetRegeneration

variable
  {endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
    mover recipient}
  (regeneration : FinFourSourceFaithfulMinimumTargetRegeneration
    source endpoint)

/-- The endpoint point and incoming point lie on exactly the same global
minimum-debt fibre. -/
theorem target_minimum
    (regeneration : FinFourSourceFaithfulMinimumTargetRegeneration
      source endpoint) :
    quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1 :=
  (regeneration.causalization.debt_eq_inf).trans source.debt_eq_inf.symm

/-- The causal atom built from the public source-faithful chronology tuple. -/
def atom : QuittingMinimumLawCausalSuffixAtom reward endpoint.targetPoint where
  terminal := endpoint.routedTerminal
  terminalMass_pos := endpoint.terminalMass_pos
  chronology := ⟨endpoint.sourceFaithfulTargetProfile,
    regeneration.causalization.cutoff,
    endpoint.sourceFaithfulTargetMark,
    regeneration.causalization.roots,
    regeneration.causalization.profiles_tendsto,
    regeneration.causalization.roots_length,
    regeneration.causalization.roots_nash,
    regeneration.causalization.prefix_debt_tendsto,
    regeneration.causalization.causal⟩

/-- The regenerated minimum source at the exact endpoint law point. -/
def next : FinFourMinimumAtomProducer reward bound where
  residual := source.residual
  point := endpoint.targetPoint
  point_mem := endpoint.target_mem
  semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier
    endpoint.targetPoint endpoint.target_mem
  minimum := by
    intro candidate hcandidate
    rw [target_minimum (regeneration := regeneration)]
    exact source.minimum candidate hcandidate
  inf_pos := source.inf_pos
  debt_eq_inf :=
    (target_minimum (regeneration := regeneration)).trans source.debt_eq_inf
  atom := regeneration.atom

/-- The explicit chronology of `next`; its suffixes and marks are the literal
incoming endpoint families. -/
def chronology : FinFourMinimumAtomChronology regeneration.next where
  profiles := endpoint.sourceFaithfulTargetProfile
  cutoff := regeneration.causalization.cutoff
  mark := endpoint.sourceFaithfulTargetMark
  roots := regeneration.causalization.roots
  profiles_tendsto := regeneration.causalization.profiles_tendsto
  roots_length := regeneration.causalization.roots_length
  roots_nash := regeneration.causalization.roots_nash
  prefix_debt_tendsto := by
    simpa only [prefixedProfile] using
      regeneration.causalization.prefix_debt_tendsto
  causal := regeneration.causalization.causal

/-- The regenerated source retains the original hard residual literally. -/
theorem next_residual_eq : regeneration.next.residual = source.residual := rfl

/-- The regenerated point is the actual endpoint joint-law point. -/
theorem next_point_eq : regeneration.next.point = endpoint.targetPoint := rfl

/-- The regenerated named atom is the endpoint's routed terminal. -/
theorem next_terminal_eq :
    regeneration.next.atom.terminal = endpoint.routedTerminal := rfl

/-- The explicit chronology uses the endpoint target profile at every rank. -/
theorem chronology_profile_eq (rank : ℕ) :
    regeneration.chronology.profiles rank =
      ConcentratedCollisionFourRole.targetProfile reward
        (ConcentratedCollisionFourRole.packetProfile packet
          (endpoint.ranks rank))
        (packet.mark (endpoint.ranks rank)) mover := rfl

/-- The explicit chronology uses the incoming endpoint date at every rank. -/
theorem chronology_mark_eq (rank : ℕ) :
    regeneration.chronology.mark rank =
      packet.mark (endpoint.ranks rank) := rfl

/-- The packet resolution remains a literal lower bound for the regenerated
named terminal-law coordinate. -/
theorem resolution_le_next_terminalMass :
    packet.resolution ≤
      regeneration.next.point.2 (some regeneration.next.atom.terminal) :=
  endpoint.terminalMass_floor

/-- The stronger object forgets to the older same-law regeneration surface. -/
def toMinimumTargetRegeneration :
    FinFourThreeRoleMinimumTargetRegeneration source endpoint where
  next := regeneration.next
  next_residual_eq := regeneration.next_residual_eq
  next_point_eq := regeneration.next_point_eq
  next_terminal_eq := regeneration.next_terminal_eq
  resolution_le_terminalMass := regeneration.resolution_le_next_terminalMass

/-- Arbitrary complete behavioral two-response menus transport rankwise along
the explicit source-faithful chronology. -/
theorem responseMenu_transport
    (who : Fin 4) {label : Type}
    (first second : label → ℕ →
      (quittingGame reward).BehaviorStrategy who) :
    ∀ name rank,
      quittingTerminalPayoff reward
          (Function.update
            (quittingLiteralRootStackProfile reward
              (regeneration.chronology.roots rank)
              (regeneration.chronology.profiles rank)) who
            (quittingShiftedBehavioralResponse
              (reward := reward) (regeneration.chronology.roots rank) who
              (first name rank))) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingLiteralRootStackProfile reward
              (regeneration.chronology.roots rank)
              (regeneration.chronology.profiles rank)) who
            (quittingShiftedBehavioralResponse
              (reward := reward) (regeneration.chronology.roots rank) who
              (second name rank))) who =
      quittingLiteralRootStackOpponentSurvival
          (regeneration.chronology.roots rank) who *
        (quittingTerminalPayoff reward
            (Function.update
              (endpoint.sourceFaithfulTargetProfile rank) who
              (first name rank)) who -
          quittingTerminalPayoff reward
            (Function.update
              (endpoint.sourceFaithfulTargetProfile rank) who
              (second name rank)) who) := by
  exact regeneration.causalization.responseMenu_transport who first second

/-- Every supplied rankwise menu lower bound survives with the same exact
opponent-survival multiplier. -/
theorem responseMenu_lowerBound_transport
    (who : Fin 4) {label : Type}
    (first second : label → ℕ →
      (quittingGame reward).BehaviorStrategy who)
    (lower : label → ℕ → ℝ)
    (hbound : ∀ name rank, lower name rank ≤
      quittingTerminalPayoff reward
          (Function.update
            (endpoint.sourceFaithfulTargetProfile rank) who
            (first name rank)) who -
        quittingTerminalPayoff reward
          (Function.update
            (endpoint.sourceFaithfulTargetProfile rank) who
            (second name rank)) who) :
    ∀ name rank,
      quittingLiteralRootStackOpponentSurvival
          (regeneration.chronology.roots rank) who * lower name rank ≤
        quittingTerminalPayoff reward
            (Function.update
              (quittingLiteralRootStackProfile reward
                (regeneration.chronology.roots rank)
                (regeneration.chronology.profiles rank)) who
              (quittingShiftedBehavioralResponse
                (reward := reward) (regeneration.chronology.roots rank) who
                (first name rank))) who -
          quittingTerminalPayoff reward
            (Function.update
              (quittingLiteralRootStackProfile reward
                (regeneration.chronology.roots rank)
                (regeneration.chronology.profiles rank)) who
              (quittingShiftedBehavioralResponse
                (reward := reward) (regeneration.chronology.roots rank) who
                (second name rank))) who := by
  intro name rank
  rw [regeneration.responseMenu_transport who first second name rank]
  exact mul_le_mul_of_nonneg_left (hbound name rank)
    (quittingLiteralRootStackOpponentSurvival_nonneg
      (regeneration.chronology.roots rank) who)

/-- The exact response-menu multiplier tends to one along the same public
chronology. -/
theorem responseMenuMultiplier_tendsto_one (who : Fin 4) :
    Tendsto (fun rank ↦ quittingLiteralRootStackOpponentSurvival
      (regeneration.chronology.roots rank) who) atTop (nhds 1) := by
  exact regeneration.causalization.opponentSurvival_tendsto_one who

/-- Joint survival is below the exact response-menu multiplier, which is at
most one, at every rank of the same public chronology. -/
theorem responseMenuMultiplier_bounds (who : Fin 4) (rank : ℕ) :
    quittingLiteralRootStackJointSurvival
        (regeneration.chronology.roots rank) ≤
      quittingLiteralRootStackOpponentSurvival
        (regeneration.chronology.roots rank) who ∧
    quittingLiteralRootStackOpponentSurvival
        (regeneration.chronology.roots rank) who ≤ 1 := by
  exact ⟨quittingLiteralRootStackJointSurvival_le_opponentSurvival
      (regeneration.chronology.roots rank) who,
    quittingLiteralRootStackOpponentSurvival_le_one
      (regeneration.chronology.roots rank) who⟩

end FinFourSourceFaithfulMinimumTargetRegeneration

/-! ## Profile-faithful fallback with reselected dates -/

/-- A same-minimum endpoint regeneration retaining every literal endpoint
target profile while selecting new positive dates from finite law-mass
windows.  This is the honest fallback when the original marked date has no
uniform routed stage-mass floor. -/
structure FinFourSourceFaithfulReselectedMarkRegeneration
    (source : FinFourMinimumAtomProducer reward bound)
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient) where
  causalization : QuittingSourceFaithfulMinimumCausalChronology
    endpoint.targetPoint endpoint.routedTerminal
      endpoint.sourceFaithfulTargetProfile

namespace FinFourSourceFaithfulReselectedMarkRegeneration

variable
  {endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
    mover recipient}
  (regeneration : FinFourSourceFaithfulReselectedMarkRegeneration
    source endpoint)

/-- The endpoint and source lie on the same global minimum-debt fibre. -/
theorem target_minimum
    (regeneration : FinFourSourceFaithfulReselectedMarkRegeneration
      source endpoint) :
    quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1 :=
  (regeneration.causalization.debt_eq_inf).trans source.debt_eq_inf.symm

/-- The fallback causal atom retains the endpoint terminal and profiles while
using its newly selected finite-window dates. -/
def atom : QuittingMinimumLawCausalSuffixAtom reward endpoint.targetPoint where
  terminal := endpoint.routedTerminal
  terminalMass_pos := regeneration.causalization.terminalMass_pos
  chronology := ⟨endpoint.sourceFaithfulTargetProfile,
    regeneration.causalization.cutoff,
    regeneration.causalization.mark,
    regeneration.causalization.roots,
    regeneration.causalization.profiles_tendsto,
    regeneration.causalization.roots_length,
    regeneration.causalization.roots_nash,
    regeneration.causalization.prefix_debt_tendsto,
    regeneration.causalization.causal⟩

/-- The fallback regenerated minimum source. -/
def next : FinFourMinimumAtomProducer reward bound where
  residual := source.residual
  point := endpoint.targetPoint
  point_mem := endpoint.target_mem
  semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier
    endpoint.targetPoint endpoint.target_mem
  minimum := by
    intro candidate hcandidate
    rw [target_minimum (regeneration := regeneration)]
    exact source.minimum candidate hcandidate
  inf_pos := source.inf_pos
  debt_eq_inf :=
    (target_minimum (regeneration := regeneration)).trans source.debt_eq_inf
  atom := regeneration.atom

/-- Public chronology of the fallback source, still indexed by the literal
endpoint target profiles. -/
def chronology : FinFourMinimumAtomChronology regeneration.next where
  profiles := endpoint.sourceFaithfulTargetProfile
  cutoff := regeneration.causalization.cutoff
  mark := regeneration.causalization.mark
  roots := regeneration.causalization.roots
  profiles_tendsto := regeneration.causalization.profiles_tendsto
  roots_length := regeneration.causalization.roots_length
  roots_nash := regeneration.causalization.roots_nash
  prefix_debt_tendsto := by
    simpa only [prefixedProfile] using
      regeneration.causalization.prefix_debt_tendsto
  causal := regeneration.causalization.causal

/-- The fallback retains the original hard residual. -/
theorem next_residual_eq : regeneration.next.residual = source.residual := rfl

/-- The fallback source point is the actual endpoint point. -/
theorem next_point_eq : regeneration.next.point = endpoint.targetPoint := rfl

/-- The fallback named terminal is the endpoint routed terminal. -/
theorem next_terminal_eq :
    regeneration.next.atom.terminal = endpoint.routedTerminal := rfl

/-- Every suffix profile is still the literal incoming endpoint target
profile.  Only the dates have been reselected. -/
theorem chronology_profile_eq (rank : ℕ) :
    regeneration.chronology.profiles rank =
      ConcentratedCollisionFourRole.targetProfile reward
        (ConcentratedCollisionFourRole.packetProfile packet
          (endpoint.ranks rank))
        (packet.mark (endpoint.ranks rank)) mover := rfl

/-- The fallback selected mark lies in its literal finite law-mass window and
carries positive mass, eventually. -/
theorem eventually_selectedMark_mem_positiveWindow : ∀ᶠ rank in atTop,
    regeneration.chronology.mark rank <
        regeneration.chronology.cutoff rank ∧
      0 < quittingStageCoalitionMass reward
        (regeneration.chronology.profiles rank)
        (regeneration.chronology.mark rank) endpoint.routedTerminal := by
  filter_upwards [regeneration.chronology.causal] with rank hrank
  exact ⟨hrank.2.1, hrank.2.2.1⟩

/-- The exact response-menu multiplier still tends to one after reselecting
only the finite-window dates. -/
theorem responseMenuMultiplier_tendsto_one (who : Fin 4) :
    Tendsto (fun rank ↦ quittingLiteralRootStackOpponentSurvival
      (regeneration.chronology.roots rank) who) atTop (nhds 1) := by
  apply tendsto_quittingLiteralRootStackOpponentSurvival_one
  simpa only [chronology, quittingLiteralRootStackJointSurvival,
    quittingCapNashStackContinueProduct] using
      regeneration.causalization.continueProduct_tendsto_one

/-- The fallback forgets to the older same-law regeneration surface. -/
def toMinimumTargetRegeneration :
    FinFourThreeRoleMinimumTargetRegeneration source endpoint where
  next := regeneration.next
  next_residual_eq := regeneration.next_residual_eq
  next_point_eq := regeneration.next_point_eq
  next_terminal_eq := regeneration.next_terminal_eq
  resolution_le_terminalMass := endpoint.terminalMass_floor

end FinFourSourceFaithfulReselectedMarkRegeneration

namespace ConcentratedCollisionThreeRoleEndpointLaw

/-- A nonsingleton same-minimum endpoint produces a source-faithful
regeneration.  Only the causal root words and finite cutoffs are selected;
the endpoint target profiles and incoming dates are kept literally. -/
theorem nonempty_sourceFaithful_finFourMinimumTargetRegeneration
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient)
    (hcollision : 1 < marked.val.card)
    (htarget : quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1) :
    Nonempty (FinFourSourceFaithfulMinimumTargetRegeneration source endpoint) := by
  have hmarked : ∀ rank, packet.resolution ≤
      quittingStageCoalitionMass reward
        (endpoint.sourceFaithfulTargetProfile rank)
        (endpoint.sourceFaithfulTargetMark rank) endpoint.routedTerminal := by
    intro rank
    have hchain := endpoint.perRank_mass_chain hcollision rank
    exact hchain.1.trans hchain.2.1
  obtain ⟨causalization⟩ := nonempty_sourceFaithfulMinimumCausalization
    endpoint.targetPoint endpoint.routedTerminal
      endpoint.sourceFaithfulTargetProfile endpoint.sourceFaithfulTargetMark
      packet.resolution endpoint.target_mem
      (by simpa only [sourceFaithfulTargetProfile] using
        endpoint.target_joint_tendsto)
      (by
        intro candidate hcandidate
        rw [htarget]
        exact source.minimum candidate hcandidate)
      (htarget.trans source.debt_eq_inf) source.inf_pos
      packet.resolution_pos hmarked
  exact ⟨{
    incoming_nonsingleton := hcollision
    causalization := causalization
  }⟩

/-- Every same-minimum endpoint, including the singleton incoming-mark case,
admits a profile-faithful regeneration after selecting new positive dates
from finite windows of the endpoint's routed terminal law. -/
theorem nonempty_sourceFaithful_reselectedMarkRegeneration
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw source.point.1 packet
      mover recipient)
    (htarget : quittingTerminalSemanticDebtSum endpoint.targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1) :
    Nonempty (FinFourSourceFaithfulReselectedMarkRegeneration
      source endpoint) := by
  obtain ⟨causalization⟩ :=
    nonempty_sourceFaithfulMinimumCausalChronology
      endpoint.targetPoint endpoint.routedTerminal
        endpoint.sourceFaithfulTargetProfile endpoint.target_mem
        (by simpa only [sourceFaithfulTargetProfile] using
          endpoint.target_joint_tendsto)
        (by
          intro candidate hcandidate
          rw [htarget]
          exact source.minimum candidate hcandidate)
        (htarget.trans source.debt_eq_inf) source.inf_pos
        endpoint.terminalMass_pos
  exact ⟨⟨causalization⟩⟩

end ConcentratedCollisionThreeRoleEndpointLaw

end GameTheory
