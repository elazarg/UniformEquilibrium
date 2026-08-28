/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Mathlib.Order.Filter.AtTopBot.Basic
import Research.Quitting.FinitePrefixClockClearing
import Research.Quitting.ConcentratedSingleton.StrategicDispatch
import Research.Quitting.FinFourProducerAtlas.ActualZenoDeletedSurvivalSource
import Research.Quitting.FinFourProducerAtlas.NormalizedReturn

/-!
# Finite data clearing for an actual Fin4 forced-pair row

This module attaches literal finite-word clearing to one actual normalized
forced-pair row.  The host exit below retains the incoming minimum source,
compact selection, source rank, pair label, comparison sibling, historical
payment, zero marked-owner defect, and complete postmark behavioral spine.

The terminal host compression is deliberately not called profitable.  The
generic recurrent packet is supported by the exposed historical pair and its
old paid sibling.  The existing concentrated consumer is applied literally,
but neither its strategic nor collision-minimum output is discharged.  No
minimum-fibre return or uniform-equilibrium conclusion is asserted here.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {rho : ℝ}
  {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
    returnSource rho}

/-- Finite provenance tag for one completed clock-clearing derivation.  Exit
modes `0`, `1`, and `2` mean host, direct nonsingleton premark, and
outsider-routed singleton premark.  `paidPlayer` records the ordered labels up
to `paidLength`; later entries are a harmless fixed filler. -/
structure FinFourFiniteClockClearingMechanism where
  paidLength : Fin 5
  paidPlayer : Fin 4 → Fin 4
  exitMode : Fin 3
  packetOwner : Fin 4
  packetTerminal : Finset (Fin 4)
  premarkMover : Fin 4
  premarkSourceTerminal : Finset (Fin 4)
  deriving DecidableEq, Fintype

/-- Once one Fin4 coordinate quits surely, one of the eight coalitions
containing it has product mass at least `1 / 8`.  This is the only finite
cardinality input in the premark pigeonhole. -/
theorem exists_finFourCoalition_containing_of_pureQuit_mass_ge_one_eighth
    (root : Fin 4 → PMF Bool) (who : Fin 4)
    (hroot : root who = PMF.pure true) :
    ∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
      who ∈ terminal.val ∧ 1 / 8 ≤ quittingRootCoalitionMass root terminal.val := by
  classical
  let labels : Finset (Finset (Fin 4)) :=
    Finset.univ.filter fun coalition => who ∈ coalition
  have hcard : labels.card = 8 := by
    dsimp only [labels]
    fin_cases who <;> decide
  have hsum : ∑ coalition ∈ labels,
      quittingRootCoalitionMass root coalition = 1 := by
    rw [← sum_quittingRootCoalitionMass_eq_one root]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro coalition _ hcoalition
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcoalition
    have hbound := quittingRootCoalitionMass_le_continueProbability_of_not_mem
      root coalition who hcoalition
    have hboundZero : quittingRootCoalitionMass root coalition ≤ 0 := by
      simpa [hroot] using hbound
    exact le_antisymm hboundZero
      (quittingRootCoalitionMass_nonneg' root coalition)
  have hlabels : labels.Nonempty := by
    refine ⟨{who}, ?_⟩
    simp [labels]
  obtain ⟨coalition, hcoalition, hmass⟩ :=
    Finset.exists_le_of_sum_le
      (f := fun _ => (1 / 8 : ℝ))
      (g := quittingRootCoalitionMass root) hlabels (by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, hsum]
        norm_num)
  have hwho : who ∈ coalition := by
    simpa [labels] using hcoalition
  exact ⟨⟨coalition, ⟨who, hwho⟩⟩, hwho, hmass⟩

/-- One actual selected forced-pair row together with a newly adjoined finite
word.  The new word is kept separate from the immutable source chronology in
the selected base profiles. -/
structure FinFourFullyScreenedForcedPairPrefix
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource rho) where
  selection : FinFourNormalizedReturnSelection packet
  rank : ℕ
  roots : List (Fin 4 → PMF Bool)

namespace FinFourFullyScreenedForcedPairPrefix

variable (data : FinFourFullyScreenedForcedPairPrefix packet)

/-- The actual normalized forced-pair family selected from the fixed source
chronology. -/
def family : QuittingMarkedPairDecoratedFamily reward :=
  data.selection.family

/-- The fixed base target before adjoining the new word. -/
def baseProfile : (quittingGame reward).BehaviorProfile :=
  data.family.profile data.rank

/-- The fixed historical comparison sibling before adjoining the new word. -/
def baseSourceProfile : (quittingGame reward).BehaviorProfile :=
  data.family.sourceProfile data.rank

/-- The actual target descendant after clearing precisely `cleared` in the
new word. -/
def profile (cleared : Finset (Fin 4)) :
    (quittingGame reward).BehaviorProfile :=
  data.family.descendantProfile data.rank
    (quittingLiteralRootStackClear data.roots cleared)

/-- The same literal clearing on the historical comparison sibling. -/
def sourceProfile (cleared : Finset (Fin 4)) :
    (quittingGame reward).BehaviorProfile :=
  data.family.descendantSourceProfile data.rank
    (quittingLiteralRootStackClear data.roots cleared)

/-- The old marked date shifted only by the length of the newly adjoined
word. -/
def mark (cleared : Finset (Fin 4)) : ℕ :=
  data.family.descendantMark data.rank
    (quittingLiteralRootStackClear data.roots cleared)

/-- Player-deleted survival through the currently cleared new word. -/
def opponentSurvival (cleared : Finset (Fin 4)) (who : Fin 4) : ℝ :=
  quittingLiteralRootStackOpponentSurvival
    (quittingLiteralRootStackClear data.roots cleared) who

/-- The current descendant is the retained-tail timing graft of its displayed
cleared word and immutable selected base profile. -/
theorem profile_eq_graft (cleared : Finset (Fin 4)) :
    data.profile cleared =
      quittingRetainedTailFiniteTimingGraft reward
        (quittingLiteralRootStackClear data.roots cleared) data.baseProfile := by
  rfl

/-- The Continue-through sibling used by finite timing is exactly the next
cleared descendant. -/
theorem passProfile_eq_insert (cleared : Finset (Fin 4)) (who : Fin 4) :
    quittingRetainedTailFiniteTimingPassProfile reward
        (quittingLiteralRootStackClear data.roots cleared) data.baseProfile who =
      data.profile (insert who cleared) := by
  unfold quittingRetainedTailFiniteTimingPassProfile profile baseProfile
  rw [quittingLiteralRootStackClear_insert]
  rfl

/-- The terminal-gap deleted-survival threshold `gamma / (16 R)`. -/
def eta (_data : FinFourFullyScreenedForcedPairPrefix packet) (R : ℝ) : ℝ :=
  source.residual.witness.terminalGap / (16 * R)

/-- The advertised fixed packet resolution `rho * gamma / (128 R)`. -/
def resolution (_data : FinFourFullyScreenedForcedPairPrefix packet)
    (R : ℝ) : ℝ :=
  rho * source.residual.witness.terminalGap / (128 * R)

theorem eta_pos {R : ℝ} (hR : 0 < R) : 0 < data.eta R := by
  exact div_pos source.residual.witness.terminalGap_pos (mul_pos (by norm_num) hR)

theorem resolution_pos {R : ℝ} (hR : 0 < R) :
    0 < data.resolution R := by
  exact div_pos
    (mul_pos packet.lambda_pos source.residual.witness.terminalGap_pos)
    (mul_pos (by norm_num) hR)

/-- Literal insertion of one clear is the ordinary unilateral update of the
current descendant, with the selected base profile restored after the new
word. -/
theorem profile_insert_eq_update (cleared : Finset (Fin 4)) (who : Fin 4) :
    data.profile (insert who cleared) =
      Function.update (data.profile cleared) who
        (quittingLiteralRootStackContinueDeviation reward
          (quittingLiteralRootStackClear data.roots cleared)
          (data.baseProfile who)) := by
  exact quittingFinitePrefixClearedProfile_insert_eq_update
    data.roots data.baseProfile cleared who

/-- The same unilateral clearing is applied to the historical comparison
sibling, so the selected arbitrary-data provenance is not lost. -/
theorem sourceProfile_insert_eq_update
    (cleared : Finset (Fin 4)) (who : Fin 4) :
    data.sourceProfile (insert who cleared) =
      Function.update (data.sourceProfile cleared) who
        (quittingLiteralRootStackContinueDeviation reward
          (quittingLiteralRootStackClear data.roots cleared)
          (data.baseSourceProfile who)) := by
  exact quittingFinitePrefixClearedProfile_insert_eq_update
    data.roots data.baseSourceProfile cleared who

/-- Clearing a host makes joint entry into the immutable base equal exactly
to that host's former opponent survival through the new word. -/
theorem prefixSurvival_insert_eq_opponentSurvival
    (cleared : Finset (Fin 4)) (host : Fin 4) :
    data.family.prefixSurvival
        (quittingLiteralRootStackClear data.roots (insert host cleared)) =
      data.opponentSurvival cleared host := by
  rw [quittingLiteralRootStackClear_insert]
  exact quittingLiteralRootStackJointSurvival_forceContinue
    (quittingLiteralRootStackClear data.roots cleared) host

/-- Exact stage-mass scaling of the old pair after the terminal host clear. -/
theorem host_markedMass_eq
    (cleared : Finset (Fin 4)) (host : Fin 4) :
    quittingStageCoalitionMass reward
        (data.profile (insert host cleared))
        (data.mark (insert host cleared)) data.family.terminal =
      data.opponentSurvival cleared host *
        quittingStageCoalitionMass reward data.baseProfile
          (data.family.mark data.rank) data.family.terminal := by
  change quittingStageCoalitionMass reward
      (data.family.descendantProfile data.rank
        (quittingLiteralRootStackClear data.roots (insert host cleared)))
      (data.family.descendantMark data.rank
        (quittingLiteralRootStackClear data.roots (insert host cleared)))
      data.family.terminal = _
  rw [← data.family.rawDecoration_markedMass_eq data.rank,
    data.family.rawDecoration_markedMass_eq_prefixSurvival_mul,
    data.prefixSurvival_insert_eq_opponentSurvival]
  rfl

/-- Exact historical source-to-pair gain scaling after the same host clear. -/
theorem host_actualGain_eq
    (cleared : Finset (Fin 4)) (host : Fin 4) :
    quittingTerminalPayoff reward (data.profile (insert host cleared))
          data.family.gainMover -
        quittingTerminalPayoff reward
          (data.sourceProfile (insert host cleared))
          data.family.gainMover =
      data.opponentSurvival cleared host *
        (quittingTerminalPayoff reward data.baseProfile
            data.family.gainMover -
          quittingTerminalPayoff reward data.baseSourceProfile
            data.family.gainMover) := by
  change quittingTerminalPayoff reward
        (data.family.descendantProfile data.rank
          (quittingLiteralRootStackClear data.roots (insert host cleared)))
          data.family.gainMover -
      quittingTerminalPayoff reward
        (data.family.descendantSourceProfile data.rank
          (quittingLiteralRootStackClear data.roots (insert host cleared)))
          data.family.gainMover = _
  rw [← data.family.rawDecoration_actualGain_eq data.rank,
    data.family.rawDecoration_actualGain_eq_prefixSurvival_mul,
    data.prefixSurvival_insert_eq_opponentSurvival]
  rfl

/-- Exact marked-pair mass scaling at every intermediate cleared set. -/
theorem markedMass_eq_jointSurvival_mul (cleared : Finset (Fin 4)) :
    quittingStageCoalitionMass reward (data.profile cleared)
        (data.mark cleared) data.family.terminal =
      quittingLiteralRootStackJointSurvival
          (quittingLiteralRootStackClear data.roots cleared) *
        quittingStageCoalitionMass reward data.baseProfile
          (data.family.mark data.rank) data.family.terminal := by
  change quittingStageCoalitionMass reward
      (data.family.descendantProfile data.rank
        (quittingLiteralRootStackClear data.roots cleared))
      (data.family.descendantMark data.rank
        (quittingLiteralRootStackClear data.roots cleared))
      data.family.terminal = _
  rw [← data.family.rawDecoration_markedMass_eq,
    data.family.rawDecoration_markedMass_eq_prefixSurvival_mul]
  rfl

/-- The historical source-to-target gain scales by the same exact joint
survival at every intermediate cleared set. -/
theorem actualGain_eq_jointSurvival_mul (cleared : Finset (Fin 4)) :
    quittingTerminalPayoff reward (data.profile cleared) data.family.gainMover -
        quittingTerminalPayoff reward (data.sourceProfile cleared)
          data.family.gainMover =
      quittingLiteralRootStackJointSurvival
          (quittingLiteralRootStackClear data.roots cleared) *
        (quittingTerminalPayoff reward data.baseProfile data.family.gainMover -
          quittingTerminalPayoff reward data.baseSourceProfile
            data.family.gainMover) := by
  change quittingTerminalPayoff reward
        (data.family.descendantProfile data.rank
          (quittingLiteralRootStackClear data.roots cleared))
        data.family.gainMover -
      quittingTerminalPayoff reward
        (data.family.descendantSourceProfile data.rank
          (quittingLiteralRootStackClear data.roots cleared))
        data.family.gainMover = _
  rw [← data.family.rawDecoration_actualGain_eq,
    data.family.rawDecoration_actualGain_eq_prefixSurvival_mul]
  rfl

/-- A host above `eta` exposes the historical pair above the fixed advertised
resolution. -/
theorem resolution_lt_host_markedMass
    {R : ℝ} (hR : 0 < R) (cleared : Finset (Fin 4)) (host : Fin 4)
    (hhost : data.eta R ≤ data.opponentSurvival cleared host) :
    data.resolution R <
      quittingStageCoalitionMass reward
        (data.profile (insert host cleared))
        (data.mark (insert host cleared)) data.family.terminal := by
  rw [data.host_markedMass_eq]
  have hbase := data.selection.lambda_lt_markedMass data.rank
  have heta := data.eta_pos hR
  have hopponent := quittingLiteralRootStackOpponentSurvival_nonneg
    (quittingLiteralRootStackClear data.roots cleared) host
  have hscaled :
      rho * data.eta R <
        data.opponentSurvival cleared host *
          quittingStageCoalitionMass reward data.baseProfile
            (data.family.mark data.rank) data.family.terminal := by
    have hbase0 : 0 ≤ quittingStageCoalitionMass reward data.baseProfile
        (data.family.mark data.rank) data.family.terminal :=
      (packet.lambda_pos.trans hbase).le
    have hproduct := mul_lt_mul hbase hhost heta hbase0
    simpa [baseProfile, family, mul_comm] using hproduct
  have hformula : data.resolution R = rho * data.eta R / 8 := by
    unfold resolution eta
    field_simp
    ring
  rw [hformula]
  have hrhoeta : 0 < rho * data.eta R := mul_pos packet.lambda_pos heta
  nlinarith

/-- The retained historical payment has the fixed positive floor
`rho * eta * gamma`.  It comes from the old comparison sibling, not from the
final host compression. -/
theorem historicalGainFloor_le_host_actualGain
    {R : ℝ} (hR : 0 < R) (cleared : Finset (Fin 4)) (host : Fin 4)
    (hhost : data.eta R ≤ data.opponentSurvival cleared host) :
    rho * data.eta R * source.residual.witness.terminalGap ≤
      quittingTerminalPayoff reward (data.profile (insert host cleared))
          data.family.gainMover -
        quittingTerminalPayoff reward
          (data.sourceProfile (insert host cleared))
          data.family.gainMover := by
  rw [data.host_actualGain_eq]
  have hbase :=
    data.selection.lambda_mul_terminalGap_le_actualGain data.rank
  have heta := data.eta_pos hR
  have hgap := source.residual.witness.terminalGap_pos
  have hgain0 : 0 ≤ quittingTerminalPayoff reward data.baseProfile
        data.family.gainMover -
      quittingTerminalPayoff reward data.baseSourceProfile
        data.family.gainMover :=
    (data.family.actualGain_pos data.rank).le
  have hproduct := mul_le_mul hbase hhost heta.le hgain0
  simpa [baseProfile, baseSourceProfile, family, mul_assoc, mul_left_comm,
    mul_comm] using hproduct

/-- Full postmark behavioral provenance of the host descendant. -/
theorem host_postMarkSpine_eq
    (cleared : Finset (Fin 4)) (host : Fin 4) :
    quittingAllContinueProfileSpine reward
        (data.profile (insert host cleared))
        (data.mark (insert host cleared) + 1) =
      quittingAllContinueProfileSpine reward data.baseProfile
        (data.family.mark data.rank + 1) :=
  data.family.descendant_postMarkSpine_eq data.rank _

/-- Constant packet source supported by the exposed historical pair. -/
def hostConstantSource
    {R : ℝ} (hR : 0 < R) (cleared : Finset (Fin 4)) (host : Fin 4)
    (hhost : data.eta R ≤ data.opponentSurvival cleared host) :
    QuittingConstantConcentratedPacketSource reward where
  profile := data.profile (insert host cleared)
  owner := data.family.markedOwner
  terminal := data.family.terminal
  stage := data.mark (insert host cleared)
  resolution := data.resolution R
  resolution_pos := data.resolution_pos hR
  resolution_le_stageMass :=
    (data.resolution_lt_host_markedMass hR cleared host hhost).le
  ownerDefect_eq_zero :=
    data.family.descendant_markedOwnerDefect_eq_zero data.rank _

/-- Provenance-rich host exit.  The generic packet is literal, while the
incoming source and historical comparison remain available through
`data`. -/
structure HostExit (R : ℝ) (cleared : Finset (Fin 4)) where
  R_pos : 0 < R
  host : Fin 4
  hostSurvival : data.eta R ≤ data.opponentSurvival cleared host

namespace HostExit

variable {data : FinFourFullyScreenedForcedPairPrefix packet}
  {R : ℝ} {cleared : Finset (Fin 4)}
  (exit : data.HostExit R cleared)

def constantSource : QuittingConstantConcentratedPacketSource reward :=
  data.hostConstantSource exit.R_pos cleared exit.host exit.hostSurvival

/-- The actual generic recurrent packet at resolution
`rho * gamma / (128 R)`. -/
def concentratedPacket : QuittingReprojectionConcentratedPacket reward
    exit.constantSource.profiles exit.constantSource.owner
      exit.constantSource.terminal exit.constantSource.cutoff
        exit.constantSource.scale :=
  exit.constantSource.packet

theorem resolution_eq : exit.constantSource.resolution =
    rho * source.residual.witness.terminalGap / (128 * R) := by
  rfl

theorem historicalGain_pos : 0 <
    quittingTerminalPayoff reward exit.constantSource.profile
          data.family.gainMover -
      quittingTerminalPayoff reward
        (data.sourceProfile (insert exit.host cleared))
          data.family.gainMover := by
  have hfloorPos : 0 <
      rho * data.eta R * source.residual.witness.terminalGap :=
    mul_pos (mul_pos packet.lambda_pos (data.eta_pos exit.R_pos))
      source.residual.witness.terminalGap_pos
  exact hfloorPos.trans_le
    (data.historicalGainFloor_le_host_actualGain exit.R_pos cleared exit.host
      exit.hostSurvival)

end HostExit

/-- One genuinely paid clearing step, together with the fact that its player
was not already cleared. -/
structure PaidClear (R : ℝ) (cleared : Finset (Fin 4)) where
  R_pos : 0 < R
  paid : QuittingFinitePrefixPaidClear reward
    (quittingLiteralRootStackClear data.roots cleared) data.baseProfile
      source.residual.witness.terminalGap
  who_not_mem : paid.who ∉ cleared

namespace PaidClear

variable {data : FinFourFullyScreenedForcedPairPrefix packet}
  {R : ℝ} {cleared : Finset (Fin 4)}
  (edge : data.PaidClear R cleared)

/-- The paid target is the literal next cleared descendant. -/
theorem targetProfile_eq :
    quittingRetainedTailFiniteTimingPassProfile reward
        (quittingLiteralRootStackClear data.roots cleared) data.baseProfile
          edge.paid.who =
      data.profile (insert edge.paid.who cleared) :=
  data.passProfile_eq_insert cleared edge.paid.who

/-- Exact mover-debt subtraction for a paid clear.  The unrestricted
best-response envelope is unchanged because only the mover's strategy is
replaced. -/
theorem moverDebt_eq_sub_gain :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (data.profile (insert edge.paid.who cleared))) edge.paid.who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (data.profile cleared))
          edge.paid.who -
        (quittingTerminalPayoff reward
            (data.profile (insert edge.paid.who cleared)) edge.paid.who -
          quittingTerminalPayoff reward (data.profile cleared)
            edge.paid.who) := by
  rw [data.profile_insert_eq_update]
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  dsimp only [Prod.fst, Prod.snd]
  rw [quittingContinuationBestResponseValue_update_self]
  ring

/-- Every paid clear weakly increases the retained marked-pair mass. -/
theorem markedMass_le_next :
    quittingStageCoalitionMass reward (data.profile cleared)
        (data.mark cleared) data.family.terminal ≤
      quittingStageCoalitionMass reward
        (data.profile (insert edge.paid.who cleared))
        (data.mark (insert edge.paid.who cleared)) data.family.terminal := by
  rw [data.markedMass_eq_jointSurvival_mul,
    data.markedMass_eq_jointSurvival_mul]
  have hsurvival := quittingLiteralRootStackJointSurvival_le_forceContinue
    (quittingLiteralRootStackClear data.roots cleared) edge.paid.who
  rw [← quittingLiteralRootStackClear_insert] at hsurvival
  exact mul_le_mul_of_nonneg_right hsurvival
    (le_of_lt (data.family.markedMass_pos data.rank))

/-- The same paid clear weakly increases the historical source-to-pair gain,
and does so by the same literal prefix-survival change. -/
theorem actualGain_le_next :
    quittingTerminalPayoff reward (data.profile cleared) data.family.gainMover -
        quittingTerminalPayoff reward (data.sourceProfile cleared)
          data.family.gainMover ≤
      quittingTerminalPayoff reward
          (data.profile (insert edge.paid.who cleared)) data.family.gainMover -
        quittingTerminalPayoff reward
          (data.sourceProfile (insert edge.paid.who cleared))
          data.family.gainMover := by
  rw [data.actualGain_eq_jointSurvival_mul,
    data.actualGain_eq_jointSurvival_mul]
  have hsurvival := quittingLiteralRootStackJointSurvival_le_forceContinue
    (quittingLiteralRootStackClear data.roots cleared) edge.paid.who
  rw [← quittingLiteralRootStackClear_insert] at hsurvival
  exact mul_le_mul_of_nonneg_right hsurvival
    (le_of_lt (data.family.actualGain_pos data.rank))

end PaidClear

/-- One typed entry of the finite paid-clearing ledger.  The entry retains
its exact pre-clear set and therefore exposes both literal prefix-scaling
identities, the mover-debt subtraction, and the two weak-increase laws. -/
structure PaidClearLedgerEntry (R : ℝ) where
  cleared : Finset (Fin 4)
  edge : data.PaidClear R cleared

namespace PaidClearLedgerEntry

variable {data : FinFourFullyScreenedForcedPairPrefix packet}
  {R : ℝ}
  (entry : data.PaidClearLedgerEntry R)

theorem markedMass_eq_before :
    quittingStageCoalitionMass reward (data.profile entry.cleared)
        (data.mark entry.cleared) data.family.terminal =
      quittingLiteralRootStackJointSurvival
          (quittingLiteralRootStackClear data.roots entry.cleared) *
        quittingStageCoalitionMass reward data.baseProfile
          (data.family.mark data.rank) data.family.terminal :=
  data.markedMass_eq_jointSurvival_mul entry.cleared

theorem markedMass_eq_after :
    quittingStageCoalitionMass reward
        (data.profile (insert entry.edge.paid.who entry.cleared))
        (data.mark (insert entry.edge.paid.who entry.cleared))
          data.family.terminal =
      quittingLiteralRootStackJointSurvival
          (quittingLiteralRootStackClear data.roots
            (insert entry.edge.paid.who entry.cleared)) *
        quittingStageCoalitionMass reward data.baseProfile
          (data.family.mark data.rank) data.family.terminal :=
  data.markedMass_eq_jointSurvival_mul _

theorem actualGain_eq_before :
    quittingTerminalPayoff reward (data.profile entry.cleared)
          data.family.gainMover -
        quittingTerminalPayoff reward (data.sourceProfile entry.cleared)
          data.family.gainMover =
      quittingLiteralRootStackJointSurvival
          (quittingLiteralRootStackClear data.roots entry.cleared) *
        (quittingTerminalPayoff reward data.baseProfile data.family.gainMover -
          quittingTerminalPayoff reward data.baseSourceProfile
            data.family.gainMover) :=
  data.actualGain_eq_jointSurvival_mul entry.cleared

theorem actualGain_eq_after :
    quittingTerminalPayoff reward
          (data.profile (insert entry.edge.paid.who entry.cleared))
          data.family.gainMover -
        quittingTerminalPayoff reward
          (data.sourceProfile (insert entry.edge.paid.who entry.cleared))
          data.family.gainMover =
      quittingLiteralRootStackJointSurvival
          (quittingLiteralRootStackClear data.roots
            (insert entry.edge.paid.who entry.cleared)) *
        (quittingTerminalPayoff reward data.baseProfile data.family.gainMover -
          quittingTerminalPayoff reward data.baseSourceProfile
            data.family.gainMover) :=
  data.actualGain_eq_jointSurvival_mul _

theorem moverDebt_eq_sub_gain :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (data.profile (insert entry.edge.paid.who entry.cleared)))
          entry.edge.paid.who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (data.profile entry.cleared))
          entry.edge.paid.who -
        (quittingTerminalPayoff reward
            (data.profile (insert entry.edge.paid.who entry.cleared))
            entry.edge.paid.who -
          quittingTerminalPayoff reward (data.profile entry.cleared)
            entry.edge.paid.who) :=
  entry.edge.moverDebt_eq_sub_gain

theorem terminalGap_div_two_le_moverGain :
    source.residual.witness.terminalGap / 2 ≤
      quittingTerminalPayoff reward
          (data.profile (insert entry.edge.paid.who entry.cleared))
          entry.edge.paid.who -
        quittingTerminalPayoff reward (data.profile entry.cleared)
          entry.edge.paid.who := by
  rw [← entry.edge.targetProfile_eq]
  change source.residual.witness.terminalGap / 2 ≤
    quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingPassProfile reward
          (quittingLiteralRootStackClear data.roots entry.cleared)
            data.baseProfile entry.edge.paid.who) entry.edge.paid.who -
      quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward
          (quittingLiteralRootStackClear data.roots entry.cleared)
            data.baseProfile) entry.edge.paid.who
  exact entry.edge.paid.gain

theorem markedMass_le_after :
    quittingStageCoalitionMass reward (data.profile entry.cleared)
        (data.mark entry.cleared) data.family.terminal ≤
      quittingStageCoalitionMass reward
        (data.profile (insert entry.edge.paid.who entry.cleared))
        (data.mark (insert entry.edge.paid.who entry.cleared))
          data.family.terminal :=
  entry.edge.markedMass_le_next

theorem actualGain_le_after :
    quittingTerminalPayoff reward (data.profile entry.cleared)
          data.family.gainMover -
        quittingTerminalPayoff reward (data.sourceProfile entry.cleared)
          data.family.gainMover ≤
      quittingTerminalPayoff reward
          (data.profile (insert entry.edge.paid.who entry.cleared))
          data.family.gainMover -
        quittingTerminalPayoff reward
          (data.sourceProfile (insert entry.edge.paid.who entry.cleared))
          data.family.gainMover :=
  entry.edge.actualGain_le_next

end PaidClearLedgerEntry

/-- The actual Continue-through sibling underlying one premark atom. -/
def premarkPassProfile {cleared : Finset (Fin 4)}
    (atom : QuittingFinitePrefixPremarkAtom reward
      (quittingLiteralRootStackClear data.roots cleared) data.baseProfile
        source.residual.witness.terminalGap) :
    (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailFiniteTimingPassProfile reward
    (quittingLiteralRootStackClear data.roots cleared) data.baseProfile atom.who

/-- The literal profitable target at the extracted premark date. -/
def premarkTargetProfile {cleared : Finset (Fin 4)}
    (atom : QuittingFinitePrefixPremarkAtom reward
      (quittingLiteralRootStackClear data.roots cleared) data.baseProfile
        source.residual.witness.terminalGap) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralOneDateProfile reward (data.premarkPassProfile atom) atom.who
    atom.time true

/-- A profitable premark target plus its pigeonholed actual coalition. -/
structure PremarkExit (R : ℝ) (cleared : Finset (Fin 4)) where
  R_pos : 0 < R
  reward_abs_le : ∀ terminal player, |reward terminal player| ≤ R
  atom : QuittingFinitePrefixPremarkAtom reward
    (quittingLiteralRootStackClear data.roots cleared) data.baseProfile
      source.residual.witness.terminalGap
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  who_mem_terminal : atom.who ∈ terminal.val
  rootMass : 1 / 8 ≤ quittingRootCoalitionMass
    (quittingProfileLiveRoot reward (data.premarkTargetProfile atom) atom.time)
      terminal.val

namespace PremarkExit

variable {data : FinFourFullyScreenedForcedPairPrefix packet}
  {R : ℝ} {cleared : Finset (Fin 4)}
  (exit : data.PremarkExit R cleared)

/-- The original premark target resumes its actual Continue-through sibling
with full behavioral equality after the marked date. -/
theorem postDateSpine_eq :
    quittingAllContinueProfileSpine reward (data.premarkTargetProfile exit.atom)
        (exit.atom.time + 1) =
      quittingAllContinueProfileSpine reward (data.premarkPassProfile exit.atom)
        (exit.atom.time + 1) :=
  quittingAllContinueProfileSpine_literalOneDateProfile_succ_eq
    (data.premarkPassProfile exit.atom) exit.atom.who exit.atom.time true

/-- The actual premark source-to-target gain keeps the strict `gamma / 4`
floor supplied by finite timing. -/
theorem gain_gt : source.residual.witness.terminalGap / 4 <
    quittingTerminalPayoff reward (data.premarkTargetProfile exit.atom)
        exit.atom.who -
      quittingTerminalPayoff reward (data.premarkPassProfile exit.atom)
        exit.atom.who := by
  exact exit.atom.gain

/-- The profitable premark mover's literal Quit action is its strict better
endpoint, hence its marked local coordinate defect is exactly zero. -/
theorem markedMoverDefect_eq_zero :
    quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (data.premarkTargetProfile exit.atom) (exit.atom.time + 1))).1
        (quittingProfileLiveRoot reward (data.premarkTargetProfile exit.atom)
          exit.atom.time) exit.atom.who = 0 := by
  let pass := data.premarkPassProfile exit.atom
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward pass (exit.atom.time + 1))
  let root := quittingProfileLiveRoot reward pass exit.atom.time
  have hcontinue : Function.update root exit.atom.who (PMF.pure false) = root := by
    funext player
    by_cases hplayer : player = exit.atom.who
    · subst player
      rw [Function.update_self]
      change PMF.pure false = quittingProfileLiveRoot reward
        (quittingRetainedTailFiniteTimingPassProfile reward
          (quittingLiteralRootStackClear data.roots cleared) data.baseProfile
            exit.atom.who) exit.atom.time exit.atom.who
      exact exit.atom.passProfile_liveRoot_self_eq_pureContinue.symm
    · simp [Function.update_of_ne hplayer]
  have hgainPos : 0 <
      quittingTerminalPayoff reward (data.premarkTargetProfile exit.atom)
          exit.atom.who -
        quittingTerminalPayoff reward pass exit.atom.who :=
    (div_pos source.residual.witness.terminalGap_pos (by norm_num)).trans
      exit.gain_gt
  unfold FinFourFullyScreenedForcedPairPrefix.premarkTargetProfile at hgainPos
  rw [quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect]
    at hgainPos
  change 0 < quittingLiveMass reward pass exit.atom.time *
    (quittingRootSuccessorPayoff reward tail.1
        (Function.update root exit.atom.who (PMF.pure true)) exit.atom.who -
      quittingRootSuccessorPayoff reward tail.1 root exit.atom.who) at hgainPos
  have hlive := quittingLiveMass_nonneg reward pass exit.atom.time
  have hdiff : 0 < quittingRootSuccessorPayoff reward tail.1
        (Function.update root exit.atom.who (PMF.pure true)) exit.atom.who -
      quittingRootSuccessorPayoff reward tail.1 root exit.atom.who := by
    nlinarith
  have hendpoint : 0 <
      quittingRootEndpointDifference reward tail.1 root exit.atom.who := by
    unfold quittingRootEndpointDifference quittingRootQuitPayoff
      quittingRootContinuePayoff
    rw [hcontinue]
    simpa [quittingRootSuccessorPayoff] using hdiff
  have hbest : quittingRootBestEndpointAction reward tail.1 root
      exit.atom.who = true := by
    unfold quittingRootBestEndpointAction
    split_ifs with hle
    · unfold quittingRootEndpointDifference at hendpoint
      linarith
    · rfl
  rw [exit.postDateSpine_eq,
    show data.premarkTargetProfile exit.atom =
        quittingLiteralOneDateProfile reward pass exit.atom.who
          exit.atom.time true by rfl,
    quittingProfileLiveRoot_literalOneDateProfile]
  change quittingRootCoordinateNashDefect reward tail.1
    (Function.update root exit.atom.who (PMF.pure true)) exit.atom.who = 0
  rw [← hbest]
  exact quittingRootCoordinateNashDefect_update_bestEndpoint_eq_zero
    reward tail.1 root exit.atom.who

/-- The profitable premark has live mass strictly above `gamma / (8 R)`. -/
theorem gap_div_eight_mul_lt_liveMass :
    source.residual.witness.terminalGap / (8 * R) <
      quittingLiveMass reward (data.premarkTargetProfile exit.atom)
        exit.atom.time := by
  unfold FinFourFullyScreenedForcedPairPrefix.premarkTargetProfile
  rw [quittingLiveMass_literalOneDateProfile_eq]
  exact exit.atom.gap_div_eight_mul_lt_liveMass exit.R_pos
    exit.reward_abs_le

/-- The pigeonholed actual stage atom has mass strictly above the packet's
advertised `gamma / (64 R)` premark floor. -/
theorem premarkMass_gt :
    source.residual.witness.terminalGap / (64 * R) <
      quittingStageCoalitionMass reward (data.premarkTargetProfile exit.atom)
        exit.atom.time exit.terminal := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  have hlive := exit.gap_div_eight_mul_lt_liveMass
  have hlive0 := quittingLiveMass_nonneg reward
    (data.premarkTargetProfile exit.atom) exit.atom.time
  have hscaled := mul_le_mul_of_nonneg_left exit.rootMass hlive0
  calc
    source.residual.witness.terminalGap / (64 * R) =
        (source.residual.witness.terminalGap / (8 * R)) * (1 / 8) := by
      field_simp
      ring
    _ < quittingLiveMass reward (data.premarkTargetProfile exit.atom)
          exit.atom.time * (1 / 8) := by nlinarith
    _ ≤ quittingLiveMass reward (data.premarkTargetProfile exit.atom)
          exit.atom.time * quittingRootCoalitionMass
            (quittingProfileLiveRoot reward (data.premarkTargetProfile exit.atom)
              exit.atom.time) exit.terminal.val := hscaled

/-- The advertised fixed resolution lies strictly below the premark atom. -/
theorem resolution_lt_stageMass :
    data.resolution R <
      quittingStageCoalitionMass reward (data.premarkTargetProfile exit.atom)
        exit.atom.time exit.terminal := by
  apply lt_trans _ exit.premarkMass_gt
  have hunit := packet.lambda_lt_one
  have hpositive : 0 <
      source.residual.witness.terminalGap / (64 * R) :=
    div_pos source.residual.witness.terminalGap_pos
      (mul_pos (by norm_num) exit.R_pos)
  calc
    data.resolution R = (rho / 2) *
        (source.residual.witness.terminalGap / (64 * R)) := by
      unfold FinFourFullyScreenedForcedPairPrefix.resolution
      field_simp
      ring
    _ < 1 * (source.residual.witness.terminalGap / (64 * R)) := by
      apply mul_lt_mul_of_pos_right _ hpositive
      linarith
    _ = source.residual.witness.terminalGap / (64 * R) := one_mul _

/-- If the premark coalition is kept without rerouting, its actual profitable
profile and mover already form a constant concentrated-packet source.  This
is the cardinality-sensitive branch used when the coalition is not a
singleton. -/
def directConstantSource : QuittingConstantConcentratedPacketSource reward where
  profile := data.premarkTargetProfile exit.atom
  owner := exit.atom.who
  terminal := exit.terminal
  stage := exit.atom.time
  resolution := data.resolution R
  resolution_pos := data.resolution_pos exit.R_pos
  resolution_le_stageMass := exit.resolution_lt_stageMass.le
  ownerDefect_eq_zero := exit.markedMoverDefect_eq_zero

/-- The direct premark packet preserves the literal profitable profile,
mover, and pigeonholed coalition. -/
def directConcentratedPacket : QuittingReprojectionConcentratedPacket reward
    exit.directConstantSource.profiles exit.directConstantSource.owner
      exit.directConstantSource.terminal exit.directConstantSource.cutoff
        exit.directConstantSource.scale :=
  exit.directConstantSource.packet

/-- Some Fin4 player has a singleton different from the extracted nonempty
coalition, providing a legal endpoint-routing owner. -/
theorem exists_packetOwner : ∃ owner : Fin 4, exit.terminal.val ≠ {owner} := by
  by_cases hzero : exit.terminal.val = {(0 : Fin 4)}
  · refine ⟨(1 : Fin 4), ?_⟩
    intro hone
    have : (0 : Fin 4) = 1 := by
      have hmem : (0 : Fin 4) ∈ exit.terminal.val := by simp [hzero]
      simp [hone] at hmem
    omega
  · exact ⟨(0 : Fin 4), hzero⟩

/-- A selected packet owner, used only to route the actual positive atom. -/
noncomputable def packetOwner : Fin 4 := Classical.choose exit.exists_packetOwner

theorem terminal_ne_packetOwner : exit.terminal.val ≠ {exit.packetOwner} :=
  Classical.choose_spec exit.exists_packetOwner

/-- A nonsingleton premark coalition contains a literal member distinct from
the unchanged premark mover. -/
theorem exists_otherOfNonsingleton
    (hcard : exit.terminal.val.card ≠ 1) :
    ∃ other ∈ exit.terminal.val, other ≠ exit.atom.who := by
  have hcardPos : 0 < exit.terminal.val.card :=
    Finset.card_pos.mpr exit.terminal.property
  have hcardTwo : 1 < exit.terminal.val.card := by omega
  exact Finset.exists_mem_ne hcardTwo exit.atom.who

/-- A selected distinct member of a nonsingleton premark coalition. -/
noncomputable def otherOfNonsingleton
    (hcard : exit.terminal.val.card ≠ 1) : Fin 4 :=
  Classical.choose (exit.exists_otherOfNonsingleton hcard)

theorem otherOfNonsingleton_mem
    (hcard : exit.terminal.val.card ≠ 1) :
    exit.otherOfNonsingleton hcard ∈ exit.terminal.val :=
  (Classical.choose_spec (exit.exists_otherOfNonsingleton hcard)).1

theorem otherOfNonsingleton_ne
    (hcard : exit.terminal.val.card ≠ 1) :
    exit.otherOfNonsingleton hcard ≠ exit.atom.who :=
  (Classical.choose_spec (exit.exists_otherOfNonsingleton hcard)).2

/-- The literal positive-stage-atom adapter at the prescribed resolution. -/
theorem adapter : QuittingStageAtomConcentratedPacketAdapter reward
    (data.premarkTargetProfile exit.atom) exit.terminal exit.packetOwner exit.atom.time
      (data.resolution R) where
  sourceTerminal_ne_owner := exit.terminal_ne_packetOwner
  resolution_pos := data.resolution_pos exit.R_pos
  resolution_le_sourceStageMass := exit.resolution_lt_stageMass.le

/-- The resulting generic recurrent concentrated packet. -/
def concentratedPacket : QuittingReprojectionConcentratedPacket reward
    exit.adapter.profiles exit.packetOwner exit.adapter.routedTerminal
      exit.adapter.cutoff exit.adapter.scale :=
  exit.adapter.packet

theorem resolution_eq : data.resolution R =
    rho * source.residual.witness.terminalGap / (128 * R) := by
  rfl

/-- In the singleton branch, the original premark mover is different from
the newly selected routing owner. -/
theorem atom_who_ne_packetOwner
    (hcard : exit.terminal.val.card = 1) :
    exit.atom.who ≠ exit.packetOwner := by
  intro heq
  apply exit.terminal_ne_packetOwner
  rw [← heq]
  obtain ⟨member, hterminal⟩ := Finset.card_eq_one.mp hcard
  have hwho : exit.atom.who = member := by
    simpa [hterminal] using exit.who_mem_terminal
  simpa [hwho] using hterminal

/-- The original singleton member survives either endpoint-routing mode. -/
theorem atom_who_mem_routedTerminal
    (hcard : exit.terminal.val.card = 1) :
    exit.atom.who ∈ exit.adapter.routedTerminal.val := by
  rcases exit.adapter.routedTerminal_erase_or_insert with herase | hinsert
  · rw [herase.2]
    exact Finset.mem_erase.mpr
      ⟨exit.atom_who_ne_packetOwner hcard, exit.who_mem_terminal⟩
  · rw [hinsert.2]
    exact Finset.mem_insert_of_mem exit.who_mem_terminal

end PremarkExit

/-- At one cleared prefix, either a high-survival host already supports the
historical packet, a new coordinate is genuinely paid to clear, or a
profitable premark atom supports a fresh packet. -/
theorem nonempty_hostExit_or_paidClear_or_premarkExit
    (R : ℝ) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (cleared : Finset (Fin 4)) :
    Nonempty (data.HostExit R cleared) ∨
      Nonempty (data.PaidClear R cleared) ∨
        Nonempty (data.PremarkExit R cleared) := by
  by_cases hhost : ∃ host,
      data.eta R ≤ data.opponentSurvival cleared host
  · obtain ⟨host, hsurvival⟩ := hhost
    exact Or.inl ⟨{
      R_pos := hR
      host := host
      hostSurvival := hsurvival
    }⟩
  · have hlow : ∀ who,
        quittingLiteralRootStackOpponentSurvival
            (quittingLiteralRootStackClear data.roots cleared) who <
          source.residual.witness.terminalGap / (16 * R) := by
      intro who
      exact lt_of_not_ge (fun hge => hhost ⟨who, hge⟩)
    rcases quittingFinitePrefix_paidClear_or_premarkAtom reward
        (quittingLiteralRootStackClear data.roots cleared) data.baseProfile
        source.residual.witness.terminalGap R
        source.residual.witness.terminalGap_pos hR hreward
        source.residual.witness.terminalExploitability hlow with
      hpaid | hpremark
    · right
      left
      obtain ⟨paid⟩ := hpaid
      have hnotmem : paid.who ∉ cleared := by
        intro hmem
        have hgain := paid.gain
        rw [data.passProfile_eq_insert cleared paid.who,
          Finset.insert_eq_of_mem hmem, ← data.profile_eq_graft cleared]
          at hgain
        linarith [source.residual.witness.terminalGap_pos]
      exact ⟨{
        R_pos := hR
        paid := paid
        who_not_mem := hnotmem
      }⟩
    · right
      right
      obtain ⟨atom⟩ := hpremark
      have hroot : quittingProfileLiveRoot reward
          (data.premarkTargetProfile atom) atom.time atom.who = PMF.pure true := by
        unfold premarkTargetProfile
        rw [quittingProfileLiveRoot_literalOneDateProfile]
        simp
      obtain ⟨terminal, hmem, hmass⟩ :=
        exists_finFourCoalition_containing_of_pureQuit_mass_ge_one_eighth
          (quittingProfileLiveRoot reward (data.premarkTargetProfile atom)
            atom.time) atom.who hroot
      exact ⟨{
        R_pos := hR
        reward_abs_le := hreward
        atom := atom
        terminal := terminal
        who_mem_terminal := hmem
        rootMass := hmass
      }⟩

/-- The exploitability threshold `eta = gamma / (16 R)` is at most `1 / 8`
under the same reward bound used by the finite timing argument. -/
theorem eta_le_one_eighth
    (R : ℝ) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    data.eta R ≤ 1 / 8 := by
  have hgap := @terminalExploitabilityGap_le_two_mul_bound (Fin 4) _ _ reward
    source.residual.witness.terminalGap R hreward
      source.residual.witness.terminalExploitability
  unfold eta
  have hpositive : 0 < 16 * R := mul_pos (by norm_num) hR
  apply (div_le_iff₀ hpositive).2
  nlinarith

theorem eta_le_one
    (R : ℝ) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    data.eta R ≤ 1 :=
  (data.eta_le_one_eighth R hR hreward).trans (by norm_num)

/-- Clearing all four coordinates makes every deleted-player survival
literally one. -/
theorem opponentSurvival_univ (who : Fin 4) :
    data.opponentSurvival Finset.univ who = 1 := by
  unfold opponentSurvival
  rw [quittingLiteralRootStackClear_univ]
  have hroot : quittingRootOpponentContinueMass
      (fun _who : Fin 4 => PMF.pure false) who = 1 := by
    unfold quittingRootOpponentContinueMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    simp
  induction data.roots with
  | nil => simp [quittingLiteralRootStackOpponentSurvival]
  | cons root roots ih =>
      simp only [List.map_cons, quittingLiteralRootStackOpponentSurvival,
        List.prod_cons, List.map_map]
      rw [hroot, one_mul]
      simpa [quittingLiteralRootStackOpponentSurvival, Function.comp_def] using ih

/-- A terminal finite-clock exit.  A nonsingleton premark keeps its literal
profile, mover, and coalition.  Only a singleton premark uses the distinct
outsider routing adapter. -/
inductive PacketExit (R : ℝ) (cleared : Finset (Fin 4)) : Type
  | host (exit : data.HostExit R cleared)
  | premarkNonsingleton (exit : data.PremarkExit R cleared)
      (terminal_card_ne_one : exit.terminal.val.card ≠ 1)
  | premarkSingleton (exit : data.PremarkExit R cleared)
      (terminal_card_eq_one : exit.terminal.val.card = 1)

/-- A finite clearing derivation.  Every paid constructor inserts a genuinely
new player, while every leaf carries an actual generic concentrated packet. -/
inductive ClearingResult
    (data : FinFourFullyScreenedForcedPairPrefix packet)
    (R : ℝ) : Finset (Fin 4) → Type
  | done {cleared : Finset (Fin 4)} (exit : data.PacketExit R cleared) :
      ClearingResult data R cleared
  | paid {cleared : Finset (Fin 4)} (edge : data.PaidClear R cleared)
      (next : ClearingResult data R (insert edge.paid.who cleared)) :
      ClearingResult data R cleared

namespace ClearingResult

variable {data : FinFourFullyScreenedForcedPairPrefix packet}
  {R : ℝ}

/-- The number of genuinely paid clearings before the packet leaf. -/
def paidLength {cleared : Finset (Fin 4)} :
    data.ClearingResult R cleared → ℕ
  | .done _ => 0
  | .paid _ next => next.paidLength + 1

/-- Ordered labels of the genuinely paid coordinate clears. -/
def paidPlayers {cleared : Finset (Fin 4)} :
    data.ClearingResult R cleared → List (Fin 4)
  | .done _ => []
  | .paid edge next => edge.paid.who :: next.paidPlayers

@[simp] theorem paidPlayers_length {cleared : Finset (Fin 4)}
    (result : data.ClearingResult R cleared) :
    result.paidPlayers.length = result.paidLength := by
  induction result with
  | done exit => simp [paidPlayers, paidLength]
  | paid edge next ih => simp [paidPlayers, paidLength, ih]

/-- The complete typed ledger of genuinely paid coordinate clears. -/
def paidLedger {cleared : Finset (Fin 4)} :
    data.ClearingResult R cleared → List (data.PaidClearLedgerEntry R)
  | .done _ => []
  | .paid edge next =>
      ({ cleared := _, edge := edge } : data.PaidClearLedgerEntry R) ::
        next.paidLedger

@[simp] theorem paidLedger_length {cleared : Finset (Fin 4)}
    (result : data.ClearingResult R cleared) :
    result.paidLedger.length = result.paidLength := by
  induction result with
  | done exit => simp [paidLedger, paidLength]
  | paid edge next ih => simp [paidLedger, paidLength, ih]

/-- The final cleared set and its packet-producing leaf. -/
def terminalExit {cleared : Finset (Fin 4)} : data.ClearingResult R cleared →
    Σ finalCleared, data.PacketExit R finalCleared
  | .done exit => ⟨cleared, exit⟩
  | .paid _ next => next.terminalExit

/-- At most the uncleared Fin4 coordinates can be paid. -/
theorem paidLength_le {cleared : Finset (Fin 4)}
    (result : data.ClearingResult R cleared) :
    result.paidLength ≤ 4 - cleared.card := by
  induction result with
  | done exit => simp [paidLength]
  | @paid cleared edge next ih =>
      rw [paidLength]
      rw [Finset.card_insert_of_notMem edge.who_not_mem] at ih
      have hcard : (insert edge.paid.who cleared).card ≤ 4 := by
        simpa using Finset.card_le_card
          (Finset.subset_univ (insert edge.paid.who cleared))
      rw [Finset.card_insert_of_notMem edge.who_not_mem] at hcard
      omega

end ClearingResult

namespace PacketExit

variable {data : FinFourFullyScreenedForcedPairPrefix packet}
  {R : ℝ} {cleared : Finset (Fin 4)}

/-- The actual profile sequence retained by either terminal leaf. -/
def profiles : data.PacketExit R cleared →
    ℕ → (quittingGame reward).BehaviorProfile
  | .host exit => exit.constantSource.profiles
  | .premarkNonsingleton exit _ => exit.directConstantSource.profiles
  | .premarkSingleton exit _ => exit.adapter.profiles

/-- The marked defect-free packet coordinate. -/
def owner : data.PacketExit R cleared → Fin 4
  | .host exit => exit.constantSource.owner
  | .premarkNonsingleton exit _ => exit.directConstantSource.owner
  | .premarkSingleton exit _ => exit.packetOwner

/-- The literal terminal routed by the packet. -/
def terminal : data.PacketExit R cleared →
    {S : Finset (Fin 4) // S.Nonempty}
  | .host exit => exit.constantSource.terminal
  | .premarkNonsingleton exit _ => exit.directConstantSource.terminal
  | .premarkSingleton exit _ => exit.adapter.routedTerminal

/-- The packet cutoff sequence. -/
def cutoff : data.PacketExit R cleared → ℕ → ℕ
  | .host exit => exit.constantSource.cutoff
  | .premarkNonsingleton exit _ => exit.directConstantSource.cutoff
  | .premarkSingleton exit _ => exit.adapter.cutoff

/-- The positive vanishing packet scale. -/
def scale : data.PacketExit R cleared → ℕ → ℝ
  | .host exit => exit.constantSource.scale
  | .premarkNonsingleton exit _ => exit.directConstantSource.scale
  | .premarkSingleton exit _ => exit.adapter.scale

/-- Both finite-clock terminal mechanisms expose the same generic
concentrated-packet interface. -/
def concentratedPacket (exit : data.PacketExit R cleared) :
    QuittingReprojectionConcentratedPacket reward exit.profiles exit.owner
      exit.terminal exit.cutoff exit.scale := by
  cases exit with
  | host host => exact host.concentratedPacket
  | premarkNonsingleton premark _ => exact premark.directConcentratedPacket
  | premarkSingleton premark _ => exact premark.concentratedPacket

theorem resolution_eq (exit : data.PacketExit R cleared) :
    exit.concentratedPacket.resolution =
      rho * source.residual.witness.terminalGap / (128 * R) := by
  cases exit with
  | host host => exact host.resolution_eq
  | premarkNonsingleton premark _ => rfl
  | premarkSingleton premark _ => rfl

/-- A fixed terminal member distinct from the packet owner.  In the host
branch it is the original singleton owner; in a nonsingleton premark it is a
second member of the unchanged coalition; in a singleton premark it is the
original atom mover retained through outsider routing. -/
noncomputable def other : data.PacketExit R cleared → Fin 4
  | .host _ => returnSource.producer.owner
  | .premarkNonsingleton exit hcard => exit.otherOfNonsingleton hcard
  | .premarkSingleton exit _ => exit.atom.who

theorem other_ne_owner (exit : data.PacketExit R cleared) :
    exit.other ≠ exit.owner := by
  cases exit with
  | host host =>
      change returnSource.producer.owner ≠
        data.selection.family.markedOwner
      rw [data.selection.markedOwner_eq]
      exact returnSource.forcedOwner_ne_owner.symm
  | premarkNonsingleton premark hcard =>
      exact premark.otherOfNonsingleton_ne hcard
  | premarkSingleton premark hcard =>
      exact premark.atom_who_ne_packetOwner hcard

theorem other_mem_terminal (exit : data.PacketExit R cleared) :
    exit.other ∈ exit.terminal.val := by
  cases exit with
  | host host =>
      change returnSource.producer.owner ∈
        data.selection.family.terminal.val
      rw [data.selection.terminal_val]
      simp
  | premarkNonsingleton premark hcard =>
      exact premark.otherOfNonsingleton_mem hcard
  | premarkSingleton premark hcard =>
      exact premark.atom_who_mem_routedTerminal hcard

theorem scale_pos (exit : data.PacketExit R cleared) (rank : ℕ) :
    0 < exit.scale rank := by
  cases exit with
  | host host => exact host.constantSource.scale_pos rank
  | premarkNonsingleton premark _ =>
      exact premark.directConstantSource.scale_pos rank
  | premarkSingleton premark _ => exact premark.adapter.scale_pos rank

theorem scale_tendsto_zero (exit : data.PacketExit R cleared) :
    Tendsto exit.scale atTop (nhds 0) := by
  cases exit with
  | host host => exact host.constantSource.scale_tendsto_zero
  | premarkNonsingleton premark _ =>
      exact premark.directConstantSource.scale_tendsto_zero
  | premarkSingleton premark _ => exact premark.adapter.scale_tendsto_zero

/-- Finite code of the terminal clearing mechanism: host, direct
nonsingleton premark, or outsider-routed singleton premark. -/
def exitMode : data.PacketExit R cleared → Fin 3
  | .host _ => 0
  | .premarkNonsingleton _ _ => 1
  | .premarkSingleton _ _ => 2

/-- The profitable premark mover, with a fixed filler in the host branch. -/
def premarkMover : data.PacketExit R cleared → Fin 4
  | .host _ => 0
  | .premarkNonsingleton exit _ => exit.atom.who
  | .premarkSingleton exit _ => exit.atom.who

/-- The original pigeonholed premark coalition before any singleton outsider
routing, with the retained pair as a fixed filler in the host branch. -/
def premarkSourceTerminal : data.PacketExit R cleared → Finset (Fin 4)
  | .host _ => data.family.terminal.val
  | .premarkNonsingleton exit _ => exit.terminal.val
  | .premarkSingleton exit _ => exit.terminal.val

/-- Exact existing downstream consumer output.  The strategic-singleton arm
and the collision-minimum residual both retain this leaf's literal packet;
neither arm is discharged in this module. -/
def ConsumerResult (exit : data.PacketExit R cleared) : Prop :=
  HasQuittingConcentratedSingletonStrategicDispatch source.residual.witness
      exit.concentratedPacket exit.other ∨
    Nonempty (QuittingConcentratedCollisionMinimumResidual reward
      source.point.1 exit.owner exit.terminal exit.concentratedPacket)

theorem consumerResult (exit : data.PacketExit R cleared) :
    exit.ConsumerResult :=
  source.residual.witness
    |>.concentratedPacket_singletonStrategic_or_collisionMinimumResidual
      source.point.1 exit.concentratedPacket exit.other exit.other_ne_owner
      exit.other_mem_terminal source.semantic_mem source.minimum
      source.minimumDebt_pos exit.scale_pos exit.scale_tendsto_zero

end PacketExit

/-- Repeatedly apply the literal one-step dispatch.  The recursion is
well-founded because a paid step inserts a player not previously cleared; at
the full set, player `0` is automatically a high-survival host. -/
theorem nonempty_clearingResult
    (data : FinFourFullyScreenedForcedPairPrefix packet)
    (R : ℝ) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (cleared : Finset (Fin 4)) :
    Nonempty (data.ClearingResult R cleared) := by
  classical
  by_cases hfull : cleared = Finset.univ
  · subst cleared
    refine ⟨ClearingResult.done (PacketExit.host {
      R_pos := hR
      host := 0
      hostSurvival := ?_
    })⟩
    rw [data.opponentSurvival_univ]
    exact data.eta_le_one R hR hreward
  · rcases data.nonempty_hostExit_or_paidClear_or_premarkExit
        R hR hreward cleared with hhost | hpaid | hpremark
    · obtain ⟨exit⟩ := hhost
      exact ⟨ClearingResult.done (PacketExit.host exit)⟩
    · obtain ⟨edge⟩ := hpaid
      obtain ⟨next⟩ := nonempty_clearingResult data R hR hreward
        (insert edge.paid.who cleared)
      exact ⟨ClearingResult.paid edge next⟩
    · obtain ⟨exit⟩ := hpremark
      by_cases hcard : exit.terminal.val.card = 1
      · exact ⟨ClearingResult.done (PacketExit.premarkSingleton exit hcard)⟩
      · exact ⟨ClearingResult.done
          (PacketExit.premarkNonsingleton exit hcard)⟩
termination_by 4 - cleared.card
decreasing_by
  rw [Finset.card_insert_of_notMem edge.who_not_mem]
  have hcard : cleared.card ≤ 4 := by
    simpa using Finset.card_le_card (Finset.subset_univ cleared)
  have hlt : cleared.card < 4 := by
    by_contra hnot
    have heq : cleared.card = 4 := by omega
    exact hfull (Finset.eq_univ_of_card cleared (by simpa using heq))
  omega

/-- One provenance-rich finite clearing from the empty set.  Its terminal
leaf retains either the old paid forced-pair host or the new profitable
premark atom, and hence a literal generic concentrated packet. -/
structure FullyScreenedClearingPacketResult (R : ℝ) where
  clearing : data.ClearingResult R ∅

namespace FullyScreenedClearingPacketResult

variable {data : FinFourFullyScreenedForcedPairPrefix packet} {R : ℝ}
  (result : data.FullyScreenedClearingPacketResult R)

/-- The terminal cleared set and exact packet mechanism. -/
def terminalExit : Σ cleared, data.PacketExit R cleared :=
  result.clearing.terminalExit

/-- Every paid modification, in chronological order, with exact scaling and
debt identities available from `PaidClearLedgerEntry`. -/
def paidLedger : List (data.PaidClearLedgerEntry R) :=
  result.clearing.paidLedger

def profiles : ℕ → (quittingGame reward).BehaviorProfile :=
  result.terminalExit.2.profiles

def owner : Fin 4 := result.terminalExit.2.owner

def terminal : {S : Finset (Fin 4) // S.Nonempty} :=
  result.terminalExit.2.terminal

def cutoff : ℕ → ℕ := result.terminalExit.2.cutoff

def scale : ℕ → ℝ := result.terminalExit.2.scale

/-- A retained member of the terminal distinct from the selected packet
owner, with branch-specific provenance available in `terminalExit`. -/
noncomputable def other : Fin 4 := result.terminalExit.2.other

/-- The exact concentrated packet produced after no more than four paid
coordinate clears. -/
def concentratedPacket : QuittingReprojectionConcentratedPacket reward
    result.profiles result.owner result.terminal result.cutoff result.scale :=
  result.terminalExit.2.concentratedPacket

theorem paidLength_le_four : result.clearing.paidLength ≤ 4 := by
  have hbound := result.clearing.paidLength_le
  simpa using hbound

theorem paidLedger_length_le_four : result.paidLedger.length ≤ 4 := by
  rw [paidLedger, result.clearing.paidLedger_length]
  exact result.paidLength_le_four

theorem resolution_eq : result.concentratedPacket.resolution =
    rho * source.residual.witness.terminalGap / (128 * R) :=
  result.terminalExit.2.resolution_eq

theorem other_ne_owner : result.other ≠ result.owner :=
  result.terminalExit.2.other_ne_owner

theorem other_mem_terminal : result.other ∈ result.terminal.val :=
  result.terminalExit.2.other_mem_terminal

/-- Literal strategic-singleton-or-collision-minimum consumer result for the
produced packet.  This does not consume either output arm. -/
theorem consumerResult :
    HasQuittingConcentratedSingletonStrategicDispatch source.residual.witness
        result.concentratedPacket result.other ∨
      Nonempty (QuittingConcentratedCollisionMinimumResidual reward
        source.point.1 result.owner result.terminal result.concentratedPacket) :=
  result.terminalExit.2.consumerResult

/-- Finite mechanism tag retaining the ordered paid labels and terminal exit
provenance.  This is descriptive only; it forgets all quantitative profiles,
which remain stored in `clearing`. -/
def mechanism : FinFourFiniteClockClearingMechanism where
  paidLength := ⟨result.clearing.paidLength,
    Nat.lt_succ_iff.mpr result.paidLength_le_four⟩
  paidPlayer := fun index => result.clearing.paidPlayers.getD index 0
  exitMode := result.terminalExit.2.exitMode
  packetOwner := result.owner
  packetTerminal := result.terminal.val
  premarkMover := result.terminalExit.2.premarkMover
  premarkSourceTerminal := result.terminalExit.2.premarkSourceTerminal

@[simp] theorem mechanism_paidLength :
    result.mechanism.paidLength.val = result.clearing.paidLength := rfl

theorem mechanism_paidPlayer_eq_getD (index : Fin 4) :
    result.mechanism.paidPlayer index =
      result.clearing.paidPlayers.getD index 0 := rfl

end FullyScreenedClearingPacketResult

/-- Actual Fin4 source-indexed producer: one selected normalized return row
and one arbitrary finite root word yield a concentrated packet after at most
four paid coordinate clears. -/
theorem nonempty_fullyScreenedClearingPacketResult
    (data : FinFourFullyScreenedForcedPairPrefix packet)
    (R : ℝ) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    Nonempty (data.FullyScreenedClearingPacketResult R) := by
  obtain ⟨clearing⟩ := data.nonempty_clearingResult R hR hreward ∅
  exact ⟨⟨clearing⟩⟩

end FinFourFullyScreenedForcedPairPrefix

/-! ## Adapter from the actual fully screened Zeno source -/

namespace FinFourActualZenoDeletedSurvivalSource

variable
  {data : FinFourNormalizedInertVanishingDensityBoundary packet}
  (zeno : FinFourActualZenoDeletedSurvivalSource data)

/-- One actual arbitrary-word row of the fixed Zeno selection, presented in
the exact input format of finite clock clearing.  The base chronology remains
inside the immutable selected family; only `newWord rank` can be cleared. -/
def clearingPrefix (rank : ℕ) :
    FinFourFullyScreenedForcedPairPrefix packet where
  selection := data.selection
  rank := zeno.originRank rank
  roots := zeno.newWord rank

@[simp] theorem clearingPrefix_baseProfile (rank : ℕ) :
    (zeno.clearingPrefix rank).baseProfile = zeno.baseProfile rank := rfl

@[simp] theorem clearingPrefix_baseSourceProfile (rank : ℕ) :
    (zeno.clearingPrefix rank).baseSourceProfile =
      zeno.baseSourceProfile rank := rfl

@[simp] theorem clearingPrefix_profile_empty (rank : ℕ) :
    (zeno.clearingPrefix rank).profile ∅ = zeno.profile rank := by
  unfold FinFourFullyScreenedForcedPairPrefix.profile
  rw [quittingLiteralRootStackClear_empty]
  rfl

@[simp] theorem clearingPrefix_sourceProfile_empty (rank : ℕ) :
    (zeno.clearingPrefix rank).sourceProfile ∅ = zeno.sourceProfile rank := by
  unfold FinFourFullyScreenedForcedPairPrefix.sourceProfile
  rw [quittingLiteralRootStackClear_empty]
  rfl

@[simp] theorem clearingPrefix_mark_empty (rank : ℕ) :
    (zeno.clearingPrefix rank).mark ∅ = zeno.mark rank := by
  unfold FinFourFullyScreenedForcedPairPrefix.mark
  rw [quittingLiteralRootStackClear_empty]
  rfl

@[simp] theorem clearingPrefix_opponentSurvival_empty
    (rank : ℕ) (who : Fin 4) :
    (zeno.clearingPrefix rank).opponentSurvival ∅ who =
      quittingLiteralRootStackOpponentSurvival (zeno.newWord rank) who := by
  unfold FinFourFullyScreenedForcedPairPrefix.opponentSurvival
  rw [quittingLiteralRootStackClear_empty]
  rfl

/-- Termwise finite-clearing output after discarding the finite initial part
needed to enter the low-prefix-survival branch.  The shifted Zeno indices are
a strict subsequence; no cofinality of the stored source chronology ranks is
asserted. -/
structure FullyScreenedClearingFamily
    (R : ℝ) where
  startRank : ℕ
  initiallyLow : ∀ rank who,
    (zeno.clearingPrefix (startRank + rank)).opponentSurvival ∅ who <
      (zeno.clearingPrefix (startRank + rank)).eta R
  clearing : ∀ rank,
    (zeno.clearingPrefix (startRank + rank)).FullyScreenedClearingPacketResult R

namespace FullyScreenedClearingFamily

variable {zeno : FinFourActualZenoDeletedSurvivalSource data}
  {R : ℝ}
  (family : zeno.FullyScreenedClearingFamily R)

/-- The actual Zeno-row subsequence retained by the clearing family. -/
def zenoRank (rank : ℕ) : ℕ := family.startRank + rank

theorem zenoRank_strictMono : StrictMono family.zenoRank := by
  apply strictMono_nat_of_lt_succ
  intro rank
  simp [zenoRank]

/-- One strict refinement on which the entire finite clearing mechanism is
fixed: paid length, ordered paid labels, exit kind, packet owner and terminal,
and the original premark mover/coalition in the atom branches. -/
structure FixedMechanismSubsequence where
  mechanism : FinFourFiniteClockClearingMechanism
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  mechanism_eq : ∀ rank,
    (family.clearing (subsequence rank)).mechanism = mechanism

/-- Finite pigeonhole on the provenance-only mechanism tag.  Quantitative
profiles and calendar dates continue to vary along the retained strict
subsequence. -/
theorem nonempty_fixedMechanismSubsequence :
    Nonempty family.FixedMechanismSubsequence := by
  let label : ℕ → FinFourFiniteClockClearingMechanism := fun rank =>
    (family.clearing rank).mechanism
  obtain ⟨fixed, hfixedInfinite⟩ := Finite.exists_infinite_fiber label
  have hfrequent : ∃ᶠ rank in atTop, label rank = fixed := by
    rw [Nat.frequently_atTop_iff_infinite]
    have hinfinite : (label ⁻¹' ({fixed} : Set
        FinFourFiniteClockClearingMechanism)).Infinite :=
      Set.infinite_coe_iff.mp hfixedInfinite
    convert hinfinite using 1
    ext rank
    simp
  obtain ⟨subsequence, hsubsequence, hfixed⟩ :=
    extraction_of_frequently_atTop hfrequent
  exact ⟨{
    mechanism := fixed
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    mechanism_eq := hfixed
  }⟩

theorem FixedMechanismSubsequence.zenoRank_strictMono
    (fixed : family.FixedMechanismSubsequence) :
    StrictMono fun rank => family.zenoRank (fixed.subsequence rank) := by
  simpa [Function.comp_def] using
    family.zenoRank_strictMono.comp fixed.subsequence_strictMono

/-- Every selected row carries the exact source-indexed clearing packet and
its already composed strategic-singleton-or-collision-minimum output. -/
theorem consumerResult (rank : ℕ) :
    HasQuittingConcentratedSingletonStrategicDispatch source.residual.witness
        (family.clearing rank).concentratedPacket
          (family.clearing rank).other ∨
      Nonempty (QuittingConcentratedCollisionMinimumResidual reward
        source.point.1 (family.clearing rank).owner
          (family.clearing rank).terminal
            (family.clearing rank).concentratedPacket) :=
  (family.clearing rank).consumerResult

theorem resolution_eq (rank : ℕ) :
    (family.clearing rank).concentratedPacket.resolution =
      rho * source.residual.witness.terminalGap / (128 * R) :=
  (family.clearing rank).resolution_eq

theorem FixedMechanismSubsequence.consumerResult
    (fixed : family.FixedMechanismSubsequence) (rank : ℕ) :
    HasQuittingConcentratedSingletonStrategicDispatch source.residual.witness
        (family.clearing (fixed.subsequence rank)).concentratedPacket
          (family.clearing (fixed.subsequence rank)).other ∨
      Nonempty (QuittingConcentratedCollisionMinimumResidual reward
        source.point.1 (family.clearing (fixed.subsequence rank)).owner
          (family.clearing (fixed.subsequence rank)).terminal
            (family.clearing (fixed.subsequence rank)).concentratedPacket) :=
  family.consumerResult (fixed.subsequence rank)

end FullyScreenedClearingFamily

/-- Section-6 composition from actual full-screening data.  Combined deleted
survival factors through the arbitrary word and the immutable base word in
`ActualZenoDeletedSurvivalSource`; the base factor has the literal `rho`
floor.  Hence, after one finite shift, every actual new word enters the low
prefix branch and is cleared termwise. -/
theorem nonempty_fullyScreenedClearingFamily
    (hscreened : IsFinFourActualZenoFullyScreened zeno)
    (R : ℝ) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    Nonempty (zeno.FullyScreenedClearingFamily R) := by
  classical
  have hlow := zeno.eventually_newWord_opponentSurvival_lt hscreened
    ((zeno.clearingPrefix 0).eta R)
      ((zeno.clearingPrefix 0).eta_pos hR)
  obtain ⟨startRank, hstartRank⟩ := Filter.eventually_atTop.mp hlow
  refine ⟨{
    startRank := startRank
    initiallyLow := ?_
    clearing := ?_
  }⟩
  · intro rank who
    rw [zeno.clearingPrefix_opponentSurvival_empty]
    exact hstartRank (startRank + rank) (by omega) who
  · intro rank
    exact Classical.choice
      ((zeno.clearingPrefix (startRank + rank))
        |>.nonempty_fullyScreenedClearingPacketResult R hR hreward)

end FinFourActualZenoDeletedSurvivalSource

namespace FinFourNormalizedInertVanishingDensityBoundary

/-- The zero-density boundary itself supplies one actual raw Zeno source.
For that source, either full screening is false, or finite clearing produces
the source-attached concentrated-packet family after a strict finite shift.
This is the honest source-level composition; no compatible renewal chain is
assumed or produced. -/
theorem nonempty_actualZeno_notFullyScreened_or_clearingFamily
    (data : FinFourNormalizedInertVanishingDensityBoundary packet)
    (hzero : data.boundary.limit.markedMass = 0)
    (R : ℝ) (hR : 0 < R)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R) :
    ∃ zeno : FinFourActualZenoDeletedSurvivalSource data,
      ¬ IsFinFourActualZenoFullyScreened zeno ∨
        Nonempty (zeno.FullyScreenedClearingFamily R) := by
  obtain ⟨zeno⟩ := data.nonempty_actualZenoDeletedSurvivalSource hzero
  refine ⟨zeno, ?_⟩
  by_cases hscreened : IsFinFourActualZenoFullyScreened zeno
  · exact Or.inr
      (zeno.nonempty_fullyScreenedClearingFamily hscreened R hR hreward)
  · exact Or.inl hscreened

end FinFourNormalizedInertVanishingDensityBoundary

end GameTheory
