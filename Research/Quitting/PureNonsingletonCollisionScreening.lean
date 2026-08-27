/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.SameStageEndpointMonodromy
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticReachedRowDebtLocalization

/-!
# Pure nonsingleton collision screening

At a pure nonsingleton quitting root, every player has a different sure
quitter.  The complete continuation is therefore screened out of that
player's unrestricted semantic debt: current debt equals the literal
one-stage endpoint defect.  A positive global minimum of total semantic debt
then selects an actual best-endpoint update with gain at least the reached
live mass times the minimum debt divided by the number of players.

The game-facing edge extends the existing same-stage endpoint edge.  The
finite orbit remains the generic `DispatchedOrbit`; no quantitative game data
is added to `MathUE`.
-/

noncomputable section

namespace GameTheory

open MathUE.FiniteBooleanEndpointOrbit

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- At a pure nonsingleton row, current total semantic debt is exactly the
sum of the root's endpoint defects.  No assumption on the continuation is
needed. -/
theorem quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (source : QuittingNonsingletonCoalition iota) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (quittingLiteralPureRootCoalitionProfile reward profile stage source)
            stage)) =
      ∑ who, quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (quittingLiteralPureRootCoalitionProfile reward profile stage source)
            (stage + 1))).1
        (quittingProfileLiveRoot reward
          (quittingLiteralPureRootCoalitionProfile reward profile stage source)
          stage) who := by
  unfold quittingTerminalSemanticDebtSum
  apply Finset.sum_congr rfl
  intro who _hwho
  obtain ⟨first, hfirst, second, hsecond, hne⟩ :=
    Finset.one_lt_card.mp source.2
  let observer := if first = who then second else first
  have hobserverMem : observer ∈ source.1 := by
    dsimp only [observer]
    split_ifs
    · exact hsecond
    · exact hfirst
  have hobserverNe : who ≠ observer := by
    dsimp only [observer]
    split_ifs with hfirstWho
    · intro hwhoSecond
      apply hne
      exact hfirstWho.trans hwhoSecond
    · exact fun hwhoFirst => hfirstWho hwhoFirst.symm
  rw [quittingTerminalSemanticPair_spine_eq_prefix]
  apply quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter
    reward _ _ observer who hobserverNe
  dsimp only [quittingLiteralPureRootCoalitionProfile]
  rw [quittingProfileLiveRoot_literalPureRootProfile_self]
  simp [quittingPureRootOfCoalition, quittingCoalitionAction, hobserverMem]

/-- A continuation-screened strict endpoint edge.  Its inherited edge keeps
the exact mover-debt subtraction and no-loss routed mass; the additional
field records the stronger pure-row gain floor. -/
structure QuittingPureNonsingletonScreenedEdge
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (minimum : QuittingTerminalSemanticPair iota)
    (lambda : ℝ) (source target : QuittingNonsingletonCoalition iota) where
  edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda
    source target
  gain_floor_live :
    quittingLiveMass reward profile stage *
          quittingTerminalSemanticDebtSum minimum /
          (Fintype.card iota : ℝ) ≤
      quittingSameStageCoalitionGain reward profile stage source
        edge.who edge.action

namespace QuittingPureNonsingletonScreenedEdge

variable
  {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
  {profile : (quittingGame reward).BehaviorProfile}
  {stage : ℕ} {minimum : QuittingTerminalSemanticPair iota}
  {lambda : ℝ} {source target : QuittingNonsingletonCoalition iota}

/-- The screened edge changes coalition cardinality by exactly one. -/
theorem card_step
    (screened : QuittingPureNonsingletonScreenedEdge reward profile stage
      minimum lambda source target) :
    target.1.card + 1 = source.1.card ∨
      source.1.card + 1 = target.1.card := by
  rcases screened.edge.target_eq_singlePlayer_toggle with hdrop | hjoin
  · left
    rw [← hdrop.1, Finset.card_erase_of_mem hdrop.2.2]
    have hnonsingleton := source.2
    omega
  · right
    rw [← hjoin.1, Finset.card_insert_of_notMem hjoin.2.2]

/-- Screened strict edges cannot immediately reverse. -/
theorem not_reverse
    (first : QuittingPureNonsingletonScreenedEdge reward profile stage
      minimum lambda source target)
    (second : QuittingPureNonsingletonScreenedEdge reward profile stage
      minimum lambda target source) : False :=
  first.edge.not_reverse second.edge

/-- Once the selected scale is below the reached live mass, every screened
edge gains at least `lambda * D_* / card` at the literal pure source row. -/
theorem gain_floor
    (screened : QuittingPureNonsingletonScreenedEdge reward profile stage
      minimum lambda source target)
    (hlive : lambda ≤ quittingLiveMass reward profile stage)
    (hminimumDebt : 0 ≤ quittingTerminalSemanticDebtSum minimum) :
    lambda * quittingTerminalSemanticDebtSum minimum /
          (Fintype.card iota : ℝ) ≤
      quittingSameStageCoalitionGain reward profile stage source
        screened.edge.who screened.edge.action := by
  have hscaled := mul_le_mul_of_nonneg_right hlive hminimumDebt
  exact (div_le_div_of_nonneg_right hscaled (by positivity)).trans
    screened.gain_floor_live

end QuittingPureNonsingletonScreenedEdge

/-- The screened dispatch uses the existing mass-preserving singleton route
as its terminal predicate. -/
def QuittingPureNonsingletonScreenedDispatch
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (minimum : QuittingTerminalSemanticPair iota)
    (lambda : ℝ) (source : QuittingNonsingletonCoalition iota) : Prop :=
  QuittingSameStageSingletonRoute reward profile stage source ∨
    ∃ target, Nonempty
      (QuittingPureNonsingletonScreenedEdge reward profile stage minimum
        lambda source target)

/-- Every pure nonsingleton vertex supplies either the literal singleton
route or a screened strict endpoint edge. -/
theorem quittingPureNonsingleton_screenedDispatch
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (source : QuittingNonsingletonCoalition iota)
    (lambda : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hlive : lambda ≤ quittingLiveMass reward profile stage) :
    QuittingPureNonsingletonScreenedDispatch reward profile stage minimum
      lambda source := by
  let sourceProfile :=
    quittingLiteralPureRootCoalitionProfile reward profile stage source
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward sourceProfile stage)
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward sourceProfile (stage + 1))
  let root := quittingProfileLiveRoot reward sourceProfile stage
  have hcurrentCarrier : current ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have hdebtFloor : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum current :=
    hminimum current hcurrentCarrier
  have hsum : quittingTerminalSemanticDebtSum current =
      ∑ who, quittingRootCoordinateNashDefect reward tail.1 root who := by
    simpa only [sourceProfile, current, tail, root] using
      quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect
        reward profile stage source
  obtain ⟨who, _hwho, haverage⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul
      Finset.univ Finset.univ_nonempty
      (fun player => quittingRootCoordinateNashDefect reward tail.1 root player)
  have haverage' : (∑ player,
        quittingRootCoordinateNashDefect reward tail.1 root player) ≤
      (Fintype.card iota : ℝ) *
        quittingRootCoordinateNashDefect reward tail.1 root who := by
    simpa using haverage
  have hcardPos : 0 < (Fintype.card iota : ℝ) := by positivity
  have hdefectFloor : quittingTerminalSemanticDebtSum minimum /
        (Fintype.card iota : ℝ) ≤
      quittingRootCoordinateNashDefect reward tail.1 root who := by
    rw [div_le_iff₀ hcardPos]
    exact hdebtFloor.trans
      (hsum.trans_le (by simpa [mul_comm] using haverage'))
  let action := quittingRootBestEndpointAction reward tail.1 root who
  let targetProfile := quittingLiteralOneDateProfile reward sourceProfile who
    stage action
  let sourcePair := quittingTerminalSemanticPair reward sourceProfile
  let targetPair := quittingTerminalSemanticPair reward targetProfile
  let gain := quittingTerminalPayoff reward targetProfile who -
    quittingTerminalPayoff reward sourceProfile who
  let routed := quittingPureEndpointRoutedCoalition source.1 who action
  have hliveSource : quittingLiveMass reward sourceProfile stage =
      quittingLiveMass reward profile stage :=
    quittingLiveMass_literalPureRootProfile_eq reward profile stage _
  have hgainDebt := quittingLiteralSameStage_bestEndpoint_gain_and_debt
    reward sourceProfile who stage
  have hgain : gain = quittingLiveMass reward profile stage *
      quittingRootCoordinateNashDefect reward tail.1 root who := by
    simpa only [sourceProfile, tail, root, action, targetProfile, sourcePair,
      targetPair, gain, hliveSource] using hgainDebt.1
  have hliveNonneg := quittingLiveMass_nonneg reward profile stage
  have hgainFloor : quittingLiveMass reward profile stage *
        quittingTerminalSemanticDebtSum minimum /
          (Fintype.card iota : ℝ) ≤ gain := by
    rw [hgain, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hdefectFloor hliveNonneg
  have hgainPos : 0 < gain := by
    have hlivePos := hlambda.trans_le hlive
    have hfloorPos : 0 < quittingLiveMass reward profile stage *
          quittingTerminalSemanticDebtSum minimum /
            (Fintype.card iota : ℝ) :=
      div_pos (mul_pos hlivePos hminimumDebt) hcardPos
    exact hfloorPos.trans_le hgainFloor
  have hrouting := quittingStageCoalitionMass_le_stagePureEndpointRouted
    reward sourceProfile who stage
      (quittingTerminalOfNonsingletonCoalition source) action source.2
  obtain ⟨hrouted, hrouteMass⟩ := hrouting
  have hcardCases : routed.card = 1 ∨ 1 < routed.card := by
    have hpositive : 0 < routed.card := Finset.card_pos.mpr hrouted
    omega
  rcases hcardCases with hsingleton | hnonsingleton
  · left
    let singleton : {S : Finset iota // S.Nonempty} := ⟨routed, hrouted⟩
    refine ⟨who, action, singleton, ?_, rfl, ?_⟩
    · exact hsingleton
    · rw [quittingStageCoalitionMass_literalOneDateProfile_eq_canonical]
      simpa only [sourceProfile, targetProfile, singleton, routed,
        quittingTerminalOfNonsingletonCoalition] using hrouteMass
  · right
    let target : QuittingNonsingletonCoalition iota := ⟨routed, hnonsingleton⟩
    have htargetEq : target.1 = routed := rfl
    have hprofile : targetProfile =
        quittingLiteralPureRootCoalitionProfile reward profile stage target := by
      exact quittingLiteralPureRootCoalitionProfile_update_eq_routed
        reward profile stage source who action target htargetEq
    have hminimumNonneg := hminimumDebt.le
    have hbaseFloor : lambda * quittingTerminalSemanticDebtSum minimum /
          (2 * (Fintype.card iota : ℝ)) ≤ gain := by
      have hscale := mul_le_mul_of_nonneg_right hlive hminimumNonneg
      rw [div_le_iff₀ (mul_pos (by norm_num) hcardPos)]
      rw [div_le_iff₀ hcardPos] at hgainFloor
      nlinarith
    refine ⟨target, ⟨{
      edge := {
        who := who
        action := action
        action_eq_best := rfl
        target_eq_routed := htargetEq
        gain_eq_live_defect := by
          change gain = quittingLiveMass reward sourceProfile stage *
            quittingRootCoordinateNashDefect reward tail.1 root who
          rw [hliveSource]
          exact hgain
        gain_pos := by
          change 0 < gain
          exact hgainPos
        gain_floor := by
          change lambda * quittingTerminalSemanticDebtSum minimum /
              (2 * (Fintype.card iota : ℝ)) ≤ gain
          exact hbaseFloor
        target_mem := by
          rw [← hprofile]
          exact quittingTerminalSemanticPair_mem_carrier reward targetProfile
        mover_debt := by
          rw [← hprofile]
          change quittingTerminalSemanticDebt targetPair who =
            quittingTerminalSemanticDebt sourcePair who - gain
          exact hgainDebt.2
        stage_mass_le := by
          rw [← hprofile,
            quittingStageCoalitionMass_literalOneDateProfile_eq_canonical]
          simpa only [sourceProfile, targetProfile, target, routed,
            quittingTerminalOfNonsingletonCoalition] using hrouteMass
      }
      gain_floor_live := by
        change quittingLiveMass reward profile stage *
            quittingTerminalSemanticDebtSum minimum /
              (Fintype.card iota : ℝ) ≤ gain
        exact hgainFloor
    }⟩⟩

/-- Iterating the screened local dispatch yields either a first-terminal
stopped orbit with every preterminal edge certified, or the unchanged generic
closed-segment alternative. -/
theorem exists_pureNonsingletonScreened_terminalOrbit_or_closedSegment
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (start : QuittingNonsingletonCoalition iota)
    (lambda : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hlive : lambda ≤ quittingLiveMass reward profile stage) :
    Nonempty (DispatchedOrbit
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingPureNonsingletonScreenedEdge reward profile stage minimum
          lambda source target)) start) ∨
      Nonempty (DispatchedClosedSegment
        (QuittingSameStageSingletonRoute reward profile stage)
        (fun source target => Nonempty
          (QuittingPureNonsingletonScreenedEdge reward profile stage minimum
            lambda source target)) start) := by
  apply exists_dispatchedOrbit_terminal_or_closedSegment
  intro source
  exact quittingPureNonsingleton_screenedDispatch reward minimum profile stage
    source lambda hminimum hminimumDebt hlambda hlive

/-- Any first-terminal screened orbit contained in at most four effective
players has at most three profitable edges. -/
theorem pureNonsingletonScreenedOrbit_terminal_time_le_three
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {minimum : QuittingTerminalSemanticPair iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition iota}
    (trace : DispatchedOrbit
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingPureNonsingletonScreenedEdge reward profile stage minimum
          lambda source target)) start)
    (support : Finset iota)
    (hcontained : ∀ time : ℕ, time ≤ trace.terminal_time →
      (trace.orbit time).1 ⊆ support)
    (hsupport : support.card ≤ 4) :
    trace.terminal_time.val ≤ 3 := by
  apply trace.terminal_time_le_three_of_effectiveSupport_card_le_four
    support hcontained
  · exact quittingSameStageSingletonRoute_of_card_eq_two reward profile stage
  · intro source target hedge
    obtain ⟨screened⟩ := hedge
    exact screened.card_step
  · intro source target hfirst hsecond
    obtain ⟨first⟩ := hfirst
    obtain ⟨second⟩ := hsecond
    exact first.not_reverse second
  · exact hsupport

/-- The exact no-loss fields on the certified preterminal edges telescope
from the initial pure row to every vertex of a stopped screened orbit. -/
theorem pureNonsingletonScreenedOrbit_stageMass_zero_le
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {minimum : QuittingTerminalSemanticPair iota}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {lambda : ℝ}
    {start : QuittingNonsingletonCoalition iota}
    (trace : DispatchedOrbit
      (QuittingSameStageSingletonRoute reward profile stage)
      (fun source target => Nonempty
        (QuittingPureNonsingletonScreenedEdge reward profile stage minimum
          lambda source target)) start)
    (time : ℕ) (htime : time ≤ trace.terminal_time) :
    quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage
          (trace.orbit 0)) stage
        (quittingTerminalOfNonsingletonCoalition (trace.orbit 0)) ≤
      quittingStageCoalitionMass reward
        (quittingLiteralPureRootCoalitionProfile reward profile stage
          (trace.orbit time)) stage
        (quittingTerminalOfNonsingletonCoalition (trace.orbit time)) := by
  induction time with
  | zero => exact le_rfl
  | succ time ih =>
      have htimeBefore : time < trace.terminal_time := by omega
      have htimeLe : time ≤ trace.terminal_time := by omega
      obtain ⟨screened⟩ := trace.edge_before time htimeBefore
      exact (ih htimeLe).trans screened.edge.stage_mass_le

end GameTheory
