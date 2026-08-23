/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.AtomSequenceDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiteralSourceReturnNoGo
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticReachedRowDebtLocalization

/-!
# Target-row debt localization

Positive observer reward stores uniform mass at the rectangle target. If the
terminal contains the observer, the observer's pure-time strategy reaches a
sure-Quit row there, while its initial semantic debt vanishes. The same
reached-row conclusion also follows from the stronger marked-tail predicate
without using its stored cluster or escape/fiber alternative.

This consumer retains the actual profile sequence, stop times, terminal
coalition mass, and a uniform positive lower bound on one fixed player's
legal one-row gains.  It does not provide source re-entry or an exact
Nash--Bellman return.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- The literal target profile on which the reached-row certificate is
evaluated. -/
def quittingStoppingLawPositiveTargetReachedRowProfile
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (rank : Nat) : (quittingGame reward).BehaviorProfile :=
  Function.update
    (quittingStoppingLawRectangleTargetProfile packet rank) packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime rank))

/-- The canonical legal best-endpoint gain at a selected literal target row.
-/
def quittingStoppingLawPositiveTargetReachedRowGain
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (stop : Nat -> Nat) (other : iota) (rank : Nat) : Real :=
  let profile := quittingStoppingLawPositiveTargetReachedRowProfile
    packet rank
  let stage := stop rank
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  let action := quittingRootBestEndpointAction reward tail.1 root other
  let deviation := quittingStagePureEndpointBehaviorDeviation
    reward profile other stage action
  quittingTerminalPayoff reward
        (Function.update profile other deviation) other -
      quittingTerminalPayoff reward profile other

/-- The explicit gain floor delivered by reached-row localization. -/
def quittingStoppingLawPositiveTargetReachedRowGainFloor
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (lower : Real) : Real :=
  lower * quittingTerminalSemanticDebtSum frontier.base /
    (2 * ((Finset.univ.erase packet.observer).card : Real))

/-- A self-contained quantitative reached-row certificate for the
positive-target packet.  Along one strict subsequence, the same target
profiles have a uniformly reached sure-Quit row and one fixed non-observer's
canonical legal gain is bounded below by the displayed positive floor. -/
def HasQuittingStoppingLawPositiveTargetReachedRowLocalization
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (lower : Real) : Prop :=
  0 < lower ∧
    ∃ (stop : Nat -> Nat) (subseq : Nat -> Nat) (other : iota),
      StrictMono subseq ∧ other ≠ packet.observer ∧
      (∀ rank, packet.quitTime (subseq rank) = some (stop (subseq rank))) ∧
      (∀ rank, lower <= quittingStageCoalitionMass reward
        (quittingStoppingLawPositiveTargetReachedRowProfile packet
          (subseq rank)) (stop (subseq rank)) packet.terminal) ∧
      ∀ rank,
        quittingStoppingLawPositiveTargetReachedRowGainFloor packet lower <=
          quittingStoppingLawPositiveTargetReachedRowGain packet stop other
            (subseq rank)

/-- Literal source-return obstruction extracted from a positive reached-row
localization certificate.

The packet keeps the actual target profile, selected date, fixed player,
terminal label, positive terminal mass, and quantitative gain floor at every
rank of the original strict subsequence.  Its `no_exact_return` field is a
no-go: it does not assert that a packet-preserving return exists. -/
structure QuittingStoppingLawPositiveTargetReachedRowLiteralNoGo
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (lower : Real) where
  lower_pos : 0 < lower
  stop : Nat -> Nat
  subseq : Nat -> Nat
  other : iota
  subseq_strictMono : StrictMono subseq
  other_ne : other ≠ packet.observer
  row : Nat -> QuittingLiteralPositiveActualRowPacket reward
  quit_time : ∀ rank,
    packet.quitTime (subseq rank) = some (stop (subseq rank))
  row_profile : ∀ rank, (row rank).profile =
    quittingStoppingLawPositiveTargetReachedRowProfile packet (subseq rank)
  row_stage : ∀ rank, (row rank).stage = stop (subseq rank)
  row_player : ∀ rank, (row rank).who = other
  row_terminal : ∀ rank, (row rank).terminal = packet.terminal
  mass_lower : ∀ rank, lower ≤ (row rank).mass
  gain_floor : ∀ rank,
    quittingStoppingLawPositiveTargetReachedRowGainFloor packet lower ≤
      quittingLiteralActualRowBestEndpointGain reward (row rank).profile
        (row rank).who (row rank).stage
  no_exact_return : ∀ rank,
    ¬ ∃ current tail : QuittingNashBellmanPoint iota,
      (row rank).IsLiteralNashBellmanEmbedding current tail

/-- The production reached-row certificate constructs the full literal
source-return no-go packet without changing its behavioral row or tail. -/
theorem HasQuittingStoppingLawPositiveTargetReachedRowLocalization.nonempty_literalNoGo
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {lower : Real}
    (certificate :
      HasQuittingStoppingLawPositiveTargetReachedRowLocalization packet lower) :
    Nonempty
      (QuittingStoppingLawPositiveTargetReachedRowLiteralNoGo packet lower) := by
  obtain ⟨hlower, stop, subseq, other, hsubseq, hother, htime, hmass,
      hgain⟩ := certificate
  let players := Finset.univ.erase packet.observer
  have hotherMem : other ∈ players :=
    Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩
  have hcardNat : 0 < players.card :=
    Finset.card_pos.mpr ⟨other, hotherMem⟩
  have hcard : 0 < (players.card : Real) := by
    exact_mod_cast hcardNat
  have hgainFloorPos : 0 <
      quittingStoppingLawPositiveTargetReachedRowGainFloor packet lower := by
    unfold quittingStoppingLawPositiveTargetReachedRowGainFloor
    exact div_pos (mul_pos hlower frontier.base_positive)
      (mul_pos (by norm_num) hcard)
  let actual : Nat -> (quittingGame reward).BehaviorProfile := fun rank =>
    quittingStoppingLawPositiveTargetReachedRowProfile packet (subseq rank)
  let stage : Nat -> Nat := fun rank => stop (subseq rank)
  have hgainFloor : ∀ rank,
      quittingStoppingLawPositiveTargetReachedRowGainFloor packet lower ≤
        quittingLiteralActualRowBestEndpointGain reward (actual rank) other
          (stage rank) := by
    intro rank
    simpa only [actual, stage,
      quittingStoppingLawPositiveTargetReachedRowGain,
      quittingLiteralActualRowBestEndpointGain,
      quittingLiteralActualRowTail, quittingLiteralActualRowRoot] using
        hgain rank
  have hgainPos : ∀ rank,
      0 < quittingLiteralActualRowBestEndpointGain reward (actual rank) other
        (stage rank) := fun rank => hgainFloorPos.trans_le (hgainFloor rank)
  let row : Nat -> QuittingLiteralPositiveActualRowPacket reward := fun rank =>
    { profile := actual rank
      stage := stage rank
      who := other
      terminal := packet.terminal
      mass := quittingStageCoalitionMass reward (actual rank) (stage rank)
        packet.terminal
      mass_eq := rfl
      mass_pos := hlower.trans_le (by
        simpa only [actual, stage] using hmass rank)
      gain_pos := hgainPos rank }
  refine ⟨⟨hlower, stop, subseq, other, hsubseq, hother, row, htime,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro rank
    rfl
  · intro rank
    rfl
  · intro rank
    rfl
  · intro rank
    rfl
  · intro rank
    simpa only [row, actual, stage] using hmass rank
  · intro rank
    simpa only [row] using hgainFloor rank
  · intro rank
    exact (row rank).not_exists_literalNashBellmanEmbedding

/-- Any approximate Nash repair on the exact root--tail fiber stored by the
proof-carrying row packet pays at least the certificate's uniform gain floor. -/
theorem QuittingStoppingLawPositiveTargetReachedRowLiteralNoGo.gainFloor_le_nashError
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {lower error : Real}
    (data : QuittingStoppingLawPositiveTargetReachedRowLiteralNoGo packet lower)
    (rank : Nat)
    (hnash : IsεQuittingRootNash reward
      (quittingLiteralActualRowTail reward (data.row rank).profile
        (data.row rank).stage).1 error
      (quittingLiteralActualRowRoot reward (data.row rank).profile
        (data.row rank).stage)) :
    quittingStoppingLawPositiveTargetReachedRowGainFloor packet lower ≤
      error :=
  (data.gain_floor rank).trans
    ((data.row rank).gain_le_nashError_of_literal_root_tail hnash)

/-- The localized positive-collision rows are literal positive-row packets,
so none admits an exact Nash--Bellman embedding on its unchanged root--tail
fiber.  The existential form is retained as a convenient projection of the
stronger proof-carrying packet above. -/
theorem positiveTargetReachedRowLocalization_no_packetPreservingExactSourceReturn
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : Real}
    (certificate : HasQuittingStoppingLawPositiveTargetReachedRowLocalization
      packet lower) :
    ∃ (stop : Nat -> Nat) (subseq : Nat -> Nat) (other : iota),
      StrictMono subseq ∧
      other ≠ packet.observer ∧
      ∀ rank,
        packet.quitTime (subseq rank) = some (stop (subseq rank)) ∧
          let actual := quittingStoppingLawPositiveTargetReachedRowProfile
            packet (subseq rank)
          ∃ row : QuittingLiteralPositiveActualRowPacket reward,
            row.profile = actual ∧
              row.stage = stop (subseq rank) ∧
              row.who = other ∧
              row.terminal = packet.terminal ∧
              lower ≤ row.mass ∧
              ¬ ∃ current tail : QuittingNashBellmanPoint iota,
                row.IsLiteralNashBellmanEmbedding current tail := by
  obtain ⟨data⟩ := certificate.nonempty_literalNoGo
  refine ⟨data.stop, data.subseq, data.other, data.subseq_strictMono,
    data.other_ne, ?_⟩
  intro rank
  refine ⟨data.quit_time rank, ?_⟩
  dsimp only
  exact ⟨data.row rank, data.row_profile rank, data.row_stage rank,
    data.row_player rank, data.row_terminal rank, data.mass_lower rank,
    data.no_exact_return rank⟩

/-- **Uniform same-fiber repair floor for the positive-collision arm.**
Along the fixed-player subsequence selected by actual-row localization, every
approximate Nash repair which reuses the literal root and continuation has
error bounded away from zero by a table-level constant.  This is an error
floor, not an existence theorem for a packet-preserving repair. -/
theorem positiveTargetReachedRowLocalization_sameFiberRepairErrorFloor
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : Real}
    (certificate : HasQuittingStoppingLawPositiveTargetReachedRowLocalization
      packet lower) :
    ∃ (stop : Nat -> Nat) (subseq : Nat -> Nat) (other : iota),
      StrictMono subseq ∧
      other ≠ packet.observer ∧
      ∀ rank (error : Real),
        let actual := quittingStoppingLawPositiveTargetReachedRowProfile
          packet (subseq rank)
        let tail := quittingLiteralActualRowTail reward actual
          (stop (subseq rank))
        let root := quittingLiteralActualRowRoot reward actual
          (stop (subseq rank))
        IsεQuittingRootNash reward tail.1 error root ->
          lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
              ((Finset.univ.erase packet.observer).card : Real) * error ∧
            lower * quittingTerminalSemanticDebtSum frontier.base /
                (2 * ((Finset.univ.erase packet.observer).card : Real)) ≤
              error := by
  obtain ⟨hlower, stop, subseq, other, hsubseq, hother, _htime, hmass,
      hgain⟩ := certificate
  refine ⟨stop, subseq, other, hsubseq, hother, ?_⟩
  intro rank error
  dsimp only
  let actual := quittingStoppingLawPositiveTargetReachedRowProfile
    packet (subseq rank)
  let stage := stop (subseq rank)
  let gain := quittingLiteralActualRowBestEndpointGain reward actual other stage
  let players := Finset.univ.erase packet.observer
  have hotherMem : other ∈ players :=
    Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩
  have hcardNat : 0 < players.card :=
    Finset.card_pos.mpr ⟨other, hotherMem⟩
  have hcard : 0 < (players.card : Real) := by
    exact_mod_cast hcardNat
  have hgainFloor :
      lower * quittingTerminalSemanticDebtSum frontier.base /
          (2 * (players.card : Real)) ≤ gain := by
    simpa only [actual, stage, players, gain,
      quittingStoppingLawPositiveTargetReachedRowGainFloor,
      quittingStoppingLawPositiveTargetReachedRowGain,
      quittingLiteralActualRowBestEndpointGain,
      quittingLiteralActualRowTail, quittingLiteralActualRowRoot] using
        hgain rank
  have hgainPos : 0 < gain := by
    have hdenom : 0 < 2 * (players.card : Real) :=
      mul_pos (by norm_num) hcard
    exact (div_pos (mul_pos hlower frontier.base_positive) hdenom).trans_le
      hgainFloor
  let row : QuittingLiteralPositiveActualRowPacket reward :=
    { profile := actual
      stage := stage
      who := other
      terminal := packet.terminal
      mass := quittingStageCoalitionMass reward actual stage packet.terminal
      mass_eq := rfl
      mass_pos := hlower.trans_le (by
        simpa only [actual, stage] using hmass rank)
      gain_pos := by simpa only [gain] using hgainPos }
  intro hnash
  have hgainLe : gain ≤ error := by
    simpa only [row, gain] using
      row.gain_le_nashError_of_literal_root_tail hnash
  have hdivided : lower * quittingTerminalSemanticDebtSum frontier.base /
        (2 * (players.card : Real)) ≤ error :=
    hgainFloor.trans hgainLe
  have hdenom : 0 < 2 * (players.card : Real) :=
    mul_pos (by norm_num) hcard
  have hscaled : lower * quittingTerminalSemanticDebtSum frontier.base ≤
      error * (2 * (players.card : Real)) :=
    (div_le_iff₀ hdenom).mp hdivided
  have hdivisionFree :
      lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
        (players.card : Real) * error := by
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 2)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  refine ⟨by simpa only [players] using hdivisionFree, ?_⟩
  simpa only [players] using hdivided

/-- The quantitative certificate implies nonconvergence of the fixed
player's full canonical gain sequence.  This is a mathematical projection:
it uses the positive gain floor on the stored strict subsequence. -/
theorem HasQuittingStoppingLawPositiveTargetReachedRowLocalization.exists_gain_not_tendsto_zero
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {lower : Real}
    (certificate :
      HasQuittingStoppingLawPositiveTargetReachedRowLocalization
        packet lower) :
    ∃ (stop : Nat -> Nat) (other : iota), other ≠ packet.observer ∧
      ¬ Tendsto
        (quittingStoppingLawPositiveTargetReachedRowGain packet stop other)
        atTop (nhds 0) := by
  obtain ⟨hlower, stop, subseq, other, hsubseq, hother, _htime, _hmass,
      hgain⟩ := certificate
  have hplayers : (Finset.univ.erase packet.observer).Nonempty :=
    ⟨other, Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩⟩
  have hcard : 0 < ((Finset.univ.erase packet.observer).card : Real) := by
    exact_mod_cast Finset.card_pos.mpr hplayers
  have hgainFloor : 0 <
      quittingStoppingLawPositiveTargetReachedRowGainFloor packet lower := by
    unfold quittingStoppingLawPositiveTargetReachedRowGainFloor
    exact div_pos (mul_pos hlower frontier.base_positive)
      (mul_pos (by norm_num) hcard)
  refine ⟨stop, other, hother, ?_⟩
  exact Math.not_tendsto_zero_of_positive_lower_bound_on_strict_subsequence
    (quittingStoppingLawPositiveTargetReachedRowGain packet stop other)
      subseq _ hsubseq hgainFloor hgain

/-- Eventual sure-Quit times and terminal mass along a strict subsequence
produce the quantitative reached-row localization. -/
theorem positiveTargetReachedRowLocalization_of_eventually_stop_mass
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : Real} (hlower : 0 < lower) (stop baseSubseq : Nat -> Nat)
    (hbaseSubseq : StrictMono baseSubseq)
    (hfinite : ∀ᶠ rank in atTop,
      packet.quitTime (baseSubseq rank) = some (stop (baseSubseq rank)))
    (hmass : ∀ᶠ rank in atTop, lower <=
      quittingStageCoalitionMass reward
        (quittingStoppingLawPositiveTargetReachedRowProfile packet
          (baseSubseq rank)) (stop (baseSubseq rank)) packet.terminal) :
    HasQuittingStoppingLawPositiveTargetReachedRowLocalization
      packet lower := by
  unfold HasQuittingStoppingLawPositiveTargetReachedRowLocalization
  have hready := hfinite.and hmass
  obtain ⟨start, hstart⟩ := eventually_atTop.1 hready
  let shifted : Nat -> Nat := fun n => start + n
  have hshifted : StrictMono shifted := fun _ _ hlt =>
    Nat.add_lt_add_left hlt start
  let subseq : Nat -> Nat := fun n => baseSubseq (shifted n)
  have hsubseq : StrictMono subseq := hbaseSubseq.comp hshifted
  let profile : Nat -> (quittingGame reward).BehaviorProfile := fun n =>
    quittingStoppingLawPositiveTargetReachedRowProfile packet (subseq n)
  let stage : Nat -> Nat := fun n => stop (subseq n)
  have htime : ∀ n,
      packet.quitTime (subseq n) = some (stage n) := by
    intro n
    exact (hstart (shifted n) (Nat.le_add_right start n)).1
  have hstageMass : ∀ n, lower <=
      quittingStageCoalitionMass reward (profile n) (stage n)
        packet.terminal := by
    intro n
    exact (hstart (shifted n) (Nat.le_add_right start n)).2
  have hsure : ∀ n,
      quittingProfileLiveRoot reward (profile n) (stage n) packet.observer =
        PMF.pure true := by
    intro n
    dsimp only [profile, quittingStoppingLawPositiveTargetReachedRowProfile]
    rw [quittingProfileLiveRoot_update_pureTime_self, htime n,
      quittingPureTimeHazard_some_self]
  have hdebt : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profile n)) packet.observer)
      atTop (nhds 0) := by
    have hcomp :=
      packet.observer_debt_tendsto_zero.comp hsubseq.tendsto_atTop
    simpa only [profile, quittingStoppingLawPositiveTargetReachedRowProfile,
      subseq, quittingStoppingLawRectangleTargetProfile, Function.comp_def]
      using hcomp
  have hminimum : ∀ n, quittingTerminalSemanticDebtSum frontier.base <=
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profile n) (stage n))) := by
    intro n
    exact frontier.base_minimum _
      (quittingTerminalSemanticPair_mem_carrier reward _)
  have hreach : ∀ n, lower <=
      quittingLiveMass reward (profile n) (stage n) := by
    intro n
    exact (hstageMass n).trans
      (quittingStageCoalitionMass_le_liveMass reward (profile n) (stage n)
        packet.terminal)
  obtain ⟨other, gainSubseq, hother, hgainSubseq, hgain⟩ :=
    exists_fixed_other_reachedRowGain_subsequence reward
      (quittingTerminalSemanticDebtSum frontier.base) frontier.base_positive
      profile stage packet.observer lower hminimum hlower hreach hsure hdebt
  let finalSubseq : Nat -> Nat := fun n => subseq (gainSubseq n)
  have hfinalSubseq : StrictMono finalSubseq :=
    hsubseq.comp hgainSubseq
  refine ⟨hlower, stop, finalSubseq, other, hfinalSubseq, hother, ?_, ?_, ?_⟩
  · intro rank
    simpa only [finalSubseq, stage] using htime (gainSubseq rank)
  · intro rank
    simpa only [finalSubseq, profile, stage] using
      hstageMass (gainSubseq rank)
  · intro rank
    simpa only [quittingStoppingLawPositiveTargetReachedRowGainFloor,
      quittingStoppingLawPositiveTargetReachedRowGain,
      quittingStoppingLawPositiveTargetReachedRowProfile, finalSubseq,
      profile, stage] using hgain rank

/-- The positive-collision marked-tail predicate already supplies the named
literal reached-row localization.  Its stored tail cluster and escape/fiber
alternative are not needed for this consumer. -/
theorem positiveCollisionMarkedTailDispatch_reachedRowLocalization
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : Real} (hlower : 0 < lower)
    (dispatch : HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch
      packet lower) :
    HasQuittingStoppingLawPositiveTargetReachedRowLocalization
      packet lower := by
  obtain ⟨stop, _cluster, baseSubseq, _hcluster, hbaseSubseq, hfinite,
      hmass, _htail, _hmarked, _hdispatch⟩ := dispatch
  exact positiveTargetReachedRowLocalization_of_eventually_stop_mass
    packet hlower stop baseSubseq hbaseSubseq hfinite hmass

/-- **Cardinality-free positive target localization.** A positive fixed
rectangle atom stores a uniform amount of terminal mass on the literal target
profiles. If the terminal contains the observer, the observer's pure-time
reset reaches an actual sure-Quit row with that mass. Vanishing observer debt
and the positive global debt floor then force one fixed other player's
canonical legal row deviation to have a uniform positive gain along a strict
subsequence. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.positiveTarget_reachedRowLocalization
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hobserver : packet.observer ∈ packet.terminal.val)
    (hrewardPositive : 0 < reward packet.terminal packet.observer) :
    HasQuittingStoppingLawPositiveTargetReachedRowLocalization packet
      ((packet.charge / 4) /
        ((Fintype.card (QuittingTerminalOutcome iota) : Real) *
          quittingRewardBound reward)) := by
  classical
  let lower := quittingStoppingLawPositiveTargetMassLower packet
  have hlower : 0 < lower := packet.positiveTargetMassLower_pos
  have hpersistent : ∀ᶠ n in atTop, lower <=
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawPositiveTargetReachedRowProfile packet n)
        (some packet.terminal) := by
    apply Eventually.of_forall
    intro n
    simpa only [lower, quittingStoppingLawPositiveTargetReachedRowProfile]
      using packet.positiveTarget_massLower hrewardPositive n
  obtain ⟨stop, hfinite, hmass, _hmarkedDefect⟩ :=
    exists_stops_tendsto_coordinateNashDefect_zero_of_persistent_collision
      reward (quittingStoppingLawRectangleTargetProfile packet)
      packet.observer packet.quitTime packet.terminal hobserver hlower
      packet.observer_debt_tendsto_zero (by
        simpa only [quittingStoppingLawPositiveTargetReachedRowProfile]
          using hpersistent)
  change HasQuittingStoppingLawPositiveTargetReachedRowLocalization
    packet lower
  exact positiveTargetReachedRowLocalization_of_eventually_stop_mass
    packet hlower stop id strictMono_id hfinite (by
      simpa [quittingStoppingLawPositiveTargetReachedRowProfile] using hmass)

/-- End-to-end literal no-go from the original positive rectangle packet.
The conclusion retains the packet's quantitative target-mass lower bound and
all actual-row provenance; it rules out unchanged exact source returns rather
than constructing one. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.nonempty_positiveTargetLiteralNoGo
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hobserver : packet.observer ∈ packet.terminal.val)
    (hrewardPositive : 0 < reward packet.terminal packet.observer) :
    Nonempty (QuittingStoppingLawPositiveTargetReachedRowLiteralNoGo packet
      ((packet.charge / 4) /
        ((Fintype.card (QuittingTerminalOutcome iota) : Real) *
          quittingRewardBound reward))) :=
  (packet.positiveTarget_reachedRowLocalization hobserver hrewardPositive).nonempty_literalNoGo

end GameTheory
