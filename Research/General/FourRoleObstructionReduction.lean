/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDebtTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumAggregateSurplusConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNegativeVertexGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn

/-!
# Four-role local obstruction reduction

This module packages the strongest currently landed player-label
reduction around a positive minimum terminal-semantic plateau.

For a positive debtor `owner`, one pure-time best-response law and one
subsequence of its literal reset profiles supply an opposite-face debt
transfer.  The same terminal law then has exactly three possible readouts:

* positive harmonic `Never` mass at a negative prescribed coordinate;
* one opponent label which is simultaneously a positive transfer recipient
  and a positive-incidence label; or
* two distinct opponents, a transfer `receiver` and an incidence `quitter`.

In the last branch, positive incidence contains an actual positive-mass
terminal coalition containing `quitter`.  Counterexample instability gives
that coalition a strict membership toggle.  Thus all locally distinguished
labels lie in

`{owner, receiver, quitter, toggle}`.

This is a reduction of **local obstruction arity**, not of the player type.
The terminal coalition may contain arbitrarily many players, the toggle need
not be distinct from the first three labels, and no outsider is deleted or
merged.  In particular, nothing below constructs a four-player reward table
or proves the cardinal reduction in
the companion random-deviation cardinal reduction.

The final section names the remaining consumer principle.  It is deliberately
not asserted: bounded role support alone does not align the reset cluster,
chronological incidence, and strict coalition toggle into a contradiction.
-/

noncomputable section

namespace GameTheory
namespace FourRoleObstructionReduction

open Filter Set
open scoped Topology
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Plateau geometry -/

/-- The positive minimum all-Continue plateau data used by the reset theorem.
The reward bound is kept in the object because it controls the quantitative
mass floor in the eventual local dispatch. -/
structure PositiveMinimumPlateau
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (M : ℝ) : Prop where
  bound_pos : 0 < M
  reward_bound : ∀ terminal player, |reward terminal player| ≤ M
  source_mem : source ∈ quittingTerminalSemanticCarrier reward
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum source ≤
      quittingTerminalSemanticDebtSum candidate
  debt_pos : 0 < quittingTerminalSemanticDebtSum source
  allContinue_nash : IsεQuittingRootNash reward source.1 0
    (quittingAllContinueRoot : ι → PMF Bool)

namespace PositiveMinimumPlateau

/-- The normalized debt coordinates of a positive plateau form a simplex:
they are nonnegative and sum to one. -/
theorem debtShare_simplex
    {source : QuittingTerminalSemanticPair ι} {M : ℝ}
    (plateau : PositiveMinimumPlateau reward source M) :
    (∀ who, 0 ≤ quittingTerminalSemanticDebtShare source who) ∧
      ∑ who, quittingTerminalSemanticDebtShare source who = 1 := by
  constructor
  · intro who
    exact quittingTerminalSemanticDebtShare_nonneg_of_mem_carrier
      source plateau.source_mem plateau.debt_pos who
  · exact sum_quittingTerminalSemanticDebtShare_eq_one
      source plateau.debt_pos

/-- Every positive plateau has a player carrying strictly positive debt. -/
theorem exists_positiveDebtor
    {source : QuittingTerminalSemanticPair ι} {M : ℝ}
    (plateau : PositiveMinimumPlateau reward source M) :
    ∃ owner, 0 < quittingTerminalSemanticDebt source owner := by
  have hnonneg : ∀ owner ∈ (Finset.univ : Finset ι),
      0 ≤ quittingTerminalSemanticDebt source owner := by
    intro owner _
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward plateau.source_mem owner
  have hsum : 0 < ∑ owner, quittingTerminalSemanticDebt source owner := by
    simpa only [quittingTerminalSemanticDebtSum] using plateau.debt_pos
  obtain ⟨owner, _hownerMem, howner⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsum
  exact ⟨owner, howner⟩

/-- The singleton slack geometry is nonnegative in every coordinate. -/
theorem singletonSlack_nonneg
    {source : QuittingTerminalSemanticPair ι} {M : ℝ}
    (plateau : PositiveMinimumPlateau reward source M) (who : ι) :
    0 ≤ quittingTerminalSemanticSingletonSlack reward source who := by
  exact minimumTerminalSemantic_singletonSlack_nonneg
    (reward := reward) source plateau.source_mem plateau.minimum
      plateau.debt_pos who

/-- There is at most one debt-vertex/zero-slack singleton gate. -/
theorem debtGate_unique
    {source : QuittingTerminalSemanticPair ι} {M : ℝ}
    (plateau : PositiveMinimumPlateau reward source M)
    {first second : ι}
    (hfirst : IsMinimumTerminalSemanticDebtGate reward source first)
    (hsecond : IsMinimumTerminalSemanticDebtGate reward source second) :
    first = second := by
  exact minimumTerminalSemantic_debtGate_unique
    (reward := reward) source plateau.source_mem plateau.debt_pos hfirst hsecond

end PositiveMinimumPlateau

/-! ## The same-law reset object -/

/-- A literal pure-time realizing law together with the semantic cluster of
the corresponding best-response resets.  The terminal law and reset cluster
come from the same deviated profiles; only the second subsequence is new. -/
structure SameLawResetCluster
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι) where
  profiles : ℕ → (quittingGame reward).BehaviorProfile
  quitTime : ℕ → Option ℕ
  mass : QuittingTerminalOutcome ι → ℝ
  baseSubseq : ℕ → ℕ
  cluster : QuittingTerminalSemanticPair ι
  resetSubseq : ℕ → ℕ
  profiles_tendsto : Tendsto
    (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (𝓝 source)
  mass_simplex : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι)
  baseSubseq_strictMono : StrictMono baseSubseq
  mass_tendsto : Tendsto (fun n => quittingTerminalOutcomeMass reward
    (Function.update (profiles (baseSubseq n)) owner
      (quittingPureTimeBehaviorStrategy reward owner
        (quitTime (baseSubseq n))))) atTop (𝓝 mass)
  cluster_mem : cluster ∈ quittingTerminalSemanticCarrier reward
  resetSubseq_strictMono : StrictMono resetSubseq
  reset_tendsto : Tendsto (fun rank => quittingTerminalSemanticPair reward
    (Function.update (profiles (baseSubseq (resetSubseq rank))) owner
      (quittingPureTimeBehaviorStrategy reward owner
        (quitTime (baseSubseq (resetSubseq rank)))))) atTop (𝓝 cluster)
  owner_reset : quittingTerminalSemanticDebt cluster owner = 0
  transfer_account :
    (∑ other ∈ Finset.univ.erase owner,
        quittingTerminalSemanticDebtChange source cluster other) =
      (quittingTerminalSemanticDebtSum cluster -
          quittingTerminalSemanticDebtSum source) +
        quittingTerminalSemanticDebt source owner
  transfer_lower : quittingTerminalSemanticDebt source owner ≤
    ∑ other ∈ Finset.univ.erase owner,
      quittingTerminalSemanticDebtChange source cluster other

/-! ## Coalition toggles and the three local branches -/

/-- One strict instability of a positive terminal coalition.  The player
either belongs to the coalition and gains by leaving, or is outside and gains
by joining. -/
structure StrictCoalitionToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) where
  player : ι
  direction :
    (player ∈ terminal.val ∧
      quittingSetReward reward terminal.val player <
        quittingSetReward reward (terminal.val.erase player) player) ∨
    (player ∉ terminal.val ∧
      quittingSetReward reward terminal.val player <
        quittingSetReward reward (insert player terminal.val) player)

/-- Counterexample instability turns every terminal coalition into a strict
toggle object. -/
theorem exists_strictCoalitionToggle
    (regime : QuittingCounterexampleRegime reward)
    (terminal : {S : Finset ι // S.Nonempty}) :
    Nonempty (StrictCoalitionToggle reward terminal) := by
  rcases regime.terminalCoalition_has_strictToggle terminal with
    ⟨member, hmem, hgain⟩ | ⟨outsider, hout, hgain⟩
  · exact ⟨⟨member, Or.inl ⟨hmem, hgain⟩⟩⟩
  · exact ⟨⟨outsider, Or.inr ⟨hout, hgain⟩⟩⟩

/-- The quantitative average-share conclusion is genuinely positive whenever
the source debt is positive and the receiver is an opponent. -/
theorem debtChange_pos_of_average_le
    (source target : QuittingTerminalSemanticPair ι)
    (owner receiver : ι)
    (hdebt : 0 < quittingTerminalSemanticDebt source owner)
    (hreceiver : receiver ≠ owner)
    (haverage : quittingTerminalSemanticDebt source owner /
        ((Finset.univ.erase owner).card : ℝ) ≤
      quittingTerminalSemanticDebtChange source target receiver) :
    0 < quittingTerminalSemanticDebtChange source target receiver := by
  have hreceiverMem : receiver ∈ Finset.univ.erase owner :=
    Finset.mem_erase.mpr ⟨hreceiver, Finset.mem_univ receiver⟩
  have hcard : 0 < ((Finset.univ.erase owner).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨receiver, hreceiverMem⟩)
  exact (div_pos hdebt hcard).trans_le haverage

/-- **Game-facing refinement of the landed separator.**  Positive debt,
opposite-face transfer, and positive opponent-containing mass give either a
matched recipient/incidence label, or three distinct base roles together
with a positive-mass coalition containing the incidence label and one strict
coalition toggle.

The fourth label is the toggle player; it may coincide with the owner or the
receiver, and in the leave branch it may also coincide with the quitter. -/
theorem exists_matched_transfer_incidence_or_separatedToggle
    (regime : QuittingCounterexampleRegime reward)
    (source target : QuittingTerminalSemanticPair ι) (owner : ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hdebt : 0 < quittingTerminalSemanticDebt source owner)
    (htransfer : quittingTerminalSemanticDebt source owner ≤
      ∑ other ∈ Finset.univ.erase owner,
        quittingTerminalSemanticDebtChange source target other)
    (hincidence : 0 <
      quittingTerminalOpponentContainingMass owner mass) :
    (∃ recipient, recipient ≠ owner ∧
        0 < quittingTerminalSemanticDebtChange source target recipient ∧
        0 < quittingTerminalOpponentIncidenceMass owner recipient mass) ∨
      ∃ (receiver quitter : ι)
          (terminal : {S : Finset ι // S.Nonempty})
          (_toggle : StrictCoalitionToggle reward terminal),
        receiver ≠ owner ∧ quitter ≠ owner ∧ receiver ≠ quitter ∧
        quittingTerminalSemanticDebt source owner /
            ((Finset.univ.erase owner).card : ℝ) ≤
          quittingTerminalSemanticDebtChange source target receiver ∧
        0 < quittingTerminalSemanticDebtChange source target receiver ∧
        0 < quittingTerminalOpponentIncidenceMass owner quitter mass ∧
        quitter ∈ terminal.val ∧ 0 < mass (some terminal) := by
  rcases exists_matched_transfer_incidence_or_twoOpponent_separator
      source target owner mass hmass hdebt htransfer hincidence with
    hmatched | hseparated
  · exact Or.inl hmatched
  · right
    obtain ⟨receiver, quitter, hreceiverNe, hquitterNe, hdistinct,
      haverage, hincidencePos, _hthree⟩ := hseparated
    obtain ⟨terminal, hquitterMem, _hquitterNe', hterminalMass⟩ :=
      _root_.GameTheory.exists_positiveMass_terminal_of_opponentIncidence
        owner quitter mass hmass hincidencePos
    let toggle := Classical.choice
      (exists_strictCoalitionToggle regime terminal)
    have htransferPos := debtChange_pos_of_average_le
      source target owner receiver hdebt hreceiverNe haverage
    exact ⟨receiver, quitter, terminal, toggle, hreceiverNe, hquitterNe,
      hdistinct, haverage, htransferPos, hincidencePos, hquitterMem,
      hterminalMass⟩

/-- The matched branch uses only the debtor and one recipient/incidence
label. -/
structure MatchedRecipientRoles
    (source : QuittingTerminalSemanticPair ι) (owner : ι)
    (law : SameLawResetCluster reward source owner) where
  recipient : ι
  recipient_ne_owner : recipient ≠ owner
  transfer_pos : 0 < quittingTerminalSemanticDebtChange
    source law.cluster recipient
  incidence_pos : 0 < quittingTerminalOpponentIncidenceMass
    owner recipient law.mass

namespace MatchedRecipientRoles

/-- The matched obstruction genuinely distinguishes exactly two labels. -/
@[simp] theorem roleSupport_card
    {source : QuittingTerminalSemanticPair ι} {owner : ι}
    {law : SameLawResetCluster reward source owner}
    (roles : MatchedRecipientRoles source owner law) :
    ({owner, roles.recipient} : Finset ι).card = 2 := by
  simp [roles.recipient_ne_owner.symm]

end MatchedRecipientRoles

/-- The separated branch retains three pairwise distinct base roles and one
coalition-toggle role.  The coalition itself is not cardinality-bounded. -/
structure SeparatedToggleRoles
    (source : QuittingTerminalSemanticPair ι) (owner : ι)
    (law : SameLawResetCluster reward source owner) where
  receiver : ι
  quitter : ι
  receiver_ne_owner : receiver ≠ owner
  quitter_ne_owner : quitter ≠ owner
  receiver_ne_quitter : receiver ≠ quitter
  transfer_average : quittingTerminalSemanticDebt source owner /
      ((Finset.univ.erase owner).card : ℝ) ≤
    quittingTerminalSemanticDebtChange source law.cluster receiver
  transfer_pos : 0 < quittingTerminalSemanticDebtChange
    source law.cluster receiver
  incidence_pos : 0 < quittingTerminalOpponentIncidenceMass
    owner quitter law.mass
  terminal : {S : Finset ι // S.Nonempty}
  quitter_mem_terminal : quitter ∈ terminal.val
  terminal_mass_pos : 0 < law.mass (some terminal)
  toggle : StrictCoalitionToggle reward terminal

namespace SeparatedToggleRoles

/-- The three roles forced by separation are exactly three distinct player
labels. -/
def baseRoleSupport
    {source : QuittingTerminalSemanticPair ι} {owner : ι}
    {law : SameLawResetCluster reward source owner}
    (roles : SeparatedToggleRoles source owner law) : Finset ι :=
  {owner, roles.receiver, roles.quitter}

/-- Adding the toggle player gives the complete local role support. -/
def roleSupport
    {source : QuittingTerminalSemanticPair ι} {owner : ι}
    {law : SameLawResetCluster reward source owner}
    (roles : SeparatedToggleRoles source owner law) : Finset ι :=
  insert roles.toggle.player (roles.baseRoleSupport)

@[simp] theorem baseRoleSupport_card
    {source : QuittingTerminalSemanticPair ι} {owner : ι}
    {law : SameLawResetCluster reward source owner}
    (roles : SeparatedToggleRoles source owner law) :
    roles.baseRoleSupport.card = 3 := by
  simp [baseRoleSupport, roles.receiver_ne_owner.symm,
    roles.quitter_ne_owner.symm, roles.receiver_ne_quitter]

/-- Separation alone forces at least three ambient players. -/
theorem three_le_playerCard
    {source : QuittingTerminalSemanticPair ι} {owner : ι}
    {law : SameLawResetCluster reward source owner}
    (roles : SeparatedToggleRoles source owner law) :
    3 ≤ Fintype.card ι := by
  calc
    3 = roles.baseRoleSupport.card := roles.baseRoleSupport_card.symm
    _ ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ roles.baseRoleSupport)
    _ = Fintype.card ι := Finset.card_univ

/-- The separated obstruction distinguishes either three or four player
labels, never more. -/
theorem roleSupport_card_eq_three_or_four
    {source : QuittingTerminalSemanticPair ι} {owner : ι}
    {law : SameLawResetCluster reward source owner}
    (roles : SeparatedToggleRoles source owner law) :
    roles.roleSupport.card = 3 ∨ roles.roleSupport.card = 4 := by
  by_cases htoggle : roles.toggle.player ∈ roles.baseRoleSupport
  · left
    rw [roleSupport, Finset.insert_eq_self.mpr htoggle,
      roles.baseRoleSupport_card]
  · right
    rw [roleSupport, Finset.card_insert_of_notMem htoggle,
      roles.baseRoleSupport_card]

/-- Four distinct local roles occur exactly when the toggle is new relative
to the debtor/receiver/quitter triple. -/
theorem roleSupport_card_eq_four_iff
    {source : QuittingTerminalSemanticPair ι} {owner : ι}
    {law : SameLawResetCluster reward source owner}
    (roles : SeparatedToggleRoles source owner law) :
    roles.roleSupport.card = 4 ↔
      roles.toggle.player ∉ roles.baseRoleSupport := by
  constructor
  · intro hcard hmem
    rw [roleSupport, Finset.insert_eq_self.mpr hmem,
      roles.baseRoleSupport_card] at hcard
    omega
  · intro hnot
    rw [roleSupport, Finset.card_insert_of_notMem hnot,
      roles.baseRoleSupport_card]

/-- If the toggle supplies a fourth distinct role, the ambient game has at
least four players.  The converse is not claimed. -/
theorem four_le_playerCard_of_roleSupport_card_eq_four
    {source : QuittingTerminalSemanticPair ι} {owner : ι}
    {law : SameLawResetCluster reward source owner}
    (roles : SeparatedToggleRoles source owner law)
    (hfour : roles.roleSupport.card = 4) :
    4 ≤ Fintype.card ι := by
  calc
    4 = roles.roleSupport.card := hfour.symm
    _ ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ roles.roleSupport)
    _ = Fintype.card ι := Finset.card_univ

/-- In the join branch, the toggle player is necessarily different from the
incidence label already lying in the terminal coalition. -/
theorem toggle_ne_quitter_of_join
    {source : QuittingTerminalSemanticPair ι} {owner : ι}
    {law : SameLawResetCluster reward source owner}
    (roles : SeparatedToggleRoles source owner law)
    (hjoin : roles.toggle.player ∉ roles.terminal.val) :
    roles.toggle.player ≠ roles.quitter := by
  intro heq
  apply hjoin
  simpa [heq] using roles.quitter_mem_terminal

end SeparatedToggleRoles

/-- The exact local dispatch produced by the landed same-law reset theorem.
The quantitative lower bound is retained in all three branches. -/
inductive LocalFourRoleBranch
    (source : QuittingTerminalSemanticPair ι) (owner : ι) (M : ℝ)
    (law : SameLawResetCluster reward source owner) : Type
  | negativeNever
      (mass_floor : quittingTerminalSemanticDebt source owner /
        (2 * M * Fintype.card (QuittingTerminalOutcome ι)) ≤ law.mass none)
      (source_negative : source.1 owner < 0)
  | matchedRecipient
      (opponent_mass_floor : quittingTerminalSemanticDebt source owner /
        (2 * M * Fintype.card (QuittingTerminalOutcome ι)) ≤
          quittingTerminalOpponentContainingMass owner law.mass)
      (roles : MatchedRecipientRoles source owner law)
  | separatedToggle
      (opponent_mass_floor : quittingTerminalSemanticDebt source owner /
        (2 * M * Fintype.card (QuittingTerminalOutcome ι)) ≤
          quittingTerminalOpponentContainingMass owner law.mass)
      (roles : SeparatedToggleRoles source owner law)

namespace LocalFourRoleBranch

/-- Player labels actually distinguished by a local branch. -/
def roleSupport
    {source : QuittingTerminalSemanticPair ι} {owner : ι} {M : ℝ}
    {law : SameLawResetCluster reward source owner}
    (branch : LocalFourRoleBranch source owner M law) : Finset ι :=
  match branch with
  | .negativeNever _ _ => {owner}
  | .matchedRecipient _ roles => {owner, roles.recipient}
  | .separatedToggle _ roles => roles.roleSupport

/-- **Local obstruction arity is at most four.**  This counts selected player
labels only; it does not bound the size of the terminal coalition. -/
theorem roleSupport_card_le_four
    {source : QuittingTerminalSemanticPair ι} {owner : ι} {M : ℝ}
    {law : SameLawResetCluster reward source owner}
    (branch : LocalFourRoleBranch source owner M law) :
    branch.roleSupport.card ≤ 4 := by
  cases branch with
  | negativeNever => simp [roleSupport]
  | matchedRecipient floor roles =>
      rw [roleSupport, roles.roleSupport_card]
      omega
  | separatedToggle floor roles =>
      rcases roles.roleSupport_card_eq_three_or_four with hthree | hfour
      · simp [roleSupport, hthree]
      · simp [roleSupport, hfour]

end LocalFourRoleBranch

/-! ## Extraction from one positive minimum plateau -/

/-- **Same-law four-role extraction.**  A chosen positive debtor at a positive
minimum plateau has one literal reset law whose obstruction is negative,
matched, or supported on a separated role tuple of arity at most four.

The separated branch strengthens the landed two-opponent separator by
retaining an actual positive-mass terminal atom and its strict counterexample
toggle. -/
theorem exists_sameLawResetCluster_localFourRoleBranch
    (regime : QuittingCounterexampleRegime reward)
    {source : QuittingTerminalSemanticPair ι} {M : ℝ}
    (plateau : PositiveMinimumPlateau reward source M)
    (owner : ι) (howner : 0 < quittingTerminalSemanticDebt source owner) :
    ∃ (law : SameLawResetCluster reward source owner)
        (branch : LocalFourRoleBranch source owner M law),
      branch.roleSupport.card ≤ 4 := by
  obtain ⟨profiles, quitTime, mass, baseSubseq, cluster, resetSubseq,
      hprofiles, hmass, hbaseSubseq, hmassLimit, hcluster,
      hresetSubseq, hresetLimit, hreset, haccount, htransfer,
      halternative⟩ :=
    exists_samePureTimeLaw_resetCluster_negativeNever_or_matched_separator
      reward source plateau.source_mem plateau.minimum
        plateau.allContinue_nash owner howner plateau.bound_pos
        plateau.reward_bound
  let law : SameLawResetCluster reward source owner :=
    { profiles := profiles
      quitTime := quitTime
      mass := mass
      baseSubseq := baseSubseq
      cluster := cluster
      resetSubseq := resetSubseq
      profiles_tendsto := hprofiles
      mass_simplex := hmass
      baseSubseq_strictMono := hbaseSubseq
      mass_tendsto := hmassLimit
      cluster_mem := hcluster
      resetSubseq_strictMono := hresetSubseq
      reset_tendsto := hresetLimit
      owner_reset := hreset
      transfer_account := haccount
      transfer_lower := htransfer }
  rcases halternative with hnegative | ⟨hopponentFloor, hfinite⟩
  · let branch : LocalFourRoleBranch source owner M law :=
      .negativeNever hnegative.1 hnegative.2
    exact ⟨law, branch, branch.roleSupport_card_le_four⟩
  · rcases hfinite with hmatched | hseparated
    · obtain ⟨recipient, hne, htransferPos, hincidencePos⟩ := hmatched
      let roles : MatchedRecipientRoles source owner law :=
        { recipient := recipient
          recipient_ne_owner := hne
          transfer_pos := htransferPos
          incidence_pos := hincidencePos }
      let branch : LocalFourRoleBranch source owner M law :=
        .matchedRecipient hopponentFloor roles
      exact ⟨law, branch, branch.roleSupport_card_le_four⟩
    · obtain ⟨receiver, quitter, hreceiverNe, hquitterNe, hdistinct,
          haverage, hincidencePos, _hthree⟩ := hseparated
      obtain ⟨terminal, hquitterMem, _hquitterNe', hterminalMass⟩ :=
      _root_.GameTheory.exists_positiveMass_terminal_of_opponentIncidence
          owner quitter mass hmass hincidencePos
      let toggle := Classical.choice
        (exists_strictCoalitionToggle regime terminal)
      have htransferPos := debtChange_pos_of_average_le
        source cluster owner receiver howner hreceiverNe haverage
      let roles : SeparatedToggleRoles source owner law :=
        { receiver := receiver
          quitter := quitter
          receiver_ne_owner := hreceiverNe
          quitter_ne_owner := hquitterNe
          receiver_ne_quitter := hdistinct
          transfer_average := haverage
          transfer_pos := htransferPos
          incidence_pos := hincidencePos
          terminal := terminal
          quitter_mem_terminal := hquitterMem
          terminal_mass_pos := hterminalMass
          toggle := toggle }
      let branch : LocalFourRoleBranch source owner M law :=
        .separatedToggle hopponentFloor roles
      exact ⟨law, branch, branch.roleSupport_card_le_four⟩

/-- Every positive minimum plateau contains a local obstruction supported on
at most four distinguished player labels. -/
theorem exists_localFourRoleObstruction_of_plateau
    (regime : QuittingCounterexampleRegime reward)
    {source : QuittingTerminalSemanticPair ι} {M : ℝ}
    (plateau : PositiveMinimumPlateau reward source M) :
    ∃ (owner : ι) (law : SameLawResetCluster reward source owner)
        (branch : LocalFourRoleBranch source owner M law),
      0 < quittingTerminalSemanticDebt source owner ∧
        branch.roleSupport.card ≤ 4 := by
  obtain ⟨owner, howner⟩ := plateau.exists_positiveDebtor
  obtain ⟨law, branch, hfour⟩ :=
    exists_sameLawResetCluster_localFourRoleBranch
      regime plateau owner howner
  exact ⟨owner, law, branch, howner, hfour⟩

/-! ## Global counterexample certificate -/

/-- Every counterexample carries a concrete positive minimum plateau and its
same-law local four-role dispatch.  All data still live in the original
player type `ι`. -/
structure CounterexampleLocalFourRoleCertificate
    (regime : QuittingCounterexampleRegime reward) where
  M : ℝ
  source : QuittingTerminalSemanticPair ι
  plateau : PositiveMinimumPlateau reward source M
  owner : ι
  owner_debt_pos : 0 < quittingTerminalSemanticDebt source owner
  law : SameLawResetCluster reward source owner
  branch : LocalFourRoleBranch source owner M law

/-- **Global local-arity theorem.**  Every finite quitting counterexample has
a same-law obstruction certificate whose selected role support has at most
four players.  This theorem does not reduce the ambient game to those roles. -/
theorem exists_counterexampleLocalFourRoleCertificate
    (regime : QuittingCounterexampleRegime reward) :
    ∃ certificate : CounterexampleLocalFourRoleCertificate regime,
      certificate.branch.roleSupport.card ≤ 4 := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨source, hsource, hminimum, ⟨owner, howner⟩,
      hnash, _hfixed⟩ :=
    noUniformPayoff_implies_positiveMinimumSemanticPlateau regime
  let M : ℝ := quittingRewardBound reward + 1
  have hM : 0 < M := by
    dsimp [M]
    linarith [quittingRewardBound_nonneg reward]
  have hreward : ∀ terminal player, |reward terminal player| ≤ M := by
    intro terminal player
    exact (abs_reward_le_quittingRewardBound reward terminal player).trans
      (by dsimp [M]; linarith)
  have hpositive : 0 < quittingTerminalSemanticDebtSum source := by
    have hnonneg : ∀ who ∈ (Finset.univ : Finset ι),
        0 ≤ quittingTerminalSemanticDebt source who := by
      intro who _
      exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hsource who
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_pos' hnonneg ⟨owner, Finset.mem_univ owner, howner⟩
  let plateau : PositiveMinimumPlateau reward source M :=
    { bound_pos := hM
      reward_bound := hreward
      source_mem := hsource
      minimum := hminimum
      debt_pos := hpositive
      allContinue_nash := hnash }
  obtain ⟨law, branch, hfour⟩ :=
    exists_sameLawResetCluster_localFourRoleBranch
      regime plateau owner howner
  let certificate : CounterexampleLocalFourRoleCertificate regime :=
    { M := M
      source := source
      plateau := plateau
      owner := owner
      owner_debt_pos := howner
      law := law
      branch := branch }
  exact ⟨certificate, hfour⟩

/-! ## Negative debt-gate supplement -/

/-- At the unique possible singleton gate, the landed negative-vertex theorem
adds an independent table-level branch: a strict singleton joiner, or a fixed
punishment moat carried by another realizing pure-time law.  This theorem is
kept separate because a negative `Never` atom does not by itself prove that
the selected debtor is a singleton gate. -/
theorem debtGate_joiner_or_punishmentMoat_sameLaw
    (regime : QuittingCounterexampleRegime reward)
    {source : QuittingTerminalSemanticPair ι} {M theta : ℝ}
    (plateau : PositiveMinimumPlateau reward source M)
    (owner : ι)
    (hgate : IsMinimumTerminalSemanticDebtGate reward source owner)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSingletonCollisionReward reward owner other) ∨
      quittingSoloReward reward owner owner <
          quittingPunishmentValue reward owner ∧
        ∃ (profiles : ℕ → (quittingGame reward).BehaviorProfile)
            (quitTime : ℕ → Option ℕ)
            (mass : QuittingTerminalOutcome ι → ℝ)
            (subseq : ℕ → ℕ),
          Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
              atTop (nhds source) ∧
          mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
          StrictMono subseq ∧
          Tendsto (fun n => quittingTerminalOutcomeMass reward
              (Function.update (profiles (subseq n)) owner
                (quittingPureTimeBehaviorStrategy reward owner
                  (quitTime (subseq n)))))
            atTop (nhds mass) ∧
          ((source.1 owner ≤
                -theta * quittingTerminalSemanticDebtSum source ∧
              theta * quittingTerminalSemanticDebtSum source / M ≤ mass none ∧
              ∀ᶠ n in atTop, quitTime (subseq n) = none) ∨
            ((1 - theta) * quittingTerminalSemanticDebtSum source / (2 * M) ≤
                quittingTerminalOpponentContainingMass owner mass ∧
              ∀ᶠ n in atTop,
                ((1 - theta) * quittingTerminalSemanticDebtSum source /
                    (2 * M)) / 2 <
                  ∑ terminal ∈ Finset.univ.filter
                      (fun terminal => terminal.val ≠ {owner}),
                    ∑' time, quittingStageCoalitionMass reward
                      (Function.update (profiles (subseq n)) owner
                        (quittingPureTimeBehaviorStrategy reward owner
                          (quitTime (subseq n)))) time terminal)) := by
  exact regime.exists_joiner_or_punishmentMoat_sameLaw
    source owner plateau.bound_pos plateau.reward_bound plateau.source_mem
      plateau.minimum plateau.debt_pos plateau.allContinue_nash hgate
      htheta hthetaOne

/-! ## The honest remaining premise -/

/-- The missing consumer/provenance principle.  It says that no complete
same-law local dispatch certificate can survive once its reset transfer,
chronological incidence, and (in the separated branch) coalition toggle are
consumed together.

This proposition is intentionally only a named target.  Role counting does
not prove it: the terminal coalition can use outsiders outside the role
support, and the strict toggle is not yet state-matched to the reset edge. -/
def EveryLocalFourRoleDispatchIsConsumed : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
      (regime : QuittingCounterexampleRegime reward)
      (_certificate : CounterexampleLocalFourRoleCertificate regime),
    False

/-- If the missing state-matched consumer is proved, no finite quitting
counterexample regime exists.  This implication is logical closure only; it
does not turn the local certificate into a four-player table. -/
theorem not_counterexampleRegime_of_everyLocalDispatchConsumed
    (hconsume : EveryLocalFourRoleDispatchIsConsumed)
    (regime : QuittingCounterexampleRegime reward) : False := by
  obtain ⟨certificate, _hfour⟩ :=
    exists_counterexampleLocalFourRoleCertificate regime
  exact hconsume reward regime certificate

end FourRoleObstructionReduction
end GameTheory
