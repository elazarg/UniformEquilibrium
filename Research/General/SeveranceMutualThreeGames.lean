/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Packet.Energy
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefixChargedBridge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Players.SmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicWindows
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Ballisticity
import UniformEquilibrium.Quitting.Cycles.PeriodicNormalizedSeam

/-!
# A severance mutual, two arenas, and three certificate exits

This module presents a finite quitting game without changing its strategy
space.  A severance mutual has finitely many members.  Each day every member
chooses `Stay` (`false`) or `File` (`true`).  The first nonempty set of filers
closes the mutual and activates that set's settlement schedule; perpetual
operation pays zero.

Current results organize the reduced problem most naturally as two
certification arenas over the same mutual, with three possible exits:

* the **normalized run-off audit arena** compares a normalized sole-filer
  prospectus with the actual occupation and complete behavioral evaluation of
  a repeated late ledger window.  It can exit through an accepted prospectus
  or an unblocked periodic audit;
* the **support-reorganization arena** starts from the packet's forced
  positive reciprocal-synergy pair and seeks a positive-exposure exact return.

The central object is `ThreeGameDossier`.  It stores the canonical
terminal exploitability witness and the independent source and dynamic-tail witnesses
which current
production theorems force from it.  Two exact reductions are proved:

1. a dossier exists iff the underlying quitting game has no
   uniform-equilibrium payoff;
2. the proposition that every dossier exits one of the two arenas through at
   least one of the three certificates is equivalent to existence of a
   uniform-equilibrium payoff for the fixed table.

Thus `ThreeCertificateDispatch` neither assumes the missing trilemma nor
weakens the quitting conjecture.  The current theorems show much more about
the obstruction before that open dispatch: packet refusal is a positive
quadratic energy with a supported reciprocal pair; conditional collision in
late source windows vanishes; every selected tail segment is already a
literal floor prefix; and periodic attachment is governed by endpoint drift
normalized by joint and opponent survival gaps.  Ballisticity then couples
underwriting to audit: a late positive-absorption window cannot have endpoint
drift little-o of its absorbed mass, since that would manufacture a fully
complementary packet.  What is not proved is a return or terminal realization;
the path may approach its boundary at nonzero absorption-clock speed.  The
remaining producer must cancel the normalized seam or pivot the reciprocal
support into a charged return.
-/

noncomputable section

namespace GameTheory
namespace SeveranceMutual

open Filter StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A severance mutual is exactly a quitting reward table: one settlement
vector for every nonempty set of simultaneous filers. -/
structure Mutual (ι : Type) [Fintype ι] where
  settlement : {S : Finset ι // S.Nonempty} → Payoff ι

namespace Mutual

variable (club : Mutual ι)

/-- The behavioral game of the mutual.  This is definitionally the quitting
game of its settlement table. -/
abbrev game := quittingGame club.settlement

/-- A complete calendar understanding while the mutual remains open. -/
abbrev Understanding := club.game.BehaviorProfile

/-- One member's unilateral filing policy. -/
abbrev FilingPolicy (who : ι) := club.game.BehaviorStrategy who

/-- Expected terminal settlement.  The event of perpetual operation
contributes zero. -/
def terminalSettlement (understanding : club.Understanding) (who : ι) : ℝ :=
  quittingTerminalPayoff club.settlement understanding who

/-- Existence of a uniform-equilibrium payoff for the mutual. -/
def HasUniformPayoff : Prop :=
  ∃ payoff : Payoff ι,
    club.game.IsUniformEquilibriumPayoff none payoff

/-- Regard an arbitrary quitting table as a mutual. -/
def ofQuittingTable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Mutual ι :=
  ⟨reward⟩

omit [DecidableEq ι] in
@[simp] theorem ofQuittingTable_settlement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (ofQuittingTable reward).settlement = reward :=
  rfl

/-- **Identity on games.**  The UE-payoff question for a quitting table and
for its severance mutual is literally the same proposition. -/
theorem quittingGame_hasUniformPayoff_iff_mutual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      (ofQuittingTable reward).HasUniformPayoff :=
  Iff.rfl

/-- The all-table quitting conjecture and the all-mutual statement are
equivalent, not merely related by a one-way encoding. -/
theorem allQuittingGames_iff_allMutuals :
    (∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
    (∀ candidate : Mutual ι, candidate.HasUniformPayoff) := by
  constructor
  · intro hall candidate
    exact hall candidate.settlement
  · intro hall reward
    exact hall (ofQuittingTable reward)

/-! ## The exact counterexample dossier -/

/-- The complete three-game dossier forced by a hypothetical counterexample.
The source packet and dynamic tail are stored as independent consequences;
no relation between them is asserted. -/
structure ThreeGameDossier where
  witness : QuittingTerminalExploitabilityWitness club.settlement
  source : QuittingCounterexampleSourceWitness witness
  dynamicTail : QuittingCounterexampleDynamicTailWitness witness

namespace ThreeGameDossier

variable {club : Mutual ι}

/-- Attach the independently forced source and dynamic-tail witnesses to a
terminal exploitability witness. -/
def ofTerminalExploitabilityWitness
    (witness : QuittingTerminalExploitabilityWitness club.settlement) :
  club.ThreeGameDossier where
  witness := witness
  source := Classical.choice witness.nonempty_sourceWitness
  dynamicTail := Classical.choice witness.nonempty_dynamicTailWitness

/-- A dossier itself refutes every uniform-equilibrium payoff. -/
theorem not_hasUniformPayoff (dossier : club.ThreeGameDossier) :
    ¬ club.HasUniformPayoff :=
  dossier.witness.not_exists_uniformEquilibriumPayoff

/-- Every possible dossier has at least four members. -/
theorem four_le_card (dossier : club.ThreeGameDossier) :
    4 ≤ Fintype.card ι := by
  have hcard := dossier.witness.three_lt_card
  omega

/-- The dossier retains the canonical finite run-off exposure bound. -/
theorem finite_runoffCapacity (dossier : club.ThreeGameDossier) :
    quittingPunishmentFloorPrefixChargeCapacity club.settlement ≠ ⊤ :=
  dossier.witness.prefixChargeCapacity_ne_top

end ThreeGameDossier

/-- **Exact counterexample reduction.**  A three-game dossier exists exactly
when the underlying quitting game has no uniform-equilibrium payoff. -/
theorem nonempty_threeGameDossier_iff_not_hasUniformPayoff
    [Nonempty ι] :
    Nonempty club.ThreeGameDossier ↔ ¬ club.HasUniformPayoff := by
  constructor
  · rintro ⟨dossier⟩
    exact dossier.not_hasUniformPayoff
  · intro hno
    let witness := quittingTerminalExploitabilityWitnessOfNoUniformPayoff
      club.settlement hno
    exact ⟨ThreeGameDossier.ofTerminalExploitabilityWitness witness⟩

/-! ## Arena one, exit A: accepted underwriting -/

/-- A sole-filer underwriting prospectus is exactly the normalized singleton
packet forced by the analytic waist. -/
abbrev Prospectus :=
  QuittingNormalizedSingletonSourcePacket club.settlement

namespace Prospectus

variable {club : Mutual ι}

/-- A prospectus is accepted when every member assigned positive filing mass
is indifferent at its own handshake: its singleton mixture delivers exactly
its own sole-filer settlement.  The remaining coverage, security, and
probability requirements are already fields of `Prospectus`. -/
def IsAccepted (prospectus : club.Prospectus) : Prop :=
  ∀ owner, 0 < prospectus.mass owner →
    quittingSingletonMixture club.settlement prospectus.mass owner =
      club.settlement (quittingSingletonTerminal owner) owner

/-- Winning the underwriting game is an independently checkable UE
certificate via the complementary singleton-mixture compiler. -/
theorem exists_uniformPayoff_of_isAccepted [Nonempty ι]
    (prospectus : club.Prospectus)
    (haccepted : prospectus.IsAccepted) :
    club.HasUniformPayoff := by
  exact exists_uniformEquilibriumPayoff_of_complementarySingletonMixture
    club.settlement prospectus.mass prospectus.target
      prospectus.mass_nonneg prospectus.mass_sum prospectus.mix_ge_target
      haccepted prospectus.solo_le_target prospectus.punishment_le_target

end Prospectus

/-- The underwriter wins if some normalized prospectus is accepted. -/
def HasWinningUnderwriter : Prop :=
  ∃ prospectus : club.Prospectus, prospectus.IsAccepted

namespace ThreeGameDossier

variable {club : Mutual ι}

/-- The particular underwriting proposal carried by the source witness. -/
def underwritingProspectus (dossier : club.ThreeGameDossier) :
    club.Prospectus :=
  dossier.source.packet

/-- In a dossier, not only the selected proposal but every normalized
prospectus has an active member with one common positive refusal advantage. -/
theorem exists_uniform_underwritingRefusalMargin
    (dossier : club.ThreeGameDossier) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ prospectus : club.Prospectus,
        ∃ owner,
          0 < prospectus.mass owner ∧ prospectus.mass owner < 1 ∧
          prospectus.target owner <
            quittingSingletonMixture club.settlement
              prospectus.mass owner ∧
          quittingSingletonMixture club.settlement
              prospectus.mass owner + δ ≤
            quittingSingletonRefusalValue club.settlement
              prospectus.mass owner owner := by
  letI : Nonempty ι := dossier.witness.nonempty_players
  exact dossier.witness.exists_pos_uniform_normalizedSingletonPacketRefusal

/-- The packet's aggregate refusal surplus is its quadratic singleton energy.
This identifies the underwriter's objections with reciprocal, rather than
skew-circulation, effects. -/
theorem underwritingRefusal_eq_quadraticEnergy
    (dossier : club.ThreeGameDossier) :
    quittingPacketWeightedRefusalSurplus dossier.underwritingProspectus =
      quittingSingletonPacketQuadraticEnergy club.settlement
        dossier.underwritingProspectus.mass := by
  letI : Nonempty ι := dossier.witness.nonempty_players
  exact dossier.witness.packetWeightedRefusal_eq_quadraticForm
    dossier.underwritingProspectus

/-- The concrete support seed now forced inside every dossier: two distinct
positive-mass prospectus owners with positive reciprocal singleton synergy. -/
structure ReciprocalSupportPair (dossier : club.ThreeGameDossier) where
  first : ι
  second : ι
  first_mass_pos : 0 < dossier.underwritingProspectus.mass first
  second_mass_pos : 0 < dossier.underwritingProspectus.mass second
  ne : first ≠ second
  reciprocal_pos :
    0 < quittingSingletonSoloEffect club.settlement first second +
      quittingSingletonSoloEffect club.settlement second first

/-- Every dossier supplies a reciprocal support seed for reorganization. -/
theorem nonempty_reciprocalSupportPair
    (dossier : club.ThreeGameDossier) :
    Nonempty dossier.ReciprocalSupportPair := by
  letI : Nonempty ι := dossier.witness.nonempty_players
  obtain ⟨first, second, hfirst, hsecond, hne, hreciprocal⟩ :=
    dossier.witness.exists_supported_pair_pos_reciprocalSoloEffect
      dossier.underwritingProspectus
  exact ⟨{
    first := first
    second := second
    first_mass_pos := hfirst
    second_mass_pos := hsecond
    ne := hne
    reciprocal_pos := hreciprocal }⟩

/-- Consequently no hypothetical counterexample dossier lets the underwriter
win. -/
theorem not_hasWinningUnderwriter
    (dossier : club.ThreeGameDossier) :
    ¬ club.HasWinningUnderwriter := by
  letI : Nonempty ι := dossier.witness.nonempty_players
  rintro ⟨prospectus, haccepted⟩
  exact dossier.not_hasUniformPayoff
    (prospectus.exists_uniformPayoff_of_isAccepted haccepted)

end ThreeGameDossier

/-! ## Arena two: support reorganization -/

/-- A reorganization candidate chooses one exact reachable predecessor edge
and a path returning from its predecessor to its tail.  It is successful when
the chosen edge carries positive closure exposure. -/
structure ReorganizationCandidate where
  edge : QuittingPunishmentFloorReachableEdge club.settlement
  returnPath :
    (quittingPunishmentFloorReachableChargedRelation club.settlement).Path
      edge.current edge.tail

namespace ReorganizationCandidate

variable {club : Mutual ι}

/-- The reorganizer wins by closing a positive-exposure exact return. -/
def IsSuccessful (candidate : club.ReorganizationCandidate) : Prop :=
  0 < candidate.edge.toBoxEdge.absorptionCharge

/-- A successful reorganization is a finite UE certificate. -/
theorem exists_uniformPayoff_of_isSuccessful [Nonempty ι]
    (candidate : club.ReorganizationCandidate)
    (hsuccess : candidate.IsSuccessful) :
    club.HasUniformPayoff :=
  quittingGame_exists_uniformPayoff_of_positive_reachable_return
    club.settlement candidate.edge candidate.returnPath hsuccess

end ReorganizationCandidate

/-- The reorganizer wins if some exact returned ledger edge has positive
closure exposure. -/
def HasWinningReorganization : Prop :=
  ∃ candidate : club.ReorganizationCandidate, candidate.IsSuccessful

namespace ThreeGameDossier

variable {club : Mutual ι}

/-- A support-reorganization attempt must retain the packet's forced
reciprocal pair as provenance for the exact returned ledger candidate.  The
missing theorem is precisely the construction of the returned edge/path from
this support seed and the full coalition settlement cube. -/
structure SupportReorganizationCandidate
    (dossier : club.ThreeGameDossier) where
  support : dossier.ReciprocalSupportPair
  returnedLedger : club.ReorganizationCandidate

namespace SupportReorganizationCandidate

variable {dossier : club.ThreeGameDossier}

/-- The support repair succeeds when its returned exact edge has positive
closure exposure. -/
def IsSuccessful
    (candidate : dossier.SupportReorganizationCandidate) : Prop :=
  candidate.returnedLedger.IsSuccessful

/-- A successful support repair retains the existing direct UE compiler. -/
theorem exists_uniformPayoff_of_isSuccessful
    (candidate : dossier.SupportReorganizationCandidate)
    (hsuccess : candidate.IsSuccessful) :
    club.HasUniformPayoff := by
  letI : Nonempty ι := dossier.witness.nonempty_players
  exact candidate.returnedLedger.exists_uniformPayoff_of_isSuccessful hsuccess

end SupportReorganizationCandidate

/-- The second arena is won by turning the forced reciprocal support seed
into a positive-exposure exact ledger return. -/
def HasWinningSupportReorganization
    (dossier : club.ThreeGameDossier) : Prop :=
  ∃ candidate : dossier.SupportReorganizationCandidate,
    candidate.IsSuccessful

/-- Because every dossier already carries a reciprocal support pair, the
support-seeded and bare positive-return propositions are equivalent there.
This is only provenance bookkeeping: it does not construct the return from
the pair. -/
theorem hasWinningSupportReorganization_iff
    (dossier : club.ThreeGameDossier) :
    dossier.HasWinningSupportReorganization ↔
      club.HasWinningReorganization := by
  constructor
  · rintro ⟨candidate, hsuccess⟩
    exact ⟨candidate.returnedLedger, hsuccess⟩
  · rintro ⟨returnedLedger, hsuccess⟩
    obtain ⟨support⟩ := dossier.nonempty_reciprocalSupportPair
    exact ⟨{
      support := support
      returnedLedger := returnedLedger }, hsuccess⟩

/-- Finite capacity forbids every positive-exposure reorganization return in
a counterexample dossier. -/
theorem not_hasWinningReorganization
    (dossier : club.ThreeGameDossier) :
    ¬ club.HasWinningReorganization := by
  letI : Nonempty ι := dossier.witness.nonempty_players
  rintro ⟨candidate, hsuccess⟩
  exact dossier.not_hasUniformPayoff
    (candidate.exists_uniformPayoff_of_isSuccessful hsuccess)

/-- In particular the support-seeded reorganization arena has no successful
certificate inside a hypothetical dossier. -/
theorem not_hasWinningSupportReorganization
    (dossier : club.ThreeGameDossier) :
    ¬ dossier.HasWinningSupportReorganization := by
  rw [dossier.hasWinningSupportReorganization_iff]
  exact dossier.not_hasWinningReorganization

/-- The optimized run-off ledger carried by the dossier. -/
def optimizedRunoffLedger (dossier : club.ThreeGameDossier) :
    ℕ → QuittingDebtPoint ι :=
  dossier.dynamicTail.tail

/-- **Literal reserve conservation.**  Current dynamic debt equals surviving
terminal debt plus the survival-weighted seams discharged inside the finite
window. -/
theorem runoffDebt_conservation
    (dossier : club.ThreeGameDossier)
    (who : ι) (start fuel : ℕ) :
    (dossier.optimizedRunoffLedger start).2 who =
      quittingJointSurvivalWeight
          (quittingDynamicDebtTailRoots dossier.optimizedRunoffLedger)
          start fuel *
          (dossier.optimizedRunoffLedger (start + fuel)).2 who +
        ∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight
              (quittingDynamicDebtTailRoots dossier.optimizedRunoffLedger)
              start offset *
            quittingDynamicDebtSeam
              (dossier.optimizedRunoffLedger (start + offset)) who := by
  simpa only [optimizedRunoffLedger] using
    dossier.dynamicTail.debt_conservation who start fuel

/-- Every reversed finite segment of the selected run-off ledger is already
a literal punishment-floor exact prefix; no extra endpoint-floor premise is
needed after all-date punishment rationality. -/
def optimizedRunoffPrefix
    (dossier : club.ThreeGameDossier) (horizon : ℕ) :
    QuittingPunishmentFloorFinitePrefix club.settlement :=
  dossier.dynamicTail.tailSegmentPunishmentFloorPrefix horizon

/-- The prefix's charge is exactly the original segment's accumulated
closure exposure. -/
theorem optimizedRunoffPrefix_charge
    (dossier : club.ThreeGameDossier) (horizon : ℕ) :
    (dossier.optimizedRunoffPrefix horizon).charge =
      ∑ time ∈ Finset.range horizon,
        quittingDynamicDebtTailAbsorptionCharge dossier.dynamicTail.tail time := by
  simpa only [optimizedRunoffPrefix] using
    dossier.dynamicTail.tailSegmentPunishmentFloorPrefix_charge horizon

/-- The limiting augmented account is a literal all-`Stay`, zero-charge exact
Nash--Bellman self-loop. -/
theorem limitingZombieAccount_exactSelfLoop
    (dossier : club.ThreeGameDossier) :
    IsQuittingNashBellmanEdge club.settlement
      (dossier.dynamicTail.limitDynamicDebtCap, quittingAllContinueSimplexRoot)
      (dossier.dynamicTail.limitDynamicDebtCap, quittingAllContinueSimplexRoot) :=
  dossier.dynamicTail.limitDynamicDebtCap_exactSelfLoop

/-- Honest late terminal settlement vanishes while the selected advertised
account converges to a positive value retaining the counterexample gap. -/
theorem ownerZombieGap_tendsto_limitValue
    (dossier : club.ThreeGameDossier) :
    Tendsto (fun start ↦
      (dossier.optimizedRunoffLedger start).1.1 dossier.dynamicTail.limit.owner -
        quittingRootSequenceTerminalValue club.settlement
          (quittingDynamicDebtTailRoots dossier.optimizedRunoffLedger)
          dossier.dynamicTail.limit.owner start)
      atTop (nhds (dossier.dynamicTail.limit.value dossier.dynamicTail.limit.owner)) := by
  simpa only [optimizedRunoffLedger] using
    dossier.dynamicTail.ownerSemanticGap_tendsto_limitValue

end ThreeGameDossier

/-! ## Arena one, exit B: normalized periodic audit -/

namespace ThreeGameDossier

variable {club : Mutual ι}

/-- The canonical increasing family of periodically repeated run-off
windows.  Window `n` starts at ledger date `n` and repeats `n+1` rows. -/
def auditFamily (dossier : club.ThreeGameDossier) :
    QuittingPeriodicWindowFamily club.settlement :=
  dossier.dynamicTail.canonicalPeriodicTailWindowFamily

/-- The source-typed window underlying canonical audit `n`.  It begins at
tail date `n` and contains `n+1` roots, before periodic repetition changes the
boundary condition. -/
def canonicalSourceWindow
    (dossier : club.ThreeGameDossier) (window : ℕ) :
    QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots dossier.dynamicTail.tail) :=
  dossier.dynamicTail.finiteRootWindow window (window + 1)

/-- Conditional multi-filer noise vanishes along the canonical source
windows.  This is the rigorous sense in which late audit occupation becomes
singleton-valued; it does not yet identify that occupation with the analytic
prospectus or with a refusal-conditioned law. -/
theorem canonicalSourceWindow_collision_tendsto_zero
    (dossier : club.ThreeGameDossier) :
    Tendsto (fun window ↦
      (dossier.canonicalSourceWindow window).normalizedCollisionMass)
      atTop (nhds 0) := by
  apply
    QuittingFiniteRootWindow.tendsto_normalizedCollisionMass_zero_of_start_tendsto
  · change Tendsto (fun window : ℕ ↦ window) atTop atTop
    exact Filter.tendsto_atTop_mono (fun _ ↦ le_rfl) tendsto_id
  · exact dossier.dynamicTail.rootAbsorptionMass_tendsto_zero

/-- **Ballistic coupling of underwriting and audit.**  No escaping sequence
of positive-absorption source windows can have endpoint displacement little-o
of its absorbed mass.  Otherwise its normalized occupations would manufacture
a complementary prospectus, contradicting the packet defect. -/
theorem not_exists_sublinearAbsorptionReturn
    (dossier : club.ThreeGameDossier)
    (window : ℕ → QuittingFiniteRootWindow
      (quittingDynamicDebtTailRoots dossier.dynamicTail.tail))
    (hstart : Tendsto (fun index ↦ (window index).start) atTop atTop)
    (habsorption : ∀ index, 0 < (window index).absorptionMass)
    (hdrift : Tendsto (fun index ↦
      dossier.dynamicTail.normalizedEndpointDrift (window index))
      atTop (nhds 0)) : False :=
  dossier.dynamicTail.not_exists_sublinearAbsorptionReturn
    window hstart habsorption hdrift

/-- Canonical-window specialization of ballisticity. -/
theorem canonicalNormalizedEndpointDrift_not_tendsto_zero
    (dossier : club.ThreeGameDossier)
    (habsorption : ∀ window,
      0 < (dossier.canonicalSourceWindow window).absorptionMass) :
    ¬ Tendsto (fun window ↦ dossier.dynamicTail.normalizedEndpointDrift
        (dossier.canonicalSourceWindow window)) atTop (nhds 0) := by
  intro hdrift
  exact dossier.not_exists_sublinearAbsorptionReturn
    dossier.canonicalSourceWindow
    (by
      change Tendsto (fun window : ℕ ↦ window) atTop atTop
      exact Filter.tendsto_atTop_mono (fun _ ↦ le_rfl) tendsto_id)
    habsorption hdrift

/-- One auditor's choice of a canonical finite window. -/
structure Audit (dossier : club.ThreeGameDossier) where
  window : ℕ

namespace Audit

variable {dossier : club.ThreeGameDossier}

/-- An audit passes at the dossier's natural half-gap tolerance when every
member's exact periodic best-response gain is at most that tolerance. -/
def Passes (audit : dossier.Audit) : Prop :=
  ∀ who,
    dossier.auditFamily.coordinateGap audit.window who ≤
      dossier.witness.terminalGap / 2

/-- Every audit in a hypothetical dossier is blocked by refusal or by filing
at one concrete phase. -/
theorem not_passes (audit : dossier.Audit) : ¬ audit.Passes := by
  intro hpasses
  obtain ⟨who, hescape⟩ :=
    dossier.dynamicTail.canonicalPeriodicTailWindow_escape audit.window
  have hgap : dossier.witness.terminalGap / 2 <
      dossier.auditFamily.coordinateGap audit.window who := by
    unfold QuittingPeriodicWindowFamily.coordinateGap
    exact (lt_quittingPeriodicWindowBestResponseValue_sub_iff
      club.settlement (dossier.auditFamily.roots audit.window) who
        (dossier.auditFamily.periodIndex audit.window + 1)
        (dossier.auditFamily.delivery audit.window who)
        (dossier.witness.terminalGap / 2)).2 hescape
  exact (not_lt_of_ge (hpasses who)) hgap

end Audit

/-- The auditor wins by finding one canonical restart window that passes. -/
def HasWinningAudit (dossier : club.ThreeGameDossier) : Prop :=
  ∃ audit : dossier.Audit, audit.Passes

/-- No canonical periodic audit passes in a counterexample dossier. -/
theorem not_hasWinningAudit (dossier : club.ThreeGameDossier) :
    ¬ dossier.HasWinningAudit := by
  rintro ⟨audit, hpasses⟩
  exact audit.not_passes hpasses

/-- The stronger landed stabilization: on infinitely many audits one fixed
member uses one fixed kind of objection (refusal, or a phase stop). -/
theorem audit_exists_infinite_fixedMember_fixedBranch
    (dossier : club.ThreeGameDossier) :
    (∃ who, Set.Infinite {window : ℕ |
      dossier.witness.terminalGap / 2 <
        quittingPeriodicWindowRefusalValue club.settlement
          (dossier.auditFamily.roots window) who -
          dossier.auditFamily.delivery window who}) ∨
    (∃ who, Set.Infinite {window : ℕ |
      ∃ phase : Fin (window + 1),
        dossier.witness.terminalGap / 2 <
          quittingPeriodicWindowPhaseStopValue club.settlement
            (dossier.auditFamily.roots window) who phase -
            dossier.auditFamily.delivery window who}) := by
  simpa only [auditFamily] using
    dossier.dynamicTail.exists_infinite_fixedPlayer_fixedBranch

end ThreeGameDossier

/-! ## Exact normalized attachment consumer -/

/-- The denominator-sensitive budget controlling periodic attachment of one
exact word.  `C` is joint survival, `rho` is survival after deleting the
tested member, and the two terms are respectively the phase-stop and refusal
normalizations of endpoint drift. -/
def normalizedAttachmentBudget
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (period : ℕ) : ℝ :=
  max
    (quittingJointSurvivalWeight roots 0 period *
      max (-(value 0 who - value period who)) 0 /
        (1 - quittingJointSurvivalWeight roots 0 period))
    ((quittingOpponentSurvivalWeight roots who 0 period -
          quittingJointSurvivalWeight roots 0 period) *
        max (value 0 who - value period who) 0 /
      ((1 - quittingOpponentSurvivalWeight roots who 0 period) *
        (1 - quittingJointSurvivalWeight roots 0 period)))

/-- Current periodic-seam theorem in mutual language.  Ordinary endpoint
convergence is insufficient: the displacement must be small relative to the
joint and deleted-player survival gaps displayed by the budget. -/
theorem periodicAuditGain_le_normalizedAttachmentBudget
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (who : ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff club.settlement (value (time + 1))
        (roots time))
    (hnash : ∀ time, IsεQuittingRootNash club.settlement
      (value (time + 1)) 0 (roots time))
    (period : ℕ) [NeZero period]
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (hjoint : quittingJointSurvivalWeight roots 0 period < 1)
    (hopponent : quittingOpponentSurvivalWeight roots who 0 period < 1) :
    quittingPeriodicWindowBestResponseValue club.settlement roots who period -
        quittingRootSequenceTerminalValue club.settlement roots who 0 ≤
      normalizedAttachmentBudget roots value who period := by
  exact
    quittingPeriodicWindowBestResponseValue_sub_terminalValue_le_normalizedDrift_of_exactNash
      club.settlement roots who value hpolicy hnash period hperiodic hjoint
        hopponent

/-! ## The exact two-arena / three-certificate UE reduction -/

namespace ThreeGameDossier

variable {club : Mutual ι}

/-- The first arena is won through either of its two exits: an accepted
prospectus or a passing periodic audit.  Ballisticity couples these exits but
does not produce either one. -/
def HasWinningRunoffAudit (dossier : club.ThreeGameDossier) : Prop :=
  club.HasWinningUnderwriter ∨ dossier.HasWinningAudit

/-- The three-certificate resolution target, grouped into its two natural
arenas.  The normalized run-off audit has underwriting and audit exits; the
support-reorganization arena has the charged-return exit. -/
def IsResolved (dossier : club.ThreeGameDossier) : Prop :=
  dossier.HasWinningRunoffAudit ∨
    dossier.HasWinningSupportReorganization

/-- Any resolution branch rules out the dossier and supplies a UE payoff.
The underwriting and reorganization branches are direct compilers; the audit
branch contradicts the dossier's fixed terminal gap. -/
theorem exists_uniformPayoff_of_isResolved [Nonempty ι]
    (dossier : club.ThreeGameDossier)
    (hresolved : dossier.IsResolved) :
    club.HasUniformPayoff := by
  rcases hresolved with hrunoff | hreorganization
  · rcases hrunoff with hunderwriting | haudit
    · obtain ⟨prospectus, haccepted⟩ := hunderwriting
      exact prospectus.exists_uniformPayoff_of_isAccepted haccepted
    · exact (dossier.not_hasWinningAudit haudit).elim
  · obtain ⟨candidate, hsuccess⟩ := hreorganization
    exact candidate.exists_uniformPayoff_of_isSuccessful hsuccess

end ThreeGameDossier

/-- The open producer statement: every dossier exits one of the two arenas
through one of the three certificates. -/
def ThreeCertificateDispatch : Prop :=
  ∀ dossier : club.ThreeGameDossier, dossier.IsResolved

/-- **Exact UE-wise reduction to the three certificates.**  For a
fixed finite settlement table, the assertion that every possible dossier is
dispatched through one of the three certificate exits is equivalent to
existence of a uniform-equilibrium payoff.

The reverse direction is vacuous for the right reason: a UE payoff and a
counterexample dossier are contradictory.  The forward direction uses the
canonical dossier extracted from nonexistence. -/
theorem threeCertificateDispatch_iff_hasUniformPayoff [Nonempty ι] :
    club.ThreeCertificateDispatch ↔ club.HasUniformPayoff := by
  constructor
  · intro hresolve
    by_contra hno
    let witness := quittingTerminalExploitabilityWitnessOfNoUniformPayoff
      club.settlement hno
    let dossier : club.ThreeGameDossier :=
      ThreeGameDossier.ofTerminalExploitabilityWitness witness
    exact hno (dossier.exists_uniformPayoff_of_isResolved
      (hresolve dossier))
  · intro hpayoff dossier
    exact (dossier.not_hasUniformPayoff hpayoff).elim

end Mutual
end SeveranceMutual
end GameTheory
