/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Orbit.SelfLoop
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Packet
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.SearchConsequences
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilitySmallPlayers
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityToggles
import UniformEquilibrium.Quitting.Classification.AnalyticWaist
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification

/-!
# Handshake clubs: an exact residual presentation of finite quitting games

This ephemeral probe presents a quitting game as a partnership with exit
clauses.  Every day each member privately chooses `Stay` (`false`) or `Walk`
(`true`).  The first nonempty set of walkers triggers its severance schedule;
perpetual Stay pays zero.  There is only one live history, so behavioral plans
are calendar walk hazards.

The presentation is the identity on games.  Its purpose is to make the
counterexample restrictions literal:

* a normalized singleton source packet is a **prospectus** consisting of a
  fractional sole-walker rota and covered account values;
* a sure exit set is a **walkout pact**;
* owner-solo certification is a **certified rota**;
* punishment-floor prefix charge is **clearing capacity**;
* an exact punishment-floor orbit with summable absorption is a **glacial
  rotation**;
* a finite positive-mass block repeated forever is a **periodic audit**.

The new result is the handshake-ledger inequality.  Every prospectus forces

`sum_i A_ii <= sum_i v_i <= sum_j mu_j (sum_i A_ij)
                  <= max_j sum_i A_ij`.

Thus aggregate handshake insolvency rules out a prospectus and, through the
analytic waist, directly supplies a uniform-equilibrium payoff.

Two distinctions are enforced below.

1. `ProspectusFeasible` is the full packet condition;
   `HandshakeLedgerSolvent` is only its scalar necessary consequence.
2. A prospectus target is a bare no-walk phantom quote, whereas an orbit
   limit is an orbit-attached phantom.  They are not identified.

Finally, summable liquidation intensity is stated correctly: the late-tail
union bound tends to zero.  It leaves positive nonliquidation mass rather
than asserting that the original rotation never liquidates almost surely.

The exact three-fraud evaluation of periodic audits (underpayment, profitable
refusal, and a negative Never ray) is deliberately not claimed here.  It is
proved in the prose solution of
the periodic-window restart analysis, but has not
yet been promoted to a kernel-checked Lean theorem.
-/

noncomputable section

namespace GameTheory
namespace HandshakeClub

open Filter StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A partnership is exactly a severance table indexed by nonempty sets of
simultaneous walkers. -/
structure Club (ι : Type) [Fintype ι] where
  severance : {S : Finset ι // S.Nonempty} → Payoff ι

namespace Club

variable (club : Club ι)

/-- The underlying quitting game; `true` is Walk and `false` is Stay. -/
abbrev game := quittingGame club.severance

/-- A fully general calendar walk plan. -/
abbrev Understanding := club.game.BehaviorProfile

/-- A unilateral calendar walk plan. -/
abbrev WalkPlan (who : ι) := club.game.BehaviorStrategy who

/-- Terminal severance delivered by an understanding. -/
def deliveredPayoff (understanding : club.Understanding) (who : ι) : ℝ :=
  quittingTerminalPayoff club.severance understanding who

/-- The handshake column generated when `owner` walks alone. -/
def handshakeColumn (owner : ι) : Payoff ι :=
  quittingSoloReward club.severance owner

/-- The owner's own handshake. -/
def handshake (owner : ι) : ℝ :=
  club.handshakeColumn owner owner

/-- Total severance distributed by one sole-walker handshake column. -/
def handshakeColumnTotal (owner : ι) : ℝ :=
  ∑ who, club.handshakeColumn owner who

/-- Sum of all members' own handshake promises. -/
def totalHandshakePromises : ℝ :=
  ∑ owner, club.handshake owner

/-- The largest total distribution in a sole-walker handshake column. -/
def maxHandshakeColumnTotal [Nonempty ι] : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty club.handshakeColumnTotal

/-- Scalar ledger solvency.  This is necessary for a prospectus but is not
the full prospectus condition. -/
def HandshakeLedgerSolvent [Nonempty ι] : Prop :=
  club.totalHandshakePromises ≤ club.maxHandshakeColumnTotal

/-- A prospectus is exactly the analytic waist's normalized singleton source
packet: rota weights and covered book accounts. -/
abbrev Prospectus :=
  QuittingNormalizedSingletonSourcePacket club.severance

/-- Full prospectus feasibility, kept distinct from scalar ledger solvency. -/
def ProspectusFeasible : Prop := Nonempty club.Prospectus

namespace Prospectus

variable {club : Club ι}

/-- Every account lies above its owner's handshake. -/
theorem totalHandshakePromises_le_accounts
    (prospectus : club.Prospectus) :
    club.totalHandshakePromises ≤ ∑ who, prospectus.target who := by
  unfold totalHandshakePromises handshake handshakeColumn
  exact Finset.sum_le_sum fun who _ => prospectus.solo_le_target who

/-- Coordinatewise coverage implies aggregate coverage. -/
theorem accounts_le_singletonMixtureTotal
    (prospectus : club.Prospectus) :
    (∑ who, prospectus.target who) ≤
      ∑ who, quittingSingletonMixture club.severance prospectus.mass who :=
  Finset.sum_le_sum fun who _ => prospectus.mix_ge_target who

/-- Summing the covered singleton mixture and exchanging its two finite sums
gives the rota-weighted average of handshake-column totals. -/
theorem singletonMixtureTotal_eq_weightedColumnTotal
    (prospectus : club.Prospectus) :
    (∑ who, quittingSingletonMixture club.severance prospectus.mass who) =
      ∑ owner, prospectus.mass owner * club.handshakeColumnTotal owner := by
  unfold quittingSingletonMixture handshakeColumnTotal handshakeColumn
  simp only [quittingSoloReward, quittingSingletonTerminal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro owner _
  rw [Finset.mul_sum]

/-- The prospectus covers all handshake promises by a convex average of the
sole-walker column totals. -/
theorem totalHandshakePromises_le_weightedColumnTotal
    (prospectus : club.Prospectus) :
    club.totalHandshakePromises ≤
      ∑ owner, prospectus.mass owner * club.handshakeColumnTotal owner := by
  exact prospectus.totalHandshakePromises_le_accounts.trans <|
    prospectus.accounts_le_singletonMixtureTotal.trans_eq
      prospectus.singletonMixtureTotal_eq_weightedColumnTotal

/-- A convex average of handshake-column totals is at most their maximum. -/
theorem weightedColumnTotal_le_max [Nonempty ι]
    (prospectus : club.Prospectus) :
    (∑ owner, prospectus.mass owner * club.handshakeColumnTotal owner) ≤
      club.maxHandshakeColumnTotal := by
  calc
    (∑ owner, prospectus.mass owner * club.handshakeColumnTotal owner) ≤
        ∑ owner, prospectus.mass owner * club.maxHandshakeColumnTotal := by
      apply Finset.sum_le_sum
      intro owner _
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' club.handshakeColumnTotal (Finset.mem_univ owner))
        (prospectus.mass_nonneg owner)
    _ = club.maxHandshakeColumnTotal := by
      rw [← Finset.sum_mul, prospectus.mass_sum, one_mul]

/-- **Handshake-ledger inequality.**  Prospectus feasibility forces scalar
ledger solvency. -/
theorem handshakeLedgerSolvent [Nonempty ι]
    (prospectus : club.Prospectus) :
    club.HandshakeLedgerSolvent :=
  prospectus.totalHandshakePromises_le_weightedColumnTotal.trans
    prospectus.weightedColumnTotal_le_max

end Prospectus

/-- Aggregate ledger insolvency rules out every prospectus. -/
theorem not_prospectusFeasible_of_not_ledgerSolvent [Nonempty ι]
    (hinsolvent : ¬ club.HandshakeLedgerSolvent) :
    ¬ club.ProspectusFeasible := by
  rintro ⟨prospectus⟩
  exact hinsolvent prospectus.handshakeLedgerSolvent

/-- **Ledger cashout through the analytic waist.**  If total own-handshake
promises exceed every singleton column's total distribution, the club has a
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_not_ledgerSolvent [Nonempty ι]
    (hinsolvent : ¬ club.HandshakeLedgerSolvent) :
    ∃ payoff : Payoff ι,
      club.game.IsUniformEquilibriumPayoff none payoff := by
  rcases quittingGame_uniformPayoff_or_normalizedSingletonSourcePacket
      club.severance with hpayoff | hprospectus
  · exact hpayoff
  · obtain ⟨prospectus⟩ := hprospectus
    exact absurd (Prospectus.handshakeLedgerSolvent prospectus) hinsolvent

/-- Simplex state carrying a book account and the all-Stay row. -/
def noWalkPoint (_club : Club ι)
    (account : Payoff ι) : QuittingNashBellmanPoint ι :=
  (account, quittingAllContinueSimplexRoot)

/-- A bare phantom account is an exact Nash--Bellman self-loop at all-Stay. -/
def IsBarePhantomAccount (account : Payoff ι) : Prop :=
  IsQuittingNashBellmanEdge club.severance
    (club.noWalkPoint account) (club.noWalkPoint account)

/-- Every prospectus target is already a bare all-Stay phantom account. -/
theorem Prospectus.target_isBarePhantomAccount
    (prospectus : club.Prospectus) :
    club.IsBarePhantomAccount prospectus.target := by
  unfold IsBarePhantomAccount noWalkPoint
  constructor
  · change prospectus.target = quittingRootSuccessorPayoff club.severance
      prospectus.target
      (quittingRootOfSimplex
        (quittingAllContinueSimplexRoot (ι := ι)))
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      quittingRootSuccessorPayoff_allContinueRoot_eq]
  · change IsεQuittingRootEndpointNash club.severance prospectus.target 0
      (quittingRootOfSimplex
        (quittingAllContinueSimplexRoot (ι := ι)))
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    exact quittingAllContinueRoot_isZeroNash_of_singleton_le
      club.severance prospectus.target prospectus.solo_le_target

/-- A walkout pact is exactly a sure exit set. -/
def IsWalkoutPact (walkers : Finset ι) : Prop :=
  IsQuittingSureExitSet club.severance walkers

/-- A certified rota is one owner and one fixed positive walk hazard accepted
by the owner-solo certification theorem. -/
def HasCertifiedRota : Prop :=
  ∃ (owner : ι) (hazard : PMF Bool),
    0 < (hazard true).toReal ∧
    0 ≤ club.handshake owner ∧
    ∀ other, other ≠ owner →
      (hazard false).toReal * club.handshake other +
          (hazard true).toReal *
            quittingSingletonCollisionReward club.severance owner other ≤
        club.handshakeColumn owner other

/-- A certified rota cashes out to a uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_certifiedRota
    (hrota : club.HasCertifiedRota) :
    ∃ payoff : Payoff ι,
      club.game.IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨owner, hazard, hpositive, howner, hinactive⟩ := hrota
  exact ⟨club.handshakeColumn owner,
    isUniformEquilibriumPayoff_soloReward_of_inactive club.severance
      owner hazard hpositive howner hinactive⟩

/-- Exact finite clearing capacity of all security-floor-anchored accounting
prefixes. -/
def HasFiniteClearingCapacity : Prop :=
  quittingPunishmentFloorPrefixChargeCapacity club.severance ≠ ⊤

/-- A club satisfying all currently landed necessary filters for a
counterexample.  This is a residual superset, not a characterization of
nonexistence. -/
structure IsResidual where
  four_members : 4 ≤ Fintype.card ι
  live_handshake : ∃ owner, 0 < club.handshake owner
  no_walkout_pact : ∀ walkers, ¬ club.IsWalkoutPact walkers
  no_certified_rota : ¬ club.HasCertifiedRota
  prospectus_feasible : club.ProspectusFeasible
  finite_clearing_capacity : club.HasFiniteClearingCapacity

namespace IsResidual

variable {club : Club ι}

/-- Every quitting terminal exploitability witness produces a residual handshake club. -/
theorem ofTerminalExploitabilityWitness
    (witness : QuittingTerminalExploitabilityWitness club.severance) :
    club.IsResidual where
  four_members := by
    have hcard := witness.three_lt_card
    omega
  live_handshake := by
    obtain ⟨owner, howner⟩ := witness.exists_terminalGap_le_soloReward
    exact ⟨owner, witness.terminalGap_pos.trans_le howner⟩
  no_walkout_pact := witness.not_isQuittingSureExitSet
  no_certified_rota := by
    intro hrota
    exact witness.not_exists_uniformEquilibriumPayoff
      (club.exists_uniformEquilibriumPayoff_of_certifiedRota hrota)
  prospectus_feasible :=
    witness.nonempty_normalizedSingletonSourcePacket
  finite_clearing_capacity := witness.prefixChargeCapacity_ne_top

end IsResidual

/-- **The residual reduction is theorem-backed.**  If every residual
handshake club has a stable understanding, then every finite quitting game
over the player type has a uniform-equilibrium payoff. -/
theorem solve_residual_implies_solve_all [Nonempty ι]
    (solver : ∀ candidate : Club ι, candidate.IsResidual →
      ∃ payoff : Payoff ι,
        candidate.game.IsUniformEquilibriumPayoff none payoff) :
    ∀ candidate : Club ι, ∃ payoff : Payoff ι,
      candidate.game.IsUniformEquilibriumPayoff none payoff := by
  intro candidate
  by_contra hno
  let witness := quittingTerminalExploitabilityWitnessOfNoUniformPayoff
    candidate.severance hno
  exact hno (solver candidate (.ofTerminalExploitabilityWitness witness))

/-- An arbitrary exact security-floor accounting orbit. -/
abbrev AccountingOrbit :=
  QuittingPunishmentFloorInfiniteOrbit club.severance

/-- A glacial rotation is an exact accounting orbit with summable joint walk
intensity. -/
structure GlacialRotation where
  orbit : club.AccountingOrbit
  intensity_summable : Summable (fun time =>
    quittingRootAbsorptionMass (orbit.roots time))

namespace GlacialRotation

variable {club : Club ι}

/-- Finite capacity makes every exact accounting orbit glacial. -/
def ofTerminalExploitabilityWitness
    (witness : QuittingTerminalExploitabilityWitness club.severance)
    (orbit : club.AccountingOrbit) : club.GlacialRotation where
  orbit := orbit
  intensity_summable := witness.infiniteOrbit_absorptionMass_summable orbit

/-- Nonnegative-real presentation of the rotation's joint walk intensity. -/
def intensityNNReal (rotation : club.GlacialRotation) (time : ℕ) : NNReal :=
  ⟨quittingRootAbsorptionMass (rotation.orbit.roots time),
    rotation.orbit.absorptionMass_nonneg time⟩

/-- Union-bound budget for dissolution after a late restart. -/
def lateDissolutionUnionBound
    (rotation : club.GlacialRotation) (start : ℕ) : NNReal :=
  ∑' offset, rotation.intensityNNReal (offset + start)

/-- **Correct glacial probability statement.**  The late-tail union bound on
ever dissolving tends to zero.  In particular the probability of perpetual
survival from a late restart tends to one; this does not assert almost-sure
survival from the original date. -/
theorem lateDissolutionUnionBound_tendsto_zero
    (rotation : club.GlacialRotation) :
    Tendsto rotation.lateDissolutionUnionBound atTop (nhds 0) := by
  exact NNReal.tendsto_sum_nat_add rotation.intensityNNReal

/-- The terminal exploitability witness attaches a limiting phantom account to every
glacial rotation.  This limit is not identified with any prospectus target. -/
theorem exists_orbitAttachedPhantomAccount
    (rotation : club.GlacialRotation)
    (witness : QuittingTerminalExploitabilityWitness club.severance) :
    ∃ limit : Payoff ι,
      (∀ who, Tendsto (fun time => rotation.orbit.value time who) atTop
        (nhds (limit who))) ∧
      limit ∈ quittingPunishmentFloorForwardCarrier club.severance ∧
      (∀ who, quittingPunishmentValue club.severance who ≤ limit who) ∧
      club.IsBarePhantomAccount limit := by
  simpa only [IsBarePhantomAccount, noWalkPoint] using
    witness.infiniteOrbit_exists_selfLoop_limit rotation.orbit

end GlacialRotation

/-- A positive-mass finite accounting window selected for periodic audit. -/
structure PeriodicAudit (rotation : club.GlacialRotation) where
  start : ℕ
  length : ℕ
  length_pos : 0 < length
  positive_mass : 0 < ∑ offset ∈ Finset.range length,
    quittingRootAbsorptionMass (rotation.orbit.roots (start + offset))

namespace PeriodicAudit

variable {club : Club ι} {rotation : club.GlacialRotation}

/-- Repeat the selected window's independent walk rows forever. -/
def rows (audit : PeriodicAudit club rotation)
    (time : ℕ) : ι → PMF Bool :=
  rotation.orbit.roots (audit.start + time % audit.length)

/-- The genuine quitting-game understanding generated by the repeated audit
window. -/
def understanding
    (audit : PeriodicAudit club rotation) : club.Understanding :=
  quittingRootSequenceProfile club.severance audit.rows 0

end PeriodicAudit

/-! ## The four-member cyclic stress club fails the prospectus ledger -/

namespace CyclicStress

/-- Four cyclic club members. -/
abbrev Member := Fin 4

/-- The periodic-window stress table: a sole walker receives `1`, its cyclic
successor receives `2`, and everyone else receives `0`; every collision pays
zero. -/
def severance
    (terminal : {S : Finset Member // S.Nonempty}) : Payoff Member :=
  if terminal.1 = {0} then ![1, 2, 0, 0]
  else if terminal.1 = {1} then ![0, 1, 2, 0]
  else if terminal.1 = {2} then ![0, 0, 1, 2]
  else if terminal.1 = {3} then ![2, 0, 0, 1]
  else 0

/-- The stress table as a handshake club. -/
def stressClub : Club Member where
  severance := severance

@[simp] theorem handshake (owner : Member) :
    stressClub.handshake owner = 1 := by
  fin_cases owner <;>
    simp [Club.handshake, Club.handshakeColumn, quittingSoloReward,
      stressClub, severance]

@[simp] theorem handshakeColumnTotal (owner : Member) :
    stressClub.handshakeColumnTotal owner = 3 := by
  fin_cases owner <;>
    simp [Club.handshakeColumnTotal, Club.handshakeColumn,
      quittingSoloReward, stressClub, severance, Fin.sum_univ_four] <;>
    norm_num

theorem totalHandshakePromises :
    stressClub.totalHandshakePromises = 4 := by
  simp [Club.totalHandshakePromises]

theorem maxHandshakeColumnTotal :
    stressClub.maxHandshakeColumnTotal = 3 := by
  unfold Club.maxHandshakeColumnTotal
  have hconstant : stressClub.handshakeColumnTotal = fun _ => 3 := by
    funext owner
    exact handshakeColumnTotal owner
  rw [hconstant]
  simp

/-- The stress club's aggregate promises are `4`, while every sole-walker
column distributes only `3`. -/
theorem not_handshakeLedgerSolvent :
    ¬ stressClub.HandshakeLedgerSolvent := by
  rw [Club.HandshakeLedgerSolvent, totalHandshakePromises,
    maxHandshakeColumnTotal]
  norm_num

/-- Consequently the stress club admits no analytic-waist prospectus. -/
theorem not_prospectusFeasible :
    ¬ stressClub.ProspectusFeasible :=
  stressClub.not_prospectusFeasible_of_not_ledgerSolvent
    not_handshakeLedgerSolvent

/-- The analytic waist therefore supplies a uniform-equilibrium payoff for
the cyclic stress club; aggregate-deficit window blocking cannot survive the
packet filter. -/
theorem exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff Member,
      stressClub.game.IsUniformEquilibriumPayoff none payoff :=
  stressClub.exists_uniformEquilibriumPayoff_of_not_ledgerSolvent
    not_handshakeLedgerSolvent

end CyclicStress

end Club
end HandshakeClub
end GameTheory
