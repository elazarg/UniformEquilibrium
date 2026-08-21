/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.UnboundedInverseIterate
import UniformEquilibrium.Quitting.Boundary.Repair.CollisionRepairCharacterization
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding
import UniformEquilibrium.Quitting.Root.SuccessorCertificate
import UniformEquilibrium.Quitting.Stationary.Root

/-!
# The three branches of the quitting-game existence characterization

Ashkenazi-Golan, Krasikov, Rainer and Solan, *Absorption paths and equilibria
in quitting games*, Mathematical Programming (2022), Theorem 3.4, state that a
quitting game admits an `ε`-equilibrium for every `ε > 0` if and only if at
least one of three statements holds.  The branches are attributed there to
Simon, *The structure of non-zero-sum stochastic games*, Adv. Appl. Math. 38
(2007), Theorem 3, and Solan and Vieille, *Quitting games*, Math. Oper. Res. 26
(2001).  This file states the three branches as ordinary propositions in the
repository's quitting semantics.  It states no part of the characterization
itself: the equivalence is not formalized anywhere in this development.

* **S.1**, a stationary `ε`-equilibrium for every small `ε`, is
  `QuittingStationaryεEquilibriumExistence`.
* **S.2**, an `ε`-equilibrium in which one player quits surely at the first
  stage and is thereafter punished to within `ε` of its min-max level, is
  `QuittingInstantPunishmentεEquilibriumExistence`.
* **S.3**, an absorbing profile at which every player is sequentially
  `ε`-perfect, is `QuittingSequentiallyεPerfectAbsorbingExistence`, built from
  the one-stage test `QuittingRowεPerfect`.

## Quantifier and shape conventions

The paper quantifies each branch over "every `ε > 0` sufficiently small";
approximate Nash is monotone in its error
(`GameTheory.StochasticGame.IsεAsymptoticNash.mono`), so the two readings agree
and the definitions below quantify over every positive `ε`.
`quittingStationaryεEquilibriumExistence_of_forall_lt` records that transfer
for the stationary branch.

Two presentation choices are deliberate and are not transparent.

* `QuittingInstantPunishmentεEquilibriumExistence` fixes the punishment
  continuation to a constant row played from the second stage on, where the
  paper leaves it an arbitrary behavior profile.  At the level of the
  existence statement the two shapes are equivalent, by
  `GameTheory.quittingInstantPunishmentεEquilibriumExistence_iff_profilePunishment` in
  `UniformEquilibrium/Quitting/Classification/InstantPunishmentEquivalence.lean`,
  which also states the paper's shape as
  `GameTheory.QuittingProfilePunishmentεEquilibriumExistence`.  The
  constant-row form is therefore the canonical one here and the
  arbitrary-profile form is derived from it.
* Branch `S.3` is stated over root sequences rather than over arbitrary
  behavior profiles.  In a quitting game the only history that carries a
  continuation is the all-continue prefix, and
  `GameTheory.quittingTerminalPayoff_eq_rootSequence_profileLiveRoot` rewrites
  any behavior profile's terminal payoff through its live rows, so this is a
  change of presentation rather than a restriction of the strategy class.
  Absorption is `GameTheory.IsCompletelyAbsorbing`, the vanishing of the
  survival product, which is the paper's `P_x(θ < ∞) = 1`.

The one-stage test `QuittingRowεPerfect` writes out the two inequalities of
the paper's Definition 3.1, borrowed there from Solan and Vieille: every
action is worth at most the row's own value plus `ε`, and every action in the
support is worth at least that value minus `ε`.  Both clauses are needed.  A
player quitting with small probability has its continue deviation weighted by
that probability in the first clause, so the clause barely constrains how much
worse quitting is than continuing, while the second clause still requires the
used quitting action to be within `ε` of the row's value.  That weighting is
the same one separating `GameTheory.IsWeightedRow` from
`GameTheory.IsSupportPerfectRow`.
-/

noncomputable section

namespace GameTheory

open StochasticGame QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## S.1: stationary approximate equilibria -/

/-- **Branch S.1.**  For every positive tolerance some stationary profile is a
terminal approximate equilibrium at that tolerance. -/
def QuittingStationaryεEquilibriumExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ root : ι → PMF Bool,
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
      (quittingStationaryProfile reward root)

/-- The paper's "for every sufficiently small `ε`" reading of `S.1` gives the
reading used here, because approximate Nash is monotone in its error. -/
theorem quittingStationaryεEquilibriumExistence_of_forall_lt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {bound : ℝ}
    (hbound : 0 < bound)
    (hsmall : ∀ ε : ℝ, 0 < ε → ε < bound → ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward root)) :
    QuittingStationaryεEquilibriumExistence reward := by
  intro ε hε
  rcases lt_or_ge ε bound with hlt | hge
  · exact hsmall ε hε hlt
  · obtain ⟨root, hroot⟩ := hsmall (bound / 2) (by linarith) (by linarith)
    exact ⟨root, hroot.mono (by linarith)⟩

/-! ## S.2: instant equilibria with a punished sure quitter -/

/-- **Branch S.2**, in the constant-row punishment shape.  For every positive
tolerance there is a player who quits surely at the first stage, and a constant
row played from the second stage on that holds that player within the tolerance
of its exact min-max, such that the resulting profile is a terminal approximate
equilibrium.

The paper leaves the punishment continuation arbitrary; the two existence
statements nevertheless agree, by
`quittingInstantPunishmentεEquilibriumExistence_iff_profilePunishment`. -/
def QuittingInstantPunishmentεEquilibriumExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (quitter : ι) (root punishRow : ι → PMF Bool),
    root quitter = PMF.pure true ∧
      quittingStationaryUnilateralCap reward punishRow quitter ≤
        quittingPunishmentValue reward quitter + ε ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
        (quittingOneStagePunishedProfile reward root punishRow)

/-- A constant row realizing the exact min-max to within any positive
tolerance.  This is the selection that makes the punishment clause of
`QuittingInstantPunishmentεEquilibriumExistence` reachable. -/
theorem exists_punishRow_stationaryUnilateralCap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ punishRow : ι → PMF Bool,
      quittingStationaryUnilateralCap reward punishRow who ≤
        quittingPunishmentValue reward who + ε := by
  haveI : Nonempty (ι → PMF Bool) := ⟨fun _ => PMF.pure false⟩
  have hlt : quittingStationaryPunishmentValue reward who <
      quittingPunishmentValue reward who + ε := by
    rw [← quittingPunishmentValue_eq_stationaryPunishmentValue]
    linarith
  obtain ⟨punishRow, hrow⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨punishRow, hrow.le⟩

/-! ## S.3: sequentially perfect absorbing profiles -/

/-- **One player's one-stage `ε`-perfectness at a product row**: neither pure
action beats the row's own value by more than `ε`, and every action in that
player's support is within `ε` from below. -/
def QuittingPlayerRowεPerfect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (ε : ℝ) : Prop :=
  quittingRootQuitPayoff reward tail root who ≤
        quittingRootSuccessorPayoff reward tail root who + ε ∧
      quittingRootContinuePayoff reward tail root who ≤
        quittingRootSuccessorPayoff reward tail root who + ε ∧
      (root who true ≠ 0 →
        quittingRootSuccessorPayoff reward tail root who - ε ≤
          quittingRootQuitPayoff reward tail root who) ∧
      (root who false ≠ 0 →
        quittingRootSuccessorPayoff reward tail root who - ε ≤
          quittingRootContinuePayoff reward tail root who)

/-- **One-stage `ε`-perfectness of a product row at a continuation vector**,
written out from the paper's Definition 3.1 for every player. -/
def QuittingRowεPerfect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (ε : ℝ) : Prop :=
  ∀ who : ι, QuittingPlayerRowεPerfect reward tail root who ε

/-- Playerwise one-stage perfection is monotone in its error tolerance. -/
theorem QuittingPlayerRowεPerfect.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool} {who : ι} {ε ε' : ℝ}
    (hperfect : QuittingPlayerRowεPerfect reward tail root who ε)
    (hle : ε ≤ ε') :
    QuittingPlayerRowεPerfect reward tail root who ε' := by
  obtain ⟨hquit, hcontinue, hsupportQuit, hsupportContinue⟩ := hperfect
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · intro hused
    linarith [hsupportQuit hused]
  · intro hused
    linarith [hsupportContinue hused]

/-- Collective one-stage perfection is monotone in its error tolerance. -/
theorem QuittingRowεPerfect.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool} {ε ε' : ℝ}
    (hperfect : QuittingRowεPerfect reward tail root ε) (hle : ε ≤ ε') :
    QuittingRowεPerfect reward tail root ε' :=
  fun who => (hperfect who).mono hle

/-- **Branch S.3.**  For every positive tolerance there is an absorbing root
sequence at which every stage's row is `ε`-perfect against that sequence's own
continuation vector. -/
def QuittingSequentiallyεPerfectAbsorbingExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ roots : ℕ → ι → PMF Bool,
    IsCompletelyAbsorbing roots ∧
      ∀ time : ℕ, QuittingRowεPerfect reward
        (quittingRootSequenceTailVector reward roots (time + 1)) (roots time) ε

/-! ## Adapters to landed results -/

/-- **The collision repair lands inside branch S.2.**  Whenever the sure-blocker
collision mechanism's three scalar conditions hold at some rate, the blocker is
a sure first-stage quitter punished to its exact min-max, so the instant branch
holds.  The three conditions are exactly the mechanism's characterization
`quittingCollisionRepairWorks_iff`. -/
theorem quittingInstantPunishmentεEquilibriumExistence_of_collisionRepair
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {owner blocker : ι}
    (hne : owner ≠ blocker) {rate : ℝ} (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1)
    (howner : QuittingCollisionOwnerOptimal reward owner blocker rate)
    (hspectator : QuittingCollisionSpectatorNoJoin reward owner blocker rate)
    (hbalance : QuittingCollisionBlockerBalance reward owner blocker rate) :
    QuittingInstantPunishmentεEquilibriumExistence reward := by
  intro ε hε
  obtain ⟨punishRow, hrow⟩ :=
    exists_punishRow_stationaryUnilateralCap_le reward blocker hε
  refine ⟨blocker, quittingCollisionRepairRoot owner blocker rate hrate0 hrate1,
    punishRow, ?_, hrow, ?_⟩
  · have hblocker : blocker ≠ owner := fun heq => hne heq.symm
    simp [quittingCollisionRepairRoot, quittingSureSetOwnerRoot,
      quittingPureSetRoot, quittingSetAction, hblocker, Function.update_of_ne]
  · exact isεAsymptoticNash_quittingCollisionRepairProfile (hrate0 := hrate0)
      (hrate1 := hrate1) hne howner hspectator hbalance hε.le hrow

end GameTheory
