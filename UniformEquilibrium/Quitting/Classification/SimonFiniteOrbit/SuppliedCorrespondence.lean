/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.CompactEdgeBudgetedPrefixRelation
import MathUE.Topology.SimonViabilityQuestion
import Mathlib.Analysis.Convex.Hull
import UniformEquilibrium.Quitting.Boundary.Repair.SupportEnlargementAlternative
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedBranch
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Supplied finite-orbit correspondences for the corrected Simon obstruction

This module states the finite-orbit data used by the corrected Simon
correspondence program in production quitting-game semantics. It does not
prove the paper's necessity implication.

At error `ε`, the carrier consists of payoff vectors which are individually
rational up to `ε` and lie within Euclidean distance `ε` of the convex hull
of the terminal reward vectors and zero. An edge from `tail` to `current` is
witnessed by one product root which is support-locally `ε`-optimal at `tail`
and whose one-stage successor payoff is `current`.

`QuittingSimonFiniteNearOrbitConditionAt` spells out the finite clause with
the source's `1 < bound` guard. Its carrier-subtype form is proved equivalent
to `Math.Topology.HasArbitrarilyLargeFiniteOrbitVariationWith`.

The capstone takes `SuppliedQuittingSimonFiniteOrbitNecessity` as an explicit
hypothesis. That proposition contains the corrected stationarily-generated
and instant exclusions and the missing implication from behavioral
approximate-equilibrium existence to the finite-orbit condition. No source
theorem, strategy extraction, or certificate producer is asserted here.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open Math.Topology.SimonViability
open scoped BigOperators

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Simon's feasible payoff set: the convex hull of all terminal reward
vectors together with the zero payoff from eternal continuation. -/
def QuittingSimonFeasiblePayoff
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (point : Payoff iota) : Prop :=
  point ∈ convexHull ℝ (Set.range reward ∪ {0})

/-- Individual rationality at error `ε`. Here "rational" has its
game-theoretic meaning, not rational-number coordinates. -/
def QuittingSimonRationalPayoffAt
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) (point : Payoff iota) : Prop :=
  ∀ who, quittingPunishmentValue reward who - ε ≤ point who

/-- Euclidean `ε`-nearness to Simon's feasible payoff set. -/
def QuittingSimonNearFeasiblePayoffAt
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) (point : Payoff iota) : Prop :=
  ∃ feasible, QuittingSimonFeasiblePayoff reward feasible ∧
    Math.Topology.SimonViability.euclideanDist point feasible ≤ ε

/-- The corrected finite-orbit carrier at one error scale. -/
def QuittingSimonFiniteOrbitCarrier
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) :=
  {point : Payoff iota //
    QuittingSimonRationalPayoffAt reward ε point ∧
      QuittingSimonNearFeasiblePayoffAt reward ε point}

/-- A production-semantic `F_ε` edge. The root support conditions are the
two endpoint inequalities of the source correspondence. -/
def QuittingSimonFEdgeAt
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) (tail current : Payoff iota) : Prop :=
  ∃ root : iota → PMF Bool,
    IsQuittingRootSupportApproxNash reward tail ε root ∧
      quittingRootSuccessorPayoff reward tail root = current

/-- The `F_ε` graph on the ambient payoff space. -/
def QuittingSimonFGraphAt
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) : Set (Payoff iota × Payoff iota) :=
  {pair | QuittingSimonFEdgeAt reward ε pair.1 pair.2}

/-- The source-shaped `F_ε` correspondence obtained from the edge graph. -/
def QuittingSimonFCorrespondenceAt
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) : Math.Topology.Correspondence (Payoff iota) (Payoff iota) :=
  Math.Topology.SimonViability.graphCorrespondence
    (QuittingSimonFGraphAt reward ε)

/-- A finite orbit of the source-shaped `F_ε` correspondence. -/
def QuittingSimonFOrbitAt
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) {length : ℕ}
    (point : Fin (length + 1) → Payoff iota) : Prop :=
  Math.Topology.IsFiniteOrbit
    (QuittingSimonFCorrespondenceAt reward ε) point

/-- The `F_ε` graph restricted to the rational, near-feasible carrier. -/
def QuittingSimonFiniteOrbitGraphAt
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) :
    Set (QuittingSimonFiniteOrbitCarrier reward ε ×
      QuittingSimonFiniteOrbitCarrier reward ε) :=
  {pair | QuittingSimonFEdgeAt reward ε pair.1.1 pair.2.1}

/-- Euclidean edge variation in the orientation printed in the finite-orbit
clause: distance from the next point to the preceding point. -/
def QuittingSimonFiniteOrbitCost
    {reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota}
    {ε : ℝ}
    (first next : QuittingSimonFiniteOrbitCarrier reward ε) : ℝ :=
  Math.Topology.SimonViability.euclideanDist next.1 first.1

/-- Exact finite-cell Lyapunov data on the rational, near-feasible Simon
carrier. Cell coverage and every local inequality remain supplied proof data. -/
def HasQuittingSimonFiniteCellLyapunovCertificate
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) {Cell : Type*} [Fintype Cell]
    (cell : Cell → Set (QuittingSimonFiniteOrbitCarrier reward ε))
    (localPotential : Cell → QuittingSimonFiniteOrbitCarrier reward ε → ℝ)
    (constant lower upper : ℝ) : Prop :=
  Math.Topology.HasFiniteCellLyapunovCertificate
    (Math.Topology.SimonViability.graphCorrespondence
      (QuittingSimonFiniteOrbitGraphAt reward ε))
    QuittingSimonFiniteOrbitCost cell localPotential constant lower upper

/-- The source-shaped finite near-orbit condition at one positive scale.
Positivity is deliberately not built into the definition. -/
def QuittingSimonFiniteNearOrbitConditionAt
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) : Prop :=
  ∀ bound : ℝ, 1 < bound →
    ∃ (length : ℕ) (point : Fin (length + 1) → Payoff iota),
      QuittingSimonFOrbitAt reward ε point ∧
        (∀ index,
          QuittingSimonRationalPayoffAt reward ε (point index) ∧
            QuittingSimonNearFeasiblePayoffAt reward ε (point index)) ∧
        bound ≤ Math.Topology.finiteOrbitVariationWith
          (fun first next ↦
            Math.Topology.SimonViability.euclideanDist next first) point

/-- The corrected finite near-orbit condition at every positive error. -/
def QuittingSimonFiniteNearOrbitCondition
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → QuittingSimonFiniteNearOrbitConditionAt reward ε

/-- Packaging every carrier point as a subtype identifies the source-shaped
finite condition with the generic arbitrarily-large finite variation
predicate. -/
theorem quittingSimonFiniteNearOrbitConditionAt_iff_arbitrarilyLargeVariation
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (ε : ℝ) :
    QuittingSimonFiniteNearOrbitConditionAt reward ε ↔
      Math.Topology.HasArbitrarilyLargeFiniteOrbitVariationWith
        (Math.Topology.SimonViability.graphCorrespondence
          (QuittingSimonFiniteOrbitGraphAt reward ε))
        QuittingSimonFiniteOrbitCost := by
  constructor
  · intro hcondition bound
    let sourceBound := max bound 2
    have hsourceBound : 1 < sourceBound :=
      (show (1 : ℝ) < 2 by norm_num).trans_le (le_max_right bound 2)
    obtain ⟨length, point, horbit, hcarrier, hvariation⟩ :=
      hcondition sourceBound hsourceBound
    let carrierPoint : Fin (length + 1) →
        QuittingSimonFiniteOrbitCarrier reward ε :=
      fun index ↦ ⟨point index, hcarrier index⟩
    refine ⟨length, carrierPoint, ?_, ?_⟩
    · intro index
      change QuittingSimonFEdgeAt reward ε
        (point index.castSucc) (point index.succ)
      exact horbit index
    · have hbound : bound ≤ sourceBound := le_max_left bound 2
      exact hbound.trans (by
        simpa only [Math.Topology.finiteOrbitVariationWith,
          QuittingSimonFiniteOrbitCost, carrierPoint] using hvariation)
  · intro hunbounded bound hbound
    obtain ⟨length, carrierPoint, horbit, hvariation⟩ := hunbounded bound
    let point : Fin (length + 1) → Payoff iota :=
      fun index ↦ (carrierPoint index).1
    refine ⟨length, point, ?_, ?_, ?_⟩
    · intro index
      change QuittingSimonFEdgeAt reward ε
        ((carrierPoint index.castSucc).1) ((carrierPoint index.succ).1)
      exact horbit index
    · intro index
      exact (carrierPoint index).2
    · simpa only [Math.Topology.finiteOrbitVariationWith,
        QuittingSimonFiniteOrbitCost, point] using hvariation

/-- A bounded strict Lyapunov potential on one carrier graph refutes the
finite near-orbit condition at that scale. This theorem does not produce the
potential. -/
theorem not_quittingSimonFiniteNearOrbitConditionAt_of_potential_bounds
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    {ε constant lower upper : ℝ}
    (potential : QuittingSimonFiniteOrbitCarrier reward ε → ℝ)
    (hconstant : 0 < constant)
    (hlower : ∀ state, lower ≤ potential state)
    (hupper : ∀ state, potential state ≤ upper)
    (hdecrease : ∀ pair ∈ QuittingSimonFiniteOrbitGraphAt reward ε,
      potential pair.2 ≤
        potential pair.1 - constant *
          QuittingSimonFiniteOrbitCost pair.1 pair.2) :
    ¬QuittingSimonFiniteNearOrbitConditionAt reward ε := by
  rw [quittingSimonFiniteNearOrbitConditionAt_iff_arbitrarilyLargeVariation]
  exact
    not_hasArbitrarilyLargeFiniteGraphOrbitVariationWith_of_potential_bounds
      hconstant hlower hupper hdecrease

/-- A supplied finite-cell certificate directly refutes the finite near-orbit
condition at its error scale. No cell decomposition is produced here. -/
theorem not_quittingSimonFiniteNearOrbitConditionAt_of_finiteCellCertificate
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    {ε constant lower upper : ℝ} {Cell : Type*} [Fintype Cell]
    {cell : Cell → Set (QuittingSimonFiniteOrbitCarrier reward ε)}
    {localPotential :
      Cell → QuittingSimonFiniteOrbitCarrier reward ε → ℝ}
    (hconstant : 0 < constant)
    (hcertificate : HasQuittingSimonFiniteCellLyapunovCertificate
      reward ε cell localPotential constant lower upper) :
    ¬QuittingSimonFiniteNearOrbitConditionAt reward ε := by
  rw [quittingSimonFiniteNearOrbitConditionAt_iff_arbitrarilyLargeVariation]
  exact
    Math.Topology.not_hasArbitrarilyLargeFiniteOrbitVariationWith_of_finiteCellCertificate
      hconstant hcertificate

/-- The corrected Simon necessity direction, isolated as supplied data. The
repository proves no inhabitant of this proposition. -/
def SuppliedQuittingSimonFiniteOrbitNecessity
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota) :
    Prop :=
  ¬QuittingStationarilyGeneratedApproximateEquilibria reward →
    ¬QuittingInstantPunishmentεEquilibriumExistence reward →
      QuittingApproximateEquilibriumExistence reward →
        QuittingSimonFiniteNearOrbitCondition reward

/-- Conditional obstruction capstone: supplied corrected necessity, both
branch exclusions, and one exact strict Lyapunov certificate rule out
behavioral approximate equilibria. -/
theorem not_quittingApproximateEquilibriumExistence_of_suppliedSimonNecessity
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hnecessity : SuppliedQuittingSimonFiniteOrbitNecessity reward)
    (hgenerated : ¬QuittingStationarilyGeneratedApproximateEquilibria reward)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    {ε constant lower upper : ℝ} (hε : 0 < ε)
    (potential : QuittingSimonFiniteOrbitCarrier reward ε → ℝ)
    (hconstant : 0 < constant)
    (hlower : ∀ state, lower ≤ potential state)
    (hupper : ∀ state, potential state ≤ upper)
    (hdecrease : ∀ pair ∈ QuittingSimonFiniteOrbitGraphAt reward ε,
      potential pair.2 ≤
        potential pair.1 - constant *
          QuittingSimonFiniteOrbitCost pair.1 pair.2) :
    ¬QuittingApproximateEquilibriumExistence reward := by
  intro hequilibrium
  have horbit := hnecessity hgenerated hinstant hequilibrium ε hε
  exact
    (not_quittingSimonFiniteNearOrbitConditionAt_of_potential_bounds
      reward potential hconstant hlower hupper hdecrease) horbit

/-- The same conditional obstruction rules out every uniform-equilibrium
payoff in the production quitting semantics. -/
theorem not_exists_uniformEquilibriumPayoff_of_suppliedSimonNecessity
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hnecessity : SuppliedQuittingSimonFiniteOrbitNecessity reward)
    (hgenerated : ¬QuittingStationarilyGeneratedApproximateEquilibria reward)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    {ε constant lower upper : ℝ} (hε : 0 < ε)
    (potential : QuittingSimonFiniteOrbitCarrier reward ε → ℝ)
    (hconstant : 0 < constant)
    (hlower : ∀ state, lower ≤ potential state)
    (hupper : ∀ state, potential state ≤ upper)
    (hdecrease : ∀ pair ∈ QuittingSimonFiniteOrbitGraphAt reward ε,
      potential pair.2 ≤
        potential pair.1 - constant *
          QuittingSimonFiniteOrbitCost pair.1 pair.2) :
    ¬∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hnoApproximate :=
    not_quittingApproximateEquilibriumExistence_of_suppliedSimonNecessity
      reward hnecessity hgenerated hinstant hε potential hconstant
        hlower hupper hdecrease
  rw [quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors,
    ← quittingApproximateEquilibriumExistence_iff_behavior]
  exact hnoApproximate

/-- Equivalently, the conditional obstruction yields a fixed positive
terminal exploitability gap against every behavior profile. -/
theorem exists_terminalExploitabilityGap_of_suppliedSimonNecessity
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hnecessity : SuppliedQuittingSimonFiniteOrbitNecessity reward)
    (hgenerated : ¬QuittingStationarilyGeneratedApproximateEquilibria reward)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    {ε constant lower upper : ℝ} (hε : 0 < ε)
    (potential : QuittingSimonFiniteOrbitCarrier reward ε → ℝ)
    (hconstant : 0 < constant)
    (hlower : ∀ state, lower ≤ potential state)
    (hupper : ∀ state, potential state ≤ upper)
    (hdecrease : ∀ pair ∈ QuittingSimonFiniteOrbitGraphAt reward ε,
      potential pair.2 ≤
        potential pair.1 - constant *
          QuittingSimonFiniteOrbitCost pair.1 pair.2) :
    ∃ gap : ℝ, 0 < gap ∧ HasTerminalExploitabilityGap reward gap := by
  apply
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).mp
  exact not_exists_uniformEquilibriumPayoff_of_suppliedSimonNecessity
    reward hnecessity hgenerated hinstant hε potential hconstant
      hlower hupper hdecrease

/-- A supplied finite-cell certificate and the supplied Simon necessity bridge
yield a fixed positive terminal exploitability gap. Neither input is produced
by this theorem. -/
theorem
    exists_terminalExploitabilityGap_of_suppliedSimonNecessity_of_finiteCellCertificate
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hnecessity : SuppliedQuittingSimonFiniteOrbitNecessity reward)
    (hgenerated : ¬QuittingStationarilyGeneratedApproximateEquilibria reward)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    {ε constant lower upper : ℝ} {Cell : Type*} [Fintype Cell]
    (hε : 0 < ε)
    {cell : Cell → Set (QuittingSimonFiniteOrbitCarrier reward ε)}
    {localPotential :
      Cell → QuittingSimonFiniteOrbitCarrier reward ε → ℝ}
    (hconstant : 0 < constant)
    (hcertificate : HasQuittingSimonFiniteCellLyapunovCertificate
      reward ε cell localPotential constant lower upper) :
    ∃ gap : ℝ, 0 < gap ∧ HasTerminalExploitabilityGap reward gap := by
  have hnoApproximate : ¬QuittingApproximateEquilibriumExistence reward := by
    intro hequilibrium
    have horbit := hnecessity hgenerated hinstant hequilibrium ε hε
    exact
      (not_quittingSimonFiniteNearOrbitConditionAt_of_finiteCellCertificate
        reward hconstant hcertificate) horbit
  have hnoUniform : ¬∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
    rw [quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors,
      ← quittingApproximateEquilibriumExistence_iff_behavior]
    exact hnoApproximate
  exact
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).mp hnoUniform

end GameTheory
