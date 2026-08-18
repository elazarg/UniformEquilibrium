/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.MaxAffineFarkasDuality
import MathUE.MaxPlusPotential
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PreemptionCycle
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic

/-!
# The preemption cycle as a max-affine transport graph

`QuittingSoloPreemptionCycle`
(`UniformEquilibrium/Quitting/Classification/PreemptionCycle.lean`) is a
positive-period closed directed walk in the strict solo-preemption relation
`QuittingSoloPreempts reward gap x y`, which unfolds to

`r_y({x}) + gap ≤ r_y({y})`.

This module reads that walk as a labelled graph in the sense of
`Math.MaxAffineTransport`, on two different vertex sets, and the reading
depends on the choice.

## The payoff-cell reading: the forced data is unit-slope transport

On the **payoff-cell** vertex set the vertices are ordered pairs of players and
the cell `(x, y)` carries the single number `r_y({x})`
(`quittingPayoffCellValue`).  The preemption inequality of a phase then reads
as the translation inequality of the edge `(x, y) → (y, y)` of weight `gap`
(`QuittingSoloPreemptionCycle.forcedCellGraph`,
`QuittingSoloPreemptionCycle.forcedCellLabel`,
`QuittingSoloPreemptionCycle.isLaxSection_forcedCellLabel_iff`), which is a
label of slope one, and the solo-reward table itself satisfies every one of
them (`QuittingSoloPreemptionCycle.isLaxSection_forcedCellLabel`).  On payoff
cells the relation therefore does supply transport.

What it does not supply is **concatenation**.  Every forced edge ends on a
diagonal cell `(y, y)` and, because a preemptor differs from its target, none
leaves one (`QuittingSoloPreemptionCycle.target_ne_source_forcedCellGraph`).
Hence no closed walk of the forced graph uses an edge at all
(`QuittingSoloPreemptionCycle.edges_eq_nil_of_closedWalk`), which is the
structural reason the forced system is feasible
(`QuittingSoloPreemptionCycle.exists_isLaxSection_forcedCellLabel`).

## The observer-switch edges and their cost

Joining the forced edge of one phase to the forced edge of the next needs the
within-row edge `(y, y) → (y, z)`, from the diagonal cell of row `y` to the
cell of row `y` read by the next preemptor's target `z`.  The solo table
charges that switch `QuittingSoloPreemptionCycle.observerSwitchCost`, the row's
own diagonal minus its cross value.  Charging at least that much keeps the
solo table a lax section of the joined system
(`QuittingSoloPreemptionCycle.isLaxSection_augmentedCellLabel`), so the
augmented walk closes.

Its total weight is then nonpositive, and sharply so: around a forced cycle the
switch costs total at least the total gap
(`QuittingSoloPreemptionCycle.period_mul_gap_le_sum_observerSwitchCost`), and
at some phase one switch costs the full gap
(`QuittingSoloPreemptionCycle.exists_gap_le_observerSwitchCost`).  The solo
table pays back every gap it grants, so free observer switches are refuted
(`QuittingSoloPreemptionCycle.not_forall_observerSwitchCost_nonpos`) and no
static charging of the switch edges leaves a positive cycle.

## The scalar-per-player compression

Compressing a cell `(x, y)` to one real coordinate per player loses this.  On
the vertex set of players (`QuittingSoloPreemptionCycle.playerTransportGraph`)
the forced datum is a constant label of slope zero
(`QuittingSoloPreemptionCycle.forcedCrossConstantLabel`,
`QuittingSoloPreemptionCycle.slope_forcedCrossConstantLabel`); the bound it
states is attached to the pair, not to the source player, so nothing is
transported.  The solo diagonal satisfies it
(`QuittingSoloPreemptionCycle.isLaxSection_forcedCrossConstantLabel`) and no
Farkas certificate exists
(`QuittingSoloPreemptionCycle.not_exists_farkasCertificate_forcedCrossConstantLabel`).

Reading each scalar edge instead as "the value rises by `gap`" is
`QuittingSoloPreemptionCycle.unforcedTelescopeLabel`.  It is not forced: it
replaces the cross value by the source's own diagonal, that is, it identifies
two players' payoff coordinates.  Its system is infeasible with the explicit
certificate
`QuittingSoloPreemptionCycle.isFarkasCertificate_unforcedTelescopeLabel`, and
the comparison that would license it is refuted
(`QuittingSoloPreemptionCycle.not_forall_soloReward_self_le_crossValue`) --
which on payoff cells is exactly the statement that the observer switches are
not free.

## Where positive-slope transport already exists

`quittingAnchoredCyclicOnPathValue_renewal`
(`UniformEquilibrium/Quitting/Cycles/AnchoredSoloPeriodic.lean`) is a genuine
positive-slope transport along *phases* at a fixed spectator coordinate:
`quittingAnchoredRenewalLabel` has slope `1 - hazard` and the on-path values of
one fixed player form an exact section of it
(`isSection_quittingAnchoredRenewalTransport`).  The spectator index is frozen
there; the observer-switch edges are what would move it.

## The interfaces

`QuittingObserverSwitchData` carries a charging of the switch edges together
with the provenance that the regime's own solo table pays it, and it is
inhabited (`QuittingSoloPreemptionCycle.tightObserverSwitchData`).  The open
obligation is the separate property that the augmented cycle still has positive
total weight (`QuittingObserverSwitchData.augmentedCycleWeight`), and
`QuittingObserverSwitchData.elim` is the checked consumer turning
obligation-holding data into a refutation of the regime.
`QuittingObserverSwitchTransportProducer` is the corresponding production
proposition, and
`quittingObserverSwitchTransportProducer_iff_isEmpty_counterexampleRegime`
records that on static data it is equivalent to nonexistence of the regime,
because `QuittingSoloPreemptionCycle.isEmpty_positiveObserverSwitchData` shows
no table-charged data has the obligation.
-/

noncomputable section

open Math.BoundedDiscrepancy Math.MaxAffineTransport

namespace Math.MaxAffineTransport

/-- **Slope-zero labellings are feasible.**  A label of slope zero ignores the
value at the source of its edge, so a constant candidate large enough to
dominate every edge's value closes every edge inequality at once.  The
statement is graph-generic and belongs with the rest of
`Math.MaxAffineTransport`; it is stated here because this file is its first
consumer. -/
theorem exists_isLaxSection_of_forall_slope_eq_zero {V E : Type*} [Fintype E]
    (G : EdgeGraph V E) (label : E → Label) (hslope : ∀ e : E, (label e).slope = 0) :
    ∃ φ : V → ℝ, IsLaxSection G label φ := by
  refine ⟨fun _ ↦ ∑ e : E, max 0 ((label e).apply 0), fun e ↦ ?_⟩
  have hconst : (label e).apply (∑ e' : E, max 0 ((label e').apply 0))
      = (label e).apply 0 := by
    rcases (label e).floor_cases with hfloor | ⟨c, hfloor⟩
    · rw [Label.apply_of_floor_bot hfloor, Label.apply_of_floor_bot hfloor]
      simp [Label.affinePart, hslope e]
    · rw [Label.apply_of_floor_coe hfloor, Label.apply_of_floor_coe hfloor]
      simp [Label.affinePart, hslope e]
  rw [hconst]
  calc (label e).apply 0 ≤ max 0 ((label e).apply 0) := le_max_right _ _
    _ ≤ ∑ e' : E, max 0 ((label e').apply 0) :=
        Finset.single_le_sum (f := fun e' : E ↦ max 0 ((label e').apply 0))
          (fun e' _ ↦ le_max_left _ _) (Finset.mem_univ e)

/-- A labelling all of whose slopes vanish admits no Farkas certificate. -/
theorem not_exists_farkasCertificate_of_forall_slope_eq_zero {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] (G : EdgeGraph V E) (label : E → Label)
    (hslope : ∀ e : E, (label e).slope = 0) :
    ¬∃ coefficient, IsFarkasCertificate G label coefficient :=
  (exists_isLaxSection_iff_no_farkasCertificate G label).1
    (exists_isLaxSection_of_forall_slope_eq_zero G label hslope)

end Math.MaxAffineTransport

namespace GameTheory

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}

/-- A wrap-around index shift leaves a sum over an initial segment unchanged.
Stated for the real line only, which is all the transport candidates below
need. -/
theorem sum_range_succ_eq_of_wrap {n : ℕ} (h : ℕ → ℝ) (hwrap : h n = h 0) :
    ∑ time ∈ Finset.range n, h (time + 1) = ∑ time ∈ Finset.range n, h time := by
  have hsub := Finset.sum_range_sub h n
  rw [Finset.sum_sub_distrib, hwrap, sub_self, sub_eq_zero] at hsub
  exact hsub

/-- The **payoff cell** of an ordered pair of players: the cell `(x, y)` carries
the payoff `y` receives at `x`'s solo exit.  The first coordinate is the
terminal row and the second is the player reading it. -/
def quittingPayoffCellValue
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (cell : player × player) : ℝ :=
  quittingSoloReward reward cell.1 cell.2

/-- The candidate of the scalar-per-player compression: every player's own solo
exit value, that is, the diagonal of the solo-reward table. -/
def quittingSoloDiagonalCandidate
    (reward : {S : Finset player // S.Nonempty} → Payoff player) (who : player) : ℝ :=
  quittingSoloReward reward who who

omit [Fintype player] [DecidableEq player] in
/-- The diagonal payoff cells carry the solo diagonal. -/
@[simp] theorem quittingPayoffCellValue_diagonal
    (reward : {S : Finset player // S.Nonempty} → Payoff player) (who : player) :
    quittingPayoffCellValue reward (who, who) = quittingSoloDiagonalCandidate reward who := rfl

namespace QuittingSoloPreemptionCycle

variable {gap : ℝ}

/-- The **cross value** of a phase: the payoff its preemptor receives at that
phase's player's solo exit.  This is the left-hand side of the preemption
inequality, and it is the payoff cell of the ordered pair, not a payoff
coordinate of the source player. -/
def crossValue (cycle : QuittingSoloPreemptionCycle reward gap) (time : ℕ) : ℝ :=
  quittingSoloReward reward (cycle.vertex time) (cycle.vertex (time + 1))

omit [Fintype player] [DecidableEq player] in
/-- The cross value of a phase is the payoff cell of that phase's ordered
pair. -/
theorem crossValue_eq_payoffCellValue (cycle : QuittingSoloPreemptionCycle reward gap)
    (time : ℕ) :
    cycle.crossValue time =
      quittingPayoffCellValue reward (cycle.vertex time, cycle.vertex (time + 1)) := rfl

/-! ## Layer 1: the payoff-cell graph

On payoff cells the preemption relation is unit-slope transport. -/

/-- The **forced payoff-cell graph** of a preemption cycle: the vertices are
ordered pairs of players, there is one edge per phase, and the edge of a phase
runs from that phase's cell to the diagonal cell of its preemptor. -/
def forcedCellGraph (cycle : QuittingSoloPreemptionCycle reward gap) :
    EdgeGraph (player × player) (Fin cycle.period) where
  source edge := (cycle.vertex (edge : ℕ), cycle.vertex ((edge : ℕ) + 1))
  target edge := (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1))

omit [Fintype player] [DecidableEq player] in
@[simp] theorem source_forcedCellGraph (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.forcedCellGraph.source edge =
      (cycle.vertex (edge : ℕ), cycle.vertex ((edge : ℕ) + 1)) := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem target_forcedCellGraph (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.forcedCellGraph.target edge =
      (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1)) := rfl

/-- **The label the relation forces on payoff cells.**  The preemption
inequality of a phase bounds the payoff cell at the head by the payoff cell at
the tail plus the gap, so the honest max-affine encoding is translation by the
gap: no floor, and slope one. -/
def forcedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (_edge : Fin cycle.period) : Label :=
  translationLabel gap

omit [Fintype player] [DecidableEq player] in
@[simp] theorem slope_forcedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) : (cycle.forcedCellLabel edge).slope = 1 := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem apply_forcedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) (x : ℝ) : (cycle.forcedCellLabel edge).apply x = gap + x :=
  apply_translationLabel gap x

omit [Fintype player] [DecidableEq player] in
/-- The forced payoff-cell system, written out: one translation inequality per
phase, between the phase's cell and the preemptor's diagonal cell. -/
theorem isLaxSection_forcedCellLabel_iff (cycle : QuittingSoloPreemptionCycle reward gap)
    (φ : player × player → ℝ) :
    IsLaxSection cycle.forcedCellGraph cycle.forcedCellLabel φ ↔
      ∀ edge : Fin cycle.period,
        gap + φ (cycle.vertex (edge : ℕ), cycle.vertex ((edge : ℕ) + 1)) ≤
          φ (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1)) := by
  simp [IsLaxSection]

omit [Fintype player] [DecidableEq player] in
/-- **On payoff cells the forced data is transport.**  The solo-reward table
satisfies the translation inequality of every phase, and it does so as the
preemption relation states it: the inequality of the edge is
`QuittingSoloPreempts` itself, with no comparison between different players'
payoff coordinates. -/
theorem isLaxSection_forcedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap) :
    IsLaxSection cycle.forcedCellGraph cycle.forcedCellLabel
      (quittingPayoffCellValue reward) := by
  rw [isLaxSection_forcedCellLabel_iff]
  intro edge
  have hedge := (cycle.edge (edge : ℕ)).2
  simp only [quittingPayoffCellValue]
  linarith

omit [Fintype player] [DecidableEq player] in
/-- **The forced edges do not concatenate.**  Every forced edge ends on a
diagonal cell, and a preemptor differs from its target, so no forced edge
starts on one. -/
theorem target_ne_source_forcedCellGraph (cycle : QuittingSoloPreemptionCycle reward gap)
    (first second : Fin cycle.period) :
    cycle.forcedCellGraph.target first ≠ cycle.forcedCellGraph.source second := by
  intro hmatch
  rw [target_forcedCellGraph, source_forcedCellGraph, Prod.mk.injEq] at hmatch
  exact (cycle.edge (second : ℕ)).1 (hmatch.2.symm.trans hmatch.1)

omit [Fintype player] [DecidableEq player] in
/-- **No closed walk uses a forced edge.**  A nonempty closed walk would make
the head of some forced edge the tail of another, which
`target_ne_source_forcedCellGraph` forbids. -/
theorem edges_eq_nil_of_closedWalk (cycle : QuittingSoloPreemptionCycle reward gap)
    {base : player × player} (walk : cycle.forcedCellGraph.Walk base base) :
    walk.edges = [] := by
  by_contra hne
  exact cycle.target_ne_source_forcedCellGraph _ _
    ((walk.target_getLast hne).trans (walk.source_head hne).symm)

omit [DecidableEq player] in
/-- **The forced payoff-cell system is feasible, structurally.**  Its graph has
no closed walk carrying any weight at all, by `edges_eq_nil_of_closedWalk`, so
the tropical duality of
`Math.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos` produces
a candidate.  The explicit witness is the solo table
(`isLaxSection_forcedCellLabel`). -/
theorem exists_isLaxSection_forcedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap) :
    ∃ φ : player × player → ℝ, IsLaxSection cycle.forcedCellGraph cycle.forcedCellLabel φ := by
  have hcyc : ∀ (base : player × player) (closed : cycle.forcedCellGraph.Walk base base),
      Math.MaxPlusPotential.walkWeight (fun _ : Fin cycle.period ↦ gap) closed ≤ 0 := by
    intro base closed
    simp [Math.MaxPlusPotential.walkWeight, cycle.edges_eq_nil_of_closedWalk closed]
  obtain ⟨φ, hφ⟩ :=
    (Math.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
      (G := cycle.forcedCellGraph) fun _ : Fin cycle.period ↦ gap).2 hcyc
  exact ⟨φ, (isLaxSection_translationLabel_iff cycle.forcedCellGraph _ φ).2 hφ⟩

/-- **The forced payoff-cell system carries no obstruction.**  A lax section
exists, so by
`Math.MaxAffineTransport.exists_isLaxSection_iff_no_farkasCertificate` no Farkas
certificate does. -/
theorem not_exists_farkasCertificate_forcedCellLabel
    (cycle : QuittingSoloPreemptionCycle reward gap) :
    ¬∃ coefficient, IsFarkasCertificate cycle.forcedCellGraph cycle.forcedCellLabel
      coefficient :=
  (exists_isLaxSection_iff_no_farkasCertificate cycle.forcedCellGraph
      cycle.forcedCellLabel).1
    ⟨quittingPayoffCellValue reward, cycle.isLaxSection_forcedCellLabel⟩

/-! ## Layer 2: the observer-switch edges

Concatenating consecutive forced edges needs a within-row edge out of the
diagonal cell the previous phase lands on. -/

/-- The **observer-switch cost** of a phase at the solo table: the amount by
which the row of that phase's preemptor drops when the reader moves from the
preemptor itself to the next preemptor.  This is the weight the within-row edge
`(y, y) → (y, z)` has to absorb for the solo table to remain a lax section. -/
def observerSwitchCost (cycle : QuittingSoloPreemptionCycle reward gap) (time : ℕ) : ℝ :=
  quittingSoloDiagonalCandidate reward (cycle.vertex (time + 1)) - cycle.crossValue (time + 1)

omit [Fintype player] [DecidableEq player] in
/-- The observer-switch cost written on the solo-reward table. -/
theorem observerSwitchCost_eq (cycle : QuittingSoloPreemptionCycle reward gap) (time : ℕ) :
    cycle.observerSwitchCost time =
      quittingSoloReward reward (cycle.vertex (time + 1)) (cycle.vertex (time + 1)) -
        quittingSoloReward reward (cycle.vertex (time + 1)) (cycle.vertex (time + 2)) := rfl

/-- The **augmented payoff-cell graph**: the forced edges of the phases on the
left, and on the right the within-row observer-switch edges that join each
phase's head to the next phase's tail. -/
def augmentedCellGraph (cycle : QuittingSoloPreemptionCycle reward gap) :
    EdgeGraph (player × player) (Fin cycle.period ⊕ Fin cycle.period) where
  source := Sum.elim
    (fun edge ↦ (cycle.vertex (edge : ℕ), cycle.vertex ((edge : ℕ) + 1)))
    fun edge ↦ (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1))
  target := Sum.elim
    (fun edge ↦ (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1)))
    fun edge ↦ (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 2))

omit [Fintype player] [DecidableEq player] in
@[simp] theorem source_augmentedCellGraph_inl (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.augmentedCellGraph.source (Sum.inl edge) =
      (cycle.vertex (edge : ℕ), cycle.vertex ((edge : ℕ) + 1)) := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem target_augmentedCellGraph_inl (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.augmentedCellGraph.target (Sum.inl edge) =
      (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1)) := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem source_augmentedCellGraph_inr (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.augmentedCellGraph.source (Sum.inr edge) =
      (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1)) := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem target_augmentedCellGraph_inr (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.augmentedCellGraph.target (Sum.inr edge) =
      (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 2)) := rfl

/-- The labels of the augmented payoff-cell graph at a charging of the switch
edges: translation by the gap on a forced edge, translation by the negated
charge on the switch edge of that phase. -/
def augmentedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap) (cost : ℕ → ℝ) :
    Fin cycle.period ⊕ Fin cycle.period → Label :=
  Sum.elim (fun _ ↦ translationLabel gap) fun edge ↦ translationLabel (-cost (edge : ℕ))

omit [Fintype player] [DecidableEq player] in
@[simp] theorem slope_augmentedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (cost : ℕ → ℝ) (edge : Fin cycle.period ⊕ Fin cycle.period) :
    (cycle.augmentedCellLabel cost edge).slope = 1 := by
  cases edge <;> rfl

omit [Fintype player] [DecidableEq player] in
/-- **The joined system is satisfied by the solo table exactly when the switch
edges are charged at least their table cost.**  The forced half holds
outright; the switch half is the definition of `observerSwitchCost`. -/
theorem isLaxSection_augmentedCellLabel_iff (cycle : QuittingSoloPreemptionCycle reward gap)
    (cost : ℕ → ℝ) :
    IsLaxSection cycle.augmentedCellGraph (cycle.augmentedCellLabel cost)
        (quittingPayoffCellValue reward) ↔
      ∀ edge : Fin cycle.period, cycle.observerSwitchCost (edge : ℕ) ≤ cost (edge : ℕ) := by
  constructor
  · intro hφ edge
    have hswitch := hφ (Sum.inr edge)
    simp only [source_augmentedCellGraph_inr, target_augmentedCellGraph_inr,
      augmentedCellLabel, Sum.elim_inr, apply_translationLabel, quittingPayoffCellValue] at hswitch
    rw [observerSwitchCost_eq]
    linarith
  · intro hcost edge
    cases edge with
    | inl edge =>
        have hedge := (cycle.edge (edge : ℕ)).2
        simp only [source_augmentedCellGraph_inl, target_augmentedCellGraph_inl,
          augmentedCellLabel, Sum.elim_inl, apply_translationLabel, quittingPayoffCellValue]
        linarith
    | inr edge =>
        have hswitch := hcost edge
        rw [observerSwitchCost_eq] at hswitch
        simp only [source_augmentedCellGraph_inr, target_augmentedCellGraph_inr,
          augmentedCellLabel, Sum.elim_inr, apply_translationLabel, quittingPayoffCellValue]
        linarith

omit [Fintype player] [DecidableEq player] in
/-- **The joined system closes on the solo table.**  Charging every switch edge
at least its table cost makes the payoff cells a lax section of the forced and
switch edges together. -/
theorem isLaxSection_augmentedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    {cost : ℕ → ℝ} (hcost : ∀ time : ℕ, cycle.observerSwitchCost time ≤ cost time) :
    IsLaxSection cycle.augmentedCellGraph (cycle.augmentedCellLabel cost)
      (quittingPayoffCellValue reward) :=
  (cycle.isLaxSection_augmentedCellLabel_iff cost).2 fun edge ↦ hcost (edge : ℕ)

/-! ## Layer 3: what the switch costs total

The gaps a preemption cycle grants are paid back by the observer switches. -/

omit [Fintype player] [DecidableEq player] in
/-- Summing the preemption inequalities around the closed walk and cancelling
the wrap-around: the cross values plus the full period's worth of gap are
dominated by the solo diagonals. -/
theorem sum_crossValue_add_period_mul_gap_le
    (cycle : QuittingSoloPreemptionCycle reward gap) :
    (∑ time ∈ Finset.range cycle.period, cycle.crossValue time) +
        (cycle.period : ℝ) * gap ≤
      ∑ time ∈ Finset.range cycle.period,
        quittingSoloDiagonalCandidate reward (cycle.vertex time) := by
  have hwrap : quittingSoloDiagonalCandidate reward (cycle.vertex cycle.period)
      = quittingSoloDiagonalCandidate reward (cycle.vertex 0) := by
    have hperiodic := cycle.vertex_periodic 0
    rw [zero_add] at hperiodic
    rw [hperiodic]
  have hshift := sum_range_succ_eq_of_wrap
    (fun time ↦ quittingSoloDiagonalCandidate reward (cycle.vertex time)) hwrap
  have hsum : ∑ time ∈ Finset.range cycle.period, (cycle.crossValue time + gap)
      ≤ ∑ time ∈ Finset.range cycle.period,
          quittingSoloDiagonalCandidate reward (cycle.vertex time) := by
    rw [← hshift]
    exact Finset.sum_le_sum fun time _ ↦ (cycle.edge time).2
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  exact hsum

omit [Fintype player] [DecidableEq player] in
/-- **The switch costs total at least the gaps.**  Around a forced preemption
cycle the observer switches of the payoff-cell reading absorb, in total, at
least the whole period's worth of gap, so the augmented walk of
`augmentedCellGraph` has nonpositive total weight at every table charging. -/
theorem period_mul_gap_le_sum_observerSwitchCost
    (cycle : QuittingSoloPreemptionCycle reward gap) :
    (cycle.period : ℝ) * gap ≤
      ∑ time ∈ Finset.range cycle.period, cycle.observerSwitchCost time := by
  have hvertex : cycle.vertex cycle.period = cycle.vertex 0 := by
    have hperiodic := cycle.vertex_periodic 0
    rw [zero_add] at hperiodic
    exact hperiodic
  have hsucc : cycle.vertex (cycle.period + 1) = cycle.vertex 1 := by
    have hperiodic := cycle.vertex_periodic 1
    rwa [Nat.add_comm 1 cycle.period] at hperiodic
  have hwrap : (fun time ↦ quittingSoloDiagonalCandidate reward (cycle.vertex time)
        - cycle.crossValue time) cycle.period
      = (fun time ↦ quittingSoloDiagonalCandidate reward (cycle.vertex time)
        - cycle.crossValue time) 0 := by
    simp only [quittingSoloDiagonalCandidate, crossValue, hvertex, hsucc, zero_add]
  have hshift := sum_range_succ_eq_of_wrap
    (fun time ↦ quittingSoloDiagonalCandidate reward (cycle.vertex time)
      - cycle.crossValue time) hwrap
  have hsplit : ∑ time ∈ Finset.range cycle.period,
        (quittingSoloDiagonalCandidate reward (cycle.vertex time) - cycle.crossValue time)
      = (∑ time ∈ Finset.range cycle.period,
          quittingSoloDiagonalCandidate reward (cycle.vertex time))
        - ∑ time ∈ Finset.range cycle.period, cycle.crossValue time := by
    rw [Finset.sum_sub_distrib]
  have hforced := cycle.sum_crossValue_add_period_mul_gap_le
  have hcost : ∑ time ∈ Finset.range cycle.period, cycle.observerSwitchCost time
      = ∑ time ∈ Finset.range cycle.period,
          (quittingSoloDiagonalCandidate reward (cycle.vertex time) - cycle.crossValue time) :=
    hshift
  rw [hcost, hsplit]
  linarith

omit [Fintype player] [DecidableEq player] in
/-- **Somewhere the switch costs the full gap.**  The pigeonhole form of
`period_mul_gap_le_sum_observerSwitchCost`: at some phase, moving the reader
within the preemptor's terminal row from the preemptor to the next preemptor
loses at least the gap. -/
theorem exists_gap_le_observerSwitchCost (cycle : QuittingSoloPreemptionCycle reward gap) :
    ∃ time < cycle.period, gap ≤ cycle.observerSwitchCost time := by
  have htotal := cycle.period_mul_gap_le_sum_observerSwitchCost
  have hconst : ∑ _time ∈ Finset.range cycle.period, gap = (cycle.period : ℝ) * gap := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  obtain ⟨time, hmem, hle⟩ :=
    Finset.exists_le_of_sum_le (f := fun _ : ℕ ↦ gap) (g := cycle.observerSwitchCost)
      ⟨0, Finset.mem_range.mpr cycle.period_pos⟩ (by rw [hconst]; exact htotal)
  exact ⟨time, Finset.mem_range.mp hmem, hle⟩

omit [Fintype player] [DecidableEq player] in
/-- **Free observer switches are refuted.**  At a positive gap at least one
switch on the cycle has strictly positive cost, so the within-row moves cannot
all be free. -/
theorem not_forall_observerSwitchCost_nonpos (cycle : QuittingSoloPreemptionCycle reward gap)
    (hgap : 0 < gap) : ¬∀ time : ℕ, cycle.observerSwitchCost time ≤ 0 := by
  intro hfree
  obtain ⟨time, -, hle⟩ := cycle.exists_gap_le_observerSwitchCost
  linarith [hfree time]

/-! ## Layer 4: the scalar-per-player compression no-go

Compressing each payoff cell to one real coordinate per player destroys the
transport of Layer 1. -/

/-- The directed multigraph of the scalar-per-player compression: the vertices
are players, there is one edge per phase, and the edge of a phase runs from
that phase's player to its preemptor.  The fiber over every player is the
line. -/
def playerTransportGraph (cycle : QuittingSoloPreemptionCycle reward gap) :
    EdgeGraph player (Fin cycle.period) where
  source edge := cycle.vertex (edge : ℕ)
  target edge := cycle.vertex ((edge : ℕ) + 1)

omit [Fintype player] [DecidableEq player] in
@[simp] theorem source_playerTransportGraph (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.playerTransportGraph.source edge = cycle.vertex (edge : ℕ) := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem target_playerTransportGraph (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.playerTransportGraph.target edge = cycle.vertex ((edge : ℕ) + 1) := rfl

/-- **The label the relation forces on the scalar-per-player vertex set.**  The
preemption inequality bounds the preemptor's own solo payoff from below by the
cross value plus the gap, and on this vertex set neither side reads any value
at the source, so the honest max-affine encoding is a constant: no floor, the
forced bound as shift, and slope zero.  In the row encoding of
`Math.MaxAffineTransport.rowDelta` this contributes a constant affine row, not
a floor row; the floor of the label is `⊥` and its floor row is vacuous. -/
def forcedCrossConstantLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) : Label :=
  ⟨⊥, cycle.crossValue (edge : ℕ) + gap, 0⟩

omit [Fintype player] [DecidableEq player] in
@[simp] theorem slope_forcedCrossConstantLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) : (cycle.forcedCrossConstantLabel edge).slope = 0 := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem floor_forcedCrossConstantLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) : (cycle.forcedCrossConstantLabel edge).floor = ⊥ := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem apply_forcedCrossConstantLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) (x : ℝ) :
    (cycle.forcedCrossConstantLabel edge).apply x = cycle.crossValue (edge : ℕ) + gap := by
  rw [forcedCrossConstantLabel, Label.apply_mk_bot]
  ring

/-- **The label the additive telescope assumes.**  Translation by the gap on
every edge of the scalar-per-player graph.  This is not the forced label of
`forcedCrossConstantLabel`: it reads the source player's own value where the
preemption inequality reads the cross value `crossValue`, that is, it
identifies the payoff coordinates of two different players. -/
def unforcedTelescopeLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (_edge : Fin cycle.period) : Label :=
  translationLabel gap

omit [Fintype player] [DecidableEq player] in
@[simp] theorem slope_unforcedTelescopeLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) : (cycle.unforcedTelescopeLabel edge).slope = 1 := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem apply_unforcedTelescopeLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) (x : ℝ) :
    (cycle.unforcedTelescopeLabel edge).apply x = gap + x :=
  apply_translationLabel gap x

omit [Fintype player] [DecidableEq player] in
theorem isLaxSection_forcedCrossConstantLabel_iff
    (cycle : QuittingSoloPreemptionCycle reward gap) (φ : player → ℝ) :
    IsLaxSection cycle.playerTransportGraph cycle.forcedCrossConstantLabel φ ↔
      ∀ edge : Fin cycle.period,
        cycle.crossValue (edge : ℕ) + gap ≤ φ (cycle.vertex ((edge : ℕ) + 1)) := by
  simp [IsLaxSection]

omit [Fintype player] [DecidableEq player] in
theorem isLaxSection_unforcedTelescopeLabel_iff
    (cycle : QuittingSoloPreemptionCycle reward gap) (φ : player → ℝ) :
    IsLaxSection cycle.playerTransportGraph cycle.unforcedTelescopeLabel φ ↔
      ∀ edge : Fin cycle.period,
        gap + φ (cycle.vertex (edge : ℕ)) ≤ φ (cycle.vertex ((edge : ℕ) + 1)) := by
  simp [IsLaxSection]

omit [Fintype player] [DecidableEq player] in
/-- **The compressed forced system is satisfied by the solo diagonal.**  This
is the preemption inequality of every phase, read as the lax-section condition
of the constant labels. -/
theorem isLaxSection_forcedCrossConstantLabel
    (cycle : QuittingSoloPreemptionCycle reward gap) :
    IsLaxSection cycle.playerTransportGraph cycle.forcedCrossConstantLabel
      (quittingSoloDiagonalCandidate reward) := by
  rw [isLaxSection_forcedCrossConstantLabel_iff]
  intro edge
  exact (cycle.edge (edge : ℕ)).2

/-- **The compressed forced system carries no obstruction.**  A lax section
exists, so by
`Math.MaxAffineTransport.exists_isLaxSection_iff_no_farkasCertificate` no Farkas
certificate does.  The same conclusion follows from the vanishing slopes alone,
by `Math.MaxAffineTransport.not_exists_farkasCertificate_of_forall_slope_eq_zero`. -/
theorem not_exists_farkasCertificate_forcedCrossConstantLabel
    (cycle : QuittingSoloPreemptionCycle reward gap) :
    ¬∃ coefficient, IsFarkasCertificate cycle.playerTransportGraph
      cycle.forcedCrossConstantLabel coefficient :=
  (exists_isLaxSection_iff_no_farkasCertificate cycle.playerTransportGraph
      cycle.forcedCrossConstantLabel).1
    ⟨quittingSoloDiagonalCandidate reward, cycle.isLaxSection_forcedCrossConstantLabel⟩

omit [Fintype player] in
/-- **The explicit certificate against the additive telescope.**  Unit weight
on the affine row of every edge and none on the floor rows: the rows are
balanced at every vertex because the indicator of a vertex telescopes around
the closed walk, and the total bound is the period times the gap. -/
theorem isFarkasCertificate_unforcedTelescopeLabel
    (cycle : QuittingSoloPreemptionCycle reward gap) (hgap : 0 < gap) :
    IsFarkasCertificate cycle.playerTransportGraph cycle.unforcedTelescopeLabel
      (Sum.elim (fun _ ↦ 1) fun _ ↦ 0) := by
  have hwrap : cycle.vertex cycle.period = cycle.vertex 0 := by
    simpa using cycle.vertex_periodic 0
  refine ⟨?_, ?_, ?_⟩
  · rintro (edge | edge) <;> simp
  · intro v
    have hterm : ∀ edge : Fin cycle.period,
        (Sum.elim (fun _ : Fin cycle.period ↦ (1 : ℝ)) fun _ : Fin cycle.period ↦ (0 : ℝ))
              (Sum.inl edge) *
            rowDelta cycle.playerTransportGraph cycle.unforcedTelescopeLabel (Sum.inl edge) v
          = (if v = cycle.vertex ((edge : ℕ) + 1) then (1 : ℝ) else 0)
            - (if v = cycle.vertex (edge : ℕ) then (1 : ℝ) else 0) := by
      intro edge
      simp [rowDelta]
    rw [Fintype.sum_sum_type]
    simp only [hterm, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Fin.sum_univ_eq_sum_range (fun time ↦
        (if v = cycle.vertex (time + 1) then (1 : ℝ) else 0)
          - (if v = cycle.vertex time then (1 : ℝ) else 0)) cycle.period,
      Finset.sum_range_sub (fun time ↦ if v = cycle.vertex time then (1 : ℝ) else 0)
        cycle.period, hwrap, sub_self]
  · have hterm : ∀ edge : Fin cycle.period,
        (Sum.elim (fun _ : Fin cycle.period ↦ (1 : ℝ)) fun _ : Fin cycle.period ↦ (0 : ℝ))
              (Sum.inl edge) *
            rowBase cycle.unforcedTelescopeLabel (Sum.inl edge) = gap := by
      intro edge
      simp [rowBase, unforcedTelescopeLabel, translationLabel]
    rw [Fintype.sum_sum_type]
    simp only [hterm, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_pos (by exact_mod_cast cycle.period_pos) hgap

/-- **The additive telescope is infeasible.**  The certificate of
`isFarkasCertificate_unforcedTelescopeLabel` rules out every candidate on the
scalar-per-player vertex set. -/
theorem not_exists_isLaxSection_unforcedTelescopeLabel
    (cycle : QuittingSoloPreemptionCycle reward gap) (hgap : 0 < gap) :
    ¬∃ φ : player → ℝ, IsLaxSection cycle.playerTransportGraph cycle.unforcedTelescopeLabel φ :=
  (not_exists_isLaxSection_iff_exists_farkasCertificate cycle.playerTransportGraph
      cycle.unforcedTelescopeLabel).2
    ⟨_, cycle.isFarkasCertificate_unforcedTelescopeLabel hgap⟩

omit [Fintype player] [DecidableEq player] in
/-- **What would close the compressed telescope.**  If at every phase the
player's own solo payoff were dominated by the payoff its preemptor receives at
that same solo row, the forced inequalities would upgrade to the telescope's,
and the solo diagonal would be a lax section of the translation labels.  The
hypothesis compares two different players' payoff coordinates; on payoff cells
it says every observer switch is free. -/
theorem isLaxSection_unforcedTelescopeLabel_of_soloReward_self_le_crossValue
    (cycle : QuittingSoloPreemptionCycle reward gap)
    (hcompare : ∀ time : ℕ,
      quittingSoloDiagonalCandidate reward (cycle.vertex time) ≤ cycle.crossValue time) :
    IsLaxSection cycle.playerTransportGraph cycle.unforcedTelescopeLabel
      (quittingSoloDiagonalCandidate reward) := by
  rw [isLaxSection_unforcedTelescopeLabel_iff]
  intro edge
  have hedge := (cycle.edge (edge : ℕ)).2
  have hcmp := hcompare (edge : ℕ)
  rw [crossValue] at hcmp
  simp only [quittingSoloDiagonalCandidate] at hcmp ⊢
  linarith

/-- **The closing comparison is refuted, not merely missing.**  It would make
the solo diagonal a lax section of a labelling that has none.  On payoff cells
it is the statement that every observer switch is free, which
`not_forall_observerSwitchCost_nonpos` also refutes. -/
theorem not_forall_soloReward_self_le_crossValue
    (cycle : QuittingSoloPreemptionCycle reward gap) (hgap : 0 < gap) :
    ¬∀ time : ℕ,
      quittingSoloDiagonalCandidate reward (cycle.vertex time) ≤ cycle.crossValue time :=
  fun hcompare =>
    cycle.not_exists_isLaxSection_unforcedTelescopeLabel hgap
      ⟨_, cycle.isLaxSection_unforcedTelescopeLabel_of_soloReward_self_le_crossValue hcompare⟩

omit [Fintype player] [DecidableEq player] in
/-- **What the compressed telescope actually yields.**  Summing the preemption
inequalities around the closed walk and cancelling the wrap-around leaves, at
some phase, the full-gap comparison between that phase player's own solo payoff
and the payoff its preemptor receives at that same solo row.  This is an
interpersonal comparison -- two players' payoff coordinates at one terminal row
-- which is exactly what identifying the fibers performs, and it is not a
contradiction. -/
theorem exists_crossValue_add_gap_le_soloReward_self
    (cycle : QuittingSoloPreemptionCycle reward gap) :
    ∃ time < cycle.period,
      cycle.crossValue time + gap ≤ quittingSoloDiagonalCandidate reward (cycle.vertex time) := by
  have hsum : ∑ time ∈ Finset.range cycle.period, (cycle.crossValue time + gap)
      ≤ ∑ time ∈ Finset.range cycle.period,
          quittingSoloDiagonalCandidate reward (cycle.vertex time) := by
    have hforced := cycle.sum_crossValue_add_period_mul_gap_le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact hforced
  obtain ⟨time, hmem, hle⟩ :=
    Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr cycle.period_pos⟩ hsum
  exact ⟨time, Finset.mem_range.mp hmem, hle⟩

end QuittingSoloPreemptionCycle

/-! ## Layer 1, continued: the transport that does exist

The renewal law of an anchored solo-periodic schedule is a genuine
positive-slope transport, but it runs along phases with the spectator
coordinate held fixed. -/

section AnchoredRenewal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- The phase graph of an anchored solo-periodic schedule: one vertex and one
edge per phase, the edge of a phase running from the next phase to it, in the
direction the renewal law computes. -/
def quittingAnchoredRenewalGraph (m : ℕ) : EdgeGraph (Fin m) (Fin m) where
  source phase := finRotate m phase
  target phase := phase

@[simp] theorem source_quittingAnchoredRenewalGraph (phase : Fin m) :
    (quittingAnchoredRenewalGraph m).source phase = finRotate m phase := rfl

@[simp] theorem target_quittingAnchoredRenewalGraph (phase : Fin m) :
    (quittingAnchoredRenewalGraph m).target phase = phase := rfl

/-- The renewal label of a phase in one fixed spectator coordinate: survival
slope `1 - hazard` and shift the hazard-weighted terminal row.  This is the
one-step affine map of `quittingAnchoredCyclicOnPathValue_renewal`. -/
def quittingAnchoredRenewalLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (who : ι) (phase : Fin m) : Label :=
  ⟨⊥, hazard phase * reward (quittingSingletonTerminal (w phase)) who, 1 - hazard phase⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem slope_quittingAnchoredRenewalLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (who : ι) (phase : Fin m) :
    (quittingAnchoredRenewalLabel reward w hazard who phase).slope = 1 - hazard phase := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem apply_quittingAnchoredRenewalLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (who : ι) (phase : Fin m) (x : ℝ) :
    (quittingAnchoredRenewalLabel reward w hazard who phase).apply x =
      hazard phase * reward (quittingSingletonTerminal (w phase)) who
        + (1 - hazard phase) * x :=
  Label.apply_mk_bot _ _ x

omit [Fintype ι] [DecidableEq ι] in
theorem slope_quittingAnchoredRenewalLabel_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) {hazard : Fin m → ℝ} (h1 : ∀ k, hazard k ≤ 1) (who : ι)
    (phase : Fin m) :
    0 ≤ (quittingAnchoredRenewalLabel reward w hazard who phase).slope := by
  simpa using sub_nonneg.mpr (h1 phase)

/-- **The renewal is exact transport at a fixed spectator coordinate.**  The
on-path values of one fixed player, read phase by phase, are a section of the
renewal transport: no inequality, no exactness hypothesis and no positivity of
the hazards is used, only `quittingAnchoredCyclicOnPathValue_renewal`.

The spectator index `who` is a parameter of the labels, not a coordinate the
transport moves.  A preemption inequality changes that index, and moving it is
what the observer-switch edges of
`GameTheory.QuittingSoloPreemptionCycle.augmentedCellGraph` do. -/
theorem isSection_quittingAnchoredRenewalTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (who : ι) :
    (toTransport (quittingAnchoredRenewalGraph m)
        (quittingAnchoredRenewalLabel reward w hazard who)).IsSection
      fun phase ↦ quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who := by
  intro phase
  show (quittingAnchoredRenewalLabel reward w hazard who phase).apply
      (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 (finRotate m phase) who)
    = quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who
  rw [apply_quittingAnchoredRenewalLabel]
  exact (quittingAnchoredCyclicOnPathValue_renewal reward w hazard h0 h1 phase who).symm

/-- The on-path values are in particular a lax section of the renewal
labelling, so the weak duality of `Math.MaxAffineTransport` applies to them. -/
theorem isLaxSection_quittingAnchoredRenewalLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ) (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (who : ι) :
    IsLaxSection (quittingAnchoredRenewalGraph m)
      (quittingAnchoredRenewalLabel reward w hazard who)
      fun phase ↦ quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who :=
  fun phase ↦
    (isSection_quittingAnchoredRenewalTransport reward w hazard h0 h1 who phase).le

end AnchoredRenewal

/-! ## Layer 5: the split interfaces -/

/-- A charging of the observer-switch edges of a forced preemption cycle,
together with its provenance: the regime's own solo-reward table pays the
charge at every switch.

The charge is the game-side datum a transport refutation needs and it is not
arbitrary: `observerSwitchCost_le` ties every entry to the payoff cells the
regime's table actually carries, and it is exactly what makes those cells a lax
section of the joined system (`QuittingObserverSwitchData.isLaxSection`).  The
structure alone is therefore consistent and inhabited
(`GameTheory.QuittingSoloPreemptionCycle.tightObserverSwitchData`); the
obligation is the separate positivity of
`QuittingObserverSwitchData.augmentedCycleWeight`. -/
structure QuittingObserverSwitchData
    (regime : QuittingCounterexampleRegime reward)
    (cycle : QuittingSoloPreemptionCycle reward regime.terminalGap) where
  /-- The weight charged to the observer switch out of each phase's head. -/
  cost : ℕ → ℝ
  /-- The regime's solo table pays the charge at every switch. -/
  observerSwitchCost_le : ∀ time : ℕ, cycle.observerSwitchCost time ≤ cost time

namespace QuittingSoloPreemptionCycle

variable {regime : QuittingCounterexampleRegime reward}

/-- **The trivial switch charging.**  Charging every observer switch exactly
what the regime's solo table loses on it is admissible data, so
`QuittingObserverSwitchData` is not an empty package. -/
def tightObserverSwitchData (regime : QuittingCounterexampleRegime reward)
    (cycle : QuittingSoloPreemptionCycle reward regime.terminalGap) :
    QuittingObserverSwitchData regime cycle where
  cost := cycle.observerSwitchCost
  observerSwitchCost_le _ := le_rfl

instance nonempty_quittingObserverSwitchData
    (regime : QuittingCounterexampleRegime reward)
    (cycle : QuittingSoloPreemptionCycle reward regime.terminalGap) :
    Nonempty (QuittingObserverSwitchData regime cycle) :=
  ⟨tightObserverSwitchData regime cycle⟩

end QuittingSoloPreemptionCycle

namespace QuittingObserverSwitchData

variable {regime : QuittingCounterexampleRegime reward}
variable {cycle : QuittingSoloPreemptionCycle reward regime.terminalGap}

/-- **The charged data closes the joined system on the payoff cells.**  This is
`GameTheory.QuittingSoloPreemptionCycle.isLaxSection_augmentedCellLabel` at the
charge, and it is why data without the obligation is consistent. -/
theorem isLaxSection (data : QuittingObserverSwitchData regime cycle) :
    IsLaxSection cycle.augmentedCellGraph (cycle.augmentedCellLabel data.cost)
      (quittingPayoffCellValue reward) :=
  cycle.isLaxSection_augmentedCellLabel data.observerSwitchCost_le

/-- The total label weight of one turn around
`GameTheory.QuittingSoloPreemptionCycle.augmentedCellGraph` at this charge: one
gap per forced edge, minus the charge of each observer switch. -/
def augmentedCycleWeight (data : QuittingObserverSwitchData regime cycle) : ℝ :=
  (cycle.period : ℝ) * regime.terminalGap -
    ∑ time ∈ Finset.range cycle.period, data.cost time

/-- **The consumer.**  A charging whose turn around the augmented graph still
has positive total weight refutes the regime, because the observer switches of
`GameTheory.QuittingSoloPreemptionCycle.period_mul_gap_le_sum_observerSwitchCost`
already absorb the whole period's worth of gap and the charge dominates them. -/
theorem elim (data : QuittingObserverSwitchData regime cycle)
    (hweight : 0 < data.augmentedCycleWeight) : False := by
  have htotal := cycle.period_mul_gap_le_sum_observerSwitchCost
  have hcharge : ∑ time ∈ Finset.range cycle.period, cycle.observerSwitchCost time
      ≤ ∑ time ∈ Finset.range cycle.period, data.cost time :=
    Finset.sum_le_sum fun time _ ↦ data.observerSwitchCost_le time
  rw [augmentedCycleWeight] at hweight
  linarith

end QuittingObserverSwitchData

namespace QuittingSoloPreemptionCycle

variable {regime : QuittingCounterexampleRegime reward}

/-- **No table-charged data carries the obligation.**  Around a forced
preemption cycle the observer switches already absorb the whole period's worth
of gap (`period_mul_gap_le_sum_observerSwitchCost`), so every admissible charge
leaves the augmented walk at nonpositive weight.  The obstruction a transport
refutation needs cannot come from a charging the static solo table justifies. -/
theorem isEmpty_positiveObserverSwitchData
    (regime : QuittingCounterexampleRegime reward)
    (cycle : QuittingSoloPreemptionCycle reward regime.terminalGap) :
    ¬∃ data : QuittingObserverSwitchData regime cycle, 0 < data.augmentedCycleWeight :=
  fun ⟨data, hweight⟩ ↦ data.elim hweight

end QuittingSoloPreemptionCycle

/-- **The production a payoff-cell transport proof would need.**  Every quitting
counterexample regime supplies, on every strict preemption cycle it forces, a
charging of the observer-switch edges whose augmented closed walk still has
positive total weight.

The content is the obligation, not the data: switch data by itself exists for
every regime and cycle
(`GameTheory.QuittingSoloPreemptionCycle.tightObserverSwitchData`), so this
proposition is not the mere existence of the interface.  It is nonetheless
settled negatively on static data by
`GameTheory.QuittingSoloPreemptionCycle.isEmpty_positiveObserverSwitchData`,
which makes it equivalent to nonexistence of the regime
(`quittingObserverSwitchTransportProducer_iff_isEmpty_counterexampleRegime`); a
charging beating that bound has to be justified by data the solo-reward table
does not contain. -/
def QuittingObserverSwitchTransportProducer
    (reward : {S : Finset player // S.Nonempty} → Payoff player) : Prop :=
  ∀ regime : QuittingCounterexampleRegime reward,
    ∀ cycle : QuittingSoloPreemptionCycle reward regime.terminalGap,
      ∃ data : QuittingObserverSwitchData regime cycle, 0 < data.augmentedCycleWeight

/-- The production proposition rules out the counterexample regime, using the
forced preemption cycle of
`QuittingCounterexampleRegime.nonempty_soloPreemptionCycle`. -/
theorem isEmpty_counterexampleRegime_of_quittingObserverSwitchTransportProducer
    (hproducer : QuittingObserverSwitchTransportProducer reward) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  refine ⟨fun regime ↦ ?_⟩
  obtain ⟨cycle⟩ := regime.nonempty_soloPreemptionCycle
  obtain ⟨data, hweight⟩ := hproducer regime cycle
  exact data.elim hweight

/-- **The consumer of the production proposition.**  A charging of the shape of
`QuittingObserverSwitchData` with positive augmented weight at every regime and
every forced preemption cycle gives every finite quitting game a
uniform-equilibrium payoff, through
`not_exists_uniformEquilibriumPayoff_iff_nonempty_counterexampleRegime`. -/
theorem exists_uniformEquilibriumPayoff_of_quittingObserverSwitchTransportProducer
    (hproducer : QuittingObserverSwitchTransportProducer reward) :
    ∃ payoff : Payoff player,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  exact (isEmpty_counterexampleRegime_of_quittingObserverSwitchTransportProducer
    hproducer).false (quittingCounterexampleRegimeOfNoUniformPayoff reward hno)

/-- **The production proposition is the goal, on static data.**  One direction
is the consumer above; the other is vacuous, because no regime remains to
supply data for.  Recording the equivalence keeps the interface honest: the
decomposition it achieves is that the per-instance obligation is a concrete
inequality about a named quantity, the observer-switch charge, and
`GameTheory.QuittingSoloPreemptionCycle.isEmpty_positiveObserverSwitchData`
settles that inequality negatively whenever the charge is justified by the
solo-reward table. -/
theorem quittingObserverSwitchTransportProducer_iff_isEmpty_counterexampleRegime :
    QuittingObserverSwitchTransportProducer reward ↔
      IsEmpty (QuittingCounterexampleRegime reward) := by
  constructor
  · exact isEmpty_counterexampleRegime_of_quittingObserverSwitchTransportProducer
  · intro hempty regime
    exact (hempty.false regime).elim

end GameTheory

end
