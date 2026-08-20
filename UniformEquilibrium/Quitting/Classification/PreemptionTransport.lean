/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.Additive.Potentials
import MathUE.DirectedTransport.MaxAffine.Additive
import MathUE.DirectedTransport.MaxAffine.Farkas
import UniformEquilibrium.Quitting.Classification.PreemptionCycle

/-!
# Static preemption transport on payoff cells and player scalars

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
own diagonal minus its cross value.  Charging at least that much keeps the solo
table a lax section of the joined system
(`QuittingSoloPreemptionCycle.isLaxSection_augmentedCellLabel`), and since every
augmented label is a translation the cells are then a potential for the edge
weights (`QuittingSoloPreemptionCycle.isPotential_augmentedCellWeight`).

The joined edges do close: alternating forced edge and observer switch through
a full period returns to the tail cell of phase zero
(`QuittingSoloPreemptionCycle.augmentedCellWalk`), a genuine closed walk of the
augmented graph whose weight is one gap per phase less the total charge
(`QuittingSoloPreemptionCycle.walkWeight_augmentedCellWalk`).  Weak duality
therefore caps that weight at zero.

The pricing behind the cap, proved directly: around a forced cycle the switch
costs total at least the total gap
(`QuittingSoloPreemptionCycle.period_mul_gap_le_sum_observerSwitchCost`), and at
some phase one switch costs the full gap
(`QuittingSoloPreemptionCycle.exists_gap_le_observerSwitchCost`).  The solo
table pays back every gap it grants, so free observer switches are refuted
(`QuittingSoloPreemptionCycle.not_forall_observerSwitchCost_nonpos`).

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

## Production consumers

`quittingAnchoredCyclicOnPathValue_renewal`
(`UniformEquilibrium/Quitting/Cycles/AnchoredRenewalTransport.lean`) gives
genuine positive-slope transport along phases at a fixed spectator coordinate.
The spectator index is frozen there; the observer-switch edges move it.

`QuittingStaticObserverSwitchData` is the class of chargings the regime's own
solo table justifies.  The diagnostic adapter and completed no-go live in
`UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/PreemptionTransport.lean`.
Every such charging has nonpositive augmented weight.

A transport route that is not closed by the above needs different cells, not a
different price on these ones.  Its vertices would have to carry values that
the static terminal table does not determine -- phase values of a profile,
continuation values indexed by the observing player, or debt coordinates --
each with its own semantic provenance, and the forced edges of the preemption
cycle would then relate those values rather than the solo rows.  No such cell
values are defined here or elsewhere in this development, so no interface for
them is stated.
-/

noncomputable section

open Math Math.MaxAffineTransport

namespace GameTheory

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}

/-- A wrap-around index shift leaves a sum over an initial segment unchanged.
Stated for the real line only, which is all the transport candidates below
need. -/
private theorem sum_range_succ_eq_of_wrap {n : ℕ} (h : ℕ → ℝ) (hwrap : h n = h 0) :
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
        quittingSoloReward reward (cycle.vertex (time + 1)) (cycle.vertex (time + 1 + 1)) := rfl

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
    fun edge ↦ (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1 + 1))

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
      (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1 + 1)) := rfl

/-- The edge weights of the augmented payoff-cell graph at a charging of the
switch edges: the gap on a forced edge, the negated charge on the switch edge
of that phase. -/
def augmentedCellWeight (cycle : QuittingSoloPreemptionCycle reward gap) (cost : ℕ → ℝ) :
    Fin cycle.period ⊕ Fin cycle.period → ℝ :=
  Sum.elim (fun _ ↦ gap) fun edge ↦ -cost (edge : ℕ)

omit [Fintype player] [DecidableEq player] in
@[simp] theorem augmentedCellWeight_inl (cycle : QuittingSoloPreemptionCycle reward gap)
    (cost : ℕ → ℝ) (edge : Fin cycle.period) :
    cycle.augmentedCellWeight cost (Sum.inl edge) = gap := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem augmentedCellWeight_inr (cycle : QuittingSoloPreemptionCycle reward gap)
    (cost : ℕ → ℝ) (edge : Fin cycle.period) :
    cycle.augmentedCellWeight cost (Sum.inr edge) = -cost (edge : ℕ) := rfl

/-- The labels of the augmented payoff-cell graph at a charging of the switch
edges: translation by the edge weight of `augmentedCellWeight`, so every label
has slope one. -/
def augmentedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap) (cost : ℕ → ℝ)
    (edge : Fin cycle.period ⊕ Fin cycle.period) : Label :=
  translationLabel (cycle.augmentedCellWeight cost edge)

omit [Fintype player] [DecidableEq player] in
@[simp] theorem slope_augmentedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (cost : ℕ → ℝ) (edge : Fin cycle.period ⊕ Fin cycle.period) :
    (cycle.augmentedCellLabel cost edge).slope = 1 := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem apply_augmentedCellLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (cost : ℕ → ℝ) (edge : Fin cycle.period ⊕ Fin cycle.period) (x : ℝ) :
    (cycle.augmentedCellLabel cost edge).apply x = cycle.augmentedCellWeight cost edge + x :=
  apply_translationLabel _ x

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
      apply_augmentedCellLabel, augmentedCellWeight_inr, quittingPayoffCellValue] at hswitch
    rw [observerSwitchCost_eq]
    linarith
  · intro hcost edge
    cases edge with
    | inl edge =>
        have hedge := (cycle.edge (edge : ℕ)).2
        simp only [source_augmentedCellGraph_inl, target_augmentedCellGraph_inl,
          apply_augmentedCellLabel, augmentedCellWeight_inl, quittingPayoffCellValue]
        linarith
    | inr edge =>
        have hswitch := hcost edge
        rw [observerSwitchCost_eq] at hswitch
        simp only [source_augmentedCellGraph_inr, target_augmentedCellGraph_inr,
          apply_augmentedCellLabel, augmentedCellWeight_inr, quittingPayoffCellValue]
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

omit [Fintype player] [DecidableEq player] in
/-- **The joined system read as a potential problem.**  Every augmented label
is a translation, so a lax section of the labels is a potential for the edge
weights of `augmentedCellWeight` in the sense of
`Math.MaxPlusPotential.IsPotential`, and the weak duality of that module
applies to it. -/
theorem isPotential_augmentedCellWeight (cycle : QuittingSoloPreemptionCycle reward gap)
    {cost : ℕ → ℝ} (hcost : ∀ time : ℕ, cycle.observerSwitchCost time ≤ cost time) :
    Math.MaxPlusPotential.IsPotential cycle.augmentedCellGraph
      (cycle.augmentedCellWeight cost) (quittingPayoffCellValue reward) := by
  intro edge
  have hedge := cycle.isLaxSection_augmentedCellLabel hcost edge
  rw [apply_augmentedCellLabel] at hedge
  linarith

omit [Fintype player] [DecidableEq player] in
/-- The forced edge of a phase lands exactly where that phase's observer switch
starts. -/
theorem target_inl_eq_source_inr_augmentedCellGraph
    (cycle : QuittingSoloPreemptionCycle reward gap) (edge : Fin cycle.period) :
    cycle.augmentedCellGraph.target (Sum.inl edge) =
      cycle.augmentedCellGraph.source (Sum.inr edge) := rfl

/-- The two edges of one phase: its forced edge, then the observer switch out of
the diagonal cell that edge lands on. -/
def phaseStepWalk (cycle : QuittingSoloPreemptionCycle reward gap) (edge : Fin cycle.period) :
    cycle.augmentedCellGraph.Walk (cycle.vertex (edge : ℕ), cycle.vertex ((edge : ℕ) + 1))
      (cycle.vertex ((edge : ℕ) + 1), cycle.vertex ((edge : ℕ) + 1 + 1)) :=
  ((EdgeGraph.Walk.singleton (G := cycle.augmentedCellGraph) (Sum.inl edge)).castFinish
      (cycle.target_inl_eq_source_inr_augmentedCellGraph edge)).concat (Sum.inr edge) rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem edges_phaseStepWalk (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    (cycle.phaseStepWalk edge).edges = [Sum.inl edge, Sum.inr edge] := rfl

omit [Fintype player] [DecidableEq player] in
/-- One phase of the alternating walk carries the gap of its forced edge less
the charge of its observer switch. -/
theorem walkWeight_phaseStepWalk (cycle : QuittingSoloPreemptionCycle reward gap)
    (cost : ℕ → ℝ) (edge : Fin cycle.period) :
    Math.MaxPlusPotential.walkWeight (cycle.augmentedCellWeight cost) (cycle.phaseStepWalk edge)
      = gap - cost (edge : ℕ) := by
  simp only [Math.MaxPlusPotential.walkWeight, edges_phaseStepWalk, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, augmentedCellWeight_inl, augmentedCellWeight_inr]
  ring

/-- The alternating walk of the first `phaseCount` phases, starting at the tail
cell of phase zero: one `phaseStepWalk` per phase, concatenated. -/
def augmentedPrefixWalk (cycle : QuittingSoloPreemptionCycle reward gap) :
    ∀ phaseCount : ℕ, phaseCount ≤ cycle.period →
      cycle.augmentedCellGraph.Walk (cycle.vertex 0, cycle.vertex 1)
        (cycle.vertex phaseCount, cycle.vertex (phaseCount + 1))
  | 0, _ => .nil
  | phaseCount + 1, hphase =>
      (cycle.augmentedPrefixWalk phaseCount (Nat.le_of_succ_le hphase)).append
        (cycle.phaseStepWalk ⟨phaseCount, Nat.lt_of_succ_le hphase⟩)

omit [Fintype player] [DecidableEq player] in
/-- The alternating walk of the first `phaseCount` phases carries one gap per
forced edge and one charge per observer switch. -/
theorem walkWeight_augmentedPrefixWalk (cycle : QuittingSoloPreemptionCycle reward gap)
    (cost : ℕ → ℝ) : ∀ (phaseCount : ℕ) (hphase : phaseCount ≤ cycle.period),
      Math.MaxPlusPotential.walkWeight (cycle.augmentedCellWeight cost)
          (cycle.augmentedPrefixWalk phaseCount hphase)
        = phaseCount * gap - ∑ time ∈ Finset.range phaseCount, cost time
  | 0, _ => by simp [augmentedPrefixWalk]
  | phaseCount + 1, hphase => by
      rw [augmentedPrefixWalk, Math.MaxPlusPotential.walkWeight_append,
        cycle.walkWeight_augmentedPrefixWalk cost phaseCount (Nat.le_of_succ_le hphase),
        cycle.walkWeight_phaseStepWalk cost ⟨phaseCount, Nat.lt_of_succ_le hphase⟩,
        Finset.sum_range_succ]
      push_cast
      ring

omit [Fintype player] [DecidableEq player] in
/-- The alternating walk of a full period returns to its starting cell. -/
theorem augmentedPrefixWalk_finish (cycle : QuittingSoloPreemptionCycle reward gap) :
    (cycle.vertex cycle.period, cycle.vertex (cycle.period + 1)) =
      (cycle.vertex 0, cycle.vertex 1) := by
  have hzero := cycle.vertex_periodic 0
  have hone := cycle.vertex_periodic 1
  rw [zero_add] at hzero
  rw [Nat.add_comm 1 cycle.period] at hone
  rw [hzero, hone]

/-- **The augmented closed walk.**  One turn of the alternating chain -- forced
edge, observer switch, forced edge, ... -- through a full period, closed by the
periodicity of the cycle's vertices. -/
def augmentedCellWalk (cycle : QuittingSoloPreemptionCycle reward gap) :
    cycle.augmentedCellGraph.Walk (cycle.vertex 0, cycle.vertex 1)
      (cycle.vertex 0, cycle.vertex 1) :=
  (cycle.augmentedPrefixWalk cycle.period le_rfl).castFinish cycle.augmentedPrefixWalk_finish

omit [Fintype player] [DecidableEq player] in
/-- The weight of the augmented closed walk: one gap per phase, minus the total
charge of the observer switches. -/
theorem walkWeight_augmentedCellWalk (cycle : QuittingSoloPreemptionCycle reward gap)
    (cost : ℕ → ℝ) :
    Math.MaxPlusPotential.walkWeight (cycle.augmentedCellWeight cost) cycle.augmentedCellWalk
      = (cycle.period : ℝ) * gap - ∑ time ∈ Finset.range cycle.period, cost time := by
  rw [augmentedCellWalk, Math.MaxPlusPotential.walkWeight_castFinish,
    cycle.walkWeight_augmentedPrefixWalk cost cycle.period le_rfl]

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

end GameTheory

end
