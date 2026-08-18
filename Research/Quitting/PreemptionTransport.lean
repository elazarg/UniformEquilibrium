/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.MaxAffineFarkasDuality
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
`Math.MaxAffineTransport`: the vertices are players, there is one edge per
phase, and the fiber over every player is the line.

## What the relation forces

The inequality of an edge bounds one number at the target vertex -- the target
player's own solo payoff `r_y({y})` -- from below by `r_y({x}) + gap`.  The
lower bound is a number attached to the *pair*: it is the payoff **to `y`** at
`x`'s solo row, not any payoff coordinate of `x`.  Encoded as a max-affine
label, the forced datum is therefore a constant, that is, a label of slope
zero (`QuittingSoloPreemptionCycle.forcedCrossFloorLabel`,
`QuittingSoloPreemptionCycle.slope_forcedCrossFloorLabel`); the regime forces a
floor at the target, not a map from the source fiber to the target fiber.

Slope-zero labellings are unconditionally feasible over finitely many edges
(`Math.MaxAffineTransport.exists_isLaxSection_of_forall_slope_eq_zero`), and
here an explicit lax section is available before that general fact: the
diagonal of the solo-reward table
(`QuittingSoloPreemptionCycle.isLaxSection_forcedCrossFloorLabel`).  So the
forced labelled system admits no Farkas certificate at all
(`QuittingSoloPreemptionCycle.not_exists_farkasCertificate_forcedCrossFloorLabel`).
That is the finding: on the vertex set of players with one real coordinate
each, the preemption relation supplies no transport and hence no obstruction.

## What the additive telescope assumes

Reading each edge instead as "the value rises by `gap`" is the labelling
`QuittingSoloPreemptionCycle.unforcedTelescopeLabel`, translation by `gap` on
every edge.  It is *not* forced by the relation: it replaces the cross value
`r_y({x})` by the source's own diagonal `r_x({x})`.  Its lax-section system is
infeasible, with the explicit certificate
`QuittingSoloPreemptionCycle.isFarkasCertificate_unforcedTelescopeLabel`
(unit weight on each affine row, none on the floor rows), so the naive
telescope fails exactly at a positive cycle and for no other reason.

Run against the relation itself, the telescope does not produce a
contradiction; it produces the interpersonal comparison
`QuittingSoloPreemptionCycle.exists_crossValue_add_gap_le_soloReward_self`:
somewhere on the cycle a player's own solo payoff beats, by the full gap, the
payoff its preemptor receives at that same solo row.  Two different players'
payoff coordinates are compared there, which is what the identification of
fibers silently does, and
`QuittingSoloPreemptionCycle.not_forall_soloReward_self_le_crossValue` records
that the comparison closing the telescope is refuted rather than merely
missing.

## Where transport does exist

`quittingAnchoredCyclicOnPathValue_renewal`
(`UniformEquilibrium/Quitting/Cycles/AnchoredSoloPeriodic.lean`) is a genuine
positive-slope transport, but along *phases* at a fixed spectator coordinate:
`quittingAnchoredRenewalLabel` has slope `1 - hazard` and the on-path values
of one fixed player form an exact section of it
(`isSection_quittingAnchoredRenewalTransport`), with no exactness hypothesis.
The spectator index is frozen there.  The preemption inequalities move it, and
that move is what carries no edge map.

## The missing producer

`QuittingPreemptionTransportProducer` states the shape of the production a
transport proof of the quitting conjecture would need, and
`exists_uniformEquilibriumPayoff_of_quittingPreemptionTransportProducer` wires
it to the conjecture.  `QuittingPreemptionTransportRefutation.label_ne_forcedCrossFloorLabel`
records that the labels of such a production cannot be the ones the relation
currently supplies.
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

/-- The candidate of the preemption transport: every player's own solo exit
value, that is, the diagonal of the solo-reward table. -/
def quittingSoloDiagonalCandidate
    (reward : {S : Finset player // S.Nonempty} → Payoff player) (who : player) : ℝ :=
  quittingSoloReward reward who who

namespace QuittingSoloPreemptionCycle

variable {gap : ℝ}

/-! ## Layer 1: the labelled system -/

/-- The directed multigraph of a preemption cycle: the vertices are players,
there is one edge per phase, and the edge of a phase runs from that phase's
player to its preemptor. -/
def transportGraph (cycle : QuittingSoloPreemptionCycle reward gap) :
    EdgeGraph player (Fin cycle.period) where
  source edge := cycle.vertex (edge : ℕ)
  target edge := cycle.vertex ((edge : ℕ) + 1)

omit [Fintype player] [DecidableEq player] in
@[simp] theorem source_transportGraph (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.transportGraph.source edge = cycle.vertex (edge : ℕ) := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem target_transportGraph (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) :
    cycle.transportGraph.target edge = cycle.vertex ((edge : ℕ) + 1) := rfl

/-- The **cross value** of a phase: the payoff its preemptor receives at that
phase's player's solo exit.  This is the left-hand side of the preemption
inequality, and it is a function of the ordered pair, not of the source
player. -/
def crossValue (cycle : QuittingSoloPreemptionCycle reward gap) (time : ℕ) : ℝ :=
  quittingSoloReward reward (cycle.vertex time) (cycle.vertex (time + 1))

/-- **The label the relation forces.**  The preemption inequality of a phase
bounds the preemptor's own solo payoff from below by the cross value plus the
gap.  Neither side reads any value at the source vertex, so the honest
max-affine encoding is a constant label: no floor, shift the forced bound, and
slope zero. -/
def forcedCrossFloorLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) : Label :=
  ⟨⊥, cycle.crossValue (edge : ℕ) + gap, 0⟩

omit [Fintype player] [DecidableEq player] in
@[simp] theorem slope_forcedCrossFloorLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) : (cycle.forcedCrossFloorLabel edge).slope = 0 := rfl

omit [Fintype player] [DecidableEq player] in
@[simp] theorem apply_forcedCrossFloorLabel (cycle : QuittingSoloPreemptionCycle reward gap)
    (edge : Fin cycle.period) (x : ℝ) :
    (cycle.forcedCrossFloorLabel edge).apply x = cycle.crossValue (edge : ℕ) + gap := by
  rw [forcedCrossFloorLabel, Label.apply_mk_bot]
  ring

/-- **The label the additive telescope assumes.**  Translation by the gap on
every edge.  This is not the forced label of `forcedCrossFloorLabel`: it reads
the source vertex's own value where the preemption inequality reads the cross
value `crossValue`, that is, it identifies the payoff coordinates of two
different players. -/
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
theorem isLaxSection_forcedCrossFloorLabel_iff
    (cycle : QuittingSoloPreemptionCycle reward gap) (φ : player → ℝ) :
    IsLaxSection cycle.transportGraph cycle.forcedCrossFloorLabel φ ↔
      ∀ edge : Fin cycle.period,
        cycle.crossValue (edge : ℕ) + gap ≤ φ (cycle.vertex ((edge : ℕ) + 1)) := by
  simp [IsLaxSection]

omit [Fintype player] [DecidableEq player] in
theorem isLaxSection_unforcedTelescopeLabel_iff
    (cycle : QuittingSoloPreemptionCycle reward gap) (φ : player → ℝ) :
    IsLaxSection cycle.transportGraph cycle.unforcedTelescopeLabel φ ↔
      ∀ edge : Fin cycle.period,
        gap + φ (cycle.vertex (edge : ℕ)) ≤ φ (cycle.vertex ((edge : ℕ) + 1)) := by
  simp [IsLaxSection]

omit [Fintype player] [DecidableEq player] in
/-- **The forced labelled system is satisfied by the solo diagonal.**  This is
the preemption inequality of every phase, read as the lax-section condition of
the constant labels. -/
theorem isLaxSection_forcedCrossFloorLabel (cycle : QuittingSoloPreemptionCycle reward gap) :
    IsLaxSection cycle.transportGraph cycle.forcedCrossFloorLabel
      (quittingSoloDiagonalCandidate reward) := by
  rw [isLaxSection_forcedCrossFloorLabel_iff]
  intro edge
  exact (cycle.edge (edge : ℕ)).2

/-! ## Layer 2: the consumers -/

/-- **The forced system carries no obstruction.**  A lax section exists, so by
`Math.MaxAffineTransport.exists_isLaxSection_iff_no_farkasCertificate` no
Farkas certificate does.  The same conclusion follows from the vanishing
slopes alone, by
`Math.MaxAffineTransport.not_exists_farkasCertificate_of_forall_slope_eq_zero`. -/
theorem not_exists_farkasCertificate_forcedCrossFloorLabel
    (cycle : QuittingSoloPreemptionCycle reward gap) :
    ¬∃ coefficient, IsFarkasCertificate cycle.transportGraph cycle.forcedCrossFloorLabel
      coefficient :=
  (exists_isLaxSection_iff_no_farkasCertificate cycle.transportGraph
      cycle.forcedCrossFloorLabel).1
    ⟨quittingSoloDiagonalCandidate reward, cycle.isLaxSection_forcedCrossFloorLabel⟩

omit [Fintype player] in
/-- **The explicit certificate against the additive telescope.**  Unit weight
on the affine row of every edge and none on the floor rows: the rows are
balanced at every vertex because the indicator of a vertex telescopes around
the closed walk, and the total bound is the period times the gap. -/
theorem isFarkasCertificate_unforcedTelescopeLabel
    (cycle : QuittingSoloPreemptionCycle reward gap) (hgap : 0 < gap) :
    IsFarkasCertificate cycle.transportGraph cycle.unforcedTelescopeLabel
      (Sum.elim (fun _ ↦ 1) fun _ ↦ 0) := by
  have hwrap : cycle.vertex cycle.period = cycle.vertex 0 := by
    simpa using cycle.vertex_periodic 0
  refine ⟨?_, ?_, ?_⟩
  · rintro (edge | edge) <;> simp
  · intro v
    have hterm : ∀ edge : Fin cycle.period,
        (Sum.elim (fun _ : Fin cycle.period ↦ (1 : ℝ)) fun _ : Fin cycle.period ↦ (0 : ℝ))
              (Sum.inl edge) *
            rowDelta cycle.transportGraph cycle.unforcedTelescopeLabel (Sum.inl edge) v
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
`isFarkasCertificate_unforcedTelescopeLabel` rules out every candidate. -/
theorem not_exists_isLaxSection_unforcedTelescopeLabel
    (cycle : QuittingSoloPreemptionCycle reward gap) (hgap : 0 < gap) :
    ¬∃ φ : player → ℝ, IsLaxSection cycle.transportGraph cycle.unforcedTelescopeLabel φ :=
  (not_exists_isLaxSection_iff_exists_farkasCertificate cycle.transportGraph
      cycle.unforcedTelescopeLabel).2
    ⟨_, cycle.isFarkasCertificate_unforcedTelescopeLabel hgap⟩

omit [Fintype player] [DecidableEq player] in
/-- **What would close the telescope.**  If at every phase the player's own
solo payoff were dominated by the payoff its preemptor receives at that same
solo row, the forced inequalities would upgrade to the telescope's, and the
solo diagonal would be a lax section of the translation labels.  The
hypothesis compares two different players' payoff coordinates; nothing in
`QuittingSoloPreempts` supplies it. -/
theorem isLaxSection_unforcedTelescopeLabel_of_soloReward_self_le_crossValue
    (cycle : QuittingSoloPreemptionCycle reward gap)
    (hcompare : ∀ time : ℕ,
      quittingSoloDiagonalCandidate reward (cycle.vertex time) ≤ cycle.crossValue time) :
    IsLaxSection cycle.transportGraph cycle.unforcedTelescopeLabel
      (quittingSoloDiagonalCandidate reward) := by
  rw [isLaxSection_unforcedTelescopeLabel_iff]
  intro edge
  have hedge := (cycle.edge (edge : ℕ)).2
  have hcmp := hcompare (edge : ℕ)
  rw [crossValue] at hcmp
  simp only [quittingSoloDiagonalCandidate] at hcmp ⊢
  linarith

/-- **The closing comparison is refuted, not merely missing.**  It would make
the solo diagonal a lax section of a labelling that has none. -/
theorem not_forall_soloReward_self_le_crossValue
    (cycle : QuittingSoloPreemptionCycle reward gap) (hgap : 0 < gap) :
    ¬∀ time : ℕ,
      quittingSoloDiagonalCandidate reward (cycle.vertex time) ≤ cycle.crossValue time :=
  fun hcompare =>
    cycle.not_exists_isLaxSection_unforcedTelescopeLabel hgap
      ⟨_, cycle.isLaxSection_unforcedTelescopeLabel_of_soloReward_self_le_crossValue hcompare⟩

omit [Fintype player] [DecidableEq player] in
/-- **What the telescope actually yields.**  Summing the preemption
inequalities around the closed walk and cancelling the wrap-around leaves, at
some phase, the full-gap comparison between that phase player's own solo
payoff and the payoff its preemptor receives at that same solo row.  This is
an interpersonal comparison -- two players' payoff coordinates at one terminal
row -- which is exactly what identifying the fibers performs, and it is not a
contradiction. -/
theorem exists_crossValue_add_gap_le_soloReward_self
    (cycle : QuittingSoloPreemptionCycle reward gap) :
    ∃ time < cycle.period,
      cycle.crossValue time + gap ≤ quittingSoloDiagonalCandidate reward (cycle.vertex time) := by
  have hwrap : quittingSoloDiagonalCandidate reward (cycle.vertex cycle.period)
      = quittingSoloDiagonalCandidate reward (cycle.vertex 0) := by
    have := cycle.vertex_periodic 0
    rw [zero_add] at this
    rw [this]
  have hshift := sum_range_succ_eq_of_wrap
    (fun time ↦ quittingSoloDiagonalCandidate reward (cycle.vertex time)) hwrap
  have hsum : ∑ time ∈ Finset.range cycle.period, (cycle.crossValue time + gap)
      ≤ ∑ time ∈ Finset.range cycle.period,
          quittingSoloDiagonalCandidate reward (cycle.vertex time) := by
    rw [← hshift]
    exact Finset.sum_le_sum fun time _ ↦ (cycle.edge time).2
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
transport moves.  A preemption inequality changes that index, and this family
of edge maps therefore does not supply the map it would need. -/
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

/-! ## Layer 3: the missing producer -/

/-- Data that a transport-style refutation of a quitting counterexample regime
on one of its preemption cycles would have to produce: max-affine labels on
the cycle's edges, a candidate satisfying them, and a Farkas certificate
against them.

The two duties are separated deliberately.  The candidate is the game-side
half: in an intended proof it would be built from the values of a hypothetical
profile, and `isLaxSection` would hold because the labels are inequalities the
regime forces at those values.  The certificate is the transport-side half.
`QuittingPreemptionTransportRefutation.elim` checks that the two together are
contradictory, so producing both refutes the regime; the whole difficulty is
that the labels the regime is currently known to force have slope zero and
therefore admit no certificate, which is
`QuittingPreemptionTransportRefutation.label_ne_forcedCrossFloorLabel`. -/
structure QuittingPreemptionTransportRefutation
    (regime : QuittingCounterexampleRegime reward)
    (cycle : QuittingSoloPreemptionCycle reward regime.terminalGap) where
  /-- The labels the regime is claimed to force on the cycle's edges. -/
  label : Fin cycle.period → Label
  /-- The candidate the regime is claimed to supply. -/
  value : player → ℝ
  /-- The candidate satisfies the labelled system. -/
  isLaxSection : IsLaxSection cycle.transportGraph label value
  /-- The weights of the claimed infeasibility certificate. -/
  coefficient : Fin cycle.period ⊕ Fin cycle.period → ℝ
  /-- The certificate is a Farkas certificate against the same system. -/
  isFarkasCertificate : IsFarkasCertificate cycle.transportGraph label coefficient

namespace QuittingPreemptionTransportRefutation

variable {regime : QuittingCounterexampleRegime reward}
variable {cycle : QuittingSoloPreemptionCycle reward regime.terminalGap}

/-- **The two duties are contradictory.**  A lax section and a Farkas
certificate for one labelled system cannot coexist, by
`Math.MaxAffineTransport.exists_isLaxSection_iff_no_farkasCertificate`. -/
theorem elim (data : QuittingPreemptionTransportRefutation regime cycle) : False :=
  (exists_isLaxSection_iff_no_farkasCertificate cycle.transportGraph data.label).1
    ⟨data.value, data.isLaxSection⟩ ⟨data.coefficient, data.isFarkasCertificate⟩

/-- **The labels cannot be the forced ones.**  The constant labels that the
preemption relation supplies admit no Farkas certificate, so a production of
this shape has to enlarge the label data beyond what
`QuittingSoloPreempts` currently gives. -/
theorem label_ne_forcedCrossFloorLabel
    (data : QuittingPreemptionTransportRefutation regime cycle) :
    data.label ≠ cycle.forcedCrossFloorLabel := by
  intro hlabel
  refine cycle.not_exists_farkasCertificate_forcedCrossFloorLabel ⟨data.coefficient, ?_⟩
  rw [← hlabel]
  exact data.isFarkasCertificate

end QuittingPreemptionTransportRefutation

/-- **The missing producer.**  Every quitting counterexample regime supplies,
on every strict preemption cycle it forces, the labels, candidate and
certificate of `QuittingPreemptionTransportRefutation`.

This proposition is a statement about the labelled transport system of
`QuittingSoloPreemptionCycle.transportGraph`, not an informal analogy, and it
is what a transport proof of the quitting conjecture would have to establish:
`exists_uniformEquilibriumPayoff_of_quittingPreemptionTransportProducer` is its
consumer.  Since `QuittingPreemptionTransportRefutation.elim` already shows the
produced data to be contradictory, the proposition is equivalent to
nonexistence of the regime; its content is the *shape* of the production, which
names the two duties separately and locates the open one.  What would make it
true is a construction assigning to each preemption edge a label of nonzero
slope that the regime forces at game-derived values -- something the relation's
own per-edge datum does not provide, by
`QuittingSoloPreemptionCycle.slope_forcedCrossFloorLabel` and
`QuittingSoloPreemptionCycle.not_exists_farkasCertificate_forcedCrossFloorLabel`. -/
def QuittingPreemptionTransportProducer
    (reward : {S : Finset player // S.Nonempty} → Payoff player) : Prop :=
  ∀ regime : QuittingCounterexampleRegime reward,
    ∀ cycle : QuittingSoloPreemptionCycle reward regime.terminalGap,
      Nonempty (QuittingPreemptionTransportRefutation regime cycle)

/-- The producer proposition rules out the counterexample regime, using the
forced preemption cycle of `QuittingCounterexampleRegime.nonempty_soloPreemptionCycle`. -/
theorem isEmpty_counterexampleRegime_of_quittingPreemptionTransportProducer
    (hproducer : QuittingPreemptionTransportProducer reward) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  refine ⟨fun regime ↦ ?_⟩
  obtain ⟨cycle⟩ := regime.nonempty_soloPreemptionCycle
  exact (hproducer regime cycle).some.elim

/-- **The consumer of the producer proposition.**  A production of the shape
of `QuittingPreemptionTransportRefutation` at every regime and every forced
preemption cycle gives every finite quitting game a uniform-equilibrium
payoff, through
`not_exists_uniformEquilibriumPayoff_iff_nonempty_counterexampleRegime`. -/
theorem exists_uniformEquilibriumPayoff_of_quittingPreemptionTransportProducer
    (hproducer : QuittingPreemptionTransportProducer reward) :
    ∃ payoff : Payoff player,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  exact (isEmpty_counterexampleRegime_of_quittingPreemptionTransportProducer hproducer).false
    (quittingCounterexampleRegimeOfNoUniformPayoff reward hno)

end GameTheory

end
