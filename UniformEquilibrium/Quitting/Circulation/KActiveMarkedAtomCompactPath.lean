/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.OneActiveCoalitionMass

/-!
# Compact paths preserving a quantitatively marked coalition atom

Support cardinality is a closed condition, but mere positivity of a selected
coalition atom is not.  The correct compact annotation is a uniform lower
bound.  This module augments the `K`-active circulation edge with

```text
eta <= probability of one fixed opponent coalition.
```

The marked edge graph is closed.  Consequently, compatible finite prefixes
of every depth give one infinite chronological path that preserves both the
`K`-active support bound and the same marked atom with the same lower bound.

This closes the compactness part of fixed-atom attachment.  It deliberately
does not construct the finite prefixes: a game-facing producer must still
put one player/coalition label, with one positive quantitative floor, on a
compatible family of reset prefixes.
-/

noncomputable section

namespace GameTheory

open Finset Set StochasticGame Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The closed marked-atom coordinate -/

/-- Opponent-coalition mass written directly in compact simplex
coordinates. -/
def quittingSimplexOpponentCoalitionMass
    (root : QuittingRootSimplex ι) (who : ι)
    (coalition : Finset ι) : ℝ :=
  (∏ player ∈ coalition, root player true) *
    ∏ player ∈ Finset.univ.erase who \ coalition, root player false

/-- The simplex atom coordinate agrees with the PMF-root definition. -/
theorem quittingSimplexOpponentCoalitionMass_eq_root
    (root : QuittingRootSimplex ι) (who : ι)
    (coalition : Finset ι) :
    quittingSimplexOpponentCoalitionMass root who coalition =
      quittingOpponentCoalitionMass
        (quittingRootOfSimplex root) who coalition := by
  simp [quittingSimplexOpponentCoalitionMass,
    quittingOpponentCoalitionMass,
    quittingRootOfSimplex_apply_toReal]

/-- A fixed atom mass is continuous on the root simplex. -/
theorem continuous_quittingSimplexOpponentCoalitionMass
    (who : ι) (coalition : Finset ι) :
    Continuous fun root : QuittingRootSimplex ι =>
      quittingSimplexOpponentCoalitionMass root who coalition := by
  apply Continuous.mul
  · exact continuous_finsetProd (s := coalition) fun player _ =>
      (continuous_apply true).comp
        (continuous_subtype_val.comp (continuous_apply player))
  · exact continuous_finsetProd
      (s := Finset.univ.erase who \ coalition) fun player _ =>
        (continuous_apply false).comp
          (continuous_subtype_val.comp (continuous_apply player))

/-- A quantitative marked-atom floor is closed. -/
theorem isClosed_quittingSimplexOpponentCoalitionMass_superlevel
    (who : ι) (coalition : Finset ι) (eta : ℝ) :
    IsClosed {root : QuittingRootSimplex ι |
      eta ≤ quittingSimplexOpponentCoalitionMass root who coalition} := by
  exact isClosed_le continuous_const
    (continuous_quittingSimplexOpponentCoalitionMass who coalition)

/-! ## The augmented chronological edge -/

/-- A circulation edge carrying both a `K`-active current root and one fixed
quantitatively marked opponent-coalition atom. -/
def IsQuittingKActiveMarkedAtomCirculationPathEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : ℕ) (markedPlayer : ι) (markedCoalition : Finset ι)
    (eta δ charge : ℝ)
    (current tail : QuittingNashBellmanPoint ι) : Prop :=
  IsQuittingCirculationPathEdge reward δ charge current tail ∧
    IsQuittingSimplexKActive K current.2 ∧
    eta ≤ quittingSimplexOpponentCoalitionMass
      current.2 markedPlayer markedCoalition

/-- The box-restricted `K`-active marked-atom edge graph is closed. -/
theorem isClosed_quittingKActiveMarkedAtomCirculationPathEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (lower : Payoff ι) (K : ℕ)
    (markedPlayer : ι) (markedCoalition : Finset ι)
    (eta δ charge : ℝ) :
    IsClosed {edge : QuittingNashBellmanPoint ι ×
        QuittingNashBellmanPoint ι |
      edge.1 ∈ quittingCirculationPathBox bound lower ∧
      edge.2 ∈ quittingCirculationPathBox bound lower ∧
      IsQuittingKActiveMarkedAtomCirculationPathEdge reward K
        markedPlayer markedCoalition eta δ charge edge.1 edge.2} := by
  have hbase := isClosed_quittingCirculationPathEdgeGraph
    reward bound lower δ charge
  have hactive : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        IsQuittingSimplexKActive K edge.1.2} :=
    (isClosed_isQuittingSimplexKActive K).preimage
      (continuous_snd.comp continuous_fst)
  have hmarked : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        eta ≤ quittingSimplexOpponentCoalitionMass
          edge.1.2 markedPlayer markedCoalition} :=
    (isClosed_quittingSimplexOpponentCoalitionMass_superlevel
      markedPlayer markedCoalition eta).preimage
        (continuous_snd.comp continuous_fst)
  rw [show {edge : QuittingNashBellmanPoint ι ×
        QuittingNashBellmanPoint ι |
      edge.1 ∈ quittingCirculationPathBox bound lower ∧
      edge.2 ∈ quittingCirculationPathBox bound lower ∧
      IsQuittingKActiveMarkedAtomCirculationPathEdge reward K
        markedPlayer markedCoalition eta δ charge edge.1 edge.2} =
      ({edge | edge.1 ∈ quittingCirculationPathBox bound lower ∧
        edge.2 ∈ quittingCirculationPathBox bound lower ∧
        IsQuittingCirculationPathEdge reward δ charge edge.1 edge.2} ∩
      {edge | IsQuittingSimplexKActive K edge.1.2}) ∩
      {edge | eta ≤ quittingSimplexOpponentCoalitionMass
        edge.1.2 markedPlayer markedCoalition} by
    ext edge
    simp only [IsQuittingKActiveMarkedAtomCirculationPathEdge,
      Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto]
  exact (hbase.inter hactive).inter hmarked

/-! ## Infinite marked extraction from compatible finite prefixes -/

/-- **Quantitatively marked compact extraction.**  If every finite depth has
a compatible boxed prefix whose current rows are `K`-active and retain the
same fixed coalition atom above `eta`, one infinite chronology has all those
properties simultaneously. -/
theorem exists_chronologicalKActiveMarkedAtomPath_of_finitePrefixes
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (lower : Payoff ι) (K : ℕ)
    (markedPlayer : ι) (markedCoalition : Finset ι)
    (eta δ charge : ℝ)
    (hprefix : ∀ horizon,
      (compactFinitePrefixSolutionSet
        (quittingCirculationPathBox bound lower)
        (IsQuittingKActiveMarkedAtomCirculationPathEdge reward K
          markedPlayer markedCoalition eta δ charge) horizon).Nonempty) :
    ∃ state : ℕ → QuittingNashBellmanPoint ι,
      (∀ time, state time ∈ quittingCirculationPathBox bound lower) ∧
      ∀ time,
        IsQuittingCirculationPathEdge reward δ charge
          (state time) (state (time + 1)) ∧
        IsQuittingSimplexKActive K (state time).2 ∧
        eta ≤ quittingOpponentCoalitionMass
          (quittingRootOfSimplex (state time).2)
            markedPlayer markedCoalition := by
  let box : Set (QuittingNashBellmanPoint ι) :=
    quittingCirculationPathBox bound lower
  let relation : QuittingNashBellmanPoint ι →
      QuittingNashBellmanPoint ι → Prop :=
    IsQuittingKActiveMarkedAtomCirculationPathEdge reward K
      markedPlayer markedCoalition eta δ charge
  have hbox : IsCompact box :=
    quittingCirculationPathBox_isCompact bound lower
  have hgraph : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        edge.1 ∈ box ∧ edge.2 ∈ box ∧ relation edge.1 edge.2} := by
    simpa only [box, relation] using
      isClosed_quittingKActiveMarkedAtomCirculationPathEdgeGraph
        reward bound lower K markedPlayer markedCoalition eta δ charge
  have hprefix' : ∀ horizon,
      (compactFinitePrefixSolutionSet box relation horizon).Nonempty := by
    simpa only [box, relation] using hprefix
  obtain ⟨state, hstateBox, hstateEdge⟩ :=
    exists_infiniteChain_of_finitePrefixes
      box relation hbox hgraph hprefix'
  refine ⟨state, hstateBox, ?_⟩
  intro time
  have hedge := hstateEdge time
  unfold relation IsQuittingKActiveMarkedAtomCirculationPathEdge at hedge
  refine ⟨hedge.1, hedge.2.1, ?_⟩
  rw [← quittingSimplexOpponentCoalitionMass_eq_root]
  exact hedge.2.2

end GameTheory
