/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.NormalizedPassportMinimumReturn

/-!
# Actual raw descendants of an arbitrary positive-density carrier point

The minimum-return actualizer structure never needed equality of the whole
debt with the global minimum.  This module exposes the honest generic
constructor: a lower bound on the carrier point's whole debt supplies half of
the reference-based mass- and gain-density floors.  It reuses the existing
actualizer and all of its provenance accessors.

The selected rows are also repackaged as a genuine decorated family.  No
origin-rank cofinality, renewed minimum source, preserved incoming absolute
floor, or downstream collision consumer is asserted.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Source-neutral public name for the existing provenance-rich actualizer
record.  The abbreviation preserves every minimum-return caller while making
the weaker debt-lower-bound interface explicit. -/
abbrev QuittingMarkedPairCarrierActualizer
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair ι)
    (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι) :=
  QuittingMarkedPairMinimumReturnActualizer
    family minimum massDensity gainDensity point

/-- A positive normalized carrier point above a positive debt reference has
actual raw descendants with half of the reference-based density floors.  The
output uses the source-neutral alias of the existing provenance-rich record. -/
theorem nonempty_quittingMarkedPairCarrierActualizer
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair ι)
    (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι)
    (hmassDensity : 0 < massDensity) (hgainDensity : 0 < gainDensity)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hpoint : point ∈
      family.normalizedPassportSlice minimum massDensity gainDensity)
    (hlower : quittingTerminalSemanticDebtSum minimum ≤ point.wholeDebt) :
    Nonempty (QuittingMarkedPairCarrierActualizer
      family minimum massDensity gainDensity point) :=
  nonempty_quittingMarkedPairMinimumReturnActualizer_of_debt_le
    family minimum massDensity gainDensity point hmassDensity hgainDensity
      hminimum_pos hpoint hlower

namespace QuittingMarkedPairCarrierActualizer

variable
  {family : QuittingMarkedPairDecoratedFamily reward}
  {minimum : QuittingTerminalSemanticPair ι}
  {massDensity gainDensity : ℝ}
  {point : QuittingMarkedPairDecoration ι}

variable (actualizer : QuittingMarkedPairCarrierActualizer
  family minimum massDensity gainDensity point)

/-- The selected actual raw descendants themselves form a new executable
decorated family with the same fixed labels. -/
def toDecoratedFamily : QuittingMarkedPairDecoratedFamily reward where
  sourceProfile := actualizer.sourceProfiles
  profile := actualizer.profiles
  mark := actualizer.mark
  terminal := family.terminal
  markedOwner := family.markedOwner
  gainMover := family.gainMover
  markedMass_pos := fun rank => actualizer.resolution_pos.trans_le
    (actualizer.resolution_le_stageMass rank)
  actualGain_pos := fun rank => actualizer.gainFloor_pos.trans_le
    (actualizer.gainFloor_le_actualPayoffGain rank)
  markedOwnerDefect_eq_zero := actualizer.markedOwnerDefect_eq_zero

/-- The new family's unprefixed row is literally the selected original raw
decoration, including both semantic/law coordinates, mass, and gain. -/
theorem toDecoratedFamily_baseDecoration_eq_rawDecoration (rank : ℕ) :
    actualizer.toDecoratedFamily.baseDecoration rank =
      family.rawDecoration (actualizer.originRank rank)
        (actualizer.originRoots rank) := by
  apply Prod.ext
  · apply Prod.ext
    · change _ = (family.rawDecoration (actualizer.originRank rank)
        (actualizer.originRoots rank)).whole
      rw [QuittingMarkedPairDecoratedFamily.rawDecoration_whole_eq]
      rfl
    · change _ = (family.rawDecoration (actualizer.originRank rank)
        (actualizer.originRoots rank)).tail
      rw [QuittingMarkedPairDecoratedFamily.rawDecoration_tail_eq]
      change
        (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (family.descendantProfile (actualizer.originRank rank)
                (actualizer.originRoots rank))
              (family.descendantMark (actualizer.originRank rank)
                (actualizer.originRoots rank) + 1)),
          quittingTerminalOutcomeMass reward
            (quittingAllContinueProfileSpine reward
              (family.descendantProfile (actualizer.originRank rank)
                (actualizer.originRoots rank))
              (family.descendantMark (actualizer.originRank rank)
                (actualizer.originRoots rank) + 1))) = _
      rw [family.descendant_postMarkSpine_eq]
  · apply Prod.ext
    · change _ = (family.rawDecoration (actualizer.originRank rank)
        (actualizer.originRoots rank)).markedMass
      rw [QuittingMarkedPairDecoratedFamily.rawDecoration_markedMass_eq]
      rfl
    · change _ = (family.rawDecoration (actualizer.originRank rank)
        (actualizer.originRoots rank)).actualGain
      rw [QuittingMarkedPairDecoratedFamily.rawDecoration_actualGain_eq]
      rfl

/-- The executable reassembled family's base decorations converge to the
original carrier point. -/
theorem toDecoratedFamily_baseDecoration_tendsto :
    Tendsto actualizer.toDecoratedFamily.baseDecoration atTop (nhds point) := by
  apply actualizer.decorations_tendsto.congr'
  filter_upwards [] with rank
  exact (actualizer.toDecoratedFamily_baseDecoration_eq_rawDecoration rank).symm

end QuittingMarkedPairCarrierActualizer

/-- Exact algebraic finite-depth saturation law. -/
def IsQuittingFiniteSaturationChain
    (mass debt : ℕ → ℝ) (depth : ℕ) : Prop :=
  ∀ step, step < depth →
    mass (step + 1) * (2 * debt step) = mass step * debt (step + 1)

/-- The compatibility interval used to pre-fund one fixed requested floor
through a prescribed finite number of exact density halvings. -/
structure QuittingFiniteSaturationPrefunding
    (minimumDebt maximumDebt desiredFloor atomMass : ℝ) (depth : ℕ) where
  minimumDebt_pos : 0 < minimumDebt
  maximumDebt_pos : 0 < maximumDebt
  desiredFloor_pos : 0 < desiredFloor
  sourceResolution : ℝ
  sourceResolution_lt_atomMass : sourceResolution < atomMass
  required_lt_sourceResolution :
    2 ^ depth * desiredFloor * maximumDebt / minimumDebt < sourceResolution

namespace QuittingFiniteSaturationPrefunding

/-- The stored interval is nonempty only when its finite pre-funding demand
lies below the available atom scale. -/
theorem required_lt_atomMass
    {minimumDebt maximumDebt desiredFloor atomMass : ℝ} {depth : ℕ}
    (funding : QuittingFiniteSaturationPrefunding minimumDebt maximumDebt
      desiredFloor atomMass depth) :
    2 ^ depth * desiredFloor * maximumDebt / minimumDebt < atomMass :=
  funding.required_lt_sourceResolution.trans funding.sourceResolution_lt_atomMass

end QuittingFiniteSaturationPrefunding

end GameTheory
