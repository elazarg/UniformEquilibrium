/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourProducerAtlas.NormalizedInertSingleDensityToll
import Research.Quitting.NormalizedPassportVanishingDensityBoundary

/-!
# Source-attached Fin4 vanishing-density boundary

This adapter applies the generic density-to-zero construction to one actual
forced-pair packet and one retained normalized-return selection.  The packet,
minimum source, selected actual family, fixed owner labels, and reference tail
therefore remain recoverable.  The newly selected minimizers and their limit
belong to the enlarged arbitrary-prefix carrier, not necessarily the original
base-family cluster.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}

/-- The generic vanishing-density boundary retained together with its actual
Fin4 packet selection. -/
structure FinFourNormalizedInertVanishingDensityBoundary
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  selection : FinFourNormalizedReturnSelection packet
  boundary : QuittingVanishingDensityPassportBoundary selection.family
    source.point.1 packet.base.forcedPairGap selection.passport

namespace FinFourNormalizedInertVanishingDensityBoundary

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- The boundary limit keeps the original minimum tail debt. -/
theorem limit_tailDebt_eq_minimum
    (data : FinFourNormalizedInertVanishingDensityBoundary packet) :
    data.boundary.limit.tailDebt =
      quittingTerminalSemanticDebtSum source.point.1 :=
  data.boundary.limit_tailDebt_eq

/-- Literal Fin4 density-to-zero trichotomy.  The final root quantifier is
inside the branch and follows the one stored limit. -/
theorem outcome
    (data : FinFourNormalizedInertVanishingDensityBoundary packet) :
    (data.boundary.limit.wholeDebt =
          quittingTerminalSemanticDebtSum source.point.1 ∧
        0 < data.boundary.limit.markedMass ∧
        Nonempty (QuittingMarkedPairMinimumReturnActualizer
          data.selection.family source.point.1
          (data.boundary.limit.markedMass /
            (2 * quittingTerminalSemanticDebtSum source.point.1))
          (packet.base.forcedPairGap *
            (data.boundary.limit.markedMass /
              (2 * quittingTerminalSemanticDebtSum source.point.1)))
          data.boundary.limit)) ∨
      (data.boundary.limit.markedMass = 0 ∧
        data.boundary.limit.actualGain = 0) ∨
      ∀ root : Fin 4 → PMF Bool,
        data.boundary.limit.wholeDebt *
            quittingRootAbsorptionMass root ≤
          quittingRootTotalNashDefect reward
            data.boundary.limit.whole.1.2 root :=
  data.boundary.outcome

end FinFourNormalizedInertVanishingDensityBoundary

namespace FinFourNormalizedReturnSelection

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- Every fixed actual selection constructs its own minimizer sequence,
subsequence, limit, and boundary outcome. -/
theorem nonempty_normalizedInertVanishingDensityBoundary
    (selection : FinFourNormalizedReturnSelection packet) :
    Nonempty (FinFourNormalizedInertVanishingDensityBoundary packet) := by
  obtain ⟨boundary⟩ :=
    selection.family.nonempty_vanishingDensityPassportBoundary
      source.point.1 source.minimum source.minimumDebt_pos selection.passport
        packet.base.forcedPairGap packet.base.forcedPairGap_pos
          (fun _point hpoint =>
            selection.carrier_actualGain_eq_gap_mul_markedMass hpoint)
  exact ⟨{
    selection := selection
    boundary := boundary
  }⟩

end FinFourNormalizedReturnSelection

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- One actual packet internally selects its compact normalized family and
then constructs the complete vanishing-density boundary. -/
theorem nonempty_normalizedInertVanishingDensityBoundary
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (FinFourNormalizedInertVanishingDensityBoundary packet) := by
  obtain ⟨selection⟩ := packet.nonempty_normalizedReturnSelection
  exact selection.nonempty_normalizedInertVanishingDensityBoundary

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
