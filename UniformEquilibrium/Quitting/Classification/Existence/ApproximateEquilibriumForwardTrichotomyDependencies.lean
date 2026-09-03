/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.CorrectedFixedBranch
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.ArbitraryNeverExtraction

/-!
# Exact dependencies for the approximate-equilibrium forward trichotomy

Simon's corrected classification has a fourth, stationarily generated branch.
Accordingly, the three-way conclusion needs two logically separate inputs.
The first extracts the corrected four-way alternative pointwise from
arbitrary-never approximate equilibria. The second compactifies the diffuse
stationarily generated residual into the stationary or well-supported branch.

These are proposition-valued dependencies, not claimed theorems.  The checked
capstone below composes them through the existing finite-branch selector and
the exact arbitrary-never translation.  It does not assume the three-way
conclusion under another name.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingLCPClassification

/-- Arbitrary-never approximate-equilibrium existence
produces the corrected pointwise four-way alternative for the translated
zero-never reward.  The output retains the actual stationary, punishment,
absorbing-sequence, or stationarily-generated witness at the requested error.
-/
def QuittingPayoffTable.HasCorrectedPointwiseFourWayExtraction
    (table : QuittingPayoffTable ι) : Prop :=
  table.ApproximateEquilibriumExistence →
    ∀ ε : ℝ, 0 < ε →
      QuittingStationaryεEquilibriumAt table.zeroNeverReward ε ∨
        QuittingInstantPunishmentεEquilibriumAt table.zeroNeverReward ε ∨
          QuittingWellSupportedAbsorbingSequenceAt table.zeroNeverReward ε ∨
            QuittingStationarilyGeneratedApproximateEquilibriaAt
              table.zeroNeverReward ε

end QuittingLCPClassification

/-- The corrected diffuse stationarily generated residual
compactifies to branch `S.1` or to the well-supported form of branch `S.3`. -/
def HasDiffuseStationarilyGeneratedCompactification
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward →
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingWellSupportedAbsorbingSequenceExistence reward

namespace QuittingLCPClassification

/-- Pointwise four-way extraction and diffuse-source compactification imply
the exact three table-level branches. The arbitrary payoff at never is
retained in the conclusion; normalization is used only inside the proof and
is removed by the checked table-branch equivalences. -/
theorem QuittingPayoffTable.threeBranches_of_correctedExtraction_of_compactification
    (table : QuittingPayoffTable ι)
    (hextraction : table.HasCorrectedPointwiseFourWayExtraction)
    (hcompactification :
      HasDiffuseStationarilyGeneratedCompactification table.zeroNeverReward)
    (hexists : table.ApproximateEquilibriumExistence) :
    table.StationaryεEquilibriumExistence ∨
      table.InstantPunishmentεEquilibriumExistence ∨
        table.SequentiallyεPerfectAbsorbingExistence := by
  have hthree :=
    fixedThreeQuittingBranches_of_pointwiseAlternative_of_diffuseCompactification
      (hextraction hexists) hcompactification
  rcases hthree with hstationary | hinstant | hwellSupported
  · exact Or.inl (table.stationaryεEquilibriumExistence_iff.mpr hstationary)
  · exact Or.inr (Or.inl
      (table.instantPunishmentεEquilibriumExistence_iff.mpr hinstant))
  · exact Or.inr (Or.inr
      (table.sequentiallyεPerfectAbsorbingExistence_iff.mpr
        (quittingSequentiallyεPerfectAbsorbingExistence_of_wellSupported
          hwellSupported)))

end QuittingLCPClassification
end GameTheory
