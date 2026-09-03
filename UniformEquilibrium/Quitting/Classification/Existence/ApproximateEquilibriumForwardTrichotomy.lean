import UniformEquilibrium.Quitting.Classification.Existence.ChronologicalAbsorptionPathTerminalDispatch
import UniformEquilibrium.Quitting.Classification.Existence.ApproximateEquilibriumVanishingNeverAlternative

/-!
# Forward trichotomy from terminal approximate-equilibrium existence

The arbitrary-never approximate-equilibrium hypothesis first yields literal
S.1 or an actual vanishing-Never root-sequence source.  In the second arm the
existing absorbing completion and chronological compactification produce one
actual path, and the terminal/no-terminal dispatch yields S.2 or S.3.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingLCPClassification

/-- AKRS Theorem 3.4: arbitrary-never approximate-equilibrium existence
implies one fixed quitting-game branch S.1, S.2, or S.3. -/
theorem QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing
    (table : QuittingPayoffTable ι)
    (happrox : table.ApproximateEquilibriumExistence) :
    table.StationaryεEquilibriumExistence ∨
      table.InstantPunishmentεEquilibriumExistence ∨
        table.SequentiallyεPerfectAbsorbingExistence := by
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      left
      intro ε _hε
      refine ⟨fun who => hempty.elim who, ?_⟩
      intro who
      exact hempty.elim who
  | inr hnonempty =>
      letI := hnonempty
      rcases table.stationary_or_vanishingNeverNashFamily happrox with
        hstationary | hfamily
      · exact Or.inl hstationary
      · let source := Classical.choice hfamily
        let diagonal := Classical.choice
          (nonempty_rootSequenceAbsorbingCompletionDiagonal
            table.zeroNeverReward source)
        let limit := Classical.choice diagonal.nonempty_chronologicalLimit
        rcases limit.instantPunishment_or_wellSupportedAbsorbingSequenceExistence with
          hinstant | hwellSupported
        · exact Or.inr (Or.inl
            (table.instantPunishmentεEquilibriumExistence_iff.mpr hinstant))
        · exact Or.inr (Or.inr
            (table.sequentiallyεPerfectAbsorbingExistence_iff.mpr
              (quittingSequentiallyεPerfectAbsorbingExistence_of_wellSupported
                hwellSupported)))

end QuittingLCPClassification
end GameTheory
