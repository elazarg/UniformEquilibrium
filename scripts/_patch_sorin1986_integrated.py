from pathlib import Path

path = Path(__file__).resolve().parents[1] / "Literature" / "Sorin1986IntegratedScratch.lean"
s = path.read_text()

# Make the typed wrappers explicit definitions so their proofs can unfold both
# the wrapper and the raw real-parameter evaluator.
s = s.replace(
    "abbrev continuationFactor {G : FiniteStageGame} (lam : G.DiscountRate) : ℝ :=",
    "def continuationFactor {G : FiniteStageGame} (lam : G.DiscountRate) : ℝ :=",
)
s = s.replace(
    "abbrev discountedRealizationPayoff (G : FiniteStageGame)",
    "def discountedRealizationPayoff (G : FiniteStageGame)",
)
s = s.replace(
    "  unfold continuationFactorRaw\n  linarith [lam.2.1]",
    "  unfold continuationFactor continuationFactorRaw\n  linarith [lam.2.1]",
)
s = s.replace(
    "  unfold discountedRealizationPayoffRaw\n",
    "  unfold discountedRealizationPayoff discountedRealizationPayoffRaw\n",
)

s = s.replace(
'''theorem paper_property_1_finite (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteFeasiblePayoffsOnHorizon n).Nonempty ∧
      PathConnectedSet (G.finiteFeasiblePayoffsOnHorizon n) ∧
        IsCompact (G.finiteFeasiblePayoffsOnHorizon n) := by
  simpa using paper_property_1 (G.finiteCompactGame n)

theorem paper_property_1_discounted
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedFeasiblePayoffsOnRate lam).Nonempty ∧
      PathConnectedSet (G.discountedFeasiblePayoffsOnRate lam) ∧
        IsCompact (G.discountedFeasiblePayoffsOnRate lam) := by
  simpa using paper_property_1 (G.discountedCompactGame lam)

theorem paper_property_2_finite (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteEquilibriumPayoffsOnHorizon n).Nonempty ∧
      IsCompact (G.finiteEquilibriumPayoffsOnHorizon n) := by
  simpa using paper_property_2 (G.finiteCompactGame n)

theorem paper_property_2_discounted
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedEquilibriumPayoffsOnRate lam).Nonempty ∧
      IsCompact (G.discountedEquilibriumPayoffsOnRate lam) := by
  simpa using paper_property_2 (G.discountedCompactGame lam)
''',
'''theorem paper_property_1_finite (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteFeasiblePayoffsOnHorizon n).Nonempty ∧
      PathConnectedSet (G.finiteFeasiblePayoffsOnHorizon n) ∧
        IsCompact (G.finiteFeasiblePayoffsOnHorizon n) := by
  rw [← G.finiteCompactGame_feasiblePayoffs n]
  exact paper_property_1 (G.finiteCompactGame n)

theorem paper_property_1_discounted
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedFeasiblePayoffsOnRate lam).Nonempty ∧
      PathConnectedSet (G.discountedFeasiblePayoffsOnRate lam) ∧
        IsCompact (G.discountedFeasiblePayoffsOnRate lam) := by
  rw [← G.discountedCompactGame_feasiblePayoffs lam]
  exact paper_property_1 (G.discountedCompactGame lam)

theorem paper_property_2_finite (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteEquilibriumPayoffsOnHorizon n).Nonempty ∧
      IsCompact (G.finiteEquilibriumPayoffsOnHorizon n) := by
  rw [← G.finiteCompactGame_equilibriumPayoffs n]
  exact paper_property_2 (G.finiteCompactGame n)

theorem paper_property_2_discounted
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedEquilibriumPayoffsOnRate lam).Nonempty ∧
      IsCompact (G.discountedEquilibriumPayoffsOnRate lam) := by
  rw [← G.discountedCompactGame_equilibriumPayoffs lam]
  exact paper_property_2 (G.discountedCompactGame lam)
''')

s = s.replace(
'''theorem paper_proposition_11_finite (G : FiniteStageGame)
    (n : G.Horizon) (hplayers : Fintype.card G.Player = 2) :
    SimplyConnectedSet (G.finiteFeasiblePayoffsOnHorizon n) := by
  obtain ⟨presentation⟩ := finiteCompactPresentation_exists G n
  rw [← finiteCompactPresentation_feasiblePayoffs_eq presentation]
  exact paper_proposition_11 presentation.toCompactContinuousGame hplayers

theorem paper_proposition_11_discounted (G : FiniteStageGame)
    (lam : G.DiscountRate) (hplayers : Fintype.card G.Player = 2) :
    SimplyConnectedSet (G.discountedFeasiblePayoffsOnRate lam) := by
  obtain ⟨presentation⟩ := discountedCompactPresentation_exists G lam
  rw [← discountedCompactPresentation_feasiblePayoffs_eq presentation]
  exact paper_proposition_11 presentation.toCompactContinuousGame hplayers
''',
'''theorem paper_proposition_11_finite (G : FiniteStageGame)
    (n : G.Horizon) (hplayers : Fintype.card G.Player = 2) :
    SimplyConnectedSet (G.finiteFeasiblePayoffsOnHorizon n) := by
  rw [← G.finiteCompactGame_feasiblePayoffs n]
  exact paper_proposition_11 (G.finiteCompactGame n) hplayers

theorem paper_proposition_11_discounted (G : FiniteStageGame)
    (lam : G.DiscountRate) (hplayers : Fintype.card G.Player = 2) :
    SimplyConnectedSet (G.discountedFeasiblePayoffsOnRate lam) := by
  rw [← G.discountedCompactGame_feasiblePayoffs lam]
  exact paper_proposition_11 (G.discountedCompactGame lam) hplayers
''')

path.write_text(s)
print("patched integrated source", path)
