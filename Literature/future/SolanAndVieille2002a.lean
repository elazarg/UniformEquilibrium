import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonPeriodTwo
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryEquilibrium

/-!
# Literature audit

Bibliography label: Solan & Vieille 2002a

Citation: Published source: Solan & Vieille 2002a.

The published four-player example was inspected. Its qualitative results and
the disputed primary continuation probability in its printed numerical packet
are recorded separately.
-/

namespace Literature.SolanAndVieille2002a

open GameTheory

/-- The numerical parameter assertion in the normalized transcription of the
printed period-two packet: its continuation probability `1 / √2` is the
unique primary parameter selected by the exact period-two equations for the
displayed table. -/
def PrintedPeriodTwoContinuationClaim : Prop :=
  FourPlayerPairedSingleton.periodTwoParameter = (Real.sqrt 2)⁻¹

/-- The printed continuation probability is not the exact primary parameter.
This refutes that scalar assertion, not the existence of period-two equilibria. -/
theorem not_printedPeriodTwoContinuationClaim :
    ¬ PrintedPeriodTwoContinuationClaim := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsquare : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hinvPos : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr hsqrt
  have hinvSquare : ((Real.sqrt 2)⁻¹) ^ 2 = (1 : ℝ) / 2 := by
    rw [inv_pow, hsquare]
    norm_num
  have hinvLt : (Real.sqrt 2)⁻¹ < (37 : ℝ) / 50 := by
    by_contra h
    have hge : (37 : ℝ) / 50 ≤ (Real.sqrt 2)⁻¹ := le_of_not_gt h
    nlinarith
  intro hprinted
  have hselected :=
    FourPlayerPairedSingleton.thirtySeven_fiftieths_lt_periodTwoParameter
  rw [PrintedPeriodTwoContinuationClaim] at hprinted
  linarith

/-- The paper's period-two existence claim, in the repository's semantics:
the displayed four-player table has a uniform-equilibrium payoff. -/
def PeriodTwoEquilibriumClaim : Prop :=
  ∃ payoff : Payoff SolanVieilleBoundary.Player,
    (quittingGame SolanVieilleBoundary.boundaryReward).IsUniformEquilibriumPayoff
      none payoff

/-- The period-two existence claim holds.  The witness is
`GameTheory.SolanVieilleBoundary.crossBlockPayoff`, carried by
`GameTheory.SolanVieilleBoundary.boundaryReward_isUniformEquilibriumPayoff`. -/
theorem periodTwoEquilibriumClaim : PeriodTwoEquilibriumClaim :=
  SolanVieilleBoundary.boundaryReward_exists_uniformEquilibriumPayoff

/-!
## Remaining source claims not yet stated in Lean

- Section 3: no equilibrium payoff lies in the convex hull of the solo
  payoffs.
- Section 3.2: the example has no stationary limiting-average equilibrium and
  no stationary epsilon-equilibrium for sufficiently small errors.
- Section 3.3: the example excludes the perturbed epsilon-equilibrium
  fallback.

The period-two existence claim from Section 3 is stated and proved above. The
printed primary continuation probability from Figure 2 and the period-two
calculation is stated and refuted above; that refutation does not concern the
existence claim.
-/

end Literature.SolanAndVieille2002a
