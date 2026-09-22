import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonPeriodTwo
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryEquilibrium
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryNonstationarity

/-!
# Literature audit

Bibliography label: Solan & Vieille 2002a

Citation: E. Solan and N. Vieille, *Quitting games -- An example*,
International Journal of Game Theory 31 (2002), 365--381.
Author-hosted journal PDF: https://www.math.tau.ac.il/~eilons/notequitting4.pdf

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

/-- Section 3, Proposition 2: the displayed table has no stationary exact
terminal equilibrium. -/
def NoStationaryEquilibriumClaim : Prop :=
  ∀ root : SolanVieilleBoundary.Player → PMF Bool,
    ¬ SolanVieilleBoundary.IsBoundaryTerminalApproxNash
      SolanVieilleBoundary.boundaryReward 0
      (SolanVieilleBoundary.boundaryStationaryProfile
        SolanVieilleBoundary.boundaryReward root)

theorem noStationaryEquilibriumClaim : NoStationaryEquilibriumClaim := by
  intro root
  exact FourPlayerPairedSingleton.periodTwo_no_stationary_exactTerminalNash root

/-- Section 3, Proposition 3: sufficiently small approximate equilibria cannot
remain uniformly close to the all-Continue profile at every stage. -/
def NoPerturbedEquilibriumClaim : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
    ¬ ∃ roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4),
      (∀ time player, |(roots time player false).toReal - 1| < ε) ∧
      SolanVieilleBoundary.IsBoundaryTerminalApproxNash
        SolanVieilleBoundary.boundaryReward ε
        (SolanVieilleBoundary.boundaryRootSequenceProfile
          SolanVieilleBoundary.boundaryReward roots)

theorem noPerturbedEquilibriumClaim : NoPerturbedEquilibriumClaim :=
  SolanVieilleBoundary.no_nearAllContinue_terminalApproximateEquilibrium

/-- Corollary following Propositions 2 and 3: stationary approximate
equilibria fail for every sufficiently small positive error. -/
def NoSmallStationaryApproximateEquilibriumClaim : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
    ¬ ∃ root : Fin 4 → PMF Bool,
      SolanVieilleBoundary.IsBoundaryTerminalApproxNash
        SolanVieilleBoundary.boundaryReward ε
        (SolanVieilleBoundary.boundaryStationaryProfile
          SolanVieilleBoundary.boundaryReward root)

theorem noSmallStationaryApproximateEquilibriumClaim :
    NoSmallStationaryApproximateEquilibriumClaim :=
  SolanVieilleBoundary.no_stationary_terminalApproximateEquilibrium

/-- The introduction's solo-hull exclusion, stated for the fixed payoff
target of a uniform equilibrium. This remains open in this audit. -/
def NoSoloHullUniformEquilibriumPayoffClaim : Prop :=
  ∀ payoff : Payoff SolanVieilleBoundary.Player,
    (quittingGame SolanVieilleBoundary.boundaryReward).IsUniformEquilibriumPayoff
      none payoff →
    payoff ∉ convexHull ℝ
      (Set.range (fun player : SolanVieilleBoundary.Player =>
        SolanVieilleBoundary.boundaryReward ⟨{player}, by simp⟩))

/-!
## Remaining source coverage

The solo-hull exclusion above is only an open proposition. The existing
production results establish the named period-two equilibrium and the three
stationary/near-Continue exclusions, but do not establish that *every* uniform
equilibrium payoff avoids the solo-payoff convex hull. This file stays in
`Literature/future/`. In particular, excluding stationary and near-Continue
profiles does not constrain the payoff targets of all other profiles.

The named-statement inventory of the author-hosted journal PDF is:

- Section 2: Proposition 1 (the stationary-or-small-quit dichotomy for games
  with at most three players) is not stated here; its five geometric cases
  are likewise not formalized in this paper's terms.
- Section 3.1: Proposition 2 is stated above. Its named intermediate claims
  are Lemmas 4--8 and Facts 1--2, involving the fully mixed stationary
  indifference polynomials and their sign regions. The production stationary
  proof uses a related gain-polynomial argument, but its private lemmas are
  not paper-order statements or direct adapters of these printed claims.
- Section 3.2: Proposition 3 is stated above. Its named intermediate claims
  are Lemmas 9--12 and Corollary 13: stage splitting, absorption and singleton
  mass bounds, a pure-deviation bound, first-crossing extraction, and the
  partner-high exclusion. Production proves related root-sequence estimates
  with different constants and hypotheses; these are not exact paper adapters.

The journal PDF numbers its first lemma in Section 3 as Lemma 4; it contains
no separately labeled Lemmas 1--3. The solo-hull sentence occurs in the
Introduction rather than as a numbered Section 3 proposition.

The published journal PDF has Section 3.1 and Section 3.2, not Section 3.3.
The printed primary continuation probability is separately stated and refuted
above; that refutation does not concern period-two existence.
-/

end Literature.SolanAndVieille2002a
