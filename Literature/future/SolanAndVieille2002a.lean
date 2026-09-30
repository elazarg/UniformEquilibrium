import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonPeriodTwo
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonPeriodTwoStationary
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryEquilibrium
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryNonstationarity
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
import UniformEquilibrium.Quitting.Root.SequentialSerializationEquilibrium
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryPerturbedEstimates
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryPerturbedCrossing
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Classification.TwoPlayer.Existence
import UniformEquilibrium.Quitting.Classification.ThreePlayer.StationaryOrSmallHazard
import UniformEquilibrium.Quitting.Classification.ThreePlayer.StationaryOrSmallHazardTransport
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.WeakInversePassiveRowSmallHazard

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

open GameTheory GameTheory.QuittingTwoPlayerExistence GameTheory.QuittingLCPClassification

/-! ## Section 2: stationary or uniformly small Quit probabilities -/

/-- The source strategy-class disjunction, using the production predicate. -/
abbrev StationaryOrSmallQuitEquilibrium
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  QuittingThreePlayerStrategyClass.StationaryOrSmallHazardTerminalEquilibrium reward ε

/-- Literal **Proposition 1**: every quitting game with at most three players
has a terminal `ε`-equilibrium in one of the two source strategy classes.
All reward signs are retained. The complete strategy-class producer remains
unformalized; ordinary uniform-payoff existence does not supply this claim.
The paper imposes no global positivity or normalization assumption here:
its positive-own-singleton restriction appears later in Section 2.2 only. -/
def Proposition1Claim : Prop :=
  ∀ n : ℕ, n ≤ 3 →
    ∀ reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n),
    ∀ ε : ℝ, 0 < ε → StationaryOrSmallQuitEquilibrium reward ε

theorem proposition1 : Proposition1Claim := by
  sorry

/-- The all-Continue branch is covered for arbitrary player counts when
every own-singleton reward is nonpositive. -/
theorem proposition1_zeroSolo
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hε : 0 < ε) (hzero : IsQuittingZeroSolo reward) :
    StationaryOrSmallQuitEquilibrium reward ε := by
  left
  refine ⟨fun _ => PMF.pure false, ?_⟩
  change (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
    (quittingAlwaysContinueProfile reward)
  exact (isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo reward hzero).mono hε.le

/-- Section 2.1 is covered by the actual stationary-root producer for every
two-player reward table and every positive terminal accuracy. -/
theorem proposition1_twoPlayer
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) {ε : ℝ}
    (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  Or.inl (quittingGame_exists_stationary_terminalApproximateEquilibrium_twoPlayer reward ε hε)

/-- Section 2.1 extends to any player type of cardinality at most two.
All reward signs are retained, and the actual stationary root is transported. -/
theorem proposition1_atMostTwoPlayers
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι ≤ 2)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  Or.inl (QuittingThreePlayerStrategyClass.exists_stationaryTerminalNash_of_card_le_two
    reward hcard hε)

/-- A supplied stationary-root family implies the Proposition 1 strategy
class at every positive accuracy, for any finite player type. -/
theorem proposition1_of_stationaryApproximateEquilibria
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hstationary : HasQuittingStationaryApproximateEquilibria reward)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_stationaryApproximateEquilibria reward hstationary hε

/-- The supplied homogeneous normal-core branch covers arbitrary reward signs.
It includes vertices through the existing stationary owner/blocker repair;
no sign condition alone is asserted to supply this branch. -/
theorem proposition1_of_homogeneousMatrixBranch
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (branch : HomogeneousMatrixBranch reward)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_homogeneousMatrixBranch reward branch hε

/-- The existing stationary producers cover three matrix regimes, with the
nonhomogeneous standard-Q side retained as an explicit unresolved alternative.
This is a scoped strategy-class gate, not unrestricted Proposition 1. -/
theorem proposition1_stationaryAlternative_or_standardQMatrixSide
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {ε : ℝ} (hε : 0 < ε) :
    StationaryOrSmallQuitEquilibrium reward ε ∨ StandardQMatrixSide reward :=
  QuittingThreePlayerStrategyClass.stationaryAlternative_or_standardQMatrixSide reward hε

/-- Excluding the nonhomogeneous standard-Q side gives the Proposition 1
strategy class, with every reward sign retained. -/
theorem proposition1_of_not_standardQMatrixSide
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬StandardQMatrixSide reward)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_not_standardQMatrixSide reward hnot hε

/-- The source's Case 1 solo branch is covered whenever its actual positive
rate satisfies the full inactive-player inequalities. This does not assert
that every table supplies such a rate. -/
theorem proposition1_of_soloStationaryCertification
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) {ε : ℝ}
    (hε : 0 < ε) (hpositive : 0 < (hazard true).toReal)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hinactive : ∀ other, other ≠ owner →
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal * quittingSingletonCollisionReward reward owner other ≤
          quittingSoloReward reward owner other) :
    StationaryOrSmallQuitEquilibrium reward ε := by
  exact Or.inl ⟨quittingSoloStationaryRoot owner hazard,
    (isεAsymptoticNash_soloStationary_exact
      reward owner hazard hpositive howner hinactive).mono hε.le⟩

/-- Section 2.2, **Case 1**, including equality in the two inactive players'
singleton comparisons. A small solo rate gives the requested terminal
accuracy even when no positive rate is exactly Nash. -/
theorem proposition1_case1
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (owner : Fin 3)
    (hcross : ∀ other, other ≠ owner →
      1 ≤ reward (quittingSingletonTerminal owner) other)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_normalizedSoloColumn
    reward hsolo owner hcross hε

/-- The normalized complementary branch, including simplex vertices.
The nonvertex branch reuses the homogeneous stationary-root producer. -/
theorem proposition1_of_homogeneousSingletonWitness
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (weight : Convexity.StdSimplex ℝ (Fin 3))
    (hresidual : ∀ who, 0 ≤ _root_.Math.LinearProgramming.singletonLCPResidual
      (normalizedSoloMatrix reward) weight who)
    (hcomplementary : ∀ who, weight.weights who *
      _root_.Math.LinearProgramming.singletonLCPResidual
        (normalizedSoloMatrix reward) weight who = 0)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_normalizedHomogeneousWitness
    reward hsolo weight hresidual hcomplementary hε

/-- Section 2.2, **Case 4**: a singleton mixture equal to the normalized
own-singleton vector supplies stationary approximate equilibria. Vertices
are retained by the preceding complementary-branch adapter. -/
theorem proposition1_case4
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (weight : Convexity.StdSimplex ℝ (Fin 3))
    (hbalance : ∀ who, quittingSingletonMixture reward weight.weights who = 1)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_normalizedBalancedSingletonMixture
    reward hsolo weight hbalance hε

/-- The source's Case 5 cyclic subdivision, once the geometric coarse arc
certificate is supplied. The existing terminal compiler gives small error;
its explicit root also bounds every player's Quit hazard at every date.
The rate is the exact subdivision `1 - (1 - p)^(1/m)`, not the paper's
printed `p/m`. No assertion about that printed rate is proved here. -/
theorem proposition1_of_singletonArcCycle
    {ι : Type} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (initial : Fin L) {aStar D ε : ℝ}
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (ha : ∀ block, quittingMeshIntensity (p block) ≤ aStar)
    (hD : 0 ≤ D)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block)) (coarse (finRotate L block)))
    (hactive : ∀ block,
      coarse block (owner block) = quittingSoloReward reward (owner block) (owner block))
    (hcoarseSolo : ∀ block who, quittingSoloReward reward who who ≤ coarse block who)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hcoarseContracts : ∀ who,
      (∏ block : Fin L, if who = owner block then 1 else 1 - p block) < 1)
    (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_singletonArcCycle
    reward owner p coarse initial hp0 hp1 ha hD harc hactive
    hcoarseSolo hcollision hcoarseContracts hε

/-- The existing strict right-cycle certificate supplies actual coarse arcs
and a small-hazard terminal approximate equilibrium. -/
theorem proposition1_of_rightSingletonCycle
    (reward : QuittingReward3) (d : RightSingletonCycle reward)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_rightSingletonCycle
    reward d hε

/-- The existing strict left-cycle certificate supplies the other oriented
small-hazard terminal approximate equilibrium. -/
theorem proposition1_of_leftSingletonCycle
    (reward : QuittingReward3) (d : LeftSingletonCycle reward)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_leftSingletonCycle
    reward d hε

/-- Every feasible normalized singleton mixture gives the source strategy
disjunction. The existing finite alternative retains degenerate supports;
its complementary branch is stationary and its strict cycles have small hazards. -/
theorem proposition1_of_normalizedFeasibleSingletonMixture
    (reward : QuittingReward3)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (weight : Convexity.StdSimplex ℝ (Fin 3))
    (hfeasible : ∀ who, 1 ≤ quittingSingletonMixture reward weight.weights who)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_normalizedFeasibleSingletonMixture
    reward hsolo weight hfeasible hε

/-- Section 2.2, **Case 2**, with an actual exact stationary root.
The original analytic-germ packet would supply the excluded feasible mixture;
therefore its endpoint absorbs and the nonnegative solo boundary compiles it. -/
theorem proposition1_case2
    (reward : QuittingReward3)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (hinfeasible : ¬ ∃ weight : Convexity.StdSimplex ℝ (Fin 3),
      ∀ who, 1 ≤ quittingSingletonMixture reward weight.weights who) :
    ∃ root : Fin 3 → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) :=
  QuittingThreePlayerStrategyClass.exists_exactStationaryTerminalNash_of_normalizedInfeasibleMixture
    reward hsolo hinfeasible

/-- The complete normalized positive-own-singleton three-player strategy
disjunction, assembled from existing stationary and cyclic root producers. -/
theorem proposition1_normalizedThreePlayer
    (reward : QuittingReward3)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_normalizedThreePlayer
    reward hsolo hε

/-- Section 2.2 before normalization: strictly positive own-singletons are
scaled multiplicatively, so Never payoff remains zero and the roots are unchanged. -/
theorem proposition1_positiveSoloThreePlayer
    (reward : QuittingReward3)
    (hpositive : ∀ who, 0 < reward (quittingSingletonTerminal who) who)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_positiveSoloThreePlayer reward hpositive hε

/-- The positive-own-singleton source discussion transports to every finite
player type with at most three players. This is not the unrestricted Proposition 1. -/
theorem proposition1_positiveSolo
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hcard : Fintype.card ι ≤ 3)
    (hpositive : ∀ who, 0 < reward (quittingSingletonTerminal who) who)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_card_le_three_of_positiveSolo reward hcard hpositive hε

/-- A literal raw inverse triple supplies the small-hazard Proposition 1
branch, including mixed own-singleton signs. These sufficient matrix tests
are not asserted for every three-player reward table. -/
theorem proposition1_of_raw_nonnegativeInverse_triple
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hdet : (PassiveRowInverseCriterion.childMatrix reward deleted).det ≠ 0)
    (hinverse : ∀ row column : {who : ι // ¬ deleted who},
      0 ≤ (PassiveRowInverseCriterion.childMatrix reward deleted)⁻¹ row column)
    (houtside : ∀ outside, deleted outside →
      ∀ inside : {who : ι // ¬ deleted who},
        0 ≤ PassiveRowInverseCriterion.inverseWeight reward deleted outside inside)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallQuitEquilibrium reward ε :=
  QuittingThreePlayerStrategyClass.of_raw_nonnegativeInverse_triple
    reward deleted hcard hdet hinverse houtside hε

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

/-! ## Section 3.1.2: the fully mixed stationary indifference polynomials

In this calculation `x,y,z,t` are Continue probabilities, as the factor
`yzt` in the printed Continue payoff shows. The root-sequence probabilities
in Section 3.2 instead record Quit. We spell out the printed polynomial
before relating it to the canonical stationary gain polynomial.
-/

/-- The printed payoff from Continue now and continuation payoff `v` tomorrow. -/
def a (v y z t : ℝ) : ℝ :=
  y * z * t * (v - 2) - 2 * y * z + 3 * z * t - y * t + y + z

/-- The printed payoff from Quit now. -/
def b (y z t : ℝ) : ℝ := t + (1 - t) * (y + z - 1)

/-- The paper's player-1 indifference polynomial. -/
def D1 (y z t : ℝ) : ℝ := a (b y z t) y z t - b y z t

/-- Player 2's polynomial, obtained by the table symmetry. -/
def D2 (x z t : ℝ) : ℝ := D1 x t z

/-- Player 3's polynomial, obtained by the table symmetry. -/
def D3 (x y t : ℝ) : ℝ := D1 t y x

/-- Player 4's polynomial, obtained by the table symmetry. -/
def D4 (x y z : ℝ) : ℝ := D1 z x y

/-- Exact identification with the canonical gain polynomial; the signs are opposite. -/
theorem D1_eq_neg_stationaryGainZero (y z t : ℝ) :
    D1 y z t = -FourPlayerPairedSingleton.stationaryGainZero y z t := by
  unfold D1 a b FourPlayerPairedSingleton.stationaryGainZero
  ring

theorem D2_eq_neg_stationaryGainOne (x z t : ℝ) :
    D2 x z t = -FourPlayerPairedSingleton.stationaryGainOne x z t := by
  unfold D2 D1 a b FourPlayerPairedSingleton.stationaryGainOne
  ring

theorem D3_eq_neg_stationaryGainTwo (x y t : ℝ) :
    D3 x y t = -FourPlayerPairedSingleton.stationaryGainTwo x y t := by
  unfold D3 D1 a b FourPlayerPairedSingleton.stationaryGainTwo
  ring

theorem D4_eq_neg_stationaryGainThree (x y z : ℝ) :
    D4 x y z = -FourPlayerPairedSingleton.stationaryGainThree x y z := by
  unfold D4 D1 a b FourPlayerPairedSingleton.stationaryGainThree
  ring

/-- **Lemma 4**, in root coordinates. This adapter eliminates the impossible
exact stationary-equilibrium antecedent using the canonical Proposition 2
proof. It does not reconstruct the paper's forward indifference derivation. -/
theorem lemma4 (root : Fin 4 → PMF Bool)
    (_hfullyMixed : ∀ who, 0 < (root who false).toReal ∧ (root who false).toReal < 1)
    (hequilibrium : SolanVieilleBoundary.IsBoundaryTerminalApproxNash
      SolanVieilleBoundary.boundaryReward 0
      (SolanVieilleBoundary.boundaryStationaryProfile
        SolanVieilleBoundary.boundaryReward root)) :
    D1 (root 1 false).toReal (root 2 false).toReal (root 3 false).toReal = 0 ∧
    D2 (root 0 false).toReal (root 2 false).toReal (root 3 false).toReal = 0 ∧
    D3 (root 0 false).toReal (root 1 false).toReal (root 3 false).toReal = 0 ∧
    D4 (root 0 false).toReal (root 1 false).toReal (root 2 false).toReal = 0 ∧
    ∀ who, quittingRootSequenceTerminalValue SolanVieilleBoundary.boundaryReward
      (fun _ => root) who 0 ∈ Set.Icc 0 1 := by
  exact False.elim (noStationaryEquilibriumClaim root hequilibrium)

/-- The literal closed-interval assertion of **Lemma 5**, journal page 373. -/
def PrintedLemma5Claim : Prop := ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < D1 t t t

/-- The printed closed-interval endpoint is false: `D₁(1,1,1)=0`. This concerns
only Lemma 5's endpoint wording, not the no-stationary-equilibrium theorem. -/
theorem not_printedLemma5Claim : ¬ PrintedLemma5Claim := by
  intro h
  have hendpoint := h 1 (by simp)
  norm_num [D1, a, b] at hendpoint

/-- **Lemma 5**, with the endpoint corrected to `t < 1`. This is the region
needed for the fully mixed argument; the proof delegates to the canonical algebra. -/
theorem lemma5 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 < D1 t t t := by
  rw [D1_eq_neg_stationaryGainZero]
  exact neg_pos.mpr (FourPlayerPairedSingleton.stationaryGainZero_diagonal_neg ht0 ht1)

/-- **Fact 1**: increasing one coordinate of `b` inside the probability cube
cannot decrease `b`. This makes the printed separate-monotonicity assertion precise. -/
theorem fact1_y {y y' z t : ℝ} (hyy' : y ≤ y') (ht1 : t ≤ 1) :
    b y z t ≤ b y' z t := by
  have hprod := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hyy')
  unfold b
  nlinarith

theorem fact1_z {y z z' t : ℝ} (hzz' : z ≤ z') (ht1 : t ≤ 1) :
    b y z t ≤ b y z' t := by
  have hprod := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hzz')
  unfold b
  nlinarith

theorem fact1_t {y z t t' : ℝ} (hy1 : y ≤ 1) (hz1 : z ≤ 1) (htt' : t ≤ t') :
    b y z t ≤ b y z t' := by
  have hprod := mul_nonneg (show 0 ≤ 2 - y - z by linarith)
    (sub_nonneg.mpr htt')
  unfold b
  nlinarith

/-- **Fact 2**, first assertion, on its stated ordered probability domain. -/
theorem fact2_y {y y' z t : ℝ} (hy0 : 0 ≤ y) (hyy' : y ≤ y')
    (hy'z : y' ≤ z) (hy't : y' ≤ t) (hz1 : z ≤ 1) (ht1 : t ≤ 1) :
    D1 y' z t ≤ D1 y z t := by
  rw [D1_eq_neg_stationaryGainZero, D1_eq_neg_stationaryGainZero]
  exact neg_le_neg (FourPlayerPairedSingleton.stationaryGainZero_mono_y
    hy0 hyy' hy'z hy't hz1 ht1)

/-- **Fact 2**, second assertion, on its stated ordered probability domain. -/
theorem fact2_z {y z z' t : ℝ} (hy0 : 0 ≤ y) (hyz : y ≤ z)
    (hyt : y ≤ t) (hzz' : z ≤ z') (hz'1 : z' ≤ 1) (ht1 : t ≤ 1) :
    D1 y z t ≤ D1 y z' t := by
  rw [D1_eq_neg_stationaryGainZero, D1_eq_neg_stationaryGainZero]
  exact neg_le_neg (FourPlayerPairedSingleton.stationaryGainZero_antitone_z
    hy0 hyz hyt hzz' hz'1 ht1)

/-- **Lemma 6**, in the fully mixed domain in which the paper uses it. -/
theorem lemma6 {y z t : ℝ} (hy : 0 < y) (hyt : y ≤ t) (htz : t ≤ z)
    (hz1 : z < 1) : 0 < D1 y z t := by
  rw [D1_eq_neg_stationaryGainZero]
  exact neg_pos.mpr (FourPlayerPairedSingleton.stationaryGainZero_neg_of_lowest_le_t_le_z
    hy hyt htz hz1.le (lt_of_le_of_lt htz hz1))

/-- **Lemma 7**, where `b(z,x,y)` is the fourth player's equilibrium payoff
in the indifference calculation. The printed proof uses its nonnegativity. -/
theorem lemma7 {x y z : ℝ} (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y)
    (hyz : y ≤ z) (hzhalf : z ≤ 1 / 2) (hpayoff : 0 ≤ b z x y) :
    0 < D4 x y z := by
  rw [D4_eq_neg_stationaryGainThree]
  exact neg_pos.mpr (FourPlayerPairedSingleton.stationaryGainThree_neg_of_quitValue_nonneg
    hx hx1 hy hyz hzhalf hpayoff)

/-- A canonical adapter for **Lemma 7** under the ambient minimal-coordinate
assumption of the fully mixed proof. It does not use any unproved source lemma. -/
theorem lemma7_of_second_coordinate_minimal {x y z : ℝ} (hy : 0 < y)
    (hyx : y ≤ x) (hyz : y ≤ z) (hzhalf : z ≤ 1 / 2) (hx1 : x < 1) :
    0 < D4 x y z := by
  rw [D4_eq_neg_stationaryGainThree]
  exact neg_pos.mpr (FourPlayerPairedSingleton.stationaryGainThree_neg_of_lowest_le_half
    hy hyx hyz hzhalf hx1)

/-- **Lemma 8**, in the fully mixed domain in which the paper uses it. -/
theorem lemma8 {y z t : ℝ} (hy : 0 < y) (hyz : y ≤ z) (hzhalf : 1 / 2 ≤ z)
    (hzt : z ≤ t) (ht1 : t < 1) : 0 < D1 y z t := by
  rw [D1_eq_neg_stationaryGainZero]
  exact neg_pos.mpr (FourPlayerPairedSingleton.stationaryGainZero_neg_of_lowest_le_z_le_t
    hy hyz hzhalf hzt ht1)

/-! ## Section 3.2: the finite deviation estimate

The paper numbers stages from one. Our cutoff `fuel` denotes the first
`fuel` stages, so the finite singleton mass is its `pⁱ_n` at `n = fuel + 1`.
The source proof considers one possible quitter at each date. The canonical
ledger proves the same lower gain bound even when simultaneous quitting is
possible, because this table has capped joint exit.
-/

/-- The four substages in the proof of **Lemma 9**: only player `phase`
uses its original mixed action from `stage`; all other players Continue. -/
noncomputable def serializedStage
    (roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4))
    (stage : ℕ) (phase : Fin 4) : Fin 4 → PMF Bool :=
  Function.update (fun _ => PMF.pure false) phase (roots stage phase)

/-- The paper's four-substage schedule, with stages numbered from zero. -/
noncomputable def serializedRoots
    (roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)) :
    SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4) :=
  fun time => serializedStage roots (time / 4) ⟨time % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Each substage has at most one possible quitter, as required by Lemma 9. -/
theorem serializedStage_atMostOne
    (roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4))
    (stage : ℕ) (phase first second : Fin 4)
    (hfirst : 0 < (serializedStage roots stage phase first true).toReal)
    (hsecond : 0 < (serializedStage roots stage phase second true).toReal) :
    first = second := by
  have howner : ∀ who, 0 < (serializedStage roots stage phase who true).toReal →
      who = phase := by
    intro who hpositive
    by_contra hne
    simp [serializedStage, Function.update_of_ne hne] at hpositive
  exact (howner first hfirst).trans (howner second hsecond).symm

/-- The source's one-quitter condition also means exact zero collision mass. -/
theorem serializedRoots_collisionMass_eq_zero
    (roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)) (time : ℕ) :
    quittingRootCollisionMass (serializedRoots roots time) = 0 := by
  apply (quittingRootCollisionMass_eq_zero_iff_atMostOne_quitProbability_pos _).2
  exact serializedStage_atMostOne roots (time / 4) _

/-- Splitting a stage preserves its near-Continue coordinate bound. -/
theorem serializedRoots_nearContinue
    {roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)} {ε : ℝ}
    (hε : 0 < ε)
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε) :
    ∀ time who, |(serializedRoots roots time who false).toReal - 1| < ε := by
  intro time who
  unfold serializedRoots serializedStage
  by_cases howner : who = (⟨time % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4)
  · subst who
    simpa using hclose (time / 4) ⟨time % 4, Nat.mod_lt _ (by norm_num)⟩
  · simpa [Function.update_of_ne howner] using hε

/-- One serialized substage has exactly its owner's Continue mass. -/
theorem serializedStage_continueMass
    (roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4))
    (stage : ℕ) (phase : Fin 4) :
    quittingStationaryContinueMass (serializedStage roots stage phase) =
      (roots stage phase false).toReal := by
  exact quittingStationaryContinueMass_soloMixedRoot phase (roots stage phase)

/-- The source's exact survival identity for one block of four substages.
This delegates to the canonical product-law evaluator. -/
theorem serializedStage_blockSurvival
    (roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)) (stage : ℕ) :
    (∏ phase : Fin 4, quittingStationaryContinueMass (serializedStage roots stage phase)) =
      quittingStationaryContinueMass (roots stage) := by
  simp_rw [serializedStage_continueMass]
  exact (quittingStationaryContinueMass_eq_prod_continueProbability (roots stage)).symm

/-- **Lemma 9**, with the exact constant `12Nr = 12·4·8 = 384`.
The reusable serialization theorem compares actual terminal payoffs and
every pure quit deadline (including Never), then invokes canonical full
behavioral pure-time extremality. Its stronger bound is weakened to the
printed constant. The source's denominator slip is avoided by the checked
division-free collision defect; no certain-absorption hypothesis is added.
The printed upper bound `ε ≤ 1/8` is retained in the source statement,
although the reusable division-free transfer does not require it. -/
theorem lemma9
    {roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)} {ε : ℝ}
    (hε : 0 < ε) (_hεsmall : ε ≤ 1 / 8)
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε)
    (hnash : SolanVieilleBoundary.IsBoundaryTerminalApproxNash
      SolanVieilleBoundary.boundaryReward ε
      (SolanVieilleBoundary.boundaryRootSequenceProfile
        SolanVieilleBoundary.boundaryReward roots)) :
    ∃ ys : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4),
      SolanVieilleBoundary.IsBoundaryTerminalApproxNash
        SolanVieilleBoundary.boundaryReward (384 * ε)
        (SolanVieilleBoundary.boundaryRootSequenceProfile
          SolanVieilleBoundary.boundaryReward ys) ∧
      (∀ time who, |(ys time who false).toReal - 1| < ε) ∧
      ∀ time first second,
        0 < (ys time first true).toReal → 0 < (ys time second true).toReal →
        first = second := by
  have hsmall : ∀ time who, (roots time who true).toReal ≤ ε := by
    intro time who
    have hsum := quittingRoot_continueProbability_add_quitProbability (roots time) who
    have hlower := (abs_lt.mp (hclose time who)).1
    linarith
  have hserialize : serializedRoots roots = quittingSerializedRoots roots := rfl
  have htransfer := isAsymptoticNash_quittingSerializedRoots
    (M := 4) (hazardBound := ε) (error := ε)
    SolanVieilleBoundary.boundaryReward_unitSoloExit roots
    SolanVieilleBoundary.boundaryReward_abs_le_four hsmall hnash
  refine ⟨serializedRoots roots, ?_, serializedRoots_nearContinue hε hclose, ?_⟩
  · unfold SolanVieilleBoundary.IsBoundaryTerminalApproxNash
      SolanVieilleBoundary.boundaryRootSequenceProfile
    rw [hserialize]
    have herror : ε + 32 * 4 * ε ≤ 384 * ε := by nlinarith [hε]
    exact GameTheory.StochasticGame.IsεAsymptoticNash.mono htransfer herror
  · intro time first second hfirst hsecond
    exact serializedStage_atMostOne roots (time / 4) _ first second hfirst hsecond

/-- **Lemma 10**, first assertion and its explicit unperturbed extension:
every behavioral `ε`-equilibrium absorbs with probability at least `1 - ε`.
Never is kept in the canonical terminal semantics. -/
theorem lemma10_termination
    {roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hnash : SolanVieilleBoundary.IsBoundaryTerminalApproxNash
      SolanVieilleBoundary.boundaryReward ε
      (SolanVieilleBoundary.boundaryRootSequenceProfile
        SolanVieilleBoundary.boundaryReward roots)) :
    1 - ε ≤ 1 - quittingJointSurvivalLimit roots 0 := by
  have hnever := SolanVieilleBoundary.boundary_survivalLimit_le_nashError hε hnash
  linarith

/-- **Lemma 10**, all three assertions for a perturbed `ε`-equilibrium,
with the printed constants `r = 8` and `N = 4`. The hypotheses use the
paper's one-quitter condition and near-Continue coordinates. The Nash cap
quantifies over every behavioral deviation; absorption is not assumed. -/
theorem lemma10
    {roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)} {ε : ℝ}
    (hε : 0 < ε)
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second)
    (hnash : SolanVieilleBoundary.IsBoundaryTerminalApproxNash
      SolanVieilleBoundary.boundaryReward ε
      (SolanVieilleBoundary.boundaryRootSequenceProfile
        SolanVieilleBoundary.boundaryReward roots)) :
    (1 - ε ≤ 1 - quittingJointSurvivalLimit roots 0) ∧
      ((∀ who : Fin 4, 1 - 8 * ε - ε ≤ quittingRootSequenceTerminalValue
          SolanVieilleBoundary.boundaryReward roots who 0) ∧
        ∃ who : Fin 4, 5 / 4 - 2 * ε ≤ quittingRootSequenceTerminalValue
          SolanVieilleBoundary.boundaryReward roots who 0) ∧
      ∀ who : Fin 4, 2 / 15 - 8 * ε ≤ quittingRootSequenceSingletonMass roots 0 who := by
  have hsmall : ∀ time who, (roots time who true).toReal ≤ ε := by
    intro time who
    have hsum := quittingRoot_continueProbability_add_quitProbability (roots time) who
    have hlower := (abs_lt.mp (hclose time who)).1
    linarith
  refine ⟨lemma10_termination hε.le hnash, ⟨?_, ?_⟩, ?_⟩
  · intro who
    have hvalue :=
      SolanVieilleBoundary.boundary_terminalValue_ge_one_sub_nine_mul_of_atMostOne
        hε.le hsmall hone hnash who
    linarith
  · exact
      SolanVieilleBoundary.boundary_exists_player_value_ge_five_fourths_sub_two_mul_of_atMostOne
        hε.le hone hnash
  · exact
      SolanVieilleBoundary.boundary_singletonMass_ge_two_fifteenths_sub_eight_mul_of_atMostOne
        hε.le hsmall hone hnash

/-- **Lemma 11**, the gain assertion in the near-Continue domain used by
Section 3.2. All source constants are retained. The stronger canonical ledger
removes the need for the at-most-one-quitter assumption. -/
theorem lemma11_gain_of_nearContinue
    {roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)} {ε : ℝ}
    (hεsmall : ε < 1)
    (hclose : ∀ time player, |(roots time player false).toReal - 1| < ε)
    (who : Fin 4) (fuel : ℕ)
    (hfloor : ∀ time, time < fuel →
      1 + Real.sqrt ε ≤ quittingRootSequenceTerminalValue
        SolanVieilleBoundary.boundaryReward roots who time) :
    quittingRootSequenceTerminalValue SolanVieilleBoundary.boundaryReward
        (quittingContinueUntilRoots roots who fuel) who 0 ≥
      quittingRootSequenceTerminalValue SolanVieilleBoundary.boundaryReward roots who 0 +
        Real.sqrt ε * (⟨0, fuel⟩ : QuittingFiniteRootWindow roots).singletonMass who := by
  have hcontinue : ∀ time, time < fuel → 0 < (roots time who false).toReal := by
    intro time _
    have hlower := (abs_lt.mp (hclose time who)).1
    linarith
  have hgain :=
    delta_mul_sum_jointSurvivalWeight_mul_quitProbability_le_continueUntil_gain
      SolanVieilleBoundary.boundaryReward_cappedJointExit roots who 0 fuel
      (Real.sqrt_nonneg ε)
      (fun time htime => by simpa using hcontinue time htime)
      (fun time htime => by simpa using hfloor time htime)
  have hclock : (⟨0, fuel⟩ : QuittingFiniteRootWindow roots).singletonMass who ≤
      ∑ time ∈ Finset.range fuel,
        quittingJointSurvivalWeight roots 0 time * (roots time who true).toReal := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [QuittingFiniteRootWindow.singletonMass, QuittingFiniteRootWindow.survivalWeight,
      QuittingFiniteRootWindow.rootAt, Nat.zero_add]
    apply Finset.sum_le_sum
    intro phase _
    exact mul_le_mul_of_nonneg_left
      (quittingRootCoalitionMass_le_quitProbability_of_mem
        (roots phase.val) {who} who (by simp))
      (quittingJointSurvivalWeight_nonneg roots 0 phase.val)
  have hscaled := mul_le_mul_of_nonneg_left hclock (Real.sqrt_nonneg ε)
  simp only [Nat.zero_add] at hgain
  linarith

/-- **Lemma 11**, its `pⁱ_n ≤ √ε` consequence in the same source domain.
This delegates to the canonical finite deviation bound and does not depend
on the unfinished paper-order lemmas. -/
theorem lemma11_singletonMass_le_sqrt
    {roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)} {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1)
    (hclose : ∀ time player, |(roots time player false).toReal - 1| < ε)
    (hnash : SolanVieilleBoundary.IsBoundaryTerminalApproxNash
      SolanVieilleBoundary.boundaryReward ε
      (SolanVieilleBoundary.boundaryRootSequenceProfile
        SolanVieilleBoundary.boundaryReward roots))
    (who : Fin 4) (fuel : ℕ)
    (hfloor : ∀ time, time < fuel →
      1 + Real.sqrt ε ≤ quittingRootSequenceTerminalValue
        SolanVieilleBoundary.boundaryReward roots who time) :
    (⟨0, fuel⟩ : QuittingFiniteRootWindow roots).singletonMass who ≤ Real.sqrt ε := by
  have hbound := SolanVieilleBoundary.boundary_delta_mul_finiteSingletonMass_le_epsilon
    hεsmall (Real.sqrt_nonneg ε) hclose hnash who fuel hfloor
  have hsqrt := Real.sqrt_pos.2 hε
  have hsquare := Real.sq_sqrt hε.le
  nlinarith


/-- **Lemma 12**, with the printed domain and constants. The paper's date
`n₁ > 1` is `cutoff + 1`, so the continuation value and prefix mass use
`n₁ - 1` in the repository's zero-based clock. Choosing the first positive
cutoff retains the initial atom even when `α ≤ √ε`, without strengthening
the printed hypothesis `α > 0`. -/
theorem lemma12
    {roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)} {ε α : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (hεsmall : ε < 1 / 900)
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second)
    (hnash : SolanVieilleBoundary.IsBoundaryTerminalApproxNash
      SolanVieilleBoundary.boundaryReward ε
      (SolanVieilleBoundary.boundaryRootSequenceProfile
        SolanVieilleBoundary.boundaryReward roots))
    (who : Fin 4)
    (hinitial : 1 + α ≤ quittingRootSequenceTerminalValue
      SolanVieilleBoundary.boundaryReward roots who 0) :
    ∃ n₁ : ℕ, 1 < n₁ ∧
      quittingRootSequenceTerminalValue SolanVieilleBoundary.boundaryReward roots who (n₁ - 1) <
        1 + Real.sqrt ε ∧
      (⟨0, n₁ - 1⟩ : QuittingFiniteRootWindow roots).singletonMass who ≤ 2 * Real.sqrt ε ∧
      α - Real.sqrt ε ≤ 3 * (⟨0, n₁ - 1⟩ : QuittingFiniteRootWindow roots).singletonMass
        (SolanVieilleBoundary.boundaryPartner who) := by
  obtain ⟨cutoff, hpositive, hdrop, _, _, hown, hpartner⟩ :=
    SolanVieilleBoundary.boundary_exists_positiveFirstDrop_with_partnerMass
      hα hε hεsmall hclose hone hnash who hinitial
  refine ⟨cutoff + 1, by omega, ?_, ?_, ?_⟩
  · simpa using hdrop
  · simpa using hown
  · simpa using hpartner

/-- **Corollary 13**, with `ε < 1/900` and the exact printed threshold
`α > 7√ε`: a perturbed equilibrium cannot give both partners `1 + α`. -/
theorem corollary13
    {roots : SolanVieilleBoundary.BoundaryRootSequence (ι := Fin 4)} {ε α : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 900)
    (hclose : ∀ time who, |(roots time who false).toReal - 1| < ε)
    (hone : ∀ time first second,
      0 < (roots time first true).toReal → 0 < (roots time second true).toReal →
      first = second)
    (hnash : SolanVieilleBoundary.IsBoundaryTerminalApproxNash
      SolanVieilleBoundary.boundaryReward ε
      (SolanVieilleBoundary.boundaryRootSequenceProfile
        SolanVieilleBoundary.boundaryReward roots))
    (who : Fin 4) (hα : 7 * Real.sqrt ε < α) :
    ¬ (1 + α ≤ quittingRootSequenceTerminalValue
          SolanVieilleBoundary.boundaryReward roots who 0 ∧
      1 + α ≤ quittingRootSequenceTerminalValue SolanVieilleBoundary.boundaryReward roots
        (SolanVieilleBoundary.boundaryPartner who) 0) :=
  SolanVieilleBoundary.boundary_not_both_partners_high_of_atMostOne
    hε hεsmall hclose hone hnash who hα

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

- Section 2: Proposition 1 is stated with the literal strategy-class
  disjunction and left as `sorry`. The two-player, zero-solo, supplied-rate solo,
  normalized Case 1 and balanced Case 4 adapters retain actual stationary roots.
  The complete normalized three-player disjunction assembles the existing finite
  singleton alternative, including degenerate supports, and the original analytic
  germ. Infeasible Case 2 yields an exact stationary endpoint. Feasible mixtures
  give a stationary complementary root or a concrete subdivided cyclic root.
  This does not formalize the source's constrained-map proof of Case 0 or its
  triangle description. The three-player nonpositive/mixed-sign own-singleton
  producer needed for the unrestricted Proposition 1 remains unformalized here.
  Positive coordinate scaling and player/cardinality transports retain the actual
  selected roots and preserve zero Never payoff; no additive terminal translation is used.
- Section 3.1: Proposition 2 and Lemma 4 are proved above; Lemma 4 delegates
  to the impossible exact-stationary antecedent, rather than the paper's
  forward indifference derivation. The printed indifference polynomials are identified
  exactly with the negatives of the canonical gain polynomials. Lemmas 6--8
  and the three coordinate assertions of Fact 1 are proved by adapters or
  elementary algebra. Lemma 5's literal closed-interval assertion is refuted
  at `t = 1`; its corrected `t < 1` version is proved. Both assertions of Fact 2
  are proved by exact finite-difference polynomial inequalities.
- Section 3.2: Proposition 3 is stated above. Its named intermediate claims
  are Lemmas 9--12 and Corollary 13: stage splitting, absorption and singleton
  mass bounds, a pure-deviation bound, first-crossing extraction, and the
  partner-high exclusion. Lemma 11's gain and singleton-mass assertions are
  proved above in the near-Continue domain, with the printed `√ε` constants;
  the canonical ledger also allows simultaneous quitting. Lemma 9 is stated
  with its exact `384ε` constant. Its explicit stage splitting, near-Continue,
  one-quitter, block-survival and full behavioral equilibrium-transfer properties
  are proved by adapters. Lemma 10's absorption, coordinate-payoff and singleton-mass
  estimates are stated with their exact printed constants and proved from the full
  behavioral Nash cap. Its absorption bound also holds without perturbation.
  Lemma 12 and Corollary 13 are stated with the printed `ε < 1/900` domain,
  positive one-based crossing date, and exact prefix and partner-high constants.
  Their adapters use a first positive-time crossing to retain the source's
  `α > 0` hypothesis, including when the initial value is below `1 + √ε`.

The journal PDF numbers its first lemma in Section 3 as Lemma 4; it contains
no separately labeled Lemmas 1--3. The solo-hull sentence occurs in the
Introduction rather than as a numbered Section 3 proposition.

The published journal PDF has Section 3.1 and Section 3.2, not Section 3.3.
The printed primary continuation probability is separately stated and refuted
above; that refutation does not concern period-two existence.

The Case 5 strategy-class adapters use exact arc subdivision, whose block
survival is `1 - beta`. The paper prints the different rate `beta/M`; for fixed
`beta`, its block survival tends to `exp(-beta)`. No literal assertion about
the printed rate construction is proved by the exact-subdivision adapter.
-/

end Literature.SolanAndVieille2002a
