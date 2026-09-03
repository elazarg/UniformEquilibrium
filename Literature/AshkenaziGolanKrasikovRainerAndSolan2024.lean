import MathUE.LinearAlgebra.PrincipalMinorDiagonalPerturbation
import MathUE.PMFProduct.SmallCellProductization
import UniformEquilibrium.Quitting.AbsorptionPath.DiscreteRootSequencePath
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQContinuousPath
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQViabilityCorrespondence
import UniformEquilibrium.Quitting.AbsorptionPath.TerminalTotalJumpVacuity
import UniformEquilibrium.Quitting.Boundary.Repair.LocalGlobalCounterexample
import UniformEquilibrium.Quitting.Classification.ErrorExponentRefutation
import UniformEquilibrium.Quitting.Classification.Existence.AKRSReverseS3Hardness
import UniformEquilibrium.Quitting.Classification.Existence.AKRSTheorem34

/-!
# Ashkenazi--Golan--Krasikov--Rainer--Solan (2024)

Galit Ashkenazi-Golan, Ilia Krasikov, Catherine Rainer, and Eilon Solan,
*Absorption paths and equilibria in quitting games*, Mathematical Programming
**203** (2024), 735--762, DOI `10.1007/s10107-022-01807-6`.

This file follows the current journal paper in its order, terminology, and
numbering.  The version of record was published online on 22 April 2022.  The
publisher's 24 May 2025 update corrected only Eilon Solan's affiliation; it did
not change the mathematical passages recorded here.  The longer HAL manuscript
`hal-03036804v2`, dated 27 October 2022, agrees with the journal version at the
locations discussed below.  A map to `arXiv:2012.04369v1` is provided at the
end of the file.

The file distinguishes four statuses literally.

* A theorem proved below is checked at exactly its displayed type.
* A live open implication is a named proposition together with a checked
  reduction to the identified general open problem; it is not asserted as a
  theorem.
* A false published statement is a named proposition followed by a checked
  theorem proving its negation.
* A superseded version-only claim is a named proposition together with a
  checked weakening to the corrected current statement; it is not asserted as
  a current theorem.

In particular, the forward implication of journal Theorem 3.4 is checked.  The
printed reverse implication is open, and the universal printed equivalence is
checked below to be equivalent to general finite-quitting terminal
approximate-equilibrium existence.  The null-tail subcase of its S.3 branch is
eliminated below.  Even the restricted stationary-exact every-restart
implication is universally equivalent, through a one-added-player reduction,
to the same open problem; this is not a same-cardinality equivalence.  Theorem
3.5 is false.  The
strict estimate in Lemma 4.9 is false at zero absorption; the checked corrected
version uses a weak inequality.  The literal path side of Theorem 4.15 is
automatic for nonempty games because the printed absorption-path definition
does not test terminal total jumps.  Its universal claim is therefore checked
to be equivalent to the same general approximate-existence problem.  The
conclusion of Theorem 5.4 is checked through the corrected
facewise polygonal construction; the printed global control correspondence is
separately proved not upper hemicontinuous.  The only claims below still
represented by `sorry` are the compactness/density chain: journal Proposition
4.8, Proposition 4.11, and Proposition 4.14.
-/

noncomputable section

namespace Literature.AshkenaziGolanKrasikovRainerAndSolan2024

open GameTheory GameTheory.StochasticGame
open GameTheory.QuittingAbsorptionPath
open GameTheory.QuittingLCPClassification
open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. Introduction

The paper introduces absorption paths, which use cumulative absorption mass
instead of calendar time.  Jumps retain discrete product rows, while continuous
pieces retain diffuse singleton quitting.  Sections 3--5 relate approximate
equilibria, sequential perfection, absorption-path compactness, and a
projective linear-complementarity condition.
-/

/-! ## 2. The model

**Definition 2.1.** A quitting game has a finite player set `I`, actions
`C^i,Q^i`, and a payoff vector for every joint action.  The first non-all-
Continue row absorbs; perpetual continuation receives `r(C)`.  The repository
represents nonempty quitting coalitions by the terminal reward below and
carries `r(C)` as the separate value `never`.
-/

/-- Journal Definition 2.1, with the all-Continue payoff separated from the
rewards of nonempty quitting coalitions. -/
abbrev FiniteQuittingGamePayoffData := QuittingPayoffTable ι

/-! ## 3. Sequential epsilon-perfectness

### Definition 3.1

The general strategic-form definition has two upper inequalities, one for
each pure action, and a lower inequality for every action used with positive
probability.
-/

/-- Expected payoff at an independent mixed profile in the finite
strategic-form game of journal Definition 3.1. -/
noncomputable def strategicMixedProfileExpectedPayoff
    (Action : ι → Type) [∀ player, Fintype (Action player)]
    (payoff : (∀ player, Action player) → Payoff ι)
    (profile : ∀ player, PMF (Action player))
    (player : ι) : ℝ :=
  Math.Probability.expect (Math.PMFProduct.pmfPi profile)
    (fun actions => payoff actions player)

/-- Payoff from one pure action against the opponents' independent mixed
actions in the finite strategic-form game of journal Definition 3.1. -/
noncomputable def strategicPureActionExpectedPayoff
    (Action : ι → Type) [∀ player, Fintype (Action player)]
    (payoff : (∀ player, Action player) → Payoff ι)
    (profile : ∀ player, PMF (Action player))
    (player : ι) (action : Action player) : ℝ :=
  strategicMixedProfileExpectedPayoff Action payoff
    (Function.update profile player (PMF.pure action)) player

/-- Journal Definition 3.1: one player is `error`-perfect at a finite
strategic-form mixed profile. -/
def PlayerIsPerfectAtMixedProfileWithinError
    (Action : ι → Type) [∀ player, Fintype (Action player)]
    (payoff : (∀ player, Action player) → Payoff ι)
    (profile : ∀ player, PMF (Action player))
    (player : ι) (error : ℝ) : Prop :=
  ∀ action,
    strategicPureActionExpectedPayoff Action payoff profile player action ≤
        strategicMixedProfileExpectedPayoff Action payoff profile player + error ∧
      (profile player action ≠ 0 →
        strategicMixedProfileExpectedPayoff Action payoff profile player - error ≤
          strategicPureActionExpectedPayoff Action payoff profile player action)

/-- Quitting-row specialization of journal Definition 3.1. -/
def PlayerRowwisePerfectAtError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (player : ι) (error : ℝ) : Prop :=
  quittingRootQuitPayoff reward continuation root player ≤
      quittingRootSuccessorPayoff reward continuation root player + error ∧
    quittingRootContinuePayoff reward continuation root player ≤
      quittingRootSuccessorPayoff reward continuation root player + error ∧
    (root player true ≠ 0 →
      quittingRootSuccessorPayoff reward continuation root player - error ≤
        quittingRootQuitPayoff reward continuation root player) ∧
    (root player false ≠ 0 →
      quittingRootSuccessorPayoff reward continuation root player - error ≤
        quittingRootContinuePayoff reward continuation root player)

/-- Every player is rowwise perfect at the supplied error. -/
def EveryPlayerRowwisePerfectAtError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (error : ℝ) : Prop :=
  ∀ player, PlayerRowwisePerfectAtError reward continuation root player error

theorem everyPlayerRowwisePerfectAtError_iff_quittingRowPerfect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (error : ℝ) :
    EveryPlayerRowwisePerfectAtError reward continuation root error ↔
      QuittingRowεPerfect reward continuation root error := by
  rfl

/-! ### Definition 3.2

The continuation at a null history is not a conditional expectation on a null
event.  It is the payoff of the tail profile started anew.  This agrees with
the paper's conditional expression whenever survival has positive probability
and gives the strategically relevant off-path continuation otherwise.

The definition's rowwise zero-perfectness is distinct from the following
sentence in the paper, which calls a complete strategy a best response in every
subgame.  The two notions are not identified here.
-/

/-- The payoff of the actual tail beginning after `time`. -/
def tailRestartContinuationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) : Payoff ι :=
  fun player => QuittingPayoffTable.terminalPayoff ⟨reward, never⟩
    (quittingRootSequenceProfile reward roots (time + 1)) player

/-- Journal Definition 3.2: one player's rowwise sequential perfection
against every actual restarted tail. -/
def PlayerSequentiallyRowwisePerfectAtError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) (roots : ℕ → ι → PMF Bool)
    (player : ι) (error : ℝ) : Prop :=
  ∀ time, PlayerRowwisePerfectAtError reward
    (tailRestartContinuationPayoff reward never roots time)
    (roots time) player error

/-- Every player is rowwise sequentially perfect against every actual
restarted tail. -/
def SequentiallyRowwisePerfectAtError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) (roots : ℕ → ι → PMF Bool)
    (error : ℝ) : Prop :=
  ∀ player, PlayerSequentiallyRowwisePerfectAtError reward never roots
    player error

/-- The separate whole-strategy notion in the final sentence of journal
Definition 3.2: one player's prescribed continuation is a best response after
every finite restart.  It is not identified with rowwise zero-perfectness. -/
def PlayerIsBestResponseAfterEveryRestart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) (roots : ℕ → ι → PMF Bool)
    (player : ι) : Prop :=
  ∀ (start : ℕ)
      (deviation : (quittingGame reward).BehaviorStrategy player),
    QuittingPayoffTable.terminalPayoff ⟨reward, never⟩
        (Function.update (quittingRootSequenceProfile reward roots start)
          player deviation) player ≤
      QuittingPayoffTable.terminalPayoff ⟨reward, never⟩
        (quittingRootSequenceProfile reward roots start) player

theorem tailRestartContinuationPayoff_eq_tableTailVector
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) :
    tailRestartContinuationPayoff reward never roots time =
      (⟨reward, never⟩ : QuittingPayoffTable ι).rootSequenceTailVector
        roots (time + 1) := by
  rfl

theorem sequentiallyRowwisePerfectAtError_iff_tableRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) (roots : ℕ → ι → PMF Bool)
    (error : ℝ) :
    SequentiallyRowwisePerfectAtError reward never roots error ↔
      ∀ time, QuittingRowεPerfect reward
        ((⟨reward, never⟩ : QuittingPayoffTable ι).rootSequenceTailVector
          roots (time + 1)) (roots time) error := by
  simp only [SequentiallyRowwisePerfectAtError,
    PlayerSequentiallyRowwisePerfectAtError, QuittingRowεPerfect]
  exact forall_comm

/-! **Remark 3.3.** Rowwise perfection bounds the gain from quitting now.  If
the player quits with positive probability, it also bounds the loss from
quitting now. -/

/-- Approximate equilibria exist at every positive error. -/
def HasApproximateEquilibriaAtEveryPositiveError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) : Prop :=
  ∀ error : ℝ, 0 < error →
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩) error profile

theorem hasApproximateEquilibriaAtEveryPositiveError_iff_table
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) :
    HasApproximateEquilibriaAtEveryPositiveError reward never ↔
      (⟨reward, never⟩ : QuittingPayoffTable ι).ApproximateEquilibriumExistence := by
  rfl

/-- Journal Theorem 3.4 branch S.1. -/
def HasSmallStationaryApproximateEquilibria
    (table : QuittingPayoffTable ι) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ error : ℝ, 0 < error → error < bound →
    ∃ root : ι → PMF Bool,
      (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff error
        (quittingStationaryProfile table.terminal root)

/-- Journal Theorem 3.4 branch S.2, with error-close minmax punishment. -/
def HasSmallInstantPunishmentApproximateEquilibria
    (table : QuittingPayoffTable ι) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ error : ℝ, 0 < error → error < bound →
    ∃ (quitter : ι) (root : ι → PMF Bool)
      (punishment : (quittingGame table.terminal).BehaviorProfile),
      root quitter = PMF.pure true ∧
        table.bestReplyValue punishment quitter ≤
          table.punishmentValue quitter + error ∧
        (quittingGame table.terminal).IsεAsymptoticNash
          table.terminalPayoff error
          (quittingRootThenContinuationProfile table.terminal root punishment)

/-- Journal Theorem 3.4 branch S.3.  Absorption is from the initial stage;
termination of every restarted tail is not inserted silently. -/
def HasSmallAbsorbingSequentiallyPerfectProfiles
    (table : QuittingPayoffTable ι) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ error : ℝ, 0 < error → error < bound →
    ∃ roots : ℕ → ι → PMF Bool, IsCompletelyAbsorbing roots ∧
      ∀ time, QuittingRowεPerfect table.terminal
        (table.rootSequenceTailVector roots (time + 1)) (roots time) error

theorem hasSmallStationaryApproximateEquilibria_iff_table
    (table : QuittingPayoffTable ι) :
    HasSmallStationaryApproximateEquilibria table ↔
      table.StationaryεEquilibriumExistence := by
  constructor
  · rintro ⟨bound, hbound, hsmall⟩ error herror
    by_cases hbelow : error < bound
    · exact hsmall error herror hbelow
    · obtain ⟨root, hroot⟩ := hsmall (bound / 2) (by linarith) (by linarith)
      exact ⟨root, hroot.mono (by linarith)⟩
  · intro hbranch
    exact ⟨1, by norm_num, fun error herror _ => hbranch error herror⟩

theorem hasSmallInstantPunishmentApproximateEquilibria_iff_table
    (table : QuittingPayoffTable ι) :
    HasSmallInstantPunishmentApproximateEquilibria table ↔
      table.InstantPunishmentεEquilibriumExistence := by
  constructor
  · rintro ⟨bound, hbound, hsmall⟩ error herror
    by_cases hbelow : error < bound
    · exact hsmall error herror hbelow
    · obtain ⟨quitter, root, punishment, hquit, hcap, hnash⟩ :=
        hsmall (bound / 2) (by linarith) (by linarith)
      refine ⟨quitter, root, punishment, hquit, ?_, hnash.mono (by linarith)⟩
      linarith
  · intro hbranch
    exact ⟨1, by norm_num, fun error herror _ => hbranch error herror⟩

theorem hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table
    (table : QuittingPayoffTable ι) :
    HasSmallAbsorbingSequentiallyPerfectProfiles table ↔
      table.SequentiallyεPerfectAbsorbingExistence := by
  constructor
  · rintro ⟨bound, hbound, hsmall⟩ error herror
    by_cases hbelow : error < bound
    · exact hsmall error herror hbelow
    · obtain ⟨roots, habsorbing, hperfect⟩ :=
        hsmall (bound / 2) (by linarith) (by linarith)
      exact ⟨roots, habsorbing, fun time =>
        (hperfect time).mono (by linarith)⟩
  · intro hbranch
    exact ⟨1, by norm_num, fun error herror _ => hbranch error herror⟩

/-- The literal equivalence printed as journal Theorem 3.4. -/
def ApproximateEquilibriumExistenceIffThreeBranchAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) : Prop :=
  HasApproximateEquilibriaAtEveryPositiveError reward never ↔
    HasSmallStationaryApproximateEquilibria ⟨reward, never⟩ ∨
      HasSmallInstantPunishmentApproximateEquilibria ⟨reward, never⟩ ∨
        HasSmallAbsorbingSequentiallyPerfectProfiles ⟨reward, never⟩

/-- The checked forward implication of journal Theorem 3.4.  It uses one
actual chronological source and sends terminal and nonterminal limits to the
literal S.2 and S.3 branches. -/
theorem approximateEquilibria_imply_stationary_or_punishedFirstQuitter_or_absorbingRowPerfection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι)
    (happrox : HasApproximateEquilibriaAtEveryPositiveError reward never) :
    HasSmallStationaryApproximateEquilibria ⟨reward, never⟩ ∨
      HasSmallInstantPunishmentApproximateEquilibria ⟨reward, never⟩ ∨
        HasSmallAbsorbingSequentiallyPerfectProfiles ⟨reward, never⟩ := by
  rw [hasSmallStationaryApproximateEquilibria_iff_table,
    hasSmallInstantPunishmentApproximateEquilibria_iff_table,
    hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table]
  exact QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing
      (⟨reward, never⟩ : QuittingPayoffTable ι) happrox

/-- The universal schema of journal Theorem 3.4 as printed.  This definition
records the live claim without asserting its open reverse implication. -/
def UniversalApproximateEquilibriumExistenceIffThreeBranchAlternative : Prop :=
  ∀ (players : Type) [Fintype players] [DecidableEq players]
      (reward : {S : Finset players // S.Nonempty} → Payoff players)
      (never : Payoff players),
    ApproximateEquilibriumExistenceIffThreeBranchAlternative reward never

/-- The universal printed journal Theorem 3.4 is equivalent to general
finite-quitting terminal approximate-equilibrium existence.  The hard
direction passes through reverse S.3 and its one-added-player reduction; this
does not prove either side of the equivalence. -/
theorem universalThreeBranchAlternative_iff_universalApproximateEquilibriumExistence :
    UniversalApproximateEquilibriumExistenceIffThreeBranchAlternative ↔
      UniversalQuittingApproximateEquilibriumExistence := by
  constructor
  · intro hpublished
    rw [← universalReverseS3_iff_universalApproximateEquilibriumExistence]
    intro players _ _ table hbranch
    apply (hpublished players table.terminal table.never).2
    exact Or.inr (Or.inr
      ((hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table table).2 hbranch))
  · intro happrox players _ _ reward never
    constructor
    · exact
        approximateEquilibria_imply_stationary_or_punishedFirstQuitter_or_absorbingRowPerfection
          reward never
    · intro _hbranch
      exact happrox players ⟨reward, never⟩

/-! ### Checked erratum status for the reverse S.3 implication

The printed reverse implication remains open.  The declarations below record
two checked facts about its S.3 branch.  A nonterminating restarted tail forces
each singleton reward below the Never payoff plus the row error.  Consequently
either all Continue is exact terminal Nash, or every sufficiently accurate
initially absorbing row-perfect witness terminates after every restart.

After that null-tail alternative, even the restricted implication for one
stationary exact every-restart source is universally equivalent to general
finite-quitting terminal approximate-equilibrium existence.  Its hard direction
adds one player, so it makes no same-cardinality claim and does not prove or
refute journal Theorem 3.4.
-/

/-- A nonterminating restarted tail forces the own singleton payoff below the
Never payoff plus the row-perfectness error. -/
theorem nonterminatingRestart_forces_singleton_le_never_add_error
    (table : QuittingPayoffTable ι) (roots : ℕ → ι → PMF Bool)
    (error : ℝ) (habsorbing : IsCompletelyAbsorbing roots)
    (hperfect : ∀ time, QuittingRowεPerfect table.terminal
      (table.rootSequenceTailVector roots (time + 1)) (roots time) error)
    (hnotEveryRestart :
      ¬ QuittingRootSequenceTerminatesAfterEveryRestart roots)
    (player : ι) :
    table.terminal (quittingSingletonTerminal player) player ≤
      table.never player + error := by
  have hbound :=
    table.solo_sub_never_le_of_completelyAbsorbing_not_everyRestart
      roots error habsorbing hperfect hnotEveryRestart player
  linarith

/-- Inclusive null-tail alternative.  Either all Continue is exact terminal
Nash, or every sufficiently accurate initially absorbing row-perfect witness
terminates after each finite restart. -/
theorem allContinueExactNash_or_smallPerfectWitnesses_terminateAfterEveryRestart
    (table : QuittingPayoffTable ι) :
    (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff 0
        (quittingAlwaysContinueProfile table.terminal) ∨
      ∃ bound : ℝ, 0 < bound ∧
        ∀ (error : ℝ) (roots : ℕ → ι → PMF Bool),
          0 < error → error < bound → IsCompletelyAbsorbing roots →
          (∀ time, QuittingRowεPerfect table.terminal
            (table.rootSequenceTailVector roots (time + 1))
            (roots time) error) →
          QuittingRootSequenceTerminatesAfterEveryRestart roots :=
  table.allContinueExactNash_or_everyRestartWitnesses

/-- The paper's small-error S.3 branch can be refined using the checked
small-to-all-error adapter: either all Continue is exact terminal Nash, or it
has witnesses at every sufficiently small error which terminate after every
restart. -/
theorem smallAbsorbingSequentiallyPerfectProfiles_refine_everyRestart
    (table : QuittingPayoffTable ι)
    (hsmall : HasSmallAbsorbingSequentiallyPerfectProfiles table) :
    (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff 0
        (quittingAlwaysContinueProfile table.terminal) ∨
      ∃ bound : ℝ, 0 < bound ∧ ∀ error : ℝ, 0 < error → error < bound →
        ∃ roots : ℕ → ι → PMF Bool,
          IsCompletelyAbsorbing roots ∧
            (∀ time, QuittingRowεPerfect table.terminal
              (table.rootSequenceTailVector roots (time + 1))
              (roots time) error) ∧
            QuittingRootSequenceTerminatesAfterEveryRestart roots := by
  rcases table.allContinueExactNash_or_everyRestartWitnesses with
    hexact | ⟨bound, hbound, hevery⟩
  · exact Or.inl hexact
  · right
    refine ⟨bound, hbound, ?_⟩
    intro error herror herrorBound
    have hall :=
      (hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table table).1 hsmall
    obtain ⟨roots, habsorbing, hperfect⟩ := hall error herror
    exact ⟨roots, habsorbing, hperfect,
      hevery error roots herror herrorBound habsorbing hperfect⟩

/-- Paper-facing name for the restricted exact every-restart source left after
the null-tail alternative. -/
abbrev StationaryExactEveryRestartRowPerfectSource
    (table : QuittingPayoffTable ι) : Prop :=
  table.HasStationaryExactEveryRestartRowPerfectSource

/-- Universally, the restricted stationary exact every-restart implication is
equivalent to terminal approximate-equilibrium existence for all finite
quitting games.  The hard direction maps `players` to `players ⊕ PUnit`; it
does not give a same-cardinality equivalence. -/
theorem universal_stationaryExactEveryRestartSource_iff_terminalApproximateExistence :
    UniversalStationaryExactEveryRestartSourceImpliesApproximateEquilibrium ↔
      UniversalQuittingApproximateEquilibriumExistence :=
  universalStationaryExactEveryRestartSource_iff_approximateExistence

/-! ### Theorem 3.5: refuted printed claim

The printed statement omits the stationary alternative in Solan--Vieille,
Proposition 2.4, and assumes only initial absorption rather than termination
of every restarted tail.
-/

/-- The literal uniform error-exponent assertion printed as Theorem 3.5. -/
def SequentialPerfectionErrorExponentClaim : Prop :=
  ∀ (players : Type) [Fintype players] [DecidableEq players]
    (reward : {S : Finset players // S.Nonempty} → Payoff players)
    (never : Payoff players),
    ∃ bound : ℝ, 0 < bound ∧
      ∀ error : ℝ, 0 < error → error < bound →
        ∀ roots : ℕ → players → PMF Bool, IsCompletelyAbsorbing roots →
          SequentiallyRowwisePerfectAtError reward never roots error →
          (quittingGame reward).IsεAsymptoticNash
            (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩)
            (error ^ ((1 : ℝ) / 6))
            (quittingRootSequenceProfile reward roots 0)

/-- The printed Theorem 3.5 is false. -/
theorem sequentialPerfectionErrorExponentClaim_is_false :
    ¬SequentialPerfectionErrorExponentClaim := by
  intro hclaim
  apply not_quittingSequentialPerfectionErrorExponent
  intro players hfinite hdecidable reward
  obtain ⟨bound, hbound, hsmall⟩ := hclaim players reward 0
  refine ⟨bound, hbound, ?_⟩
  intro error herror hbelow roots habsorbing hperfect
  have hperfect' : SequentiallyRowwisePerfectAtError reward 0 roots error := by
    intro player time
    change QuittingPlayerRowεPerfect reward
      (tailRestartContinuationPayoff reward 0 roots time) (roots time) player error
    rw [tailRestartContinuationPayoff_eq_tableTailVector]
    have htail :
        (⟨reward, 0⟩ : QuittingPayoffTable players).rootSequenceTailVector
            roots (time + 1) =
          quittingRootSequenceTailVector reward roots (time + 1) := by
      funext player
      exact terminalPayoff_repositoryQuittingPayoffTable reward
        (quittingRootSequenceProfile reward roots (time + 1)) player
    rw [htail]
    exact hperfect time player
  have hnash := hsmall error herror hbelow roots habsorbing hperfect'
  have hpayoff :
      QuittingPayoffTable.terminalPayoff ⟨reward, 0⟩ =
        quittingTerminalPayoff reward := by
    funext profile player
    simpa [repositoryQuittingPayoffTable] using
      terminalPayoff_repositoryQuittingPayoffTable reward profile player
  rw [hpayoff] at hnash
  exact hnash

/-- In the two-player witness, switching the prescribed quitter to perpetual
continuation has exact terminal gain one. -/
theorem rowPerfectCounterexample_alwaysContinueDeviationGain_eq_one :
    quittingTerminalPayoff localGlobalCounterexampleReward
        (Function.update localGlobalCounterexampleProfile false
          (quittingAlwaysContinueStrategy localGlobalCounterexampleReward false)) false -
      quittingTerminalPayoff localGlobalCounterexampleReward
        localGlobalCounterexampleProfile false = 1 :=
  localGlobalCounterexample_terminalRegret_eq_one

/-- The corrected Solan--Vieille disjunction needed in place of journal
Theorem 3.5.  Under unit singleton self-exit rewards and zero payoff at Never,
every restarted tail must terminate; then either the supplied profile is an
approximate equilibrium after every restart or a stationary approximate
equilibrium exists. -/
theorem terminatingTails_and_rowPerfection_imply_subgameEquilibrium_or_stationaryEquilibrium
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward) :
    ∃ bound : ℝ, 0 < bound ∧
      ∀ (roots : ℕ → ι → PMF Bool) (error : ℝ),
        0 < error → error < bound →
        (∀ start, Tendsto (quittingJointSurvivalWeight roots start)
          atTop (𝓝 0)) →
        (∀ time, QuittingRowεPerfect reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (roots time) error) →
        (∀ start,
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) (error ^ ((1 : ℝ) / 6))
            (quittingRootSequenceProfile reward roots start)) ∨
          ∃ root : ι → PMF Bool,
            (quittingGame reward).IsεAsymptoticNash
              (quittingTerminalPayoff reward) (error ^ ((1 : ℝ) / 6))
              (quittingStationaryProfile reward root) :=
  exists_quittingSubgamePerfectOrStationary_of_unitSoloExit_of_terminatingTails
    hunit

/-! ## 4. An alternative representation of strategy profiles

### 4.1. A motivating example

For the three-player game `Gamma_eta`, the period-three exact equilibrium at
`eta = 0` is replaced for positive `eta` by period-`3m` profiles in which each
player's block has total conditional quitting probability one half.  Calendar-
time limits lose this behavior; absorption-time limits retain the successive
singleton blocks.

### 4.2. Absorption paths: definition

**Definition 4.1.** Every absorbing strategy profile induces a stepwise
absorption path by recording cumulative coalition absorption mass between its
survival clocks.

At a positive source row, the path jumps at the survival clock to the
cumulative coalition law through that row.  Zero-absorption rows are invisible.
-/

/-- A discrete absorption path induced by an initially absorbing root
sequence, in the paper's Definition 4.1. -/
def IsInducedByAbsorbingRootSequence
    (path : AbsorptionPath (ι := ι)) : Prop :=
  ∃ roots : ℕ → ι → PMF Bool,
    IsCompletelyAbsorbing roots ∧
      pathTimes path.1 = {1} ∧
      pathJumps path.1 =
        {time | ∃ stage,
          time = quittingRootSequenceClock roots stage ∧
            quittingRootSequenceClock roots stage <
              quittingRootSequenceClock roots (stage + 1)} ∧
      ∀ stage,
        quittingRootSequenceClock roots stage <
            quittingRootSequenceClock roots (stage + 1) →
          ∀ coalition,
            path.1.value (quittingRootSequenceClock roots stage) coalition =
              quittingRootSequenceCumulativeCoalitionMass roots
                (stage + 1) coalition

/-!

**Remark 4.2.** Inserting an initial all-Continue row does not change the
induced path.  The printed assertion that this is the only ambiguity is false
after a sure absorption row: the entire unreachable tail can be changed.

The ambient space `F` consists of cadlag, coordinatewise nondecreasing paths of
coalition masses.  The paper defines total mass, left limits, jump set, clock
set, weak convergence, and the lower right derivative before Definition 4.3.
These are represented by `CadlagPath`, `pathTotal`, `pathJump`, `pathJumps`,
`pathTimes`, and `pathRightDerivative`.
-/

/-- Weak convergence in the paper's cumulative-mass coordinates, defined
immediately before journal Definition 4.3. -/
def WeaklyConvergesAbsorptionPaths
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (limit : AbsorptionPath (ι := ι)) : Prop :=
  ∀ time : ℝ, time ∈ Icc (0 : ℝ) 1 → time ∉ pathJumps limit.1 →
    Tendsto (fun index coalition => (sequence index).1.value time coalition)
      atTop (𝓝 fun coalition => limit.1.value time coalition)

/-!

**Definition 4.3.** An absorption path satisfies (A.1)--(A.4): total mass
dominates the clock; gaps are filled by the preceding jump; every jump is a
product law; and continuous motion carries singleton coalitions only.  This is
the bundled type `AbsorptionPath`.
-/

/-- The paper's Definition 4.3, delegated to the bundled repository type. -/
abbrev PaperAbsorptionPath := AbsorptionPath (ι := ι)

/-!

**Remarks 4.4.** The eleven remarks identify jump and continuous intervals,
show constancy on clock gaps, characterize their endpoints, partition
`[0,1)`, prove continuity at one, prove nonsingleton coordinates piecewise
constant, and explain why the lower rather than upper derivative supports
sequential compactness.

**Example 4.5.** The limiting three-player cycle consists of successive
continuous singleton intervals, each absorbing one half of the then-surviving
mass.

**Example 4.6.** A two-player path first uses product rows `(1/3,1/4)` and
`(1/2,0)`, then a continuous interval on which player 1 quits at twice player
2's rate.

**Remark 4.7.** On a continuous interval the singleton derivatives sum to one
and are the players' relative quitting rates.

Weak convergence is equivalently coordinatewise convergence at every point
where the limiting cumulative path has no jump. -/

/-!

**Proposition 4.8.** Every absorption path is the weak limit of paths induced
by absorbing behavior profiles.  In the printed proof the cell law must use
the complete normalized path increment, the large-jump endpoint is the
post-jump total, and the collision factor is `1/(k-1)`, not `1/k`.
-/

/-- At resolution five, a two-player product row refutes the printed `1/k`
collision factor used in the proof of journal Proposition 4.8. -/
theorem printedOneOverResolutionCollisionFactor_failsAtResolutionFive :
    ∃ root : Bool → ℝ,
      (∀ player, 0 ≤ root player ∧ root player ≤ 1) ∧
        1 - Math.PMFProduct.continueMass root = 19081 / 100000 ∧
        1 - Math.PMFProduct.continueMass root < 1 / 5 ∧
        Math.PMFProduct.coalitionMass root Finset.univ /
            Math.PMFProduct.coalitionMass root {false} = 19 / 81 ∧
        1 / 5 < Math.PMFProduct.coalitionMass root Finset.univ /
          Math.PMFProduct.coalitionMass root {false} :=
  akrsPrintedCollisionFactor_five_counterexample

/-- The density statement of journal Proposition 4.8. -/
def EveryAbsorptionPathIsWeakLimitOfAbsorbingProfiles : Prop :=
  ∀ path : AbsorptionPath (ι := ι),
    ∃ approximants : ℕ → AbsorptionPath (ι := ι),
      (∀ resolution,
        IsInducedByAbsorbingRootSequence (approximants resolution)) ∧
      WeaklyConvergesAbsorptionPaths approximants path

/-- Journal Proposition 4.8.  Its corrected full weak-path construction has
not yet been checked in Lean. -/
theorem absorptionPaths_are_weakLimits_of_absorbingProfiles :
    EveryAbsorptionPathIsWeakLimitOfAbsorbingProfiles (ι := ι) := by
  sorry

/-!

**Lemma 4.9.** A sufficiently small correlated row whose nonsingleton atoms
are bounded by `error` times each participating singleton atom is claimed to
admit a product row with the same absorption probability and coordinate error
strictly below `2^|I| * error * absorption`.  The strict estimate is false at
zero absorption, where it requires `0 < 0`.  Replacing it by a weak estimate
gives the checked statement below.  The current journal proof is a Brouwer
argument and differs materially from arXiv v1 Lemma 4.7.
-/

/-- The literal strict-coordinate statement printed as journal Lemma 4.9. -/
def PrintedUniformSmallCellProductization [Nonempty ι] : Prop :=
  ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ 1 / 2 ∧
    ∀ error : ℝ, 0 < error → error ≤ threshold →
      ∀ law : Finset ι → ℝ,
        (∀ coalition, 0 ≤ law coalition) →
        (∑ coalition, law coalition) = 1 →
        1 - law ∅ ≤ error →
        (∀ coalition player, 2 ≤ coalition.card → player ∈ coalition →
          law coalition ≤ error * law {player}) →
        ∃ root : ι → ℝ,
          (∀ player, 0 ≤ root player ∧ root player ≤ 1) ∧
            1 - Math.PMFProduct.continueMass root = 1 - law ∅ ∧
            ∀ coalition, coalition.Nonempty →
              |Math.PMFProduct.coalitionMass root coalition - law coalition| <
                ((2 ^ Fintype.card ι : ℕ) : ℝ) * error * (1 - law ∅)

/-- The printed strict inequality in journal Lemma 4.9 fails for the
all-Continue law, whose absorption mass and coordinate-error bound are zero. -/
theorem printedUniformSmallCellProductization_is_false [Nonempty ι] :
    ¬PrintedUniformSmallCellProductization (ι := ι) := by
  classical
  intro hclaim
  obtain ⟨threshold, hthreshold, _, hsmall⟩ := hclaim
  let error := threshold / 2
  let law : Finset ι → ℝ := fun coalition => if coalition = ∅ then 1 else 0
  have hlawNonneg : ∀ coalition, 0 ≤ law coalition := by
    intro coalition
    simp only [law]
    split_ifs <;> norm_num
  have hlawSum : (∑ coalition, law coalition) = 1 := by
    simp [law]
  have habsorption : 1 - law ∅ ≤ error := by
    simp [law]
    exact (div_pos hthreshold (by norm_num)).le
  have hcollision : ∀ coalition player, 2 ≤ coalition.card →
      player ∈ coalition → law coalition ≤ error * law {player} := by
    intro coalition player hcard _
    have hcoalition : coalition ≠ ∅ := by
      intro hempty
      subst coalition
      simp at hcard
    simp [law, hcoalition]
  obtain ⟨root, _, _, hcoordinate⟩ :=
    hsmall error (div_pos hthreshold (by norm_num))
      (div_le_self hthreshold.le (by norm_num)) law hlawNonneg hlawSum
      habsorption hcollision
  let player : ι := Classical.choice inferInstance
  have hstrict := hcoordinate {player} (Finset.singleton_nonempty player)
  have hboundZero :
      ((2 ^ Fintype.card ι : ℕ) : ℝ) * error * (1 - law ∅) = 0 := by
    simp [law]
  rw [hboundZero] at hstrict
  exact (not_lt_of_ge (abs_nonneg _)) hstrict

/-- The corrected uniform sufficiently-small statement of journal Lemma 4.9,
with a weak coordinate estimate that remains meaningful at zero absorption. -/
def CorrectedUniformSmallCellProductization [Nonempty ι] : Prop :=
  ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ 1 / 2 ∧
    ∀ error : ℝ, 0 < error → error ≤ threshold →
      ∀ law : Finset ι → ℝ,
        (∀ coalition, 0 ≤ law coalition) →
        (∑ coalition, law coalition) = 1 →
        1 - law ∅ ≤ error →
        (∀ coalition player, 2 ≤ coalition.card → player ∈ coalition →
          law coalition ≤ error * law {player}) →
        Nonempty (SmallCellProductization error law)

/-- Checked corrected Lemma 4.9, with the product witness carrying the stronger
support and relative-singleton conclusions used in its proof. -/
theorem correctedUniformSmallCellProductization [Nonempty ι] :
    CorrectedUniformSmallCellProductization (ι := ι) :=
  akrsSmallCellProductizationStatement

/-- Checked strengthened form of journal Lemma 4.9.  It also preserves
relative singleton weights and characterizes the positive singleton support. -/
theorem smallCellProductization_exists [Nonempty ι]
    {error : ℝ} {law : Finset ι → ℝ}
    (herror : 0 < error) (herrorHalf : error ≤ 1 / 2)
    (hlawNonneg : ∀ coalition, 0 ≤ law coalition)
    (hlawSum : (∑ coalition, law coalition) = 1)
    (habsorption : 1 - law ∅ ≤ error)
    (hcollision : ∀ coalition player, 2 ≤ coalition.card →
      player ∈ coalition → law coalition ≤ error * law {player}) :
    Nonempty (SmallCellProductization error law) :=
  exists_akrsSmallCellProductization herror herrorHalf hlawNonneg hlawSum
    habsorption hcollision

/-! **Remark 4.10.** Sure eventual quitting by one player can be represented
by one sure jump, countably many half-probability jumps, one continuous
singleton path, or mixtures of these.

**Proposition 4.11.** Absorption paths are sequentially compact in the paper's
weak topology, with convergent source jumps and product witnesses at every
limiting jump.
-/

/-- The sequential compactness statement of journal Proposition 4.11. -/
def AbsorptionPathSequentialCompactness : Prop :=
  ∀ sequence : ℕ → AbsorptionPath (ι := ι),
    ∃ (limit : AbsorptionPath (ι := ι)) (subsequence : ℕ → ℕ),
      StrictMono subsequence ∧
        WeaklyConvergesAbsorptionPaths (sequence ∘ subsequence) limit ∧
        ∀ time ∈ pathJumps limit.1,
          ∃ (sourceTimes : ℕ → ℝ)
              (sourceRoots : ℕ → ι → PMF Bool)
              (limitRoot : ι → PMF Bool),
            Tendsto sourceTimes atTop (𝓝 time) ∧
              Tendsto (fun index coalition =>
                  (sequence (subsequence index)).1.value
                    (sourceTimes index) coalition)
                atTop (𝓝 fun coalition => limit.1.value time coalition) ∧
              (∀ index,
                sourceTimes index ∈
                    pathJumps (sequence (subsequence index)).1 ∧
                  AbsorptionPathJumpRelation
                    (sequence (subsequence index)) (sourceTimes index)
                    (sourceRoots index)) ∧
              AbsorptionPathJumpRelation limit time limitRoot ∧
              ∀ player action,
                Tendsto (fun index =>
                    ((sourceRoots index player) action).toReal)
                  atTop (𝓝 ((limitRoot player) action).toReal)

/-- Journal Proposition 4.11.  The paper's whole-path weak compactness has not
yet been checked in this interface. -/
theorem absorptionPaths_have_weaklyConvergentSubsequence :
    AbsorptionPathSequentialCompactness (ι := ι) := by
  sorry

/-!

### 4.3. The payoff path

The payoff path is the terminal reward of the still-unassigned mass divided by
remaining live mass, and is set arbitrarily to zero after total absorption.

The repository function `absorptionPathPayoff` is this payoff path.

**Remarks 4.12.** It is bounded by the reward bound; its left value at zero is
the expected path payoff; induced paths recover discrete tail values; on a
continuous path it satisfies the displayed linear differential equation; and
it is continuous at continuity points under weak path convergence.

**Definition 4.13.** At a nonterminal jump, the selected product row is
perfect against the post-jump payoff.  At continuous clock times, singleton
quitting cannot improve continuation, and positive singleton rate forces
indifference.  The predicate is `IsSequentiallyPerfectAbsorptionPath`.

The printed jump clause is imposed only when post-jump total mass is below one.
Consequently it does not test a jump which absorbs all remaining probability.
-/

/-- Journal Definition 4.13 for one player, delegated to the literal jump and
continuous-clock clauses. -/
abbrev PlayerIsSequentiallyPerfectAtAbsorptionPathWithinError :=
  IsPlayerSequentiallyPerfectAbsorptionPath (ι := ι)

/-- Journal Definition 4.13 for every player. -/
abbrev AbsorptionPathIsSequentiallyPerfectWithinError :=
  IsSequentiallyPerfectAbsorptionPath (ι := ι)

/-- The literal path-only Definition 4.13 admits a zero-perfect terminal-jump
path in every nonempty quitting game, independently of its reward table. -/
theorem exists_terminalTotalJump_sequentiallyZeroPerfectAbsorptionPath
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ path : AbsorptionPath (ι := ι),
      IsSequentiallyPerfectAbsorptionPath reward path 0 ∧
        0 ∈ pathJumps path.1 ∧ pathTotal path.1 0 = 1 :=
  exists_sequentiallyZeroPerfectAbsorptionPath_with_terminalTotalJumpAtZero reward

/-! **Proposition 4.14.** Sequential zero-perfectness is closed under weak
limits of paths whose perfection errors tend to zero.
-/

/-- The playerwise closedness assertion of journal Proposition 4.14. -/
def PlayerSequentialPerfectionClosedUnderWeakLimits
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (errors : ℕ → ℝ) (paths : ℕ → AbsorptionPath (ι := ι))
      (limit : AbsorptionPath (ι := ι)) (player : ι),
    (∀ index, 0 ≤ errors index) →
      Tendsto errors atTop (𝓝 0) →
      WeaklyConvergesAbsorptionPaths paths limit →
      (∀ index,
        IsPlayerSequentiallyPerfectAbsorptionPath reward (paths index)
          player (errors index)) →
      IsPlayerSequentiallyPerfectAbsorptionPath reward limit player 0

/-- Journal Proposition 4.14.  Its playerwise whole-path closure argument is
not yet checked in Lean. -/
theorem playerSequentialPerfection_closedUnderWeakLimits
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    PlayerSequentialPerfectionClosedUnderWeakLimits reward := by
  sorry

/-!

**Theorem 4.15.** If all sufficiently small errors have neither a sure-first-
stage equilibrium nor the all-Continue equilibrium, then approximate
equilibria exist at every positive error iff a zero-perfect absorption path
exists.  The converse proof is incomplete: a terminal total jump retains no
off-path continuation with which to test a quitter's deviation to Continue.
-/

/-- The journal's exclusion of its two kinds of simple equilibria. -/
def HasNoSmallSimpleApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ error : ℝ, 0 < error → error < bound →
    (¬∃ profile : (quittingGame reward).BehaviorProfile,
      QuittingProfileAbsorbsSurelyAtFirstStage reward profile ∧
        (quittingGame reward).IsεAsymptoticNash
          (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩) error profile) ∧
      ¬(quittingGame reward).IsεAsymptoticNash
        (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩) error
        (quittingAlwaysContinueProfile reward)

/-- The literal equivalence printed as journal Theorem 4.15. -/
def ApproximateEquilibriumExistenceIffZeroPerfectAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) : Prop :=
  HasNoSmallSimpleApproximateEquilibria reward never →
    (HasApproximateEquilibriaAtEveryPositiveError reward never ↔
      ∃ path : AbsorptionPath (ι := ι),
        IsSequentiallyPerfectAbsorptionPath reward path 0)

/-- For a nonempty player set, the literal journal Theorem 4.15 is exactly the
open assertion that every game in its nonsimple regime has approximate
equilibria.  The path-existence side disappears because Definition 4.13 admits
a zero-perfect terminal-total-jump path in every such game. -/
theorem zeroPerfectAbsorptionPathEquivalence_iff_nonsimpleApproximateEquilibriumExistence
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) :
    ApproximateEquilibriumExistenceIffZeroPerfectAbsorptionPath reward never ↔
      (HasNoSmallSimpleApproximateEquilibria reward never →
        HasApproximateEquilibriaAtEveryPositiveError reward never) := by
  let hexists : ∃ path : AbsorptionPath (ι := ι),
      IsSequentiallyPerfectAbsorptionPath reward path 0 :=
    ⟨(exists_terminalTotalJump_sequentiallyZeroPerfectAbsorptionPath reward).choose,
      (exists_terminalTotalJump_sequentiallyZeroPerfectAbsorptionPath
        reward).choose_spec.1⟩
  constructor
  · intro hpublished hnonsimple
    exact (hpublished hnonsimple).2 hexists
  · intro hnonsimple hnonsimpleGame
    exact ⟨fun _happrox ↦ hexists,
      fun _hpath ↦ hnonsimple hnonsimpleGame⟩

/-- Outside the paper's nonsimple regime, arbitrarily accurate simple
equilibria already give approximate-equilibrium existence. -/
theorem approximateEquilibria_of_not_noSmallSimpleApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι)
    (hnot : ¬HasNoSmallSimpleApproximateEquilibria reward never) :
    HasApproximateEquilibriaAtEveryPositiveError reward never := by
  classical
  intro target htarget
  have hfails : ¬∀ error : ℝ, 0 < error → error < target →
      (¬∃ profile : (quittingGame reward).BehaviorProfile,
        QuittingProfileAbsorbsSurelyAtFirstStage reward profile ∧
          (quittingGame reward).IsεAsymptoticNash
            (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩)
            error profile) ∧
        ¬(quittingGame reward).IsεAsymptoticNash
          (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩) error
          (quittingAlwaysContinueProfile reward) := by
    intro hsmall
    exact hnot ⟨target, htarget, hsmall⟩
  push Not at hfails
  obtain ⟨error, herror, hbelow, hsimple⟩ := hfails
  by_cases hsure : ∃ profile : (quittingGame reward).BehaviorProfile,
      QuittingProfileAbsorbsSurelyAtFirstStage reward profile ∧
        (quittingGame reward).IsεAsymptoticNash
          (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩) error profile
  · obtain ⟨profile, _hfirst, hnash⟩ := hsure
    exact ⟨profile, hnash.mono hbelow.le⟩
  · have hallContinue := hsimple (by
      intro profile hfirst hnash
      exact hsure ⟨profile, hfirst, hnash⟩)
    exact ⟨quittingAlwaysContinueProfile reward,
      hallContinue.mono hbelow.le⟩

/-- The open nonsimple-game existence schema isolated by literal Theorem
4.15. -/
def UniversalNonsimpleApproximateEquilibriumExistence : Prop :=
  ∀ (players : Type) [Fintype players] [DecidableEq players] [Nonempty players]
      (reward : {S : Finset players // S.Nonempty} → Payoff players)
      (never : Payoff players),
    HasNoSmallSimpleApproximateEquilibria reward never →
      HasApproximateEquilibriaAtEveryPositiveError reward never

/-- The nonsimple-game schema is equivalent to general finite-quitting
terminal approximate-equilibrium existence: failure of the nonsimple
hypothesis supplies arbitrarily accurate simple equilibria. -/
theorem universalNonsimpleApproximateEquilibriumExistence_iff_universalApproximateExistence :
    UniversalNonsimpleApproximateEquilibriumExistence ↔
      UniversalQuittingApproximateEquilibriumExistence := by
  classical
  constructor
  · intro hnonsimple players _ _ table
    cases isEmpty_or_nonempty players with
    | inl hempty =>
        letI : IsEmpty players := hempty
        intro error _herror
        refine ⟨quittingAlwaysContinueProfile table.terminal, ?_⟩
        intro who
        exact isEmptyElim who
    | inr hnonempty =>
        letI : Nonempty players := hnonempty
        by_cases hsimple :
          HasNoSmallSimpleApproximateEquilibria table.terminal table.never
        · exact hnonsimple players table.terminal table.never hsimple
        · exact approximateEquilibria_of_not_noSmallSimpleApproximateEquilibria
            table.terminal table.never hsimple
  · intro happrox players _ _ _ reward never _hnonsimple
    exact happrox players ⟨reward, never⟩

/-- Universal literal journal Theorem 4.15 over nonempty finite player sets. -/
def UniversalApproximateEquilibriumExistenceIffZeroPerfectAbsorptionPath : Prop :=
  ∀ (players : Type) [Fintype players] [DecidableEq players] [Nonempty players]
      (reward : {S : Finset players // S.Nonempty} → Payoff players)
      (never : Payoff players),
    ApproximateEquilibriumExistenceIffZeroPerfectAbsorptionPath reward never

/-- Because terminal-total-jump paths make its right side automatic, the
universal literal journal Theorem 4.15 is equivalent to the general
finite-quitting terminal approximate-equilibrium problem. -/
theorem universalZeroPerfectAbsorptionPathEquivalence_iff_universalApproximateExistence :
    UniversalApproximateEquilibriumExistenceIffZeroPerfectAbsorptionPath ↔
      UniversalQuittingApproximateEquilibriumExistence := by
  rw [← universalNonsimpleApproximateEquilibriumExistence_iff_universalApproximateExistence]
  constructor
  · intro hpublished players _ _ _ reward never hnonsimple
    exact (zeroPerfectAbsorptionPathEquivalence_iff_nonsimpleApproximateEquilibriumExistence
      reward never).1 (hpublished players reward never) hnonsimple
  · intro hnonsimple players _ _ _ reward never
    exact (zeroPerfectAbsorptionPathEquivalence_iff_nonsimpleApproximateEquilibriumExistence
      reward never).2 (hnonsimple players reward never)

/-! ## 5. Continuous equilibria

A continuous equilibrium is a sequentially zero-perfect absorption path whose
total mass equals its clock throughout `[0,1]`.  Only singleton rewards enter.
The diagonal is normalized to zero.

This paper-specific conjunction is recorded explicitly below.

**Definition 5.1.** For an `n` by `n` matrix `M` and `q : R^n`, the projective
LCP asks for a nonnegative residual and a simplex weight on a cemetery point
plus the columns of `M`, subject to complementarity.  The printed `q : R` is a
dimension typo.
-/

abbrev LinearComplementarityProblemSolution
    (matrix : ι → ι → ℝ) (offset : ι → ℝ) :=
  ProjectiveLCPSolution matrix offset

abbrev IsProjectiveQMatrix (matrix : ι → ι → ℝ) :=
  GameTheory.QuittingLCPClassification.IsProjectiveQMatrix matrix

/-! **Definition 5.2.** A projective Q-bar matrix is projective-Q on every
nonempty principal submatrix.  The paper says "principal minor" where the
matrix-valued phrase "principal submatrix" is required. -/

abbrev IsProjectiveQBarMatrix (matrix : ι → ι → ℝ) :=
  GameTheory.QuittingLCPClassification.IsProjectiveQBarMatrix matrix

/-! **Remark 5.3.** The paper gives one-, two-, and three-dimensional sign
classifications.  In dimension three the alternatives are an ordered
nonnegative lower sign pattern, or an oriented three-cycle with nonnegative
determinant.

**Theorem 5.4.** If the normalized singleton matrix is projective Q-bar, a
continuous equilibrium exists.  A nonempty player set is implicit and
necessary.
-/

/-- The unnumbered definition at the start of journal Section 5: a continuous
equilibrium is a continuous, sequentially zero-perfect absorption path. -/
def IsContinuousEquilibrium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) : Prop :=
  IsContinuousAbsorptionPath path ∧
    IsSequentiallyPerfectAbsorptionPath reward path 0

/-- With no players, no absorption path can satisfy total-mass domination at
time one. -/
theorem no_absorptionPath_on_emptyPlayerType :
    IsEmpty (AbsorptionPath (ι := Empty)) := by
  constructor
  intro path
  letI : IsEmpty {S : Finset Empty // S.Nonempty} :=
    ⟨fun coalition => by
      obtain ⟨player, _⟩ := coalition.property
      exact player.elim⟩
  have hone := path.property.1 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  rw [pathTotal, Finset.sum_of_isEmpty] at hone
  norm_num at hone

/-- Corrected, checked conclusion of journal Theorem 5.4.  The proof uses
facewise polygonal boundary arcs, compactness of cumulative control-mass paths,
clock reversal, and an explicit terminal filler. -/
theorem continuousEquilibrium_of_projectiveQBar
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hqbar : IsProjectiveQBarMatrix (normalizedSoloMatrix reward)) :
    ∃ path : AbsorptionPath (ι := ι),
      IsContinuousEquilibrium reward path :=
  exists_continuous_zeroPerfect_of_projectiveQBar reward hqbar

/-! **Remark 5.5.** The Q-bar condition is not necessary if a suitable player
face supports a continuous equilibrium and excluded players do not gain by
quitting.  The printed P0-matrix justification must use all principal minors:
`det(M_J + error I_J)` is the sum over principal minors of `M_J`, weighted by
powers of `error`.  The section also distinguishes projective Q from standard
Q and completely-Q matrices.

### The printed Step 2 defect and corrected proof

At a boundary point `q`, the printed correspondence supports controls on the
zero coordinates and tests nonnegative matrix residual only there.  A positive
coordinate may converge to zero, activating a new inequality only at the
limit.  Thus its graph need not be closed even under the theorem's matrix
hypothesis.
-/

/-- The corrected principal-minor expansion needed in journal Remark 5.5. -/
theorem determinant_diagonalPerturbation_eq_sum_principalMinors
    (matrix : Matrix ι ι ℝ) (error : ℝ) :
    (matrix + error • (1 : Matrix ι ι ℝ)).det =
      ∑ players : Finset ι, error ^ (Fintype.card ι - players.card) *
        (matrix.submatrix
          (Subtype.val : players → ι) (Subtype.val : players → ι)).det :=
  Math.LinearAlgebra.det_add_smul_one_eq_sum_principalMinors matrix error

/-- A positive diagonal perturbation has positive determinant when all
principal minors are nonnegative, correcting journal Remark 5.5's determinant
shortcut. -/
theorem positiveDeterminant_of_positiveDiagonalPerturbation_and_nonnegativePrincipalMinors
    (matrix : Matrix ι ι ℝ) {error : ℝ} (herror : 0 < error)
    (hminor : ∀ players : Finset ι,
      0 ≤ (matrix.submatrix
        (Subtype.val : players → ι) (Subtype.val : players → ι)).det) :
    0 < (matrix + error • (1 : Matrix ι ι ℝ)).det :=
  Math.LinearAlgebra.det_add_smul_one_pos_of_principalMinors_nonneg
    matrix herror hminor

/-- The printed viability-control correspondence is not upper
hemicontinuous, even for a zero-diagonal projective-Q-bar matrix. -/
theorem printedViabilityControlCorrespondence_not_upperHemicontinuous :
    ∃ matrix : Bool → Bool → ℝ,
      IsProjectiveQBarMatrix matrix ∧
        (∀ player, matrix player player = 0) ∧
        ¬ UpperHemicontinuous (principalQViabilityControls matrix) :=
  principalQViabilityControls_not_upperHemicontinuous

/-! The corrected construction selects one facewise direction at a time,
extends it only along a locally valid boundary segment, and forms polygonal
Euler chains with vanishing mesh.  Cumulative control mass is uniformly
Lipschitz; compactness preserves nonnegative residual and the limiting support
condition.  Clock reversal gives the path.  An explicit simplex filler covers
the final short interval.  The payoff estimate contains both the initial state
norm and matrix norm, and its correct range is `[0,1-1/n]`.

**Example 5.6.** The three-player cyclic singleton matrix admits a continuous
period-three equilibrium with conditional absorption one half per phase.

**Example 5.7.** A five-player table admits periodic continuous equilibria of
every period `3*l+2` and a nested well-ordered limiting pattern.

**Example 5.8.** A continuous equilibrium may have an index order which is not
well-ordered.  The paper then records the successor recursion
`w = p R^i + (1-p)v`, `w_i = 0`; in generic payoffs a successor edge
`i -> j` has `R_{j i} < 0 < R_{i j}`.
-/

/-! ## 6. Discussion

The paper emphasizes compactness and payoff continuity in absorption time and
asks whether these topological properties force zero-perfect paths beyond the
projective-Q-bar class.  Those research questions are not theorem claims.
-/

/-! ## Map to arXiv:2012.04369v1

The useful number map is:

* journal 3.4 / v1 3.4: v1 is forward-only and asks for exact minmax
  punishment; journal 3.4 is an equivalence with error-close punishment;
* journal 3.5 / v1 3.5: unchanged false claim;
* journal Proposition 4.8 / v1 Proposition 4.6;
* journal Lemma 4.9 / v1 Lemma 4.7: substantively rewritten;
* journal Proposition 4.11 / v1 Proposition 4.9;
* journal Definition 4.13 / v1 Definition 4.11;
* journal Proposition 4.14 / v1 Proposition 4.12;
* journal Theorem 4.15 / v1 Theorem 4.13: journal additionally excludes the
  all-Continue simple equilibrium; and
* journal Theorem 5.4 / v1 Theorem 5.2.

Only semantically distinct v1 statements and useful checked number lookups are
declared below.
-/

namespace ArxivV1

/-- The exact-minmax version of v1 branch S.2. -/
def HasSmallExactMinmaxInstantPunishmentEquilibria
    (table : QuittingPayoffTable ι) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ error : ℝ, 0 < error → error < bound →
    ∃ (quitter : ι) (root : ι → PMF Bool)
      (punishment : (quittingGame table.terminal).BehaviorProfile),
      root quitter = PMF.pure true ∧
        table.bestReplyValue punishment quitter =
          table.punishmentValue quitter ∧
        (quittingGame table.terminal).IsεAsymptoticNash
          table.terminalPayoff error
          (quittingRootThenContinuationProfile table.terminal root punishment)

/-- The distinct forward-only, exact-minmax statement printed as v1 Theorem
3.4.  The journal forward theorem does not prove this stronger S.2 branch. -/
def ExactMinmaxThreeBranchForwardClaim
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) : Prop :=
  HasApproximateEquilibriaAtEveryPositiveError reward never →
    HasSmallStationaryApproximateEquilibria ⟨reward, never⟩ ∨
      HasSmallExactMinmaxInstantPunishmentEquilibria ⟨reward, never⟩ ∨
        HasSmallAbsorbingSequentiallyPerfectProfiles ⟨reward, never⟩

/-- Exact minmax attainment in v1 branch S.2 implies the error-close branch
used by the corrected current theorem. -/
theorem exactMinmaxInstantPunishment_implies_errorCloseInstantPunishment
    (table : QuittingPayoffTable ι)
    (hexact : HasSmallExactMinmaxInstantPunishmentEquilibria table) :
    HasSmallInstantPunishmentApproximateEquilibria table := by
  obtain ⟨bound, hbound, hsmall⟩ := hexact
  refine ⟨bound, hbound, ?_⟩
  intro error herror hbelow
  obtain ⟨quitter, root, punishment, hquit, hminmax, hnash⟩ :=
    hsmall error herror hbelow
  exact ⟨quitter, root, punishment, hquit, by linarith, hnash⟩

/-- The corrected current error-close forward claim which supersedes v1
Theorem 3.4. -/
def ErrorClosePunishmentThreeBranchForwardClaim
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) : Prop :=
  HasApproximateEquilibriaAtEveryPositiveError reward never →
    HasSmallStationaryApproximateEquilibria ⟨reward, never⟩ ∨
      HasSmallInstantPunishmentApproximateEquilibria ⟨reward, never⟩ ∨
        HasSmallAbsorbingSequentiallyPerfectProfiles ⟨reward, never⟩

/-- The corrected current forward statement is proved. -/
theorem errorClosePunishmentThreeBranchForward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) :
    ErrorClosePunishmentThreeBranchForwardClaim reward never :=
  approximateEquilibria_imply_stationary_or_punishedFirstQuitter_or_absorbingRowPerfection
    reward never

/-- The historical v1 exact-minmax statement uses the stronger S.2 witness and
implies the corrected current forward statement.
No converse or refutation of the superseded v1 claim is asserted. -/
theorem exactMinmaxThreeBranchForward_implies_errorClosePunishmentThreeBranchForward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι)
    (hv1 : ExactMinmaxThreeBranchForwardClaim reward never) :
    ErrorClosePunishmentThreeBranchForwardClaim reward never := by
  intro happrox
  rcases hv1 happrox with hstationary | hexact | habsorbing
  · exact Or.inl hstationary
  · exact Or.inr (Or.inl
      (exactMinmaxInstantPunishment_implies_errorCloseInstantPunishment
        ⟨reward, never⟩ hexact))
  · exact Or.inr (Or.inr habsorbing)

/-- V1 Lemma 4.7 additionally claimed uniqueness and prescribed ratios of
individual quit probabilities.  The current journal replaces it by the
existence/Brouwer statement.  This named proposition records the substantive
version difference without identifying the two claims. -/
def UniqueSmallCellProductizationWithRatiosAndCoordinateErrorClaim : Prop :=
  ∀ (players : Type) [Fintype players] [DecidableEq players]
    [Nonempty players],
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ error : ℝ, 0 < error → error ≤ threshold →
        ∀ law : Finset players → ℝ,
          (∀ coalition, 0 ≤ law coalition) →
          (∑ coalition, law coalition) = 1 →
          1 - law ∅ ≤ error →
          (∀ coalition player, 2 ≤ coalition.card → player ∈ coalition →
            law coalition ≤ error * law {player}) →
          ∃! root : players → ℝ,
            (∀ player, 0 ≤ root player ∧ root player < 1) ∧
              1 - Math.PMFProduct.continueMass root = 1 - law ∅ ∧
              (∀ player, 0 < root player ↔ 0 < law {player}) ∧
              (∀ first second,
                root first * law {second} = root second * law {first}) ∧
              (∀ coalition, coalition.Nonempty →
                |Math.PMFProduct.coalitionMass root coalition -
                    law coalition| ≤
                  ((2 ^ Fintype.card players : ℕ) : ℝ) *
                    (Fintype.card players + 1) * error * (1 - law ∅))

/-- V1 Theorem 4.13 omits the journal version's all-Continue exclusion. -/
def SureFirstQuitExcludedPathEquivalenceClaim
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) : Prop :=
  (∃ bound : ℝ, 0 < bound ∧
      ∀ error : ℝ, 0 < error → error < bound →
        ¬∃ profile : (quittingGame reward).BehaviorProfile,
          QuittingProfileAbsorbsSurelyAtFirstStage reward profile ∧
            (quittingGame reward).IsεAsymptoticNash
              (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩)
              error profile) →
    (HasApproximateEquilibriaAtEveryPositiveError reward never ↔
      ∃ path : AbsorptionPath (ι := ι),
        IsSequentiallyPerfectAbsorptionPath reward path 0)

end ArxivV1

end Literature.AshkenaziGolanKrasikovRainerAndSolan2024
