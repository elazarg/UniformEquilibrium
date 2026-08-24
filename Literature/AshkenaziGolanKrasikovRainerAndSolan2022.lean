import UniformEquilibrium.Quitting.Classification.ErrorExponentRefutation
import UniformEquilibrium.Quitting.Classification.Existence.AGKRSTheorem34Dependencies
import UniformEquilibrium.Quitting.Classification.Existence.ExceptionalOwnerPrefixConcentration
import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointPrefixReachEndpoint
import UniformEquilibrium.Quitting.Classification.Existence.PositiveRhoLandingClassificationBoundary
import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRootSequence
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.ThreeByThreeZeroDiagonalQ
import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.Classification.OnePlayer.StationaryBranch
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQContinuousPath

/-!
# Ashkenazi--Golan--Krasikov--Rainer--Solan (2022)

O. Ashkenazi-Golan, I. Krasikov, C. Rainer and E. Solan, *Absorption paths
and equilibria in quitting games*, Mathematical Programming (2022),
arXiv:2012.04369.  This file is pinned to the supplied arXiv v1 archive
(`AKRS.tex`), rather than silently combining it with the published version.

The v1 paper uses an arbitrary payoff at never terminating.  The repository
quitting-game adapter has zero as its default, so `never` is carried explicitly
where a paper statement needs it.  Unproved paper claims are `sorry`; paper
statements whose topology or probability interface is genuinely unavailable
are recorded precisely in comments at their paper position.

There are four kinds of material below.

* A **paper statement** or **paper proof sketch** records the mathematics of
  arXiv v1 in its original order.  A comment is not a checked Lean theorem.
* A theorem with a proof term is a **checked Lean theorem** at exactly its
  displayed type.
* The checked version of Theorem 5.2 is a **corrected repository theorem**:
  it proves the paper's conclusion from the paper's matrix hypothesis, but its
  viability proof uses a support-indexed control correspondence in place of a
  false closed-graph claim in the printed proof.
* The printed statement of Theorem 3.5 is a **refuted printed claim**; the
  theorem named `theorem3_5` proves its negation.

Theorem 3.4 remains only partly proved here: the exact paper implication is
displayed with `sorry`, after the branches and their quantifiers are defined.
-/

namespace Literature.AshkenaziGolanKrasikovRainerAndSolan2022

open GameTheory QuittingLCPClassification
open GameTheory.QuittingAbsorptionPath
open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Section 1 (introduction and proof roadmap)

The paper studies the open problem whether every finite quitting game has an
`ε`-equilibrium for every positive `ε`.  The usual product topology on behavior
profiles is poorly matched to this question: quit probabilities can converge
stage by stage to zero while the induced terminal distribution does not
converge to the payoff of perpetual continuation.

An absorption path replaces calendar time by cumulative absorption.  Its
jumps record stages at which several players may quit simultaneously; its
continuous pieces record diffuse quitting, where only singleton quit events
survive.  This representation makes the relevant path space sequentially
compact and makes continuation payoffs continuous along the convergence used
by the paper.

The proof architecture is as follows.  Section 3 starts from a result of Simon
and Solan--Vieille and extracts stationary, immediate-punishment, or
sequentially perfect approximate profiles.  Section 4 proves that discrete
absorbing profiles are dense in absorption paths, that absorption paths are
sequentially compact, and that sequential perfection is closed under the
resulting convergence.  Thus approximate equilibria produce a sequentially
zero-perfect limiting path, and a suitable path can be discretized back into
approximate equilibria.  Section 5 constructs a continuous zero-perfect path
under a projective linear-complementarity condition, using viability theory.
-/

/-! ## Section 2 (model)

**Definition 2.1 (paper).** A quitting game is a pair `Γ=(I,r)`, where `I`
is a finite player set and `r : ∏ᵢ{Cᶦ,Qᶦ} → ℝᴵ` is the payoff function.
At each stage players choose continue or quit; the first stage with at least
one quitter ends the game and pays `r(a)`, while never quitting pays
`r(⃗C)`.  A mixed row is `ξ∈[0,1]ᴵ`, where `ξᶦ` is the quit probability, and
`p(ξ)=1-∏ᵢ(1-ξᶦ)`.  A behavior strategy is a sequence of conditional quit
probabilities, a profile is a vector of strategies, and an ε-equilibrium is
`γᶦ(x*) ≥ γᶦ(xᶦ,x*⁻ᶦ)-ε` for every player and unilateral strategy.

The repository's `quittingGame` and `Payoff` types provide the corresponding
finite Boolean-action adapter; the arbitrary `r(⃗C)` datum is represented by
the explicit `never` argument in the statements below. -/

/-! ## Section 3 (perfect profiles and the fixed-branch alternative) -/

/-! **Definition 3.1 (exact paper statement).** For a finite strategic-form
game `G=(I,(Aᶦ),r)`, player `i` is ε-perfect at a mixed profile `ξ` iff, for
every action `aᶦ`,
`rᶦ(aᶦ,ξ⁻ᶦ) ≤ rᶦ(ξ)+ε` and
`ξᶦ(aᶦ)>0 → rᶦ(aᶦ,ξ⁻ᶦ) ≥ rᶦ(ξ)-ε`.

The general strategic-form expected-payoff interface is absent from the
current dependencies, so the exact definition is intentionally retained here
as a paper comment.  The following is the faithful playerwise quitting-row
specialization used by Remark 3.3. -/
def PlayerEpsilonPerfectRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : ι → ℝ) (root : ι → PMF Bool) (who : ι) (ε : ℝ) : Prop :=
  quittingRootQuitPayoff reward continuation root who ≤
      quittingRootSuccessorPayoff reward continuation root who + ε ∧
    quittingRootContinuePayoff reward continuation root who ≤
      quittingRootSuccessorPayoff reward continuation root who + ε ∧
    (root who true ≠ 0 →
      quittingRootSuccessorPayoff reward continuation root who - ε ≤
        quittingRootQuitPayoff reward continuation root who) ∧
    (root who false ≠ 0 →
      quittingRootSuccessorPayoff reward continuation root who - ε ≤
        quittingRootContinuePayoff reward continuation root who)

def EpsilonPerfectRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : ι → ℝ) (root : ι → PMF Bool) (ε : ℝ) : Prop :=
  ∀ who, PlayerEpsilonPerfectRow reward continuation root who ε

theorem epsilonPerfectRow_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : ι → ℝ) (root : ι → PMF Bool) (ε : ℝ) :
    EpsilonPerfectRow reward continuation root ε ↔
      QuittingRowεPerfect reward continuation root ε := by
  rfl

/-! **Definition 3.2 (exact paper statement).** For a quitting game Γ and
player i, player i is sequentially ε-perfect at a behavior profile x iff for
every stage n she is ε-perfect at xₙ in `G_Γ(γₙ₊₁(x))`.  The next definition is
the faithful root-sequence adapter used in Theorem 3.4's S.3 branch. -/
noncomputable def sequentialContinuationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : Payoff ι :=
  fun who => QuittingPayoffTable.terminalPayoff ⟨reward, never⟩
    (quittingRootSequenceProfile reward roots (time + 1)) who

def SequentiallyEpsilonPerfect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι)
    (roots : ℕ → ι → PMF Bool) (ε : ℝ) : Prop :=
  ∀ time : ℕ, EpsilonPerfectRow reward
    (sequentialContinuationPayoff reward never roots time) (roots time) ε

/-! **Remark 3.3 (paper).** In the one-shot continuation game at stage `n`,
the payoff from the prescribed row is the conditional payoff `γ_n`.  Quitting
now gives `r(Qᶦ,x_n⁻ᶦ)`, while continuing gives the mixture of absorption by
the opponents and the continuation `γ_{n+1}`.  Hence sequential
`ε`-perfection implies that quitting now gains at most `ε`; if player `i`
quits with positive probability, quitting now also loses at most `ε`. -/

def EpsilonEquilibriumExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ profile : (quittingGame reward).BehaviorProfile,
    (quittingGame reward).IsεAsymptoticNash
      (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩) ε profile

/-! The three fixed-branch predicates below use the arbitrary-never payoff
table interfaces already present in `TableExistenceBranches`.  Each branch has
one small-ε threshold; the disjunction therefore cannot change branch with ε.
In S.2, “at the min-max level” means the usual `ε`-attainment of the infimum,
not an exactly minimizing infinite-horizon profile. -/
def SmallStationaryBranch (table : QuittingPayoffTable ι) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ ε : ℝ, 0 < ε → ε < bound →
    ∃ root : ι → PMF Bool,
      (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff ε
        (quittingStationaryProfile table.terminal root)

def SmallPunishmentBranch (table : QuittingPayoffTable ι) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ ε : ℝ, 0 < ε → ε < bound →
    ∃ (quitter : ι) (root : ι → PMF Bool)
      (punish : (quittingGame table.terminal).BehaviorProfile),
      root quitter = PMF.pure true ∧
        table.bestReplyValue punish quitter ≤
          table.punishmentValue quitter + ε ∧
        (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff ε
          (quittingRootThenContinuationProfile table.terminal root punish)

def SmallSequentialBranch (table : QuittingPayoffTable ι) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ ε : ℝ, 0 < ε → ε < bound →
    ∃ roots : ℕ → ι → PMF Bool, IsCompletelyAbsorbing roots ∧
      ∀ time : ℕ, QuittingRowεPerfect table.terminal
        (table.rootSequenceTailVector roots (time + 1)) (roots time) ε

/-- The paper's “every sufficiently small `ε`” stationary branch is exactly
the production all-positive-tolerances branch, by monotonicity of Nash error. -/
theorem smallStationaryBranch_iff (table : QuittingPayoffTable ι) :
    SmallStationaryBranch table ↔ table.StationaryεEquilibriumExistence := by
  constructor
  · rintro ⟨bound, hbound, hsmall⟩ ε hε
    by_cases hεbound : ε < bound
    · exact hsmall ε hε hεbound
    · obtain ⟨root, hroot⟩ :=
        hsmall (bound / 2) (by linarith) (by linarith)
      exact ⟨root, hroot.mono (by linarith)⟩
  · intro hbranch
    exact ⟨1, by norm_num, fun ε hε _ => hbranch ε hε⟩

/-- S.2's small-threshold form equals the production instant-punishment
branch; both its Nash error and its approximate min-max cap are monotone. -/
theorem smallPunishmentBranch_iff (table : QuittingPayoffTable ι) :
    SmallPunishmentBranch table ↔
      table.InstantPunishmentεEquilibriumExistence := by
  constructor
  · rintro ⟨bound, hbound, hsmall⟩ ε hε
    by_cases hεbound : ε < bound
    · exact hsmall ε hε hεbound
    · obtain ⟨quitter, root, punish, hquit, hcap, hnash⟩ :=
        hsmall (bound / 2) (by linarith) (by linarith)
      refine ⟨quitter, root, punish, hquit, ?_,
        hnash.mono (by linarith)⟩
      linarith
  · intro hbranch
    exact ⟨1, by norm_num, fun ε hε _ => hbranch ε hε⟩

/-- S.3's small-threshold form equals the production absorbing sequentially
perfect branch, since one-stage perfection is monotone in its tolerance. -/
theorem smallSequentialBranch_iff (table : QuittingPayoffTable ι) :
    SmallSequentialBranch table ↔
      table.SequentiallyεPerfectAbsorbingExistence := by
  constructor
  · rintro ⟨bound, hbound, hsmall⟩ ε hε
    by_cases hεbound : ε < bound
    · exact hsmall ε hε hεbound
    · obtain ⟨roots, habsorbing, hperfect⟩ :=
        hsmall (bound / 2) (by linarith) (by linarith)
      refine ⟨roots, habsorbing, fun time =>
        (hperfect time).mono (by linarith)⟩
  · intro hbranch
    exact ⟨1, by norm_num, fun ε hε _ => hbranch ε hε⟩

/-- The positive-solo weak-preference regime lands in the paper's literal
S.3 branch after playerwise scaling relative to the never payoff. -/
theorem smallSequentialBranch_of_positiveSolo_of_weakPreference
    [Nonempty ι] (table : QuittingPayoffTable ι)
    (hsolo : ∀ who,
      0 < quittingSoloReward table.zeroNeverReward who who)
    (hweak : QuittingWeakSoloExitPreference table.zeroNeverReward) :
    SmallSequentialBranch table := by
  rw [smallSequentialBranch_iff]
  exact
    QuittingPayoffTable.sequentiallyεPerfectAbsorbingExistence_of_positiveSolo_of_weakPreference
      table hsolo hweak

/-- If every singleton self-reward is at most the payoff at never, the
literal all-Continue stationary profile is an exact equilibrium. -/
theorem smallStationaryBranch_of_zeroSolo
    (table : QuittingPayoffTable ι)
    (hzero : IsQuittingZeroSolo table.zeroNeverReward) :
    SmallStationaryBranch table := by
  rw [smallStationaryBranch_iff,
    table.stationaryεEquilibriumExistence_iff]
  intro error herror
  exact ⟨quittingAllContinueRoot,
    (isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo
      table.zeroNeverReward hzero).mono herror.le⟩

/-! **Theorem 3.4 (paper statement and proof architecture).** If ε-equilibria exist for
every positive ε, then one fixed branch among S.1 (stationary), S.2 (a sure
first-stage quitter with arbitrary-profile punishment at min-max), and S.3
(absorbing sequentially ε-perfect profile) holds for every sufficiently small
positive ε.

The paper invokes Simon's perfect-equilibrium extraction together with the
Solan--Vieille alternative.  Simon (2012) later corrected Theorem 3 of Simon
(2007): the hypothesis is nonexistence of stationarily generated equilibria,
not merely nonexistence of stationary equilibria.  Thus the corrected cited
argument has a fourth, stationarily generated output.  It does not by itself
prove the displayed three-way theorem; one must additionally compactify that
fourth output into S.1 or S.3.  This is a proof dependency, not a refutation
of the three-way statement.

Since the same branch must work on a punctured interval of error parameters,
the conclusion is stronger than choosing one of three branches separately for
every ε.  In the sequential branch the continuation at stage `n` is the payoff
induced by the actual tail beginning at `n+1`, and the resulting root sequence
must absorb with probability one.

The three predicates above preserve those quantifiers.  The checked proof
below covers the empty-player case, the normalized nonpositive-solo regime,
and a normalized positive-solo weak-preference regime.  The general
fixed-disjunct extraction is the `sorry`; it is not supplied by the production
existence interfaces. -/
theorem theorem3_4
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι) :
    EpsilonEquilibriumExistence reward never →
      SmallStationaryBranch ⟨reward, never⟩ ∨
        SmallPunishmentBranch ⟨reward, never⟩ ∨
          SmallSequentialBranch ⟨reward, never⟩ := by
  intro _hexists
  let table : QuittingPayoffTable ι := ⟨reward, never⟩
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      left
      rw [smallStationaryBranch_iff,
        table.stationaryεEquilibriumExistence_iff]
      intro ε _hε
      refine ⟨fun who => hempty.elim who, ?_⟩
      intro who
      exact hempty.elim who
  | inr hnonempty =>
      letI := hnonempty
      by_cases hzeroSolo : IsQuittingZeroSolo table.zeroNeverReward
      · left
        exact smallStationaryBranch_of_zeroSolo table hzeroSolo
      · by_cases hnormalized :
            (∀ who, 0 < quittingSoloReward table.zeroNeverReward who who) ∧
              QuittingWeakSoloExitPreference table.zeroNeverReward
        · right
          right
          exact smallSequentialBranch_of_positiveSolo_of_weakPreference
            table hnormalized.1 hnormalized.2
        · sorry

/-! **Checked dependency capstone for Theorem 3.4.**  The two missing inputs
are stated in production semantics as
`QuittingPayoffTable.HasCorrectedPointwiseFourWayExtraction` and
`HasDiffuseStationarilyGeneratedCompactification`.  The first is the
source-faithful corrected four-way extraction from arbitrary-never
approximate equilibria.  The second sends the diffuse stationarily generated
residual to S.1 or the well-supported form of S.3.  The theorem below checks
that these two inputs, with no additional arbitrary-never adapter, imply the
literal fixed three-way conclusion above. -/
theorem theorem3_4_of_correctedDependencies
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι)
    (hextraction :
      (⟨reward, never⟩ : QuittingPayoffTable ι).HasCorrectedPointwiseFourWayExtraction)
    (hcompactification : HasDiffuseStationarilyGeneratedCompactification
      (⟨reward, never⟩ : QuittingPayoffTable ι).zeroNeverReward) :
    EpsilonEquilibriumExistence reward never →
      SmallStationaryBranch ⟨reward, never⟩ ∨
        SmallPunishmentBranch ⟨reward, never⟩ ∨
          SmallSequentialBranch ⟨reward, never⟩ := by
  intro hexists
  let table : QuittingPayoffTable ι := ⟨reward, never⟩
  have htableExists : table.ApproximateEquilibriumExistence := hexists
  have hbranches :=
    table.threeBranches_of_correctedExtraction_of_compactification
      hextraction hcompactification htableExists
  rcases hbranches with hstationary | hpunishment | hsequential
  · exact Or.inl ((smallStationaryBranch_iff table).mpr hstationary)
  · exact Or.inr (Or.inl
      ((smallPunishmentBranch_iff table).mpr hpunishment))
  · exact Or.inr (Or.inr
      ((smallSequentialBranch_iff table).mpr hsequential))

/-! **A source-level dependency refinement.**  The preceding capstone asks
the diffuse fourth branch to return only S.1 or S.3.  The actual positive-reach
source can instead close S.2: its reached punishment profiles converge to a
zero-debt endpoint at the punished player's min-max value, and an exact
sure-exit Nash row over that endpoint can be approximated by executable
profiles.  Thus the following checked capstone uses three literal residual
conditions:

* none of the three refined residuals from the corrected pointwise extraction
  occurs at a positive error;
* no positive-joint-reach source remains for which every punishment endpoint
  lacks a sure-exit Nash solution; and
* every unique-exceptional-owner source has divergent prefix length and a
  nonnegative singleton self-payoff for its owner.

These are still hypotheses, not proofs of the cited extraction or
compactification arguments.  Their value is that the positive-reach seam is
allowed to land in its natural paper branch S.2 rather than being forced
through the stronger two-way compactification dependency above. -/
theorem theorem3_4_of_refinedSourceClosures
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι)
    (hpointwise : ∀ δ : ℝ, 0 < δ →
      ¬QuittingCorrectedPointwiseRefinedSourceResidualAt
        (⟨reward, never⟩ : QuittingPayoffTable ι).zeroNeverReward δ)
    (hpositive :
      ¬Nonempty (QuittingPositiveJointPrefixReachNoSureExitResidual
        (⟨reward, never⟩ : QuittingPayoffTable ι).zeroNeverReward))
    (hexceptional :
      ∀ source : QuittingUniqueExceptionalOwnerSource
          (⟨reward, never⟩ : QuittingPayoffTable ι).zeroNeverReward,
        Tendsto
            (fun n ↦ source.family.horizon (source.selected n)) atTop atTop ∧
          0 ≤ quittingSoloReward
            (⟨reward, never⟩ : QuittingPayoffTable ι).zeroNeverReward
            source.owner source.owner) :
    EpsilonEquilibriumExistence reward never →
      SmallStationaryBranch ⟨reward, never⟩ ∨
        SmallPunishmentBranch ⟨reward, never⟩ ∨
          SmallSequentialBranch ⟨reward, never⟩ := by
  intro hexists
  let table : QuittingPayoffTable ι := ⟨reward, never⟩
  have htableExists : table.ApproximateEquilibriumExistence := hexists
  have hextraction : table.HasCorrectedPointwiseFourWayExtraction :=
    table.hasCorrectedPointwiseFourWayExtraction_of_noRefinedSourceResidual
      hpointwise
  have hfixed := fixedCorrectedQuittingBranch_of_pointwiseAlternative
    (hextraction htableExists)
  rcases hfixed with hstationary | hpunishment | hsequential | hdiffuse
  · exact Or.inl ((smallStationaryBranch_iff table).mpr
      (table.stationaryεEquilibriumExistence_iff.mpr hstationary))
  · exact Or.inr (Or.inl ((smallPunishmentBranch_iff table).mpr
      (table.instantPunishmentεEquilibriumExistence_iff.mpr hpunishment)))
  · exact Or.inr (Or.inr ((smallSequentialBranch_iff table).mpr
      (table.sequentiallyεPerfectAbsorbingExistence_iff.mpr
        (quittingSequentiallyεPerfectAbsorbingExistence_of_wellSupported
          hsequential))))
  · rcases
        stationary_or_positiveJointPrefixReachSource_or_uniqueExceptionalOwnerSource
          hdiffuse with hstationary | hpositiveSource | hexceptionalSource
    · exact Or.inl ((smallStationaryBranch_iff table).mpr
        (table.stationaryεEquilibriumExistence_iff.mpr hstationary))
    · obtain ⟨source⟩ := hpositiveSource
      rcases source.instantPunishment_or_noSureExitResidual with
        hpunishment | hresidual
      · exact Or.inr (Or.inl ((smallPunishmentBranch_iff table).mpr
          (table.instantPunishmentεEquilibriumExistence_iff.mpr hpunishment)))
      · exact False.elim (hpositive hresidual)
    · obtain ⟨source⟩ := hexceptionalSource
      obtain ⟨hhorizon, hsolo⟩ := hexceptional source
      have hstationary :=
        source.stationaryεEquilibriumExistence_of_nonnegSolo hhorizon hsolo
      exact Or.inl ((smallStationaryBranch_iff table).mpr
        (table.stationaryεEquilibriumExistence_iff.mpr hstationary))

/-- Theorem 3.4 is unconditional for a one-player quitting game: after
subtracting the arbitrary payoff at never, nonpositive solo reward makes
all-Continue stationary, while positive solo reward makes sure quitting
stationary. -/
theorem theorem3_4_onePlayer
    [Unique ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι) :
    EpsilonEquilibriumExistence reward never →
      SmallStationaryBranch ⟨reward, never⟩ ∨
        SmallPunishmentBranch ⟨reward, never⟩ ∨
          SmallSequentialBranch ⟨reward, never⟩ := by
  intro _hequilibrium
  left
  rw [smallStationaryBranch_iff,
    (⟨reward, never⟩ : QuittingPayoffTable ι).stationaryεEquilibriumExistence_iff]
  exact quittingStationaryεEquilibriumExistence_onePlayer
    (⟨reward, never⟩ : QuittingPayoffTable ι).zeroNeverReward

/-! **Current checked boundary inside the first dependency.**  The
arbitrary-never extraction reaches the corrected four-way conclusion unless
one of three source-derived phenomena survives.  In ordinary mathematical
terms these are:

* a nonzero continuation annotation over an all-Continue limiting row,
  retained together with the actual reached suffixes which realize it;
* a positive-absorption pair of consecutive limiting Bellman rows with
  temporal nonrecurrence, or with an explicit negative punishment-value
  coordinate obstructing automatic boundary admissibility; or
* a positive-survival Bellman spine with a positive singleton self-reward
  and a fixed unrestricted deviation gain on all sufficiently late
  executable suffixes.

The last description is sharper than a bare positive-survival boundary.
When all singleton self-rewards are nonpositive, all-Continue is already an
exact stationary equilibrium, so that half of the former boundary belongs
to S.1.  The persistent late-suffix deviation is an exact checked defect,
not itself an equilibrium branch or a refutation of Theorem 3.4.

The second dependency remains separate.  Its positive-joint-reach source now
has a sharper checked endpoint theorem: the actually reached punishment
suffixes converge to a semantic-carrier point with zero deviation debt for
every player, and the fixed punished player's prescribed payoff and
best-response envelope both equal that player's behavioral min-max value.
If this endpoint admits an exact one-stage Nash root with some sure quitter,
actual profiles realizing the endpoint compile to S.2.  Thus the remaining
positive-reach residual is the explicit finite-dimensional failure of every
such sure-exit root, not merely positive reach itself.  The other source,
with one exceptional player-deleted survival clock, is also partly decoded.
When its repeated-prefix lengths diverge, absorption over the whole prefix
concentrates on the exceptional owner's singleton outcome.  The source Nash
inequality then produces S.1 whenever that owner's singleton self-payoff is
nonnegative.  What remains on this arm is a negative singleton self-payoff,
or a source for which divergent prefix length has not been obtained. -/

/-! **Theorem 3.5 (refuted printed claim).** For sufficiently small ε, every
absorbing profile at which all players are sequentially ε-perfect is an
`ε^(1/6)`-equilibrium.  The paper has arbitrary `r(⃗C)`; this printed claim is
false because it omits the stationary alternative of Solan--Vieille.  The
checked declaration `theorem3_5` proves the negation of the literal uniform
statement below. -/
def ErrorExponentBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι),
    ∃ bound : ℝ, 0 < bound ∧
      ∀ ε : ℝ, 0 < ε → ε < bound →
        ∀ roots : ℕ → ι → PMF Bool, IsCompletelyAbsorbing roots →
          (∀ time : ℕ, EpsilonPerfectRow reward
            (sequentialContinuationPayoff reward never roots time)
            (roots time) ε) →
          (quittingGame reward).IsεAsymptoticNash
            (QuittingPayoffTable.terminalPayoff ⟨reward, never⟩)
            (ε ^ ((1 : ℝ) / 6)) (quittingRootSequenceProfile reward roots 0)

theorem theorem3_5 : ¬ ErrorExponentBound := by
  intro hbound
  apply not_quittingSequentialPerfectionErrorExponent
  intro κ hF hD reward
  obtain ⟨bound, hbound_pos, hsmall⟩ := hbound κ reward 0
  refine ⟨bound, hbound_pos, ?_⟩
  intro ε hε hεbound roots habsorbing hperfect
  have hcont : ∀ time : ℕ,
      sequentialContinuationPayoff reward 0 roots time =
        quittingRootSequenceTailVector reward roots (time + 1) := by
    intro time
    funext who
    change QuittingPayoffTable.terminalPayoff ⟨reward, 0⟩
        (quittingRootSequenceProfile reward roots (time + 1)) who =
      quittingTerminalPayoff reward
        (quittingRootSequenceProfile reward roots (time + 1)) who
    simpa [repositoryQuittingPayoffTable] using
      (terminalPayoff_repositoryQuittingPayoffTable reward
        (quittingRootSequenceProfile reward roots (time + 1)) who)
  have hperfect' : ∀ time : ℕ, EpsilonPerfectRow reward
      (sequentialContinuationPayoff reward 0 roots time) (roots time) ε := by
    intro time
    change QuittingRowεPerfect reward
      (sequentialContinuationPayoff reward 0 roots time) (roots time) ε
    rw [hcont time]
    exact hperfect time
  have hnash := hsmall ε hε hεbound roots habsorbing hperfect'
  have hpayoff :
      QuittingPayoffTable.terminalPayoff ⟨reward, 0⟩ =
        quittingTerminalPayoff reward := by
    funext profile who
    simpa [repositoryQuittingPayoffTable] using
      (terminalPayoff_repositoryQuittingPayoffTable reward profile who)
  rw [hpayoff] at hnash
  exact hnash

/-! **Solan--Vieille's actual per-`ε` alternative.** Proposition 2.4 of
the paper cited for Theorem 3.5 gives a disjunction for each sufficiently
small `ε`: either the generated profile is an `ε^(1/6)`-equilibrium, or the
game has a stationary `ε^(1/6)`-equilibrium. It does not state Theorem 3.5's
unconditional first disjunct. -/

/-! ## Section 4 (alternative representation by absorption paths)

### Motivation and the construction represented by a path

Stationary quit probabilities `1/k` converge pointwise to perpetual
continuation, although for each `k` absorption still occurs almost surely.
Thus ordinary strategy convergence does not control terminal payoffs.  There
is a second obstruction: a limiting conditional distribution over quitting
coalitions need not itself be generated by one product row when several
marginal quit probabilities remain positive.

The absorption parameter resolves both problems.  A path coordinate records
the cumulative probability assigned to one nonempty quitting coalition.  At a
jump, the normalized jump must be generated by a product mixed row.  On a
continuous part, simultaneous quitting is second order, so only singleton
coordinates may have positive right derivative.  The parameter reaches one
exactly when all probability mass has been assigned.

### Definition 4.1 -/

/-! **Definition 4.1 (paper).** The paper's ambient `𝔽` consists of cadlag,
coordinatewise nondecreasing paths `π : [0,1] → [0,1]^{A*}`. The reusable
`GameTheory.QuittingAbsorptionPath` interface implements this ambient space
without silently adding the subsequently derived bound `π̂_t≤1`. -/

/-! Conditions (A.1)--(A.4) are the corresponding definitions in that
interface.  Here `π̂_t` is total accumulated absorption, `S(π)` is the jump
set, and `T(π)` is the set where cumulative absorption equals the path
parameter. -/

/-! **Remarks 4.2 (paper).** On `S(π)` a point represents a discrete product
row and the interval up to `π̂_t` represents the absorption caused by that
row.  On `T(π)` the path runs in continuous absorption time.  The complement
of `S(π)∪T(π)` is partitioned into intervals on which the path is constant.
The path is continuous at `1`; nonsingleton coordinates are piecewise
constant; and the liminf convention in (A.4) is chosen to obtain sequential
compactness.

**Example 4.3 (paper).** For two players, the paper splices three kinds of
behavior: a discrete row with quit probabilities `1/3` and `1/4`, a later row
in which only player 1 quits with probability `1/2`, and a continuous segment
with relative singleton rates `1/2` and `1/4`.  In absorption time the first
two rows become jumps, while the diffuse segment becomes an interval.  For
that path the jump set is `{0, 1/2}` and the continuous set is `[3/4,1]`.

The example explains why an absorption path contains both discrete product-row
witnesses and continuous singleton rates; neither part alone represents all
limits of behavior profiles.

**Remark 4.4 (paper).** Every absorbing behavior profile `x` induces a purely
discrete absorption path `πˣ`.  If `t_n` is the probability of absorption
before stage `n`, then the path on `[t_n,t_{n+1})` records absorption through
stage `n`; its jumps are the `t_n`, its only continuous terminal point is `1`,
and its jump witness at `t_n` is the stage row `x_n`.

**Remark 4.5 (paper).** The map `x ↦ πˣ` is not injective.  Inserting or
deleting stages at which every player continues leaves the absorption path
unchanged, and this is the only ambiguity. -/

/-! **Proposition 4.6 (paper statement).** For every absorption path `π` there is a
sequence of absorbing behavior profiles `(xᵏ)` whose induced paths `πˣᵏ`
converge weakly to `π`.

**Lemma 4.7 (paper statement).** Let `ε>0` be sufficiently small and let `y∈Δ(A)`
satisfy `p(y)≤ε` and `y(a)≤ε y(Qᶦ,C⁻ᶦ)` for every `i` and every
`a∈A*_{≥2}` with `aᶦ=Qᶦ`.  There is a unique `ξ∈[0,1]^I` such that
`p(ξ)=p(y)` and
`ξᶦ/ξʲ=y(Qᶦ,C⁻ᶦ)/y(Qʲ,C⁻ʲ)` (with `0/0=1`), and
`|ξ(a)-y(a)| ≤ 2^{|I|}(|I|+1)εp(y)` for every `a∈A*`.

**Proof architecture for Lemma 4.7.** Matching total absorption and the
singleton ratios determines the product row.  Under the displayed collision
bound, both `y` and the product row put only order-`εp(y)` mass on coalitions
with at least two quitters.  Comparing their total singleton mass and then
using the fixed singleton ratios gives the coordinatewise estimate.

**Proof architecture for Proposition 4.6.** Partition absorption time so that
all large jumps are copied exactly and every remaining cell carries small
mass.  On a small cell, apply Lemma 4.7 to the cell's normalized increment and
insert the resulting product row.  An induction over cells controls cumulative
coordinate error; refining the partition makes the induced behavior-profile
paths converge weakly to the prescribed path.

**Remark 4.8 (paper).** Even the behavior in which one fixed player eventually
quits surely has many path representations: one sure quit jump, repeated
half-probability quit jumps, a continuous singleton path, or mixtures of these
descriptions.  Absorption paths identify their terminal law and absorption
order, not a unique calendar-time implementation.

**Proposition 4.9 (paper statement).** `𝔄` is sequentially compact for the weak
topology: every sequence in `𝔄` has a weakly convergent subsequence with
limit in `𝔄`; moreover at every jump of the limit one can choose convergent
jump times and convergent mixed-action witnesses satisfying (A.3).

**Proof architecture for Proposition 4.9.** Coordinatewise monotonicity and
boundedness give a weakly convergent subsequence.  Conditions (A.1) and (A.2)
pass to the limit.  Near each limiting jump, compactness of product rows and a
diagonal choice recover a limiting jump witness.  On continuous parts, the
small-jump collision estimate suppresses nonsingleton derivatives.  The
liminf right derivative in (A.4) is what survives this weak convergence.

The paper now defines the payoff path
`γ_t(π) = (∑ₐ(π₁(a)-π_t(a))r(a))/(1-π̂_t)` when `π̂_t<1`, and assigns an
irrelevant zero value after all mass is absorbed.  Thus `γ_t` is the
conditional terminal payoff of the unassigned tail mass.

**Remarks 4.10 (paper).** The payoff path stays in the reward bound.  Its
left value at zero is the expected payoff of the path.  For an induced path
`πˣ`, its value just before the `n`th absorption point is the profile's stage
`n` continuation payoff.  On a continuous path it satisfies the displayed
linear differential equation, and at continuity points it is continuous under
weak convergence of absorption paths.

**Definition 4.11 (paper).** Sequential perfection has a jump condition and
two continuous conditions.  At a jump, the generating mixed row must be
perfect in the one-shot game whose continuation is the post-jump payoff.  At
a continuous point, quitting now cannot improve on continuation; a player
whose singleton coordinate grows at positive right rate must be indifferent.
The production interface selects one product-row witness from (A.3) at every
jump and uses that same row for every player in (SP.1).  Its playerwise
predicate states both continuous conditions, including the positive-right-
derivative clause in (SP.2b).

**Proposition 4.12 (paper statement).** If `πᵏ⇒π`, `εᵏ→0`, and player `i` is
sequentially `εᵏ`-perfect at `πᵏ` for every `k`, then player `i` is
sequentially 0-perfect at `π`.  The statement is playerwise; the collective
version follows by quantifying this result over `i`.

**Proof architecture for Proposition 4.12.** At a limiting jump, Proposition
4.9 supplies convergent source jumps and product-row witnesses; convergence of
the tail payoff then passes one-shot perfection to the limit.  At a continuous
point, approximate either by source continuous times or by shrinking source
jumps.  The quit-now inequality passes by payoff continuity, and a positive
liminf singleton derivative supplies the source support needed to pass the
indifference inequality.

The paper also gives payoff-path convergence as an unnumbered remark.  These
paper statements remain comments here because the weak Stieltjes topology and
the full behavior-profile decoder have not been formalized in this module. -/

/-! **Theorem 4.13 (paper statement).** If a quitting game does not
possess an ε-equilibrium under which the game terminates with probability one
in the first stage, then it admits ε-equilibria for every ε>0 iff it has a
sequentially 0-perfect absorption path.  The behavior-profile event now has
the exact repository predicate `QuittingProfileAbsorbsSurelyAtFirstStage`.
The theorem is nevertheless retained as a paper statement rather than a Lean
declaration: its proof needs Proposition 4.6's full path-to-profile decoder
and Proposition 4.12's closure theorem in the weak Stieltjes topology, neither
of which is currently available.

**Paper proof architecture.** In the forward direction, Theorem 3.4 selects a
small-error branch and Proposition 4.12 passes a sequence of sequentially
perfect profiles to a zero-perfect limiting path; the hypothesis excludes the
first-stage sure-termination case.  In the reverse direction, Proposition 4.6
discretizes a zero-perfect path.  Uniform control of continuation payoffs and
the local row errors makes the discretizations ε-equilibria with errors tending
to zero.  No checked Lean theorem is claimed for this equivalence here. -/

/-! ## Section 5 -/

/-! **Definition 5.1 (paper v1).** For an `n×n` matrix `R` and `q∈ℝⁿ`,
`LCP(R,q)` asks for `w≥0` and `z=(z₀,…,zₙ)∈Δ({0,…,n})` with
`w=z₀q+∑ᵢzᵢRᶦ` and `zᵢ=0` or `wᵢ=0`. -/
def LinearComplementarityProblemSolution (M : ι → ι → ℝ) (q : ι → ℝ) : Type :=
  ProjectiveLCPSolution M q

def IsQMatrix (M : ι → ι → ℝ) : Prop :=
  ∀ q : ι → ℝ, Nonempty (LinearComplementarityProblemSolution M q)

/-! Theorem 5.2 says that `R` and all its "principal minors" are
`Q`-matrices. Since the `Q` predicate applies to matrices rather than scalar
minors, the adapter below records the intended principal submatrices. The
paper has no numbered Definition 5.2 and no `Q̄` definition; that later
published notation is deliberately not introduced. -/
/-! Adapter for the principal-submatrix hypothesis in Theorem 5.2; this is
not an additional paper definition. -/
def PrincipalQCondition (M : ι → ι → ℝ) : Prop :=
  IsQMatrix M ∧ ∀ players : Finset ι, players.Nonempty →
    IsQMatrix (fun i j : players => M i.1 j.1)

/-- There is no absorption path with an empty player set: at time `1`, (A.1)
requires positive total absorption mass, but there are no nonempty quitting
coalitions.  This records the implicit nonemptiness premise of Theorem 5.2. -/
theorem no_absorptionPath_empty : IsEmpty (AbsorptionPath (ι := Empty)) := by
  constructor
  intro path
  letI : IsEmpty {S : Finset Empty // S.Nonempty} :=
    ⟨fun coalition => by
      obtain ⟨player, _⟩ := coalition.property
      exact player.elim⟩
  have hone := path.property.1 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  rw [pathTotal, Finset.sum_of_isEmpty] at hone
  norm_num at hone

/-! **Theorem 5.2 (paper statement).** If `R(Γ)` and every principal
"minor" (read: principal submatrix) are `Q`-matrices, then a continuous
equilibrium exists, i.e. there is a continuous, sequentially 0-perfect
absorption path. The paper implicitly assumes that the finite player set is
nonempty; without that assumption (A.1) makes the conclusion false at every
positive time.

**Paper proof architecture.** First, every nonempty principal player set `J`
has a probability vector `z` supported on `J` such that `zR` is nonnegative on
`J` and at least one coordinate is zero.  This follows by applying the
projective LCP to a vector with one negative coordinate and normalizing the
complementary solution.  Second, the paper defines a differential inclusion
on the boundary of the nonnegative orthant: controls are supported on the zero
coordinates of the state, and their `R`-image points into the tangent cone.
Viability theory supplies a boundary-valued trajectory.  Third, trajectories
started at time `1/n` are reversed and interpreted as singleton absorption
rates.  A uniform estimate identifies their continuation payoff with the
boundary trajectory away from the endpoint; compactness then gives a
continuous path satisfying the two conditions of sequential perfection.

**Checked corrected theorem.** The declaration below proves the same
conclusion from the displayed principal-`Q` hypothesis.  Its proof invokes
`exists_continuous_zeroPerfect_of_projectiveQBar`, whose viability argument
uses a support-indexed control correspondence.  The printed correspondence in
the paper does not have the closed-graph property asserted in its Step 2, so
the checked proof is not a formalization of that defective intermediate
claim.  In particular, the paper is not being credited with the corrected
support-indexed correspondence. -/
theorem theorem5_2
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hq : PrincipalQCondition (normalizedSoloMatrix reward)) :
    ∃ path : AbsorptionPath (ι := ι),
      IsContinuousAbsorptionPath path ∧
      IsSequentiallyPerfectAbsorptionPath reward path 0 := by
  apply exists_continuous_zeroPerfect_of_projectiveQBar reward
  intro players hplayers
  exact hq.2 players hplayers

/-! **Remark 5.3 (paper).** The condition in Theorem 5.2 is not tight:
continuous equilibria may exist when the matrix condition fails, for example
when a restriction to a subset of players satisfies it.  It is unknown whether
existence of a continuous equilibrium along which every player quits with
positive probability forces `R` and all principal submatrices to be
`Q`-matrices.

**Example 5.4 (paper).** For the three-player solo-reward columns
`(0,2,-1)`, `(-1,0,2)`, and `(2,-1,0)`, a continuous equilibrium cycles
through players `1,2,3`, each with conditional absorption coefficient `1/2`.
All continuous equilibria in this example arise by starting within that
periodic path.

**Example 5.5 (paper).** A displayed five-player table has periodic continuous
equilibria of every period `3l+2`, with player order consisting of `l` cycles
through `1,2,3` followed by `4,5`.  It also has a limiting nested pattern
corresponding to `l=∞`.  The paper leaves open whether some game has a
continuous equilibrium but no finite-period continuous equilibrium. -/

/-! ## Section 6 (discussion)

The paper's representation separates two equilibrium mechanisms which can
coexist in one profile.  Jumps encode publicly visible discrete stages with
simultaneous quitting risk.  Continuous pieces encode a diffuse quitting time:
players know the prescribed hazard law but cannot identify an exact stage at
which a quit is scheduled.

The compactness results give a conditional structural conclusion.  Whenever
arbitrarily accurate equilibria exist in the regime covered by Theorem 4.13,
their absorption paths have a sequentially zero-perfect limit.  Conversely, a
zero-perfect path can be approximated by discrete profiles with vanishing
incentive error.  Thus the absence of an exact discrete-time equilibrium is
interpreted as a failure to implement the diffuse timing device exactly, not
as a discontinuity of the absorption-path payoff itself.

The paper emphasizes that the absorption-path space is compact, payoff
continuous under its weak convergence, and contractible.  It leaves open
whether these topological features, beyond the projective-`Q` class of Section
5, can force a zero-perfect path or otherwise settle existence of approximate
equilibria.  This discussion states research directions; it is not a theorem
proved by the declarations in this file. -/

end Literature.AshkenaziGolanKrasikovRainerAndSolan2022
