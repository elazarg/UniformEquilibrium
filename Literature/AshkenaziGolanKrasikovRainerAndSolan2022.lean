import UniformEquilibrium.Quitting.Classification.ErrorExponentRefutation
import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRootSequence
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.ThreeByThreeZeroDiagonalQ
import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.AbsorptionPath.HomogeneousContinuousPath
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQControlledTrajectory

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
are retained verbatim in comments at their paper position.
-/

namespace Literature.AshkenaziGolanKrasikovRainerAndSolan2022

open GameTheory QuittingLCPClassification
open GameTheory.QuittingAbsorptionPath
open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

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

/-! ## Section 3 -/

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

/-! **Theorem 3.4 (arXiv v1, forward statement).** If ε-equilibria exist for
every positive ε, then one fixed branch among S.1 (stationary), S.2 (a sure
first-stage quitter with arbitrary-profile punishment at min-max), and S.3
(absorbing sequentially ε-perfect profile) holds for every sufficiently small
positive ε.  The branch predicates above are faithful, but the imported
`ExistenceBranches` interface explicitly records that the Simon--Solan--Vieille
classification itself is not formalized.  The missing proof is precisely the
implication from `EpsilonEquilibriumExistence` to this fixed-disjunct
small-threshold alternative. -/
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
      by_cases hnormalized :
          (∀ who, 0 < quittingSoloReward table.zeroNeverReward who who) ∧
            QuittingWeakSoloExitPreference table.zeroNeverReward
      · right
        right
        exact smallSequentialBranch_of_positiveSolo_of_weakPreference
          table hnormalized.1 hnormalized.2
      · sorry

/-! **Theorem 3.5 (paper statement).** For sufficiently small ε, every
absorbing profile at which all players are sequentially ε-perfect is an
`ε^(1/6)`-equilibrium.  The paper has arbitrary `r(⃗C)`; this printed claim is
false because it omits the stationary alternative of Solan--Vieille. -/
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

/-! ## Section 4: Definition 4.1 -/

/-! **Definition 4.1 (paper).** The paper's ambient `𝔽` consists of cadlag,
coordinatewise nondecreasing paths `π : [0,1] → [0,1]^{A*}`. The reusable
`GameTheory.QuittingAbsorptionPath` interface implements this ambient space
without silently adding the subsequently derived bound `π̂_t≤1`. -/

/-! Conditions (A.1)--(A.4), the payoff path
`γ_t(π) = (∑ₐ(π₁(a)-π_t(a))r(a))/(1-π̂_t)`, and continuity
`T(π)=[0,1]` are the corresponding definitions in that interface. -/

/-! **Definition 4.11, SP.1--SP.2.** The production interface selects one
product-row witness from (A.3) at every jump and uses that same row for every
player in (SP.1).  Its playerwise predicate also states both continuous
conditions (SP.2a)--(SP.2b), including the positive-right-derivative clause. -/

/-! **Proposition 4.6 (paper).** For every absorption path `π` there is a
sequence of absorbing behavior profiles `(xᵏ)` whose induced paths `πˣᵏ`
converge weakly to `π`.

**Lemma 4.7 (paper).** Let `ε>0` be sufficiently small and let `y∈Δ(A)`
satisfy `p(y)≤ε` and `y(a)≤ε y(Qᶦ,C⁻ᶦ)` for every `i` and every
`a∈A*_{≥2}` with `aᶦ=Qᶦ`.  There is a unique `ξ∈[0,1]^I` such that
`p(ξ)=p(y)` and
`ξᶦ/ξʲ=y(Qᶦ,C⁻ᶦ)/y(Qʲ,C⁻ʲ)` (with `0/0=1`), and
`|ξ(a)-y(a)| ≤ 2^{|I|}(|I|+1)εp(y)` for every `a∈A*`.

**Proposition 4.9 (paper).** `𝔄` is sequentially compact for the weak
topology: every sequence in `𝔄` has a weakly convergent subsequence with
limit in `𝔄`; moreover at every jump of the limit one can choose convergent
jump times and convergent mixed-action witnesses satisfying (A.3).

**Proposition 4.12 (paper).** If `πᵏ⇒π`, `εᵏ→0`, and player `i` is
sequentially `εᵏ`-perfect at `πᵏ` for every `k`, then player `i` is
sequentially 0-perfect at `π`.  The statement is playerwise; the collective
version follows by quantifying this result over `i`.

The paper also gives the payoff-path convergence assertion as a remark, not
a numbered proposition.  These statements remain comments because no weak
Stieltjes-path topology or full behavior-profile decoder is available. -/

/-! **Theorem 4.13 (arXiv v1, exact statement).** If a quitting game does not
possess an ε-equilibrium under which the game terminates with probability one
in the first stage, then it admits ε-equilibria for every ε>0 iff it has a
sequentially 0-perfect absorption path.  The full behavior-profile event
“terminates in the first stage with probability one” has no accessor in the
current interface, so this theorem is intentionally not declared with a
proxy or missing hypothesis. -/

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

/-! **Remark 5.3 (paper).** The condition in Theorem 5.2 is not tight:
continuous equilibria may exist when the matrix condition fails (for example,
when a restriction to a subset of players satisfies it).  It is unknown
whether existence of a continuous equilibrium along which all players quit
with positive probability implies that `R` and all principal submatrices are
`Q`-matrices. -/

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

/-! **Theorem 5.2 (paper v1, open here).** If `R(Γ)` and every principal
"minor" (read: principal submatrix) are `Q`-matrices, then a continuous
equilibrium exists, i.e. there is a continuous, sequentially 0-perfect
absorption path. The paper implicitly assumes that the finite player set is
nonempty; without that assumption (A.1) makes the conclusion false at every
positive time. No exact proof is present in this repository: the missing
boundary is now confined to the standard-`Q` side of the exact projective-`Q`
split.  The homogeneous side is proved by the explicit linear path
`exists_continuous_zeroPerfect_of_homogeneous`; the remaining side is the
paper's viability-theory construction, whose printed control correspondence
does not have the claimed closed-graph property. -/
theorem theorem5_2
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hq : PrincipalQCondition (normalizedSoloMatrix reward)) :
    ∃ path : AbsorptionPath (ι := ι),
      IsContinuousAbsorptionPath path ∧
      IsSequentiallyPerfectAbsorptionPath reward path 0 := by
  have hprojective : IsProjectiveQMatrix (normalizedSoloMatrix reward) := hq.1
  rw [isProjectiveQMatrix_iff_standard_or_homogeneous] at hprojective
  rcases hprojective with hstandard | hhomogeneous
  · sorry
  · exact exists_continuous_zeroPerfect_of_homogeneous reward hhomogeneous

end Literature.AshkenaziGolanKrasikovRainerAndSolan2022
