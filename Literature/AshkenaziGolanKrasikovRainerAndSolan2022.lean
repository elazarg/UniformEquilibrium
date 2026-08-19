import UniformEquilibrium.Quitting.Classification.ErrorExponentRefutation
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.ThreeByThreeZeroDiagonalQ
import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.AbsorptionPath.RealizedMarkedAbsorptionCylinder

/-!
# Ashkenazi--Golan--Krasikov--Rainer--Solan (2022)

O. Ashkenazi-Golan, I. Krasikov, C. Rainer and E. Solan, *Absorption paths
and equilibria in quitting games*, Mathematical Programming (2022),
arXiv:2012.04369.  This file is pinned to the supplied arXiv v1 archive
(`AKRS.tex`), rather than silently combining it with the published version.

The v1 source uses an arbitrary payoff at never terminating.  The repository
quitting-game adapter has zero as its default, so `never` is carried explicitly
where a source statement needs it.  Unproved paper claims are `sorry`; source
statements whose topology or probability interface is genuinely unavailable
are retained verbatim in comments at their source position.
-/

namespace Literature.AshkenaziGolanKrasikovRainerAndSolan2022

open GameTheory QuittingLCPClassification
open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Section 2 (model)

**Definition 2.1 (source).** A quitting game is a pair `Γ=(I,r)`, where `I`
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

/-! **Definition 3.1 (exact source statement).** For a finite strategic-form
game `G=(I,(Aᶦ),r)`, player `i` is ε-perfect at a mixed profile `ξ` iff, for
every action `aᶦ`,
`rᶦ(aᶦ,ξ⁻ᶦ) ≤ rᶦ(ξ)+ε` and
`ξᶦ(aᶦ)>0 → rᶦ(aᶦ,ξ⁻ᶦ) ≥ rᶦ(ξ)-ε`.

The general strategic-form expected-payoff interface is absent from the
current dependencies, so the exact definition is intentionally retained here
as a source comment.  The following is the faithful playerwise quitting-row
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

/-! **Definition 3.2 (exact source statement).** For a quitting game Γ and
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
-/
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
        table.bestReplyValue punish quitter ≤ table.punishmentValue quitter + ε ∧
        (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff ε
          (quittingRootThenContinuationProfile table.terminal root punish)

def SmallSequentialBranch (table : QuittingPayoffTable ι) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ ε : ℝ, 0 < ε → ε < bound →
    ∃ roots : ℕ → ι → PMF Bool, IsCompletelyAbsorbing roots ∧
      ∀ time : ℕ, QuittingRowεPerfect table.terminal
        (table.rootSequenceTailVector roots (time + 1)) (roots time) ε

/-! **Theorem 3.4 (arXiv v1, forward statement).** If ε-equilibria exist for
every positive ε, then one fixed branch among S.1 (stationary), S.2 (a sure
first-stage quitter with arbitrary-profile punishment at min-max), and S.3
(absorbing sequentially ε-perfect profile) holds for every sufficiently small
positive ε.  The branch predicates above are faithful, but the imported
`ExistenceBranches` interface explicitly records that the Simon--Solan--Vieille
classification itself is not formalized.  The missing proof is precisely the
implication from `EpsilonEquilibriumExistence` to this fixed-disjunct
small-threshold alternative. -/
theorem paper_thm3_4
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι) :
    EpsilonEquilibriumExistence reward never →
      SmallStationaryBranch ⟨reward, never⟩ ∨
        SmallPunishmentBranch ⟨reward, never⟩ ∨
          SmallSequentialBranch ⟨reward, never⟩ := by
  sorry

/-! **Theorem 3.5 (source statement).** For sufficiently small ε, every
absorbing profile at which all players are sequentially ε-perfect is an
`ε^(1/6)`-equilibrium.  The source has arbitrary `r(⃗C)`; this printed claim is
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

theorem paper_thm3_5 : ¬ ErrorExponentBound := by
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

/-! **Corrected Solan--Vieille alternative.** The source cited for Theorem 3.5
gives a disjunction: under the same hypotheses, either the generated profile
is an `ε^(1/6)`-equilibrium, or the game has a stationary ε-equilibrium for
every positive ε.  This is an open proposition here; no placeholder `True`
proposition is introduced. -/

/-! ## Section 4: Definition 4.1 -/

/-! **Definition 4.1 (source).** The source's `𝔽` consists of cadlag,
coordinatewise nondecreasing
subprobability paths `π : [0,1] → [0,1]^{A*}`: in addition to coordinate
bounds, `π̂_t=∑ₐπ_t(a)≤1` is the total absorption mass.  The following
structure stores the exact path and the two one-sided limit clauses. -/
structure CadlagPath where
  /- The carrier is `ℝ` for convenient filters; all mathematical constraints
  and all AP predicates below restrict times to `Icc 0 1`. -/
  value : ℝ → {S : Finset ι // S.Nonempty} → ℝ
  leftValue : ℝ → {S : Finset ι // S.Nonempty} → ℝ
  value_mem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a, 0 ≤ value t a ∧ value t a ≤ 1
  total_le_one : ∀ t ∈ Icc (0 : ℝ) 1, ∑ a, value t a ≤ 1
  monotone : ∀ a, MonotoneOn (fun t => value t a) (Icc 0 1)
  right_continuous : ∀ a t, t ∈ Icc (0 : ℝ) 1 →
    Tendsto (fun s => value s a) (nhdsWithin t (Icc t 1)) (𝓝 (value t a))
  left_limit : ∀ a t, t ∈ Icc (0 : ℝ) 1 →
    Tendsto (fun s => value s a) (nhdsWithin t (Icc 0 t \ {t}))
      (𝓝 (leftValue t a))
  left_zero : ∀ a, leftValue 0 a = 0

noncomputable def pathTotal (path : CadlagPath (ι := ι)) (t : ℝ) : ℝ :=
  ∑ a, path.value t a

def pathJump (path : CadlagPath (ι := ι)) (t : ℝ)
    (a : {S : Finset ι // S.Nonempty}) : ℝ := path.value t a - path.leftValue t a

def pathTimes (path : CadlagPath (ι := ι)) : Set ℝ :=
  {t | t ∈ Icc 0 1 ∧ pathTotal path t = t}

def pathJumps (path : CadlagPath (ι := ι)) : Set ℝ :=
  {t | t ∈ Icc 0 1 ∧ ∃ a, pathJump path t a ≠ 0}

noncomputable def pathRightDerivative (path : CadlagPath (ι := ι)) (t : ℝ)
    (a : {S : Finset ι // S.Nonempty}) : ℝ :=
  Filter.liminf (fun s => (path.value s a - path.value t a) / (s - t))
    (nhdsWithin t (Ioo t 1))

/-! (A.2) is stated directly using connected components of the complement of
`S(π) ∪ T(π)`.  The `sSup` endpoint is the source's right endpoint. -/
def AbsorptionPathA2 (path : CadlagPath (ι := ι)) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1 \ (pathJumps path ∪ pathTimes path),
    ∀ s ∈ connectedComponentIn
      (Icc 0 1 \ (pathJumps path ∪ pathTimes path)) t,
      pathTotal path s = sSup
        (connectedComponentIn (Icc 0 1 \ (pathJumps path ∪ pathTimes path)) t)

def IsAbsorptionPath (path : CadlagPath (ι := ι)) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, t ≤ pathTotal path t) ∧ AbsorptionPathA2 path ∧
  (∀ t ∈ pathJumps path, ∃ ξ : ι → PMF Bool, ∀ a,
    pathJump path t a / (1 - t) = quittingRootCoalitionMass ξ a.1) ∧
  (∀ t ∈ pathTimes path, t ≠ 1 → ∀ a,
    pathRightDerivative path t a ≠ 0 → a.1.card = 1)

def AbsorptionPath := {path : CadlagPath (ι := ι) // IsAbsorptionPath path}

/-! **Payoff path.** For `t<1`, the source defines
`γ_t(π) = (∑ₐ(π₁(a)-π_t(a))r(a))/(1-π̂_t)`, and defines it as zero when
`π̂_t=1`. -/
noncomputable def absorptionPathPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) (t : ℝ) : Payoff ι :=
  if t ∈ Icc (0 : ℝ) 1 then
    if pathTotal path.1 t < 1 then
      fun who => (∑ a, (path.1.value 1 a - path.1.value t a) * reward a who) /
        (1 - pathTotal path.1 t)
    else 0
  else 0

def IsContinuousAbsorptionPath (path : AbsorptionPath (ι := ι)) : Prop :=
  pathTimes path.1 = Icc 0 1

/-! **Definition 4.11, SP.1--SP.2.** The next predicate is the actual
playerwise sequential ε-perfect AP test: at jumps with post-jump mass below
one it applies the quitting-row ε-perfect test to the ξ witnessing (A.3); on
continuous portions it states (SP.2a) and (SP.2b), including the positive
right-derivative implication. -/
def AbsorptionPathJumpRelation (path : AbsorptionPath (ι := ι))
    (t : ℝ) (ξ : ι → PMF Bool) : Prop :=
  ∀ a, pathJump path.1 t a / (1 - t) = quittingRootCoalitionMass ξ a.1

def IsPlayerSequentiallyPerfectAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) (who : ι) (ε : ℝ) : Prop :=
  (∀ t ∈ pathJumps path.1, pathTotal path.1 t < 1 → ∃ ξ,
      AbsorptionPathJumpRelation path t ξ ∧
      PlayerEpsilonPerfectRow reward (absorptionPathPayoff reward path t) ξ who ε) ∧
    (∀ t ∈ pathTimes path.1, t ≠ 1 →
      reward ⟨{who}, Finset.singleton_nonempty who⟩ who - ε ≤
        absorptionPathPayoff reward path t who ∧
      (pathRightDerivative path.1 t
          ⟨{who}, Finset.singleton_nonempty who⟩ > 0 →
        absorptionPathPayoff reward path t who ≤
          reward ⟨{who}, Finset.singleton_nonempty who⟩ who + ε))

def IsSequentiallyPerfectAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) (ε : ℝ) : Prop :=
  (∀ t ∈ pathJumps path.1, pathTotal path.1 t < 1 → ∃ ξ,
      AbsorptionPathJumpRelation path t ξ ∧
        ∀ who, PlayerEpsilonPerfectRow
          reward (absorptionPathPayoff reward path t) ξ who ε) ∧
  ∀ who, ∀ t ∈ pathTimes path.1, t ≠ 1 →
    reward ⟨{who}, Finset.singleton_nonempty who⟩ who - ε ≤
      absorptionPathPayoff reward path t who ∧
    (pathRightDerivative path.1 t
        ⟨{who}, Finset.singleton_nonempty who⟩ > 0 →
      absorptionPathPayoff reward path t who ≤
        reward ⟨{who}, Finset.singleton_nonempty who⟩ who + ε)

/-! **Proposition 4.6 (source).** For every absorption path `π` there is a
sequence of absorbing behavior profiles `(xᵏ)` whose induced paths `πˣᵏ`
converge weakly to `π`.

**Lemma 4.7 (source).** Let `ε>0` be sufficiently small and let `y∈Δ(A)`
satisfy `p(y)≤ε` and `y(a)≤ε y(Qᶦ,C⁻ᶦ)` for every `i` and every
`a∈A*_{≥2}` with `aᶦ=Qᶦ`.  There is a unique `ξ∈[0,1]^I` such that
`p(ξ)=p(y)` and
`ξᶦ/ξʲ=y(Qᶦ,C⁻ᶦ)/y(Qʲ,C⁻ʲ)` (with `0/0=1`), and
`|ξ(a)-y(a)| ≤ 2^{|I|}(|I|+1)εp(y)` for every `a∈A*`.

**Proposition 4.9 (source).** `𝔄` is sequentially compact for the weak
topology: every sequence in `𝔄` has a weakly convergent subsequence with
limit in `𝔄`; moreover at every jump of the limit one can choose convergent
jump times and convergent mixed-action witnesses satisfying (A.3).

**Proposition 4.12 (source).** If `πᵏ⇒π`, `εᵏ→0`, and player `i` is
sequentially `εᵏ`-perfect at `πᵏ` for every `k`, then player `i` is
sequentially 0-perfect at `π`.  The statement is playerwise; the collective
version follows by quantifying this result over `i`.

The source also gives the payoff-path convergence assertion as a remark, not
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

/-! **Definition 5.1 (source v1).** For an `n×n` matrix `R` and `q∈ℝⁿ`,
`LCP(R,q)` asks for `w≥0` and `z=(z₀,…,zₙ)∈Δ({0,…,n})` with
`w=z₀q+∑ᵢzᵢRᶦ` and `zᵢ=0` or `wᵢ=0`. -/
def LinearComplementarityProblemSolution (M : ι → ι → ℝ) (q : ι → ℝ) : Type :=
  ProjectiveLCPSolution M q

def IsQMatrix (M : ι → ι → ℝ) : Prop :=
  ∀ q : ι → ℝ, Nonempty (LinearComplementarityProblemSolution M q)

/-! Theorem 5.2 assumes that `R` and all its principal submatrices are
`Q`-matrices.  The source has no numbered Definition 5.2 and no `Q̄`
definition; that later published notation is deliberately not introduced. -/
/-! Adapter for the principal-submatrix hypothesis in Theorem 5.2; this is
not an additional source definition. -/
def PrincipalQCondition (M : ι → ι → ℝ) : Prop :=
  IsQMatrix M ∧ ∀ players : Finset ι, players.Nonempty →
    IsQMatrix (fun i j : players => M i.1 j.1)

/-! **Remark 5.3 (source).** The condition in Theorem 5.2 is not tight:
continuous equilibria may exist when the matrix condition fails (for example,
when a restriction to a subset of players satisfies it).  It is unknown
whether existence of a continuous equilibrium along which all players quit
with positive probability implies that `R` and all principal submatrices are
`Q`-matrices. -/

/-! **Theorem 5.2 (source v1, open here).** If `R(Γ)` and every principal
submatrix are `Q`-matrices, then a continuous equilibrium exists, i.e. there
is a continuous, sequentially 0-perfect absorption path.  No exact proof is
present in this repository: the missing boundary is the paper's viability-
theory construction of a path in the source's weak absorption-path space,
including its limiting and sequential-perfectness arguments.  The faithful
path predicates above are therefore retained, but this theorem is deliberately
kept as an open source statement rather than an assumed or proxy Lean result.
-/
theorem paper_thm5_2
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hq : PrincipalQCondition (normalizedSoloMatrix reward)) :
    ∃ path : AbsorptionPath (ι := ι),
      IsContinuousAbsorptionPath path ∧
      IsSequentiallyPerfectAbsorptionPath reward path 0 := by
  sorry

end Literature.AshkenaziGolanKrasikovRainerAndSolan2022
