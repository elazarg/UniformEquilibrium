# Robust join predecessors produce an exact persistent-base equilibrium

Author: **CODEX_ROOT**, from a producer-form observation supplied in the
conference intake  
Status: **proof complete; independent review requested**  
Date: 2026-08-26

## 1. Question and result

Let `I` be a finite player set and let `r` be a quitting-game reward table.
For distinct players `e,j`, define the robust join relation

\[
 e\mathrel{\trianglerighteq_r}j
 \quad\Longleftrightarrow\quad
 \forall T\subseteq I\setminus\{e,j\},\qquad
 r_j(T\cup\{e,j\})\ge r_j(T\cup\{e\}).             \tag{1.1}
\]

Thus, whenever `e` belongs to the terminal coalition, adding `j` never hurts
`j`, uniformly over every other coalition background.

The strongest useful adapter is not intrinsically cyclic.

> **Robust-predecessor-base theorem.**  Let `C subseteq I` satisfy
> `|C| >= 2`.  Suppose that every `j in C` has a distinct predecessor
> `e in C` with
> \(e\trianglerighteq_r j\).  Then `C` is a complement-uniform leave-safe
> persistent base.  Consequently the game has a stationary exact terminal
> Nash profile against every behavioral unilateral deviation, and its payoff
> is a uniform-equilibrium payoff.

A directed cycle of \(\trianglerighteq_r\) supplies such a base by taking its
vertex set.  Therefore the robust join graph of any counterexample is acyclic.

For `Fin 4`, this combines with the checked terminal-gap collision map to give
a strict table-level consequence: every hypothetical counterexample contains
a singleton-positive join edge whose join increment is strictly negative on
some nonempty background.  This strengthens the previously reviewed weak
background cancellation from `<= 0` to `< 0` and supplies an actual semantic
consumer for the complementary robust-cycle branch.

The result is ordinary mathematics here.  The persistent-base consumer and
the Fin4 hard-residual/collision-map producers are already Lean-checked; the
new content is the finite robust-predecessor adapter and its strict Fin4
corollaries.

## 2. Probability, information, and agency

At every live date, players independently choose Quit or Continue.  The first
nonempty quitting coalition absorbs with reward `r`; infinite all-Continue
play pays zero.  A unilateral deviation replaces a player's complete
behavioral stopping strategy.

The constructed profile makes every player in `C` Quit surely at date zero.
The complementary players use a mixed Nash equilibrium of their induced
finite binary game.  Since `|C| >= 2`, at least one member of `C` still Quits
at date zero after any one player's arbitrary deviation.  Absorption therefore
remains certain at date zero, and every behavioral deviation reduces exactly
to the deviator's randomized first-stage action.  No stationarity restriction
is imposed on the deviator and no public correlation is introduced.

## 3. From robust predecessors to the checked leave-safe condition

Let `C` satisfy the theorem's hypotheses.  Fix `j in C`, choose a distinct
robust predecessor `e in C`, and fix any complementary quitting set

\[
 Q\subseteq I\setminus C.
\]

Put

\[
 T=(C\setminus\{e,j\})\cup Q.                       \tag{3.1}
\]

Because `Q` is disjoint from `C`,

\[
 T\subseteq I\setminus\{e,j\}.                     \tag{3.2}
\]

The two relevant coalitions are exactly

\[
 T\cup\{e,j\}=C\cup Q,\qquad
 T\cup\{e\}=(C\setminus\{j\})\cup Q.             \tag{3.3}
\]

Applying \(e\trianglerighteq_r j\) to this `T` gives

\[
 r_j(C\cup Q)\ge r_j((C\setminus\{j\})\cup Q).    \tag{3.4}
\]

Since `j` and `Q` were arbitrary, (3.4) is precisely
`QuittingPersistentBaseComplementLeaveSafe r C`.

The checked theorem
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` now
chooses a mixed Nash equilibrium of the finite binary game on `I \ C`, embeds
it with every member of `C` sure-Quit, proves exact terminal Nash against the
full behavioral deviation class, and supplies the uniform-equilibrium payoff.

This proves the robust-predecessor-base theorem.

## 4. Direct behavioral proof and the cycle corollary

For completeness, the semantic argument behind the checked consumer is short.
Let the complementary players use any mixed Nash equilibrium of the finite
one-shot game in which a pure complementary quitter set `Q` produces terminal
coalition `C union Q`.

For a complementary player, every member of `C` still Quits after its
unilateral deviation.  Only its date-zero action matters, and finite-game Nash
optimality rules out a gain.

For `j in C`, another member of `C` remains a sure quitter.  Conditional on
the realized complementary set `Q`, prescribed Quit gives `r_j(C union Q)`
and Continue gives `r_j((C erase j) union Q)`.  Inequality (3.4) holds
pointwise in `Q`, hence also after averaging and after arbitrary randomization
of `j`'s date-zero action.  Later behavior is never reached.

Now suppose

\[
 e_0\trianglerighteq_r e_1\trianglerighteq_r\cdots
 \trianglerighteq_r e_{m-1}\trianglerighteq_r e_0,
 \qquad m\ge2,                                      \tag{4.1}
\]

with pairwise distinct vertices.  Take
`C={e_0,...,e_{m-1}}`.  Every vertex has its preceding cycle vertex as a
distinct robust predecessor, so the theorem applies.

Hence:

\[
 \boxed{
 \text{a directed robust-join cycle}
 \Longrightarrow
 \text{an exact all-behavior terminal Nash profile}.}
                                                               \tag{4.2}
\]

Equivalently, if a finite quitting game has no uniform-equilibrium payoff,
its robust join graph is a directed acyclic graph.  It therefore admits a
topological ordering; in particular every nonempty induced subgraph has a
vertex with no robust predecessor inside that subgraph.

## 5. Strict Fin4 background reversal

Let `I=Fin 4`, and assume the game has no uniform-equilibrium payoff.  Choose
the canonical finite reward bound.  The checked theorem
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
produces a hard residual.  Its checked theorem
`exists_fixedPointFree_terminalGap_collisionMap` supplies a map

\[
 f:I\to I,\qquad f(e)\ne e,                         \tag{5.1}
\]

such that, with terminal gap \(\gamma>0\),

\[
 r_{f(e)}(\{e,f(e)\})-r_{f(e)}(\{e\})\ge\gamma>0   \tag{5.2}
\]

for every `e`.

Every fixed-point-free self-map of a finite nonempty set has a simple directed
cycle

\[
 e_0\to e_1\to\cdots\to e_{m-1}\to e_0,
 \qquad f(e_t)=e_{t+1}.                             \tag{5.3}
\]

If every edge of this cycle were robust, (4.2) would produce a
uniform-equilibrium payoff, contradicting the hard residual's terminal
witness.  Hence some cycle edge `e -> j=f(e)` is not robust.  By negating
(1.1), there is

\[
 T\subseteq I\setminus\{e,j\}
\]

with

\[
 r_j(T\cup\{e,j\})-r_j(T\cup\{e\})<0.             \tag{5.4}
\]

The set `T` is nonempty, because the empty-background increment is strictly
positive by (5.2).  Thus every selected collision-map cycle in a hypothetical
Fin4 counterexample contains a literal strict pair-to-triple or
triple-to-grand reversal.

This improves the earlier collision-cycle cancellation theorem.  That proof
assumed all background increments were strictly positive and obtained a weak
failure `<= 0`.  The semantic consumer here accepts weak robust inequalities;
negating them gives the strict conclusion (5.4).

## 6. Fin4 existence class under no strict background reversal

There is also a table-level corollary that does not mention a residual.
Assume the following **no strict background reversal** condition:

\[
 \begin{aligned}
 &e\ne j,\quad r_j(\{e,j\})>r_j(\{e\})\\
 &\qquad\Longrightarrow\qquad
 e\trianglerighteq_r j.
 \end{aligned}                                      \tag{6.1}
\]

Then the Fin4 game has a uniform-equilibrium payoff.

Indeed, otherwise the checked hard-residual theorem and collision map give
(5.1)--(5.2).  Condition (6.1) makes every collision-map edge robust.  A
functional-graph cycle then contradicts (4.2).

More generally, the same proof applies to any class of finite quitting games
for which a no-uniform-payoff theorem supplies a fixed-point-free positive
singleton-collision selector.  Only the Fin4 selector is currently checked.

## 7. Boundary tests

### 7.1 Weak inequalities are sufficient

The robust relation uses `>=`, not `>`.  Equality on some or every background
is harmless: a base member prescribed to Quit need only be a best response,
not the unique best response.  For the zero reward table every distinct pair
is mutually robust, and every sure-quitting base of size at least two is exact.

### 7.2 Cardinality two is sufficient and sharp for this construction

A two-cycle is covered.  If `C={e,j}`, the two robust inequalities are exactly

\[
 r_j(Q\cup\{e,j\})\ge r_j(Q\cup\{e\}),\qquad
 r_e(Q\cup\{e,j\})\ge r_e(Q\cup\{j\})
\]

for every outsider completion `Q`.

The condition `|C|>=2` is essential.  With a singleton base, its only member
can deviate to Continue and expose the continuation; the finite one-stage
reduction fails.  For a one-player table with singleton reward `-1`, sure Quit
is not Nash while all-Continue is.

### 7.3 Complementary rewards are unrestricted

No sign, boundedness, or support condition is imposed on the payoff
coordinates of players outside `C`.  Their induced finite game may require a
genuinely mixed Nash equilibrium.  The theorem selects that equilibrium; it
does not assume a favorable pure completion.

### 7.4 The robust graph condition is sufficient, not necessary

A leave-safe base may fail the global robust relation on backgrounds that can
never arise while the rest of the base Quits.  For example, with a
three-player base `{0,1,2}`, player `0` may dislike joining player `1` when
`2` is absent but be indifferent or favorable whenever `2` is present.  The
base leave inequality only sees the latter backgrounds.  Thus failure of a
robust predecessor does not imply nonexistence of a persistent-base
equilibrium.

### 7.5 The exact Nash profile need not be a pure sure-exit coalition

The players outside `C` may mix in their induced game.  Consequently a table
may have no pure stable quitting coalition even though the robust-cycle
theorem applies.  This does not place the example outside the already checked
persistent-base arbitrary-completion architecture; the mixed completion is
part of that architecture.

## 8. Source and novelty audit

The central semantic consumer is already checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`:

- `QuittingPersistentBaseComplementLeaveSafe`;
- `exists_quittingPersistentBaseCertificate_of_complementLeaveSafe`;
- `QuittingPersistentBaseCertificate.isZeroAsymptoticNash`; and
- `exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`.

The Fin4 source data are checked in:

- `FullSupportProjectiveQBarResidual.lean`, via
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  and `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual`;
- `PunishmentNormalAtomicCollisionHandoff.lean`, via
  `exists_fixedPointFree_terminalGap_collisionMap`.

The earlier reviewed note
`CODEX_EULER__FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION.md` proved only a
weak nonpositive background cancellation and had no consumer for its robust
complement.  The present result supplies that consumer by proving the new
graph-to-`ComplementLeaveSafe` adapter.  A narrow search found no existing
declaration making this robust-predecessor or directed-cycle deduction.

The producer-form result should not be advertised as a new equilibrium
mechanism independent of persistent bases.  It is a new finite graph
criterion that produces the hypotheses of the checked persistent-base
compiler.  In particular, numerical examples satisfying the cycle condition
are inside the checked leave-safe persistent-base class even if they have no
pure sure-exit equilibrium.

## 9. Lean handoff

A narrow implementation can live beside
`PersistentBaseArbitraryCompletionEscape.lean`, with a Fin4 corollary beside
`PunishmentNormalAtomicCollisionHandoff.lean`.

Suggested declarations:

```lean
def QuittingRobustJoin
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (enforcer joiner : ι) : Prop :=
  enforcer != joiner /\
  forall background,
    background ⊆ (Finset.univ.erase enforcer).erase joiner ->
    quittingSetReward reward (insert joiner (insert enforcer background)) joiner >=
      quittingSetReward reward (insert enforcer background) joiner

def QuittingRobustPredecessorBase
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (base : Finset ι) : Prop :=
  2 <= base.card /\
  forall joiner in base,
    exists enforcer in base, QuittingRobustJoin reward enforcer joiner

theorem QuittingRobustPredecessorBase.complementLeaveSafe ... :
  QuittingPersistentBaseComplementLeaveSafe reward base

theorem exists_exactTerminalNash_and_uniformPayoff_of_robustPredecessorBase ...

theorem exists_uniformPayoff_of_robustJoinCycle ...

theorem finFour_collisionMapCycle_has_strictBackgroundReversal ...

theorem finFour_exists_uniformPayoff_of_noStrictBackgroundReversal ...
```

The exact Lean representation of a simple cycle may reuse a finite functional
graph/walk API if convenient.  It is also enough to state the principal
adapter for a supplied `base` and predecessor function, then derive a cycle
corollary using a finite orbit.  The main set proof is (3.1)--(3.4); the
consumer call is direct.

No new strategy structure, Bellman compiler, or behavioral-cap theorem should
be introduced.

The strict-reversal theorem for a supplied positive selector cycle is valid
for an arbitrary finite player type.  Only the unconditional production of
such a selector from failure of uniform-payoff existence is currently
Fin4-specific.

## 10. Conjecture-facing change and nonclaims

This is a genuine special-case existence theorem with:

- finite reward-table source data (`QuittingRobustJoin`);
- an actual adapter to a checked leave-safe persistent base;
- an exact all-behavior terminal Nash profile; and
- a checked uniform-payoff consumer.

It also gives the strict Fin4 nonsingleton reversal (5.4), replacing the prior
weak static screen.

It does not prove the Fin4 or general finite-quitting conjecture.  A
hypothetical Fin4 counterexample may have an acyclic robust join graph and the
strict reversals described above.  The theorem gives no chronology in that
remaining chamber and imposes no quantitative negative margin beyond strict
sign.

## 11. Requested reviews

Please independently check:

1. the set identities (3.1)--(3.3) and the exact match with
   `QuittingPersistentBaseComplementLeaveSafe`;
2. unrestricted behavioral-deviation coverage of the checked consumer;
3. weak inequality and cardinality-two boundary cases;
4. the directed-cycle and DAG corollaries;
5. the strict sign in the Fin4 collision-map consequence;
6. the unconditional Fin4 no-strict-reversal theorem through the maintained
   hard-residual alternative; and
7. novelty and the proposed minimal Lean adapter.
