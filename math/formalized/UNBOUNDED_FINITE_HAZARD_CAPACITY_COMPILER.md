# Unbounded finite Nash--Bellman hazard capacity compiles to a uniform payoff

Authors: GPT, CODEX_ROOT, CODEX_STRENGTHEN

Independent reviews:

- [adversarial audit](../feedback/NONZERO_PERSIST_ATTEMPT_1__BY_CODEX_ADVERSARY.md)
- [source and unrestricted-behavior gate](../feedback/CODEX_STRENGTHEN__FIN4_NONZERO_PERSISTENT_SPINE_SELECTION__BY_CODEX_SOURCE_GATE.md)

## Exact statement

Let \(I\) be finite and let \(r\) be a finite quitting reward table.  For a
product root \(x\in[0,1]^I\), write

\[
 h(x)=\sum_{i\in I}x_i.
\]

A finite exact Nash--Bellman block is a word

\[
 B=(v_0,x_0,v_1,\ldots,x_{n-1},v_n)
\]

such that

\[
 v_t=F_{x_t}(v_{t+1})
\]

and \(x_t\) is an exact Nash root against \(v_{t+1}\), for every \(t<n\).
Its marginal-hazard charge is

\[
 H(B)=\sum_{t<n}h(x_t).
\]

Fix a compact set \(K\subset\mathbb R^I\), and assume that all annotations of
the blocks below belong to \(K\).

### Theorem A: finite-capacity extraction

If finite exact Nash--Bellman blocks with annotations in \(K\) have unbounded
charge, then there are bounded annotations \(w_t\in K\), product roots
\(y_t\), and nonnegative sequences \(\beta_t,\nu_t\) such that

\[
 \lVert w_t-F_{y_t}(w_{t+1})\rVert_\infty\le\beta_t,
 \qquad \sum_t\beta_t<\infty,
\]

\[
 \sup_{z_i\in[0,1]}
 \left(
 F_{y_t[i\leftarrow z_i]}(w_{t+1})_i
 -F_{y_t}(w_{t+1})_i
 \right)
 \le\nu_t,
 \qquad \sum_t\nu_t<\infty,
\]

and one fixed player \(p\in I\) satisfies

\[
 \sum_t y_{t,p}=\infty.
\]

The total residual \(\sum_t(\beta_t+\nu_t)\) may be made arbitrarily small.
No source or ancestry hypothesis is needed after the same-table exact blocks
have been supplied.

### Theorem B: persistent approximate-spine consumers

Assume the output of Theorem A.

1. If two distinct players have divergent marginal-hazard series, the game
   has a uniform-equilibrium payoff.
2. If exactly one player \(p\) has divergent marginal-hazard series, every
   other marginal series is summable, and \(p\) is punishment-normal, then
   the singleton reward vector \(r(\{p\})\) is a uniform-equilibrium payoff.

Both conclusions quantify over every unilateral behavioral stopping strategy,
including Never and arbitrarily late, randomized stopping.

### Fin4 capstone

If a four-player quitting game is punishment-normal and its finite exact
Nash--Bellman blocks in the canonical bounded reward cube have unbounded
marginal-hazard charge, then it has a uniform-equilibrium payoff.

Consequently, under the checked Fin4 hard-residual implication from absence of
a uniform payoff to punishment normality,

\[
 \boxed{
 \text{no Fin4 uniform-equilibrium payoff}
 \Longrightarrow
 \sup_B H(B)<\infty .}
\]

## Conjecture-facing change

The supremum ranges over every finite exact Nash--Bellman block in the fixed
canonical bounded value cube.  This is a strict reduction of
`questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`: the unbounded finite
capacity branch is consumed, and only the finite-capacity all-summable branch
remains.

## Proof of Theorem A

For a block \(B\), define cumulative charge

\[
 C_t=\sum_{s<t}h(x_s).
\]

One row has charge at most \(|I|\).  Fix \(\delta>0\), and cover \(K\) by
\(N\) sets of diameter less than \(\delta\).  Choose a block with

\[
 H(B)>(|I|+1)N.
\]

For \(0\le j\le N\), let \(t_j\) be the first index satisfying

\[
 C_{t_j}\ge (|I|+1)j.
\]

Minimality of \(t_j\) and the one-row bound give

\[
 C_{t_j}< (|I|+1)j+|I|.
\]

Two of the (N+1) marked payoff vectors lie in one cover set.  If their
indices are (a<b), the intervening contiguous exact subblock has endpoint
distance less than \(\delta\), while its charge is at least

\[
 (|I|+1)(b-a)-|I|\ge1.
\]

Apply this construction with \(\delta_k\downarrow0\).  Compactness gives a
subsequence of exact blocks \(B_k\) whose initial and terminal annotations
\(a_k,b_k\) converge to one common point.  Refine rapidly enough that

\[
 \sum_k\lVert b_k-a_{k+1}\rVert_\infty<\infty.
\]

Concatenate the literal root words.  Every internal row remains exact.  At
the last root of \(B_k\), the old expected successor was \(b_k\), while the
new successor annotation is \(a_{k+1}\).  Bellman prefixing is \(1\)-Lipschitz
in its tail, so the Bellman residual at this seam is at most

\[
 d_k=\lVert b_k-a_{k+1}\rVert_\infty.
\]

For every unilateral root replacement, both the prescribed root payoff and
the replaced root payoff change by at most \(d_k\).  Exact Nash against
\(b_k\) therefore becomes root-Nash defect at most \(2d_k\) against
\(a_{k+1}\).  Put \(\beta=d_k\), \(\nu=2d_k\) at seams and zero elsewhere.
The residual series are summable.

Each copied block has charge at least one.  Hence

\[
 \sum_t\sum_{i\in I}y_{t,i}=\infty.
\]

Since \(I\) is finite, one fixed player has a divergent marginal series.
Choosing the fast subsequence with an arbitrarily small prescribed sum of
seam distances proves the final quantitative assertion.

## Proof of Theorem B, two persistent labels

Put

\[
 P_t=F_{y_t}(w_{t+1}),\qquad
 S_t=(w_{t+1},w_{t+1}),\qquad
 C_t=\operatorname{Prefix}_{y_t}(S_t).
\]

The successor \(S_t\) is diagonal.  Thus the debt of player \(i\) in \(C_t\)
is exactly the gain from replacing its prescribed root marginal by its best
root endpoint.  The approximate root-Nash inequality gives

\[
 0\le d_i(C_t)\le\nu_t. \tag{1}
\]

Shift the construction to an arbitrary time \(T\).  The exact candidate step
at calendar \(n\) is the prefix \(C_{T+n}\), and its successor is
\(S_{T+n}\).  The seam is between \(S_{T+n}\) and \(C_{T+n+1}\).  Coordinatewise,

\[
 \operatorname{prescribedSeam}(n)\le\beta_{T+n+1}, \tag{2}
\]

\[
 \operatorname{capSeam}(n)
 \le\beta_{T+n+1}+\nu_{T+n+1}, \tag{3}
\]

and hence

\[
 \operatorname{totalSeam}(n)
 \le2\beta_{T+n+1}+\nu_{T+n+1}. \tag{4}
\]

The initial candidate debt is at most \(\nu_T\) by (1).  Because
\(\beta,\nu\) are summable, their tails and \(\nu_T\) tend to zero.  Equations
(1)--(4) therefore give the prescribed/cap semantic seam source required by
the checked summable-seam consumer at every accuracy.

If two fixed marginal labels are persistent, deleting any one player leaves
at least one persistent clock.  Thus both joint survival and every
player-deleted survival vanish for these literal roots.  The checked
summable-seam consumer now supplies terminal approximate equilibria with one
limiting payoff, and hence a uniform-equilibrium payoff.  Its caps quantify
over complete behavioral replacements, not only stationary deviations.

## Proof of Theorem B, one persistent label

Assume \(p\) is the unique persistent player.  Every opponent marginal is
summable.  Let \(U_t\) be the literal terminal payoff vector of the root
schedule beginning at \(t\).  Persistence of \(p\) forces joint survival to
zero, so \(U\) is bounded and satisfies the exact Bellman recursion

\[
 U_t=F_{y_t}(U_{t+1}).
\]

Let

\[
 B_t=\sum_{s\ge t}\beta_s.
\]

Iteration of the Bellman contraction, followed by the vanishing joint
survival remainder, gives

\[
 \lVert w_t-U_t\rVert_\infty\le B_t. \tag{5}
\]

The exact bounded-Bellman concentration estimate applied to \(U\), together
with summability of \(p\)'s opponent clock, gives

\[
 \lVert U_t-R\rVert_\infty
 \le 2M\,\operatorname{OpponentClockTail}(p,t), \tag{6}
\]

where \(M\) bounds rewards and annotations and
\(R=r(\{p\})\) is the singleton reward vector.

Choose increasing dates \(t_n\) with \(y_{t_n,p}>0\).  At those dates,
approximate root Nash and Bellman give each outsider's pure-Quit endpoint
bound with error

\[
 \beta_{t_n}+\nu_{t_n}. \tag{7}
\]

Use in the checked deleted-Quit endpoint consumer:

- hazard error equal to \(p\)'s opponent-clock charge at \(t_n\);
- target error equal to
  \(B_{t_n}+2M\operatorname{OpponentClockTail}(p,t_n)\);
- Quit error equal to \(\beta_{t_n}+\nu_{t_n}\).

All three vanish.  Punishment normality supplies the owner's punishment
inequality.  The consumer constructs punishment-completed terminal
approximants to \(R\), controls every unilateral behavioral deviation, and
therefore makes \(R\) a uniform-equilibrium payoff.

The two cases exhaust every nonempty persistent set and prove the Fin4
capstone.

## Probability and strategy audit

- Roots are simultaneous independent product actions at the unique live
  public history.
- Exact root Nash and its residual quantify over every mixed marginal root
  replacement.
- The constructed infinite schedule is a literal behavioral profile.
- The two-persistent consumer uses player-deleted survival, so arbitrary
  calendar-dependent, randomized and Never deviations are included.
- The unique-persistent consumer uses the checked deleted-Quit and punishment
  completion theorem, which likewise quantifies over the unrestricted
  behavioral strategy class.
- No bounded deadline, stationary-deviation restriction, or attainment of an
  infinite-horizon cap is introduced.

## Boundary tests

1. If one positive-charge exact block has equal endpoints, periodic repetition
   gives an exact persistent spine.  The extraction specializes to this
   zero-seam case.
2. Finite exact chains may have charge tending to infinity while every fixed
   calendar root converges to all-Continue.  The four-player table with one
   player receiving (1) exactly when it quits, a final sure-Quit row, and
   preceding hazard \(N^{-1/2}\), has this behavior.  Ordinary prefix-diagonal
   compactification loses its charge; the near-return subblock extraction does
   not.
3. The canonical all-Continue phantom has zero capacity along its own path and
   is not consumed by this theorem.
4. Punishment normality is essential in the unique-persistent target
   conclusion.  A one-player exact persistent spine at a negative singleton
   reward converges to that reward although Never yields zero.

## Source correspondence

The checked exact-spine and consumer endpoints are:

- `IsCanonicalExactQuittingNashBellmanSpine` and the bounded exact-spine
  interfaces in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`;
- the exact Bellman concentration and normal unique-persistent compiler added
  at repository commit `a0842d13`;
- `HasTwoPersistentQuittingMarginals.survival` in
  `UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors`
  in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`;
- `isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits` in
  `UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean`;
- Fin4 hard-residual punishment normality and the literal no-uniform-payoff
  summability corollary added at `a0842d13`.

The new ordinary mathematics is the compact-cover extraction and the two
summable-residual adapters.  The checked exact consumers do not already accept
these approximate inputs verbatim.

## Adapter and consumer

The actual-data hypothesis is deliberately exact and source-free: it ranges
over finite Nash--Bellman blocks for the supplied reward table in its canonical
compact value cube.  If their charge is unbounded, Theorem A constructs the
literal persistent approximate spine.  Theorem B then reaches the existing
unrestricted-strategy terminal consumers.  No selected minimum source, law,
atom or atlas packet is required in this branch.

## Lean handoff

Suggested declarations, in dependency order:

1. `exists_nearReturn_exactBlock_of_hazardCapacity_gt`;
2. `exists_summableResidual_persistentSpine_of_unbounded_exactBlockHazard`;
3. `quittingSummableSeamSource_of_summableNashBellmanResiduals` with the exact
   ledger (1)--(4);
4. `isUniformEquilibriumPayoff_of_twoPersistent_summableNashBellmanResiduals`;
5. `isUniformEquilibriumPayoff_soloReward_of_uniquePersistent_summableResiduals`
   using (5)--(7);
6. `exists_uniformEquilibriumPayoff_of_unbounded_exactBlockHazardCapacity`;
7. the Fin4 no-uniform-payoff finite-capacity corollary.

The formalizer should reuse the checked exact concentration and persistent
consumers rather than reproduce them.  Finite covers may be expressed through
total boundedness of the canonical finite-dimensional value cube.

## Scope and nonclaims

- The theorem does not prove that Fin4 exact-block capacity is unbounded.
- It does not consume the finite-capacity all-summable branch.
- The resulting capacity bound is real-valued and is not a well-founded rank.
- No claim is made that the capacity supremum is attained or upper
  semicontinuous.
- The theorem proves existence of a uniform-equilibrium payoff, not an exact
  stationary equilibrium.

## Lean formalization record

Pre-formalization packet SHA-256:
`8c7eae46ddb04fdd327e307170ffe41ade9437f56c5d425d895894e87253aee0`.

The implementation landed in commits
`b3e370483960c852b9315533da774056d6858598`,
`ff46b0b4db3d01dde15ff97d6f4c748b25448360`, and
`e509d5c355a98afa361ff3b8688ba355b4aa278b`.  The exact-block capacity,
return extraction, and residual-spine layers are in
`UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`
and
`UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualNashBellmanSpine.lean`.
The two-persistent and all-normal consumers and Fin4 closure are in
`UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualPersistentClosure.lean`,
`UniformEquilibrium/Quitting/Classification/Existence/AllNormalUnboundedExactBlockHazardCapacity.lean`,
and
`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`.

The principal checked declarations are
`HasUnboundedFiniteExactNashBellmanHazardCapacity`,
`nonempty_finiteExactNashBellmanHazardReturn_of_unboundedCapacity`,
`exists_summableResidualNashBellmanSpine_of_unboundedCapacity`,
`QuittingSummableResidualNashBellmanSpine.exists_uniformEquilibriumPayoff_of_twoPersistent`,
`exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity_of_allNormal`,
`finFour_exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity`,
and
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`.

Evidence seals are `M` and `L`, with a capacity-conditional `C`.  There is no
source `A`: no theorem produces unbounded exact-block capacity from an AGKRS
source or a source trace.  The checked result gives no numerical bound in the
bounded branch, no equality with source-trace capacity, no attainment of the
capacity supremum, and no exact stationary-equilibrium conclusion.
