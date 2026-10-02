# Endpoint closure preserves a passport but cannot supply a rank

Author: FORCED_PAIR_REVIEW

## Status

The off-minimum normalized-passport minimizer can be enlarged so that every
literal same-stage pure-coalition endpoint sibling and every subsequent
finite literal prefix remains in one compact decorated class.  A nonzero
normalized **historical** mass/gain passport survives this enlargement.

This does not produce a minimization contradiction.  The active fixed-payer
passport is necessarily destroyed by the first best-endpoint update: the
updated payer's local defect is exactly zero.  If the state is enlarged again
to select the next payer, the hard-residual full-gap toggle theorem produces a
literal closed same-stage cycle.  Therefore no natural-valued or
lexicographic rank determined by these endpoint data can strictly decrease at
every update.

The maximal formal conclusion of endpoint closure is a source-matched debt
transfer at a minimum-debt corner of the marked cube.  Consuming that transfer
still requires non-horizontal chronology or no-new-support control.

This is an architectural no-go for the proposed endpoint-enlargement
strategy, not a counterexample to the quitting-game conjecture.

## 1. Enlarge the decorated state to the complete marked cube

Start at an off-minimum normalized-passport point from
`FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY.md`.
Its raw actualizers have a marked pure pair at one literal date, a fixed
minimum post-date tail, and a positive live mass.  For one such raw actualizer
$X$ at date $t$, write

\[
 \ell=\Pr_X(\text{reach the live history at }t).
\]

For every nonempty coalition $A\subseteq\operatorname{Fin}4$, let $X_A$
be the literal sibling obtained by overwriting only the marked root with the
pure coalition $A$.  Store simultaneously:

* the joint semantic/law point of every $X_A$;
* the common post-date joint semantic/law tail;
* the common marked live mass $\ell$;
* the original source/minimum provenance; and
* the current distinguished coalition $A$.

There are only fifteen semantic/law corner coordinates.  Closing all these
finite tuples under every common finite product-root prefix and then taking
closure gives a compact decorated carrier.  If a common prefix word has
survival $c$, then every corner point is prefixed by the same affine
semantic/law action, while

\[
 \ell\longmapsto c\ell.
\tag{1}
\]

Changing the distinguished coalition is a finite-coordinate permutation.
Thus the enlarged carrier is closed under both common literal prefixing and
same-stage pure-coalition replacement.

This construction is finite-dimensional.  It does not store a stopping law
or identify different corner profiles with one executable chronology.

## 2. A normalized historical passport survives

Let $\gamma>0$ be the terminal exploitability gap in the hard residual and
let $D^{\max}$ be a uniform upper bound for total terminal semantic debt.
The checked full-gap toggle theorem gives, at every nonempty pure coalition
$A$, a player $i(A)$ and a nonempty toggle

\[
 F(A)=A\mathbin\triangle\{i(A)}
\]

such that

\[
 r_{i(A)}(F(A))-r_{i(A)}(A)\ge\gamma.
\tag{2}
\]

For nonsingletons this is the unrestricted pure-set exploitability identity.
For singletons it is the hard residual's punishment-normal full-gap collision
theorem, which selects a join and avoids the empty coalition.

At the actual marked date, (2) gives the exact whole-profile gain

\[
 G_A
 :=U_{i(A)}(X_{F(A)})-U_{i(A)}(X_A)
 =\ell\bigl(r_{i(A)}(F(A))-r_{i(A)}(A)\bigr)
 \ge\ell\gamma.
\tag{3}

Every sibling keeps stage mass exactly $\ell$.  If the initial normalized
passport gives $\ell\ge\theta D_*>0$, then for every corner

\[
 \frac{\ell}{D(X_A)}
 \ge\frac{\theta D_*}{D^{\max}},
 \qquad
 \frac{G_A}{D(X_A)}
 \ge\frac{\theta\gamma D_*}{D^{\max}}.
\tag{4}

Hence endpoint replacement need not destroy all quantitative information.
After one universal normalization by $D^{\max}$, the whole finite marked
cube has fixed positive mass/debt and selected-gain/debt floors.

If $q$ is exact cap--Nash at the currently distinguished corner and has
survival $c$, exact prefixing scales its whole debt, $\ell$, and $G_A$
all by $c$.  Thus the two ratios in (4) are then preserved exactly.

So failure of endpoint closure is **not** caused by vanishing mass or gain.

## 3. What necessarily fails: the fixed active payer

Let $B=F(A)$, and let $i=i(A)$.  The update from $X_A$ to $X_B$
changes only player $i$'s prescribed strategy.  Its opponents and therefore
its unrestricted behavioral cap are unchanged.  Consequently

\[
 d_i(X_B)=d_i(X_A)-G_A.
\tag{5}

At the marked root of $X_B$, player $i$ is now playing its selected best
Boolean endpoint.  Therefore its new local root defect is exactly zero:

\[
 \delta_i(\operatorname{tail},\operatorname{root}(X_B))=0.
\tag{6}

Thus a class requiring the same fixed payer to carry a positive current
marked defect is not endpoint-invariant.  This is an exact failure, not a
loss in a limiting estimate.

One can retain $G_A$ as a historical annotation, or select a new payer
$i(B)$.  Historical gain is prefix-transportable but no longer represents a
currently executable improving edge.  Selecting a new payer preserves an
active edge but changes the finite labels.

## 4. Reselecting payers produces a literal horizontal cycle

Choose one full-gap outgoing toggle $F(A)$ at every nonempty coalition and
iterate it.  Since the nonempty Fin4 cube has fifteen vertices, some vertex
repeats.  Removing the transient part gives a simple cycle

\[
 A_0\to A_1\to\cdots\to A_K=A_0,
\tag{7}

with every edge realized on the same actual marked row, the same past, the
same post-date tail, the same live mass $\ell$, and gain at least
$\ell\gamma$.

This is the reviewed theorem in
`ATLAS_FALSIFIER__CONCENTRATED_SINGLETON_FULL_GAP_TOGGLE_CYCLE.md`.  Its
all-behavior ingredients are checked by:

* `QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain` and
  `.not_isQuittingSureExitSet` for nonsingletons;
* `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  for singleton joins; and
* the literal one-date payoff and own-debt identities in
  `Research/Quitting/SameStageEndpointMonodromy.lean`.

The newer impossibility of a `QuittingSameStageEndpointEdge` monodromy does
not contradict (7).  That stronger edge type includes near-minimum transfer
fields.  The full-gap toggle cycle stores only pure-coalition payoff gains and
exact own-debt subtraction; it may pass through singleton vertices and total
debt may rise through cross-coordinate cap externalities.

Because (7) returns to the identical behavioral profile, no function of the
stored finite endpoint data can strictly decrease at every selected update.
In particular:

* no natural-valued rank can decrease on all edges;
* no lexicographically ordered finite tuple can decrease on all edges; and
* retaining the whole visited path as state only turns one circuit into a
  fixed point after one lap.

This is a formal obstruction to every rank proof whose transition is exactly
"take another profitable same-stage endpoint".

## 5. The exact output of debt minimization on the cube

The complete marked cube is finite at every raw source, and its decorated
closure is compact.  Minimize total whole debt over all its corners and
prefix descendants, subject to the fixed historical density floors.  The
same normalized-passport argument makes every exact cap root at a minimizer
all Continue.

If this enlarged minimum equals $D_*$, raw actualizers again give a
whole-source-return concentrated collision packet and the checked three-role
compiler applies.  Thus only the strictly off-minimum cube minimum remains in
this section.

Let $A$ be its distinguished minimum-debt corner and choose the full-gap
edge $A\to B$ with mover $i$.  Because $B$ is another admissible corner,

\[
 D(X_B)\ge D(X_A).
\tag{8}

Combining (5) and (8) gives the exact cross-coordinate transfer

\[
 \sum_{j\ne i}\bigl(d_j(X_B)-d_j(X_A)\bigr)
 \ge G_A
 \ge\ell\gamma.
\tag{9}

This is the strongest unconditional consequence of adding the endpoint
operation to the compact minimization class.  It is a fixed positive,
source-matched transfer on a common row and common tail.

Equation (9) does not say that the receiving debt belonged to an already
active coordinate, that the target stays on the minimum fibre, or that the
transfer is a prescribed-payoff Bellman edge.  The cycle (7) shows that such
transfers can replenish one another indefinitely around the horizontal cube.

## 6. Verdict

There are exactly two endpoint-closed passport choices.

1. **Current fixed-payer passport.**  It is not invariant: its positive
   defect becomes zero by (6) after the first best-endpoint update.
2. **Historical or reselected-payer passport.**  It retains fixed normalized
   mass and gain scales, but its update graph contains the exact literal cycle
   (7), so it has no decreasing finite or lexicographic rank.

Therefore enlarging the off-minimum inert class under same-stage endpoint
updates cannot by itself contradict compact minimality.  The operation does
produce the positive transfer (9), so the next genuinely different input
must control one of:

\[
 \text{no new debt support},
 \qquad
 \text{minimum-fibre return},
 \qquad
 \text{or chronological expenditure of the horizontal transfer}.
\]

Without one of those inputs, endpoint closure is quantitatively stable but
not well-founded.
