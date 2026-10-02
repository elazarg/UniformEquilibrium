# Audit of `CONSUME.md`, Sections 4--6

## Verdict

The untyped-relation objection is correct, and both abstract
occupation-measure theorems are valid under their stated compactness and
measurability hypotheses.  The positive-charge theorem really does select one
fixed observation target, with quantifiers

\[
  \exists v\;\forall \varepsilon>0\;\forall A>0\;\exists
  \text{ a finite source-matched path}.
\]

There are nevertheless two important qualifications before this becomes a
quitting-game consumer.

1. The proposed space of finite certified chronological blocks has not been
   proved compact (or even closed in the raw actual-profile topology).  The
   cap discontinuity established earlier in the note is one obstruction, and
   unbounded finite block lengths give another.  Thus Theorems 1 and 2 are
   presently conditional abstract results, not an invariant occupation
   theorem for the actual quitting edge system.
2. Prescribed survival zero makes the chronological successor physically
   unreachable, but it does not in general make the off-path suffix irrelevant
   to unrestricted caps.  The suffix may be discarded from the strategic
   certificate only under unilateral screening, for example at a pure
   nonsingleton quitting row.  It should remain stored as counterfactual data
   otherwise.

Subject to those qualifications, the central diagnosis is sound: recurrence
must be applied to typed, composable chronological edges, not to an untyped
union of source operations.

## Sources inspected

- `QuittingPositiveAdmissiblePayoffNearReturnFamily` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`
  in
  `UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`;
- `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`
  in
  `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`;
- `QuittingPunishmentFloorAdmissibleEdge` and
  `quittingPunishmentFloorAdmissibleChargedRelation` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`;
- `QuittingAnchoredBoundaryTransportGraph.closedWalk_edges_eq_nil` in
  `UniformEquilibrium/Quitting/Boundary/Holonomy/TransportGraph.lean`.

## 1. The untyped relation counterexample is exact

For the table

\[
r_i(S)=0\quad(i\in S),\qquad r_i(S)=1\quad(i\notin S),
\]

let \(x\) be a complete profile whose date-zero root is all Quit, and let
\(y=P_{\mathbf C}x\).  Then both prescribed payoffs are zero and Never gives
each deviator payoff one, so every coordinate debt is one at both profiles.
At cap \((1,1,1,1)\), Quit has value zero and Continue has value one against
every opponents' root.  Hence all Continue is the unique exact cap root.

The graphs of prefix and suffix are closed, their union is serial, and

\[
  x\xrightarrow{P_{\mathbf C}}y\xrightarrow{S}x
\]

is a legal zero-charge two-cycle.  The identity replacement is an even more
immediate zero-charge self-loop; deleting it does not give a closed
replacement relation because the diagonal lies in the closure.

This falsifies an inference from the weak condition
"every point has some successor in the set" to productivity of that set.  It
does not show that a maximal strongly connected component under a richer
relation is unproductive, nor does it exclude a theorem that deliberately
chooses a different invariant occupation measure.  The note should keep its
conclusion at the stated level: untyped serial recurrence alone carries no
chronological or charge content.

The observation that the same table has the all-Continue exact equilibrium is
also correct.  It confirms that the example attacks the architecture, not the
uniform-equilibrium conjecture.

## 2. The typed chronological correction is conceptually right

The equality

\[
  \operatorname{profile}(a)=B\star\operatorname{profile}(a')
\]

is the correct source-matching condition for a forward chronological edge
from the current source to its actually reached live continuation.  It makes
successive edges literally composable.  A replacement, compact projection,
reset, or change of minimizer is not such an edge merely because it is a legal
mathematical operation.  A commuting-square or splice theorem is genuinely
needed before it can occur inside one executable chronology.

There are three details to make explicit.

### 2.1 Zero survival versus counterfactual tails

If \(c(B)=0\), no prescribed play reaches the continuation.  Hence the target
of the *physical chronological graph* may correctly be a cemetery state.
However, if one player is solely responsible for sure absorption, that player
can deviate and expose the suffix.  Replacing the suffix itself by a cemetery
payoff would then change the unrestricted cap.

The safe formulation is:

- the on-path successor is cemetery when \(c(B)=0\);
- the literal off-path suffix remains part of the edge's counterfactual
  certificate unless every unilateral replacement is screened from it.

For a pure coalition of cardinality at least two, screening is exact: after
one player changes strategy, another sure quitter remains.  Thus the claimed
nonrealizability of a temporal forced-pair label cycle is correct.  It does
not follow from \(c(B)=0\) alone.

### 2.2 Additivity must be data, not terminology

Calling a number an "admissible charge" does not make it additive under block
concatenation.  The edge type must carry the exact cocycle/decoding theorem
that identifies path charge with the charge accepted by the lasso consumer.
This is present for the checked punishment-floor relation through
`pathToFinitePrefix_charge`; an abstract chronological edge space needs the
corresponding field or a map into that checked relation.

### 2.3 Orientation differs from the checked relation

The note orients a chronological edge current-to-continuation.  The checked
`quittingPunishmentFloorAdmissibleChargedRelation` has source equal to `tail`
and target equal to `current`, because its paths build exact predecessors.
This is not a mathematical obstruction, but an application must reverse each
chronological path (or define the abstract edge orientation to match the
checked relation) before invoking the existing near-return compiler.

## 3. Invariant occupation existence is correct but conditional

Let the edge space be compact metric, let source and target be continuous,
and suppose every state has an internal outgoing edge.  Dependent choice gives
an infinite legal path.  Empirical edge measures have a weakly convergent
subsequence, and for continuous \(f\),

\[
\int(f\circ t-f\circ s)\,d\pi_N
=\frac{f(x_N)-f(x_0)}{N}\longrightarrow0.
\]

The limiting measure is therefore invariant.  No stronger recurrence or
ergodicity assumption is needed.

The main application gap is compactness of the edge space.  "Finite
executable block" allows unbounded lengths, so the union of the fixed-length
block spaces is not automatically compact.  Compactifying the length adds
infinite blocks, which need not be finite executable edges.  Restricting to
one-stage edges avoids that particular problem, but exact cap--Nash
admissibility need not be closed in the raw actual-profile topology because
the unrestricted cap is discontinuous there.  The manuscript itself proves
this discontinuity in Section 3.

Consequently, statement (27) is correct for a component already presented as
a compact serial edge system.  It is not yet proved for the desired space of
actual certified quitting chronologies.

## 4. Positive mean charge gives fixed-target near-returns

Theorem 2 is valid.  Here is the precise standard argument.

Let \(m=s_\#\pi=t_\#\pi\).  Since the spaces are standard Borel,
disintegrate \(\pi\) over \(s\) to obtain a kernel \(K_x\) supported on edges
with source \(x\).  Starting from \(x_0\sim m\), sample
\(e_n\sim K_{x_n}\) and put \(x_{n+1}=t(e_n)\).  Invariance makes this a
stationary probability law on legal edge paths, with one-edge marginal
\(\pi\).

Ergodic decomposition supplies a stationary ergodic component whose mean
charge is positive.  Choose \(v\) in the support of the pushforward of its
state marginal by \(z\).  For every \(k\), the measurable set

\[
V_k=z^{-1}(B(v,1/k))
\]

has positive measure.  On one trajectory belonging to the countable
intersection of the Birkhoff-generic sets for \(q\) and all indicators
\(1_{V_k}\), the cumulative nonnegative charge diverges and every \(V_k\) is
visited infinitely often.  Two sufficiently separated visits to a suitable
\(V_k\) delimit a legal path with charge at least any prescribed \(A\).

This proves the advertised quantifier order with a single \(v\), independent
of both endpoint tolerance and charge target.  Measurability of \(q\) and
\(z\) is enough; continuity is unnecessary for this theorem.  Nonnegativity
and boundedness of \(q\) ensure integrability and the monotone accumulation
used between return visits.

Internal source matching is exact because consecutive sampled edges satisfy
\(t(e_n)=s(e_{n+1})\).  No public randomization is introduced when one finite
sample-path segment is selected.

## 5. Relation to the checked quitting consumer

Taking \(z\) to be the payoff vector already gives more than the checked
cumulative near-return interface requires: endpoints lying within
\(\varepsilon\) of one fixed \(v\) lie within \(2\varepsilon\) of each other,
and one may fix any positive \(A\) as the common charge floor.  The checked
structure permits the endpoints and path to vary with tolerance, and
`quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`
then yields a uniform-equilibrium payoff.

But that application requires every abstract edge path to decode to a path in
the punishment-floor admissible charged relation (up to the orientation noted
above), with the same additive charge.  A literal executable block plus an
informal "all-deviation certificate" is not yet such a bridge.

If the intended conclusion is specifically that the uniform-equilibrium
payoff equals the payoff coordinate of \(v\), an additional bookkeeping lemma
should be stated.  The checked theorem presently concludes existence of a
uniform payoff; it does not name that payoff as the recurrent target.  This is
not needed for existence, but it matters if "fixed-target" is meant as an
identified target rather than merely one target shared by all near-returns.

## Final assessment

Sections 4--6 contain a useful and mostly correct conceptual reduction:

\[
\text{compact serial typed chronological component}
+\text{positive invariant charge}
\Longrightarrow
\text{source-matched cumulative payoff near-returns}.
\]

The remaining work is not in the ergodic argument.  It is to construct a
compact or otherwise recurrence-capable edge system whose points and edges
remain actual, whose exact strategic certificates are closed enough to pass
to limits, and whose edge charge decodes into the checked admissible relation.
The actuality--compactness--cap-continuity trilemma explains why that step is
substantive.
