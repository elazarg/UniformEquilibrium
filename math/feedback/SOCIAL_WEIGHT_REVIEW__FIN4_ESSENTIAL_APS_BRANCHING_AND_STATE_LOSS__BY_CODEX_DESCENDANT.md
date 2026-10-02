# Review of Fin4 essential-APS branching and state loss

## Final packet delta

Verdict: **PASS** for the frozen candidate
`/tmp/FIN4_ESSENTIAL_APS_SUMMABLE_THIRD_MODE_AND_COLLISION_EXPRESSIVENESS_NO_GO.md`
at SHA-256
`abf85b5ab35235dd9ecd243a87b84592e4bb79e8caa621b88d795e089f651854`.

The change from the previously reviewed mathematical text is mechanical:
balanced inline-math delimiters were restored without changing the claims,
formulas, proof, scope, or source correspondence.  I independently confirmed
39/39 display delimiters, 84/84 inline delimiters, no control-byte matches,
and resolution of both final-location review links.  No export blocker
remains for these exact bytes.

Reviewer: `CODEX_DESCENDANT`

Date: 2026-09-01

Verdict: **REVISE.**  Propositions 2.1, 2.2, and 3.1 are correct, and the
two-level rational regression and homogeneous balance compute exactly as
stated.  The proposed capstone is not exhaustive for an arbitrary
"nonempty Fin4 algebraic APS family."  It becomes a credible target only
after restricting to the greatest family inside coordinatewise convex
carriers.  Even under that restriction, the shrinking-positive-mass
ballistic boundary is still an unconsumed third output unless a further
theorem turns it into the homogeneous certificate.

## Local purification

If owner $i$ has two distinct Flesch successors, two of the three nonowner
coordinates of $R_i$ are strictly above baseline.  Hence at most one
coordinate is bad.  In a positive finite convex representation, activity at
$i$ forces every positively weighted continuation to be active at $i$.
Selecting a continuation whose value at the sole bad coordinate is at least
the average preserves viability at that coordinate; every other coordinate
is automatically viable.  Proposition 2.2 is therefore correct.

The conclusion is exactly set-level: the purified point generally differs
from the supplied current point.  It cannot be inserted behind an already
fixed predecessor segment.

## Oriented graph classification

Strong connectivity forces positive indegree and outdegree.  An oriented
four-vertex graph has at most six edges.  With four, five, or six edges the
sorted outdegrees are respectively

\[
(1,1,1,1),\qquad(1,1,1,2),\qquad(1,1,2,2).
\]

In the six-edge tournament case an outdegree-three vertex would have
indegree zero, so it is excluded.  The three-vertex case is the directed
cycle.  Proposition 3.1 is correct for a strongly connected live graph.
Transient vertices outside the eventual SCC can have three successors; that
does not change the SCC classification, but it should not be described as a
classification of every owner in the full Flesch graph.

## Rational regression and homogeneous branch

The six claimed edges follow from (4.1), and the two displayed half-mass
calculations are exact.  Purifying owner $1$ toward $u_2$ violates
coordinate $0$; purifying toward $u_3$ preserves the owner-$1$ step but
makes the preceding owner-$0$ step negative at coordinate $3$.  This is a
valid regression against independent levelwise purification.

The balance also checks coordinatewise:

\[
R_0+R_1+2R_2+2R_3=0.
\]

After normalization the weights are strictly positive and nonvertex, so the
normalized singleton residual is identically zero.  The checked nonvertex
homogeneous-witness theorem therefore supplies the stationary uniform-payoff
consumer.  The example is not a counterexample to the desired capstone.

## Missing hypothesis: one-successor nonconvex state loss

The project definitions explicitly allow nonconvex continuation sets in a
general `QuittingEssentialAPSPacket`.  With only one successor, an owner may
have two bad coordinates, and convexification inside that one fiber can be
essential.

For an exact local regression take baseline zero,

\[
R_0=(0,1,-1,-1),
\]

and let owner $0$'s only live successor fiber contain

\[
w^2=(0,0,2,0),\qquad w^3=(0,0,0,2),
\]

but not their midpoint.  With $p=1/2$,

\[
{1\over2}R_0+{1\over2}{w^2+w^3\over2}
=(0,1/2,0,0)
\]

is viable and active.  Neither one-continuation segment is viable: the
$w^2$ segment is negative at coordinate $3$, and the $w^3$ segment is
negative at coordinate $2$.  There is no branching owner at all.

This mode is excluded for
`quittingEssentialAPSGreatestFamily reward carrier` when every supplied
carrier fiber is convex, because
`convex_quittingEssentialAPSGreatestFamily` makes the one live successor
fiber convex and
`quittingEssentialAPSPrefix_eq_segment_of_convex` then preserves the exact
current point.  Those hypotheses must be part of the capstone statement;
they are not consequences of an arbitrary algebraic APS packet.

## Remaining third output under convex greatest-family hypotheses

After the convex-fiber repair, the branching/state-compatibility problem is
indeed localized to at most two vertices of a recurrent Fin4 SCC.  However,
the note itself identifies positive masses tending to zero with summable
total mass.  Such a path need not be an absorbing singleton path, and the
present propositions do not produce a homogeneous stationary witness from
it.  Existing normalized ballistic arguments generally leave a boundary or
common-active-face alternative in addition to the homogeneous zero.

Therefore the honest current target is at least a trichotomy:

\[
\begin{array}{c}
\text{executable path with divergent total absorption},\\
\text{homogeneous stationary certificate},\\
\text{or a summable-mass boundary/common-face state-loss certificate}.
\end{array}
\]

Eliminating the third line may well be the desired Fin4 theorem, but it is
not a consequence of Propositions 2.2 and 3.1 and should not be omitted from
the statement before that proof is supplied.

## Net assessment

The note contains useful new local mathematics: Fin4 branching creates at
most one viability constraint per branching owner, and a recurrent oriented
component has at most two such owners.  Its regression correctly proves that
local purification cannot be iterated greedily.  The proposed two-output
capstone is a research target, not yet an exhaustive reduction; it needs the
convex greatest-family/compact-carrier setting and a separate elimination of
the summable boundary mode.

## Delta review of Sections 7--8

Verdict: **PASS.**  Sections 7 and 8 incorporate the preceding objections and
give exact regressions for the surviving third mode and for the smallest
missing game-semantic datum.

### Greatest-family equality and forced path

The three displayed arc identities are coordinatewise exact.  The parameter
maps send

\[
[0,1/2]\longrightarrow[0,1/3]\longrightarrow[0,1/5]
\longrightarrow[0,1/9]\subset[0,1/2].
\]

Hence the compact convex carrier (K) is subinvariant.  The greatest
carrier-restricted family contains every subinvariant subset and is itself
contained in (K), so it equals (K).  Each nonempty fiber has exactly the
one graph successor; convexity identifies the full prefix with the segment
prefix.  The active-owner coordinate and the unique negative cross coordinate
then force the displayed mass and successor.  At the common zero coordinate
they force zero mass and the zero successor as stated.

One circuit is indeed

\[
T(x)=\frac{x}{8-7x},
\qquad 0\le T(x)\le\frac29x.
\]

The per-circuit mass bounds

\[
p_0=x/2,
\qquad p_1\le x/3,
\qquad p_2\le x/5
\]

are correct, so the total positive mass is summable and the survival product
is strictly positive.  This is a genuine third output even in the compact
convex greatest family, not the nonconvex local failure from the first review.

### Homogeneous and Never-residual calculations

The three nontrivial coordinates of
(sum_i\lambda_i(R_i-s)=0) give exactly the displayed system.  Substitution
reduces it to (7\lambda_0+7\lambda_3=0), and nonnegativity kills every
coefficient.  The unnormalized nonnegative rows likewise admit no nonzero
nonnegative zero balance.

The finite telescope and its limit are exact:

\[
v_0=\sum_nS_np_nR_{i_n}+S_\infty s.
\]

The literal quitting profile pays zero on Never, so its terminal reward
moment omits the last term.  Thus (v_0-U=S_\infty s\ne0).  The note also
states the unrestricted-deviation scope correctly: since every own singleton
payoff is one and the remaining conditional absorption tends to zero, late
suffix exploitability does not vanish.  The completed game has an immediate
all-Quit equilibrium and is not claimed as a counterexample.

### Same-singleton completion comparison

The additive completion in Section 8 is consistent for every coalition and
preserves all four singleton outcome vectors.  For a product root (q) at cap
(s), pure Quit minus pure Continue is exactly

\[
H_i(q)=\sum_{j\ne i}L_{ij}q_j.
\]

The exact root inequalities imply (q_iH_i(q)\ge0).  Since every unordered
pair has (L_{ij}+L_{ji}=-1),

\[
\sum_iq_iH_i(q)=-\sum_{i<j}q_iq_j.
\]

Two positive coordinates are therefore impossible.  With exactly one
positive coordinate (q_j), the explicitly displayed column (j) has a
positive off-diagonal entry, so a pure-Continue player has a profitable Quit
deviation.  Hence (q=0), and at (q=0) all endpoint differences vanish.
All Continue is the unique exact product root.  By contrast, in the constant
nonsingleton completion all Quit is exact at the same cap.

The two completions have identical singleton rewards, Flesch graph, carrier,
greatest APS family, forced Möbius path, and common active-face limit.  The
comparison therefore correctly proves that singleton APS data alone cannot
choose a collision-root consumer.  Pair insertion toggles are already enough
to reverse the exact root conclusion; the full endpoint polynomial is the
general missing semantic field.

No new objection remains to Sections 7--8.  They falsify only the abstract
APS two-output capstone and do not purport to decide the quitting-game
conjecture.
