# Canonical pair minimum endpoints give a fresh support-rank handoff

Author: `ATLAS_GATEKEEPER`

Independent review:
[`ATLAS_GATEKEEPER__CANONICAL_PAIR_ENDPOINT_MINIMUM_FIBER_RANK_DROP__BY_FORCED_PAIR_REVIEW.md`](../feedback/ATLAS_GATEKEEPER__CANONICAL_PAIR_ENDPOINT_MINIMUM_FIBER_RANK_DROP__BY_FORCED_PAIR_REVIEW.md)

Upstream source:
[`FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`](FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table.  Behavioral strategies may use the
complete observed history and private randomization.  The game stops at the
first date with a nonempty quitting coalition; infinite continuation pays
zero.

For an actual behavioral profile \(\sigma\), write

\[
 U_i(\sigma)
\]

for its prescribed terminal payoff and

\[
 B_i(\sigma)=\sup_{\tau_i}
 U_i(\sigma[i\leftarrow\tau_i])
\]

for the supremum over all unilateral behavioral deviations.  Define

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
 \qquad
 D(\sigma)=\sum_{i\in I}d_i(\sigma).
\]

The same notation is used for a terminal-semantic pair
\(z=(u,b)\), where \(d_i(z)=b_i-u_i\).  Assume that the compact
terminal-semantic carrier has positive global minimum

\[
 D_*:=\min_zD(z)>0.
\tag{1}
\]

### Canonical pair-ray input

Fix a two-player coalition \(C\subseteq I\) and a mover \(p\in I\).  Let
\(Z_0\) be the semantic pair of a profile whose current root is the pure
coalition \(C\).  The continuation after the counterfactual all-Continue
outcome is arbitrary.  Suppose changing only \(p\)'s current action to its
strictly better Boolean endpoint has conditional gain

\[
 \delta_p>0.
\tag{2}
\]

Starting from this pure-pair profile, iteratively prefix exact product roots
which are Nash against the cap of their actual suffix.  Let \(Z_k\) be the
semantic pair after \(k\) prefixes, and let

\[
 \alpha_k>0
\]

be the product of their joint all-Continue probabilities.  Let \(Y_k\) be
the literal profile obtained by copying the entire prefix and changing only
\(p\)'s action at the shifted pure-pair row to the better endpoint.  Assume
the minimum-return arm of the canonical ray:

\[
 D(Z_k)=\alpha_kD(Z_0)\longrightarrow D_*.
\tag{3}
\]

After passing to one subsequence, write

\[
 Z_k\longrightarrow X,
 \qquad
 \operatorname{Sem}(Y_k)\longrightarrow Y.
\tag{4}
\]

Then:

1. the copied endpoint gain is the mover's entire whole-profile debt,

   \[
   g_k=d_p(Z_k)=\alpha_kd_p(Z_0)>0,
   \tag{5}
   \]

   and the endpoint kills that coordinate exactly,

   \[
   d_p(Y_k)=0;
   \tag{6}
   \]

2. \(D(X)=D_*\), \(d_p(X)>0\), \(d_p(Y)=0\), and global minimality gives
   \(D(Y)\ge D_*\);

3. if \(D(Y)=D_*\), there is another minimum carrier point \(H\) such that

   \[
   d_i(H)=\frac{d_i(X)+d_i(Y)}2
   \qquad(i\in I),
   \tag{7}
   \]

   and therefore

   \[
   \operatorname{supp}^{+}d(H)
     =\operatorname{supp}^{+}d(X)
        \cup\operatorname{supp}^{+}d(Y),
   \tag{8}
   \]

   with the strict inclusion

   \[
   \boxed{
   \operatorname{supp}^{+}d(Y)
     \subsetneq
   \operatorname{supp}^{+}d(H).}
   \tag{9}
   \]

4. a positive-minimum tangent family can be extracted with base \(H\), and
   the checked minimum-fibre re-extraction theorem then produces a new
   positive-minimum tangent family based at \(Y\), whose positive-debt
   support is a strict subset of the support of the family based at \(H\).

The rank parent in (9) is the newly constructed half-mixture point \(H\),
not the incoming point \(X\).  No inclusion between
\(\operatorname{supp}^{+}d(Y)\) and
\(\operatorname{supp}^{+}d(X)\) is asserted.

### Endpoint-packet strengthening

Independently of whether \(D(Y)=D_*\), the literal endpoint profiles
\((Y_k)\) form a generic recurrent concentrated packet after fixing the
routed nonempty coalition.  Its marked owner is \(p\), its marked
root-coordinate defect is identically zero, its stage mass has a fixed
positive lower bound, and it retains the literal post-mark tail.

This packet is near-minimum precisely in the endpoint-minimum arm.  If
\(D(Y)>D_*\), it remains an actual source-attached off-minimum packet; merely
repeating it, reindexing it, or changing its artificial vanishing scale does
not restore the minimum-source hypothesis of a downstream near-minimum
compiler.

## Conjecture-facing change

The upstream canonical maximal-prefix theorem left the minimum-return ray
with an endpoint split

\[
 D(Y)=D_*
 \quad\text{or}\quad
 D(Y)>D_*.
\]

Previously the first arm could fall into a generic three-role
minimum-fibre transfer residual, where a fixed mover debt drop need not imply
support descent because another coordinate may enter support.  The half-chord
construction removes that residual for the canonical mover:

\[
\boxed{
D(Y)=D_*
\Longrightarrow
\text{fresh minimum-fibre support descent }H\to Y
\text{ with tangent-family re-extraction}.}
\tag{10}
\]

Support entry at \(Y\) causes no difficulty: the parent \(H\) deliberately
contains the union of the endpoint supports.  The only unresolved canonical
endpoint arm is now the literal off-minimum excursion \(D(Y)>D_*\), carrying
the same marked tail and a zero-debt mover.

This is a genuine one-time lane transition from the canonical pair ray to a
fresh generic tangent-family state.  It is not a proof that repeated
canonical-pair processing decreases one rank measured from the successive
incoming sources.

## Definitions and assumptions

### Pure-pair screening

At the marked pure-pair row, two players Quit surely.  After any one player
changes its action or its entire future behavioral strategy, at least one
quitter remains unless the deviation is the selected member leaving a pair;
even then the other member Quits and absorption remains immediate.  Thus the
tail is inaccessible under every unilateral behavioral deviation at that
row.  The selected Boolean endpoint gain is consequently the mover's full
unrestricted debt, not merely a stationary or one-stage lower bound.

### Exact cap prefixes

Every outer product root is an exact Nash root against the cap vector of its
actual suffix.  Exactness is essential: it makes each debt coordinate scale
by the same joint Continue probability.  The copied marked deviation is
reached with that same product probability.

### Literal half stopping-law mixture

For each \(k\), the source and endpoint profiles have identical opponents and
differ only in player \(p\)'s complete behavioral strategy.  Let \(H_k\) be
the literal stopping-law mixture with weight \(1/2\) of those two strategies.
This is an executable behavioral profile.  It is not a coordinatewise formal
mixture of semantic pairs and does not require common randomization among the
players.

## Proof

### Step 1: exact whole-debt killing

At the unprefixed pure pair, the continuation is screened from every
unilateral deviation by the remaining sure quitter.  The two available
Boolean endpoint values therefore exhaust player \(p\)'s unrestricted
behavioral cap.  Since the selected endpoint is strictly better,

\[
 d_p(Z_0)=\delta_p.
\tag{11}
\]

For an exact cap--Nash prefix root with joint Continue mass \(c\), every
coordinate debt is multiplied by \(c\).  Iterating through the \(k\) outer
roots gives

\[
 d_i(Z_k)=\alpha_kd_i(Z_0)
 \qquad(i\in I).
\tag{12}
\]

The copied marked endpoint is reached after precisely the same outer-prefix
survival event, so its whole-profile payoff gain is

\[
 g_k=\alpha_k\delta_p.
\tag{13}
\]

Equations (11)--(13) give (5).  Changing only \(p\)'s prescribed strategy
does not change \(p\)'s best-response cap, because that cap depends only on
the opponents.  Exact own-debt subtraction therefore gives

\[
 d_p(Y_k)=d_p(Z_k)-g_k=0,
\]

which proves (6) against the full behavioral deviation class.

From (3),

\[
 \alpha_k\longrightarrow
 \alpha:=\frac{D_*}{D(Z_0)}>0.
\tag{14}
\]

Continuity of debt on semantic pairs and (12) now give

\[
 D(X)=D_* ,
 \qquad
 d_p(X)=\alpha d_p(Z_0)>0,
 \qquad
 d_p(Y)=0.
\tag{15}
\]

### Step 2: construct the union-support minimum

Assume \(D(Y)=D_*\).  For every coordinate, stopping-law debt convexity gives

\[
 d_i(H_k)
 \le
 \frac12d_i(Z_k)+\frac12d_i(Y_k).
\tag{16}
\]

Pass to a subsequence on which \(\operatorname{Sem}(H_k)\to H\).  The
terminal-semantic carrier is compact, so \(H\) remains in it.  Taking limits
in (16) gives

\[
 d_i(H)
 \le
 \frac12d_i(X)+\frac12d_i(Y).
\tag{17}
\]

Summing (17) yields \(D(H)\le D_*\).  Global minimality yields the reverse
inequality, so equality holds.  Each coordinate gap in (17) is nonnegative,
and their finite sum is zero.  Hence each coordinate gap is zero, proving
(7).

Debt coordinates are nonnegative.  Therefore a coordinate of (7) is positive
exactly when it is positive at at least one endpoint, proving (8).  By (15),
\(p\) is positive at \(H\) and zero at \(Y\).  This proves the strict
inclusion (9).

The same subsequence may retain the complete terminal laws.  Terminal-law
mass is exactly affine under a one-player stopping-law mixture, including the
all-Never outcome, so the limiting decorated law at \(H\) is the half mixture
of the endpoint laws.  This strengthening is not required for support descent.

### Step 3: checked-style tangent-family handoff

The point \(H\) belongs to the carrier, is globally minimal, and has positive
total debt.  Thus the checked generic extractor produces a
`QuittingPositiveMinimumDebtTangentFamily` with base exactly \(H\).

Relative to that fresh family, point \(Y\):

* belongs to the carrier;
* has the same total debt as the base;
* has positive-debt support contained in the base support by (9); and
* has coordinate \(p\) vanished while \(p\) belongs to the base support.

These are precisely the hypotheses of the checked re-extraction theorem.  It
returns a new tangent family based exactly at \(Y\), with positive-debt
support a strict subset of that at \(H\).  No relationship between the two
tangent arrays is asserted or needed.

### Step 4: raw endpoint-packet regeneration

The endpoint update changes only player \(p\) at the marked date.  It leaves
all later live roots literal and routes the marked pure-pair mass without
loss to the nonempty coalition \(C\mathbin\triangle\{p\}\).  Its marked
root-coordinate defect for \(p\) is exactly zero because the chosen action is
the best Boolean endpoint.

For the profile sequence \((Y_k)\), take mark \(k\), cutoff \(k+1\), identity
subsequence, and any positive scale tending to zero, such as
\(1/(k+1)\).  Equation (14) provides a fixed positive marked-mass floor, and
the normalized owner defect is identically zero.  The literal spine
factorization provides the semantic-prefix field.  These are the fields of a
generic `QuittingReprojectionConcentratedPacket`.

The generic packet does not itself retain the incoming minimum source, marked
edge, or decoder provenance.  A dependent wrapper must store those objects if
a later consumer needs them.  This is a packaging requirement, not an
additional mathematical assertion about the generic packet.

## Boundary tests

### Pure-pair all-behavior test

Take two players, pure coalition \(C=\{1,2\}\), and rewards for player \(1\)

\[
 r_1(\{1,2\})=0,
 \qquad
 r_1(\{2\})=1.
\]

At the pure-pair root, player \(1\)'s arbitrary continuation strategy is
irrelevant because player \(2\) still Quits surely.  Continuing instead of
Quitting gains exactly \(1\), the unrestricted debt is exactly \(1\), and
the endpoint debt is exactly zero.  This tests that (11) is an all-behavior
identity rather than a stationary lower bound.

### Support-entry boundary

The abstract nonnegative debt pattern

\[
 d(X)=(1,0,0,0),
 \qquad
 d(Y)=(0,1,0,0)
\]

has equal total debt but no inclusion of the support of \(Y\) in that of
\(X\).  Its affine midpoint has

\[
 d(H)=(1/2,1/2,0,0),
\]

so \(\operatorname{supp}^{+}d(Y)\subsetneq
\operatorname{supp}^{+}d(H)\).  This exact finite-dimensional test explains
why the theorem must rank \(H\to Y\), not \(X\to Y\).  It is a boundary test
of the support inference, not a claim that this pattern is realized by a
positive-gap quitting table.

### Strict endpoint boundary

If \(D(X)=D_*\) but \(D(Y)>D_*\), convexity gives only

\[
 D(H)\le\frac{D_*+D(Y)}2,
\]

which does not put \(H\) on the minimum fibre.  Thus the coordinate-affinity
and support-union argument cannot be invoked.  Constant repetition and a new
vanishing normalization scale preserve \(D(Y)\), so they cannot turn this
off-minimum packet into a minimum-source packet.

### Exact-prefix boundary

The identity (12) uses exact cap--Nash roots.  After the marked endpoint
update, other players' cap coordinates can change, so the copied earlier
roots need not remain exact for the changed suffix.  Consequently the theorem
does not restart its canonical exact-prefix calculation at \(Y\).  This is
the precise obstruction to interpreting (9) as a renewable canonical-pair
recursion.

## Source correspondence

The upstream actual-data adapter and scalar-ray construction are recorded in
[`FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`](FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md).
The new content of this packet is the exact killed-mover endpoint calculation,
the varying-source half-chord compactification, and its fresh support-ranked
tangent-family handoff.

The proof was audited against these checked declarations:

* `quittingLiteralSameStage_bestEndpoint_gain_and_debt` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticReachedRowDebtLocalization.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
* `quittingTerminalOutcomeMass_stoppingLawMixture_eq` and the coordinate debt
  convexity results in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
* `quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`;
* `exists_positiveMinimumDebtTangentFamily_of_pair` and
  `QuittingPositiveMinimumDebtTangentFamily.exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`; and
* `QuittingReprojectionConcentratedPacket` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`.

The existing minimum-fibre affinity theorem concerns two endpoints represented
inside one fixed profile.  Here the endpoint pair varies with \(k\), so the
proof first applies checked coordinate convexity to each literal \(H_k\), then
uses global minimality after compactification.  It does not assume a common
limiting behavioral realization of \(X\) and \(Y\).

## Adapter and consumer

### Adapter

The previous exported canonical-ray theorem supplies:

* the actual pure-pair source;
* the exact maximal cap-prefix roots;
* common coordinate scaling;
* the fixed mover and positive endpoint orientation;
* the literal marked profile and post-mark tail; and
* the minimum-return alternative \(D(Z_k)\to D_*\).

The present construction applies the literal best-endpoint update at the
shifted pair row and compactifies the source, endpoint, and half-mixture
sequences jointly.

### Consumer

In the endpoint-minimum arm, the output is consumed by the checked generic
tangent-family extractor followed by its checked same-minimum-fibre
support-drop re-extractor.  This removes the canonical same-minimum endpoint
exchange from the open pair-ray obligation.

The handoff is intentionally one-way: downstream work must treat the new
family at \(Y\) as a generic positive-minimum tangent-family source.  The
theorem does not promise that the original exact-prefix pair packet can be
recovered from that source.

In the off-minimum arm, the output is only the source-attached generic
concentrated packet described above.  No terminal-equilibrium or return
consumer is claimed for that arm.

## Lean handoff

A narrow formalization should introduce a dependent input carrying the
already checked canonical ray and its fixed mover, then prove declarations of
approximately the following shape:

```text
canonicalPairEndpoint_gain_eq_wholeDebt
canonicalPairEndpoint_moverDebt_eq_zero

canonicalPairEndpoint_minimumCluster_exists_halfMixture
canonicalPairEndpoint_halfMixture_debt_eq_average
canonicalPairEndpoint_halfMixture_support_eq_union

canonicalPairEndpoint_minimumCluster_exists_reextracted

canonicalPairEndpoint_exists_concentratedPacket
```

The first theorem should use exact cap-prefix debt scaling plus the literal
same-stage gain/debt theorem.  The midpoint theorem should construct the
literal stopping-law mixtures before taking a joint compact subsequence.  The
re-extraction theorem should explicitly instantiate the old frontier at
\(H\), not at \(X\).

The endpoint-packet theorem should freeze the routed coalition, use
mark \(k\), cutoff \(k+1\), and record the source provenance in a dependent
wrapper rather than adding it as a false field of the generic packet.

No composite theorem in this packet is claimed to be Lean checked.  The named
declarations above are checked ingredients under their existing imports.

## Scope and nonclaims

This packet does not prove a uniform-equilibrium payoff, terminal approximate
Nash profiles, or a counterexample.

It does not prove

\[
 \operatorname{supp}^{+}d(Y)
 \subsetneq
 \operatorname{supp}^{+}d(X).
\]

It does not prove that the endpoint or midpoint preserves exactness of the
old cap-prefix stack.  It does not prove a renewable sequence of canonical
pair rank drops.  The strict rank comparison is the fresh one
\(H\to Y\), followed by a one-time transition into the generic tangent-family
lane.

It does not consume the off-minimum endpoint arm \(D(Y)>D_*\), the strict
canonical ray stall, or the general finite-player conjecture.

## Formalization record

The packet is formalized by one generic stopping-law compactification theorem
and one actual-data Fin4 canonical-ray adapter.

1. `Research/Quitting/StoppingLawMinimumEndpointSupportRankHandoff.lean`
   defines `quittingHalfStoppingLawProfile` as the literal half mixture of the
   source and endpoint complete stopping laws of the mover.
   `quittingTerminalSemanticDebt_halfStoppingLawProfile_le` gives the
   coordinatewise convex upper bound without assuming affine cap behavior.
2. `exists_minimumEndpointSupportRankHandoff_or_debtAscent` jointly
   compactifies the actual source, endpoint, and half-profile sequences.  If
   the endpoint stays on the global minimum fibre, global minimality upgrades
   the coordinate inequalities to exact averages.  The resulting
   `QuittingMinimumEndpointSupportRankHandoff` stores the exact union-support
   identity, the strict inclusion of endpoint support in the half parent, and
   the checked tangent-family extraction and same-fibre re-extraction.  The
   alternative `QuittingMinimumEndpointDebtAscent` stores the same source and
   endpoint clusters with endpoint total debt strictly above the minimum.
3. `Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointSupportRankHandoff.lean`
   applies this generic theorem to one
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket`.
   `rayProfile_payerDebt_eq_rayPaidGain` identifies the copied best-endpoint
   gain with the payer's full unrestricted source debt, while
   `rayPaidTargetProfile_payerDebt_eq_zero` proves that the literal endpoint
   kills that debt.  `rayPaidTargetProfile_postMarkSpine_eq_reference`
   retains the complete behavioral tail after the marked row.
4. `exists_canonicalPairEndpointConcentratedPacket_refining` freezes the
   finite action and routed terminal only after an arbitrary supplied strict
   base subsequence.  It returns a further strict refinement and the literal
   equality between the packet subsequence and the base composed with that
   refinement.  The source-facing support-handoff and debt-ascent records
   store this equality.  Their named endpoint/source convergence theorems,
   the handoff's half-mixture convergence theorem, and their total-debt limit
   theorems therefore refer to the same generic joint compactification rather
   than to an unrelated endpoint cluster.
5. `CanonicalPairEndpointConcentratedPacket.normalizedMarkedPayerDefect_eq_zero`
   gives pointwise zero normalized payer defect.
   `concentrated_resolution_eq_minimumDebt_div_sourceDebt_sq` gives the exact
   squared resolution `(D_* / D_0)^2`; the concentrated packet retains the
   fixed routed label, its marked dates, and its strict subsequence.
6. `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_canonicalPairMinimumEndpointSupportRankHandoff_or_debtAscent_or_rayStall`
   is the certificate-free source capstone.  It retains the canonical scalar
   minimum-return/stall split.  In the return arm it refines the actual paid
   endpoint into the minimum-fibre support handoff or strict endpoint-debt
   ascent.  The module is reachable through
   `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` and the `Research`
   reader umbrella.

Evidence seals:

- **M:** PASS.  The reviewed killed-mover identity, joint half-mixture
  compactification, exact minimum-fibre affinity, union support, and one-time
  strict support comparison are retained without strengthening the
  off-minimum or strict-stall alternatives.
- **L:** PASS.  The generic and Fin4 declarations are checked Lean.  Direct,
  named, reader, Research, and full builds, axiom-audit freshness, trust,
  exact-index import-graph, documentation, duplicate-proof,
  derivable-telescope, unit, whitespace, and source-width checks passed at
  promotion.  The raw-worktree import-graph check was obstructed only by the
  concurrent unintegrated
  `Research/Quitting/FinFourProducerAtlas/StrictEndpointNormalizedReturn.lean`;
  the handoff itself is reader-reachable and its named reader build passed.
- **A:** PASS for the Fin4 capstone.  It starts from the actual source-attached
  canonical forced-pair packet and constructs the literal endpoint profiles,
  common-word debt/gain account, joint compactification, and concentrated
  packet without accepting an endpoint or leaf certificate.
- **C:** PASS only in the minimum-endpoint arm, through the checked generic
  tangent-family extractor and same-minimum-fibre support-drop re-extractor.
  The off-minimum endpoint and strict canonical ray stall have no checked
  downstream consumer.

The strict support comparison is from the fresh half parent to the endpoint,
not from the old source support to the endpoint.  The construction is a
one-time handoff into the generic tangent-family lane.  It does not preserve
exactness of the old prefix roots after the endpoint update, restart the
canonical ray at that endpoint, prove renewable rank descent, consume the
off-minimum or strict-stall arm, produce terminal approximation, or prove a
uniform-equilibrium payoff or counterexample.  The mathematical provenance is
this reviewed packet and its independent audit; no external paper theorem is
imported.
