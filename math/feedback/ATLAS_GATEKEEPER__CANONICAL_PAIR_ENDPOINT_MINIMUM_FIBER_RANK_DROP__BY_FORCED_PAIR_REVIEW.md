# Review of canonical pair endpoint minimum-fibre rank drop

Reviewer: `FORCED_PAIR_REVIEW`

Source:
[`ATLAS_GATEKEEPER__CANONICAL_PAIR_ENDPOINT_MINIMUM_FIBER_RANK_DROP`](../notes/ATLAS_GATEKEEPER__CANONICAL_PAIR_ENDPOINT_MINIMUM_FIBER_RANK_DROP.md)

Verdict: **PASS for the killed-mover identity, half-chord affinity, strict
support inclusion, checked re-extraction handoff, and raw endpoint-packet
regeneration; REVISE the atlas-rank wording before export.**

The required repair is conceptual but does not alter the proved formulas:
the strict inclusion is

```text
support(Y) proper-subset support(H),
```

where `H` is the freshly constructed half-mixture minimum.  It need not be
`support(Y) proper-subset support(X)` for the incoming exact-prefix source
`X`.  Thus this is a valid one-time transition into a freshly based
support-ranked tangent-family lane, but it is not by itself a renewable rank
decrease for repeated canonical-pair processing.  Export is warranted after
that scope is explicit and any downstream use names the consumer which accepts
the fresh tangent family without requiring the original exact-prefix packet.

## 1. Exact identity `g_k = d_p(Z_k)`: PASS

At the unprefixed pure pair, at least one player other than `p` Quits surely.
Therefore every arbitrary behavioral deviation of `p` is screened at the
current row.  Its unrestricted whole-profile debt is exactly its pure
Quit-versus-Continue root defect.  Since the selected endpoint has positive
gain,

\[
                       \delta_p=d_p(Z_0)>0.
\]

Each outer root in the canonical ray is exact cap--Nash against its actual
successor.  The checked identity
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
therefore scales the debt through the full prefix:

\[
                       d_p(Z_k)=\alpha_kd_p(Z_0).
\]

The copied same-stage deviation is reached with the same survival factor, so
the literal payoff identity gives

\[
                       g_k=\alpha_k\delta_p=d_p(Z_k).
\]

Finally, changing only `p`'s prescribed strategy leaves `p`'s unrestricted
cap unchanged.  The exact own-debt subtraction in
`quittingLiteralSameStage_bestEndpoint_gain_and_debt` yields

\[
                         d_p(Y_k)=0
\]

at every index.  This is all-behavioral: no stationary or best-response-
attainment restriction is used.

The equality uses exactness of the incoming outer stack.  The same literal
roots need not remain exact after the endpoint update; that affects
renewability, not the displayed identity.

## 2. Varying-source half-mixture and coordinate affinity: PASS

After the common compact subsequence,

\[
  \operatorname{Sem}(Z_k)\to X,
  \qquad
  \operatorname{Sem}(Y_k)\to Y,
\]

with `D(X)=D(Y)=D_*` in the equality arm.  For every `k`, the two profiles
have identical opponents and differ only in `p`'s complete behavioral
strategy.  Their half stopping-law mixture is therefore a literal behavioral
profile, not a correlated mixture of whole profiles.

Coordinatewise stopping-law debt convexity gives

\[
 d_i(H_k)\le \tfrac12d_i(Z_k)+\tfrac12d_i(Y_k).
\]

Any compact cluster `H` is in the terminal-semantic carrier.  Summing and
passing to the limit gives `D(H)<=D_*`; global minimality gives the reverse
inequality.  Every coordinate convexity gap is nonnegative and their finite
sum is zero, so each gap vanishes:

\[
                 d_i(H)=\tfrac12d_i(X)+\tfrac12d_i(Y).
\]

No endpoint attainment and no common limiting best-response witness is
needed.  The same argument may retain the complete terminal law: the checked
`quittingTerminalOutcomeMass_stoppingLawMixture_eq` makes every law coordinate
affine before compactification.

## 3. Strict support inclusion: PASS, with the correct reference source

Debt nonnegativity gives

\[
 \operatorname{supp}_+d(H)
   =\operatorname{supp}_+d(X)\cup\operatorname{supp}_+d(Y).
\]

Consequently `support(Y) subseteq support(H)`.  Since `d_p(X)>0` and
`d_p(Y)=0`, player `p` belongs to the right-hand support but not the left-hand
support.  Therefore

\[
 \boxed{\operatorname{supp}_+d(Y)
        \subsetneq\operatorname{supp}_+d(H).}
\]

This correctly handles support entry at `Y`: every newcomer is included in
the union-support base `H`.

It does **not** imply

```text
support(Y) proper-subset support(X).
```

For example, debts may exchange support from one coordinate of `X` to a new
coordinate of `Y`; then `H` contains both.  This is why the half-mixture
argument needs no maximum-support hypothesis, and also why its rank is based
at `H`, not at the incoming `X`.

## 4. Checked tangent-family handoff: PASS

The precise hypotheses line up with the checked declarations.

First apply `exists_positiveMinimumDebtTangentFamily_of_pair` to `H`:

* `H` is in the carrier;
* global minimality follows from `D(H)=D_*`; and
* `D(H)>0` follows from the positive minimum.

Let the resulting frontier have base `H`.  Then apply
`exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished` with point
`Y`:

* `Y` is in the carrier;
* `D(Y)=D(H)`;
* every positive coordinate of `Y` lies in `support(H)`; and
* `p` lies in `support(H)` and has zero debt at `Y`.

The declaration returns a new tangent family based at `Y` with support a
strict subset of the fresh frontier's support.  No relation between the two
tangent arrays is required.

The actual endpoint sequence is not itself a tangent family.  It supplies the
carrier points and the common chord; the checked generic extractor builds new
actual realizing profiles at `H` and `Y`.

## 5. Rank audit and the class-closure caveat

The note's local strict support theorem is genuine.  The stronger phrase
"the canonical source has undergone a renewable atlas rank descent" needs a
qualification.

The incoming state is `X`, while the parent of the checked strict inclusion is
the newly introduced `H`.  `support(H)` may be strictly larger than
`support(X)`.  Hence the argument does not give a decreasing sequence

```text
support(X_0) > support(X_1) > support(X_2) > ...
```

under repeated canonical endpoint processing.

There is also an exact closure reason.  The endpoint and half-mixture retain
the literal pre-mark roots, marked live mass, and post-mark tail, but the old
pre-mark roots need not remain exact cap--Nash roots for the changed suffix.
Thus:

* maximizing or iterating inside exact-prefix pure-pair sources excludes the
  midpoint needed for the union-support argument; while
* enlarging to an endpoint/mixture-closed class allows maximum points which
  need not have an exact incoming stack, so the identity `g=d_p` cannot be
  invoked again there.

This is the nonrenewability seam recorded independently in
`FORCED_PAIR_REVIEW__MINIMUM_FIBER_KILLED_MOVER_CHORD_AND_CLOSURE_SEAM.md`.

There is nevertheless an honest useful handoff: construct the fresh frontier
at `H`, re-extract at `Y`, and then **leave the canonical-pair lane**.  If a
named downstream theorem consumes an arbitrary positive-minimum tangent family
using its own monotone support-rank recursion, the original exact-prefix
packet is no longer needed.  In that form the step is a valid one-time lane
transition, and the output rank is at most `card(I)-1` because `p` is absent
from `support(Y) subset support(H) subset univ`.

Before an export calls this a completed atlas consumer, it should name that
downstream tangent-family lane or state explicitly that it only constructs the
strictly nested pair of fresh frontiers.  It should not imply repeatability of
the canonical endpoint operation at `Y` with another strict decrease.

## 6. Source-attached half chord: PASS at the stated strength

The source and endpoint differ only at the marked action of `p`.  Their
one-player stopping-law mixture preserves the common literal roots before the
mark and the common formal post-mark tail.  At the mark, the source coalition
or routed endpoint coalition retains at least half the reached mass.  Payoff
affinity gives remaining gain `g_k/2` from the half profile to the endpoint.

This is enough to retain a dependent origin record and fixed positive mass and
gain floors in the minimum-return arm.  It is not enough to retain:

* exactness of the old outer prefix at `H` or `Y`;
* the old packet owner's zero defect; or
* the same actionable paid residual at the endpoint, where `p`'s defect is
  zero.

The source note acknowledges the latter two.  It should add the first one
explicitly when describing the class enlargement.

## 7. Raw endpoint concentrated packet: PASS with packaging caveat

After freezing the finite labels on a cofinal subsequence, the literal
endpoint sequence supplies the fields of a generic
`QuittingReprojectionConcentratedPacket`:

* one routed nonempty terminal has a fixed stage-mass floor;
* the marked date is below cutoff `mark+1`;
* the semantic-prefix equality is the literal spine factorization;
* the endpoint root-coordinate defect of owner=`mover` is exactly zero; and
* any positive scale tending to zero makes the normalized defect identically
  zero.

The routed coalition and the decoder atom must indeed be frozen separately;
they need not coincide.  The packet structure itself does not store the old
minimum source, tail, or incoming edge.  A source-retaining dependent wrapper
is therefore needed if later code must recover that provenance.  This is a
Lean packaging issue, not a mathematical gap in packet existence.

If the routed terminal is nonsingleton and the endpoint whole debts tend to
`D_*`, the checked concentrated-collision dispatch can be called again.  If
the routed terminal is singleton, a different atlas node is required.  In the
strict endpoint arm `D(Y)>D_*`, reindexing or changing the artificial scale
does not restore the dispatch's near-minimum whole-source premise.  The note's
boundary statement is correct.

## 8. Export verdict

The following package is export-worthy ordinary mathematics after a wording
revision:

1. exact whole-debt killing at canonical exact-prefix pure-pair endpoints;
2. the varying-source minimum-fibre half-chord with exact coordinate and law
   affinity;
3. strict support inclusion `support(Y) proper-subset support(H)` and exact
   tangent-family re-extraction at `Y`; and
4. raw endpoint concentrated-packet regeneration with its explicit
   near-minimum boundary.

The export must state:

* the rank parent is the freshly constructed half-mixture `H`, not the
  incoming source `X`;
* no inclusion between `support(Y)` and `support(X)` is proved;
* this is a one-time transition into a generic tangent-family lane unless an
  additional re-exactification theorem is supplied; and
* repeated canonical processing is not shown well-founded.

With those repairs, **PASS for export**.  Without them, the phrases "consumes
the node" and "renewable rank descent" overstate the result.

## Checked declarations and files audited

* `quittingLiteralSameStage_bestEndpoint_gain_and_debt`,
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticReachedRowDebtLocalization.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
* stopping-law terminal-law and debt affinity/convexity in
  `TerminalSemanticStoppingLawDebtConvexity.lean` and
  `TerminalSemanticStoppingLawMinimumFiberAffine.lean`;
* `exists_positiveMinimumDebtTangentFamily_of_pair` and
  `exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`,
  `PositiveMinimumDebtTangentFamily.lean`; and
* `QuittingReprojectionConcentratedPacket`,
  `TerminalSemanticResetReprojectionTemporalSplit.lean`.

