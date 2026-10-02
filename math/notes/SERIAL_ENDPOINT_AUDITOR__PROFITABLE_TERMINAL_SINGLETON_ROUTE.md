# The final screened pair-to-singleton route is already a paid edge

Author: `SERIAL_ENDPOINT_AUDITOR`

## Status

This is an interface-loss audit of the checked pure-nonsingleton screening
proof.  The mathematics is already present in the proof of
`quittingPureNonsingleton_screenedDispatch`, before its routed-coalition
cardinality split.  In the singleton branch the public result retains only
the routed label and mass comparison, and discards the simultaneously proved
positive gain, quantitative gain floor, exact mover-debt subtraction, and
best-endpoint certificate.

Retaining those fields strengthens the **local singleton branch** selected by
that particular best-endpoint calculation to a literal paid edge.  It does
**not** strengthen the final route stored by the existing Fin4 orbit.  The
generic orbit stops as soon as its terminal predicate is inhabited, and every
pair has an arbitrary mass-preserving Continue route to a singleton.  It need
not use the best endpoint computed by the local dispatch.  This distinction
blocks the tempting claimed atlas contraction.

## 1. What the checked proof has before the split

Fix an actual profile \(\sigma\), a marked date \(t\), a pure nonsingleton
coalition \(C\), a positive global minimum \(z_*\), and a live-mass floor

\[
 0<\lambda\le L_t(\sigma).
\]

In `quittingPureNonsingleton_screenedDispatch`, pure-nonsingleton screening
first proves

\[
 D(z_*)
 \le
 \sum_i \delta_i,
\]

where \(\delta_i\) is the literal Quit-versus-Continue root defect against
the actual prescribed tail.  It then selects a best endpoint \((p,a)\) and
defines the routed coalition

\[
 C'=C\triangle_{p,a}.
\]

Before testing whether \(|C'|=1\) or \(|C'|>1\), the proof has all of the
following, for the actual one-date target \(\sigma'\):

\[
 g:=U_p(\sigma')-U_p(\sigma_C)
   =L_t(\sigma)\,\delta_p>0,
\tag{1}
\]

\[
 g\ge
 L_t(\sigma)\frac{D(z_*)}{|I|}
 \ge
 \lambda\frac{D(z_*)}{|I|},
\tag{2}
\]

\[
 d_p(\sigma')=d_p(\sigma_C)-g,
\tag{3}
\]

and

\[
 \Pr_{\sigma_C}(C\text{ at }t)
 \le
 \Pr_{\sigma'}(C'\text{ at }t).
\tag{4}
\]

The update is a literal best Boolean endpoint, changes only player \(p\)'s
action at date \(t\), and preserves the complete post-date live-root tail.
Equations (1)--(4) do not use the later cardinality case split.

For `Fin 4`, (2) is

\[
 g\ge L_t(\sigma)D_*/4\ge\lambda D_*/4.
\tag{5}
\]

## 2. Exactly where the API drops the data

The proof names the relevant intermediate facts:

* `hgain` gives (1);
* `hgainPos` gives strict positivity;
* `hgainFloor` gives the first inequality in (2);
* `hgainDebt.2` gives (3); and
* `hrouteMass` gives (4).

It then performs

```text
rcases hcardCases with hsingleton | hnonsingleton
```

In the nonsingleton branch these facts are packaged in
`QuittingPureNonsingletonScreenedEdge`, whose inherited
`QuittingSameStageEndpointEdge` retains gain, debt, and mass.  In the
singleton branch the proof returns `QuittingSameStageSingletonRoute`, whose
fields retain only the mover, action, singleton label, cardinality, routing
identity, and stage-mass comparison.

Thus there is a local API loss in
`quittingPureNonsingleton_screenedDispatch`: when its selected best endpoint
happens to route to a singleton, the public singleton disjunct forgets the
paid data.  But `FinFourPureNonsingletonScreenedEndpoint` has a different,
more serious reason for documenting no payoff sign.  Its
`DispatchedOrbit` uses `QuittingSameStageSingletonRoute` as the terminal
predicate.  At a pair that predicate is already true by
`quittingSameStageSingletonRoute_of_card_eq_two`, independently of the local
best-endpoint dispatch.  The stored `terminal_at` witness may therefore be an
arbitrary member-Continue route, and none of `hgain`, `hgainPos`, or
`hgainDebt.2` applies to it.

## 3. Strong public packet

A suitable target is a new structure, because
`QuittingSameStageEndpointEdge` currently requires both source and target to
be nonsingleton:

```text
QuittingPureNonsingletonProfitableSingletonRoute
```

It should retain:

* `who`, `action`, and `action_eq_best`;
* the singleton terminal, its cardinality, and exact routed equality;
* `gain_eq_live_defect`, `gain_pos`, and `gain_floor_live`;
* membership of the literal singleton target semantic pair in the carrier;
* exact mover-debt subtraction;
* no-loss stage mass; and
* exact equality of every post-date live root.

Then the **local** dispatch can return

```text
Nonempty QuittingPureNonsingletonProfitableSingletonRoute
  or
exists target, Nonempty QuittingPureNonsingletonScreenedEdge
```

This exposes all data honestly when the selected best endpoint itself is a
singleton route.  It does not by itself let the existing Fin4 endpoint store
a profitable final route.

## 4. Interaction with the active-passport frontier

For a cofinal minimum-tail pure-pair row with fixed marked mass \(\lambda\),
the local strengthening gives a useful dichotomy:

* if the selected best endpoint leaves the pair, there is immediately a paid
  singleton edge with gain at least \(\lambda D_*/4\);
* if it joins an outsider, it is the already packaged paid nonsingleton edge
  to a triple.

It does **not** yet give a finite paid path ending in a singleton.  To obtain
that path one would replace the terminal predicate by the new paid-singleton
predicate.  Pair vertices can then persist in a closed dispatched segment.
The current `not_nonempty_finFourSameStageEndpointClosedSegment` proof no
longer applies: its period-two reduction uses essentially that every pair is
terminal, leaving only triples and the full coalition in a closed segment.
With paid terminality, ordinary strict endpoint cycles through pairs are not
excluded.

It does not alone resolve either live obstruction:

1. The whole singleton target need not have debt close to \(D_*\); only its
   post-date tail is near the minimum.
2. Equation (3) controls the mover exactly, but other players' unrestricted
   caps may rise by order one.  Hence neither total-debt descent nor
   no-new-debtor support descent follows.
3. The off-minimum unique-all-Continue normalized-passport node still lacks a
   minimum-return or exact chronology.  A paid horizontal terminal route
   does not manufacture that return.

So this closes a real local API loss but does not upgrade the existing orbit's
singleton arrival.  A new paid-terminal orbit theorem would need either to
consume its possible pair-containing closed cycles or to show, using the
positive-minimum source provenance, that one selected best endpoint must
leave a pair.  That is substantive new mathematics, not repackaging.

## Lean handoff

The safe proof task is to refactor the common construction in
`quittingPureNonsingleton_screenedDispatch` into a private or public raw
best-endpoint record before splitting on routed cardinality.  Both branches
then retain the same `hgain`, `hgainPos`, `hgainFloor`, `hgainDebt.2`, and
`hrouteMass`; the nonsingleton wrapper can remain unchanged, while the
singleton wrapper gains the fields above.

One must **not** add terminal-route accessors to
`FinFourPureNonsingletonScreenedEndpoint` from this alone.  To obtain Fin4
accessors analogous to

```text
FinFourPureNonsingletonScreenedEndpoint.edge_gain_floor_live
FinFourPureNonsingletonScreenedEndpoint.edge_mover_debt
FinFourPureNonsingletonScreenedEndpoint.edge_stageMass_le
```

for a terminal route, the Fin4 structure would have to carry the new paid
terminal predicate, followed by a new closed-cycle consumer.  The local
record needs no new analytic estimate; the global orbit upgrade does.
