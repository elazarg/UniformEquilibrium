# Strict Fin4 maximal rays: a positive limit root, full binding, or card three

Author: CODEX_BOREL

Independent review:
[CODEX_NOETHER](../feedback/CODEX_BOREL__STRICT_RAY_TAIL_NORMALIZATION__BY_CODEX_NOETHER.md)

Source-facing correction audit:
[CODEX_RIEMANN](../feedback/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION__BY_CODEX_RIEMANN.md)

Solo-probe falsification and repair audit:
[CODEX_LEFSCHETZ](../feedback/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION__BY_CODEX_LEFSCHETZ.md)

Whole repaired cardinal-two gate:
[CODEX_CARDTWO_GATE](../feedback/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION__BY_CODEX_CARDTWO_GATE.md)

## Exact statement

Consider the canonical maximum-absorption exact-cap-root ray of a four-player
quitting game. Let \(b_k\) be its cap vector and \(q_k\) its selected product
root. Assume:

1. \(q_k\) is an exact Nash root against \(b_k\) and maximizes absorption
   among all exact roots against \(b_k\);
2. the ray is not eventually all Continue;
3. after a finite cut, every selected root has positive absorption, the total
   absorption is finite, and \(\operatorname{Abs}(q_k)\to0\);
4. \(b_k\to\bar b\); and
5. all Continue is the unique exact root against \(\bar b\).

For \(s_i=r_i(\{i\})\), define the limiting binding set

\[
A:=\{i:\bar b_i=s_i\}.
\]

If \(A\) is proper, then

\[
\boxed{|A|=3}.
\]

The exclusion of \(|A|=2\) uses one finite-cap, same-resolution
cubical-Sperner count. Global parity is one. Maximum absorption localizes
every finite-cap exact root near all Continue. After permuting the binding
pair to the last two coordinates, the localized count is zero: it contains
exactly two complete Kuhn simplices when both binding hazards are positive,
and no complete simplex when only one is positive.

No equilibrium-component index, perturbation homotopy, regularity theory,
subdivision invariance, or abstract local-parity specification is needed.

## Source-facing conclusion

The checked strict-ray source does not unconditionally supply assumption 5.
The honest exhaustive conclusion is:

- the limiting cap admits a positive-absorption exact root; or
- the limiting binding set is all four players; or
- the limiting binding set has cardinality three.

Indeed, if the first alternative fails, every exact limiting root has zero
absorption and is therefore all Continue. Closedness supplies all Continue as
an exact limiting root, so it is unique and the conditional theorem applies.

## Root-face formulas

For distinct players put

\[
J_{ij}:=r_i(\{i,j\})-r_i(\{j\}),\qquad
\delta_{k,i}:=b_{k,i}-s_i.
\]

Every player outside \(A\) has a strictly positive limiting Continue margin.
If \(A=\{i,j\}\), then on the face where both outsiders Continue the exact
Quit-minus-Continue comparisons are

\[
g_i(x_j)=-(1-x_j)\delta_{k,i}+x_jJ_{ij},
\qquad
g_j(x_i)=-(1-x_i)\delta_{k,j}+x_iJ_{ji}.
\tag{1}
\]

These are global affine formulas on the face, not linearizations.

## Proof

### 1. Localization of the complete finite-cap root set

Let

\[
\alpha(x)=1-\prod_h(1-x_h)
\]

be root absorption. Every coordinate satisfies

\[
x_h\le\alpha(x).
\tag{2}
\]

Choose a fixed neighborhood \(R\) of all Continue on which every outsider to
\(A\) strictly prefers Continue. For sufficiently large \(k\), maximality
gives, for every exact root \(x\) against \(b_k\),

\[
\alpha(x)\le\alpha(q_k)\to0.
\]

Equation (2) puts the entire exact-root set inside a smaller open neighborhood
\(V\) whose closure lies in \(R\). At every sufficiently fine mesh, the
one-mesh thickening of \(V\) also lies in \(R\). Thus every exact root lies in
\(V\), and every grid simplex counted in \(V\) sees both outsiders as strict
Continue.

### 2. Limiting solo probes force both collision signs

Write

\[
\bar\delta_h:=\bar b_h-s_h.
\]

For \(0<t<1\), let only player \(j\) Quit with probability \(t\). At the
limiting cap the endpoint differences are

\[
g_j=-\bar\delta_j=0,\qquad
g_i=tJ_{ij},\qquad
g_h=-(1-t)\bar\delta_h+tJ_{hj}\quad(h\notin A).
\tag{3}
\]

The first comparison is independent of \(t\), because a player's endpoint
difference depends only on the opponents' root. Every outsider has
\(\bar\delta_h>0\), so its comparison is strictly negative for sufficiently
small \(t>0\).

If \(J_{ij}\le0\), the probe is an exact positive-absorption root against
\(\bar b\), contradicting uniqueness of all Continue. Hence
\(J_{ij}>0\). Interchanging \(i,j\) gives

\[
\boxed{J_{ij}>0,\qquad J_{ji}>0}.
\tag{4}
\]

This limit-cap argument establishes signs of fixed reward-table constants.
No finite-cap inequality is inferred from a limiting inequality.

### 3. Coordinate normalization and finite-grid position

Permute coordinates so the outsiders are \(0,1\) and the binding pair is
\(2,3\). Use the standard reduced cubical-Sperner label: the first violating
coordinate labels a vertex, and label \(4\) is used when no coordinate
violates.

For every sufficiently fine complete four-dimensional Kuhn simplex whose
label-\(4\) anchor lies in \(V\):

- its first three vertices have outsider coordinates \(0,1\) equal to zero
  and carry labels \(2,3,4\);
- its first two steps increment the binding coordinates; and
- its last two steps increment coordinates \(1,0\).

Therefore every binding label in the count is evaluated using the exact face
formulas (1). No uncontrolled off-face payoff appears.

### 4. Both binding hazards positive

Suppose the selected finite-cap root mixes both binding players. Exact
indifference gives

\[
(1-x_j)\delta_{k,i}=x_jJ_{ij},\qquad
(1-x_i)\delta_{k,j}=x_iJ_{ji}.
\tag{5}
\]

For late \(k\), both positive hazards are strictly below one. Equations
(4)--(5) imply

\[
\delta_{k,i}>0,\qquad\delta_{k,j}>0.
\]

Thus each face gain has one positive threshold. At mesh resolution \(p\), put

\[
M=\lceil p x_i\rceil,\qquad N=\lceil p x_j\rceil.
\]

For sufficiently fine mesh, \(M,N\ge2\). The exact reduced-label enumeration
has precisely two complete simplices with anchor in \(V\):

1. the origin simplex, with labels \(4,3,2,1,0\); and
2. the simplex based one grid step below both sign-change thresholds, with
   labels \(2,3,4,1,0\).

Hence the local count is \(2=0\) modulo two.

### 5. Exactly one binding hazard positive

Suppose only \(i\) has positive selected hazard. Exact mixing and \(x_j=0\)
give

\[
\delta_{k,i}=0.
\]

On the binding face, (1) and (4) therefore give

\[
g_i=x_jJ_{ij}\ge0.
\tag{6}
\]

Throughout the localization neighborhood, coordinate \(i\) is below the
upper face. Its reduced grid label would require \(g_i<0\), so that label is
unattainable. No complete simplex is counted. The opposite solo orientation
is symmetric, and the local parity is again zero.

There is no third nonempty support pattern on a two-coordinate face.

### 6. Same-resolution contradiction

For the selected finite-cap box problem, \(V\) is open and contains every
exact root. Cubical-Sperner localization therefore makes its local
complete-simplex parity equal to the global parity \(1\) at every sufficiently
fine resolution. Sections 4--5 make that same local parity \(0\) at every
sufficiently fine resolution. Choosing one common resolution gives

\[
0=1\quad\text{in }\mathbb Z/2\mathbb Z,
\]

a contradiction. Therefore \(|A|\ne2\).

### 7. Cardinalities zero and one

If \(A\) is empty, eventual binding-support localization makes every late
selected root all Continue, contrary to the strict-ray hypothesis.

If \(A=\{i\}\), the positive late hazard of \(i\) is interior and exact
mixing pins \(b_{k,i}=s_i\). The other players have a uniform strict Continue
margin. One fixed small solo hazard for \(i\) is then an exact root for all
large \(k\), contradicting maximum absorption tending to zero.

Thus a proper nonconstant binding set has cardinality three.

## Boundary tests

### Positive-absorption limiting root

The limiting cap may admit a positive-absorption exact root even though the
selected finite-cap roots converge to all Continue. This is why the
source-facing result must return that possibility rather than assume limiting
uniqueness.

### Cardinal-three and full-binding survival

Checked zero-minimum regressions realize strict maximal-ray geometry with
cardinality-three binding and with full binding, and possess uniform
equilibrium payoffs. These regressions also have a positive-absorption exact
root at their limiting caps, so they do not witness the unique-all-Continue
subbranch. They show only that binding cardinality by itself cannot remove
either label from the unrestricted source-facing trichotomy.

### Why the two-player face alone is insufficient

The restricted two-player coordination game also has a both-Quit equilibrium,
and its global parity is one. The contradiction is four-dimensional:
maximum-absorption localization uses outsider incentives to exclude that
remote face equilibrium, while the grid-position theorem keeps outsider
coordinates in the finite count.

## Checked ingredients and remaining Lean adapter

The following generic ingredients are already checked:

- the solo-probe collision signs in
  Research/Quitting/BindingCollisionGainPositivity.lean;
- the ordered-Kuhn face-position theorem in
  Research/Topology/BoxComplementarityFaceSimplexPosition.lean;
- the both-mixed count-two theorem in
  Research/Topology/BoxComplementarityFaceLocalCountTwo.lean;
- the solo count-zero theorems in
  Research/Topology/BoxComplementarityFaceLocalCountZero.lean; and
- global and eventual localized parity in
  Research/Topology/BoxComplementaritySpernerEventualLocalParity.lean.

The source-specific Fin4 adapter is not yet checked. It must:

1. select a sufficiently late finite cap and build its Bernoulli
   QuittingEndpointNashBoxBridge;
2. permute the binding pair to coordinates \(2,3\);
3. choose nested localization neighborhoods using maximality, cap convergence,
   and the outsider margins;
4. derive the exact face formulas from the quitting endpoint expansion;
5. split the nonempty selected support into both-positive and solo cases;
6. invoke the checked local count; and
7. apply the same-resolution contradiction.

This replaces the older conditional ModTwoBoxComplementarityParitySpec route;
no inhabitant of that general specification is required.

## Adapter and consumer

The checked forced-pair strict-ray object provides the cap sequence, selected
roots, limiting cap, root maximality, and summable absorption. It does not
unconditionally provide uniqueness at the limiting cap. The adapter must
first test for a positive-absorption exact root there. Only when none exists
does the cardinal-three/full-binding reduction apply.

## Scope and nonclaims

This result does not consume:

- a positive-absorption limiting root;
- the cardinal-three ray;
- a full-binding ray;
- the eventual-constant stall; or
- the strict normalized inert endpoint.

It proves no terminal approximation, uniform payoff, chronological return,
renewable support drop, or counterexample. The repaired ordinary-mathematics
cardinality-two exclusion is complete; only its source-specific Fin4 Lean
adapter remains to be formalized.

## Formalization record

The export packet at intake had SHA-256
`ff1ae08e858d67ab7b21a6364e85b3b5fe396017068de2f2bc26425035aa7a09`.
The checked implementation was integrated and pushed at repository revision
`c9aefad1b696665ec321574395f0d688b8933d0f`.

The implementation has the following checked layers.

1. `MathUE/PMFProduct/Reindex.lean` provides
   `Math.PMFProduct.pmfPi_map_precompEquiv`, and
   `MathUE/PMFProduct/Bool.lean` provides the canonical
   `Math.PMFProduct.bernoulliBoolEquiv`.  These are the generic product-PMF
   reindexing and Boolean-simplex adapters used by the proof.
2. `UniformEquilibrium/Quitting/Root/PlayerReindex.lean` lowers the stable
   quitting-root transport API.  In particular,
   `quittingRootEndpointDifference_reindex`,
   `isZeroQuittingRootNash_reindex_iff`, and
   `quittingRootAbsorptionMass_reindex` make the coordinate normalization
   literal.  The pre-existing higher
   `UniformEquilibrium/Quitting/Classification/PlayerReindex.lean` API is
   preserved and imports this lower owner.
3. `Research/Quitting/Root/EndpointNashBoxComplementarity.lean` now constructs
   `quittingEndpointNashBoxBridge` for every finite reward table and cap.
   `QuittingEndpointNashBoxBridge.isSolution_iff_isZeroQuittingRootNash`
   identifies its cube solutions with exact Boolean product-root Nash
   solutions.  The bridge reuses the public Boolean-PMF equivalence rather
   than a second private inverse construction.
4. `Research/Quitting/BindingCollisionGainPositivity.lean` exposes the exact
   arbitrary-Boolean-PMF solo-face formula in
   `quittingRootEndpointDifference_soloStationaryRoot_other_cap_pmf` and the
   two positive cross-collision gains forced by limiting all-Continue
   uniqueness.
5. `Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`
   exposes the actual selected-root maximality as
   `FinFourStrictRayForwardExactCapTail.root_maximal`.
6. `Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinalityExplicit.lean`
   performs the source-specific normalization, finite-cap localization,
   outsider sign control, both-active count-two/solo count-zero split, and
   same-resolution contradiction.  Its public capstones are
   `FinFourStrictRayForwardExactCapTail.bindingFinset_card_ne_two`,
   `FinFourStrictRayForwardExactCapTail.bindingFinset_eq_univ_or_card_eq_three`,
   and
   `FinFourStrictRayForwardExactCapTail.positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three`.
   The first two consume the explicit limiting all-Continue uniqueness
   hypothesis.  The source-facing third theorem returns a positive limiting
   root when uniqueness fails and otherwise derives that hypothesis from the
   absence of such a root.
   No inhabitant of `ModTwoBoxComplementarityParitySpec` is assumed, and the
   pinned GameTheory Sperner submodule is not used as a substitute for the
   concrete same-grid local count.
7. `Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean`
   strengthens
   `minimumLawHandoff_or_offMinimumDescent_or_ballistic_or_omitted_or_cardThree`
   to consume only the actual strict flow.  It no longer takes a supplied
   parity specification or finite-cap certificate.

Evidence seals:

- **M:** PASS.  The exact face identities, limiting collision signs,
  nested finite-cap localization, coordinate permutation, both-active and
  solo support cases, and common-resolution parity contradiction match the
  reviewed proof.  The source-facing theorem retains the positive limiting
  root alternative rather than assuming uniqueness.
- **L:** PASS.  The new generic, production, and Research modules pass direct
  and named Lean builds.  The public capstones report only `propext`,
  `Classical.choice`, and `Quot.sound`.  The production additions are present
  in the generated exhaustive axiom audit, and the Research additions are
  reachable from the Research umbrella.
- **A:** PASS.  The theorem consumes one actual
  `FinFourStrictRayForwardExactCapTail`, including its source-selected cap
  sequence, roots, cap limit, summable absorption, eventual binding support,
  and literal maximum-absorption property.  It constructs the late cap,
  bridge, permutation, neighborhoods, and same-resolution contradiction
  internally; no conclusion-equivalent localization or parity certificate is
  supplied by the caller.
- **C:** PASS at the source-facing branch level.  The positive-root branch is
  immediately consumed into a same-residual minimum-law handoff or a strict
  off-minimum point below the ray limit.  The full-binding branch is consumed
  into uniformly ballistic renewal or one fixed player omitted infinitely
  often.  Binding cardinality three is exposed literally.  These are not
  terminal consumers: the returned minimum handoff, strict descent,
  ballistic, omitted-player, and cardinal-three endpoints remain open.

Validation at revision `c9aefad1b696665ec321574395f0d688b8933d0f`
included the documentation gate, 109 script unit tests, execution of all 33
registered experiments, import-graph, proof-duplicate, reward-bound,
redundant-order, derivable-telescope, and trust checks, and a full
`lake build` of 11,078 jobs.  The generated axiom audit was exact.

Nonclaims:

- no theorem eliminates the positive-root branch or makes either of its
  returned endpoints renewable;
- no theorem consumes cardinality three, ballistic renewal, or the
  frequently omitted player;
- full binding is routed but not contradicted;
- the result proves no terminal approximation, chronological return,
  uniform-equilibrium payoff, strict-ray impossibility, or counterexample;
  and
- the older abstract parity contract remains a valid conditional interface,
  but it is no longer an input to the actual-flow cardinality consumer.
