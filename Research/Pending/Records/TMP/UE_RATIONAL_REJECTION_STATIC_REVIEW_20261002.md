Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Independent static review: rational rejection drafts 36–43

Verdict: PASS for mathematical argument and source-quantifier fidelity.
No mathematical defect requiring a theorem weakening or new assumption was found.
This is a static review of frozen drafts, not a Lean, axiom, build, or integration seal.

## Scope and method

Read `AGENTS.md` completely, both source exports completely, all eight patches
36–43, their `HANDOFF.md`, and `AXIOM_HARNESS.lean`. Inspected frozen prerequisite
patches 04, 09, 12, and 25. Inspected the actual shared collision-adjusted probe,
full-exact-root face drift, standard-Q face theorem and projectivization,
robust relation, exact-root relation, rational expected-payoff/regret bridges,
rational solo-root construction, polynomial syntax, cube-grid density, and
Mathlib finite-function encodings.

No Lean/Lake/Git commands, builds, shared-checkout edits, children, worktrees,
snapshots, or duplicate caches were used. The only write is this new report.

The reviewed source obligations are Theorem 4 and proof 8 of
`math/exports/QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md`, and item 5 and proof 7 of
`math/exports/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md`. Other results
in those packets are context and prerequisite contracts, not claimed as newly
validated implementations by this review.

## Mathematical and quantifier checks

1. Patch 36 proves density in the literal rational-endpoint closed box, with
   arbitrary index type and only coordinatewise lower <= upper. Continuous
   clipping is surjective onto the real closed-box subtype and preserves
   rational coordinates. A zero-width coordinate remains exactly fixed.
   No interior-point assumption or positive-width division is introduced.

2. Patch 37 interprets the five constructors of the actual
   `Math.Interval.RationalPolynomial` syntax. `ratCast_evalRat` relates its
   exact rational result to that same expression's `evalReal`. The test does
   not swap to a different polynomial or rely on syntactic degree bounds.

3. Patch 38 uses the actual independent Bernoulli product interpretation.
   Its absorption cast is 1 minus the all-Continue product, and its successor
   cast delegates to the existing rational expected-payoff bridge. Unit-cube
   coordinates recover every actual Boolean root, including boundary roots.

4. Patch 39 is explicitly a generic helper accepting a positive exact
   rejecting edge. It forms the closed source-box/root-cube product and
   intersects the relative neighborhoods for positive absorption, strict
   potential rejection, and every coordinate's strict regret bound. Finiteness
   justifies that last intersection. The comparison is the ordinary defect
   at the SOURCE against tolerance times the NEW root's absorption; neither
   a fixed absolute error nor target-based regret is substituted. Rational
   density selects source and root jointly. The target is their exact
   rational successor, whose box membership follows from reward/source bounds.
   Its Bellman residual is therefore zero. Rational exact Nash is not claimed.

5. Patch 40 removes the favorable-edge premise from the source-facing result.
   The actual supplied expression's normalized total degree or individual
   degrees feed frozen 04 or 09. Their full-exact-root exclusions yield a
   violation on the radius-three box. The canonical displacement bound proves
   that absorption zero would make successor equal source, so a strict
   violation has positive absorption. Patch 39 then produces the rational
   pair. The theorem retains at least two players, reward bound one,
   nonnegative own singletons, the same reward and expression, and every
   supplied positive rational tolerance. Omitting the source packet's upper
   tolerance bound is a valid strengthening of this rejection result.
   There is no added no-UE, Q, minimizer, or favorable-root premise.

6. Patch 41 has an executable exact-rational test. It checks both endpoint
   boxes, both probability bounds, positive charge, every ordinary source
   regret <= tolerance times charge, and potential drop < charge. The raw
   successor is definitionally the existing rational expected payoff once
   valid probabilities are bundled as a rational root. The soundness theorem
   returns the same source, same exact target, actual robust edge, positive
   actual absorption, and rejection for the same expression. Its nonnegative
   tolerance hypothesis correctly discharges the zero residual bound.

7. Enumeration is exhaustive over EVERY rational source/probability pair.
   `List.range (budget + 1)` followed by `Encodable.decode` contains a pair
   for every budget at least its canonical code, by `decode_encode`.
   The generic eventual-success helper openly assumes an accepted pair;
   the excluded-polynomial public theorem constructs that pair using 40.
   The conclusion is success at every sufficiently large finite budget.
   It does not assert a uniform threshold, runtime, denominator bound, or
   decision procedure for arbitrary candidates.

8. Patch 42 uses genuine FACE-ONLY standard-Q exclusion through frozen 25.
   Its `IsStandardQ` is textbook solvability for every real right-hand side;
   the actual matrix is the supplied reward table's centered singleton matrix.
   The inspected generic owner normalizes actual standard solutions, has
   positive cemetery coefficient before taking limits, bounds normalized
   residuals, and allows cemetery zero at the limit. No full-root-potential
   hypothesis is substituted for the source's face theorem.

9. Contraposition in 42 constructs an offending lower-face point with drift
   <= 0 from standard Q and quasiconvexity of the SAME polynomial. The rational
   approximation box sets upper(owner) = lower(owner) = the actual rational
   own-singleton value. All other coordinates retain their original closed
   face bounds. Gradient continuity supplies drift < 1/2 at a rational point
   on that exact face. No rational LCP witness or supplied minimizer is needed.

10. The rational source in 42 is the arithmetic version of the canonical
    frozen-upper collision repair. Its cast bridge uses the same reward,
    owner, face, upper cap, and rate. The small-rate probe gives exact source
    Nash, actual absorption equal to rate, and the exact boxed successor.
    The difference quotient tends to the face drift. Intersecting its
    neighborhood with the probe's neighborhood and choosing a rational rate
    gives 0 < rate < 1 and drop < 3 rate / 4. Freezing upper coordinates is
    valid here and gives internal bounds in radius M+1; the exported endpoint
    bounds are the source packet's radius M+2. Thus the smaller-box claim is
    justified by the proof but is not separately exposed in its conclusion.
    Nonempty players suffices for this draft; the source's n >= 2 case is
    included. One-player zero-diagonal standard Q has no examples.

11. Patch 43 uses the exact same witness from 42. Exact Nash gives zero
    ordinary regret; positive tolerance and absorption imply the tested
    relative bound, and 3 rate / 4 < rate gives the unit-charge rejection.
    The search keeps the supplied expression, table, tolerance, and M+2 box.

12. No branch constructs or rejects a game, proves UE, or turns one-stage
    Nash into a behavioral deviation cap. Approximate rational robust
    rejection and exact rational one-quitter rejection remain separate.

## Canonical reuse and presentation

The drafts reuse existing successor/regret semantics, the exact solo probe,
its derivative limit, endpoint bounds, the frozen full-root exclusions,
canonical polynomial regularity, and standard-Q face exclusion. New density
uses Mathlib product density and clipping rather than copying the existing
finite-grid rounding proof. Other namespaces have `evalRat`, but the searched
checkout does not already provide this interface for `RationalPolynomial`.
No mathematical proof duplication requiring a new owner was identified.

One optional wording correction: patch 40's docstring says “No candidate,
root, or minimum is selected as a new input”, although the proposed candidate
expression is an explicit parameter. Prefer “No favorable root or minimum is
supplied; the proposed candidate expression is the one being rejected.” This
does not affect the theorem or its mathematical validity.

## Verification limits and next gate

The handoff honestly labels these unapplied/uncompiled drafts. The axiom
harness names the added public interfaces but has no output to inspect.
This review supplies no L/A/C seal. Root still needs serialized module
compilation, actual axiom output, integration and repository policy checks.
Ordinary elaboration issues may require proof-script repair; no theorem
weakening, favorable-object premise, or replacement polynomial is justified
by this static review. In particular, preserve exact successor/source regret
and fixed owner-coordinate density while resolving casts or subtype syntax.

## Frozen input integrity

Recomputed SHA256 twice during this review. Every patch digest below matches
the handoff; HANDOFF matches the digest supplied with the assignment.

```text
36 b1c004e87b1ec88898acd12089d2ad598bf860b130fded45bf334986c74b1f12
37 9e27afc420d3c9645a6bb050d11ef071cd7bcbe650a8b621eb7d2552c85edaf3
38 6215031453395edaaa47bf3f296605658c90db8f06c80288b88b1f44fa954a99
39 3efda40ae095b4a2d49fae2e3b533d12cef24eade9f14a6e418a67a2348d7f18
40 2823f43d275aa6ff27f6bb4a258ee827529c17fc54ee89bda7964904db32f984
41 3e55ce72de55aca37307d1b71f262b9e9035be917dfcd426da2d03b0cdcba940
42 4c9dcee45a9b4c156af7443d08ea7aad6b069783bfa8ad9fd0f64bceb2838f02
43 72b8dbd0a55a8a7fbda5b2b25e657d994ba4a218ceb4484a83bea67fe04630ba
HANDOFF 7c49df7be4ea41365668eedd82372bb5bed449e33bc1c736d4d90dbe99ce89e8
AXIOM_HARNESS 7ed57bd16a71845d84bd2cc25dd5e522fcd4f7413a549dc4cf2299aa813fe8b1
04 f8916e57cd7e1dae92b81aabea403be8a26d7ec25e780c323992d1c47e9c4a5b
09 cc6f862cba399bc35bb971d15cd067f229dff172b534bac53343fdbb84420551
12 fee7dfd98d7d2867e424cdab9ad834406d2de87244fd451636fd08af02470f94
25 479f375cb9fffb4c38f08de7ca017b019a8d1697581c3c4a95cd8fdb7ba90532
```
