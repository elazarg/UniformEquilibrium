Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Reflection rational rejection and exhaustive search: independent static review

## Verdict and evidence boundary

Mathematical/source PASS for frozen 37/39/40/41, using already-reviewed 36/38 and the separate canonical Bernoulli continuity overlay for 38. The four new patches implement reflection packet item 5 and proof Section 7 without a supplied rejecting pair, minimizer, standard-Q certificate, normality premise, no-UE premise, or denominator bound. No definite Lean API error was found in this pass. This is an independent STATIC review, not a compiler, axiom, integration, downstream-consumer, full-build, or whole-packet seal.

One important distinction must remain explicit: 39/40 produce strict source regret < τA. The executable test in 41 accepts regret ≤ τA, exactly as the source's item 5 requests. Consequently the first pair returned by that search is not asserted to satisfy the stronger strict regret inequality. Strict rejection P(v)−P(u)<A and positive absorption hold in both interfaces. Do not describe the search output as strict-regret certified without a separate strengthening.

The full reflection export was read, including the exact statement, definitions, strategic dependencies, Sections 1–7, adapter, boundary fixtures, and nonclaims. The selected four patch bodies and original handoff/harness were read, and relevant current semantic owners and pinned enumeration APIs were inspected. No compiler, Git, shared edits, children, cache duplication, or mathematical research was used. The Unicode-math skill governs notation only.

## Claim-by-claim review

### 37: same-expression executable evaluation

`Math.Interval.RationalPolynomial.evalRat` and `ratCast_evalRat` in future `MathUE/Interval/RationalPolynomialRationalEvaluation.lean` interpret the existing five-constructor syntax directly. Their structural proof matches addition, negation and multiplication with the SAME `evalReal`, not a substituted polynomial or rounded evaluator. No normalization is required at runtime. The later degree tests use the existing canceled `toMvPolynomial`; this does not change the expression evaluated by the search.

Discovery found rational evaluators for the distinct `RationalMaxExpression` and `RealQuantifierElimination.RingExpression` syntaxes, but no existing evaluator for this exact syntax or ready-made bridge that would eliminate this five-case adapter. Replacing it with a new syntax conversion would add proof work and imports, not remove a duplicated foundation.

### 39: one simultaneous rational approximation in closed boxes

`exists_rational_robust_rejection_of_positive_exact_rejection` in future `UniformEquilibrium/Quitting/Projective/RationalRobustRejectionDensity.lean` is explicitly a GENERIC helper. It legitimately takes a positive, exact real rejecting edge as its premise; 40 supplies that edge internally.

The relative topology is on the product of the literal closed source box and closed probability cube. Absorption, every source-based coordinate regret, and the potential drop are made simultaneously strict in one neighborhood. The finite-player `Filter.eventually_all` step does not select a different neighborhood or pair per player. One call to the product dense-range result selects ONE rational source and ONE rational probability vector. It includes boundary probabilities 0 and 1, source faces, and zero-width source coordinates. No interior approximation, clipping of the actual root definition, or independent target rounding is used.

`quittingUnitCubeSimplex_eq_actual` recovers the original real PMF root; `quittingUnitCubeSimplex_rational_eq` recovers the selected rational root. `quittingRootSuccessorPayoff_rational_eq_cast` identifies its exact successor. `abs_quittingRootSuccessorPayoff_le_bound` then supplies the target box from the same reward and source bounds. Thus both endpoints are in the same full box and the robust Bellman residual is exactly zero.

Exact source Nash is used only to establish zero original defect. Positive τ and positive original absorption make the regret inequality open. The output is approximate Nash at the SOURCE; it is not exact rational Nash, target-based Nash, or a restricted unilateral-action test. Canonical `isεQuittingRootNash_iff_coordinateNashDefect_le` (`UniformEquilibrium/Quitting/Root/NashDefect.lean`) gives the ordinary all-PMF-deviation interpretation of the coordinate bound. This is still a one-stage root statement, not a repeated-game behavioral-equilibrium conclusion.

### 40: favorable edge produced internally, with the full degree disjunction

`exists_positive_exact_rejection_of_not_fullRootPotential` in future `UniformEquilibrium/Quitting/Projective/ExcludedPolynomialRationalRejection.lean` negates the actual universally quantified full-root relation. It obtains a boxed source, exact source Nash root, and strict failure. Its zero-absorption case invokes the canonical bounded displacement estimate, forces successor=source, and contradicts strict failure. No omitted positive-absorption premise is added to the source-facing producer.

`exists_rational_robust_rejection_of_excluded_polynomial` fixes the rational reward table, rational expression, and supplied positive rational tolerance BEFORE existentially producing the pair. Its only substantive source assumptions are n≥2, all terminal coordinates bounded by one, nonnegative own singletons, and canceled totalDegree≤2 OR every canceled coordinate degree≤1. Current owners `not_isQuittingFullExactRootPotential_rational_totalDegree_le_two` and `not_isQuittingFullExactRootPotential_rational_multiAffine` produce the failure for the identical actual evaluation. There is no convexity, Hessian sign, selected critical minimum, lower-face-only minimum, or total-degree restriction on the multi-affine branch. In Fin4 the latter includes every one of the sixteen square-free monomials.

The output retains radius three for both rational endpoints, positive actual PMF absorption, STRICT source regret < τA, and strict drop < A for the identical expression. The proof derives potential continuity from canonical polynomial regularity. Allowing every τ>0 is a valid strengthening of the packet's 0<τ≤1/4; it does not assert a uniform tolerance or runtime bound. A one-player or empty-player extension of the source-facing theorem is not claimed.

### 41: exact test, every rational pair, eventual success

In future `UniformEquilibrium/Quitting/Projective/RationalPotentialRejectionSearch.lean`, `rationalQuittingPotentialRejects` is a finite decidable rational predicate. It tests source box, both probability bounds, exact successor box, positive absorption, ordinary source regret ≤ τA, and literal same-expression drop < A. Invalid raw probabilities are rejected. The rational Boolean expectation and endpoint regret are existing canonical implementations, not new payoff semantics. Runtime definitions precede the noncomputable proof section; actual PMF interpretation is confined to proofs.

`rationalQuittingRejectionCandidates` decodes every integer in `List.range (budget+1)`. `mem_rationalQuittingRejectionCandidates` uses the actual `Encodable.decode_encode` identity and proves inclusion of EVERY rational pair for EVERY budget at least its encoding. It is not a hand-picked dense sequence or finite denominator truncation. Pinned `Rat.Encodable` and `Encodable.finArrow` provide computable encodings of the finite rational vectors; product encoding gives the pair. Failed decodings are harmlessly omitted.

`rationalQuittingPotentialRejectionSearch_eventually_succeeds` is correctly generic and has a supplied accepted pair existential. The source-facing `rationalQuittingPotentialRejectionSearch_eventually_succeeds_of_excluded_polynomial` discharges it internally using 40 for the SAME table, expression and supplied tolerance. The threshold is the internally obtained pair's code. The conclusion quantifies over all larger budgets. Nothing supplies a rejecting pair, a code, a denominator cutoff, or an a priori runtime bound to that final theorem.

`rationalQuittingPotentialRejects_sound` reconstructs the actual root from the accepted raw vector. Its public conclusion explicitly retains root probabilities, literal source, literal exact target, successor equality, the floor-free robust edge, positive actual absorption, and strict potential rejection. The regret calculation uses `rationalQuittingBooleanPayoff reward pair.1`, so the continuation annotation is the source, never the target. The actual edge uses the same boxed endpoints and the same root's simplex. At τ=0 this conditional soundness theorem remains valid for any accepted exact-regret pair; the source-facing existence/termination theorem correctly needs τ>0.

## Minimal API recommendations, not hidden proof repairs

1. Keep the already-frozen canonical Bernoulli continuity reuse overlay after 38. It preserves all public signatures and the literal unclipped root definition. No second Bernoulli continuity proof is needed.
2. Add a narrow returned-result facade if this group is to expose an explicit end-to-end search consumer. Suggested `rationalQuittingPotentialRejectionSearch_sound` should take `search? reward expression bound tolerance budget = some pair` and nonnegative tolerance, and conclude exactly the existing `rationalQuittingPotentialRejects_sound` output for that SAME pair. The entire proof should obtain acceptance from pinned `List.find?_some` and delegate. Optionally a two-line accepted-result lemma can expose that intermediate fact. This is an explicit theorem-surface improvement, not a mathematical gap in the present algorithm or its source termination proof.
3. Do not silently advertise strict regret for the returned pair. If root deliberately requires the stronger search-output API rather than the packet's non-strict bound, an explicit strict-test variant can reuse 40's strict witness and the same enumeration proof. This is optional relative to the export, changes the acceptance contract, and should not be smuggled in as a proof-only repair.

No new replacement proof, hypothesis strengthening, linter option, axiom, or trust exception is recommended. Residual compiler risks are ordinary reducibility/elaboration at 39's selected product cast and 41's raw-successor/root-successor casts; static inspection did not establish a failing site. Pinned `List.find?_isSome`, `List.mem_filterMap`, `List.mem_range` and `Encodable.decode_encode` have the shapes used by the drafts.

## Canonical dependency boundary and application scope

Order: 36, 37, 38, its Bernoulli overlay, 39, 40, 41. Already-present prerequisites are the actual quadratic exclusion, actual multi-affine exclusion, rational polynomial regularity, root expected-payoff/regret casts, root continuity, bounded endpoint/displacement estimates, and the floor-free robust relation. The original all-eight-unit harness imports 43, hence is NOT the narrow harness for this group. Root should use a group-only harness importing 41 and printing the selected declarations, with the shared 36/38 declarations as desired; neither exact-solo42 nor its search join43 is needed for the reflection item-5 claim.

This group is not a rational reward producer, no-UE characterization, strategic normalization, exact-Nash rational selector, or complete decision procedure. It excludes an already supplied polynomial candidate under the displayed degree disjunction. Other reflection packet claims and future fixture/import changes remain outside this group's seal.

## Frozen hash inventory

All following bytes were SHA256-verified in this pass; originals were untouched.

```text
Export REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md
a28b23b400cfef2fce48d0dfd33027b344e00d45a015de549c328dce4f397e69
/tmp/ue-potential-completion-matrix-FJa3ts/ORDERED_MANIFEST.json
32b2d2308371826d964b46f6c89477d269cee88586175d6989fd1ebca80843dc
/tmp/ue-rational-rejection-MLTrufnP/HANDOFF.md
7c49df7be4ea41365668eedd82372bb5bed449e33bc1c736d4d90dbe99ce89e8
/tmp/ue-rational-rejection-MLTrufnP/AXIOM_HARNESS.lean
7ed57bd16a71845d84bd2cc25dd5e522fcd4f7413a549dc4cf2299aa813fe8b1
36_RATIONAL_CLOSED_BOX_DENSITY.patch
b1c004e87b1ec88898acd12089d2ad598bf860b130fded45bf334986c74b1f12
37_RATIONAL_POLYNOMIAL_EVALUATION.patch
9e27afc420d3c9645a6bb050d11ef071cd7bcbe650a8b621eb7d2552c85edaf3
38_RATIONAL_BOXED_ROOT_INTERFACES.patch
6215031453395edaaa47bf3f296605658c90db8f06c80288b88b1f44fa954a99
39_RATIONAL_ROBUST_REJECTION_DENSITY.patch
3efda40ae095b4a2d49fae2e3b533d12cef24eade9f14a6e418a67a2348d7f18
40_ACTUAL_EXCLUDED_POLYNOMIAL_RATIONAL_REJECTION.patch
2823f43d275aa6ff27f6bb4a258ee827529c17fc54ee89bda7964904db32f984
41_EXHAUSTIVE_RATIONAL_REJECTION_SEARCH.patch
3e55ce72de55aca37307d1b71f262b9e9035be917dfcd426da2d03b0cdcba940
/tmp/UE_RATIONAL_BOXED_ROOT_38_CANONICAL_BERNOULLI_REUSE_20261002.patch
8739b1e950ff2d911012bc13de42ef2fc6665f285ae87e85187c44aab5ac06b0
```

The numbered patch paths above are under `/tmp/ue-rational-rejection-MLTrufnP/`. The 38 overlay has previously verified payload base `e396d1676630ce631449206de9334857232b91d6b7d7de3f059af24988c0598c` and result `47fcf61929f593a050c5476b23fc398c50877d825f41323f783ad72a8f0b3568`.

Current canonical owner snapshots (relative checkout paths):

```text
UniformEquilibrium/Quitting/Projective/FullExactRootPotentialQuadraticExclusion.lean
91a177d317c897b26f91df0b8a5cdfd7fe24e9f71db30e7d7d38f805d7894621
UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMultiAffineExclusion.lean
8e291161ced7e4486bbf2b4ed5dc479e52b568f81fd773a781d3a486d40551ff
UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean
77e260563e679b8f6fb0f2583a96360480b5ebef1e9a5e1ef7086910aa25bc1f
UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean
da2aa9371840e8713ce545fb9bf80006088a9c26279794afed6855a5e00428b0
UniformEquilibrium/Quitting/Root/BoundedEndpoint.lean
5e1bc4e649aa1bc5411a5e63a8b00247aa08a1313a5d69ea1f839a4dd837ade5
UniformEquilibrium/Quitting/Root/NashDefectContinuity.lean
803794f8505fbce12c470adeb845980b1de0c3ea131679ad35de26f9e0585f23
UniformEquilibrium/Quitting/Root/RationalFiniteWordSemantics.lean
f5fd759e6af2c4bf33a48c37c3f01a5dfdc401ea2d04f30a76a8a15065875e87
UniformEquilibrium/Quitting/Root/RationalQuittingRootGridSelector.lean
86bc5acaf0f3b3c576c3bf27e179622686a97e5faee99fc6c36602a10d09964a
UniformEquilibrium/Quitting/Root/NashDefect.lean
1ac2ae76a070204d2a1426a64f1be23b442a6862461978fa97a068ada95b1bc3
MathUE/Interval/RationalPolynomial.lean
557c9b1d13b07fd53b685ad189aa5595029612ad6e9a9bfa9bd835b448d2c59b
MathUE/Interval/RationalPolynomialRegularity.lean
22b8ac7250ec19b625483520c0e41aab6cf1699798d1fbf163f7733d297b08ba
.lake/packages/mathlib/Mathlib/Data/Rat/Encodable.lean
390d9a42c1cf3d7eb96d638228592e5493a280494649e4ea36bda603fe10fe1c
.lake/packages/mathlib/Mathlib/Logic/Encodable/Pi.lean
0ee96b0937043b2ecf835aa7da8512a85f90e9a039aa6c2664060b976c231f15
```

No current status in the older manifest overrides root's actual application/build record. These hashes identify reviewed bytes, not their checked status.
