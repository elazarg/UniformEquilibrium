Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Independent static review: screened polynomial density61–62

## Verdict

PASS for the mathematics and source quantifiers of these two units. No precise source or proof-call defect was found. This is an independent static review, not a Lean/elaboration, axiom, warning-cleanliness or integration seal. The original drafts are unchanged.

Read both complete patches, handoff and harness, the complete1109-line screened-root export, the complete prior independent algebra review, and exact relevant library/chart/polynomial/witness declarations. All ten old prerequisite patch hashes match the previously reviewed versions, including both separate repairs. This review does not repeat their entire algebra audit or represent them as compiled. No compiler, Lake, Git, shared edit, cache, worktree or child agent was used.

## Generic density and closed-boundary audit

Unit61 proves openness from actual polynomial evaluation continuity. The nonzero hypothesis enters only the density theorem, as appropriate. Assuming an open region missed the nonvanishing set would make the same polynomial vanish on that region. `isOpen_pi_iff'` supplies a product of open coordinate neighborhoods; each side contains a nonempty open interval and is infinite. The exact pinned `MvPolynomial.funext_set` then identifies the polynomial with zero. No degree induction, sampled testing, rational-coefficient assumption or favorable nonvanishing point is introduced.

The rational selection theorem first intersects the region with the open nonvanishing set. Only after establishing this intersection is nonempty does it apply `DenseRange.piMap` to `Rat.denseRange_cast`. This is the correct order: mere density of two arbitrary sets would not suffice. I checked the exact intersection orientation in `dense_iff_inter_open`/`Dense.inter_open_nonempty` and the actual `DenseRange.exists_mem_open` signature. The returned rational coordinates therefore evaluate nonzero for the identical supplied polynomial.

Finite variable types, including the empty type, are allowed. Empty variable indexing causes no hidden failure: the coordinate space is a singleton and a nonzero constant polynomial cannot vanish there. No nonempty-index premise is needed.

The closed-box approximation theorem requires every side to have strictly positive width, permits the starting point anywhere in its closed box, and constructs a rational point in each interval

    (max(lower, point−radius), min(upper, point+radius)).

Its nonemptiness proof uses the positive width, closed starting-point inequalities and positive radius. This remains valid at lower and upper corners and all intersections of faces. The conclusion is strictly interior and coordinatewise radius-close. It does NOT claim rational nonvanishing density within a fixed lower-dimensional face or a degenerate zero-width box: a polynomial could vanish identically on such a face. The source needs interior perturbations near closed boundary points, so this distinction is correct and no repair is needed.

## Same actual polynomial, fixed b before every singleton vector

Unit62's evaluation bridge uses `MvPolynomial.eval_map` to equate the existing integer-polynomial evaluator with real evaluation of the coefficient-cast SAME polynomial. Its nonzero premise is internally discharged by `screenedRootExclusionPolynomial_map_real_ne_zero`, not supplied by a source-facing caller. The predecessor proves every factor nonzero from its own literal rational reward witness, then uses the integral-domain product theorem; neither it nor62 asserts a common displayed witness for all factors.

The actual polynomial is still the product of all six unordered sure pairs times all four optional branch labels, with the predecessor's exact degree144. Density does not construct a different polynomial or ignore a factor. The same product's nonvanishing set is open dense, its zero locus has empty interior, and its rational nonvanishing points are dense.

`exists_rational_screenedRootCoordinates_mem_open` selects ONE rational free-coordinate vector inside the requested region, proves its polynomial evaluation nonzero, and only then quantifies over EVERY real own-singleton vector and EVERY screened PMF root. The bound-free singleton facade is stronger than the source's bounded use, not a restriction. `exists_rational_interior_screenedRootCoordinates_near` similarly selects ONE rational interior b′ before every s in the CLOSED unit singleton cube and every screened root. Its original b may lie on a closed cube face. The ignored singleton-bound proof is intentional: the stronger unrestricted-singleton exclusion already applies.

The canonical direct `quittingOwnSingletonReward` chart changes only the four own singleton entries; all56 free coordinates remain literally fixed. This is not a recipient-row translation. Never stays at the model's zero payoff. No singleton-dependent rational reselection is hidden in either theorem.

The concluding debts are `quittingTerminalDeviationDebt` of the actual `quittingOneDateThenNeverProfile`, not endpoint/root regrets substituted for complete regret. The existing screened-root exclusion delegates the semantic reduction to full behavioral screening: after any one player's replacement, a distinct original sure quitter still quits at zero. Thus every late finite date and Never is covered by the Continue endpoint; no reply menu is restricted. Optional probabilities0 and1 and roots with three/four sure quitters remain included by `IsScreenedQuittingRoot`.

There is no supplied source maximizer, minimum, positive eta, favorable root, polynomial nonzero certificate, or strategic witness in the source-facing density facades. The generic MathUE theorem's explicit nonzero polynomial input is appropriate and is discharged by the actual facade.

## Coverage and remaining work

This supplies the source's Section4.1 final density paragraph, dependency-audit P7, and the topological rational perturbation step used later in Section5.1. It does not supply TheoremA(3)'s compact strict gap, TheoremB's positive-eta source selection and maximizing singleton table, TheoremC's MAX-minimum total-singleton-law collar, or the common-calendar/harmonic consumers. Openness/density alone cannot prove eta>0 or manufacture a counterexample.

Still separate are the chart metric/cube adapters, compact fiber eta maximum, compact screened minimum, the all-player-tie strict-gap join, preservation of eta>0 under the chosen rational perturbation, and rational gamma selection. A source producer must output those objects; accepting them as final favorable fields would not close the source reduction. The maximizing singleton vector need not be rational. Existing SUM-debt cap collars do not replace the required MAX-minimum total-law collar.

Both new module paths were absent during this read-only inspection.61 can be checked independently;62 needs the complete old ten-patch chain, preserving its repairs. The handoff correctly leaves umbrella wiring and axiom inventory to root. The supplied harness lists all12 new declarations, but no harness output was produced. Specific unverified elaboration surfaces include finite-subtype inference for the56 variables, unfolding `Pi.map` and coordinate casts, set-comprehension/complement simplification, and import visibility of the listed tactics. Exact library signatures inspected here fit the intended uses; this is not a promise of warning-free compilation.

## Integrity

New packet:

- 61_MVPOLYNOMIAL_NONVANISHING.patch: `cfbf2df77abe2f17d8396178f63283dbe580bcffc1dd72b6ab71afc506ff4254`
- 62_SCREENED_ROOT_POLYNOMIAL_DENSITY.patch: `5ff786b574db33957988c2203e44a27517ea6d127c3e8c0ee5b93ff408493faa`
- AXIOM_HARNESS.lean: `012ce5cb1258ac37f19f4b00d296b1ffb610b775c5549f58bf81bdd91af7694c`
- HANDOFF.md: `e470d528865baf2ebc20cfc19fa61a5d62e157a07f7a63791abad71a54126cbb`
- Complete source export: `c3004d986acc316a20b7c29a7cdc9c764235f843e4b006a7fc99e0cbe0e0f5d7`
- Prior independent algebra review: `b421e3a9a9163e90d5d63e0cf5196ea0dd4975a881832a7c00a6de36228dbcb8`
- Dependency/theorem specs: `0f4412a92546f7036c1d850e96141275526cf18e9aa000bc48c1c079d8509a59`

All ten old prerequisites independently rehashed in recorded order:

```text
OWN_SINGLETON_REWARD_CHART.patch
6cf88b0275721e0e933301951eab49a015316f75a3717df01e6e0f2a25c4ee06
SCREENED_ROOT_DEBT_BRANCHES.patch
46d69174893acfbcea517076790e9408007249e030f0dbe2ad0db131ba937e2a
SCREENED_ROOT_BRANCH_LABELS.patch
ebaa9d7113b14e79bc3c12491f580a18c734ef76b9a68d8df21a1d28da25a7c2
SCREENED_ROOT_FOUR_CORNERS.patch
47813f600a0ff663cf7b9ddbb16f958d55cc589a60f7844ac351a2f50a2a5a5a
SCREENED_ROOT_FOUR_CORNERS_REPAIR.patch
bfdc3b0bc8706f0b3e3e56fcc7f3487af43a4d3e546b7ec8d6fa5c71abc3a22c
RECTANGULAR_COFACTOR_SEGRE.patch
b07ca5fb697d2c34992ad6d96c593fa1f3447c7cfcd16a5099ac41231bcf0c29
RECTANGULAR_COFACTOR_SEGRE_REPAIR.patch
fdecf5890b7892f339d0fb71f1285942b1fe7d98ec6e4c42cb1a543eb607904e
SCREENED_ROOT_POLYNOMIAL.patch
e3ddc227b55d3f48518ed5d60af28620026e95710bf31687e069dda4252e2440
SCREENED_POLYNOMIAL_DEGREES.patch
9572c041d806a5fbfa8c293f85ca7c5b188492e141eb229a0c3fb91df753af3b
SCREENED_POLYNOMIAL_WITNESSES.patch
dab5f8e14dc55cd8ef8d005a7d25948767b0060e773aac6542ecbc02b85acbdb
```

Final status: independent static PASS for61–62 only; no packet retirement or compilation seal.
