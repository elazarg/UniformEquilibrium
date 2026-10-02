# Independent review of the two-pair entrance used in the auxiliary selector

Reviewer: CODEX_NOETHER_SUPPORT.
Source: [two-pair manuscript](../gpt/TWO_PAIR_PAYOFF_EXCLUSION_AND_GEOMETRIC_FINITE_MENU_SELECTION.md).

Scope: Sections 1–3 and the qualitative reward-table entrance, including
Never and the κ=3/8 specialization. The separate joining-gain finite-menu
construction later in the manuscript is not covered by this review verdict.
The reviewed entrance passes; no unresolved objection was found. Ordinary
mathematics and source inspection only, not Lean compilation.

For four independent complete clocks, pair (T₀,T₂) supplies the probabilities
of its two strict orders and joint Never. Pair (T₁,T₃) supplies the same
three probabilities independently. Each triple sums to at most one, because
finite ties are omitted. Target {0,1} implies both forward comparisons;
target {2,3} implies both reverse comparisons; all-Never is the intersection
of the two joint-Never events. Cauchy–Schwarz therefore proves

    √x+√y+√ν≤1,   1−x−y−ν≥2(√xy+√xν+√yν).

This proof includes arbitrary support and Never. The sharp two-date family
in the manuscript gives equality directly, so the inequality is not being
used as a generic property of correlated coalition lotteries.

Under the thirty displayed raw row inequalities, write z=1−x−y−ν.
The group surplus is bounded by ax−by−Lz minus its nonnegative
singleton-sum Never term. If x≤y this is at most
(a−b−2L)x−b(y−x)≤0. The other case uses the other group. Thus the
payoff-only exclusion is valid on all actual profiles and their payoff
limits. At a global positive semantic debt minimum, each group surplus is
at least D−(its pair debt)/2≥D/2>0. This contradicts the exclusion
without reconstructing or changing caps.

For the canonical stricter row bounds, let p=√x, q=√y, t=√ν. The two
surplus bounds are

    2p²+q²/4+t²/2−1,
    p²/4+2q²+t²−1,

with p+q+t≤1. For p≤1/2 the first is at most
2p²+(1−p)²/2−1≤−3/8. For p≥1/2 the second is at most
p²/4+2(1−p)²−1≤−7/16. Convexity on each displayed interval reduces
the final bound to its two endpoints. Therefore the claimed uniform
coordinate deficit κ=3/8 follows.

I inspected `twoDisjointFirstStoppingPairMasses_sqrt_sum_le_one` and
`sqrt_exactFiniteFirstStoppingPairMass_add_sqrt_le_one`
(`MathUE/Probability/IndependentFirstStoppingPair.lean`), and
`minimumTerminalSemantic_singletonMargin`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`).
The existing terminal-all-errors consumer is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).

The source's qualitative entrance is credited in the
[consolidated proposal](../notes/CODEX_NOETHER_SUPPORT__PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md).
There, the later auxiliary-cap algorithm replaces the joining-gain
finite-menu recursion and supplies total unrestricted debt control over
the full non-strict class. That quantitative construction must retain its
separate credit and proof; the present review does not enlarge the older
finite-menu theorem's own stated hypotheses.
