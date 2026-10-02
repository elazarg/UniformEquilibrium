# Review of universal reset kernel and positive barrier topology no-go

Reviewer: CODEX_HAHN

Reviewed artifact:
`notes/CODEX_SPINOZA__UNIVERSAL_RESET_KERNEL_AND_POSITIVE_BARRIER_TOPOLOGY_NOGO.md`

Exact SHA256:
`a8b3847b42a6ebfc77b7b40cb61efe01a01c9cd072e3618566e81e8f12414dd1`

## Verdict

**PASS.**  The result is an exact obstruction to a bare invariant-set,
connectedness, or convexification proof.  It is not a positive-gap
certificate and the note does not present it as one.

## Checks

For a deterministic root with at least two quitters, changing one player's
action cannot expose the tail at that date.  Both prescribed payoff and all
unilateral cap branches are consequently tail-independent.  This validates
the constants `c_S`.  Closure of all finite-prefix images of these constants
is nonempty and compact, is stable under one more prefix, and belongs to every
nonempty closed set invariant under every product-root prefix.  Proposition
1.1 is therefore correctly oriented and proves leastness.

The convex-diagonal identity is also exact.  Each coordinate debt is
nonnegative, so a convex combination with zero debt in every coordinate can
use only constituents having zero debt in every coordinate.  In finite
dimension the corresponding finite convex-hull identity and its compact
closed-hull version follow.  The separate warning that full semantic prefix
maps are not affine is necessary and correct.

For the regression table `r_i(S)=-1` when `i in S` and zero otherwise, a word
terminating in a deterministic nonsingleton reset absorbs surely.  Never gives
each player zero and no unilateral strategy can exceed zero, hence `b_i=0`
and `d_i=Pr(i in K)`.  Thus total debt is the expected nonempty coalition
size and the maximum coordinate debt is at least `1/4`.  Closure does not lose
this bound: the semantic payoff vector determines the membership marginals,
whose sum stays at least one.  The sequential hazards `1/4,1/3,1/2,1`
indeed give the uniform singleton law and equality.  At that point Continue
strictly dominates Quit at cap zero, so all Continue is the unique exact root;
deleting player 0 gives the displayed `(0,1/3,1/3,1/3)` debt vector and gain
`1/4`.

The all-Never point of the same table is diagonal, so the example has global
minimum zero.  It therefore falsifies only the proposed topological shortcut,
not Fin4 UE.  The use of the exact universal-prefix hull floor and of the
checked fact that the all-Never universal-prefix hull is the full carrier is
consistent with the cited controller--tester and carrier results.

## Surviving contribution

Every nonempty closed set invariant under all quitting-root prefixes contains
one universal reset kernel, and that least kernel may have a strictly positive
debt floor even when the full carrier contains a diagonal point.  Adding the
mandatory all-Never base expands universal prefix saturation to the full
carrier.  Hence a successful positive barrier must use a signed or otherwise
passport-specific restriction on horizontal response transitions; minimal
invariant-set topology alone cannot supply it.

