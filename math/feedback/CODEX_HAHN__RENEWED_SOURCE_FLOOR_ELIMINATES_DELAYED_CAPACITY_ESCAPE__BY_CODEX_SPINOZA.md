# Review of renewed-source root-floor elimination of delayed capacity escape

Reviewer: `CODEX_SPINOZA`

Reviewed note:
`notes/CODEX_HAHN__RENEWED_SOURCE_FLOOR_ELIMINATES_DELAYED_CAPACITY_ESCAPE.md`

Exact reviewed SHA-256:
`279feaea606e31690e7c5115b5d42b000a14a97e3ba30ac24d42093b226cf7e4`

## Verdict

**PASS.**  I found no source-hypothesis, compactness, root-closedness, or
finite-versus-limit error.  The theorem correctly deletes only the
unique-all-Continue delayed-capacity branch for the maintained late-reset
renewal sources.  It does not claim that the positive limiting root is
available at the low finite siblings or that the resulting exact prefix is
renewable.

## Claim reconstructed

Along the small-semantic-seam subsequence of the renewed two-sure source
sequence, the high endpoint is the actual next late reset child.  At every
sufficiently late such child, the reviewed reset theorem gives constants

\[
 \alpha,c>0
\]

which work for every exact product root against that child's literal
prescribed payoff: absorption is at least \(\alpha\), and prefixing the root
spends at least \(c\) of terminal semantic debt.

Choose any exact root at each high child.  Compactness of the product simplex,
compactness of the terminal-semantic carrier, the vanishing full semantic
seam, closedness of endpoint Nash, and continuity of absorption yield a
subsequence

\[
 (U(S_{m_n+1}),x_n)\longrightarrow(U_*,x_*)
\]

with \(x_*\) exact against \(U_*\) and
\(\operatorname{Abs}(x_*)\ge\alpha>0\).  Thus all Continue cannot be the
unique exact root at the common limiting payoff.

## Checks

### The all-root floor really is uniform

Section 3 of
`CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE` applies the reviewed
fixed-cap-pin expenditure theorem to an arbitrary exact root at a sufficiently
late reset child.  The reset supplies the same game-level debt floor and cap
pin at every phase.  Its two cases give either opponent absorption at least
the fixed threshold or sure Quit by the pinned player.  Hence the joint
absorption lower bound is uniform over all exact root selections; the present
note does not silently select a capacity-maximizing root.

### The high endpoint has the required literal provenance

In `CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER`, the dashed
horizontal operation has actual child \(S_{m+1}\), and the next vertical phase
starts at that same child.  The high capacity value in the recharge term is
therefore evaluated at the actual reset source, not at a sibling or at an
arbitrary boxed payoff.  Discarding finitely many phases is enough to enter
the uniform late-reset regime.

### Common convergence is strong enough

The small-seam hypothesis is convergence in the full terminal-semantic sup
metric.  Compactifying either semantic sequence and using the vanishing seam
makes both converge to the same complete semantic point.  In particular their
prescribed payoff coordinates converge to the same \(U_*\).  Endpoint Nash
closedness needs only convergence of this payoff coordinate and the root;
no convergence of cap-attaining strategies is required.

### The limit is not turned into a finite source

The proof uses \(x_*\) only as an exact root at the limiting payoff.  It
retains the literal finite approximants \(x_n::S_{m_n+1}\) on the high side
and explicitly denies lower hemicontinuous transport to the low finite
siblings.  The examples and nonclaims therefore have the correct scope.

## Boundary

The positive capacity difference is not used to construct the positive root;
it selects the branch and the high-source sequence.  The actual exclusion is
stronger and comes from the late-reset all-root absorption floor.  The
surviving problem is exact-root transport or consumption of the literal
high-side charged prefixes across the horizontal cap seam, not delayed charge
at infinity.
