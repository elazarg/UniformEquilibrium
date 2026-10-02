# Review of pure-clock affine-translation localization

Identity: `CODEX_DESCENDANT`

Verdict: **PASS as a conditional strict refinement; not a consumer.**

## Claim checked

For two deterministic pure-clock profiles differing only in player (p)'s
clock, if (p) Continues at date zero at both endpoints, then every spectator
(j\ne p) has the common response anchor `QuitAt 0`.  Hence a spectator cap
displacement of magnitude at least (c) yields, on one of the two literal
endpoints, a pure-response contrast of gain at least (c/2) whose first
disagreement is date zero.

## Mathematical audit

The stopping-law value calculation is exact.  Under `QuitAt 0` by (j), the
terminal coalition consists of (j) and exactly the fixed opponents other
than (p) whose clocks equal zero.  Since (p) Continues at zero on both
sides, its later clock is irrelevant and the two anchor values agree.

Cap attainment is valid for deterministic opponents.  If some opponent has
earliest finite deadline (m), a pure response has only the values obtained
before (m), tied at (m), or after (m); if every opponent is Never, the
only values are the singleton value and Never.  Thus the maximizing response
(q) used in Theorem 4.1 exists without a compactness or continuity claim.

After orienting so that (B_j(Y)-B_j(P)\ge c), a maximizer (q) at (Y)
satisfies

\[
 V_j^Y(q)-V_j^P(q)\ge B_j(Y)-B_j(P)\ge c.
\]

Subtracting the common `QuitAt 0` anchor gives the displayed gap difference.
The elementary split is sharp: either the (Y)-gap is at least (c/2), or
the reverse (P)-gap is strictly greater than (c/2).  The selected (q)
cannot itself be `QuitAt 0`, and therefore the first disagreement is exactly
zero.  Its opponent-reach factor is the empty-prefix product, hence one.

The charged-root substitution is also correct: inserting
(c=\alpha D_*/6) gives the retained row gain
(\alpha D_*/12).  This is a row on one of the same two actual pure-clock
endpoints; no unrelated carrier realizer or response attainment is used.

The boundary regression is valid.  When (p) changes from Never to
`QuitAt 0` and (j)'s reward is the indicator that (p) belongs to the
terminal coalition, every (j)-response value translates from zero to one.
Thus the common-anchor hypothesis really is necessary for this argument.

## Scope and novelty

This strictly removes the pure affine-translation and escaping-response
loopholes **only after** the generic charged cap-displacement endpoints have
been identified with deterministic pure-clock profiles and the mover keeps
the same Continue action at date zero.  It does not supply that adapter from
an arbitrary purified off-minimum port.  Its output remains a horizontal
paid row, not an exact cap--Nash root or an extension-compatible
Nash--Bellman edge.  Consequently it narrows the selected pure-clock charged
residual but consumes neither that residual nor the quantitative/inert
paid-cap branches.

No mathematical correction is required.
