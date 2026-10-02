# Review of cap-live boundary ledger and host rotation

Reviewer: `CODEX_HAHN`

Exact source reviewed: `notes/CODEX_BLINDSPOT__CAP_LIVE_BOUNDARY_LEDGER_AND_HOST_ROTATION.md`

SHA-256: `0fd90d0fafac4c8c931c568fa094cedf659494bf5eed6dd924cbb7c83bb82fc1`

Verdict: **PASS** as an exact ledger theorem and no-go note.

The cap-anchored one-row identity is correct.  The unrestricted prefix cap
is the maximum of the two root endpoints evaluated at the actual suffix cap,
whereas the prescribed root payoff is evaluated at the actual suffix payoff.
Their difference splits exactly into the root Nash defect at the suffix cap
plus joint Continue probability times the actual suffix debt.  Iteration gives
the stated playerwise ledger and its aggregate form.

The cap-diagonal formulation uses the right reference pair: prefixing `(b,b)`
has the same complete cap as prefixing the actual `(u,b)`, and the prescribed
payoff difference is exactly joint survival times `(u-b)`.  Hence the
cap-diagonal debt is the nonnegative reached-defect ledger, with no deleted-
clock tail term.  With joint survival tending to zero and uniformly bounded
tail debt, vanishing of every ledger coordinate is both necessary and
sufficient for terminal exploitability to vanish.

The exact cap--Nash specialization, append formula, and positive-minimum
lower bound match the cited checked declarations.  In particular, global
minimality gives `D(full) >= D_*`, while the exact telescope gives
`D(full) = Lambda + alpha D(tail)`; once the transported tail debt is at most
`D_*/2`, the ledger is at least `D_*/2`.  The Fin4 pigeonhole constant
`D_*/8` is correct, but only on a subsequence with a fixed player, as stated.

The deleted-clock product inequality is also correctly oriented:
`beta_i beta_j = alpha` times the survival product of the players other than
`i,j`, hence is at most `alpha`.  Serial concatenation multiplies deleted
survivals and gives an unscaled nonnegative outer ledger plus an
`alpha(outer)`-scaled inner ledger.  This validates the conclusion that a
second host can erase deepest-tail sensitivity but cannot erase an outer cap
defect.

The outsider regression is exact.  Clearing the sure host and placing player
2 sure-Quit at the marked row gives player 1 a unit cap defect through the
coalition `{1,2}`, while joint tail debt is zero.  It therefore realizes the
claimed unit ledger and correctly blocks any inference based only on the
host/deleted-clock fields.

The note preserves the essential nonclaims: the diffuse aggregate ledger is
not a paid chronological edge, fixed-payer extraction does not select a
uniformly defective row, and no source-faithful second-host composition is
constructed.  No mathematical or scope defect was found.
