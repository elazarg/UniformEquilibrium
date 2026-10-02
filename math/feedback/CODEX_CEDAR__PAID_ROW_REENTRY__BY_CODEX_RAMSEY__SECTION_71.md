# Review of Proposition 71 and Corollaries 71A--71B

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

For a nonempty persistent base, the two antipodal `i` comparisons have the
claimed signs.  Mixing the other free label with any probability strictly
between zero and one makes both of `i`'s date-zero actions strict convex
combinations with one endpoint below `P_i`; both values are therefore below
`P_i`.  Since the base quits surely, there is no continuation or arbitrary-
timing issue, and the maximum of those two values is the unrestricted cap,
contradicting the punishment lower bound.

For the empty base, the final selected leave gives `P_j=0>r_j(j)`, while the
other `j` edge gives `r_{i,j}(j)=P_j>r_i(j)`.  Against a stationary positive
hazard of `i`, quitting by `j` has value
`(1-x)r_j(j)+x r_{i,j}(j)<0`; Never has value `r_i(j)<0` because `i` quits
almost surely.  Stationarity makes every finite behavioral timing choice a
repeat of the same Quit/Continue Bellman comparison, so the unrestricted cap
is the maximum of these two negative values.  This is the required strict
contradiction; no bounded-controller restriction is hidden.

The length conclusions are also exact.  Hypercube cycles have even length,
two edges would immediately reverse one strict toggle, and Proposition 71
excludes four.  Hence a tight simple cycle has length at least six, which
removes the two-player arm because the two-dimensional cube has no longer
simple cycle.

For a length-six simple word, adjacent equal labels are forbidden and every
label has even multiplicity.  A `4+2` distribution forces two of the four
occurrences to be adjacent, so the word uses three labels twice.  Unless all
three pairs are antipodal, one obtains a subword `i,j,i`.  The two `i` edges
already give the nonempty-base contradiction.  At empty base, the only local
orientation not contradicted directly is
`empty -> {i} -> {i,j} -> {j}`.  The remaining word is necessarily `k,j,k`
and yields `{j}->{j,k}->{k}->empty`, whose two `k` comparisons are the
opposite, forbidden empty-base orientation.  Thus the surviving label word
is exactly `i,j,k,i,j,k` up to rotation and relabeling.

The scope is accurate: this classifies a static edgewise punishment-tight
orbit and neither constructs exact floor connectors nor identifies the six
coalition vertices beyond their toggle word.
