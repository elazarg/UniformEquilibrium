# Review of the weighted-debt affine barrier no-go

Reviewer: CODEX_SPINOZA

Reviewed artifact:
notes/CODEX_HAHN__WEIGHTED_DEBT_AFFINE_BARRIER_NOGO.md,
exact SHA-256
3635da07d9ca8fbd9d4163d4e84b3ba88461e42e1f14d2d53417d548876c1c57.

## Verdict

**PASS.** The top-state argument, deterministic toggle calculation, adjacent
coalition contradiction, finite-min extension, and full-box function-barrier
scope are correct.

## Reconstruction

At \(z^\top=(-R,R)\), every debt is \(2R\), so every probability-weighted
debt average equals \(2R\). Universal Bellman monotonicity at any
deterministic nonempty coalition root \(x^S\), together with the upper bound
\(2R\) on every output debt, forces every coordinate in the weight's support
to retain debt \(2R\).

Fix a supported coordinate \(i\) and another player \(j\). For
\(S=\{j\}\) and \(S=\{i,j\}\), both prescribed and \(i\)-toggled coalitions
are nonempty. The continuation is screened and the exact coordinate debt is

\[
 \bigl(r_i(S\mathbin\triangle\{i\})-r_i(S)\bigr)_+.
\]

Debt \(2R\) on the first edge forces
\(r_i(\{i,j\})=R\), \(r_i(\{j\})=-R\); debt \(2R\) on the reverse edge
forces the opposite assignments. This is the required contradiction.

For a finite minimum of weighted averages, all branches equal \(2R\) at the
top state. If the minimum after every pure root were at least \(2R\), every
branch would separately equal \(2R\); any branch and any positive coordinate
repeat the same contradiction. The proof therefore covers arbitrary finite
families without assuming a common support.

The grammar scope matches the checked dual: the function is required on the
full compact semantic box and the root quantifier ranges over all product
roots, not only exact Nash roots. The note correctly leaves open offsets,
separate payoff/cap coefficients, maxima, richer piecewise functions, and
carrier-restricted invariant sets.
