# Review of fixed cap-pin approximate-root debt expenditure

Reviewer: `CODEX_SPINOZA`

Reviewed candidate:
`/tmp/FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md`

Reviewed SHA-256:
`6e89d61d836839fb3fa292ebd750a0757c0f59c6fda1d88b9f06e95956eee6d0`

## Verdict

**PASS.**  The candidate faithfully contains the two already reviewed core
theorems.  Its new interleaved arbitrary-re-entry ledger is correct: it
measures exactly the positive replenishment of the named debt, telescopes
without assuming anything about the re-entry operation, and is bounded by
the displayed two-coordinate semantic seam.  I found no mathematical,
source, strategy-class, link, control-byte, or export-format objection.

## New re-entry claim reconstructed

For each actual source pair `S_k`, prefix an `ε_k`-Nash product root and call
the literal child `P_k`.  Let the next actual source `S_{k+1}` be produced by
an arbitrary operation and define

\[
 \kappa_k=[d_b(S_{k+1})-d_b(P_k)]_+.
\]

This definition alone gives

\[
 d_b(S_{k+1})\le d_b(P_k)+\kappa_k.
\]

At a visit to the fixed chamber, the reviewed approximate theorem gives
`d_b(P_k)≤d_b(S_k)-δ_b+ε_k`; away from the chamber, its general arbitrary-
root inequality gives `d_b(P_k)≤d_b(S_k)+ε_k`.  Therefore

\[
 d_b(S_{k+1})\le d_b(S_k)
 -\mathbf 1_{\{k\in V\}}\delta_b+\varepsilon_k+\kappa_k.
\]

Telescoping and using final debt nonnegativity proves exactly

\[
 |V\cap\{0,\ldots,N-1\}|\delta_b
 \le d_b(S_0)+\sum_{k<N}(\varepsilon_k+\kappa_k).
\]

No ancestry, continuity, Nash, or law-preservation property of the arbitrary
re-entry step is used or claimed.

## Seam estimate

Writing a semantic pair as `(prescribed,cap)`, one has identically

\[
 d_b(S_{k+1})-d_b(P_k)
 =(S_{k+1}.2_b-P_k.2_b)-(S_{k+1}.1_b-P_k.1_b).
\]

Taking positive part and applying the triangle inequality gives

\[
 \kappa_k\le
 |S_{k+1}.1_b-P_k.1_b|+|S_{k+1}.2_b-P_k.2_b|=\eta_k.
\]

This is precisely the existing coordinate debt-Lipschitz estimate specialized
to the re-entry pair.  It is a bound by the full two-coordinate seam, not by
only a payoff error or only a cap error.  If both the root-error sum and seam
sum are finite, infinitely many chamber visits contradict the finite-prefix
inequality.  Conversely, infinite chamber recurrence forces at least one of
these two nonnegative series to diverge.

## Core theorem and semantic scope

I rechecked that the candidate retains the exact arbitrary-prefix identity

\[
 d'_b=\max\{e,sd\}-q_be,
\]

the three `ε`-Nash sign cases yielding `d'_b≤sd+ε`, and the cap-pin split
giving the fixed drop `δ_b-ε`.  The complete old-tail cap, rather than a
stationary or finite-clock substitute, is used in the Continue endpoint.
Thus all behavioral deviations, including Never and arbitrarily late clocks,
remain covered.  Only the newly prefixed current action is an independent
product row.

The reward bound controls every actual prescribed payoff and cap, so
`d_b(S_0)≤2M` is valid.  The staged tropical adapter cites the byte-frozen
export at its actual SHA and correctly converts its fixed Quit0 cap gain and
cluster cap identity into the debt floor and scalar cap-pin convergence.

## Gate checks and nonclaims

All four review links, both source-note links, the tropical export link, and
the live question link resolve from the intended `exports/` location.  The
candidate contains each mandatory export heading, has no control bytes, and
passes `../scripts/check_docs.py`.  Its nonclaims are exact: it neither bounds
`κ_k` for arbitrary horizontal reconstruction nor converts a nonsummable seam
into playable absorption, and it does not claim a global rank, a terminal
equilibrium, or a uniform-equilibrium payoff.

