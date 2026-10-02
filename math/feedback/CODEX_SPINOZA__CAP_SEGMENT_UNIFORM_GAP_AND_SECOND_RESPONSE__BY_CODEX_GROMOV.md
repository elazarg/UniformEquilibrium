# Review of near-full finite-cap installation

Reviewer: `CODEX_GROMOV`

Reviewed artifact:
`notes/CODEX_SPINOZA__CAP_SEGMENT_UNIFORM_GAP_AND_SECOND_RESPONSE.md`,
SHA-256
`aa6fa955e0ba9cf1a5e17683284e1d3732531ddef0631e063a11bd7f4c140fb7`.

## Verdict

**PASS.**  I found no mathematical error or scope inflation.

## Checks

The cap-segment identity is exact.  Only player `k`'s stopping law is mixed,
so its opponents and hence its unrestricted cap are fixed.  Affinity of its
payoff in its own private stopping-law mixture gives

\[
d_k(\sigma^t)=(1-t)d_k(\sigma).
\]

At the cap endpoint this debt is zero.  Therefore a response with gain at
least the game-level gap must belong to a distinct player.

The coupling estimate is also correct.  The source mixture and the full cap
endpoint can be coupled to agree in the cap branch of mass `t`.  For either
the prescribed profile or one fixed response of the second player, payoff
changes by at most `2M(1-t)`.  Subtracting the two comparisons costs at most
`4M(1-t)`, exactly as stated.

The constant choice is valid.  The terminal payoff range gives
`Gamma <= 2M`, hence

\[
0<\varepsilon_0=\Gamma/(8M)\le 1/4.
\]

At `t=1-epsilon_0`, the old cap response gains at least
`Gamma^2/(8M)` and the second response gains at least `Gamma/2`.

The finite-clock refinement uses the correct opponent argument.  At the full
cap endpoint, the distinct sure quitters `b` and `k` imply that after deleting
any one player at least one sure finite opponent remains.  Thus every
unrestricted cap is attained by a finite pure time no later than the common
bound, or by the single `Never` representative for all later responses.  At
the intermediate mixture, only the more limited claim for `j != b` is made;
the note correctly avoids claiming cap attainment there when `j=b`.

## Scope

The output is a co-sourced pair of profitable complete responses and, in the
finite-cap case, a literal two-step horizontal response chain.  It does not
make either response an exact Nash--Bellman predecessor, preserve the first
debt after the second update, or establish a temporal return.  The note states
these limitations explicitly.

## Delta review

The author subsequently added only source-audit context and froze SHA-256
`42c6c5461c11520961e4842c76cf4c6af67e3df1f89c0fdc032b3070aefb26b0`.
The addition identifies the older half-reset calculation and distinguishes
the present attained-cap specialization and near-endpoint response transport.
It changes no hypothesis, proof, constant, conclusion, or nonclaim.
**PASS unchanged.**
