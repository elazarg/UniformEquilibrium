# Independent review of Theorem 31.1 and Corollary 31.2

Reviewer: CODEX_RAMSEY

## Claim reviewed

I checked the constrained-stationary construction in Theorem 31.1: from a
finite quitting game in which every player is punishment-normal and which has
a fixed positive terminal exploitability gap `g`, construct a full-support
`QuittingNormalizedSingletonSourcePacket`.  I also checked the claimed
support-cardinality decrease in Corollary 31.2.

## Verdict

**PASS, with one small presentation repair.**  The mathematical argument is
valid.  Before export, Step 2 should explicitly choose a null sequence, for
example `epsilon_k=1/(k+2)`, select one constrained Nash root for each `k`, and
then pass to a subsequence of the normalized rates.  The current prose moves
from a fixed `epsilon` to a convergent subsequence without naming this
sequence.  This is not a substantive gap, but the export statement should
make the quantifiers literal.  Also the final sentence of Step 3 should cite
`(31.10)`, not `(31.11)`, for full support.

## Detailed falsification audit

### Constrained game and unrestricted deviations

With every opponent rate at least `epsilon>0`, the opponent absorption
probability `delta_i` is positive and the displayed stationary payoff is

```text
[p Q_i+(1-p)A_i]/[delta_i+p beta_i].
```

Its derivative has constant sign: after multiplying by the positive square
of the denominator, the sign is that of `Q_i-delta_i^{-1}A_i=Q_i-N_i`.
Consequently the best-reply values on `[epsilon,1]` are compact convex faces,
and the closed-graph Kakutani step is sound.

The unrestricted-behavior claim also checks.  Against stationary opponents,
the exact behavioral cap is `max(Q_i,N_i)`.  Thus an interior constrained
rate (`Q_i=N_i`) and the upper rate (`Q_i>=N_i`) have zero unrestricted
regret.  At the lower rate, `Q_i<=N_i`, and direct subtraction gives exactly

```text
N_i-V_i = epsilon*(N_i-Q_i)/(delta_i+epsilon beta_i).
```

This includes Never and every history-dependent unilateral stopping rule;
it is not merely a stationary-deviation calculation.

### Hazard purification and constants

The terminal gap therefore selects a lower-bound player.  Since both endpoint
values lie in `[-M,M]`,

```text
delta_i+epsilon beta_i <= 2M epsilon/g.
```

For every opponent `j`, `q_j<=delta_i`; all coordinates also satisfy
`q_j>=epsilon`.  Hence

```text
H_epsilon<=epsilon+[2M(n-1)/g]epsilon=C epsilon,
q_j/H_epsilon>=1/C.
```

The argument itself shows `M>0` in the inhabited terminal-gap branch.  No
division by a possibly zero constant is hidden.

### First-order singleton limit

The common upper bound makes every rate tend to zero, so the upper face is
eventually impossible and `delta_i Q_i<=A_i` for every player.  After division
by `H_epsilon`, the singleton terms give

```text
delta_i/H -> sum_(j!=i) mu_j,
A_i/H     -> sum_(j!=i) mu_j r_{ {j} }(i),
Q_i       -> r_{ {i} }(i).
```

Every coalition containing at least two opponent quitters has product-law
probability `O(H^2)`; finiteness makes the remainder uniform.  The limiting
inequality is therefore exact.  Adding the diagonal term yields

```text
sum_j mu_j r_{ {j} }(i) >= r_{ {i} }(i).
```

Together with punishment normality, `v_i=r_{ {i} }(i)`, mass normalization,
and `mu_i>=1/C`, these are precisely all fields of
`QuittingNormalizedSingletonSourcePacket`.  The probability mode remains an
ordinary independent product root; no correlated device is introduced.

### Corollary and strict decrease

In the crossed four-player support-two chamber, packet support makes both
owners normal, while the two strict crossed-harm inequalities and
`abnormal_singletonFloor_chain` make both outsiders normal.  Thus Theorem
31.1 applies in the no-uniform-payoff branch and produces support cardinality
four.  The integer `4-card(support)` strictly decreases from `2` to `0`; the
claim does not recurse at full support and honestly transfers the residual to
the separately maintained full-support obligation.

## Boundary and scope

Equality in `Q_i=N_i` is harmless: the whole constrained interval is a best
reply and the unrestricted cap equals the prescribed value.  Upper endpoints
are eventually excluded by the quantitative rate bound, not by a genericity
assumption.  The theorem does not solve the resulting full-support packet,
support three, or the quitting-game conjecture.  Its exact new content is a
finite support-complexity reduction under the terminal-witness and all-normal
hypotheses.
