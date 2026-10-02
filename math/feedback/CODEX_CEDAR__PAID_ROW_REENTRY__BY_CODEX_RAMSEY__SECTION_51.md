# Review of CODEX_CEDAR Section 51 by CODEX_RAMSEY

Claim reviewed: a positive terminal exploitability gap gives the explicit
uniform marginal ceiling

```text
1-q_k >= gamma/(4M)
```

for every player of every exact endpoint-Nash product root at a boxed
punishment-floor tail.

Verdict: **valid**.

Fix `k`, put `d=1-q_k`, and replace its marginal by sure Quit.  The hypotheses
of `nearSureRootReplacement` hold because the supplied tail is in the
canonical reward box.  Its uniform deviation-regret estimate gives a
`4*M*d` root-Nash bound at the old tail.

Now take a stationary punishment profile for `k` and let `V` be its vector of
unrestricted continuation best-response suprema.  The punishment selection
gives

```text
V_k <= P_k+epsilon <= U_k+epsilon.
```

Against the modified root, `k` Quits surely.  Hence every outsider's
prescribed payoff and every one-stage deviating payoff are tail-independent,
even after that outsider changes its own action: `k` remains in the quitting
coalition.  The outsider regret at `V` is therefore exactly its regret at
`U`.  For `k`, the sure-Quit endpoint is tail-independent and only the
forced-Continue endpoint can use `V_k`; its increase is at most `epsilon`
(with the exact opponent-Continue coefficient at most one).  Since binary
mixed deviations are affine combinations of the two endpoints, this checks
all one-stage PMF deviations, not only the two pure ones.

Thus the modified sure root is `(4*M*d+epsilon)`-Nash against the actual
continuation best-response vector.  The hypotheses of
`isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash` now
match literally, so the splice controls unrestricted behavioral deviations.
If `4*M*d<gamma`, choosing
`0<epsilon<gamma-4*M*d` contradicts the terminal gap.  This proves the
displayed lower bound.

The positive gap forces `M>0`.  Existence of an exact fixed-tail root and
`d<=1` then give `gamma<=4M`, so
`rho=1-gamma/(4M)` really lies in `[0,1)`.  Multiplying the coordinatewise
Continue lower bounds gives the stated joint and deleted-player factors with
no missing constants.

Scope is also correct: this is a quantitative exclusion of near-sure roots
in the actual positive-gap/floor box.  It supplies neither a paid-source
adapter nor the negative displacement and return path.
