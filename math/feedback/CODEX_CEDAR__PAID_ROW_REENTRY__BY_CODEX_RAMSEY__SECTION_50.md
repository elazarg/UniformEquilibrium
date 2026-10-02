# Review of CODEX_CEDAR Section 50 by CODEX_RAMSEY

Claim reviewed: in the floor-safe uniform-singleton-gap arm, one exact
fixed-tail endpoint root has uniformly positive absorption, while the
terminal exploitability gap supplies a uniform upper bound below one on
every marginal of every such exact root.  Hence the selected root has
uniform joint and player-deleted Continue floors and at least one genuinely
interior active marginal.

Verdict: **valid in the stated first-edge scope**.

The named quantitative theorem
`gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash` applies to
every exact endpoint-Nash root at the fixed tail `U` and gives

```text
delta/(delta+2M) <= 1-prod_i(1-q_i).
```

The qualitative existence theorem supplies at least one such simplex root.
The terminal-gap marginal ceiling from Proposition 49 applies to that same
boxed tail and root, so `q_i<=rho<1` for every `i`.  Multiplication gives the
claimed lower bounds

```text
prod_i(1-q_i)       >= (1-rho)^n,
prod_(j!=i)(1-q_j) >= (1-rho)^(n-1).
```

The distinguished singleton-gap player makes the player set nonempty.  The
union bound

```text
absorption(q) <= sum_i q_i
```

therefore gives some `k` with `q_k>=c/n`; Proposition 49 gives `q_k<=rho`.
In particular `0<q_k<1`, so both support inequalities bind.  Writing the
forced-Continue payoff as `K_k(q)+O_k(q)U_k`, exact indifference gives

```text
U_k=(Q_k(q)-K_k(q))/O_k(q),
O_k(q)>=(1-rho)^(n-1)>0.
```

No conditional independence or strategy-class restriction is hidden here;
these are literal product-root factors and exact endpoint-Nash support
conditions.

Scope qualification: the result constructs one incoming exact charged edge
at a supplied boxed tail in the singleton-gap arm.  The one-row Continue
floors are not by themselves persistent survival along an infinite
chronology.  The proposition does not supply the negative payoff transfer,
source-matched continuation, or near-return path needed by the paid
consumer.  Subject to reading “persistent” in the local one-row sense, no
repair is required.
