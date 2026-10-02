# Review of Section 69

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

## Claim checked

Section 69 claims that an arbitrarily accurate exact floor-admissible payoff
shadow of a closed strict-toggle payoff cycle automatically carries a fixed
aggregate exact-edge absorption denominator.  It further gives the analogous
constants for the reviewed deterministic strategy-update return and a
single-edge corollary under a uniform total-row bound.

I checked the edge estimate against
`abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass` in
`UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean` and checked the
consumer against the hypotheses restated in reviewed Proposition 26 of the
same note.

## Compensation and shadow error

The orientation is correct.  Around the closed static cycle the sum of all
coordinate increments is zero, while edge `t` gives its selected coordinate
an increment at least `gamma`.  The `L(n-1)` off-diagonal entries therefore
have total at most `-L gamma`, so one unchanged coordinate satisfies

```text
u_(t+1,i)-u_(t,i) <= -gamma/(n-1).
```

Each of the two shadowed endpoints contributes at most `epsilon`, and
`epsilon<=gamma/[4(n-1)]` therefore leaves a negative exact-state motion of
at least `gamma/[2(n-1)]`.  No stationarity or repeated label is used here.

## Raw and aggregate absorption

On each exact Bellman edge, the checked absolute motion estimate is applicable
because both tail and admissible-state payoff coordinates lie in the reward
box.  Telescoping absolute values along the selected connecting path gives

```text
gamma/[2(n-1)] <= 2M Raw(pi_t),
```

hence `Raw(Pi)>=gamma/[4M(n-1)]` with the stated orientation and constant.

For `q_k in [0,1]`, the product estimate is also exact.  If a `q_k` is one it
is immediate; otherwise

```text
1/product(1-q_k) >= product(1+q_k) >= 1+sum q_k.
```

Thus `Agg>=Raw/(1+Raw)`, which gives precisely

```text
gamma/[gamma+4M(n-1)].
```

The endpoint seam is at most `2 epsilon` because both endpoints shadow the
same returned payoff `u_0=u_L`.  If the concatenation has at most `H` rows,
averaging the raw sum gives the claimed single-edge threshold.  Positive raw
mass automatically excludes an empty concatenation.

## Corollaries

Corollary 69A matches Proposition 26: for a requested seam `eta`, choosing
`epsilon<=eta/2` and the fixed toggle threshold supplies endpoint error at
most `eta` and one accuracy-independent aggregate denominator.  The cited
consumer is against unrestricted behavioral deviations, so no bounded-policy
qualification is hidden.

For Corollary 69B, substituting the reviewed gain `g=3 gamma/4` into the same
calculation gives

```text
Raw >= 3 gamma/[16M(n-1)],
Agg >= 3 gamma/[3 gamma+16M(n-1)],
```

and, under a total connector bound `H`, an edge of absorption at least
`3 gamma/[16M(n-1)H]`.  The fact that the behavioral update return has bounded
length does not bound the number of exact Bellman rows in its connectors;
the note keeps this distinction explicit.

## Scope

The result is a conditional charge/denominator conversion only.  It produces
neither the floor-admissible states nor any exact path between successive
payoff nodes, and it does not produce a uniform row bound.  The remaining
producer is exact source-matched payoff-node connectivity; no charge premise
has merely been renamed.  No repair is required.
