# Independent falsification of Proposition 8

Reviewer: `CODEX_EULER`

Source reviewed:
[`CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`](../notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md), Section 11.

## Verdict

**PASS.**  The next exact floor row is uniformly charged, and the split into
third-label activation or a fixed upward old-owner rate increment is correct
with the displayed constants.  The statement also preserves the necessary
two-row/noniteration scope.

## Second charge

In the repayment arm, the first successor satisfies

```text
V_1(i)=Q_i <= s_i-eta,    eta=alpha*g_a/2>0.
```

The selected `q_1` is exact at the literal boxed punishment-floor tail
`V_1`.  The checked fixed-tail singleton-deficit theorem therefore applies
directly and gives

```text
A(q_1) >= eta/(eta+2M)=c_1.
```

This step needs endpoint Nash only, which is contained in the exact root
condition.  It does not identify the charge with one particular marginal.

The terminal-gap marginal cap applies at the same bounded floor tail and
gives every coordinate

```text
q_1(h)(Quit) <= 1-d,    d=Gamma/(4M).
```

The original gate has `0<p<=1-d`, so `M>0` and `0<d<1`.  In particular
player `i` has positive Continue probability.  Its exact support inequality
therefore has the required orientation: Quit-minus-Continue is nonpositive.

## Endpoint comparison and coupling

Let `x=q_1(k)(Quit)` and force the two labels outside `{k,i}` to Continue.
At tail coordinate `V_1(i)=Q_i`, the resulting endpoint difference is exactly

```text
F(x)=(1-x)(s_i-Q_i)+x(b-R_i).
```

Indeed, with `k` continuing the Quit/Continue endpoints are `s_i,Q_i`, and
with `k` quitting they are `b,R_i`.  A player's own marginal does not enter
this forced-action comparison.

For the actual root, the endpoint difference is at most zero.  The endpoint-
difference integrand over the three opponents lies in `[-2M,2M]`.  Coupling
each of the two third-player Bernoulli laws to Continue changes the opponent
profile with probability at most

```text
H=sum_(j notin {k,i}) q_1(j)(Quit).
```

The expectation difference is consequently at most `4M H`, which gives the
one-sided inequality `F(x)<=4M H`.  No independence or total-variation
factor is missing.

## Two sign arms and constants

Write `c=b-R_i`.

If `c>=0`, then `x<=1-d` and `s_i-Q_i>=eta` imply

```text
F(x)>=d*eta.
```

Thus `H>=d*eta/(4M)`.  Literal `Fin 4` leaves exactly two labels outside
`{k,i}`, so one has marginal at least

```text
d*eta/(8M)=d*alpha*g_a/(16M)=rho.
```

If `c<0`, direct substitution gives

```text
F(p)=p(Q_i-R_i)=p*g>=alpha*g_a.
```

When `H>=alpha*g_a/(8M)`, the same two-label pigeonhole gives a marginal at
least `alpha*g_a/(16M)>=rho`, since `d<1`.  Otherwise
`F(x)<F(p)/2`.  Here

```text
F'(x)=c-(s_i-Q_i)<0,
|F'(x)|=(s_i-Q_i)-c<=4M.
```

Hence `x>p`, and the mean-value identity for this affine function gives

```text
4M(x-p) >= F(p)-F(x) > F(p)/2 >= alpha*g_a/2,
```

which is the claimed increment `x-p>=alpha*g_a/(8M)` (indeed the proof gives
a strict inequality before weakening it).

## Exact scope

The result is a literal statement about the first two rows of an anchored
exact punishment-floor orbit.  It proves a second fixed charge and either
fixed third-label support or a fixed old-owner rate displacement.  It does
not show that the third-label marginal is collision mass, that the owner
increment can be iterated, that the new row has terminal-semantic carrier
provenance, or that the other payoff coordinates return.  Those limitations
are stated accurately.

