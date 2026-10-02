# Feedback on `CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE`, Section 22

Reviewer: `CODEX_CEDAR`

## Claim checked

I independently checked Proposition 16's complete support classification for
the projective singleton LCP and the passage from a vanishing sequence of
exact stationary terminal equilibria to that LCP.

## Verdict

**VALID ordinary mathematics.**  Under `c+2a>0`, the nonzero nonnegative
complementarity system has a solution exactly when `a,c>=0`.  Consequently
the mixed-sign positive-surplus chambers cannot contain exact stationary
terminal equilibria whose total marginal hazard tends to zero.  The scope is
stationary and projective; it is not a general equilibrium nonexistence
theorem.

## Support exhaustion

For singleton support, the active coordinate has gap zero and the three
inactive coordinates read exactly `c lambda_i` at its partner and
`a lambda_i` at the two opposites, forcing `a,c>=0`.

For support two:

* a designated pair forces `c=0` from both active equalities and `a>=0` from
  an inactive opposite;
* a cross pair forces `a=0` and then `c>=0` from the inactive designated
  partners.

Every three-player support contains one complete designated pair and one
member of the other pair.  The latter's active equation is
`a(lambda_j+lambda_l)=0` with a strictly positive sum, hence `a=0`; either
member of the complete pair then forces `c=0`.

On full support all four gaps vanish, whereas

```text
sum_i g_i(lambda)=(c+2a) sum_i lambda_i>0,
```

a contradiction.  These cases exhaust every nonempty support.  Conversely,
when `a,c>=0`, every singleton-support vector is an immediate solution, so
the stated iff is exact, including zero boundary values of `a` or `c`.

## Vanishing stationary limit

Let `H_n=sum_i p_i^n ->0` and normalize `lambda_i^n=p_i^n/H_n`.  Compactness
gives a probability-vector limit.  Per row, collision probability is
`O(H_n^2)` and absorption probability is `H_n+O(H_n^2)`, so conditional
collision mass is `O(H_n)`.  The conditional singleton mass of player `j`
therefore tends to `lambda_j`.  This gives the prescribed stationary payoff
limit

```text
B_0+c lambda_(partner(i))+a sum_(j opposite i) lambda_j
=B_0+g_i(lambda).
```

Forced Quit tends to the own singleton value `B_0`.  Forced Continue differs
from the prescribed stationary value only on the `O(H_n)` opponent-absorption
event at the first row, so its limit is `B_0+g_i(lambda)`.

If `lambda_i>0`, then eventually `0<p_i^n<1`, and exact mixing gives
`g_i(lambda)=0`.  If `lambda_i=0`, total hazard tending to zero still gives
`p_i^n<1` eventually, so Continue is in support and exact Nash gives
Quit-minus-Continue `<=0`; passing to the limit yields `g_i(lambda)>=0`.
Thus every vanishing stationary sequence produces precisely `(22.3)`, which
the mixed-sign classification excludes.

## Scope retained

The proof is support-complete for projective limits of stationary product
roots.  It says neither that a macroscopic stationary equilibrium exists nor
that nonstationary/periodic behavioral equilibria are excluded.  The note's
qualification is correct.

## Addendum: vanishing-error stationary profiles

I checked the strengthened consequence with terminal errors
`epsilon_n->0`.  **Verdict remains VALID.**

Let `h_-i^n=1-product_(j!=i)(1-p_j^n)`.  Geometric first-row conditioning
gives exactly

```text
U_i^n=theta_i^n Q_i^n+(1-theta_i^n)N_i^n,
theta_i^n=p_i^n/[p_i^n+(1-p_i^n)h_-i^n].
```

When `0<lambda_i<1`, one has
`p_i^n=lambda_i H_n+o(H_n)` and
`h_-i^n=(1-lambda_i)H_n+o(H_n)`, so
`theta_i^n->lambda_i`; both weights are uniformly positive eventually.
Immediate Quit and Never are legal deviations.  Since `U_i^n` is their exact
convex combination while each endpoint is at most `U_i^n+epsilon_n`, the
positive weight bounds force `|Q_i^n-N_i^n|->0`.  Together with
`Q_i^n->B_0` and the singleton-law limit for `U_i^n`, this yields
`g_i(lambda)=0`.

If `lambda_i=0`, the immediate-Quit deviation alone gives
`lim U_i^n>=lim Q_i^n=B_0`, hence `g_i(lambda)>=0`; no assertion about the
possibly vanishing Never weight is needed.  If `lambda_i=1`, every other
lambda coordinate is zero and `(22.2)` gives `g_i(lambda)=0` directly.
Thus all endpoint cases and the approximate-Nash quantifiers are covered.
