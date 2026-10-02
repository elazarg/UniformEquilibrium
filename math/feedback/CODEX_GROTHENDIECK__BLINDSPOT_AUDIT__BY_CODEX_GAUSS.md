# Feedback on the independent-clock candidate

Reviewer: `CODEX_GAUSS`

Reviewed item: Candidate 3's clock-tie conjecture in
[`../notes/CODEX_GROTHENDIECK__BLINDSPOT_AUDIT.md`](../notes/CODEX_GROTHENDIECK__BLINDSPOT_AUDIT.md).
This is ordinary mathematics, not checked in Lean.

## Verdict

The conjecture is **true, sharp, and admits a stronger finite-family form**.
For independent countable quit times, if `a_k` is the probability that the
`k`-th of `m` disjoint designated pairs is exactly the strict first-quitter
coalition, then

`sum_k sqrt(a_k) <= 1`.

For two pairs this is exactly

`ell=1-a-b >= 2*sqrt(a*b)`, hence `ell^2>=4ab`.

The full proof and an equal-size-coalition generalization are recorded as
Propositions 17--19 in
[`../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md).

## Independent proof capsule

At one live date let `q_i` and `c_i=1-q_i` be the four Quit and Continue
probabilities.  For the two pairs set

```text
x=sqrt(c_1*c_2), y=sqrt(c_3*c_4),
u=sqrt(q_1*q_2), v=sqrt(q_3*q_4).
```

AM--GM gives `u<=1-x` and `v<=1-y`.  If `A_0,B_0,C_0` are the date's two
desired-exit probabilities and joint-continuation probability, then

```text
sqrt(A_0)+sqrt(B_0)+sqrt(C_0)
 =u*y+v*x+x*y
 <=x+y-x*y<=1.
```

If `a',b'` are the conditional future desired probabilities, then
`a=A_0+C_0*a'` and `b=B_0+C_0*b'`.  Subadditivity of square root propagates
`sqrt(a')+sqrt(b')<=1` one step backward.  Apply this to finite truncations
and pass to the increasing infinite-horizon events.

For `m` pairs, the local left side is bounded by

`sum_k (1-x_k)*product_(j!=k)x_j + product_j x_j <=1`,

the probability of at most one failure in an auxiliary Bernoulli product.

## Scope

This resolves only the law inequality.  It is genuinely all-profile for an
ordinary quitting game because the unique live history induces independent
player stopping laws; it does not cover an external public-correlated device.
It is not a game counterexample.  The hard remaining step in Candidate 3 is
exactly as stated in the audit: realize incompatible lower bounds on the
desired events and an upper bound on leakage through unilateral pure-time
deviation gains of one literal finite reward table.  Passive dominated
``auditor'' players cannot do this; their Never constraint is automatic, so
any useful calibrator must itself enter the independent-clock accounting.
