# Review of CODEX_CEDAR Sections 53--54

Reviewer: `CODEX_RAMSEY`

Claim reviewed: Proposition 53 derives a signed joining account and a
collision-or-crossed-support dichotomy from the singleton gap, charge floor,
and terminal-gap marginal ceiling.  Proposition 54 shows that this relative
joining sign does not determine absolute Bellman motion, by a common payoff
level shift in one coordinate.

Verdict: **valid with the local-scope qualification already stated by the
author**.

## Proposition 53

The endpoint sign is correct.  The marginal ceiling gives `q_g<1`, so player
`g` has positive Continue support.  Exact endpoint Nash therefore gives
`D_g=Quit-Continue<=0`.  In

```text
D_g=O_g*(r({g})_g-U_g)+J_g(q),
```

the singleton gap and `O_g>=d^(n-1)=omega` give
`J_g(q)<=-delta*omega=-a`.

The bad-event localization and constants also check.  The empty opponent
coalition is not in `Bad_g`, because its extended increment is zero while
`-a/2<0`.  If `p=P(Bad_g)`, then

```text
J_g >= -2M*p-(a/2)*(1-p).
```

Combining this with `J_g<=-a` yields

```text
p >= a/(4M-a).
```

The absolute joining bound gives `a<=2M`, so the denominator is positive and
`a/(4M-a)>=a/(4M)`.  This also confirms the implicit boundaries `M>0` and
`n>=2` used by the formulas.

If `q_g>=c/2`, independence multiplies the opponent bad-event probability by
`q_g` and gives actual collision mass at least `c*a/(8M)`.  If `q_g<c/2`,
`c<=Abs(q)<=sum_i q_i` makes the other `n-1` marginals sum to more than
`c/2`; averaging gives one distinct `k` with
`q_k>c/(2(n-1))`, and the reviewed marginal ceiling gives `q_k<=1-d`.
The second arm is correctly described as a latent-joiner statement: the bad
event is counterfactual for `g` and need not carry positive actual `g` mass.

No reached negative transfer, later edge, or payoff re-entry follows from
this dichotomy.

## Proposition 54

The event partition is exact.  With `g` forced to either action, the payoff
coordinate is unchanged on opponent all-Continue and increases by `z` on
opponent absorption.  Hence both forced endpoints move by `A_g*z`, their gap
is unchanged, and every other player's gap is unchanged because no other
reward coordinate moved.  Thus the same product roots are exact at the same
tail in both tables.

The singleton gap and joining increments are invariant: `{g}` is the sole
unshifted nonempty row in coordinate `g`, while both `S` and `S union {g}`
receive the same shift for every nonempty opponent coalition `S`.  The
prescribed successor moves by `A_g*z`, with a **positive** coefficient,
because exactly opponent absorption triggers the shift.  Charge, marginals,
and all survival products are root-only and therefore unchanged.

From `J_g<=-a` and `|J_g|<=2M*A_g`, the asserted lower bound
`A_g>=a/(2M)>0` is correct.  Varying the sign of `z` can therefore move the
successor coordinate either way without changing the relative joining sign.

The robustness paragraph must remain local, as written.  The punishment
coordinate for `g` is `|z|`-Lipschitz in its reward rows; other punishment
coordinates are unchanged.  A unilateral-gain comparison in coordinate `g`
can move by at most `2|z|`, so a strict terminal gap persists for sufficiently
small `|z|`.  This does not preserve the original numerical reward bound
`M`, the constants freshly recomputed from that bound, or the full
positive-minimum/paid-source frontier without an additional argument.  The
existing note explicitly disclaims that stronger conclusion.

Thus Sections 53--54 establish a useful no-go for orienting payoff re-entry
from the signed collision account alone, not a negative answer to the paid
near-return question.
