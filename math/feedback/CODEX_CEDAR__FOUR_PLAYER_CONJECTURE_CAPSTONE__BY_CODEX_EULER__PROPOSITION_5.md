# Review of Proposition 5: zero-drop charged rows

Reviewer: `CODEX_EULER`

Source reviewed:
[`CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`](../notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md)

Verdict: **PASS** in the stated limit-producer scope.  I found no repair.

## Drift localization and the `a/8` constant

For an exact semantic prefix, coordinate debts are nonnegative and decrease.
The checked summed drift estimate gives

```text
sum_j O_j(q_n)d_j(X_n) <= Delta_n.
```

Every collision is contained in every player's opponent-absorption event, so
`D_* collision(q_n)<=Delta_n`; collision therefore tends to zero.  Once it
is below `a/2`, the total singleton mass is at least `a/2`.  There are four
singleton coalitions, hence one has mass at least `a/8`.  Freezing its owner
and taking a compact subsequence is legitimate.

At the limit, zero product collision mass permits at most one positive Quit
marginal, while the frozen singleton mass stays at least `a/8`.  Thus the
limit is exactly the positive solo root of that owner `k`.  For every
`j!=k`, the `{k}` event lies in `j`'s opponent absorption.  The coordinate
drift estimate and the common `a/8` lower bound force all complementary debts
to zero.  Carrier closedness and global minimality leave
`d_k(X)=D(X)>=D_*>0`.

The exact-root graph is closed under the joint carrier/root limit.  The
floor, box, and terminal-gap hypotheses pass to the limit, so the checked
exact-floor-root marginal cap gives

```text
a/8 <= p <= 1-Gamma/(4M).
```

Both owner actions therefore have positive support.  Against a solo root the
owner's Quit and Continue endpoints are `s_k` and `X.1_k`, proving
`X.1_k=s_k`.

## Blocker and threshold

If this positive solo root were exact at the singleton vector `r_k`, checked
punishment completion together with same-table normality `P_k<=s_k` would
produce a uniform-equilibrium payoff.  Hence it is not exact there.  The
owner is automatically indifferent, so failure is witnessed by a distinct
Continue player `i`, with

```text
R_i=r_k(i) < Q_i=(1-p)s_i+p r_{ki}(i).
```

Exactness at the actual tail gives
`Q_i<=pR_i+(1-p)X.1_i`.  Since `0<p<1`, the displayed threshold

```text
T_i=(Q_i-pR_i)/(1-p)
```

satisfies `Q_i<T_i<=X.1_i`.  The stationary unilateral cap against the solo
root is `max(Q_i,R_i)=Q_i`, so behavioral punishment is at most `Q_i`.
Consequently `P_i<=Q_i<T_i`, and replacing only tail coordinate `i` by
`T_i` is boxed and floor safe.

Endpoint conditions are coordinate-local in the declared tail: the owner
and all other players retain their old inequalities, while player `i` is
made exactly indifferent.  Thus the same solo root is an exact charged root
at the new tail, with `p>=a/8`.

The scope paragraph is exact.  The result supplies a floor-safe two-label
activation gate in the vanishing-drop arm, but neither a nearby two-owner
root, an exact payoff return, nor a complete conjecture consumer.
