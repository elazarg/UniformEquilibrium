# Review of paid-row Proposition 70

Reviewer: `CODEX_EULER`

Verdict: **PASS**.

I checked Section 70 of
[`CODEX_CEDAR__PAID_ROW_REENTRY.md`](../notes/CODEX_CEDAR__PAID_ROW_REENTRY.md),
including the pure-row cap formula, floor lift, cap invariance, returned cycle,
the `Lambda` constants, endpoint cases of the maximum ratio, and the exact
scope of both arms.

## Floor-safe convex lift

For every pure coalition row and player, the checked membership-toggle cap
satisfies `b_(t,i)>=P_i`.  If `u_(t,i)<P_i`, the denominator
`b_(t,i)-u_(t,i)` is strictly positive and

```text
0 < (P_i-u_(t,i))/(b_(t,i)-u_(t,i)) <= 1.
```

Otherwise the declared ratio is zero.  Hence `theta_i`, the finite maximum
over the orbit, lies in `[0,1]`.  For every vertex, using a coefficient at
least its local ratio lifts the convex combination

```text
w_(t,i)=(1-theta_i)u_(t,i)+theta_i b_(t,i)
```

above `P_i`; if `u_(t,i)>=P_i`, both endpoints are already above the floor.
Both `u_t` and `b_t` lie in the canonical reward box, so convexity preserves
the box.  Since `S_L=S_0`, both `u_L=u_0` and `b_L=b_0`; the coordinatewise
coefficients are fixed around the orbit, so `w_L=w_0` exactly.

## Selected gain and slack-arm constants

Across the selected toggle `S_t -> S_(t+1)`, only player `m_t` changes its
membership action.  Its opponents' pure row is unchanged, so the unrestricted
membership-toggle cap is identical at the endpoints.  Therefore

```text
w_(t+1,m_t)-w_(t,m_t)
 =(1-theta_(m_t))[u_(t+1,m_t)-u_(t,m_t)]
 >=delta_(m_t) gamma.
```

Summing gives total selected motion at least `gamma Lambda`.  The returned
full payoff vector forces total off-diagonal motion at most its negative, and
there are `L(n-1)` off-diagonal entries.  The Section 69 argument with

```text
epsilon <= gamma Lambda/[4L(n-1)]
```

therefore gives

```text
Raw >= gamma Lambda/[4ML(n-1)],
Agg >= gamma Lambda/[gamma Lambda+4ML(n-1)].
```

The factors `L`, `n-1`, `2 epsilon`, and the Bellman motion factor `2M` are
all accounted for correctly.

## Tight arm

Every `delta_i` is nonnegative.  Thus `Lambda=0` forces
`delta_(m_t)=0`, equivalently `theta_(m_t)=1`, on every selected edge.  For
each label occurring as a selected toggler, the finite maximum defining its
`theta` is therefore attained at one ratio equal to one.  A zero-case ratio
cannot attain one, so at that vertex `u<P<=b`; equality of

```text
(P-u)/(b-u)=1
```

is exactly `P=b`.  The pure-row cap is the maximum of the current membership
payoff `u` and the other membership payoff.  Since `u<P=b`, the other action
attains `P` exactly.  Thus the stated conclusion

```text
u_(t,i)<P_i=b_(t,i)
```

and the attained pure opponent minmax interpretation are correct for every
selected label, though generally at different orbit vertices.

## Scope

The dichotomy removes only the hidden floor-feasibility issue.  In the
positive-`Lambda` arm it does not construct any exact connector or global
shadow; the charge conclusion remains conditional on those paths.  In the
zero-`Lambda` arm it gives separate pure rows attaining each selected
player's punishment value but does not assemble them into one common
punishment profile or an exact Bellman chronology.  No connector, minmax
assembly, fixed edge, or conjecture-level producer is inferred.  The note's
scope statements are exact.

## Addendum: Corollary 70A

Verdict: **PASS**.

The coordinatewise clipping

```text
z_(t,i)=max(u_(t,i),P_i)
```

is floor-safe, remains in the canonical reward box, and is exactly returned
because `u_L=u_0`.  On a selected edge only `m_t` changes membership against
the same pure opponent row.  Hence its pure-row cap is unchanged and is

```text
b_(t,m_t)=max(u_(t,m_t),u_(t+1,m_t))=u_(t+1,m_t),
```

where the last equality uses the strict selected gain.  The punishment-floor
bound `P_(m_t)<=b_(t,m_t)` then gives

```text
g_t=z_(t+1,m_t)-z_(t,m_t)
   =b_(t,m_t)-max(u_(t,m_t),P_(m_t)) >= 0.
```

Thus the `z` ledger is a literal closed floor-safe payoff ledger, and the
Section 69 off-diagonal averaging argument applies with total selected gain
`G`.  Substituting `G` for its earlier lower bound gives exactly

```text
epsilon <= G/(4*L*(n-1)),
Raw >= G/(4*M*L*(n-1)),
Agg >= G/(G+4*M*L*(n-1)).
```

If `G=0`, nonnegativity of every `g_t` forces every one to vanish.  If the old
selected payoff were at least punishment, then the strict toggle gain would
give `g_t=u_(t+1,m_t)-u_(t,m_t)>=gamma`, a contradiction.  Therefore the old
payoff is strictly below punishment, and `g_t=0` becomes

```text
u_(t,m_t)<P_(m_t)=b_(t,m_t)=u_(t+1,m_t).
```

This is genuinely stronger than Proposition 70's labelwise conclusion: the
punishment equality holds on every selected edge of the returned orbit.  Its
scope remains conditional.  Positive `G` does not supply the exact floor-path
shadow, and `G=0` does not assemble the edgewise punishment rows into a common
minmax strategy or a Bellman chronology.
