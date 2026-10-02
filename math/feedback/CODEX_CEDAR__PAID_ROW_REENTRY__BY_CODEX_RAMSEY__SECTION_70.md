# Review of Section 70

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

## Claim checked

Section 70 interpolates each payoff coordinate of the checked strict-toggle
orbit toward its pure-row unilateral cap.  It claims an exact dichotomy:
either a positive amount of selected gain survives in a returned floor-safe
cycle, or every label used by the orbit has a pure opponent row which attains
its punishment value and makes the alternate membership action exactly
minmax.

## Cap lift

For a below-floor entry `u_(t,i)<P_i`, the checked bound `P_i<=b_(t,i)` makes
the denominator in (70.3) positive and puts the ratio in `(0,1]`.  Taking the
finite maximum `theta_i` makes

```text
(1-theta_i)u_(t,i)+theta_i b_(t,i) >= P_i
```

at every vertex.  Both endpoints lie in the canonical reward box, so the
interpolated vector does too.  The orbit returns in both its coalition and
pure-row cap data; hence `w_L=w_0`.

At edge `t`, only `m_t` changes its own membership action.  Its opponents are
identical, so its two-action unilateral cap is identical at both endpoints.
Therefore

```text
w_(t+1,m_t)-w_(t,m_t)
 = (1-theta_(m_t))
     [u_(t+1,m_t)-u_(t,m_t)]
 >= delta_(m_t) gamma.
```

The orientation and use of cap invariance are exact.

## Positive-slack constants

If `Lambda>0`, total selected motion is at least `gamma Lambda`.  Since the
whole vector cycle returns, one of the `L(n-1)` off-diagonal entries is at
most `-gamma Lambda/[L(n-1)]`.  The two endpoint shadow errors and (70.6)
leave negative exact-state motion at least
`gamma Lambda/[2L(n-1)]`.  The checked `2M` one-edge Bellman motion estimate
then gives

```text
Raw >= gamma Lambda/[4ML(n-1)].
```

Using `Agg>=Raw/(1+Raw)` gives exactly (70.7).  Thus the reduction to the
reviewed aggregate-block consumer has the stated constants and does not need
a separately assumed charge after the exact connectors exist.

## Tight-minmax alternative

If `Lambda=0`, every nonnegative selected `delta_(m_t)` is zero.  For every
player which actually appears as a toggler, `theta_i=1`.  A finite maximum in
(70.3) can equal one only at a below-floor vertex whose ratio equals one;
because `u<P<=b`, this is exactly

```text
u_(t,i)<P_i=b_(t,i).
```

The pure-row cap is the maximum of the two membership payoffs.  The current
membership payoff is strictly below `P_i=b`, so the alternate action pays
exactly `P_i`.  Since `P_i` is the punishment infimum and this pure opponent
row has cap exactly `P_i`, the environment genuinely attains the stationary
minmax; this is stronger than merely finding a tight inequality.

## Boundary and scope

If all orbit payoffs already dominate punishment, every `theta_i=0` and
`Lambda=L`, reducing to Section 69.  If `b=P>u`, the full lift erases that
coordinate's selected gain, so the zero-slack alternative is sharp.

The proposition does not construct exact floor-admissible connectors in the
positive-slack arm and does not consume the attained tight-minmax rows in the
zero-slack arm.  It therefore removes the floor-feasibility ambiguity without
renaming either remaining producer.  No repair is required.

## Corollary 70A addendum

The coordinatewise floor-clip sharpening also **passes**.  On selected edge
`t`, the new membership action beats the old one, so the exact two-action cap
is

```text
b_(t,m_t)=u_(t+1,m_t)>=P_(m_t).
```

Therefore

```text
z_(t+1,m_t)-z_(t,m_t)
 = b_(t,m_t)-max(u_(t,m_t),P_(m_t))=g_t>=0.
```

The clipped vector returns and stays in the canonical box.  If `G=sum g_t`
is positive, the same off-diagonal compensation and `2M` edge-motion proof
gives exactly `Raw>=G/[4ML(n-1)]` and the displayed aggregate denominator.
If `G=0`, every nonnegative `g_t` is zero.  The old payoff cannot already be
above punishment because its selected gain is at least `gamma`; hence
`u_t<P=b=u_(t+1)` on every selected edge.  Conversely that equality gives
`g_t=0`.  Thus (70.14) is an edgewise tight orbit, not merely an unrelated
collection of tight vertices.  Exact connector production and consumption
of that tight orbit remain correctly open.
