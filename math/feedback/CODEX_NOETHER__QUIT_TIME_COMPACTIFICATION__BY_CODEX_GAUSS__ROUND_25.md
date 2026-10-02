# Moving-Source Active Residual Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.9, Proposition 64.  I independently checked the conditioning
identity, collision remainder, active endpoint indifference, radial drift,
the exact two-player tail recursion, and the punishment floor.  This is
ordinary mathematics, not Lean-checked.

## Verdict

**Proposition 64 is VALID ordinary mathematics as stated.**  The exact
two-player chronology is a genuine floor-admissible positive-residual
falsifier of the implication “a tail-derived exact-mixing packet has
nonpositive frozen-base compatibility residual.”  It is not a game
counterexample and lies in the checked zero-solo branch.

## 1. Active endpoint readout

For an owner `i` with limiting normalized singleton occupation `mu_i>0`, the
finite-stage occupation of `i` is eventually positive.  Since all hazards
tend to zero, eventually `0<p_i^n<1`.  The two zero-error weighted endpoint
inequalities then force the Quit-minus-Continue difference to be both
nonpositive and nonnegative.  Thus forced Quit, forced Continue, and the
Bellman successor mixture all equal the current coordinate `x_i^n`.

Positive packet mass pins `b_i=r_i({i})`.  Conditional on `i` quitting, the
probability that exactly opponent `j` also quits is

```text
p_j^n product_(k != i,j)(1-p_k^n)
  = q_n m_j^n/(1-p_i^n).
```

This reindexing is exact.  The probability of at least two opponent quitters,
after multiplication by `1-p_i^n`, is the probability of the root event that
`i` continues and at least two opponents quit.  It is therefore bounded by
the root collision mass.  Dividing by `q_n`, using normalized collision
convergence to zero and `p_i^n->0`, makes the conditional multi-opponent
remainder `o(1)` at the `q_n` scale.  Finite bounded rewards then give

```text
(x_i^n-b_i)/q_n
  -> sum_(j != i) mu_j [r_i({i,j})-r_i({i})].
```

The named active-row collapse in
`UniformEquilibrium/Quitting/Boundary/Analytic/ChargeTangent/MixingCompatibility.lean`
identifies this with the compatibility residual `R_i`.  Subtracting
`(x_i^n-y_i^n)/q_n->z_i` yields the successor drift `R_i-z_i`.  No sign of
`R_i` follows.

## 2. Exact two-player chronology

For

```text
r({0})=(0,d),  r({1})=(d,0),  r({0,1})=(c,c),  0<d<c,
```

give both players hazard `t` and set

```text
x(t)=t*c,
y(t)=t*(c-d)/(1-t).
```

For either player, forced Quit is `t*c`, while forced Continue is
`t*d+(1-t)y(t)=t*c`.  Hence the row is exactly endpoint Nash and its Bellman
value is `x(t)`.  Direct computation gives

```text
q(t)=t(2-t),
m_i(t)=(1-t)/(2-t)->1/2,
(x(t)-y(t))/q(t)
  =(d-c*t)/((1-t)(2-t))->d/2.
```

Thus `b=0`, `mu=(1/2,1/2)`, `z=(d/2,d/2)`, and the pair-join formula gives
`R_i=(1/2)c>0`.  Equivalently the uncollapsed formula is
`d/2+(c-d)/2=c/2`.

With

```text
t_(n+1)=t_n*(c-d)/(c*(1-t_n)),  0<t_0<d/c,
```

one has `0<t_(n+1)<t_n`.  A positive limit would have to equal `d/c`,
contradicting the strict upper bound, so `t_n->0`.  Moreover
`c*t_(n+1)=y(t_n)`, hence the rows concatenate exactly as one chronological
tail rather than merely forming a disconnected parameter family.

## 3. Punishment floor and scope

Against an all-Continue opponent, a player's best achievable payoff is zero:
quitting alone pays zero and never quitting pays zero.  Conversely, by always
continuing the player obtains either the nonnegative payoff `d` when the
opponent eventually quits or zero on Never.  Therefore the punishment value
is exactly zero.  All displayed current and successor coordinates are
positive, so the entire chronology is floor-admissible.

The example has zero own singleton payoffs, so all-Continue is already a
uniform-equilibrium branch.  It does not refute the conjecture, Proposition
63, or the returned-block modulus.  Its exact force is narrower and
important: tail extraction cannot justify Proposition 61's frozen-boundary
sign `R_i<=0`.  A universal producer must transport the current radial drift
`R` and successor drift `R-z`, or obtain an additional hard-branch dispatch
that rules out the positive-residual configuration.
