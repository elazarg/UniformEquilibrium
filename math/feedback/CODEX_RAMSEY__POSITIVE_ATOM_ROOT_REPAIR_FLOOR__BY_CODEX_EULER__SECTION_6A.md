# Focused feedback on Section 6A of `CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR`

Reviewer: `CODEX_EULER`

## Scope and verdict

I independently checked Proposition 6A's posterior identity and constants,
literal prefix semantics, all-suffix clocks, semantic/debt coupling, and atom
orientation/provenance claims.

**Verdict: the finite two-port estimates and initial whole-ray atom scaling
are valid.  Items 3--4 need a scope repair:** the residual port can be written
on the conditional component ray, but its posterior coordinates need not
remain small, and the original atom/pure-time orientation is not thereby
reusable at the residual endpoint.

## Valid posterior and clock estimates

For

```text
M_t(c)=(1-c)S_t+cT_t,
F_t(c)=cT_t/M_t(c),
```

direct cancellation gives exactly

```text
F_t(a)-F_t(b)
 =S_t*T_t*(a-b)/(M_t(a)M_t(b)).
```

Since `|a-b|<=h`, `S_t,T_t<=1`, and both denominators are at least `rho`,

```text
|F_t(a)-F_t(b)|<=h/rho^2.
```

Conditional mover Quit probabilities are affine in the posterior component
weight, so their rowwise difference is at most this amount.  Opponents agree.
Product telescoping on any interval of at most `L` rows therefore gives

```text
min(1,L*h/rho^2)
```

for joint survival and every one-player-deleted survival.  When the deleted
player is the mover, the products agree exactly.  The constants in (6A.5) are
correct.

## Valid literal semantics and cap/debt coupling

Conditioning `sigma^a` on `t` all-Continue outcomes gives its actual residual
profile, so every identity

```text
x^a_t=Phi_{q^a_t}(x^a_{t+1})
```

is literal.  At time `L`, the two mover residual laws are mixtures of the same
two conditional components with weights `F_L(a),F_L(b)`.  Maximal coupling of
the component labels disagrees with probability at most `h/rho^2`.

For a fixed deviation by a nonmover, this couples the complete payoff
experiment; for a deviation by the mover, the updated opponents are actually
identical.  Bounded payoffs in `[-R,R]` yield `2R*h/rho^2` for prescribed and
cap coordinates, uniformly before taking the best-response supremum.  Debt is
their difference, giving `4R*h/rho^2`.  Thus (6A.4), (6A.6), and the rate
condition (6A.7) are correct.  The symbol `delta` should simply be defined in
the proposition as the chosen coordinatewise initial semantic discrepancy.

## Valid initial whole-ray atom scaling

At the unconditioned profile level,

```text
Law(sigma^a)=(1-a)Law(sigma^0)+a Law(sigma^1).
```

Hence comparison with the same full endpoint `sigma^1` multiplies every fixed
signed terminal atom by exactly `1-a`.  If the observer response is applied
identically on the two rectangle sides (with observer distinct from mover),
the same affine identity holds.  Therefore `a<=1/2` preserves the same
terminal label and prescribed/rectangle orientation at at least half charge;
the full-endpoint debt field is unchanged because the endpoint remains
`sigma^1`.  No argmax-stability hypothesis is needed for this initial
whole-profile statement.

## Required repair: residual reusability is not proved

At cutoff `L`, the residual ports do lie on a common **conditional** two-law
ray, but their coordinates are `F_L(a),F_L(b)`.  The reach-floor assumptions
bound their difference; they do not keep either coordinate below `h` or below
`1/2`.  Bayesian amplification can make both posteriors order one.  Thus the
residual comparison cannot automatically be “restarted” with the same small
parameter required by (6A.1), nor does semantic proximity to a next frozen
anchor establish that the residual port lies on that next packet's required
same-law ray.

Likewise, the preserved terminal label, observer pure time, and orientation
belong to the initial unconditioned comparison `sigma^a` versus `sigma^1`.
Conditioning may pass the pure stopping date and can change the residual atom's
label or size.  Section 6A's final limitation already acknowledges this, but
items 3--4 should not state unconditional restartability/provenance before the
limitation.

A precise replacement is:

```text
the endpoint is an actual carrier point and remains a mixture of the two
conditional component laws; the finite two-port estimates can be applied
there if fresh posterior-size/reach-floor hypotheses hold.  Initial whole-ray
atom orientation scales exactly, but residual atom-terminal reusability is a
separate hypothesis.
```

With that repair, Proposition 6A is a valid finite-port theorem and its stated
nonclaim about semantic-state-only reprojection is exact.
