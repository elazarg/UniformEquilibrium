# Paid block-hazard and finite-packing reduction

Author: `CHATGPT_EXTERNAL`
Status: `PROOF_DRAFT`

## Exact question

This addresses
[`../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md).
It does not construct the requested fixed-charge exact near-return family and
does not give a full-source counterexample. It separates the behavioral mass
certified by a paid first-disagreement row from the charge of an exact
Nash--Bellman edge, and gives two sharper producer targets.

## Why it could matter

The paid row supplies a fixed behavioral block hazard, but neither its pure
stopping-time Quit nor its live mass is automatically a root of an exact
floor-admissible Nash--Bellman edge. A valid producer must Nashify and reproject
the whole block at its actually reached source while retaining either a fixed
edge charge or fixed aggregate block absorption.

## Sources checked

- [`../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md).
- [`../formalized/PUNISHMENT_FLOOR_PAYOFF_NEAR_RETURN.md`](../formalized/PUNISHMENT_FLOOR_PAYOFF_NEAR_RETURN.md)
  for the existing payoff-near-return consumer and finite-forward-packet
  compactness route.
- [`../formalized/TIGHT_FACE_COLLISION_DEBT_ESCAPE_FOR_PAID_NEAR_RETURNS.md`](../formalized/TIGHT_FACE_COLLISION_DEBT_ESCAPE_FOR_PAID_NEAR_RETURNS.md)
  for the independently established local collision/debt obstruction.

## Work

### 1. Finite-packing criterion

Let `X` be the compact space of punishment-floor-admissible states, let
`P:X -> R^I` be payoff projection, and fix `c>0`. Choose a finite cover of
`P(X)` by `N_P(eta)` sets of sup-norm diameter at most `eta`.

If one exact admissible path contains more than `N_P(eta)` edges of charge at
least `c`, list their indices

```text
j_1<...<j_(N_P(eta)+1).
```

Two corresponding edge tails have payoff projections in one cover element.
The subpath between those tails has endpoint payoff distance at most `eta` and
contains the earlier selected `c`-charged edge.

Consequently the requested family follows from

```text
exists c>0, for every K,
  there is an exact admissible path containing at least K edges
  of charge at least c.                                  (R)
```

Conversely, failure of a `c`-charged near-return at accuracy `eta` bounds the
number of `c`-charged edges on every admissible exact path by `N_P(eta)`.

### 2. What the paid row supplies

Let `M` bound all absolute quitting rewards. Suppose two pure stopping times
`s<t` have paid payoff difference at least `g>0`. Let `E_(s,t)` be the event
that some opponent Quits between the two dates, including endpoint ties.
Outside this event the two plans give the same payoff: before `s` they are
identical, and otherwise both eventually Quit alone. Hence

```text
g <= 2M*P(E_(s,t)).
```

When `M>0`,

```text
P(E_(s,t)) >= kappa := g/(2M)>0.                       (1)
```

For conditional opponent-absorption hazards `h_u`, this is the fixed block
bound

```text
1-product_(u=s)^t (1-h_u) >= kappa.                    (2)
```

It does not force any one `h_u` to be bounded away from zero. For example,
with observer payoff one only when the opponent Quits alone, opponent hazard
`1/N` on each of `N` dates gives waiting gain tending to `1-exp(-1)` while
every responsible marginal hazard tends to zero. This is a telescope-level
regression, not a full positive-minimum source instance.

### 3. Why the pure witness does not give charge one

The witness's sure Quit is a unilateral counterfactual. An exact admissible
edge instead requires one simultaneous stage-Nash product root. Fixing the
observer to Quit and Nashifying the absorbed one-shot game among outsiders
may change collision and preemption probabilities by order one; the observer
may then prefer Continue. Because sure observer Quit makes continuation
unreachable, continuation values cannot repair outsiders' incentives.

Therefore neither `c=1` from the pure witness nor `c=g/(2M)` from behavioral
live mass is a valid exact-edge conclusion.

### 4. Aggregate block denominator

For an exact path with stage absorption charges `q_t`, put

```text
beta_t=1-q_t,
Beta=product_t beta_t.
```

The composed prescribed Bellman map is `F(v)=a+Beta*v`. If
`v_m=F(v_0)`, its repeated-block fixed point satisfies

```text
||vbar-v_0||_infinity
  = ||F(v_0)-v_0||_infinity/(1-Beta).                  (3)
```

Thus the prescribed seam naturally asks for fixed aggregate block absorption,
not necessarily a macroscopic individual edge. A proposed weaker target is

```text
exists c>0, for every eta>0, there is an exact floor-admissible path pi_eta
with endpoint payoff distance <=eta and
1-product_(e in pi_eta)(1-q(e)) >= c.                  (B)
```

Equation (3) proves only the prescribed-payoff denominator. It is not yet an
all-behavior consumer: exact Nashification, punishment-floor admissibility,
and unilateral continuation-cap control remain to be supplied.

### 5. Logical status

Let `S(r)` mean the full positive-minimum paid first-disagreement source
package, `N(r)` the requested exact payoff-near-return family, and `U(r)`
uniform-equilibrium-payoff existence. For finite quitting games the project
has the equivalence between `U(r)` and terminal approximate Nash profiles at
all errors. Hence positive minimum terminal semantic debt in `S(r)` implies
`not U(r)`. The checked near-return consumer gives `N(r) -> U(r)`. Therefore

```text
S(r) -> not N(r),
(S(r) -> N(r)) iff not S(r).                            (4)
```

Pointwise, the producer implication proves that the paid source package cannot
exist; it should not be interpreted as constructing `N(r)` from a consistently
inhabited counterexample source.

## Checks and open objections

- Criterion (R) is correct but may overlap the existing finite-forward-packet
  compactness machinery; determine the exact incremental interface.
- The block-hazard estimate is behavioral and must never be relabelled as an
  exact-edge charge.
- Target (B) is not yet a checked or ordinary all-behavior capstone. A proof
  must control caps and floors as well as the scalar prescribed seam.
- The tight-face collision/debt theorem shows that a source-matched block with
  nonvanishing aggregate absorption and local payoff return must make a fixed
  semantic-debt excursion, activate an outside owner, or leave the local face.

## Feedback wanted

1. Can the paid behavioral interval be Nashified into one exact admissible
   block while retaining a fixed aggregate absorption denominator?
2. Can the exact block be replicated enough to satisfy (R), with its actual
   reached endpoint used as the next source?
3. Is there an exact block-denominator lasso compiler that controls unilateral
   continuation caps, or does an explicit regression rule it out?
