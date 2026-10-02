# Independent review of the positive-Never half-release Zeno endpoint

Reviewer: **CODEX_EULER**

Source:
[`CODEX_MINER__POSITIVE_NEVER_HALF_RELEASE_ZENO_ENDPOINT.md`](../notes/CODEX_MINER__POSITIVE_NEVER_HALF_RELEASE_ZENO_ENDPOINT.md)

Verdict: **PASS, internal only.**  The fixed-source geometric-chord theorem,
the debt telescope, the minimum/off-minimum endpoint split, and the rational
boundary regression are correct.  The minimum endpoint enters an existing
checked causal-suffix producer; the strict off-minimum endpoint remains
unconsumed.

## 1. Claim checked

Starting from one finite-clock actual product profile `sigma`, choose a date
after every finite support point and let `tau` move player `a`'s remaining
Never mass to that date.  Repeated equal stopping-law mixtures with `tau`
form the single chord

```text
aLaw(sigma^k)=2^(-k)aLaw(sigma)+(1-2^(-k))aLaw(tau).
```

The note claims exact formulas for the Never and singleton coordinates,
semantic/cap convergence to `tau`, a geometric descent-or-transfer
telescope, a checked causal handoff when `D(tau)=D_*`, and a two-player
regression showing that `D(tau)>D_*` is compatible with strict unique
all-Continue cap geometry when the global hard-residual hypotheses are
absent.

## 2. Exact stopping-law chord and unrestricted caps

Choose `K` after the finite support of every marginal law.  The source and
late-cap laws differ on terminal outcomes only when every source clock was
Never.  That event remains `Never` in the source branch and becomes
singleton `{a}` in the capped branch.  Therefore, with `q_k=2^(-k)q`,

```text
Law(sigma^k)(Never)=q_k,
Law(sigma^k)({a})=Law(sigma)({a})+q-q_k.
```

The owner payoff increases by `s(q-q_k)`.  Since player `a`'s unrestricted
cap depends only on the opponents, it is constant, giving the displayed
owner-debt identity.

The complete `a`-law converges to the late-cap law in total variation.  For
each outsider and each fixed behavioral deviation, the payoff perturbation
has the same uniform total-variation bound; taking the supremum preserves
it.  Thus the convergence of the full terminal semantic pair, including
unrestricted caps, is justified.  No stationary-only argument is used.

## 3. Descent/transfer telescope

At step `k`, the owner improvement is

```text
g_k=s(q_k-q_(k+1))=s q_k/2.
```

If the opponent debt increase is at most `g_k/2`, total debt drops by at
least `s q_k/4`.  Otherwise the reviewed finite-recipient/three-label decoder
is the transfer arm.  In the no-transfer branch,

```text
sum_k s q_k/4=(s/4)(2q)=s q/2,
```

and continuity at the chord endpoint gives
`D(tau)<=D(sigma)-s q/2`.  Hence an initial excess below `s q/2` forces a
finite transfer stage.  The constants and inequality orientations pass.

## 4. Endpoint handoff and exact scope

When `D(tau)=D_*>0`, the endpoint is an **actual** minimum joint-law point
with `Law(tau)({a})>=q>0`.  The hypotheses of
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` are then
literal, so the checked deep causal-prefix producer applies at this endpoint.
The note correctly stops short of claiming that the suffix atom is an exact
prefix root, a Bellman edge, or a uniform-payoff consumer.

When `D(tau)>D_*`, ordinary causalization can retain the finite atom, but the
near-minimum front-debt conclusion is unavailable.  This strict off-minimum
endpoint is the exact surviving branch.

## 5. Rational regression

For

```text
r({a})=(1,1),  r({b})=(2,0),  r({a,b})=(-1,-1),
```

with `b` quitting at date zero with probability `1/4` and `a` quitting at
date one with probability `1-x`, direct stopping-time comparison gives

```text
U=(5/4-3x/4, 3(1-x)/4),
B=(5/4,       1-x),
d=(3x/4,      (1-x)/4),
D=1/4+x/2.
```

These are unrestricted cap values: later Quit and Never attain the stated
maxima, while immediate/collision alternatives are weakly lower.  At the
one-stage cap root the two Continue-minus-Quit differences are

```text
1/4+(11/4)z,
2w+(1-w)(1-x),
```

so all Continue is the unique exact root for `0<x<=1/2`, with strict margin.
Half release sends `x` to `x/2` and lowers debt by `x/4`, while the endpoint
has positive singleton mass and debt `1/4`.  The profile with `b` surely
quitting at date zero and `a` continuing has zero debt, so `D_*=0`.  Thus the
example refutes only a local strict-root implication, exactly as stated; it
is neither a positive-minimum example nor a terminal-gap counterexample.

## 6. Comparison with the marked-ray compactification

This theorem and
`CODEX_EULER__POSITIVE_NEVER_ZENO_MARKED_ATOM_COMPACTIFICATION` address
different renewal modes.

- Here every stage lies on one literal actual-profile chord with a fixed
  endpoint `tau`.  This yields the sharper exact total drop `s q/2` and an
  attained q=0 endpoint.
- In the marked-ray theorem, every release is followed by compact cap-ray
  minimization and a separately selected law-matched actualizer.  The source
  and endpoint are reselected, so there is no single geometric chord.  Its
  extra content is that the normalization factors have positive product and
  therefore cannot erase the deposited singleton atom.

Accordingly the present fixed-source theorem is the preferred endpoint
description whenever one can keep the same `sigma,tau` chord.  It does not
replace the marked-ray argument in the reselected-source iteration, and
neither theorem consumes the strict off-minimum q=0 endpoint.

## 7. Recommendation

Keep internal.  The exact chord and regression are useful source/provenance
clarifications, but the only conjecture-facing equality arm feeds an already
checked causal-suffix producer, while the strict off-minimum arm remains the
same live obstruction.  No standalone export is warranted without a new
consumer.
