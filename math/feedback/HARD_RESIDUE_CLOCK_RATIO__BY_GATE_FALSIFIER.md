# Adversarial review of the corrected clock-ratio follow-up

Reviewer: `CODEX_GATE_FALSIFIER`

## Verdict

**PASS as ordinary mathematics after minor statement repairs; FAIL the export
gate in its present role.**

Equations (1)--(9) are correct and imply a slightly stronger classification
than stated. But this classifies a *supplied* eventually two-active, strictly
mixed, exact Nash--Bellman tail. No maintained hard-residual producer is shown
to yield that object, and positive Never mass has no closing consumer or rank
transition. It therefore does not yet strictly narrow a named maintained
hard-residual obligation under `exports/README.md`.

The maximal-orbit tail statements (11)--(12) are correct but elementary
consequences of the already-known summability result. They should remain
separate and do not improve the clock-ratio export verdict.

## Exact theorem audited

After one finite cutoff, suppose only distinct players `p,q` can Quit. At
every later date both use probabilities strictly between zero and one. Let
`a_t,b_t` be their respective Quit probabilities. Let `v_t` obey the exact
Bellman recursion and let every root be exact endpoint Nash against `v_{t+1}`.

For player `p`, define

```text
s_p = r_p({p}),
A_p = r_p({p,q}) - r_p({p}),
B_p = r_p({q}) - r_p({p}).
```

The symmetric definitions apply to `q`. The finite cutoff should be removed
from the notation at the outset, or every later quantifier should say “for
all sufficiently large `t`.” Nothing uses the discarded prefix.

## 1. Endpoint and clock-ratio identities

Because `p` strictly mixes, both pure endpoints equal its Bellman value. The
Quit endpoint gives

```text
v_t(p)-s_p = b_t A_p.                         (1)
```

The Continue endpoint gives

```text
v_t(p)-s_p
  = (1-b_t)(v_{t+1}(p)-s_p) + b_t B_p.        (2)
```

Using (1) at date `t+1` in (2) gives exactly

```text
(1-b_t)b_{t+1}A_p = b_t(A_p-B_p).             (3)
```

No boundary value, terminal limit, cap approximation, or limit interchange
is involved. The symmetric equation (4) is equally valid. The proof uses
endpoint Nash for one actual continuation payoff; it neither establishes nor
requires an unrestricted behavioral cap statement.

## 2. Stronger diffuse classification

Assume `b_t -> 0`. If `A_p=0`, equation (1) at `t+1` gives
`v_{t+1}(p)-s_p=0`; then (2) and `b_t>0` give `B_p=0`.

If `A_p != 0`, equation (3) gives

```text
b_{t+1} = rho_p b_t/(1-b_t),
rho_p = (A_p-B_p)/A_p = 1-B_p/A_p.            (5)
```

Strict positivity of consecutive hazards implies `rho_p>0`. If `rho_p>=1`,
then `b_{t+1}>b_t`, contradicting convergence to zero. Therefore

```text
0 < rho_p < 1.                                (6)
```

It follows both that the hazards are eventually geometrically bounded and
summable and that `0 < B_p/A_p < 1`. Thus the exact classification is:

```text
A_p = 0  iff  B_p = 0;

if A_p and B_p are nonzero, they have the same sign,
0 < |B_p| < |A_p|, and sum_t b_t < infinity.
```

The reverse implication in the first line uses diffuseness: if `B_p=0` and
`A_p!=0`, then `rho_p=1`, contradicting `b_t->0`. The symmetric classification
holds for `q` and `a_t`. This should replace the weaker one-way statement (8).

## 3. Positive Never mass

For a genuinely diffuse two-clock tail, root absorption tending to zero
implies both `a_t->0` and `b_t->0`. If both normalized off-diagonal singleton
entries are nonzero, the two classifications give

```text
sum_t a_t < infinity,
sum_t b_t < infinity.
```

Since every tail factor is strictly positive, the infinite-product criterion
gives

```text
product_t (1-a_t)(1-b_t) > 0.                 (9)
```

This is survival forever *conditional on reaching the eventual two-clock
cutoff*. Calling it the all-Never probability of the whole original profile
would also require positive pre-cutoff joint survival. The conclusion is
exact: a nondegenerate diffuse strict-interior two-clock tail cannot absorb
almost surely.

## 4. Sign and projective interpretation

For a card-two nonprojective hard principal, checked project code forces
`B_p<0` and `B_q<0`. The clock-ratio theorem does **not** turn the principal
projective. Instead it forces

```text
A_p < B_p < 0,
A_q < B_q < 0.
```

Each collision payoff lies farther below the receiver's own solo payoff than
the partner-singleton payoff. The negative solo entries are compatible with a
Zeno tail and determine its asymptotic ratios through

```text
rho_p = 1-B_p/A_p,
rho_q = 1-B_q/A_q.
```

This is a collision-geometry restriction, not a contradiction to
nonprojectivity.

## 5. Sharp boundary tests

### Nonzero case

The earlier exact counterexample is a sharp positive test:

```text
r_p({p})=0, r_p({q})=-1/2, r_p({p,q})=-1,
r_q({q})=0, r_q({p})=-1/2, r_q({p,q})=-1,
h_t=1/(2+2^t), a_t=b_t=h_t, v_t(p)=v_t(q)=-h_t.
```

Here `A_p=A_q=-1`, `B_p=B_q=-1/2`, and `rho_p=rho_q=1/2`. Equation (5) is
exactly `h_{t+1}=h_t/(2(1-h_t))`. Every root is strictly mixed and exact
endpoint Nash, Bellman recursion is exact, the hazards are summable, and the
tail has positive Never mass.

### Degenerate case

Set every reward to zero, so all `A` and `B` values vanish. Let
`a_t=b_t=1/(t+2)` and `v_t=0`. Every root is strictly mixed, exact
Nash--Bellman, and diffuse, but both hazard series diverge and the survival
product is zero. Thus nonzero off-diagonal entries are essential.

Strict mixing is also essential because otherwise endpoint equality is
unavailable. Eventual two-player support is essential because a third active
player introduces additional coalition terms.

## 6. Source/provenance audit

The local endpoint calculations are close to checked declarations in
`Research/Quitting/PairActiveSoloPhase.lean`, especially
`quittingRootQuitPayoff_pair_active`,
`quittingRootContinuePayoff_pair_active`, and `pairActive_indifference`. The
new content is the consecutive-date recurrence and exact summability
classification.

What is absent is an adapter from the maintained Fin4 hard residual to the
complete hypothesis bundle:

- one literal forward root sequence;
- eventual support exactly `{p,q}`;
- strict mixing by both players at every late date;
- exact Bellman annotations; and
- exact endpoint Nash at every late date.

A card-two nonprojective principal is table data, not such a chronology. The
canonical maximal paid/reset orbit is a left-prefix sequence of changing
actual sources, not automatically one forward two-clock strictly mixed tail;
its roots may also have one, three, or four active coordinates or binding pure
faces.

Positive conditional Never mass is not currently a terminal consumer,
returned block, or finite rank. The hard-residual frontier already retains
positive-Never/phantom behavior as an open obstruction. Thus this theorem
narrows only a hypothetical subbranch whose production has not been proved,
not a maintained hard-residual node in the export-gate sense.

## 7. Separation from maximal-orbit claims (11)--(12)

The statements

```text
sup_{m>n}(1-product_{k=n}^{m-1} c_k) -> 0,
sup_{m>n} sum_{k=n}^{m-1}(1-c_k) -> 0
```

follow immediately from summability of `1-c_k` and
`1-product c_k <= sum(1-c_k)`. They correctly show that late blocks of the
known maximal orbit cannot provide a fixed root-absorption charge floor.

They are not consequences of the clock-ratio theorem and should not count as
new clock-ratio progress. Nor do they exclude a different chronology using
the retained paid row, suffix atom, or reset dispatch; they exclude only the
direct use of later and later blocks of inserted maximal roots.

## Required repairs and export boundary

Before formalization, the statement should:

1. make post-cutoff quantifiers explicit;
2. state both `a_t->0` and `b_t->0` in the diffuse theorem;
3. use the exact zero/nonzero and sign classification above;
4. state positive Never mass conditionally from the cutoff;
5. avoid calling the conclusion projective; and
6. keep (11)--(12) with the already-known maximal-orbit material.

After repair the lemma is clean and formalizable, but belongs in `notes/`, not
`exports/`, unless paired with either a source-faithful producer from a named
hard-residual node into this exact chronology and a consumer of its
positive-Never output, or a maintained question that explicitly accepts this
subcase classification as a complete answer.
