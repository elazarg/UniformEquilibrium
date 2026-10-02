# Review of Proposition 23.1 and Corollary 23.2

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

## Square and sign audit

Let `a` be a strictly stable label at the Proposition 22 corner `P`, let
`s` be its other certified stable label, and let `k` be the strict
destabilizer outside `{a,s}`.  With

```text
Q=P triangle {k},  R=P triangle {a},
W=P triangle {a,k},
```

the supplied strict comparisons are exactly

```text
P -> Q          (k prefers its action at Q),
R -> P          (a prefers its action at P).
```

The proposed case split is exhaustive:

- `r_Q(a)>=r_W(a)` makes `Q` stable for both coordinates, with `k`
  strictly stable.
- In the complementary case `Q->W` is strict, so `a` is strictly stable at
  `W`.  If `r_W(k)>=r_R(k)`, then `W` is stable for both coordinates.
- If that second weak inequality fails, `W->R` is strict and the four arrows
  are exactly `P->Q->W->R->P`.

Equality in either new comparison is correctly assigned to a stable-corner
arm.  There is no leftover sign chamber.

The strict-label premise is not an extra genericity condition.  At the `U`
corner of Proposition 22, `i` is strict by `T->U`; at its `V` corner, `b` is
strict by `U->V`.

## Empty coalitions and label agency

The convention `r_empty(j)=0` makes all four comparisons meaningful when one
of the vertices is empty.  In particular, if `P=empty`, strict stability of
`a` says `0>r_{a}(a)`, and the destabilizing edge says
`r_{k}(k)>0`.  The same square proof applies without a hidden nonempty-base
assumption.  A strict four-cycle with empty fixed base is exactly the case
handled by the Section 10 empty-base dispatcher.

Since `k notin {a,s}`, the old and new stable pairs are genuinely distinct.
At a returned corner, terminal failure cannot be witnessed by either of its
two stable coordinates; the next strict label therefore lies in the
complementary pair.  This is a membership statement at one literal coalition,
not an assertion that the corner is already a full equilibrium.

## Path and scope

The inherited path to `P` retains the original `gamma_(B,F)` edge.  Reaching
the new corner adds `P->Q`, and in the `W` arm also `Q->W`; it does not delete
any earlier path data.  The failed-square arm is a static strict four-cycle,
so the complete Section 10 semantic tests apply without an original-cycle
incidence assumption.

Corollary 23.2 accurately records only a finite stable-pair exchange state.
In the `Q` arm the surviving strict label may be `k`, not `a`, and the
corollary correctly says only “one strict.”  It makes no termination claim,
does not identify repetition of a pair with repetition of a coalition, and
does not promote a finite-state directed cycle to a quitting-game compiler.
