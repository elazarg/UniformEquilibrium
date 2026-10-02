# Review of Euler Sections 26 and 28

Reviewer: `CODEX_CEDAR`

Scope: only Proposition 20's quantitative iid common-clock deletion bound and
Proposition 22's exact common-clock chronological drift theorem in
`notes/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE.md`.

## Verdict

Both propositions are **VALID ordinary mathematics** in their stated common-
clock scopes.  I found no error in the deletion exponent, constants, reached-
history conditioning, or drift orientation.  Neither result applies to
asymmetric clocks, approximate late conditional Nash after division by small
reach probability, or a macroblock with order-one collision mass.

## Proposition 20

Let `p_t` be the finite atom masses, `p_infty` the Never mass, and
`delta=sup_t p_t`.  The four-clock bad mass

```text
ell_4=Pr(first coalition is nonsingleton or Never)
```

contains the fourfold tie at every finite atom, hence
`delta^4<=ell_4`.  It also contains fourfold Never, so with
`x=ell_4^(1/4)` one has `delta<=x` and `p_infty<=x`.

For three iid clocks, the exact finite collision mass is

```text
sum_t (3 p_t^2 R_t+p_t^3),
```

where `R_t=Pr(T>t)`.  Since `p_t<=delta` and
`sum_t p_t(p_t+R_t)<=1`, it is at most `3 delta`.  Adding threefold Never
gives

```text
ell_3<=3x+x^3.
```

Exchangeability makes the good singleton outcomes uniform.  Replacing bad
mass `ell_j` by the ideal singleton average changes a payoff bounded by `R`
by at most `2R ell_j`.  Therefore the prescribed four-clock payoff and the
Never-deviation three-clock payoff together differ from their ideal values by
at most

```text
2R(ell_4+ell_3)
 <=2R(x^4+3x+x^3)
 <=10Rx.
```

The ideal prescribed and Never values are respectively
`B_0+sigma/4` and `B_0+sigma/3`, so the ideal gain is `sigma/12`.  This proves

```text
exploitability >= sigma/12-10R ell_4^(1/4).
```

If exploitability is below `sigma/24`, then
`ell_4^(1/4)>sigma/(240R)`, which implies the displayed weak lower bound
`ell_4 >= (sigma/(240R))^4`.  The qualitative liminf follows when
`ell_4->0`.  The definition of `ell_4` must retain both collision and Never;
with that definition all estimates and the fourth-root exponent check.

## Proposition 22

At an interior common root `h`, exact conditional support indifference at a
positive-probability reached history gives

```text
u_t=Q(h),
u_(t+1)=S(h)=[Q(h)-W(h)]/(1-h)^3.
```

The conditioning is legitimate for unrestricted behavioral strategies: a
deviator can copy the prescribed strategy until that public history and then
change its current action.  Every finite history remains positively reached
before a sure root.

At zero,

```text
Q(0)=S(0)=B_0,
W'(0)=C_0+2A_1=3B_0+sigma,
S'(0)=Q'(0)-sigma.
```

Thus `(Q-S)'(0)=sigma>0`, and for a sufficiently small fixed `h_0`

```text
Q(h)-S(h)>=(sigma/2)h
```

on `0<h<=h_0`.  This is exactly the forward chronological inequality
`u_t-u_(t+1)>=(sigma/2)h_t`; the sign and predecessor/successor ordering are
correct.

If eventually every root is at most `h_0`, telescoping and bounded payoffs
force `sum h_t<infinity`.  With no sure root this gives positive Never
probability but absorption probability from a late tail tending to zero, so
bounded rewards imply `u_t->0`.  Infinitely many positive rows contradict
this because there `u_t=Q(h_t)->B_0>0`; finitely many positive rows leave an
eventual all-Continue tail where immediate Quit gains `B_0>0`.  Hence, absent
a sure root, infinitely many rows must exceed `h_0`.

The proof uses exact terminal Nash essentially.  It does not yield a late
conditional error estimate for approximate Nash profiles, and it does not
screen asymmetric or genuinely changing root vectors.
