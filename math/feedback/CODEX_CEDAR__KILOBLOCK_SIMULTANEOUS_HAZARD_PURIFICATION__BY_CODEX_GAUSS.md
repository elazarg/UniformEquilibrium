# Paired Kiloblock Source and Refusal-Gap Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_CEDAR__KILOBLOCK_SIMULTANEOUS_HAZARD_PURIFICATION.md`](../notes/CODEX_CEDAR__KILOBLOCK_SIMULTANEOUS_HAZARD_PURIFICATION.md)

Scope: Sections 11--12, Propositions 9--10. I independently checked every
literal `BuildingBlock` field against the paper-facing definition, the
advance/absorption macro masses, positive scaling of the checked matrix
classes, the probability partition, blocker-clock bound, two-player coupling,
and the quantitative `1/72` limit. This is ordinary mathematics, not
Lean-checked.

## Verdict

**Propositions 9--10 are VALID ordinary mathematics as stated.** Proposition
9 is a literal source-data adapter: the scaled paired matrix supports the
displayed building block with active singleton masses `1/6,1/6` and advance
mass `2/3`. Proposition 10 proves a genuine fixed local refusal gap for every
finite time-inhomogeneous independent-clock implementation preserving that
payoff/survival data with vanishing collision mass.

The result is not a counterexample and not a global chained-block no-go. A
later reached block may still pay the present refusal premium. The
paper-facing `BuildingBlock` lane is non-built and contains `sorry`; the
review verifies the displayed ordinary data against its definition but adds
no Lean seal to that adapter.

## 1. Literal boundary and approach data

For `M=pairedSingletonMatrix/3`, the displayed columns are correct. Direct
coordinate substitution gives

```text
y=(1/5)c0+(1/5)c1+(3/10)c2+(3/10)c3=(0,0,1/6,1/6),
w=(3/10)c0+(3/10)c1+(1/5)c2+(1/5)c3=(1/6,1/6,0,0).
```

Both convex combinations are coordinatewise nonnegative and have zero
coordinates, so they satisfy the exact `DZero M` definition in
`Literature/SolanAndSolan2020.lean`.

For owners `0,1`,

```text
w^0=(2/3)y+(1/3)c0=(0,1/3,0,0),
w^1=(2/3)y+(1/3)c1=(1/3,0,0,0).
```

These are strict segments from `y` to their columns, hence advance attempts
with Quit weight `1/3`. For owners `2,3`,
`w^j=(1-h)y+h c_j` is also a strict `y`-to-column segment because
`0<h<1`. Its only negative coordinates equal `-h/3`; the chosen
`h=min(1/2,3epsilon/2)` gives `-h/3>=-epsilon`. All remaining coordinates are
nonnegative.

## 2. Balance, complementarity, and macro orientation

The public weights have cemetery mass zero and singleton masses
`z_0=z_1=1/2`, `z_2=z_3=0`. Therefore

```text
(1/2)w^0+(1/2)w^1=w.
```

The only positive-weight complementarity fields are
`(w^0)_0=0` and `(w^1)_1=0`; the positive public mass sums to one. This checks
all remaining `BuildingBlock` fields.

Both positive-weight attempts are in the `.advance` branch. Their singleton
absorption masses are

```text
(1/2)(1/3)=1/6,
```

and their nonquit advance masses are each `(1/2)(2/3)=1/3`, totaling `2/3`.
No restart mass is present. This is the macro orientation claimed in
Proposition 9.

Positive scalar multiplication preserves standard-LCP solvability by scaling
the right-hand side, and preserves the homogeneous complementarity equations.
Thus the checked
`pairedSingletonMatrix_standardQ` and
`pairedSingletonMatrix_noHomogeneous`
(`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`)
pass from the unscaled matrix to `M`. Every displayed column has a distinct
negative entry.

## 3. Exact probability partition and blocker bounds

For main coordinates `0,1`, unique singleton outcomes and zero continuation
tail give

```text
u_0=S_1-B/3+e_0,
u_1=S_0-B/3+e_1,
|e_i|<=C.
```

The unique-first, tie, and all-infinite events partition probability one:

```text
S_0+S_1+B+C+s=1.
```

Combining the two payoff lower bounds with this partition yields

```text
B <= (3/5)(sigma+2tau+C).
```

Let `r_j=P(T_j=infinity)` and
`kappa=P(T_2<infinity or T_3<infinity)=1-r_2r_3`. On the event that both main
clocks are infinite but a blocker clock is finite, the first outcome is a
unique blocker or a collision, so

```text
r_0r_1 kappa <= B+C.
```

Since `s=r_0r_1(1-kappa)` and `s>0`, rearrangement gives
`kappa<=(B+C)/(s+B+C)`. Ties and Never are both explicitly accounted for.

## 4. Coupling to the exact two-player refusal law

Force both blocker clocks to Never and set main-player tie payoff to zero.
The prescribed law changes only if a blocker is finite or the original block
collides. Rewards lie in `[-1,1]`, hence

```text
|u_i-u_i^*|<=2(kappa+C).
```

After deleting main owner `i`, the continuation law can differ only when a
blocker is finite. Combining that payoff comparison with the preceding
prescribed comparison gives the safe bound

```text
|(n_i-u_i)-g_i^*|<=4(kappa+C).
```

Proposition 4's independent-clock identity is correctly oriented:
`g_0^*+g_1^*>=u_0^*u_1^*`. Each ideal prescribed coordinate is at least

```text
L=1/6-tau-2(kappa+C).
```

When `L>0`, summing the two refusal caps and coupling errors gives

```text
2eta >= L^2-8(kappa+C).
```

## 5. Quantitative limit and exact scope

Under `(12.4)`, the first blocker bound gives `B->0`; the positive survival
limit and the second bound give `kappa->0`. Hence `L->1/6` and

```text
liminf eta >= (1/2)(1/6)^2=1/72.
```

This excludes the proposed local blockwise ordinary compiler. It does not
sum refusal gains along a causal chain, control a later compensation block,
or establish a uniform terminal gap for a fixed quitting reward table. Those
are the exact remaining obligations for the negative thesis.
