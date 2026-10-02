# Projective Moving-Chart Transition Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.10, Proposition 65.  I checked the exact transition identity,
the shifted application of Proposition 64, the recurrent-chart consequences,
and the iterated cycle formula.  This is ordinary mathematics, not
Lean-checked.

## Verdict

**The transition identity `(N76)`, recurrent identity `(N77)`, and cycle
identity `(N78)` are VALID ordinary mathematics.  Proposition 65 is NOT VALID
as stated because its sign conclusion omits the expanding-clock branch.**

**Post-review resolution.**  The author incorporated the correction while
this review was open.  The revised Proposition 65 states the two-branch sign
dichotomy, restricts local contraction to a chart occurring at every
sufficiently late edge, and restricts product contraction to a genuinely
repeated finite cycle.  I rechecked those quantifiers; **the revised
Proposition 65 is VALID ordinary mathematics with no remaining objection.**

The exact repair is small but substantive:

```text
z_i>0
  -> (R_i>0 and theta<1) or (R_i<0 and theta>1).
```

The advertised positive-residual/strict-contraction conclusion needs an
additional hypothesis such as `theta<=1`.  It also follows for one stable
chart occurring at every sufficiently late edge when `q_n->0` and the full
successive ratio converges, since then the ratio limit cannot exceed one.

## 1. Exact source-matching identity

For `v_n=(x_n-b)/q_n` and
`z_n=(x_n-x_(n+1))/q_n`, direct subtraction gives

```text
v_n=z_n+(q_(n+1)/q_n)v_(n+1).
```

No Bellman or Nash hypothesis is used in this equality.  On a subsequence of
consecutive positive-absorption edges, Proposition 64 gives

```text
v_(n),i -> R_i(mu),
v_(n+1),i -> R_i(mu')
```

whenever `i` is positive in both limiting occupations.  Passing to the finite
ratio limit proves

```text
R_i(mu)=z_i+theta*R_i(mu').
```

Thus `(N76)` is correct, subject to the background assumptions from
Proposition 64: exact Nash--Bellman edges, hazards tending to zero, both
endpoint values tending to the same `b`, and vanishing normalized collision.
These should be repeated explicitly if Proposition 65 is later exported or
formalized rather than left in the running tail context.

When `mu'=mu`, the residual depends only on the active occupation through the
pair-join formula, so `(N77)` follows exactly:

```text
z_i=(1-theta)R_i(mu).
```

## 2. Missing expanding-clock branch

From `(N77)` and only `theta>=0`, the numerical data

```text
theta=2,  R_i=-1,  z_i=1
```

satisfy the identity and have `z_i>0`.  Hence positive tangent does not by
itself force positive residual or contraction.  A summable positive sequence
with `q_n->0` may have `q_(n+1)/q_n>1` on infinitely many sparse consecutive
pairs, compensated by larger drops between them, so global summability does
not repair the local inference.

The exact sign table is

```text
z_i>0  <->
  (R_i>0 and theta<1) or (R_i<0 and theta>1),
z_i<0  <->
  (R_i<0 and theta<1) or (R_i>0 and theta>1).
```

For nonzero `R_i`, the ratio formula
`z_i/R_i=1-theta` remains correct and common across active coordinates.
At `theta=1`, `(N77)` does force `z_i=0` throughout the recurring positive
support.

## 3. When contraction is justified

If one stable chart governs every sufficiently late edge and the full ratio
`q_(n+1)/q_n` tends to `theta`, then `q_n->0` rules out `theta>1`: eventual
ratios bounded below by a number greater than one would make `q_n` increase
geometrically.  Under this stronger recurrence quantifier one has
`theta<=1`, and `z_i>0` indeed implies `theta<1` and `R_i>0`.

For a finite chart cycle repeated coherently, the analogous global condition
is on the product of the edge ratios around the whole cycle, not on every
individual edge.  Some local charts may expand while the cycle product
contracts.

## 4. Iterated cycle identity

Iterating

```text
R^a=z^a+theta_a R^(a+1)
```

around a cycle gives

```text
(1-product_a theta_a)R^0
  =sum_a (product_(b<a) theta_b)z^a,
```

so `(N78)` is correct.  Its useful sign consequences must use either the
whole-cycle product or additional signs on all `R^a,z^a`; the uncorrected
local contraction sentence cannot be inserted into that argument.

## Scope

The repaired theorem remains a useful necessary screen for moving-source
recurrence, not a packet producer or semantic conclusion.  It sharpens the
remaining obligation by distinguishing locally contracting and expanding
chart transitions.  The two-player example in Proposition 64 occupies the
contracting positive-residual branch, but it does not eliminate the expanding
negative-residual branch in a support-switching chronology.
