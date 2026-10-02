# Seventh review: rational polyhedral full-core block

Reviewer: `CODEX_GAUSS`

Target: Section 24, Proposition 22 of
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md).

Verdict: `VALID` as ordinary mathematics.  This is a second independent
falsification review of the fixed rational block and its all-behavior
consumer.  I recomputed the three recursions, four active indifferences,
eight inactive endpoint inequalities, box and admissibility fields, and the
actual-family adapter.  I found no mathematical objection.  I also give a
stronger exact member of the polyhedron with no pure sure-exit set, no
instant-no-join owner, and no balanced singleton cycle.  Proposition 23's
later implicit-function thickening is outside this review.

The externally supplied file
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean`
was present but untracked at this refresh.  I did not build it and do not use
it as Lean evidence.  Proposition 22 and all raw-table calculations below
remain ordinary mathematics, not Lean-checked adapters.

## Claim and exact data

Let `Player=Fin 4`, let

```text
M = [ 0  3 -1  3
      2  0  1 -3
      2 -2  0 -1
     -1 -2  1  0 ],
```

and choose an arbitrary baseline `s in R^4`.  Impose

`r({j})_i=s_i+M(i,j)` and `r({1,3})=s`.

The claimed block has phases with supports `{0}`, `{2}`, `{1,3}`, hazards

```text
(p_0,p_1,p_2,p_3)=(4/21,1/15,7/17,5/26)
(q_0,q_1,q_2,q_3)=(17/21,14/15,10/17,21/26)
```

and values

```text
X^J=s+(7/10,0,0,0),
X^2=s+(0,7/17,0,7/17),
X^0=s+(0,5/7,8/21,1/7).
```

The eight caps are exactly those displayed in the note.

## Singleton-family equality

Since `M(i,i)=0`, the own singleton payoff of player `i` is `s_i`.
Therefore

`r({j})_i-r({i})_i=M(i,j)`.

The declaration `normalizedSoloMatrix_eq_projectiveLCPMatrix`
(`UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`)
identifies this difference table with `normalizedSoloMatrix r`.  Thus the
singleton hypothesis implies `IsFullCoreDeadlockCompletion r`.  Conversely,
if that named predicate holds, set `s_i=r({i})_i`; its matrix equality forces
all singleton coordinates to have the displayed form.  The row `{1,3}` and
the eight caps are extra raw-data restrictions, not consequences of the
named family.

## Exact on-path recursions

Subtract `s` coordinatewise.  The two solo phases give

```text
(7/17) M(*,2)+(10/17)(7/10,0,0,0)
  =(0,7/17,0,7/17),

(4/21) M(*,0)+(17/21)(0,7/17,0,7/17)
  =(0,5/7,8/21,1/7).
```

At the joint phase, the event masses for `{1}`, `{3}`, `{1,3}`, and the
empty coalition are

```text
7/130=21/390,  7/39=70/390,
1/78=5/390,    49/65=294/390.
```

They sum to one.  Coordinate `0` has excess

`3(21+70)/390=273/390=7/10`.

Coordinate `2` has excess

`-2(7/130)-7/39+(49/65)(8/21)=0`.

For coordinate `1`, the excess is

`-3(70/390)+(5/7)(294/390)=0`,

and for coordinate `3` it is

`-2(21/390)+(1/7)(294/390)=0`.

Thus the joint successor is exactly `X^J`.  Adding the arbitrary vector `s`
back is legitimate because at each phase the absorbing coalition weights
and continuation weight sum to one.

## Active endpoint equalities

All four active hazards are strictly interior.

- At phase `{0}`, Quit gives `s_0`, equal to `X^2_0`.
- At phase `{2}`, Quit gives `s_2`, equal to `X^J_2`.
- At phase `{1,3}`, player `1` gets `s_1` when it Quits whether or not
  player `3` co-quits.  On Continue its excess is
  `(5/26)(-3)+(21/26)(5/7)=0`.
- At the same phase, player `3` gets `s_3` when it Quits, while its Continue
  excess is `(1/15)(-2)+(14/15)(1/7)=0`.

These are the four required active indifferences.

## The eight caps are an iff for this fixed block

At phase `{0}`, a zero-hazard spectator `i` obtains

`q_0 s_i+p_0 r({0,i})_i`

by Quitting.  Comparison with the three spectator coordinates of `X^0`
gives precisely

```text
r({0,1})_1-s_1 <= 15/4,
r({0,2})_2-s_2 <= 2,
r({0,3})_3-s_3 <= 3/4.
```

At phase `{2}`, comparison with `X^2` gives precisely

```text
r({0,2})_0-s_0 <= 0,
r({1,2})_1-s_1 <= 1,
r({2,3})_3-s_3 <= 1.
```

At the joint phase the inactive player sees weights `294,21,70,5` over its
own singleton, the two pair collisions, and the triple collision.  After
subtracting its baseline and multiplying by `390`, the two comparisons are

```text
21[r({0,1})_0-s_0]+70[r({0,3})_0-s_0]
  +5[r({0,1,3})_0-s_0] <= 273,

21[r({1,2})_2-s_2]+70[r({2,3})_2-s_2]
  +5[r({1,2,3})_2-s_2] <= 0.
```

There are three inactive players at each solo phase and two at the joint
phase, so these eight comparisons are exhaustive.  Every unlisted
nonsingleton coordinate is absent from both the on-path law and all one-player
endpoint comparisons.  With the singleton and `{1,3}` equalities fixed, the
caps are therefore necessary and sufficient for this particular displayed
hazard/value block.  Violating a cap makes its associated inactive player
strictly prefer Quit at that phase; it says nothing about other blocks.

## Box, absorption, information, and consumer

All hazards are private independent Boolean coins; the public phase is the
date modulo three.  Phase `{0}` has positive absorption.  After deleting any
one player's hazards, at least one opponent still has positive hazard during
the period: player `0` sees player `2`, and players `1,2,3` see player `0`.
Thus every deleted-player period has Continue mass strictly below one, so the
first admissibility branch holds even for negative `s_i`.

The closed affine recursion is contracting because one period has absorption.
Hence its displayed solution is the actual eventual absorbing-payoff
expectation of the periodic product block.  Every coordinate is consequently
a convex combination of raw reward coordinates and lies in the canonical
`quittingRewardBound` box.  Arbitrarily large unused coordinates only enlarge
that bound.

These checks supply every field of `IsQuittingBlockCertificate`.  The checked
theorem `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`
(`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`) gives the one
fixed target `X^0` against replacement of any one player's entire behavioral
strategy.  This is terminal/uniform-payoff semantics, uses no public random
device, and is not restricted to stationary or one-shot deviations.

## Stronger exact nonoverlap witness

The note's all-ones witness separates the class from the capped-joint
producer, but it has easy pure sure exits.  The following exact member gives
a stronger boundary test.  Take `s=(1,1,1,1)`, keep the forced singleton rows

```text
r0=(1,3,3,0), r1=(4,1,-1,-1),
r2=(0,2,1,2), r3=(4,-2,0,1),
```

and set

```text
r01   =(-2, 4, 2, 2)     r02   =( 1, 0,-2, 5)
r03   =( 1,-1,-1,-3)     r12   =( 5,-4,-1, 5)
r13   =( 1, 1, 1, 1)     r23   =(-2, 4,-3, 1)
r012  =( 0, 1,-3, 0)     r013  =( 4,-4, 5,-3)
r023  =( 1,-2, 2, 3)     r123  =(-1,-2,-4, 5)
r0123 =(-3, 1,-1, 4).
```

In the order of the eight caps, their left sides are

```text
3, -3, -4, 0, -5, 0, -48, -347,
```

while the right sides are

```text
15/4, 2, 3/4, 0, 1, 1, 273, 0.
```

Thus the table lies in Proposition 22's polyhedron.

Every coalition has the following strict destabilizing deviation; the first
number is the deviator and the verb is its action:

```text
empty: 0 joins       {0}: 1 joins       {1}: 3 joins
{2}: 0 joins         {3}: 1 joins       {0,1}: 0 leaves
{0,2}: 1 joins       {0,3}: 0 leaves    {1,2}: 1 leaves
{1,3}: 0 joins       {2,3}: 0 joins     {0,1,2}: 0 leaves
{0,1,3}: 1 leaves    {0,2,3}: 1 joins   {1,2,3}: 1 leaves
{0,1,2,3}: 0 leaves.
```

For reproducibility, the corresponding current-to-deviation payoff pairs are

```text
0->1, 3->4, -1->1, 0->1, -2->1, -2->4, 0->1, 1->4,
-4->2, 1->4, -2->1, 0->5, -4->-1, -2->1, -2->4, -3->-1.
```

Hence no coalition, including the empty coalition, is a pure sure-exit set.
Every proposed instant-no-join owner also fails: owners `0,1,2,3` are broken
respectively by outsiders `1,3,0,1`, with strict singleton-to-pair gains

```text
3->4, -1->1, 0->1, -2->1.
```

There is no `BalancedSingletonCycleCertificate` either.  This last statement
depends only on the singleton rows and can be checked by the same exact
deadlock-lasso reduction, which I rederive here.  Delete zero-hazard phases
and combine adjacent equal owners.  Opponent divergence leaves at least two
positive-hazard phases with adjacent distinct owners.  For each retained
phase subtract the coordinatewise baseline `s` from its coarse value; the
solo-floor field gives a nonnegative clearance `v_n`.  If `a_n` is the owner
and `sigma_n` the survival, the arc and active fields say

```text
v_n=(1-sigma_n) M(*,a_n)+sigma_n v_(n+1),
v_n(a_n)=v_(n+1)(a_n)=0.
```

Read the phases in reverse cyclic order.  Use incoming clearance
`v_(n+1)`, survival `sigma_n`, and owner `a_n`.  The outgoing clearance is
exactly `v_n`; because it is nonnegative, the clipping maximum in
`idealSingletonClearance` is inactive.  The incoming owner clearance is zero
and every opponent affine update is nonnegative, so every local debt cost is
zero.  Identically zero debt would therefore form a
`ReducedIdealSingletonLasso`, contradicting the checked
`ReducedIdealSingletonLasso.debt_pos`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`).

Thus this literal member is simultaneously outside the named sure-exit,
instant-no-join, and balanced-singleton producers.  It also fails the
unit-solo/capped-joint hypothesis, for example player `1` receives `4>1` in
coalition `{0,1}`.

It also lies outside every **common-box** playerwise face-gap certificate of
Proposition 10.  Put every
opponent Quit probability equal to `t` and form player `0`'s division-free
stationary numerator

`N_0(t)=(1-(1-t)^3)R_0(t)-W_0(t)`.

Direct expansion from the displayed raw rows gives

```text
R_0(t)=1-3t+8t^2-9t^3,
W_0(t)=8t-12t^2+3t^3,

N_0(t)=t(-5+31t^2-54t^3+35t^4-9t^5).
```

Equivalently, `N_0(t)=-t Q(t)`, where

`Q(t)=5-31t^2+54t^3-35t^4+9t^5`.

The degree-five Bernstein coefficients of `Q` on `[0,1]` are

`(5,5,19/10,11/10,1,2)`,

all strictly positive.  Hence `N_0(t)<0` for every `0<t<=1`.  On any common
box `[alpha,beta]^4` with `alpha>0`, the all-`alpha` corner belongs to the
lower face of every candidate coordinate and has `G_0<0`, since the
denominator is positive.  No assignment can therefore give player `0` the
required uniformly positive lower face.  This rules out every Proposition 10
common-box playerwise face-gap certificate.  It does **not** rule out the
stronger checked coordinatewise-rectangle theorem in `ConditionalFaceGap.lean`:
for nonconstant lower bounds, the all-lower corner need not lie on the
diagonal used by this calculation.

The table is thus outside four independently named positive languages, but
this still does not prove exclusion from every possible repository producer
or from other block certificates.

## Novelty and scope

The checked predicate `IsFullCoreDeadlockCompletion` fixes only the singleton
comparison matrix; it supplies no strategy.  The literal table
`FullCoreDeadlock.reward` has `s=(1,1,1,1)` and all nonsingleton rows zero,
whereas Proposition 22 requires `r({1,3})=s` and uses different rational
hazards.  The untracked external literal-table file, even if later checked,
does not state this polyhedral raw-data adapter.

The paper-facing non-Q result `theorem5_1_nonQ`
(`Literature/SolanAndSolan2020.lean`, Section 5.1 / paper Theorem 5.1(1)) does
not apply to the nonhomogeneous standard-Q deadlock matrix.  Proposition 22's
new content is a rational, nonlocal, unbounded polyhedral slice of the named
full-core family with an exact all-behavior block consumer.  It is not a
producer for every full-core completion and not a solution of the finite
quitting conjecture.

No mathematical gate objection remains in the fixed-block proof.  The
stronger witness materially improves the producer-overlap audit, including an
exact common-box face-gap exclusion, but an export packet should retain the
final qualification that exclusion from the integrated arbitrary-rectangle
face-gap theorem and every other checked producer has not been proved.
