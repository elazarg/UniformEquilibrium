# A zero-hazard handoff fails on the paired two-parameter slice

Author: CODEX_NOETHER_SUPPORT.

Status: bounded computer-assisted ordinary mathematics, not independently
reviewed or Lean-checked. An exact contact and two strict crossing signs
refute a particular local support-drop rule. A single fixed-band test of the
different four-phase construction is inconclusive. No full-slice exclusion,
root-count theorem, UE failure, or export is claimed. The separately reviewed
three-state equilibrium proof and its certificate remain unchanged.

## 1. Raw slice, symmetry, and known produced portions

Use the literal table of
[the three-state closure](../notes/CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_THREE_STATE_NASH_BELLMAN_CLOSURE.md),
except replace its four directed high entries by

```text
r0(02)=a,   r2(12)=a,   r1(13)=b,   r3(03)=b,
1≤a≤2, 1≤b≤2.
```

All within-pair member entries remain 2, opposite cross members remain 1,
and singleton, passive, triple, grand, live and Never rows are unchanged.
Private clocks are independent, and deviations are unrestricted behavioral
strategies, not periodic deviations.

The cyclic relabeling P=(0 2 1 3) preserves the fixed rows and rotates the
four directed high entries. Hence P²=(0 1)(2 3) sends the table (a,b) to
(b,a). This exact reward-table relabeling preserves all clocks and Never;
it suffices to examine the triangle a≤b. No affine payoff shift is involved.

The following portions have already produced original-game equilibria in
the current notes:

- The square [1,6/5]² is contained in the
  [independent cross-reward rectangle](../notes/CODEX_NOETHER_SUPPORT__INDEPENDENT_CROSS_REWARD_BOX_PERIOD_TWO_SOURCE.md).
- The entire diagonal a=b=h belongs to the
  [oriented two-to-four-phase handoff](../notes/CODEX_NOETHER_SUPPORT__ORIENTED_PAIR_REWARDS_TWO_TO_FOUR_PHASE_HANDOFF.md):
  two phases for h≤8/5 and four for h≥8/5, with overlap.
- The reported row-sum stationary sources add the point (2,2), already on
  that diagonal. The row sums in this slice are (a+3,b+3,a+3,b+3), so a
  common row sum in [5,6] forces a=b=2, while four sums at least 29/5 are
  impossible. This is a comparison with those producers, not stationary
  nonexistence elsewhere.
- The reviewed three-state certificate solves (a,b)=(8/5,2), and relabeling
  solves (2,8/5). No open parameter region is imported from that proof.

Cheap pure/normal tests do not dispose of the remaining slice. Every pure
nonempty coalition has a profitable membership toggle, uniformly in a,b:
a singleton has a cross outsider gaining at least 1; a within pair has a
member improving from 2 to its partner singleton payoff 4; a cross pair
has a zero-paid outsider joining to receive 1. For triples 012,013,023,123,
respectively players 1,0,0,1 can leave and gain 1. A grand-coalition member
can leave and gain at least 1. All-Never has singleton gain 1. Further,
every owner's punishment value is exactly zero: Never guarantees nonnegative
payoffs from every excluding coalition; three opponents sure-Quit limit its
best response to zero rather than grand reward −1.

These facts are not no-UE certificates. In particular the diagonal and the
reviewed off-diagonal point satisfy these same exclusions and are solved.

## 2. One precise boundary operation

Fix the top edge b=2. Start with the discovered chronological word

```text
023 | 012 | 013
```

and its nine-rate order

```text
h=(q00,q02,q03,q10,q11,q12,q20,q21,q23).
```

The proposed transition is: when q10 reaches zero, retain the other eight
rates as a jointly reselected equilibrium branch of the reduced word
023|12|013. Nothing in finite-game Nash existence guarantees the newly
quiet player's inequality. The exact calculation below checks this missing
condition rather than identifying an active-equation root with Nash.

Use the actual polynomial equations F_ti from Section 2 of the frozen
three-state proof, but with raw entries a in both 02 and 12. In particular

```text
F_ti = D(Q_ti−H_ti)−d_ti W_(t+1),i,
D=1−c0 c1 c2.
```

All counterfactual grand and triple terms remain in Q and H. The nine
active labels before the transition are 00,02,03,10,11,12,20,21,23.

At the contact set q10=0 and regard a as an unknown replacing that hazard.
There is a unique zero of all nine F's in the radius 10⁻⁶ sup-norm box
around the following exact rational decimal center, in order
(q00,q02,q03,a,q11,q12,q20,q21,q23):

```text
(.242380904838369,.117097521503689,.066981662274761,
 1.734302259292673,.208873697214118,.224194672194819,
 .094482875251960,.095010892632442,.239817592202553).
```

Write a* for this exact contact parameter. In particular 17/10<a*<7/4.
All eight nonzero hazards are in (0,1/4). The three previously quiet
numerators F01,F13,F22 are strictly below −1/6; the new quiet F10 is zero.
The actual absorption denominator lies in (7/10,4/5), and every one-row
deleted survival is less than 5/6. Thus the contact itself is an actual
exact terminal equilibrium, not an inadmissible polynomial point.

No exact continuation from the previously certified point a=8/5 to this
contact has been proved or is needed here. This is an exact contact of the
same original-table equations, not a certified first boundary of that
particular numerical component.

## 3. Exact crossing directions: neither local chart survives to the right

Let Φ(h,a) be the nine cleared active equations before dropping q10.
Both its full nine-rate Jacobian and the reduced eight-rate Jacobian are
invertible at the contact. Therefore the local full active-equation branch
h(a) and the local reduced branch h̃(a), with q10 fixed zero, are well defined
and differentiable. The reduced branch solves the other eight equations;
its remaining Quiet inequality still has to be checked.

The same rational interval calculation gives

```text
−1/8 < (d/da) q10(a*) < −1/12,                       (1)
 1/5 < (d/da) F10(h̃(a),a) at a* < 1/4.              (2)
```

Consequently, for all sufficiently small ε>0:

- the full nine-role branch at a*+ε has q10<0 and is not a strategy;
- the reduced eight-role branch has F10>0, so the now-quiet player 0 has a
  profitable current Quit deviation at its positively reached phase 1.

This refutes the literal operation “drop the role that reaches zero and
continue the reduced root.” It does not exclude a distant root of either
support grammar or an independently selected equilibrium with another
support or calendar. In fact both these local branches are legal immediately
to the LEFT of the contact; the boundary is not a proof of global loss.

### Certificate and derivative verification

The complete exact test is

```text
PYTHONDONTWRITEBYTECODE=1 python \
  experiments/CODEX_NOETHER_SUPPORT__PAIRED_SLICE_ZERO_HAZARD_CONTACT.py
```

The [owned script](../experiments/CODEX_NOETHER_SUPPORT__PAIRED_SLICE_ZERO_HAZARD_CONTACT.py)
imports the frozen literal polynomial evaluator read-only. Its temporary
ten-component derivatives represent nine rates and the one raw parameter a;
only in-memory data are changed. The contact Jacobian uses parameter column
9 instead of rate column 3, while all other columns retain their labels.
Rational Gaussian elimination, with inverse multiplication checked exactly,
and the same contraction argument as in the frozen proof give a unique
contact zero: the Newton correction is below 10⁻⁹, the interval operator
norm is below 1/100, and the image displacement is below radius/50.

For completeness, the derivative enclosure does not invert an interval
matrix heuristically. For each actual derivative equation Jy=−f_a, choose
the exact center inverse A and center solution y0. If
ε=||Id−AJ||<1, then

```text
||y−y0||∞ ≤ ||A(−f_a−Jy0)||∞/(1−ε).                 (3)
```

The right side is bounded by rational interval arithmetic, uniformly over
the contact box. Formula (3) gives (1). Applying it to the eight retained
equations and then evaluating
∂_aF10 + D_h F10 · h̃′ gives (2). The cleared numerator and the actual
Quit gap have the same crossing sign because D>0 and F10=0 at contact.
Parametric contraction, or its elementary implicit differentiation, supplies
the local branches; no generic regularity assumption about all Nash roots
is made.

## 4. One different fixed-band test, and the stopping boundary

The older four-phase word 02|12|13|03 is a genuinely different possible
dispatch. At the contact a* a numerical root of its exact four-equation
system has both small quiet slacks approximately 0.0267 and 0.0275, with
the other quiet slacks positive. This is diagnostic only; it neither
certifies a root nor yields a uniform raw interval.

One fixed interval test was made on the declared raw band

```text
a∈[17/10,7/4], b=2.
```

It uses the high-cycle equations and complete quiet tests in Section 5 of
[the unequal-high system note](../notes/CODEX_NOETHER_SUPPORT__THREE_MATCHING_FAILURE_AND_UNEQUAL_HIGH_CYCLE_SYSTEM.md).
The four low-role Continue probabilities are enclosed in a radius 1/100
cube centered at the rational decimals

```text
(.756797160998065,.788350570071128,
 .815835502748927,.781314552938357).
```

The center preconditioner is the exact inverse of the four-equation Jacobian
at a=69/40. Natural rational interval evaluation gives an operator bound
between 47/100 and 49/100, a preconditioned center-residual enclosure norm
between 13/1000 and 14/1000, and a resulting image-radius bound divided by
1/100 between 9/5 and 19/10. Thus this sufficient inclusion test fails.
All four first-quiet signs are strictly positive on the
box, but two second-quiet sign enclosures contain zero.

The script reproduces these exact bounds and labels the result
FAILED TO CERTIFY, not nonexistence. The raw band was not shrunk, subdivided,
or searched for optimized radii. Interval dependency can itself account for
this failure; no actual bad root in the band follows from it.

The current exact result is therefore the failed local zero-hazard handoff,
plus an inconclusive attempt at a different uniform four-phase dispatch.
The covered square, diagonal and reviewed off-diagonal point do not yet
form an exhaustive table-based selector for the two-parameter slice.
This bounded pass stops here. The missing datum is actual rate production
and all quiet signs for a different source-selected branch across this boundary,
not a theorem that root continuation must preserve one chosen component.
