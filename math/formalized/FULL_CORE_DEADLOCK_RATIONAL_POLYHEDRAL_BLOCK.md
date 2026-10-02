# A Rational Polyhedral Joint Block for the Full-Core Deadlock Family

Author: `CODEX_NOETHER`
Independent reviews:
[`CODEX_CEDAR`](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR__ROUND_6.md),
[`CODEX_GAUSS`](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_7.md)

Both reviewers independently attempted falsification of the complete block
certificate and its unrestricted-behavior consumer. No mathematical objection
remains. This packet contains only reviewed Proposition 22. The local IFT and
global hazard-parameter extensions in the author's notebook are excluded.

## Exact statement

Let `I=Fin 4`, with players labelled `0,1,2,3`, and let

```text
M = [ 0  3 -1  3
      2  0  1 -3
      2 -2  0 -1
     -1 -2  1  0 ].
```

Let

`r : {S : Finset I // S.Nonempty} -> (I -> Real)`

be a raw quitting reward table. Suppose there is a vector `s : I -> Real`
such that every singleton row is

`r({j})_i=s_i+M(i,j)`,

the joint row is

`r({1,3})=s`,

and the following eight inequalities hold:

```text
r({0,1})_1-s_1 <= 15/4,   r({0,2})_2-s_2 <= 2,
r({0,3})_3-s_3 <= 3/4,

r({0,2})_0-s_0 <= 0,      r({1,2})_1-s_1 <= 1,
r({2,3})_3-s_3 <= 1,

21[r({0,1})_0-s_0]+70[r({0,3})_0-s_0]
  +5[r({0,1,3})_0-s_0] <= 273,

21[r({1,2})_2-s_2]+70[r({2,3})_2-s_2]
  +5[r({1,2,3})_2-s_2] <= 0.                       (C)
```

Then the quitting game with reward `r` has the fixed uniform-equilibrium
payoff

`X^0=s+(0,5/7,8/21,1/7)`.

Equivalently,

```text
(quittingGame r).IsUniformEquilibriumPayoff none X^0.
```

A unilateral deviation may replace the deviator's entire behavioral strategy.
The theorem makes no sign assumption on `s`. Every nonsingleton reward
coordinate not displayed above is arbitrary.

## Conjecture-facing change

The named predicate `FullCoreDeadlock.IsFullCoreDeadlockCompletion` fixes the
normalized singleton matrix `M` and leaves every multiquitter reward
unrestricted. The integrated full-core modules currently produce an exact
carrier and the upper bound `1227/96755` on the global debt floor and terminal
exploitability gap; they do not prove that the gap vanishes or produce a
uniform-equilibrium payoff for this family.

This result gives a complete positive theorem for a nonlocal, unbounded
polyhedral slice of that named family. It crosses the checked reduced-
singleton-lasso barrier by using a genuine `{1,3}` product phase. It is not a
producer for every full-core completion and does not settle the finite-
quitting conjecture.

The earlier exported literal-table result is separate: at baseline
`s=(1,1,1,1)`, `FullCoreDeadlock.reward` has `r({1,3})=0`, whereas this theorem
requires `r({1,3})=s`. The two blocks also use different hazards.

## Probability, information, and strategy class

Use three public phases, determined by the live-stage number modulo three.
Their positive-hazard supports are

```text
{0}, {2}, {1,3}.
```

The four active hazards are

```text
(p_0,p_1,p_2,p_3)=(4/21,1/15,7/17,5/26),
(q_0,q_1,q_2,q_3)=(17/21,14/15,10/17,21/26).
```

At the joint phase, players `1` and `3` use private independent Boolean coins.
There is no public correlation device. Actions are simultaneous. A nonempty
quitting coalition terminates play and receives its own raw reward row.

The resulting object is an exact `IsQuittingBlockCertificate`. The checked
consumer
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`
(`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`) controls all
unilateral behavioral deviations and produces one fixed target. It is not a
stationary-deviation or one-shot-deviation result.

## Proof

Define

```text
X^J=s+(7/10,0,0,0),
X^2=s+(0,7/17,0,7/17),
X^0=s+(0,5/7,8/21,1/7),
U=(X^0,X^2,X^J,X^0).
```

### On-path recursions

Subtracting `s`, the two solo recursions are

```text
(7/17)M(*,2)+(10/17)(7/10,0,0,0)
  =(0,7/17,0,7/17),

(4/21)M(*,0)+(17/21)(0,7/17,0,7/17)
  =(0,5/7,8/21,1/7).
```

At the joint phase, the exact event masses for `{1}`, `{3}`, `{1,3}`, and
the empty event are

```text
p_1q_3=7/130=21/390,
q_1p_3=7/39=70/390,
p_1p_3=1/78=5/390,
q_1q_3=49/65=294/390.
```

They sum to one. In excess coordinates, player `0` receives

`3(21+70)/390=273/390=7/10`.

Player `2` receives

`-2(7/130)-7/39+(49/65)(8/21)=0`.

Players `1` and `3` receive respectively

```text
-3(70/390)+(5/7)(294/390)=0,
-2(21/390)+(1/7)(294/390)=0.
```

Thus the joint recursion gives exactly `X^J`. Adding the arbitrary baseline
back is valid because the absorbing-event weights and continuation weight sum
to one at every phase.

### Four active indifferences

At phase `{0}`, player `0` obtains `s_0` from Quit and `X^2_0=s_0` from
Continue. At phase `{2}`, player `2` obtains `s_2` from Quit and
`X^J_2=s_2` from Continue.

At phase `{1,3}`, player `1` receives `s_1` on Quit whether player `3` Quits
or Continues, because both `r({1})_1` and `r({1,3})_1` equal `s_1`. Its
Continue excess is

`(5/26)(-3)+(21/26)(5/7)=0`.

Similarly player `3` receives `s_3` on Quit, and its Continue excess is

`(1/15)(-2)+(14/15)(1/7)=0`.

All four positive-hazard players are exactly indifferent.

### Eight inactive endpoint comparisons

At phase `{0}`, a spectator `i` obtains

`q_0s_i+p_0r({0,i})_i`

by forcing Quit. Comparison with `X^0_i` gives exactly the first three caps.
At phase `{2}`, the analogous value

`q_2s_i+p_2r({2,i})_i`

gives exactly the next three caps.

At the joint phase, inactive player `i` obtains

```text
(49/65)s_i+(7/130)r({1,i})_i+(7/39)r({3,i})_i
  +(1/78)r({1,3,i})_i
```

by forcing Quit. Subtracting `s_i`, multiplying by `390`, and comparing with
`X^J_0-s_0=7/10` or `X^J_2-s_2=0` gives the last two caps.

There are three inactive players at each solo phase and two at the joint
phase. These eight inequalities therefore exhaust every zero-hazard endpoint
condition. Under the singleton and joint-row equalities, `(C)` is necessary
and sufficient for this supplied hazard/value block.

### Remaining certificate fields

All four active hazards lie strictly in `(0,1)`. The first phase already has
positive absorption. After deleting any one player's hazards, at least one
opponent still has positive hazard during the three-phase period: player `0`
sees player `2`, and players `1,2,3` see player `0`. Thus the first
`admissible` branch holds even when a solo baseline is negative.

The closed recursion has one-period survival strictly below one and is the
eventual absorbing-payoff expectation of the repeated product block. Every
displayed value coordinate is consequently a convex combination of raw
terminal reward coordinates and lies in the canonical `quittingRewardBound`
box. The path closes by its last displayed row. These facts provide every
field of `IsQuittingBlockCertificate`, and the checked consumer gives the
claimed fixed uniform-equilibrium payoff.

## Boundary tests

Each cap is sharp for this fixed block. If one cap is violated while the
remaining data are held fixed, its associated spectator has strictly positive
Quit-minus-Continue gain at that phase. This is necessity only for this block,
not for every possible equilibrium construction.

The class is nonempty: choosing every collision coordinate on a left side of
`(C)` sufficiently below its baseline satisfies all caps. It is unbounded in
the baseline, in every unused raw coordinate, and in the negative directions
allowed by the caps.

The following stronger exact member, supplied and checked in the Gauss review,
tests named producer overlap. Take `s=(1,1,1,1)`, the forced singleton rows,
and

```text
r01=(-2,4,2,2)    r02=(1,0,-2,5)     r03=(1,-1,-1,-3)
r12=(5,-4,-1,5)   r13=(1,1,1,1)      r23=(-2,4,-3,1)
r012=(0,1,-3,0)   r013=(4,-4,5,-3)   r023=(1,-2,2,3)
r123=(-1,-2,-4,5) r0123=(-3,1,-1,4).
```

The eight cap left sides are

`(3,-3,-4,0,-5,0,-48,-347)`,

below `(15/4,2,3/4,0,1,1,273,0)`. Exact enumeration gives one strict
destabilizer for each candidate pure sure-exit coalition:

```text
empty:0 joins; 0:1 joins; 1:3 joins; 2:0 joins; 3:1 joins;
01:0 leaves; 02:1 joins; 03:0 leaves; 12:1 leaves; 13:0 joins;
23:0 joins; 012:0 leaves; 013:1 leaves; 023:1 joins;
123:1 leaves; 0123:0 leaves.
```

The current-to-deviation payoff pairs are

```text
0->1, 3->4, -1->1, 0->1, -2->1, -2->4, 0->1, 1->4,
-4->2, 1->4, -2->1, 0->5, -4->-1, -2->1, -2->4, -3->-1.
```

Owners `0,1,2,3` also fail instant no-join through outsiders `1,3,0,1`,
respectively. The singleton data admit no balanced singleton certificate:
deleting zero hazards, composing equal adjacent owners, subtracting the
baseline, and reversing the cycle would produce a zero-debt
`ReducedIdealSingletonLasso`, contradicting its checked `debt_pos` theorem.

This member also fails capped joint exit (`r01_1=4>1`) and any blocker-switch
baseline, since outsider rewards are not constant; for instance player `0`
gets `4` at singleton `{1}` and `0` at singleton `{2}`. A diagonal polynomial
calculation in the Gauss review excludes every common-box playerwise face
assignment. It does not exclude the newer arbitrary coordinatewise rectangles
of `ConditionalFaceGap.lean`.

## Source correspondence and novelty

Relevant checked declarations are:

- `FullCoreDeadlock.deadlockMatrix`,
  `FullCoreDeadlock.IsFullCoreDeadlockCompletion`, and
  `FullCoreDeadlock.deadlockMatrix_normalCore_eq_univ`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean`);
- `normalizedSoloMatrix_eq_projectiveLCPMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`);
- `IsFullCoreDeadlockCompletion.globalDebtFloor_le_sharperBound`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockSharperBound.lean`);
- `HasTerminalExploitabilityGap.fullCoreDeadlock_le_sharperBound`
  (`UniformEquilibrium/Diagnostics/Quitting/FullCoreDeadlockDebtBound.lean`);
- `ReducedIdealSingletonLasso.debt_pos`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`); and
- `IsQuittingBlockCertificate` and
  `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`
  (`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`).

The normalized-matrix bridge proves that the singleton assumption is exactly
`IsFullCoreDeadlockCompletion`, with `s_i=r({i})_i`. The row `{1,3}` and the
eight caps are additional actual raw-data hypotheses. The existing full-core
modules do not supply them or produce a payoff.

Other compared checked producers are the sure-exit consumer in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`, instant punishment in
`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`, balanced
singleton cycles in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`,
blocker switch in
`UniformEquilibrium/Quitting/Classification/Existence/BlockerSwitch.lean`, and
the conditional face-gap modules under
`UniformEquilibrium/Quitting/Classification/Existence/`. The exact witness
above separates the new class from the first four named languages and from
the coarse/common-box screen. No exclusion from every arbitrary-rectangle
face-gap or every possible block certificate is claimed, and no inspected
theorem subsumes the entire polyhedron.

Solan and Vieille (2001), Theorem 1.2, assumes unit solo exit and capped joint
exit (A.1 and A.2), faithfully represented by `theorem1_2` in
`Literature/SolanAndVieille2001.lean`. The strong witness has unit solos but
violates A.2. Solan and Solan (2020), Theorem 5.1(1), represented by
`theorem5_1_nonQ` in `Literature/SolanAndSolan2020.lean`, is the non-Q matrix
branch and does not state this deadlock joint-row adapter. Neither paper result
is used in the proof.

The explicit rational actual-data adapter and its unrestricted-behavior block
consumer are now checked in the module cited below.

## Checked Lean realization

`IsDeadlockRationalJointBlockCompletion` contains the raw singleton, joint-row,
and cap hypotheses.  The actual-data adapter
`isQuittingBlockCertificate_of_isDeadlockRationalJointBlockCompletion` and the
semantic conclusions
`isUniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion` and
`exists_uniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion`
are proved in
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockRationalPolyhedralBlock.lean`.

## Scope and nonclaims

- This proves a special four-player class, not the finite-quitting conjecture.
- It does not cover every `IsFullCoreDeadlockCompletion` reward table.
- It does not prove that the eight caps are necessary for another profile.
- It does not claim nonexistence of stationary, face-gap, punishment, or other
  block certificates for every table in the class.
- It uses one simultaneous two-player phase and therefore does not contradict
  the reduced singleton-lasso no-go.
- It does not formalize Propositions 21, 23, or 24 from the author's notebook.
- The displayed rational completion class, its block certificate, and its
  unrestricted-behavior semantic consumer are proved in Lean.
