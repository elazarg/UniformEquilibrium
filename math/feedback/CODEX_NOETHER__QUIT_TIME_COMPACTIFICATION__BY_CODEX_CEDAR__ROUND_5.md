# Second falsification review: the deadlock joint-phase block

Reviewer: `CODEX_CEDAR`

Note reviewed: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 22, Proposition 20 only.  I refreshed the shared conference
files before review.  This is independent of Gauss's existing fifth review.

## Verdict

`VALID_ORDINARY_MATHEMATICS_NOT_CHECKED_IN_LEAN`.

I found no falsifier.  The interval root exists, the exact elimination and
hazard identities check, all certificate inequalities have the right endpoint
and sign, and the literal table is exactly `FullCoreDeadlock.reward`.  The
checked block consumer keeps the target `X^0` fixed and covers unrestricted
behavioral deviations.  The positive result evades
`ReducedIdealSingletonLasso.debt_pos` precisely because its final phase has
two simultaneous active quitters and a positive-probability nonsingleton
outcome; it does not contradict or weaken that one-owner route no-go.

## Exact root and rational interval

For the displayed degree-eight polynomial, direct rational evaluation gives

```text
P(191/1000)
 = -1374675715873650310293/3906250000000000000000 < 0,

P(24/125)
 = 2923619984558827/59604644775390625 > 0.
```

Continuity therefore gives a root in the open interval.  No uniqueness is
needed: every root in this interval obeys the subsequent uniform bounds.  As
an additional falsification check, the elementary interval estimate

```text
P'(t) > 335+6112(191/1000)-2724(24/125)^2
          -99456(24/125)^3-206960(24/125)^4
          -115968(24/125)^5
       =11795914534343/30517578125>0
```

also shows that the certified interval contains only one root.

The denominator estimate is exact:

```text
D(t)>50-836(24/125)^2-344(24/125)^3
    =32708794/1953125>16.
```

The coefficient expansions

```text
20N-D=-50+590t-2124t^2+2104t^3+2096t^4,
3D-50N=150-1470t+4892t^2-5432t^3-5168t^4
```

are correct.  The first derivative has the note's positive lower bound
`492739863/7812500`, and its value at the left endpoint is
`165890386791/62500000000>0`.  The second derivative has the note's negative
upper bound `-2578173479/7812500`, and its value at the right endpoint is
`641729382/244140625>0`.  Since `D>0`, these comparisons give exactly

`1/20<y=N/D<3/50`.

## Elimination and hazard algebra

Expanding as polynomials in `t,y` gives coefficientwise

```text
A_1 F_0-A_0 F_1=D(t)y-N(t).
```

Substituting `y=N/D` in `F_1` and clearing `D^2` gives exactly

```text
D(t)^2 F_1(t,N(t)/D(t))=40t^2P(t).
```

At the selected root, `D>0`, `t>0`, and
`A_1=4t(1+2t)>0`; hence first `F_1=0` and then `F_0=0`.  There is no hidden
division by a possibly zero expression.

Writing `B=(1-2y-t)(1+y)`, direct denominator clearing also gives the two
displayed identities

```text
q_2[4(p_1q_3+q_1p_3)+q_1q_3]-1
  =F_0/[B(1+2t)],

3p_0+q_0(2p_2+q_2q_3)-(1+4t)
  =(1-2y-t)F_1/[(1-y)B(1+2t)].
```

All factors are positive on the certified interval.  Thus `(E0)` and `(E1)`
follow exactly.  The remaining identities do not use the resultant:

```text
p_0q_1-p_1=t,
q_3[1+2t]=1,
q_0q_1(2p_2+q_2q_1)=1.
```

For the last equality, `q_0q_1=1-2y-t` and the definition of `q_2` reduce its
left side to

```text
2(1-2y-t)-(1-4y-2t)=1.
```

The interval implications for `p_0,p_1,p_3` check directly.  For `q_2`, its
numerator lies in `(47/125,209/500)`.  Its denominator is decreasing in both
positive variables on this box; the actual corner bounds

```text
2279/3125 < (1-2y-t)(1+y) < 14889/20000
```

are already stronger than the note's coarse
`7224/10000 < ... < 75154/100000`.  These imply

```text
1/2<q_2<3/5,
2/5<p_2<1/2.
```

Thus all four active hazards are interior probabilities and every omitted
hazard is exactly zero.

## Literal source table

In
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean`,
`FullCoreDeadlock.reward` is definitionally

```text
1+deadlockMatrix who owner  for a singleton {owner},
0                            for every coalition of cardinality at least two.
```

Its four singleton columns are exactly

```text
R_0=(1,3,3,0), R_1=(4,1,-1,-1),
R_2=(0,2,1,2), R_3=(4,-2,0,1).
```

The zero double-quit payoff used at the joint phase is therefore literal
source data, not an arbitrary completion assumption.

## Three recursions and four indifferences

From the definitions of `X^2,X^0`,

```text
X^2_0=1, X^2_2=1,
X^0_0=1, X^0_2=1+2p_0,
X^0_1=1+4t, X^0_3=1/q_1,
```

where the last two identities are `(E1)` and `(E3)`.  At the joint phase the
inactive Continue values are

```text
C_0=4(p_1q_3+q_1p_3)+q_1q_3X^0_0,
C_2=-p_1q_3+q_1q_3X^0_2.
```

Equation `(E0)` gives `C_0=1/q_2=X^J_0`.  Substituting
`X^0_2=1+2p_0` makes `(E2)` exactly `C_2=1=X^J_2`.
The active coordinates obey their recursion because their Quit and Continue
endpoints coincide.

The four intended indifferences are:

- phase `0`, player `0`: `Quit=1=Continue=X^2_0`;
- phase `2`, player `2`: `Quit=1=Continue=X^J_2`;
- phase `J`, player `3`: `Quit=q_1` and
  `Continue=-p_1+q_1X^0_3=q_1`;
- phase `J`, player `1`: `Quit=q_3` and
  `Continue=-2p_3+q_3X^0_1=q_3`.

The last equality uses `p_3/q_3=2t`.  Hence every positive hazard is exactly
complementary.

## Eight inactive endpoint inequalities

The remaining cases are exhaustive and strict.

- At phase `0`, each spectator's Quit endpoint is `q_0<1`; its Continue
  values are `1+4t`, `1+2p_0`, and `1/q_1`, all greater than one.
- At phase `2`, each spectator's Quit endpoint is `q_2<3/5`; its Continue
  values are `1`, `2p_2+q_2q_3`, and `2p_2+q_2q_1`, the last two greater
  than `4/5`.
- At phase `J`, each inactive player's Quit endpoint is `q_1q_3<1`; its
  Continue value is respectively `1/q_2>1` or `1`.

These are the `3+3+2=8` zero-hazard cases.  They have precisely the sign
required by `IsQuittingBlockCertificate.gain`: Quit-minus-Continue is
nonpositive.

## Remaining certificate fields and consumer

With `m=2`, the hazard list has three product-root phases and the value path
`U=(X^0,X^2,X^J,X^0)` has four rows.  The last row is literally the first.
The box audit is sound:

- `X^J in [0,2]^4`;
- `X^2` is a convex combination of `R_2` and `X^J`, both in `[0,2]^4`;
- `X^0` is a convex combination of `R_0 in [0,3]^4` and `X^2`.

The source table contains an absolute payoff of four, so
`4<=quittingRewardBound reward`, which is sufficient for every displayed
row.  The solo-`0` phase already absorbs because `p_0>0`.  Finally every own
singleton payoff is one, so every player satisfies the nonnegative-solo arm
of `admissible`; no player-deleted contraction has been silently assumed.

The theorem
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` concludes
exactly

```text
(quittingGame reward).IsUniformEquilibriumPayoff none (U 0).
```

Thus the target is the one fixed vector `X^0`, and the deviation class is all
behavior strategies.

## Exact scope of the lasso evasion

`ReducedIdealSingletonLasso` in
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`
stores one `owner` and one ideal-singleton clearance update at each phase.
Its theorem `ReducedIdealSingletonLasso.debt_pos` rules out zero debt only for
that reduced one-owner cycle class.

The last phase here gives positive Quit probability simultaneously to players
`1` and `3`.  In particular, the joint outcome has probability `p_1p_3>0`,
and its zero nonsingleton reward enters the exact recursion.  Sequentially
splitting the phase into singleton owner rows would remove that joint outcome
and change the Bellman equations.  Hence this block is outside the lasso
hypothesis in substance, not merely notation.  Proposition 20 proves a
uniform payoff only for the literal zero-multiquitter completion; it does not
settle all `IsFullCoreDeadlockCompletion` tables.

No Lean file was created.  The new algebraic certificate itself has no `L`
seal until formalized, although its source table and downstream conditional
consumer are checked declarations.
