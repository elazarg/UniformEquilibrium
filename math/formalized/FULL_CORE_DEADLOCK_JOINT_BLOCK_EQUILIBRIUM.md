# A Joint-Phase Uniform Equilibrium for the Full-Core Deadlock Table

Author: `CODEX_NOETHER`
Independent reviews:
[`CODEX_GAUSS`](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_5.md),
[`CODEX_CEDAR`](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR__ROUND_5.md)

Both reviews independently attempted falsification and found no mathematical
objection. This packet contains only the reviewed concrete result. It excludes
the unreviewed local-neighborhood generalization in the author's notebook.

## Exact statement

Let `I=Fin 4` and let

```text
M = [ 0  3 -1  3
      2  0  1 -3
      2 -2  0 -1
     -1 -2  1  0 ].
```

For every nonempty coalition `S` and player `i`, define the quitting reward

```text
r(S)_i = 1 + sum_{j in S} M(i,j)  if |S|=1,
         0                         if |S|>=2.
```

This is definitionally `FullCoreDeadlock.reward` in
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean`.

There is a payoff vector `x : I -> Real` such that

```text
(quittingGame r).IsUniformEquilibriumPayoff none x.
```

Equivalently, with this one fixed `x`, for every `epsilon>0` there are one
behavioral profile and one threshold `T_0` such that, at every horizon
`T>=T_0`, the profile is an `epsilon`-Nash equilibrium of the expected-average
game and every payoff coordinate is within `epsilon` of `x`. A unilateral
deviation replaces the deviator's entire behavioral strategy.

More precisely, the proof constructs an exact three-phase
`IsQuittingBlockCertificate` whose supports are

```text
{0}, {2}, {1,3}.
```

The first two phases have one active quitter. The last phase has two players
mixing independently and has a positive-probability double-quit outcome.

## Definitions and assumptions

The four singleton reward columns are

```text
R_0=(1,3,3,0),   R_1=(4,1,-1,-1),
R_2=(0,2,1,2),   R_3=(4,-2,0,1).
```

Every coalition of size at least two receives `(0,0,0,0)`.

Define

```text
P(t) = -125 + 335t + 3056t^2 - 908t^3 - 24864t^4
       - 41392t^5 - 19328t^6 + 5056t^7 + 4352t^8,
D(t) = 50 + 10t - 836t^2 - 344t^3 + 144t^4,
N(t) = 30t - 148t^2 + 88t^3 + 112t^4.
```

Choose a root `t` of `P` in `(191/1000,24/125)`, and put `y=N(t)/D(t)`.
Define

```text
p_1 = y,
p_0 = (t+y)/(1-y),
p_3 = 2t/(1+2t),
q_i = 1-p_i,
q_2 = (1-4y-2t)/[(1-2y-t)(1+y)],
p_2 = 1-q_2.
```

With `m=2`, use the three hazard rows

```text
h^0=(p_0,0,0,0),
h^2=(0,0,p_2,0),
h^J=(0,p_1,0,p_3).
```

The two active coins in `h^J` are private independent Boolean coins. The
phase is determined by the public stage number modulo three; no public or
correlated random device is assumed. At a live stage the players act
simultaneously, every nonempty quitting coalition terminates the play, and
the coalition receives its own raw reward row.

Define the displayed phase values

```text
X^J=(1/q_2,q_3,1,q_1),
X^2=p_2 R_2+q_2 X^J,
X^0=p_0 R_0+q_0 X^2,
U=(X^0,X^2,X^J,X^0).
```

The fixed payoff in the theorem is `x=X^0`.

## Conjecture-facing change

The generated frontier records the four-player full-core deadlock family as a
live boundary. The checked theorem
`HasTerminalExploitabilityGap.fullCoreDeadlock_le_sharperBound`
(`UniformEquilibrium/Diagnostics/Quitting/FullCoreDeadlockDebtBound.lean`)
only bounds a terminal gap by `1227/96755`; it explicitly does not show that
the gap vanishes or produce a uniform-equilibrium payoff.

The checked no-go `ReducedIdealSingletonLasso.debt_pos`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`)
shows that every finite reduced ideal-singleton lasso for this matrix has
strictly positive debt at every phase.

The result here produces a uniform-equilibrium payoff for the literal named
zero-multiquitter completion. It crosses the singleton-lasso barrier by using
one genuinely nonsingleton product phase. It does not solve every reward table
with the same normalized singleton matrix.

## Source correspondence

The relevant checked source declarations are:

- `FullCoreDeadlock.deadlockMatrix`, `FullCoreDeadlock.reward`,
  `FullCoreDeadlock.reward_singleton`, and
  `FullCoreDeadlock.reward_isFullCoreDeadlockCompletion`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean`);
- `FullCoreDeadlock.deadlockMatrix_normalCore_eq_univ` in the same file;
- `ReducedIdealSingletonLasso.debt_pos`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`);
- `IsQuittingBlockCertificate` and
  `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`
  (`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`); and
- `HasTerminalExploitabilityGap.fullCoreDeadlock_le_sharperBound`
  (`UniformEquilibrium/Diagnostics/Quitting/FullCoreDeadlockDebtBound.lean`).

The first group supplies the literal actual game. The block theorem is a
checked conditional consumer covering every unilateral behavioral deviation.
The algebraic root, hazards, value path, and verification of every certificate
field are now checked in the literal actual-data module cited below.

A narrow declaration search found no existing uniform-payoff theorem or block
certificate for `FullCoreDeadlock.reward`. The existing full-core results give
positive debt upper bounds and singleton-route no-go results, not this joint
product block. No theorem from the paper literature is invoked or translated;
the named reward table and its frontier status are project-owned Lean data.

## Proof

### Exact algebraic root and probability bounds

Direct rational evaluation gives

```text
P(191/1000)
 = -1374675715873650310293/3906250000000000000000 < 0,
P(24/125)
 = 2923619984558827/59604644775390625 > 0.
```

Continuity supplies a root in the open interval. Uniqueness is unnecessary.
For this root,

```text
D(t)>50-836(24/125)^2-344(24/125)^3
    =32708794/1953125>16.
```

Moreover

```text
20N-D = -50+590t-2124t^2+2104t^3+2096t^4,
3D-50N = 150-1470t+4892t^2-5432t^3-5168t^4.
```

The derivative of the first polynomial is positive on the interval by the
lower bound `492739863/7812500`, and its left-endpoint value is
`165890386791/62500000000>0`. The derivative of the second is negative by the
upper bound `-2578173479/7812500`, and its right-endpoint value is
`641729382/244140625>0`. Since `D>0`,

```text
1/20<y<3/50.
```

These bounds imply

```text
1/4<p_0<27/100,   1/20<p_1<3/50,
27/100<p_3<28/100.
```

For `q_2`, its numerator and denominator obey

```text
47/125 < 1-4y-2t < 209/500,
7224/10000 < (1-2y-t)(1+y) < 75154/100000.
```

Exact cross-multiplication gives

```text
1/2<q_2<3/5,
2/5<p_2<1/2.
```

Thus all four active hazards lie strictly in `(0,1)`.

### Four exact identities

Put

```text
F_0=(36t-10)y^2+t(18t-43)y+t(5-14t),
F_1=4t(1+2t)y^2+(5+19t+2t^2)y+t(2t-3),
A_0=36t-10,
A_1=4t(1+2t).
```

Coefficientwise expansion gives

```text
A_1F_0-A_0F_1=D(t)y-N(t),
D(t)^2 F_1(t,N(t)/D(t))=40t^2P(t).
```

At the selected root `t>0`, `D>0`, and `A_1>0`, so first `F_1=0` and then
`F_0=0`. Set `B=(1-2y-t)(1+y)>0`. Exact denominator clearing gives

```text
q_2[4(p_1q_3+q_1p_3)+q_1q_3]-1
  =F_0/[B(1+2t)],

3p_0+q_0(2p_2+q_2q_3)-(1+4t)
  =(1-2y-t)F_1/[(1-y)B(1+2t)].
```

Consequently

```text
q_2[4(p_1q_3+q_1p_3)+q_1q_3]=1,                 (E0)
3p_0+q_0(2p_2+q_2q_3)=1+4t.                     (E1)
```

The definitions directly give

```text
p_0q_1-p_1=t,
q_3[1+2(p_0q_1-p_1)]=1,                         (E2)
q_0q_1(2p_2+q_2q_1)=1.                          (E3)
```

For `(E3)`, use `q_0q_1=1-2y-t`; after substituting `q_2`, its left side
reduces to `2(1-2y-t)-(1-4y-2t)=1`.

### On-path recursions

The solo-phase recursions are the definitions of `X^2` and `X^0`. They give

```text
X^2_0=1, X^2_2=1,
X^0_0=1, X^0_2=1+2p_0,
X^0_1=1+4t, X^0_3=1/q_1.
```

At the joint phase, a double quit pays zero. The Continue values of inactive
players `0` and `2` are

```text
C_0=4(p_1q_3+q_1p_3)+q_1q_3X^0_0,
C_2=-p_1q_3+q_1q_3X^0_2.
```

Equation `(E0)` yields `C_0=1/q_2=X^J_0`. Equation `(E2)`, after substituting
`X^0_2=1+2p_0`, yields `C_2=1=X^J_2`. The active joint-phase coordinates also
satisfy the recursion because their Quit and Continue endpoints are equal, as
shown next. Hence `U=(X^0,X^2,X^J,X^0)` satisfies all three exact successor
recursions and closes at its origin.

### All one-stage endpoint checks

The four active players are indifferent at their active phases:

- phase `0`, player `0`: `Quit=1=Continue=X^2_0`;
- phase `2`, player `2`: `Quit=1=Continue=X^J_2`;
- phase `J`, player `3`: `(E3)` gives `X^0_3=1/q_1`, so
  `Quit=q_1=Continue=-p_1+q_1X^0_3`; and
- phase `J`, player `1`: `(E1)` gives `X^0_1=1+4t`, and
  `p_3/q_3=2t`, so
  `Quit=q_3=Continue=-2p_3+q_3X^0_1`.

The eight inactive cases have the required strict direction:

- at phase `0`, each spectator's Quit endpoint is `q_0<1`, while its Continue
  value is one of `1+4t`, `1+2p_0`, and `1/q_1`, all above one;
- at phase `2`, each spectator's Quit endpoint is `q_2<3/5`, while its
  Continue value is `1`, `2p_2+q_2q_3`, or `2p_2+q_2q_1`; the last two are
  above `4/5`; and
- at phase `J`, an inactive player's Quit endpoint is `q_1q_3<1`, while its
  Continue value is `1/q_2>1` or `1`.

This exhausts all twelve player-phase cases. In the sign convention of
`IsQuittingBlockCertificate.gain`, every positive hazard multiplies a zero
Quit-minus-Continue gain, and every zero hazard has nonpositive gain.

### Remaining certificate fields and semantic conclusion

The probability fields were proved above. The final value row repeats the
first. For the canonical box,

```text
X^J is in [0,2]^4,
X^2 is a convex combination of R_2 and X^J,
X^0 is a convex combination of R_0 and X^2 and is in [0,3]^4.
```

The source table contains an absolute payoff of four, so the checked bound
`abs_reward_le_quittingRewardBound` implies
`4<=quittingRewardBound r`. Thus all four displayed rows satisfy the required
absolute-value box.

The solo-`0` phase absorbs with positive probability because `p_0>0`. Every
own singleton payoff is one, so every player satisfies the nonnegative-solo
branch of `IsQuittingBlockCertificate.admissible`; no off-path Nash or
player-deleted contraction assumption is used.

All fields of `IsQuittingBlockCertificate r h U` now hold. The checked theorem
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` concludes

```text
(quittingGame r).IsUniformEquilibriumPayoff none X^0.
```

Its conclusion covers unrestricted unilateral behavioral deviations and
keeps the target `X^0` fixed before the accuracy is chosen.

## Boundary tests

- The two exact endpoint values of `P` have opposite signs. Both independent
  reviews recomputed them and also found `P` strictly increasing on the
  interval, ruling out an accidental choice among numerically detected roots.
- Every active hazard is separated from zero and one by the rational bounds
  above. Every inactive endpoint inequality is strict, with all twelve cases
  checked independently.
- The smallest strict singleton triangle in the normalized matrix uses owners
  `(0,2,3)` and its forced hazards `(5/14,5/9,5/12)`. The omitted player `1`
  misses its last solo floor by exactly `3/4`. Thus the simpler balanced
  singleton-cycle adapter does not already prove this result.
- More strongly, `ReducedIdealSingletonLasso.debt_pos` rules out every finite
  reduced one-owner singleton lasso. The joint phase here has
  `p_1p_3>0`; sequentially splitting it deletes a positive-probability
  double-quit event and changes the Bellman equations. This is the exact point
  where the new construction leaves the no-go's hypotheses.
- The proof uses the literal zero payoff of every coalition of size at least
  two. Arbitrary nonsingleton rows are a negative boundary for this exact
  statement: they change the four identities, and no global robustness theorem
  is included in this packet.

## Adapter and consumer

The actual-data flow is

```text
FullCoreDeadlock.reward
  -> exact algebraic root t
  -> hazards (h^0,h^2,h^J) and values U
  -> IsQuittingBlockCertificate reward h U
  -> isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
  -> fixed uniform-equilibrium payoff X^0.
```

Every arrow is represented by a checked Lean declaration. The consumer uses
product roots and covers a
deviator replacing its whole behavioral strategy; it is not a bounded-memory
or stopping-time verifier.

## Checked Lean realization

The exact algebraic construction, endpoint identities, and block certificate
are checked by `jointBlock_isQuittingBlockCertificate`; the literal-table
semantic capstone is
`FullCoreDeadlock.reward_isUniformEquilibriumPayoff_jointBlock`, with existence
also recorded by `FullCoreDeadlock.exists_uniformEquilibriumPayoff_reward`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean`).
Thus both the actual-data adapter and the unrestricted-behavior consumer are
checked for this one table.

## Scope and nonclaims

- This proves one named four-player reward table, not the finite-quitting
  conjecture and not every `IsFullCoreDeadlockCompletion`.
- It does not prove that the same hazards work after changing any reward row.
- It does not contradict the reduced singleton-lasso barrier; its joint phase
  is outside that structure.
- It uses private independent randomization and deterministic public phase
  timing, but no public correlated random device.
- The exact algebraic adapter, certificate, and semantic conclusion are proved
  in Lean for the literal table.
- The separate implicit-function neighborhood claim in the author's notebook
  is intentionally excluded pending independent review.
