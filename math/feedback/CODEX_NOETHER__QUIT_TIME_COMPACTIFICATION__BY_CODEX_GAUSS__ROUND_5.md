# Fifth review: one joint phase repairs the concrete deadlock completion

Reviewer: `CODEX_GAUSS`

Note reviewed: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 22, Proposition 20 only.

Verdict: `VALID_ORDINARY_MATHEMATICS_NOT_CHECKED_IN_LEAN`.  I independently
expanded both elimination identities, recomputed the exact interval and
hazard bounds, reconstructed all three product-root recursions and every
player's two endpoint values, and checked the fields of
`IsQuittingBlockCertificate`.  The literal source table is exactly
`FullCoreDeadlock.reward`.  The joint `{1,3}` phase lies outside the checked
reduced ideal-singleton-lasso no-go, so the positive result crosses that route
barrier without contradicting it.  I found no mathematical objection.

## Literal source data

The checked definition `FullCoreDeadlock.reward`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean`)
sets a singleton payoff to `1+deadlockMatrix who owner` and every coalition of
cardinality at least two to zero.  Its singleton columns are therefore exactly

```text
R_0=(1,3,3,0), R_1=(4,1,-1,-1),
R_2=(0,2,1,2), R_3=(4,-2,0,1).
```

This is not merely another completion with the same normalized singleton
matrix.  The zero payoff of every simultaneous-quitter coalition is used at
the joint phase, and is true of the named literal `reward` by definition.

## Polynomial root and uniqueness

Direct exact evaluation of the displayed degree-eight polynomial gives

```text
P(191/1000)
 = -1374675715873650310293/3906250000000000000000 < 0,
P(24/125)
 = 2923619984558827/59604644775390625 > 0.
```

Continuity therefore gives a root in the open interval.  Uniqueness is not
needed: every root in the interval satisfies all subsequent uniform bounds
and elimination identities.  It is nevertheless also available.  On the
whole interval, dropping the two positive high-degree terms and bounding the
negative terms at the upper endpoint gives

`P'(t) > 11795914534343/30517578125 > 0`.

Thus there is exactly one root in the certified interval.

For

`D=50+10t-836t^2-344t^3+144t^4`,

the note's coarse estimate is valid:

`D(t)>50-836(24/125)^2-344(24/125)^3
     =32708794/1953125>16`.

Hence `y=N/D` is well-defined.  The two comparison numerators are exactly

```text
20N-D = -50+590t-2124t^2+2104t^3+2096t^4,
3D-50N = 150-1470t+4892t^2-5432t^3-5168t^4.
```

The first is increasing on the interval and is positive at `191/1000`; the
second is decreasing and is positive at `24/125`.  The endpoint values and
derivative bounds printed in the note recompute exactly.  Since `D>0`, they
give

`1/20<y<3/50`.

## Resultant identities

I expanded the two bivariate polynomials independently.  Coefficient by
coefficient,

`A_1 F_0-A_0 F_1=D(t)y-N(t)`.

After substituting `y=N/D` and clearing the denominator, the second identity
is exactly

`D(t)^2 F_1(t,N(t)/D(t))=40t^2P(t)`.

At the selected root, `D>0` and `t>0`, so `F_1=0`.  The first identity then
gives `A_1F_0=0`, and `A_1=4t(1+2t)>0`; hence `F_0=0`.  No unrecorded
nonvanishing assumption or numerical root selection is used.

Substitution of the hazard definitions turns these two identities into

```text
q_2[4(p_1q_3+q_1p_3)+q_1q_3]=1,                 (E0)
3p_0+q_0(2p_2+q_2q_3)=1+4t.                     (E1)
```

The other two identities are immediate rather than resultant consequences.
The formula for `p_0` gives `p_0q_1-p_1=t`, and
`p_3=2t/(1+2t)` gives

`q_3[1+2(p_0q_1-p_1)]=1`.                       `(E2)`

Solving the displayed definition of `q_2` gives

`q_0q_1(2p_2+q_2q_1)=1`.                         `(E3)`

All four identities also agree with the approximate values, but no decimal is
needed for the proof.

## Exact hazard bounds

The bounds on `t,y` give directly

`1/4<p_0=(t+y)/(1-y)<27/100`,

`1/20<p_1=y<3/50`,

`27/100<p_3=2t/(1+2t)<28/100`.

For `q_2`, its numerator lies in `(47/125,209/500)` and its denominator lies
in `(7224/10000,75154/100000)`.  These deliberately coarse rational bounds
give

`1/2<q_2<3/5`, and therefore `2/5<p_2<1/2`.

Every active hazard is strictly between zero and one; every omitted hazard is
zero.  Thus the three rows are genuine private independent product roots.  In
particular the last phase uses two independent Boolean coins, not a public or
correlated draw.

## On-path value recursion

Put

```text
X^J=(1/q_2,q_3,1,q_1),
X^2=p_2R_2+q_2X^J,
X^0=p_0R_0+q_0X^2.
```

The first two phase recursions hold by definition.  They also give

`X^0_0=1` and `X^0_2=1+2p_0`.

At the joint phase, a double quit pays zero.  The Continue values of inactive
players `0,2` are therefore

```text
C_0=4(p_1q_3+q_1p_3)+q_1q_3X^0_0,
C_2=-p_1q_3+q_1q_3X^0_2.
```

Equation `(E0)` gives `C_0=1/q_2=X^J_0`.  Using
`X^0_2=1+2p_0`, equation `(E2)` gives `C_2=1=X^J_2`.
For active player `1`, both endpoints equal `q_3`; for active player `3`, both
equal `q_1`, as checked explicitly below.  Hence the whole joint product row,
not only its inactive coordinates, has successor value `X^J` with tail
`X^0`.  The four-row path `(X^0,X^2,X^J,X^0)` closes exactly.

## All endpoint inequalities

There are four intended indifferences.

- At the solo-`0` phase, player `0`'s Quit value is one and its Continue value
  is `X^2_0=q_2X^J_0=1`.
- At the solo-`2` phase, player `2`'s Quit value and Continue value `X^J_2`
  are both one.
- Equation `(E3)` gives
  `X^0_3=q_0(2p_2+q_2q_1)=1/q_1`.  At the joint phase, player `3` gets
  `q_1` by Quitting and
  `-p_1+q_1X^0_3=q_1` by Continuing.
- Equation `(E1)` gives `X^0_1=1+4t`.  Since `p_3/q_3=2t`, player `1` gets
  `q_3` by Quitting and `-2p_3+q_3X^0_1=q_3` by Continuing.

Every zero-hazard endpoint inequality has the correct direction.

- At phase `0`, any spectator's Quit endpoint is `q_0<1`.  The Continue
  values are `X^0_1=1+4t`, `X^0_2=1+2p_0`, and
  `X^0_3=1/q_1`, all strictly above one.
- At phase `2`, any spectator's Quit endpoint is `q_2<3/5`.  The Continue
  values are `X^2_0=1`,
  `X^2_1=2p_2+q_2q_3>4/5`, and
  `X^2_3=2p_2+q_2q_1>4/5`.
- At the joint phase, an inactive player gets `q_1q_3<1` by Quitting.  Its
  Continue value is `X^J_0=1/q_2>1` for player `0` and `X^J_2=1` for player
  `2`.

These twelve player-phase checks are exhaustive.  In the sign convention of
`IsQuittingBlockCertificate.gain`, positive hazards multiply a zero gain and
zero hazards see a nonpositive Quit-minus-Continue gain.  Exact root Nash is
therefore established at every phase.

## Box, absorption, and admissibility

The vector `X^J` lies in `[0,2]^4`.  The vector `X^2` is a convex combination
of `R_2` and `X^J`, both in `[0,2]^4`.  The vector `X^0` is a convex
combination of `R_0 in [0,3]^4` and `X^2`, hence lies in `[0,3]^4`.  The final
row repeats `X^0`.

The literal reward table contains the payoff `4`; the checked bound
`abs_reward_le_quittingRewardBound` therefore implies
`4<=quittingRewardBound reward`.  All four displayed rows satisfy the
certificate's absolute-value box.

Every phase has positive absorption probability, so the certificate's weaker
existential `absorb` field holds.  Every own singleton reward is exactly one.
Thus every player satisfies the nonnegative-solo branch of the `admissible`
disjunction; no unproved player-deleted contraction is required.

All fields of `IsQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` are now
accounted for: probability bounds, box, last row, successor recursion, gain,
absorption, and admissibility.  Its checked consumer
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` concludes that the
fixed target `X^0` is a uniform-equilibrium payoff against all unilateral
behavioral strategies.

## Why the singleton-lasso no-go is not contradicted

`ReducedIdealSingletonLasso` in
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`
has one owner and one ideal-singleton clearance update at each phase.  Its
theorem `ReducedIdealSingletonLasso.debt_pos` says every such finite reduced
singleton lasso retains positive debt.  It is a route impossibility theorem,
not a nonexistence theorem for `FullCoreDeadlock.reward`.

Proposition 20's last phase gives positive Quit probability simultaneously to
players `1` and `3`.  Its coalition law has two singleton outcomes and a
positive-probability joint outcome, whose literal payoff zero enters the
recursion.  This phase is not an ideal-singleton clearance with one owner and
cannot be encoded by merely repeating or relabelling singleton phases.  The
new block certificate therefore evades the no-go's hypothesis exactly where
claimed.  It proves a uniform payoff for the concrete zero-multiquitter
completion only; it does not solve every `IsFullCoreDeadlockCompletion`.

## Remaining formalization and scope

The construction is a complete ordinary-mathematics actual-data certificate
for a named checked source table and a named checked unrestricted-behavior
consumer.  None of the polynomial root, hazards, value identities, or
certificate assembly is checked in Lean here.  A formalization must define the
algebraic root by the interval existence proof and verify the exact polynomial
and finite-coordinate identities; it must not replace them by the displayed
decimals or by an assumed certificate field.

I found no counterexample.  This review does not claim uniqueness of all
possible deadlock block certificates, robustness to arbitrary nonsingleton
rows, or a solution of the full-core class.
