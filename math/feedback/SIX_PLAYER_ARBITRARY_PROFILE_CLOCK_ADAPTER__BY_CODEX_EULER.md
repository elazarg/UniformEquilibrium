# Independent falsification of the six-player arbitrary-profile clock adapter

Reviewer: `CODEX_EULER`

Source reviewed:
[`SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER.md`](../formalized/SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER.md)

## Verdict

**REVISE, then PASS after one mandatory literal-label repair.**  The
square-root clock construction, zero-safe product identities, finite-to-
infinite passage, actual-profile time disintegration, Never handling, and
claimed narrowing of the conditional six-player theorem are mathematically
valid.  The current statement, however, mixes human one-based labels with
literal `Fin 6` numerals.

## Mandatory repair: use the checked six-player labels

The checked file
`UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`
defines

```text
player1=0, player2=1, player3=2,
player4=3, player5=4, player6=5 : Fin 6,
targetA={player1,player2}, targetB={player3,player4}.
```

The note instead calls the *literal* pairs `{1,2}` and `{3,4}` and puts the
remaining hazards at coordinates `5,6`.  Literal `Fin 6` has coordinates
`0,...,5`; `(6 : Fin 6)` is not a legal checked label.  Moreover the written
pairs would leave `{0,5}`, not the displayed background `{5,6}`.

State the theorem using

```text
A=SixPlayerOnePair.targetA,
B=SixPlayerOnePair.targetB,
q_r(t)=hazard of SixPlayerOnePair.player_r,
background(t)=sqrt((1-q_player5(t))*(1-q_player6(t))).
```

Then replace (5) and its symmetric formula by the corresponding
`player1,...,player6` expressions.  The human gloss “pair A is players 1 and
2; pair B is players 3 and 4” may remain, but it must not be presented as
literal `Fin 6` notation.

## Clock construction and zero cases

After that relabeling, all six coordinates occur exactly once.  Put

```text
S(t)=quittingJointSurvivalWeight roots 0 t,
z(t)=sqrt(S(t)),
g(t)=sqrt((1-q_5(t))*(1-q_6(t))).
```

The checked survival recurrence is

```text
S(t+1)=S(t)*product_r(1-q_r(t)).
```

Every factor is nonnegative.  Repeated use of the nonnegative identity
`sqrt(x*y)=sqrt(x)*sqrt(y)` gives the asserted `survivalRoot_step`.  This
argument remains exact when `S(t)=0`, a hazard is `0` or `1`, or a background
Continue factor vanishes; no division or positivity cancellation occurs.
The initial field follows from `S(0)=1`.

For the first target,

```text
firstTargetAmplitude(t)^2
 = S(t) q_1(t)q_2(t)
     (1-q_3(t))(1-q_4(t))(1-q_5(t))(1-q_6(t)),
```

where the subscripts now mean the named human players.  `Real.sq_sqrt` is
applicable to every grouped product because all factors are nonnegative.  The
same expansion holds for the second target.  Thus (6) is an equality at all
boundary hazards, not merely in the positive interior.

## Finite-to-infinite passage

`TwoPairHazardClock.finite_targetMass_sqrt_sum_le_one` has exactly the sum-of-
squared-amplitudes conclusion used in (7).  By (6), those squares are the
nonnegative stage coalition masses.  For either nonempty target pair the
checked summability theorem for
`rootSequenceStageCoalitionMass` identifies its increasing range sums with
the `tsum`.  Continuity and monotonicity of `Real.sqrt` therefore pass (7) to

```text
sqrt(rootSequenceTerminalCoalitionMass roots A)
 + sqrt(rootSequenceTerminalCoalitionMass roots B) <= 1.
```

There is no hidden assumption that total absorption tends to one.

## Actual-profile disintegration

For `roots=quittingProfileLiveRoot reward sigma`, the checked identity

```text
quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot
```

matches the prefix survival in the root-sequence stage mass.  The checked
factorization

```text
quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
```

then identifies each chronological summand.  Finally
`quittingTerminalOutcomeMass_eq_timeDisintegration` says that the mass of
`some terminal` is exactly the `tsum` of these summands.  Applying it to the
nonempty subtypes carried by `targetA` and `targetB` proves (9).

The `none`/Never outcome equals the residual live mass and contributes zero to
either exact nonempty coalition.  Hazards of the two background players are
already present in `g(t)` and in survival; they are neither discarded nor
double counted.

## Behavioral semantics and novelty

Before absorption there is a unique public live history, while the stage law
conditional on that history is the product of the six private behavioral
marginals.  Hence the proof applies to arbitrary time-dependent behavioral
profiles.  It uses no unilateral-deviation reduction and makes no stationary
or public-correlation assumption.

A narrow search of
`TwoPairClockBoundary.lean`, `SquareRootCoalitionClock.lean`, and
`SixPlayerOnePairMassTargetLock.lean` found the source-native masses, finite
clock inequality, and conditional `hclock` consumer, but no arbitrary-profile
construction composing them.  `docs/FRONTIER.md` explicitly records this
adapter as missing.  The novelty and scope claims are therefore accurate.

After the literal-label repair, final verdict: **PASS, no further objection.**
