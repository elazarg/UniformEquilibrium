# Review of Proposition 86 by `CODEX_GAUSS`

Reviewed note: [`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md), Section 66.

## Claim checked

For `SolanVieilleBoundary.boundaryReward` on `Fin 4`, Proposition 86 claims:

1. every behavioral punishment value is zero;
2. no zero-target physical frozen-root continuation lift whose support
   contains every positive-solo owner can satisfy the punishment floor;
3. after deleting only that floor constraint, the symmetric full-support
   root with hazard `p=1/sqrt(2)` and constant continuation
   `z=-10-8sqrt(2)` satisfies the exact Bellman and endpoint equations and
   lies in the symmetric reward box of radius `48`; and
4. this one-row obstruction coexists with the checked residual-hard,
   stationary-nonexistence, and period-two uniform-equilibrium facts.

This is a claim in ordinary mathematics.  I did not run Lean and do not
assign an `L`, `A`, or `C` seal.

## Verdict

**VALID for clauses 1--4, with one interpretive correction.**  I found no
mathematical objection to the proposition.  In particular, the floor
obstruction is exact: the same table has a literal raw full-support
zero-target product root once negative continuation values are permitted.
The checked period-two repair does **not**, however, literally transport that
negative continuation through one of its reached states; all coordinates of
`oddValue` and `evenValue` are at least `1`.  It repairs the obstruction by
moving the Bellman target while remaining floor-admissible.  Thus the raw
root diagnoses why the frozen zero-target formulation fails, but does not
identify the sign of a continuation used by the actual repair.

## Independent calculations

### 1. Punishment value

Fix a player `i`.  Reading the fifteen rows of
`SolanVieilleBoundary.boundaryReward` directly, every nonempty coalition
excluding `i` pays `i` a nonnegative amount.  The coalition of all three
opponents pays `i` exactly zero.  Since the continue-floor definition also
includes zero, this gives

```text
quittingContinueFloor(boundaryReward,i)=0.
```

Against the pure row in which all three opponents Quit, player `i` gets
zero by Continue and `-1` by joining.  Its pure-row cap is therefore zero.
The hypotheses and orientation of
`quittingPunishmentValue_eq_continueFloor_of_pureRow`
(`UniformEquilibrium/Quitting/Punishment/ContinueFloor.lean`) are exactly
satisfied, so `chi_i=0`.  The same calculation directly checks the
behavioral interpretation: Never guarantees at least zero against arbitrary
opponent behavior, while the displayed pure row caps every response by zero.

### 2. Full-support floor obstruction

Every own singleton payoff is `1`, so the positive-solo set `P` is all of
`Fin 4`.  Thus `P subset S` forces `S=univ`, and interiority gives every
hazard and every Continue probability strictly positive.

At a zero-target lift, the checked
`quittingRootQuitPayoff_eq_zero_of_zeroTargetLift`
(`UniformEquilibrium/Quitting/Boundary/Repair/TerminalFunding/SupportNecessity.lean`)
makes each active owner's forced-Quit endpoint zero.  Its active derivative
equality then makes the forced-Continue endpoint zero as well.

This contradicts the table and the floor.  If `j` is `i`'s same-pair
partner, the opponent event "only `j` Quits" has strictly positive product
probability and pays `i` exactly `4`.  Every other nonempty opponent
coalition pays `i` nonnegatively.  The all-opponents-Continue event pays the
continuation coordinate, which is at least `chi_i=0`.  Hence the forced-
Continue endpoint is strictly positive, not zero.

The proof uses all of the advertised hypotheses: without full support the
partner-only event can lose positive mass, and without the punishment floor
the continuation term can cancel it.

### 3. Raw symmetric root

Write `q=1-p`.  Conditional on owner `i` being forced to Quit, the rewards
over its three opponents are

```text
size 0: 1,
size 1: 1,1,1,
size 2: 1,0,0,
size 3: -1.
```

Therefore the forced-Quit endpoint is

```text
q^3+3pq^2+p^2q-p^3 = 1-2p^2.
```

It vanishes at `p=1/sqrt(2)`.  Conditional on forced Continue, the three
singleton-opponent rewards sum to `4`, the three doubleton-opponent rewards
sum to `2`, and the all-three reward is zero.  Its endpoint is

```text
q^3 z + 4 p q^2 + 2 p^2 q.
```

Since `p/q=1+sqrt(2)`, its unique zero is

```text
z = -4(p/q)-2(p/q)^2 = -10-8sqrt(2).
```

Thus both endpoints vanish for all four owners.  Their product mixture is
the zero Bellman target and every full-support derivative is zero.

The absolute row totals of the literal reward table are

```text
singletons: 4*5 = 20,
pairs:      4+3+3+3+3+4 = 20,
triples:    4*1 = 4,
all four:   4,
```

so the sum-form `quittingRewardBound` is exactly `48`.  From
`1<sqrt(2)<3/2`,

```text
-48 < -10-8sqrt(2) < 0 < 48.
```

The continuation therefore satisfies the ordinary symmetric payoff box but
fails exactly the lower punishment bound `0<=z`.

### 4. Semantic scope

`periodTwo_residualHard_fullCore_nonstationary_but_uniform`
(`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`)
checks the claimed conjunction: residual-hard data, full normal core, no
stationary product exact terminal Nash profile, and a uniform-equilibrium
payoff supplied by the period-two block.  Proposition 86 is consequently not
a game counterexample and not a new existence producer.  It is a sharp
counterexample to the proposed **universal one-row** zero-target funding
step.

## Consequence for the live route

Proposition 85's automatic magnitude law remains valid, but physical-root
feasibility cannot be the universal remaining obligation.  The exact next
producer must replace the below-floor cancellation required by the frozen
zero-target equations with a floor-admissible moving-target, multi-phase
chronology.  The checked period-two block proves that such recurrence can
solve the literal obstruction.  It does not show that an actual reached
continuation ever goes below the floor.
