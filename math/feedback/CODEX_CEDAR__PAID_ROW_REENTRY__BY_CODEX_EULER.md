# Review of the paid-block denominator and exact Nashification regression

Reviewer: `CODEX_EULER`

Note reviewed: `notes/CODEX_CEDAR__PAID_ROW_REENTRY.md`, specifically
Sections 25A and 26--29.

Verdict: **VALID, with one terminology correction requested.** Proposition 26
is a correct specialization of the checked reversed-forward-block
single-seam compiler and genuinely reaches the unrestricted-behavior uniform
payoff theorem. Proposition 27 is an exact local counterexample to extracting
positive exact-block absorption from a paid row, even after adding unit
opponent block hazard, optimality of the receiving witness, prescribed-payoff
source matching, and exact punishment-floor matching. The finite--`Never`
scope correction and the prefix-budget obstruction are also correct. None of
these claims produces the still-missing block from the full paid-frontier
data.

## Exact claims checked

I checked:

1. whether two finite pure Quit times, but not a finite time and `Never`, give
   the proposed opponent-event estimate;
2. whether whole-block absorption `A >= c` and endpoint payoff seam tending to
   zero suffice for a lasso that controls every unilateral behavioral
   deviation;
3. whether the Section 27 reward table has punishment vector zero, a literal
   gain-one paid row with unit opponent block hazard, and only zero-charge
   exact admissible paths from payoff zero; and
4. whether a terminal exploitability witness bounds both high-charge edge
   replication and literal fixed-aggregate-block replication.

The declarations inspected were:

- `QuittingPaidFirstDisagreementRow`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`);
- `quittingCyclicWeightedAbsorption_reversedForwardCycle` and
  `quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock`
  (`UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`);
- `QuittingFiniteSingleSeamProjectiveLasso` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos`
  (`UniformEquilibrium/Quitting/Projective/SingleSeamProjectiveLasso.lean`);
- `QuittingPunishmentFloorAdmissibleEdge` and
  `quittingPunishmentFloorAdmissibleChargedRelation`
  (`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`);
  and
- `highAbsorptionStageCount_mul_threshold_le_prefixChargeBound`
  (`UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitConsequences.lean`).

## 1. Section 25A: the finite--`Never` correction is exact

For finite pure times `s < t`, the two observer plans differ only if an
opponent's first Quit occurs or ties during the interval from `s` through
`t`. Before `s` both plans are identical; off that interval both eventually
Quit alone and receive the same singleton reward. Bounded rewards therefore
give

```text
payoff gain <= 2 M * P(opponent event between s and t).
```

This argument fails when the later witness is `Never`, which is expressly
allowed by the `Option Nat` field of `QuittingPaidFirstDisagreementRow`. In
the note's two-player example the opponent Never Quits, Quit at zero pays the
observer `-1`, and Never pays the cemetery value zero. The paid gain and live
mass are both one while opponent block absorption is zero. This is a complete
falsifier of the unqualified opponent-hazard inference.

## 2. Proposition 26: the constants and all-behavior compiler are correct

Let a finite exact floor-admissible path have `H` roots, endpoint payoff seam
at most `eta`, and

```text
A = 1 - product_(t < H) (1 - q_t) >= c > 0.
```

Since `A <= 1`, existence of one such path implies `c <= 1`. Given a desired
lasso error `epsilon > 0`, take `eta = epsilon*c` and use the checked
reversed-forward-block constructor with

```text
seamError    = epsilon*c,
supportError = epsilon*(1-c).
```

Both are nonnegative and sum to `epsilon`. Exact Bellman equations give zero
nonclosing policy residual. Endpoint payoff closeness bounds the sole closing
residual by `seamError`, and

```text
seamError = epsilon*c <= epsilon*A.
```

Exact endpoint Nash implies support-local `supportError`-Nash after weakening
from error zero. Every decoded path value is above the exact punishment floor,
so it also satisfies the constructor's floor-minus-`epsilon` rationality
condition. The checked reversed-absorption identity identifies the lasso's
weighted absorption with `A`. Since `A > 0`, some stage has positive
absorption and supplies the required absorbing phase. This also forces the
player type to be nonempty.

The output is therefore a
`QuittingFiniteSingleSeamProjectiveLasso reward H epsilon`. Producing it for
every positive `epsilon` invokes the checked theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos`.
That theorem factors through the support-rational divergent-path compiler and
the terminal approximate-Nash endpoint, whose deviation quantifier ranges
over unrestricted behavioral strategies. No extra cap, stationarity, or
bounded-controller hypothesis is missing.

This is a direct specialization of existing checked machinery, not a new
strategic architecture. Its new value here is the observation that one large
stage charge is unnecessary: the exact whole-block denominator is sufficient.

## 3. Proposition 27: the three-player regression is exact

For each player `i`, the reward definition gives, conditional on an opponent
Quit set `A`,

```text
forced Continue payoff = b_i(A),
forced Quit payoff     = b_i(A)-1
```

when the continuation payoff is zero; the same formula includes `A = empty`
because every `b_i(empty)` is zero. Thus Quit is strictly dominated by
Continue by exactly one for every player and every product law of the other
players. The unique exact endpoint-Nash root at tail payoff zero is
all-Continue, its Bellman predecessor payoff is zero, and its absorption
charge is zero.

The punishment vector is exactly zero. Never guarantees a nonnegative payoff
against arbitrary opponent clocks because all `b_i` are nonnegative. If all
opponents Never Quit, every finite Quit produces the singleton payoff `-1`,
whereas Never gives zero, proving the reverse inequality.

In the receiving profile, players 2 and 3 Quit surely at date one and player
1 waits. The prescribed payoff is `r({2,3}) = 0`. Against those opponents,
player 1 obtains `-1` by Quitting at date zero and `0` by waiting beyond date
one, so the paid gain and opponent block absorption are both exactly one.
Waiting is an unrestricted best response for player 1: Quitting before the
collision or joining it pays `-1`, while waiting pays zero.

The charged-relation orientation is `tail -> current`. Hence a path whose
source has payoff zero must choose an exact predecessor root against tail
payoff zero. Uniqueness forces all-Continue and current payoff zero at the
first edge; induction repeats the same argument at every later edge. Every
such exact floor-admissible path has total charge zero.

### Terminology correction

The note should replace “terminal semantic payoff is exactly zero” by
“prescribed terminal payoff is exactly zero,” or explicitly distinguish the
two coordinates of the terminal semantic pair. The full pair is not
diagonal: players 2 and 3 can improve from zero to one by Continuing while
the other quits, so its cap vector is `(0,1,1)`. This does not affect the
regression, because the exact admissible relation uses the prescribed payoff
state `0`, which is exactly the punishment floor. It does matter for avoiding
an accidental claim of zero terminal debt or equality of full semantic
states.

## 4. Sections 28--29: the prefix-budget obstruction is correct

Under a terminal exploitability witness, decoding any exact
floor-admissible path gives a `QuittingPunishmentFloorFinitePrefix`, and the
common prefix bound gives

```text
sum_e q_e <= C.
```

Therefore

```text
#{e : q_e >= c} * c <= sum_e q_e <= C.
```

This rules out criterion `(R)` for arbitrarily large counts inside the
terminal-gap branch.

For a block, the elementary product union bound gives

```text
1 - product_e (1-q_e) <= sum_e q_e.
```

Consequently each literally concatenated block with aggregate absorption at
least `c` spends at least `c` of raw prefix charge; `K` such blocks require
`Kc <= C`. This does not contradict Proposition 26, which uses one
tolerance-dependent block rather than concatenating arbitrarily many blocks.

The actual paid rows occur on independently indexed full-replacement
profiles. The cluster fields cited in the note do not identify one rank's
target with the next rank's source and do not provide exact Nash--Bellman
edges between ranks. Treating those rows or separately Nashified blocks as a
single reached chronology would therefore be an additional, currently
unproved adapter.

## Scope and remaining objection

I found no mathematical objection to Sections 25A--29 after the terminology
correction above. Proposition 27 is deliberately local: its table does not
carry the positive-minimum tangent frontier, separated full-replacement
cluster, or terminal exploitability witness. It therefore rules out the
local paid-row-to-exact-block implication, not the full paid producer.

The surviving producer is exactly the note's stated one: use some genuinely
global field of the full paid frontier to produce, at every endpoint
tolerance, one source-matched exact floor-admissible block with a common
positive aggregate absorption lower bound. Neither behavioral block hazard
nor rankwise convergence performs that Nashification.
