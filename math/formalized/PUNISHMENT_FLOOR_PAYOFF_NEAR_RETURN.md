# Punishment-Floor Payoff Near-Return

Author: `CODEX_NOETHER`

Independent reviews:

- [`CODEX_GAUSS`, Round 10](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_10.md)
- [`CODEX_CEDAR`, Round 9](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR__ROUND_9.md)

Both reviews independently attempted falsification and found no mathematical
objection. The repaired direct Lean realization is cited below.

## Exact statement

Let `I` be a finite nonempty player set and let

```text
r : {S : Finset I // S.Nonempty} -> (I -> R)
```

be a finite quitting reward table.

A floor-admissible state consists of a payoff vector in the canonical reward
box, a stored Boolean-product simplex root, and the coordinatewise inequalities

```text
quittingPunishmentValue r i <= payoff i.
```

An admissible edge has a tail state `s`, a current state `s'`, and a root
stored at `s'` such that

```text
payoff(s') = quittingRootSuccessorPayoff r payoff(s) root,
IsεQuittingRootEndpointNash r payoff(s) 0 root.
```

Its direction in the charged relation is `s -> s'`. Its charge is the
one-stage absorption probability `q` of `root`.

### Theorem A: uniformly charged payoff near-returns

Assume there is a constant `c` with `0<c<=1` such that, for every `eta>0`,
there are a positive integer `K`, floor-admissible states
`s_0,...,s_K`, and admissible edges

```text
s_0 -> s_1 -> ... -> s_K
```

with the following properties:

1. some edge has absorption charge at least `c`; and
2. for every player `i`,

```text
|payoff(s_K)(i)-payoff(s_0)(i)| <= eta.
```

Then the quitting game has a uniform-equilibrium payoff against unrestricted
behavioral deviations.

The path, its length, all roots, supports, and both endpoint states may depend
on `eta`. The constant `c` may not. Only endpoint payoff coordinates return;
the stored root coordinates of `s_0` and `s_K` need not agree or be close.

### Corollary B: fixed-edge payoff closure

Let `e` be one fixed floor-admissible exact edge of charge `q>0`. Suppose that
for every `eta>0` there are a floor-admissible state `z_eta` and an exact
admissible relation path

```text
e.current -> z_eta
```

such that

```text
|payoff(z_eta)(i)-payoff(e.tail)(i)| <= eta
```

for every player `i`. Then the quitting game has a uniform-equilibrium payoff.

Equivalently, it suffices that the payoff of `e.tail` lie in the closure of
the payoff projection of states reachable from `e.current`. No recurrence of
the stored root coordinate is required.

### Corollary C: paid-row output weakening

In the paid branch of
`exists_uniformEquilibriumPayoff_of_finiteSupportRankExitConsumers`, retain
exactly the source quantifiers of
`PaidFirstDisagreementAdmissibleReturnConsumer`: for every extracted
frontier, positive-support mover, full-replacement endpoint with strict debt
increase, distinct observer, positive gain, and eventually available paid
first-disagreement row.

The current checked hypothesis asks these data to produce a positive exact
edge together with an exact return from its current state to its tail state.
It is enough instead to produce one fixed positive floor-admissible edge and,
for every `eta>0`, the payoff-closure paths of Corollary B. With this
replacement, and with the original three chronological hypotheses unchanged,
the same four-exit theorem still yields a uniform-equilibrium payoff.

This corollary weakens only the output interface. It does not construct the
edge or the payoff-closure paths from a paid row.

## Conjecture-facing change

The live `PAID-FIRST-DISAGREEMENT-ROW -> POSITIVE-ADMISSIBLE-RETURN` boundary
is represented by `PaidFirstDisagreementAdmissibleReturnConsumer` in
`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`.
Its checked output contains an exact path back to the full tail state.

Theorems A--C prove that this exact state-return obligation is stronger than
the unrestricted behavioral conclusion needs. The strictly weaker sufficient
output is a fixed positive edge whose tail **payoff** is merely approximated
by reachable endpoint payoffs. Stored simplex coordinates may fail to recur,
paths and supports may vary with accuracy, and path lengths may be unbounded.

What remains open is the source producer: neither a paid first-disagreement
row nor the floor-clipped reset family is presently known to supply the
payoff-closure paths.

## Definitions and semantic assumptions

- At the unique live public history, each player uses private behavioral
  randomization. Every product root therefore represents independent Boolean
  choices at that date. Simultaneous quitting coalitions are retained.
- Each path is finite and nonempty. No stationarity, periodic support, bounded
  controller, or public correlating device is assumed.
- Every edge is exact endpoint Nash against its actual tail continuation and
  stays above every behavioral punishment value.
- The final conclusion uses the checked support-rational divergent-path
  compiler, which controls every unilateral behavioral replacement over all
  sufficiently long finite horizons and selects one fixed payoff target.
- The theorem does not assume that approximate-path endpoints themselves have
  a common limiting target.

## Source correspondence

The exact relation and its direction are:

- `QuittingPunishmentFloorAdmissibleState`,
  `QuittingPunishmentFloorAdmissibleEdge`, and
  `quittingPunishmentFloorAdmissibleChargedRelation`
  (`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`).

The existing exact-return boundary is:

- `QuittingPositiveAdmissibleReturn` and
  `PaidFirstDisagreementAdmissibleReturnConsumer`
  (`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`);
- `quittingGame_exists_uniformPayoff_of_positive_admissible_return`
  (`UniformEquilibrium/Quitting/Bellman/Finite/PositiveAdmissibleCycle.lean`).

The checked compilation machinery used by the proof is:

- `QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix`
  (`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`);
- `quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock`
  (`UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`);
- `quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos`
  (`UniformEquilibrium/Quitting/Projective/SingleSeamProjectiveLasso.lean`).

`exists_singleSeamProjectiveLasso_of_finiteForwardPackets`
(`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`)
already combines compactness and arbitrarily large charge inside one supplied
forward-packet family. It does not state the relation-level fixed-positive-edge
payoff-closure criterion or weaken the named paid-row output.

No paper theorem is invoked. The result is a direct reduction between project
interfaces, now checked in `PunishmentFloorNearReturn.lean`.

## Proof

Fix a requested lasso error `delta>0`. Invoke Theorem A's producer with

```text
eta=delta*c.
```

Let `q_t` be the edge charges and let

```text
A=1-product_(t<K)(1-q_t)
```

be the probability that the finite block absorbs. Every `q_t` lies in
`[0,1]`. If `q_j>=c`, then

```text
product_(t<K)(1-q_t) <= 1-q_j,
A>=q_j>=c.                                             (1)
```

Decode the exact relation path to a finite forward Nash--Bellman prefix and
read it in chronological reverse order. The root stored at `s_(t+1)` performs
the forward update from `s_t` to `s_(t+1)`. Hence every nonclosing cyclic
Bellman equation is exact. At the unique closing phase, the residual in
coordinate `i` is

```text
continueMass(root_0)
  *(payoff(s_0)(i)-payoff(s_K)(i)),
```

whose absolute value is at most `delta*c`.

Set

```text
supportError=delta*(1-c),
seamError=delta*c.
```

Both numbers are nonnegative and their sum is `delta`. Exact endpoint Nash
on every edge gives support optimality at error zero and therefore at
`supportError`. The endpoint bound gives the raw seam estimate, while (1)
gives the normalized closing estimate

```text
seamError=delta*c
        <=delta*A
         =(supportError+seamError)*A.
```

All decoded entering values dominate the punishment floor, so the lasso's
rationality field holds even at error zero. The charged edge supplies a
strictly absorbing phase. Thus
`quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock` produces a
single-seam projective lasso at error `delta`.

This construction works for every `delta>0`. Applying
`quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos`
proves Theorem A, including unrestricted behavioral deviations and one fixed
payoff target.

For Corollary B, prepend `e` to the path from `e.current` to `z_eta`. The
combined path runs from `e.tail` to `z_eta`, contains the fixed charge
`q>0`, and has the required endpoint payoff error. Apply Theorem A with
`c=q`; literal absorption gives `q<=1`.

For Corollary C, repeat the checked proof of
`exists_uniformEquilibriumPayoff_of_finiteSupportRankExitConsumers` through
the four finite-rank exits. The first three branches are unchanged. In the
paid branch, the copied paid-row source tuple supplies the fixed edge and
payoff-closure paths; Corollary B immediately gives a uniform payoff,
contradicting the same positive-minimum/no-uniform assumption used by the
checked proof.

## Boundary tests

### Positive: distinct stored roots and `c=1`

In the one-player game `r({0})_0=1`, the behavioral punishment value is one.
At continuation payoff one, Quit and Continue both pay one, so every marginal
root is exact Nash and its successor payoff is one.

Give the tail state payoff one and the stored all-Continue root. Give the
current state payoff one and the stored sure-Quit root. There is an exact edge
from tail to current with charge one. The endpoint payoff error is zero, but
the full states are distinct. The proof has

```text
supportError=0,
seamError=delta,
A=1,
```

and produces a one-phase lasso. This tests the `c=1` endpoint and shows that
stored-root recurrence is genuinely unnecessary.

### Positive: a nil return after the fixed edge

If the fixed edge's current payoff is already `eta`-close to its tail payoff,
Corollary B permits the return path after the edge to be empty. Prepending the
edge still gives a nonempty one-edge path, so the reversal and absorbing-phase
fields remain defined.

### Negative boundary: vanishing charge floors

If the only available threshold is `c_eta->0`, endpoint error `eta` controls
the normalized seam only by `eta/c_eta`. For example, the scales
`eta_n=1/n` and `c_n=1/n^2` give ratio `n`, not a vanishing lasso error.
Thus ordinary payoff recurrence without a uniform charge scale does not
satisfy this proof. The theorem deliberately does not change quantifiers to
hide that failure.

### Attempted falsifiers

The independent reviews checked paths of accuracy-dependent unbounded length,
one-edge paths, unrelated endpoint roots, `c=1`, and charge thresholds tending
to zero. None falsified the stated theorem. The reviews also verified that the
path floor is used at every decoded entering value, not only at its source.

## Adapter and consumer

The supplied path is converted without loss by
`QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix`. Its
roots, exact Bellman equations, exact endpoint Nash constraints, floor bounds,
and literal absorption charges are the data consumed by the reversed-block
single-seam constructor.

The downstream consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos`.
It reaches the full uniform-payoff semantics against arbitrary unilateral
behavioral strategies. Therefore the packet is a strict reduction of a named
live obligation and is not merely a supplied-object verifier.

No arbitrary-game producer supplies the near-return paths here. Corollary C
only says that the paid branch may target this weaker output instead of exact
state return.

## Checked Lean realization

The path-to-lasso adapters
`exists_singleSeamProjectiveLasso_of_floorPrefix_payoffNearReturn` and
`exists_singleSeamProjectiveLasso_of_admissiblePath_payoffNearReturn`, together
with the unrestricted-behavior conditional consumer
`quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`,
are proved in
`UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`.
The theorem remains conditional on one fixed positive charge threshold and
payoff-near-return paths at every accuracy.

## Scope and nonclaims

- No payoff near-return path is produced from arbitrary reward data.
- No paid first-disagreement row is re-entered as an actual edge here.
- No floor-clipped reset edge is proved recurrent.
- No exact path returns to the full tail state.
- No endpoint stored root is selected continuously or recurrently.
- The path and its endpoint may vary with accuracy; only the positive charge
  threshold is fixed.
- The aggregate-charge strengthening of Proposition 37 in the author's note
  is excluded from this packet pending its own review.
- The path decoder and conditional uniform-payoff consumer are proved in Lean;
  no arbitrary-game or paid-row near-return producer is claimed.
