# Horizontal Replacement: Exact No-Go and Minimal Actual Repair

## 1. Unary response data are insufficient

There is an exact three-player counterexample showing that prescribed payoff,
terminal law, and every player's complete pure-time response graph do not
determine the result of changing one player's strategy.

Let the players be `j,p,k`.  Give players `p` and `k` reward zero at every
terminal coalition.  Give player `j` reward

```text
r_j({p}) = 1
```

and reward zero at every other nonempty coalition.

Consider two profiles:

```text
sigma:  j Never, p Never, k QuitAt 0;
tau:    j Never, p Never, k QuitAt 2.
```

Both have terminal law concentrated on `{k}` and prescribed payoff vector
zero.  Every pure-time response payoff of every player is also zero:

* players `p,k` have identically zero reward;
* against `p = Never`, player `j` can generate only `{j}`, `{j,k}`, or `{k}`,
  all of which pay zero.

Therefore

```text
(U, terminal law, all completed unary response graphs)
```

is identical for `sigma` and `tau`.

Now replace only player `p` by `QuitAt 1`.  From `sigma`, player `k` has
already quit at date zero, so player `j` receives zero.  From `tau`, player
`p` quits first at date one, so player `j` receives one.  The target prescribed
payoffs, terminal laws, and response games differ.

Hence there is no deterministic horizontal-update operation on the state
proposed in `EXACT_RESPONSE_GRAPH_TRANSPORT.md`.

This is the ordinary-game analogue of a missing mixed partial derivative:
all one-coordinate slices at the source fail to determine a slice after a
different coordinate has moved.

## 2. The exact actual-profile repair

For quitting games there is a particularly clean repair at actual profiles.
Every player's live-spine behavior induces a stopping law on

```text
T = Nat union {infinity}.
```

Conversely, every such probability law admits a hazard reconstruction.  The
vector of player stopping laws determines all terminal semantics:

1. draw the player stopping times independently;
2. if their minimum is finite, the terminal coalition is the set attaining
   that minimum;
3. if every time is infinity, the outcome is Never.

Thus the vector of complete stopping laws is a sufficient statistic for every
actual horizontal replacement.  Replacing player `p` simply replaces its law
in this vector and recomputes the product-clock terminal outcome.

This sufficiency is exact and includes arbitrary randomized hazards, Never,
ties, and arbitrarily late dates.  Values of a behavioral strategy after a
zero-probability live history are irrelevant to terminal semantics, so the
stopping-law quotient loses no operational information.

## 3. Why compactness breaks the repaired operation

Equip stopping laws with weak convergence on the one-point compactification.
Terminal-outcome evaluation is not continuous.

For two players `p,k`, compare the deterministic clock pairs

```text
(T_p,T_k) = (n,n+1),
(T_p,T_k) = (n+1,n).
```

In both sequences each marginal law converges weakly to literal Never.  The
first terminal law is always `{p}`; the second is always `{k}`.  Thus the same
limiting vector of compact stopping laws supports two different limiting
terminal laws.

More generally, let a source opponent clock and a replacement clock both
escape to infinity.  Their separate weak limits do not say which clock is
earlier, whether they collide, or what mixture of those events survives.
This is exactly the relative-timing bubble lost by marginal compactification.

Therefore no continuous function

```text
(limiting source stopping laws, limiting replacement law)
    -> limiting target terminal law
```

can agree with every actual sequence.

This failure persists even after storing the source terminal law and all unary
response graphs jointly.  Reuse the three-player reward table from Section 1.
For index `m`, take

```text
source A_m:  j Never, p Never, k QuitAt (2m),
source B_m:  j Never, p Never, k QuitAt (4m).
```

Both source sequences have:

```text
stopping-law limit:       every player Never;
terminal law:             {k} with mass one;
prescribed payoff/caps:   zero;
all unary response graphs:the zero graph.
```

Use the **same** replacement in both sequences, namely `p = QuitAt (3m)`.
The replacement laws have the same limit, literal Never.  In the first target
`k` stops first, while in the second target `p` stops first.  Player `j`'s
target payoff is respectively zero and one.

Thus even

```text
(source laws, source terminal law, U, all response graphs,
 limiting replacement law)
```

does not determine a boundary target.  The missing datum is the correlated
relative scale of the replacement clock and the source clock.

## 4. Correct compact boundary object

The honest completed horizontal operation is a closed relation.  Embed every
actual replacement diagram jointly as

```text
(source full state, replacement law, target full state)
```

and take the closure of that joint graph.  A member retains one correlated
approximating sequence and therefore does not confuse the two examples above.

This has the same discipline as the existing completed marked-path
composition relation: retain inputs and output jointly rather than selecting
an output from separately compactified inputs.

There are two limitations.

1. The relation need not be single-valued at boundary inputs.
2. Independently selected consecutive relation witnesses need not share one
   approximating sequence.  To compose several horizontal moves, one must
   close the entire finite diagram jointly or carry an actual source sequence
   throughout.

The second limitation is the precise source-provenance obstruction.  A closed
one-edge relation is not a renewable chronology producer.

## 5. Minimal lessons

* `(U,B)` is sufficient for exact vertical prefix semantics but far too small
  for horizontal replacement.
* Adding the terminal law and all unary response graphs still does not repair
  horizontal replacement.
* Adding individual stopping laws repairs the operation on actual profiles.
* At compact limits, one must additionally retain correlated relative-timing
  data or use a closed replacement relation.
* A sequence of closed replacement edges is not automatically one jointly
  realizable diagram.
