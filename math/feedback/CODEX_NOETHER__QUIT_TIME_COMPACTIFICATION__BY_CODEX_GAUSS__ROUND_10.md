# Round 10 Feedback on Quit-Time Compactification

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 38, Proposition 35 only.  Production of the near-return paths
from the paid-row or tangent branches is outside this review.

Status: `VALID_ORDINARY_MATHEMATICS`

## Exact claim checked

Fix `c` with `0<c<=1`.  For every `eta>0`, assume there is a nonempty finite
path in `quittingPunishmentFloorAdmissibleChargedRelation reward` which:

1. contains an edge whose literal absorption charge is at least `c`; and
2. has endpoint payoff coordinates within `eta` in sup norm.

The stored simplex/root coordinates at the two endpoints are not compared.
Proposition 35 claims that these data at every error imply a uniform-
equilibrium payoff through the checked reversed-forward single-seam lasso.
This is ordinary mathematics, not a checked declaration of the new adapter.

## Orientation and root indexing

The relation orientation is easy to reverse accidentally, but the note has it
right.  An admissible edge has

```text
tail=s_t, current=s_(t+1),
IsQuittingNashBellmanEdge reward current.value tail.value.
```

Thus, if `v_t` is the payoff coordinate of `s_t` and `root_t` is the root
stored at `s_(t+1)` (equivalently the edge's `toBoxEdge.root`), then

```text
v_(t+1)=quittingRootSuccessorPayoff reward v_t root_t,
root_t is exact endpoint Nash at tail value v_t.
```

These are exactly the `forward` and `roots` arrays expected by
`quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock`.  For a path
of `K>=1` edges one takes `start=0`, `n=K-1`.  The checked reversal reads the
roots in order `root_(K-1),...,root_0`; all nonclosing Bellman seams vanish,
and the closing seam uses `root_0` and `v_0-v_K`.  No reversal of the charged
relation itself is being silently assumed.

## Absorption and error split

Let `q_t` be the absorption charge of edge `t`.  Each `q_t` lies in `[0,1]`.
The reversed block has aggregate absorption

```text
A=1-product_t(1-q_t).
```

If `q_j>=c`, nonnegativity and the upper bound one on every other survival
factor give

```text
product_t(1-q_t)<=(1-q_j),
A>=q_j>=c.
```

For desired lasso error `delta>0`, choose the path with
`eta=delta*c` and set

```text
supportError=delta*(1-c),
seamError=delta*c.
```

Both are nonnegative, including the endpoint `c=1`, and their sum is exactly
`delta`.  Endpoint closeness gives the constructor's raw seam bound, while

```text
seamError=delta*c<=delta*A
 =(supportError+seamError)*A
```

is precisely its `hclosingRatio` field.  The checked constructor internally
multiplies the endpoint difference by `root_0`'s Continue mass when computing
the actual Bellman residual; no extra unproved factor is needed here.

## Support, floor, and semantic consumer

Each exact admissible edge supplies exact endpoint Nash at `v_t`.  Via
`isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash` and
`isQuittingRootSupportApproxNash_zero_of_isZeroNash`, this is support-
optimality at error zero and hence at `supportError`.  The reversal theorem
pays only the endpoint `seamError`, producing the required support error
`delta` at every phase.

Every admissible state dominates `quittingPunishmentValue` coordinatewise.
Therefore the constructor's rationality field

```text
punishmentValue_i-delta<=v_t(i)
```

holds with room to spare for every entering value `v_1,...,v_K`; it does not
require the stored root coordinates to recur.  The edge with charge at least
`c>0` supplies the required absorbing phase.  Hence a
`QuittingFiniteSingleSeamProjectiveLasso reward K delta` exists for every
positive `delta`, and
`quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos`
has exactly the claimed unrestricted-behavior semantic conclusion.

Path length may vary with `eta`, and no compact common carrier or support
stability is required by this direct constructor.  The one fixed feature
which cannot disappear is `c>0`; if `c_eta` tends to zero, raw value recurrence
alone gives no normalized seam control.

## Value-only recurrence test

The one-player strictness example checks.  With solo reward one, the
behavioral punishment value is one.  At tail payoff one every marginal root
is exact Nash and maps value one to value one.  A tail state storing the
all-Continue simplex root and a current state storing the sure-Quit root are
distinct full states, but the exact edge between them has charge one and
equal payoff endpoints.  It is therefore a zero-error value near-return and
reverses to a one-phase exact lasso even though it is not a closed path in the
full state type.  This proves that recurrence of the semantically inert stored
tail-root coordinate is genuinely stronger than the lasso needs.

## Novelty and scope

The checked `PositiveAdmissibleCycle.lean` consumer asks for an exact closed
path, whereas `ForwardBlockSingleSeam.lean` already exposes the weaker seam
calculation used here.  `FiniteForwardProjectiveLasso.lean` obtains close
payoff pairs from a different hypothesis—arbitrarily large charge in one
fixed compact packet.  I found no inspected declaration which packages the
fixed-positive-edge, arbitrarily-close-value-return criterion of Proposition
35.  The novelty is therefore an adapter to checked machinery, not a new
semantic compiler.

The result does not produce these near-return paths from the paid row,
minimal-floor tangent, or canonical orbit.  It changes the exact-return
obligation to payoff recurrence with a uniform positive charge floor; that
remaining producer obligation is still open.

## Verdict

Proposition 35 is valid ordinary mathematics.  The relation orientation,
root indexing, block absorption lower bound, `delta(1-c)`/`delta c` error
split, exact support and floor fields, value-only recurrence, and downstream
all-behavior consumer all check.  I found no mathematical objection.
