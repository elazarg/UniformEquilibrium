# Independent review of the derangement completion

Reviewer: `CODEX_EULER`

Verdict: **PASS** as ordinary mathematics in the stated deranged
interval-core architecture.  The finite hypotheses, componentwise boundary
classification, two-positive-hazard count, limiting full stationary best
responses, endpoint certificate, player-deleted contraction, arbitrary
calibrator scope, and two-disjoint-pair consequence all check.  No repair is
required.  This review does not by itself authorize an export amendment.

## Hypotheses and constrained producer

The source consists of a finite player set, a core `K` with `|K|>=3`, a
fixed-point-free permutation `b:K->K`, and the literal finite-row extrema

```text
C_i^-, C_i^+, H_i^-, L_i^+
```

satisfying `L_i^+ < C_i^- <= C_i^+ < H_i^-` for every core player.  The
extrema are nonempty: `b(i)!=i` supplies a continuation row, while the
blocker-present and blocker-absent background families both include their
literal finite choices.  No restriction is placed on any payoff coordinate
of a player outside `K`.

On `[epsilon,1]^K x [0,1]^(I\K)`, every player has a positive-rate core
opponent because `|K|>=3`.  All deleted absorption denominators are positive,
the stationary payoffs are continuous and fractional linear in each own
rate, and each best-response set is an endpoint or the whole allowed
interval.  The constrained Kakutani producer is therefore valid.

## Componentwise boundary propagation

The continuation endpoint of a core player remains in
`[C_i^-,C_i^+]`.  Conditioning its forced-Quit payoff on the current action
of `b(i)` gives the same strict eventual implications as in the reviewed odd
theorem:

```text
q_{b(i)} -> 0  implies  Q_i>N_i eventually,
q_{b(i)} -> 1  implies  Q_i<N_i eventually.
```

These implications depend only on the player's own blocker coordinate and
are therefore component-local.  A limiting zero forces the predecessor to
the upper endpoint one; the next predecessor is forced to the lower endpoint
`epsilon_m`, hence to zero.  A limiting one starts the same propagation one
step earlier.  It follows exactly that an odd component is wholly interior,
while an even component is either wholly interior or alternates
`0,1,0,1,...` around the complete component.  No relation between distinct
components is assumed in this classification.

Every derangement component has at least two vertices and hence contributes
at least one positive limiting core rate.  If there is one component, its
length is at least three: an odd component is interior, while an even one has
length at least four and its alternating arm has at least two ones.  If there
are multiple components, two distinct components each contribute a positive
rate.  Thus in every decomposition there are at least two distinct positive
core coordinates.

## Full best responses and unrestricted semantics

The two-positive-coordinate fact makes every player's opponent absorption
strictly positive at the limit, including after deleting that player's own
clock.  It also gives a neighborhood on which the repeated stationary payoff
formula is jointly continuous.

For a core player and any fixed alternative `p in [0,1]`, the comparison
`p_m=max(p,epsilon_m)` is admissible in the constrained game and converges to
`p`.  Passing its Nash inequality to the limit proves optimality of the
limiting coordinate against every stationary rate in `[0,1]`, including the
zero endpoint.  Calibrator rates were optimized on the full interval from the
start, and the same continuity passes their inequalities to the limit.  Thus
the entire limiting product is stationary Nash; this step does not assume
that boundary core coordinates are interior.

Fractional linearity turns the stationary optimum into the exact endpoint
complementarity conditions, and multiplying the stationary value equation by
its positive denominator gives the literal Bellman fixed point.  At least two
positive core hazards imply both joint absorption and every player-deleted
contraction.  The named stationary endpoint compilers therefore cover
replacement of a player's complete behavioral strategy, including arbitrary
time dependence, private randomization, ties, and Never, and yield the claimed
uniform payoff.  Calibrator rewards entered only through their actual full-
interval best responses.

## Two-pair consequence and boundary

For four core clocks with blocker permutation `(1 2)(3 4)`, each two-cycle
contributes a positive limiting hazard even when it takes the alternating
boundary arm.  Hence the two components together supply the precise
player-deleted contraction missing from an isolated two-cycle.  The strict
partner-band architecture, including the special case

```text
C_i^-=C_i^+=0, H_i^-=E, L_i^+=T, T<0<E,
```

is therefore solved even with arbitrary calibrator coordinates and cannot
produce the requested incompatible-clock gadget.

The stated exclusions are sharp for this proof.  A single two-cycle can have
only one positive limiting hazard and fails the deleted-contraction handoff;
a fixed point has no predecessor alternation.  Overlapping bands,
background-dependent blocker reversal, and changing active clock labels are
not covered.  The theorem is a universal escape for this exact separated-band
derangement class, not a general negative-cycle or general quitting-game
existence result.
