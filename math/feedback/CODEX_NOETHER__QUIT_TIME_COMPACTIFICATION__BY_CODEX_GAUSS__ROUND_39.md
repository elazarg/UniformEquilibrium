# Feedback on `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION` — Round 39

## Claim checked

I independently falsified Section 59, Proposition 79: bounded total charge on
a compact closed one-sided relation gives an exact bounded state-local Bellman
bias, but need not give any continuous exact bias even when the relation is
predecessor-serial and the charge is continuous.

**Verdict: VALID ordinary mathematics.**  I found no mathematical objection.

## 1. Viable carrier and Bellman identity

For compact metrizable `K`, the countable product `K^N` is compact.  The path
constraints `R(omega_t,omega_(t+1))` are closed coordinate conditions, so the
nonempty path space `Omega` is compact.  Its initial projection `Y` is compact.
Every fiber over `x in Y` is nonempty, and `(N169)` bounds every infinite
charge sum between zero and `B`; hence `(N170)` is a finite real number.

If a path from `x` has first successor `y`, its charge is `a(x)` plus the
charge of its tail from `y`.  Conversely, `R(x,y)` with `y in Y` lets one
prepend `x` to every viable path from `y`; this also shows automatically that
`x in Y`.  Taking the two nested suprema gives exactly

```text
V(x)=a(x)+sup {V(y): y in Y and R(x,y)}.
```

No maximizer, measurable selection, continuity, or compactness of individual
fibers is being smuggled into this equality.  The one-edge inequality follows
immediately.

## 2. Compact branch-chain example

For

```text
o=(0,0),  x_(n,k)=(1/n,k/n^2),  0<=k<=n,
```

every nontrivial sequence of states with `n->infinity` converges to `o`.
Therefore the state set is compact.  For the edges in `(N173)`, every
convergent sequence either is eventually in one finite branch or has both
endpoints converge to `(o,o)`, which is an edge.  Thus `R` is closed.

Every state has a predecessor: `o` and `x_(n,0)` use their self-loops,
`x_(n,k+1)` has predecessor `x_(n,k)`.  Every state also has an infinite
future, since the branch reaches `o`, while `x_(n,0)` may wait finitely or
forever on its zero loop.

The charge in `(N174)` is continuous.  All nonzero charges on a branch equal
`1/n`, hence tend to zero uniformly as the branch converges to `o`.  A viable
path traverses at most one positive branch and pays

```text
sum_(k=1)^n 1/n = 1.
```

Consequently `B=1`, `V(o)=0`, and `V(x_(n,0))=1`.  Here the arrow in `(N175)`
should be read as topological convergence `x_(n,0)->o`, not as an additional
relation edge; the surrounding proof already uses it in that sense.

## 3. No continuous exact bias

If continuous `W` satisfied `a(x)+W(y)<=W(x)` on all edges, telescope the
edges

```text
x_(n,1)->x_(n,2)->...->x_(n,n)->o.
```

The source charges, including the last source `x_(n,n)`, sum to one, giving

```text
W(x_(n,1))-W(o)>=1.
```

But `x_(n,1)->o` in the topology, contradicting continuity.  This proves the
stronger no-continuous-bias statement, not merely discontinuity of the
canonical envelope.

## Exact scope

The example is a generic compact relation, not an embedding in the quitting
punishment-floor Nash--Bellman relation.  Proposition 79 correctly changes
the universal obligation: bounded transient charge always has a state-local
exact account, but continuity needs additional game geometry or an enlarged
state.  It does not itself supply a Simon finite-cell Lyapunov certificate or
a quitting-game producer.
