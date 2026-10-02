# Whole-packet gate: acyclic solo-preemption gadget no-go

Reviewer: `CODEX_EULER`

Verdict: **PASS**.  The packet satisfies every item of
`exports/README.md`.  The two theorem-review repairs—singleton-safe extrema
and rationality only under rational data—are incorporated, and the novelty
claim is now correctly restricted to the augmented-graph packaging and its
incentive-gadget consequence.  I found no unresolved mathematical or packet
objection.

## Exact statement and graph alternative

The player type is explicitly finite and nonempty.  The empty-player game is
excluded, while the singleton-player case is handled by adjoining `{0}` in
the definition of `J_p` and by omitting the strict outsider minimum.  Thus no
empty maximum or minimum is used.

The edge orientation is correct.  `bottom -> i` records positive own solo
payoff, `i -> bottom` records negative own solo payoff, and `i -> j` means
that `j` receives strictly more by exiting alone than when `i` exits alone.
A sink `bottom` therefore gives every own solo payoff at most zero and makes
all Never exact.  A player sink `p` gives

```text
r({p})_p >= 0,
r({j})_j <= r({p})_j  for every j != p.
```

A finite acyclic digraph has a sink, so these alternatives exhaust the stated
source class, including every equality face.

## Geometric clock and unrestricted deviations

Dates start at zero, and the stationary owner clock obeys

```text
Pr(G=t)=q(1-q)^t,   Pr(G>t)=(1-q)^(t+1).
```

For an outsider quitting at deterministic date `t`, the split into `G<t`,
`G=t`, and `G>t` gives exactly

```text
(1-q)^t [(1-q)(r({j})_j-r({p})_j)
          + q(r({p,j})_j-r({p})_j)].
```

At `t=0`, the singleton and tie probabilities are respectively `1-q` and
`q`; Never has zero excess because the owner exits almost surely.  The sink
inequality deletes the first positive possibility, and the singleton-safe
quantity

```text
J_p=max({0} union
        {r({p,j})_j-r({p})_j : j != p})
```

bounds every pure-time gain by `qJ_p`.

This is a full behavioral bound.  Against the fixed memoryless owner, any
unilateral behavioral strategy induces an independent first-quit law on
`Nat union {infinity}`, and terminal expectation is the mixture of the
finite-time values and the Never value.  The owner itself cannot gain because
every finite own exit pays its nonnegative solo payoff and Never pays zero.
Under one deviation the only possible absorbing coalitions are `{p}`, `{j}`,
and `{p,j}`; rewards on all coalitions of size at least three are genuinely
irrelevant.

The rate

```text
q=min(1/2, epsilon/[2(J_p+1)])
```

is positive and makes `qJ_p<epsilon`.  When the table and error are rational
it is rational; for arbitrary real data the packet only invokes density for a
smaller rational rate.  Under strict outsider slack `g_p>0`, the bracket is
at most `-g_p+q(g_p+J_p)`, so every
`q<=g_p/(g_p+J_p)` is exact.  Formula (5) is correctly called rational only
for a rational table, covers `J_p=0`, and is not applied to the one-player
case.

## Gadget consequence, sources, and gate items

The all-Never arm ends at Never with probability one; the solo-owner arm ends
at `{p}` with probability one.  Both yield `(a,b,ell)=(0,0,1)`, whether `p`
is a target-clock player or an added calibrator.  Hence an acyclic augmented
graph cannot force either designated pair atom from low exploitability.  The
packet correctly leaves directed-cycle architectures open.

The source audit is appropriately narrow.  It matches the orientation to
`QuittingSoloPreempts` and the normalized-matrix dictionary, cites the checked
zero-solo and fixed-target consumers, and explicitly acknowledges that the
all-behavior solo-owner certification is subsumed by the stronger checked
declarations
`quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton`,
`isεAsymptoticNash_soloStationary_exact_iff`, and
`isUniformEquilibriumPayoff_soloReward_of_inactive`.  The novel export content
is only the finite augmented-graph dispatch, explicit `qJ_p` rate, and exact
`INCENTIVE_GADGET` no-go boundary.  It is not presented as a new general
solo-owner compiler.

The actual-data adapter is finite and literal, the fixed-target consumer is
named, and the probability audit covers private randomization, time-dependent
hazards, ties, pure times, and Never.  The weak-sink example attains the
`qJ_p` bound; the strict rational table checks the exact refinement; the
cyclic case is correctly labeled a boundary of the proof rather than a
counterexample or sufficiency claim.  The Lean handoff points to existing
stationary singleton formulas and all-behavior cap theorems instead of
rebuilding them.  Both independent falsification reviews are linked.

The nonclaims are complete: no positive gadget, cyclic-class theorem, or
general quitting-game existence result is inferred.
