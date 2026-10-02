# Independent falsification of the acyclic solo-preemption diffuse escape

Reviewer: `CODEX_CEDAR`

Verdict: **REVISE -> PASS.**  The graph orientation, sink alternatives,
geometric calculation, arbitrary-behavior reduction, exploitability constant,
strict-sink exact rate, terminal semantics, and incentive-gadget obstruction
are all correct.  I found no mathematical counterexample.  Three small
statement/source repairs are required before packet review:

1. define `J_p` by a singleton-safe finite maximum, for example
   `max ({0} union {r({p,j})_j-r({p})_j : j != p})`;
2. either retain the stated nonempty-player hypothesis and explicitly say the
   empty case is outside the theorem, or add the vacuous empty-player clause
   required by the supplied finite-`I` statement; and
3. narrow the novelty claim: the acyclic augmented-graph packaging is new,
   but the all-behavior solo-owner strategic certification is subsumed by
   stronger checked declarations already in the repository.

These are not proof repairs.  With those edits, the theorem passes.

## Claim and graph orientation

Write `s_i=r({i})_i` and use the directed edges

```text
bottom -> i  iff s_i>0,
i -> bottom  iff s_i<0,
i -> j       iff i!=j and r({j})_j>r({i})_j.
```

The last orientation is load-bearing and correct.  In the checked convention,
`QuittingSoloPreempts reward gap i j` means that `j`'s own singleton payoff
exceeds its payoff when `i` exits alone.  Thus absence of an outgoing edge
from a player sink `p` gives exactly

```text
s_p >= 0,
r({j})_j <= r({p})_j       for every j!=p.
```

If `bottom` is a sink, absence of `bottom -> i` gives `s_i<=0` for every
player, so all Never is exact.  A finite acyclic digraph has a sink, so these
two alternatives exhaust the nonempty case.  Equality correctly creates no
strict edge and is handled by the weak inequalities.

## Pure-time calculation and endpoint conventions

Let only `p` use live-date Quit hazard `q>0`; let all outsiders Never.  With
dates beginning at zero, its geometric time `G` satisfies

```text
Pr(G=t)=q(1-q)^t,
Pr(G>t)=(1-q)^(t+1).
```

Fix `j!=p` and abbreviate

```text
x=r({j})_j,   y=r({p})_j,   z=r({p,j})_j.
```

If `j` Quits at deterministic date `t`, splitting into `G<t`, `G=t`, and
`G>t` gives the exact excess over prescribed payoff `y`:

```text
D_j(t)=(1-q)^t [q(z-y)+(1-q)(x-y)].
```

At `t=0`, the singleton outcome `{j}` has probability `1-q` and the tie
`{p,j}` has probability `q`, exactly as this formula states.  At
`t=infinity`, `j` stays Never and its excess is zero because `p` quits almost
surely.

The sink inequality makes `x-y<=0`.  With

```text
J_p=max({0} union {r({p,j})_j-r({p})_j : j!=p}),
```

we obtain

```text
D_j(t) <= q(1-q)^t J_p <= qJ_p.
```

This constant is sharp in the displayed weak-sink regression: when `x=y=0`
and `z=1`, the date-zero gain is exactly `q`.

## Arbitrary behavioral deviations and the owner

Before absorption, a unilateral deviator sees only the unique live history of
past all-Continue rows.  Its behavioral strategy therefore induces a first-
Quit law on `Nat union {infinity}`.  Behavioral randomization is independent
of `p`'s private geometric randomization, and terminal expectation is affine
in this law.  Hence an arbitrary deviation gain is a convex combination of
the finite `D_j(t)` values and the zero Never gain, and is at most `qJ_p`.
This is an unrestricted all-behavior argument, not merely a stationary or
bounded-controller calculation.

Player `p` faces opponents who never quit.  Every finite own stopping time
pays `s_p`, and Never pays zero.  Its prescribed geometric clock quits almost
surely and pays `s_p`; since `s_p>=0`, no own deviation gains.  Under any
unilateral deviation, only `{p}`, `{j}`, and `{p,j}` can occur.  Therefore
rewards on coalitions of size at least three are genuinely irrelevant, rather
than silently constrained.

## Strict sink and constants

Assume at least one outsider and put

```text
g_p=min_(j!=p) [r({p})_j-r({j})_j] > 0.
```

For every outsider, the bracket in the exact formula is at most

```text
qJ_p-(1-q)g_p.
```

At

```text
q=g_p/[2(g_p+J_p)]
```

this is exactly `-g_p/2<0`.  The rate lies in `(0,1/2]`; if the reward table is
rational, it is rational.  Every finite outsider Quit time is strictly worse,
Never ties, and the owner's prescribed strategy is optimal, so the profile is
an exact terminal Nash profile.  The note correctly separates the one-player
case, where every positive hazard is exact whenever `s_p>=0`.

The word "rational" must remain conditional on rational reward data.  For
arbitrary real input, the displayed quotient need not be rational, although a
smaller positive rational exact rate can be chosen by density.

## Incentive-gadget and terminal semantics

In the `bottom`-sink arm the terminal outcome is Never with probability one.
In the player-sink arm it is the singleton `{p}` with probability one.  Both
belong to leftover mass, so in the four-clock notation

```text
a=0, b=0, ell=1.
```

This remains true when `p` is a calibrator.  Thus arbitrarily small terminal
exploitability directly contradicts the requested uniform positive lower
bound on either designated strict-first pair atom.  Because all approximate
profiles in the player-sink arm deliver the same literal payoff `r({p})`,
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_fixedTarget`
is the correct checked downstream consumer.

For `I` singleton, the inner outsider maximum in the note's current `(2)` is
empty.  The union-with-`{0}` definition above gives `J_p=0` and removes the
notation gap.  For `I` empty, the graph has only `bottom` and the empty profile
is vacuously exact; no player, `J_p`, or division should be invoked.  The note
currently assumes `I` nonempty, so it should either record this separate
boundary or explicitly say it is proving only that restriction of the
supplied statement.

## Source audit and novelty qualification

The relation orientation agrees with `QuittingSoloPreempts` in
`UniformEquilibrium/Quitting/Classification/PreemptionCycle.lean`.  The
zero-solo source and fixed-target terminal consumer cited by the note are also
appropriate.

However, the sentence calling the player-sink strategic argument "new
ordinary-mathematics content" is too broad.  The stronger checked theorem

```text
quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton
```

in
`UniformEquilibrium/Quitting/Classification/Existence/NoHarmSingletonGenerated.lean`
already produces arbitrarily accurate stationary-prefix equilibria from the
same no-harm singleton inequalities plus punishment normality; here normality
follows from `s_p>=0` and `quittingPunishmentValue_le_max_solo`.  At a fixed
rate, the exact all-behavior inequality is already characterized by

```text
isεAsymptoticNash_soloStationary_exact_iff
isUniformEquilibriumPayoff_soloReward_of_inactive
```

in `UniformEquilibrium/Quitting/Punishment/OwnerSoloCertification.lean`.
Thus the valid novelty is the transparent **acyclic augmented-graph
corollary**, the explicit `qJ_p` calculation, and its incentive-gadget
architecture interpretation.  It is not a new general solo-owner equilibrium
compiler.  It says nothing about directed-cycle architectures, consistently
with the note's nonclaims.

