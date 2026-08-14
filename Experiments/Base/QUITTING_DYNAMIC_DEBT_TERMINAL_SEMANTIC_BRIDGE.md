# Exact dynamic debt is literal terminal semantic debt

## Result

The missing semantic bridge is exact.

Let a finite quitting root/value chain have cutoff `K`, zero terminal value,
exact prescribed Bellman recursion before `K`, and the all-Continue root from
`K` onward. For player `i`, let

```text
c_i = max(0, r({i})_i)
```

be the singleton-or-Never terminal cap. Then, for every positive remaining
horizon, the finite dynamic debt is exactly the unrestricted behavioral
best-response gap of the executable restarted suffix:

```text
D_i(t; K-t, c_i)
  = BR_i(profile started at t) - payoff_i(profile started at t).
```

This is not an inequality, a limiting assertion, or a pure-time proxy. The
right side is the literal infinite-game supremum over all behavioral
deviations.

For a production zero-boundary Nash--Bellman path, the equality holds at every
displayed time `t <= K`, including the padded cutoff debt. Before the cutoff,
the complete raw behavioral port

```text
(prescribed payoff, time-zero live root, terminal semantic debt)
```

is exactly the raw-root presentation of the production `QuittingDebtPoint` at
that time. The Lean development is
The related production source is
[`UniformEquilibrium/Quitting/Debt/Dynamic/FiniteDynamicDebtSemantics.lean`](../../UniformEquilibrium/Quitting/Debt/Dynamic/FiniteDynamicDebtSemantics.lean).

## 1. Why the terminal cap is semantic

The dynamic recursion is initialized with `c_i`. Previously this could look
like an externally imposed upper bound. It is instead the exact behavioral
envelope of the all-Continue suffix.

Against opponents who Continue forever, player `i` has only two relevant
extreme outcomes:

- Never quit, obtaining zero;
- quit alone at some finite time, obtaining `r({i})_i`.

The existing elementary-cap theorem proves, over every behavioral strategy,

```text
BR_i(all-Continue) = max(0, r({i})_i) = c_i.
```

Thus the boundary datum used by exact-`D` is already a co-realized terminal
semantic boundary, not a relaxation.

## 2. The exact composition

Three existing exact statements compose.

1. Finite dynamic-debt semantics gives

   ```text
   value_i(t) + D_i(t)
     = finite behavioral Bellman envelope with terminal value c_i.
   ```

2. Infinite behavioral-tail holonomy says that evaluating the finite prefix
   envelope at an actual tail's behavioral envelope gives the literal
   behavioral best response of the phase-switched infinite profile.

3. The finite terminal compiler says that an exact zero-boundary chain
   completed by all-Continue delivers its declared value exactly.

The all-Continue completion is literally the original operational root
sequence, so subtracting the third identity from the first two gives

```text
D_i(t) = terminal semantic debt_i(restarted suffix at t).
```

Time translation of finite dynamic debt upgrades the entrance identity to
every internal boundary.

## 3. Full production-port identity

For `t < K`, write `P_t` for the executable root-sequence profile restarted
at time `t`. The production path stores

```text
((value(t), simplexRoot(t)), D(t)).
```

After converting the simplex root to its Boolean PMF family, Lean proves

```text
rawTerminalPort(P_t)
  = rawPort(productionDynamicDebtPoint(t)).
```

Coordinatewise, this says:

```text
terminalPayoff(P_t)       = value(t),
liveRoot(P_t, 0)          = operationalRoot(t),
terminalSemanticDebt(P_t) = D(t).
```

At `t=K`, the debt equality still holds. The complete port theorem is stated
only for `t<K` because the padded production point retains the path's terminal
simplex coordinate, while the operational extension intentionally ignores
that coordinate and plays all-Continue. This is a representational endpoint
convention, not a debt mismatch.

## 4. What this changes for stopping-law geometry

The caveat in the fixed-port experiment is now removed on the production
finite-chain class. A terminal semantic debt coordinate of an executable
finite exact-chain suffix is precisely its production exact-`D` costate.

Therefore a stopping-law deformation which preserves

```text
(payoff, boundary root, terminal semantic debt)
```

preserves the corresponding raw production debt point whenever its endpoint
profiles are such finite exact-chain suffixes.

This is a real improvement over merely preserving an infinite semantic
summary: the summary is now known to be the seam state used by the exact-`D`
compiler.

There is still an important closure issue. The stopping-law mixture between
two exact-chain endpoint profiles need not itself satisfy every local
Nash--Bellman edge equation. The fixed-port theorem preserves its behavioral
port; it does not automatically put every mixed profile back inside the
production finite-chain carrier. For replacement, one needs either:

- a same-port deformation which stays in the exact-chain class;
- a decoder from a fixed semantic port back to an exact finite chain; or
- a proof that the compiler can consume the semantic port directly without
  retaining the intermediate local-chain presentation.

## 5. The useful equivalence classes

On executable all-Continue completions of production chains, two preterminal
boundaries are equivalent exactly when their raw behavioral terminal ports
agree:

```text
(value, root, exact-D) = (value', root', exact-D').
```

Lean proves the iff for suffixes taken from two different production paths
and two different cutoffs. The raw-root map is injective because the
simplex/PMF conversion is an equivalence, so this is equality of the actual
production points, not equality only after a lossy observation map.

This is a useful axis because it is simultaneously:

- behavioral: it records actual payoff and unrestricted deviation debt;
- dynamic: it is the exact costate propagated by the finite recursion;
- splice-facing: it records the current live root and continuation state;
- finite-dimensional for a fixed finite player set.

It is not a finite exact quotient. At fixed accuracy, enriched compression
and finite witness passports give finite codebooks/atlases, but exact port
fibers may still be uncountable and may be singleton fibers. The outstanding
question is multiplicity and controllability inside a prescribed fiber, not
semantic identification of the debt coordinate.

## 6. Relation to finite stochastic-button caps

The finite-splice and finite-cap convergence experiments give a complementary
reduction. They move all late stopping mass of one player's stochastic button
to a finite cap date. The prescribed payoff and full behavioral envelope are
each controlled by

```text
2 M * (
  late finite stopping mass
  + Never mass * pair-deleted survival to the cap
).
```

and semantic debt is controlled by twice that amount. Late finite stopping
mass always tends to zero. The deleted clock is now factored exactly at
infinity as the product of the playerwise Never masses outside the
mover/observer pair. Thus the explicit cap error tends to zero iff the moved
law has zero Never mass or two distinct other laws do. This is an exact finite
zero-pattern classification of the universal splice bound; payoff-specific
cancellations may still do better.

One cutoff simultaneously controls every player's payoff, unrestricted
behavioral envelope, and semantic debt under either condition. See
[`QUITTING_STOPPING_LAW_FINITE_CAP_CONVERGENCE.md`](QUITTING_STOPPING_LAW_FINITE_CAP_CONVERGENCE.md).

Two distinct zero-Never seeds already let the cap construction iterate over
all players inside one common error budget, with no Never restriction on the
remaining laws. The resulting profile gives every unilateral deviator a
distinct finite sure-quitting opponent, and all deviation problems share a
single profile-dependent finite horizon. The cap dates may be required to lie
after any fixed entrance prefix, which preserves its complete live-root word
exactly.

There is also an unconditional alternative when fewer than two seeds exist.
Retain a finite global root prefix and attach the matching elementary boundary
`Never`, `sureJoint`, or `sureSolo(owner)`. The full terminal semantic pair of
this representative is exactly a finite backward recursion from an explicit
boundary pair, and terminal approximate Nash transports. This is a
finite-semantic reduction, not necessarily a finite-horizon one; it preserves
the cemetery branch precisely in the regimes where deviations can see it. See
[`QUITTING_ELEMENTARY_TAIL_SEMANTIC_REDUCTION.md`](QUITTING_ELEMENTARY_TAIL_SEMANTIC_REDUCTION.md).

Once the all-player capped profile also lies in the exact finite-chain class,
the present
bridge identifies every stored dynamic-debt coordinate with its literal
behavioral gap. What remains unformalized is exact projection of the capped
word back to a Nash--Bellman chain while preserving both external ports.

## 7. Revised next question

The dynamic-debt bridge is no longer the next problem. The sharp question is:

```text
Given a prescribed pair of production exact-D boundary points, is there a
nontrivial stopping-law deformation or finite decoder which keeps both points
fixed and remains inside (or returns to) the exact Nash--Bellman chain class?
```

There are two distinct subproblems.

1. **Fiber multiplicity:** prove that a relevant two-ended port fiber contains
   more than one executable realization.
2. **Exact-chain closure:** move inside that fiber without losing the local
   Bellman and zero-slack Nash equations.

The first is geometric. The second is algebraic/strategic. Neither is solved
by compactness alone, but the semantic mismatch between terminal debt and
exact-`D` has been eliminated.

## 8. Lean inventory

The experiment formalizes:

- literal equality of a phase switch with an already all-Continue-completed
  root sequence;
- the generic positive-length entrance bridge;
- its time-translated arbitrary-suffix form;
- the production entrance specialization;
- the production equality at every nonterminal time;
- the padded cutoff debt equality;
- one uniform all-times debt theorem; and
- the full preterminal payoff/root/debt port identity;
- injectivity of the raw-root presentation; and
- the exact iff between production-point equality and behavioral-port
  equality for suffixes of arbitrary two finite paths.

The file compiles without `sorry` or `admit`. All printed capstones use only
`propext`, `Classical.choice`, and `Quot.sound`.
