# Independent review and strengthening of the finite reset compiler

## Verdict

The candidate's core finite reset-arrival theorem is correct, and its
attachment to one actual three-role endpoint row is mathematically sound.
Its finite-stopper acquisition phase is not new: it is already proved in Lean
by `exists_bounded_quittingPureTimeSelfResetChain`, including the exact
payoff/debt identity and the length bound `card(I)+1`.  The new general content
is the passage from that checked finite stopper to exact zero debt plus
same-profile opponent incidence.

The finite-deadline induction is unnecessary, however.  Its no-incidence arm
can be replaced immediately by Quit-at-zero, after which one further exact
response gives unit incidence.  Consequently:

```text
finite-stopper phase: at most 2 exact profitable updates;
arbitrary finite-player profitable path: at most card(I) + 3 updates;
Fin 4 role-aligned path: at most 7 updates.
```

There is also a simpler static strengthening: every terminal exploitability
witness already supplies a pure simultaneous two-player target with exact
zero debt and incidence exactly one.  This follows from the checked
empty-set/singleton toggle geometry and is recorded separately in
[`FINITE_RESET_STRENGTHENER__CANONICAL_TWO_QUIT_RESET`](../notes/FINITE_RESET_STRENGTHENER__CANONICAL_TWO_QUIT_RESET.md).

The final packet should describe the endpoint-to-reset list as a finite
all-profitable pure-time reachability path, not a backward compiler.  It does
not transport equilibrium, payoff, law, routed atoms, or roles backward or
forward.  The final reset law and labels are fresh; the endpoint data remain
historical provenance.

Subject to those corrections and the sharper bounds below, the result is a
valid answer to item 4 of
`questions/FIN4_THREE_ROLE_TARGET_ASCENT_CONSUMER.md`: transition to another
stated source-attached completion component.  It is not item 3, and it does
not consume the fixed-law reset dispatch's all-Continue arm.

## Claim checked

Let `I` be finite, `gamma > 0`, and suppose

```text
HasTerminalExploitabilityGap reward gamma.
```

Starting from any actual behavioral profile, the candidate constructs a
finite list of unilateral deterministic stopping-time updates ending at an
actual profile `pi` with distinct `q,j` such that

```text
d_q(pi) = 0,
0 < Inc_q(j, law(pi)).
```

For a strict Fin4 three-role ascent, it selects one actual endpoint row with a
literal total-debt ascent, makes the fixed endpoint recipient the first
profitable responder, and applies the general theorem.  The resulting actual
semantic/law target enters the checked `QuittingFixedLawResetDispatch` from
the incoming positive global-minimum source.

## What checks in the submitted proof

### Pure-time cap approximation

`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` identifies
the unrestricted behavioral cap with the supremum of finite deterministic
quit times and Never.  Updating a player's own prescribed strategy leaves
that player's cap unchanged because all deviations overwrite the same
coordinate.  Thus an `epsilon`-optimal pure time leaves updated debt at most
`epsilon`.

### Finite-stopper acquisition

At every current profile the terminal gap selects a debt coordinate at least
`gamma`.  A pure time within `gamma/4` of its cap gains at least
`3 gamma/4`.  If it is Never, the player was not already literally Never, so
the update strictly enlarges the prescribed-Never set.  Other-player updates
do not remove prior Never coordinates.  Hence there are at most

```text
m(start) = card {i | start_i is not literally Never}
```

Never updates before one finite update appears.  The finite updater has debt
at most `gamma/4 < gamma`.  This gives a finite stopper after at most
`m(start)+1 <= card(I)+1` profitable updates.

This count, rather than “at most `card I` and then one” left only in prose,
should be a public quantitative field or theorem.

More importantly, this entire phase should be consumed rather than reproved.
`HasQuittingUniformTerminalDebtFloor`, `QuittingPureTimeSelfResetStep`, and
`exists_bounded_quittingPureTimeSelfResetChain` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticBoundedSelfReset.lean`
already give exactly this chain.  The adapter
`QuittingTerminalExploitabilityWitness.hasUniformTerminalDebtFloor` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/BoundedSelfResetLocalization.lean`
supplies its hypothesis from the retained witness.  Taking
`error = gamma/4` gives the candidate's finite stopper with debt below
`gamma` and chain length at most `card(I)+1`.

### Exact cap attainment under a finite stopper

If player `a` quits surely at time `T`, then for every other player all pure
times strictly after `T` have the same payoff as Never.  Pure-time extremality
therefore turns the unrestricted cap into the maximum of the finite family

```text
Never, 0, 1, ..., T.
```

If `d_a < gamma`, a gap-selected debtor `i` is distinct from `a`.  Updating
`i` to an exact maximizing pure time gives `d_i=0`.  The submitted split is
correct: positive opponent incidence finishes, while zero opponent incidence
forces the complete terminal law to be the singleton law at `i`.

### Endpoint attachment and dispatch

The convergence fields of the checked three-role endpoint allow one common
rank `N` satisfying both the literal total-debt separation and the recipient
debt floor.  The recipient's first selected pure response has gain strictly
larger than

```text
eta / 2,
eta = resolution^2 * D_* / 64,
```

and leaves recipient debt below `gamma`.  If finite it is the stopper; if
Never it is the first strict Never-set step.

The eventual profile is actual, so its semantic pair and complete outcome law
belong jointly to the terminal semantic/law carrier.  Its zero-debt and
positive-incidence fields, together with the incoming source minimum and
terminal witness, exactly match
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.

## Strengthening 1: deadline descent collapses to two steps

The submitted recursion proves termination but misses a stronger consequence
of its own no-incidence arm.

Suppose `a` is a finite stopper with `d_a < gamma`.  Select a distinct
gap debtor `i` and an exact maximizing pure time `q`.  Let

```text
sigma_q = sigma[i <- Q_i(q)].
```

If `sigma_q` has positive incidence in an opponent of `i`, take this one
update and finish.

Otherwise `law(sigma_q)` is the singleton law at `i`.  In particular no
opponent quits before or together with `i` on the reached history.  Therefore
replacing `q` by time zero produces the same singleton terminal outcome and
the same payoff for `i`.  Since `q` attained the cap, `Q_i(0)` also attains
the cap.  Make the actual first update

```text
sigma_0 = sigma[i <- Q_i(0)].
```

It has `d_i(sigma_0)=0` and `i` quits surely at time zero.

Apply the gap at `sigma_0`.  It selects `k != i`.  Against a sure time-zero
stopper, `k`'s cap is the maximum of immediate Quit and Never; choose an exact
one and update `k`.  The new owner `k` has zero debt.  Regardless of which
maximizer is chosen, player `i` belongs to every terminal coalition, so

```text
Inc_k(i, finalLaw) = 1.
```

Thus the exact phase has length at most two, with both gains at least
`gamma`.  The natural deadline is not needed as a recursion rank.

Combining this with acquisition gives the exact upper bound

```text
path length <= m(start) + 3 <= card(I) + 3.
```

For `Fin 4`, the bound is seven.  With the endpoint recipient forced first:

- if the recipient response is finite, the complete path has length at most
  three;
- if it is Never, at most three further Never updates, one finite update, and
  two exact updates remain, so the complete path has length at most seven.

These are upper bounds for the stated all-profitable construction.  No claim
is made that seven is the globally shortest possible path for every table.
The two-step exact phase is locally necessary in the branch where the first
exact responder preempts alone: that first profile has no opponent incidence
for its new zero-debt owner.

## Strengthening 2: a canonical static reset target

The general reset existence can be made simpler and stronger if profitable
connectivity from an arbitrary start is not required.

The checked declarations

```text
exists_terminalGap_le_soloReward
exists_collision_gain
exists_immediateSingletonCollision
```

select distinct players `a,b` with

```text
gamma <= r({a},a),
r({a},b) + gamma <= r({a,b},b).
```

At the pure profile in which exactly `{a,b}` Quit at zero, player `b`'s
unrestricted cap is the better of joining and staying out.  The second
inequality makes the prescribed joining payoff maximal, hence `d_b=0`; the
law is exactly the point mass at `{a,b}`, hence `Inc_b(a)=1`.

From any starting profile this canonical target is reachable by at most
`card(I)` coordinatewise pure-time rewrites, but those rewrites need not be
profitable.  This distinction should be explicit in the final theorem design:

```text
canonical law + unit incidence + card(I) rewrite bound
or
all-profitable endpoint path + card(I)+3 bound + noncanonical final law.
```

The first alternative shows that reset-target existence itself is not what
uses the strict ascent.  The endpoint wrapper's new content is the
all-profitable path beginning with the fixed recipient and the co-retention of
one literal strict-ascent row as provenance.

## Exact novelty boundary

The following parts are already checked and should not be presented as new:

- behavioral-to-pure-time cap extremality;
- own-coordinate cap invariance and the exact gain/debt identity;
- the Never-set cardinal descent;
- construction of a finite pure-time stopper with residual debt below a
  prescribed positive error; and
- the `card(I)+1` acquisition-chain bound.

The candidate adds:

- exact cap attainment once an opponent has a finite deterministic deadline;
- conversion of that attained response to a zero-debt/incidence arrival;
- after the strengthening above, a two-step rather than deadline-ranked exact
  finish; and
- attachment to one retained endpoint row with the fixed recipient as the
  first profitable response.

The static simultaneous-pair reset is mostly a new wrapper around already
checked terminal-gap toggle and immediate-collision declarations.  Its value
is a simpler and stronger target law, not a new source of collision geometry.

## Minimal hypotheses

For the arbitrary-start all-profitable theorem, the clean hypothesis is a
common positive terminal gap.  The proof uses no Fin4 data, reward bound,
minimum source, compactness, stationary restriction, or endpoint law.

For the canonical static two-Quit target, a global gap is stronger than
necessary.  It suffices to supply an `ImmediateSingletonCollision` with
positive margin.  More minimally still, only the two displayed table
inequalities and `a != b` are used.

If profitable edges are dropped entirely, absence of a terminal Nash profile
is enough for several clearing constructions, but the canonical toggle proof
is cleaner and already supplied quantitatively by the terminal witness.  Such
nonprofitable paths should not be conflated with better-response reachability.

## Necessary corrections and nonclaims

### The question arm is item 4

Section 8 says output 3.  The transition to a fixed-law reset dispatch is item
4.  No positive cumulative admissible-payoff near-return is produced.

### “Backward compiler” is false as a semantic claim

A list of profitable unilateral deviations does not transport Nashness,
uniform payoff delivery, or deviation bounds backward.  The one-player table
with singleton payoff `1` is already a counterexample: all-Never updates
profitably to Quit-at-zero; the latter is terminal Nash and the former is not.
The terminal law simultaneously changes from nonabsorption to the singleton
law.  Hence neither equilibrium nor law can be pulled backward across even
one profitable pure-time edge.

Use “finite all-profitable pure-time path” or “better-response reachability
certificate.”  If the word compiler is retained, it must be qualified as
provenance only.

### Endpoint laws, routed atoms, and roles are not preserved

The selected endpoint source/target profiles, mover, recipient, routed atom,
and target law can remain fields of the handoff wrapper.  After the first
recipient update, however, none of their law or atom bounds is shown for any
later profile.  Subsequent updates may overwrite the recipient, and the final
reset owner and incidence label are selected by the gap dynamics.  There is
no conclusion equating either final label with mover or recipient.

In the branch where the recipient itself is the finite stopper, the first
exact gap responder is necessarily different from the recipient; if that
step already has incidence, the final reset owner is therefore not the
recipient.  This directly rules out a general owner-preservation claim from
the presented construction.

### Strict ascent has a limited role

Strict ascent is used to retain a finite endpoint row whose total-debt
difference is separated by half the limiting gap.  The recipient response
floor already comes from the endpoint's recipient-rise estimate, and the
reset path works from every behavioral profile under the hard residual.
Therefore the theorem attaches the reset path to strict ascent; strict ascent
does not cause or power reset arrival.

### The downstream reset node remains open

`QuittingFixedLawResetDispatch` still has its absorbing positive-survival
descent versus all-Continue cap-face alternative.  The candidate consumes
neither alternative recursively.  It answers the source-attached transition
question but is not a uniform-equilibrium theorem or global atlas closure.

## Boundary and falsification tests

1. **All-Never boundary.** A positive gap cannot be witnessed by the identity
   Never update, so finite-stopper acquisition cannot remain forever in the
   prescribed-Never phase.
2. **Deadline zero.** A distinct exact responder has only immediate Quit and
   Never as payoff-relevant pure choices; the sure zero-time stopper gives
   unit incidence either way.
3. **No-incidence branch.** Certain absorption plus zero incidence in every
   opponent forces the singleton law; this is precisely what permits the
   Quit-at-zero shortcut.
4. **Single-player boundary.** A positive terminal witness is impossible;
   `QuittingTerminalExploitabilityWitness.one_lt_card` checks the required
   cardinal consequence.
5. **Law-preservation falsifier.** The one-player `Never -> Quit(0)` update
   changes the full law and refutes any generic law-transport reading.
6. **Role-preservation falsifier.** When the fixed recipient is the finite
   low-debt stopper, every gap-selected exact responder is a different player.

## Source audit

Inspected exact declarations and nearby interfaces:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` and
  `quittingTerminalPayoff_update_pureTimeBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- `HasTerminalExploitabilityGap.exists_debt_ge` in
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`;
- `HasQuittingUniformTerminalDebtFloor`, `QuittingPureTimeSelfResetStep`, and
  `exists_bounded_quittingPureTimeSelfResetChain` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticBoundedSelfReset.lean`;
- `QuittingTerminalExploitabilityWitness.hasUniformTerminalDebtFloor` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/BoundedSelfResetLocalization.lean`;
- `quittingTerminalPayoff_update_pureSetRoot_le` and
  `quittingTerminalSemanticDebt_pureSetRoot_eq` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`;
- `QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward`,
  `exists_collision_gain`, and `one_lt_card` in
  `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`;
- `QuittingTerminalExploitabilityWitness.exists_immediateSingletonCollision`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/ImmediateSingletonCollision.lean`;
- `QuittingImmediateSingletonCollision.margin_le_collider_gain` and its
  all-behavior debt formulas in
  `UniformEquilibrium/Quitting/Classification/ImmediateSingletonCollision.lean`;
- `QuittingFixedLawResetDispatch` and
  `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `ConcentratedCollisionThreeRoleEndpointLaw` in
  `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`;
- `QuittingTerminalExploitabilityWitness.exists_finFour_prescribedOwner_resetDispatch`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourPrescribedOwnerResetAlignment.lean`;
- `questions/FIN4_THREE_ROLE_TARGET_ASCENT_CONSUMER.md`.

No original-paper theorem is invoked for the new finite-path shortcut.  The
pure-set toggle mechanism is documented in the checked source as standard
first-stage quitting-game analysis; the new content is its reset-target and
path-length packaging.  No Lean-check status is assigned to that packaging.

## Recommended final theorem organization

1. State the arbitrary-finite-player all-profitable reset-arrival theorem with
   the public length bound `card(I)+3`, reusing the checked bounded self-reset
   chain and adding only the two-step finite-stopper finish.
2. State the canonical simultaneous-pair/unit-incidence corollary separately,
   preferably as a small wrapper around `ImmediateSingletonCollision`.
3. State the Fin4 adapter last: one common endpoint rank, literal finite
   ascent, fixed-recipient first response, length at most seven, actual final
   reset law, and checked fixed-law dispatch.
4. Put endpoint law/roles under retained provenance fields, not preservation
   fields.
5. State explicitly that the result answers question item 4 and leaves the
   reset dispatch's dynamic alternative open.
