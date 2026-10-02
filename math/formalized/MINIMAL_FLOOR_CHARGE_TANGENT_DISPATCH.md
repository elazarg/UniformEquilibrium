# Minimal-Floor Dispatch for Quitting Charge Tangents

Author: `CODEX_NOETHER`
Independent review:
[`CODEX_GAUSS`](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_9.md)

The reviewer independently reconstructed the compiler argument, checked the
exact threshold and quantifiers, and tested all three algebraic boundary
examples. The one requested prose correction is incorporated here.

## Exact statement

Let `I` be a nonempty finite player type with decidable equality and let

```text
r : {S : Finset I // S.Nonempty} -> (I -> Real)
```

be an arbitrary finite quitting reward table. Let
`data : QuittingChargeTangentData r`. Thus `data` consists of real vectors
`mass`, `boundary`, and `tangent` satisfying, for every player `i`,

```text
0 <= mass_i,
sum_i mass_i = 1,
tangent_i = mix_i - boundary_i,
solo_i <= boundary_i,
chi_i <= boundary_i,
0 < mass_i  ->  boundary_i = solo_i,
```

where

```text
solo_i = r({i})_i,
chi_i  = quittingPunishmentValue r i,
mix_i  = sum_j mass_j * r({j})_i.
```

Define the nonnegative action and punishment gaps

```text
a_i = boundary_i - solo_i,
f_i = boundary_i - chi_i,
```

and the minimal security floor

```text
ell_i = max(solo_i,chi_i).
```

Then at least one of the following holds:

1. there is a payoff `x` such that
   `(quittingGame r).IsUniformEquilibriumPayoff none x`;
2. for some player `i`,
   `tangent_i < -min(a_i,f_i)`, equivalently `mix_i < ell_i`; or
3. for some player `i`, `0 < mass_i` and `0 < tangent_i`.

Consequently, if `r` is equipped with a
`QuittingTerminalExploitabilityWitness r`, alternatives 2 and 3 form an exact
disjunction: every charge-tangent datum either falls below the minimal
coordinatewise security floor somewhere or moves strictly outward on an
occupied owner.

## Conjecture-facing change

The checked theorem
`QuittingTerminalExploitabilityWitness.chargeTangentData_underfunded_or_active_funded`
(`UniformEquilibrium/Diagnostics/Quitting/Debt/ChargeTangentPacket.lean`)
leaves the alternatives

```text
some tangent_i < 0,
or some active tangent_i > 0.
```

The first branch charges every negative passive tangent, even when the
boundary has enough strict own-solo and punishment slack to absorb it. The
result here strictly narrows that branch to

```text
tangent_i < -min(boundary_i-solo_i, boundary_i-chi_i).
```

Thus a negative tangent inside both buffers is already consumed by the
checked complementary-singleton-mixture route. The remaining negative arm
must breach at least one of the two security constraints. The other live arm
is positive motion on an occupied owner. This is a strict reduction of the
named charge-tangent obligation, not a producer for either residual arm and
not a proof of the full conjecture.

## Definitions and assumptions

`quittingPunishmentValue r i` is the behavioral min-max value used by the
project: an infimum over complete opponent behavioral profiles of player
`i`'s supremum over complete behavioral replies. The theorem does not assume
attainment of that infimum.

The input `mass` is a real simplex vector encoding limiting singleton-owner
occupation. It is not a public randomization device and is not asserted to be
the terminal law of a supplied profile. The proof uses it as the weight vector
of a checked face-circulation certificate.

All inequalities are coordinatewise. No sign assumption is made on the raw
reward table, its nonsingleton coalition rewards, `boundary`, or `tangent`.
Finiteness and nonemptiness are the only player-set assumptions.

## Source correspondence

The relevant checked declarations are:

- `QuittingChargeTangentData`
  (`UniformEquilibrium/Quitting/Boundary/Analytic/ChargeTangent.lean`), which
  defines exactly the input fields above;
- `QuittingPositiveDebtDynamicTailWitness.exists_chargeTangentData_of_windows`
  (`UniformEquilibrium/Diagnostics/Quitting/Debt/ChargeTangentPacket.lean`),
  which extracts such data from arbitrary positive-absorption windows escaping
  along the checked optimized exact-debt tail;
- `QuittingTerminalExploitabilityWitness.chargeTangentData_underfunded_or_active_funded`
  in the same file, which gives the prior unbuffered sign dispatch;
- `QuittingChargeTangentData.punishmentValue_le_singletonMixture_iff_neg_tangent_le_slack`
  (`UniformEquilibrium/Quitting/Cycles/ConditionedSlackThreshold.lean`), which
  identifies the punishment-buffer half of the threshold; and
- `exists_uniformEquilibriumPayoff_of_complementarySingletonMixture`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/SingletonMixtureCompiler.lean`),
  the checked downstream semantic consumer.

The exact-D tail extraction is the named actual-data adapter. The consumer is
valid for every nonempty finite player type despite its source path. It
constructs a finite-closing face circulation and concludes an ordinary
uniform-equilibrium payoff in the project's behavioral semantics.

A narrow search for the declaration names and the phrases `minimal floor`,
`underfunded_or_active`, `min tangent`, and `complementarySingletonMixture` in
`UniformEquilibrium/` found the unbuffered dispatch and the one-buffer slack
identity, but no theorem combining both gaps into this sharper disjunction.
No paper theorem is invoked or translated; the result is a new algebraic
reduction among project-owned checked interfaces.

## Proof

Assume alternatives 2 and 3 both fail. For every player `i`, failure of 2 and
the tangent identity give

```text
mix_i - boundary_i = tangent_i >= -min(a_i,f_i).
```

But

```text
ell_i - boundary_i
  = max(solo_i-boundary_i, chi_i-boundary_i)
  = max(-a_i,-f_i)
  = -min(a_i,f_i).
```

Therefore `ell_i <= mix_i`. By definition, both `solo_i <= ell_i` and
`chi_i <= ell_i`.

Now fix an owner `i` with `0 < mass_i`. The positive-mass pin gives
`boundary_i=solo_i`, hence `a_i=0`. Because `f_i>=0`,
`min(a_i,f_i)=0`. Failure of alternative 2 gives `0<=tangent_i`, while
failure of alternative 3 gives `tangent_i<=0`. Thus `tangent_i=0`, and the
tangent identity gives

```text
mix_i = boundary_i = solo_i.
```

The data's mass nonnegativity and unit sum, the already proved
`ell<=mix`, the active pinning just obtained, and the inequalities
`solo<=ell` and `chi<=ell` are exactly the hypotheses of
`exists_uniformEquilibriumPayoff_of_complementarySingletonMixture` with floor
`ell`. That checked theorem supplies alternative 1. This proves the
trichotomy. If a terminal-exploitability witness rules out alternative 1, the
last two alternatives are the asserted exact disjunction.

## Probability, information, and deviation audit

The new proof is finite-dimensional algebra after the charge-tangent datum has
been supplied; it performs no conditioning, limit exchange, or stopping-time
optimization. The checked tail adapter obtains `mass` and `tangent` by a
subsequence limit of literal positive-absorption windows and does not introduce
correlated play.

The checked complementary-mixture consumer uses the project's simultaneous
quitting game and a finite-closing circulation. Its conclusion is
`IsUniformEquilibriumPayoff`, so one fixed payoff works at all sufficiently
long horizons for each accuracy and a unilateral deviator may replace their
entire history-dependent behavioral strategy. The packet does not weaken that
deviation class to stationary, pure-time, periodic, or bounded-controller
deviations. No public coin or extra observation is assumed.

## Boundary tests

Take two players `0,1` and set the double-quit reward to `(0,0)`.

### Buffered negative tangent

Let

```text
r({0}) = (1,1/2),  r({1}) = (0,0),
mass   = (1,0),    boundary = (1,1).
```

Then `mix=(1,1/2)` and `tangent=(0,-1/2)`. The checked bound
`quittingPunishmentValue_le_max_solo` gives `chi_0<=1` and `chi_1<=0`, so
`ell=(1,0)`. The mixture dominates `ell`, and the active coordinate has zero
tangent. Hence the new theorem compiles this datum, while the older dispatch
still enters its undifferentiated negative-tangent arm.

### Genuine minimal-floor failure

Change only `r({0})_1` from `1/2` to `-1/2`, keeping the same mass and
boundary. Then `mix=(1,-1/2)`, `tangent=(0,-3/2)`, and the second coordinate
falls below its own-solo floor `0`. Alternative 2 is genuine.

### Genuine positive-active arm

Let

```text
r({0}) = (0,1),  r({1}) = (1,0),  r({0,1})=(0,0),
mass   = (1/2,1/2),
boundary = (0,0).
```

Then `mix=tangent=(1/2,1/2)`. Both owners are active and pinned to their own
zero solo reward, and `quittingPunishmentValue_le_max_solo` supplies
`chi_i<=0=boundary_i`. Alternative 3 is genuine. These three tables test the
dispatch algebra; none is claimed to be a game counterexample.

## Adapter and consumer

For the checked optimized exact-debt tail,
`exists_chargeTangentData_of_windows` is an actual-data adapter: every chosen
sequence of positive-absorption windows whose starts escape to infinity has a
subsequence converging to a datum with all required fields. Applying the new
dispatch to that datum removes buffered passive negative drift from the
hypothetical-counterexample frontier.

If neither residual arm occurs,
`exists_uniformEquilibriumPayoff_of_complementarySingletonMixture` consumes
`data.mass` with floor `max(solo,chi)` and produces a uniform-equilibrium
payoff. The reduction and this conditional semantic consumer are checked in
the module cited below.

## Checked Lean realization

`QuittingChargeTangentData.uniformPayoff_or_minimalFloor_underfunded_or_active_funded`
checks the three-way dispatch.  The counterexample-facing reductions
`QuittingTerminalExploitabilityWitness.chargeTangentData_minimalFloor_underfunded_or_active_funded`
and
`QuittingTerminalExploitabilityWitness.chargeTangentPacket_minimalFloor_underfunded_or_active_funded`
are proved in
`UniformEquilibrium/Diagnostics/Quitting/Debt/ChargeTangentPacket.lean`.
These are conditional reductions for supplied tail-derived data; they do not
supply the remaining near-return producer.

## Scope and nonclaims

- This is not a uniform-equilibrium proof for arbitrary quitting games.
- It does not construct a positive exact admissible return, chronological
  debt-shadowing certificate, or divergent support-rational path.
- It does not repair minimal-floor underfunding or positive active tangent;
  those are precisely the two residual arms.
- It does not assert that every canonical punishment-floor orbit already has
  a checked adapter to `QuittingChargeTangentData`; the named checked adapter
  is for windows of the optimized exact-debt tail.
- It does not identify `mass` with a public lottery used by the players.
- The finite dispatch and its counterexample-facing wrapper are proved in Lean;
  no consumer of either residual arm is claimed.
