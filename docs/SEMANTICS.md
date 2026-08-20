# Semantic contract

This file gives the stable model and quantifier conventions needed to read the
project. It contains no current frontier claims.

## Uniform-equilibrium payoff

For a finite stochastic game `G`, initial state `s₀`, and payoff vector `v`,
`G.IsUniformEquilibriumPayoff s₀ v` means:

```text
for every ε > 0,
  there exist one behavioral profile σ and one threshold T₀ such that
  for every horizon T ≥ T₀,
    σ is an ε-Nash equilibrium of the T-stage expected-average game, and
    every coordinate of its expected-average payoff is within ε of v.
```

The target `v` is fixed before the accuracy is chosen. The profile and horizon
threshold may depend on the accuracy, but the same selected profile must work
for every horizon beyond its threshold. A deviation replaces one player's
whole behavioral strategy, not merely one stationary action or a bounded-memory
controller.

The canonical execution-level definitions are in
[`GameTheory/GameTheory/Stochastic/Uniform.lean`](../GameTheory/GameTheory/Stochastic/Uniform.lean):

- `Stochastic.Game.IsεHorizonNash`;
- `Stochastic.Game.IsUniformεEquilibrium`;
- `Stochastic.Game.IsUniformEquilibriumPayoff`; and
- `Stochastic.Game.HasUniformDeviationCapConstructor`.

The project proof view is in
[`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`](../UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean):

- `IsεHorizonNash`;
- `IsUniformεEquilibrium`;
- `IsUniformEquilibriumPayoff`; and
- `HasUniformDeviationCapConstructor`.

The last predicate is the delivery-and-deviation-cap constructor and is proved
equivalent to the semantic payoff property. The finite-state, finite-action
bridge in
[`UniformEquilibrium/ProofView/Native/Equilibrium.lean`](../UniformEquilibrium/ProofView/Native/Equilibrium.lean)
proves exact equivalence of finite-horizon approximate Nash and uniform-payoff
predicates between the canonical runner and the project proof view.

## General model scope

The present `StochasticGame` action type depends on the player but not on the
state. Consequently the general existence proposition has state-independent
action sets. Padding a state-dependent model with duplicate illegal labels is
not automatically faithful under perfect monitoring: duplicate labels can act
as observable randomization devices.

Finite public memory, private randomized memory, clock dependence, stationary
play, finite-period play, and unrestricted behavioral strategies are distinct
classes unless a named theorem transports between them.

## Quitting games

A quitting game has one live state. Every player chooses `Bool` at every live
stage (`false` = Continue, `true` = Quit). The first nonempty set of simultaneous
quitters selects an absorbing state and its terminal reward; if nobody ever
quits, active play continues with stage reward zero.

The model is defined in
[`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`](../UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean).
The open quitting proposition concerns the live state `none`; absorbed states
are already solved by the generic absorbing-state result.

## Terminal payoff and finite averages

`quittingTerminalPayoff` is the absorption-probability-weighted terminal reward,
with nonabsorption contributing zero. For every behavioral profile—including
profiles produced by unilateral deviations—the expected finite-average payoff
converges to this terminal payoff. The definitions and convergence theorem are
in
[`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean`](../UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean).

This convergence is a bridge, not a license to identify every asymptotic
notion. The project distinguishes:

- finite-horizon expected-average Nash;
- uniform finite-horizon equilibrium;
- terminal approximate Nash;
- limiting or undiscounted payoff notions; and
- discounted equilibrium and its endpoint data.

Use a named theorem whenever moving between them. The detailed notion map is
[`NOTION_LATTICE.md`](NOTION_LATTICE.md).

## Quitting-game semantic waist

For finite quitting games, terminal approximate Nash profiles at every positive
error exist if and only if some uniform-equilibrium payoff exists. The exact
selection theorem is
[`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`](../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean).

Nonexistence is equivalent to a fixed positive terminal exploitability gap
against every behavioral profile. The exact interface is
[`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`](../UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean).

These two results determine what a complete positive proof or a complete
counterexample must ultimately provide.
