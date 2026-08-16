# Uniform-equilibrium mathematical frontier

This file states the current mathematical dependency boundary. Exact theorem
truth belongs to Lean declarations under their imports; the generated
declaration index is [`STATUS.md`](STATUS.md). Detailed compiler interfaces are
in [`TOOLKIT.md`](TOOLKIT.md), and the mechanically maintained quitting leaf
ledger is [`QuittingProofFrontier.json`](QuittingProofFrontier.json).

This is not a chronology. Explicitly historical mathematical synthesis is
scoped under [`audits/`](audits/README.md); repository-transition provenance,
old source paths, and extraction decisions belong only in
[`../TRANSITION.md`](../TRANSITION.md).

## Exact questions

The project distinguishes two existence propositions:

1. existence of a uniform-equilibrium payoff for finite stochastic games with
   state-independent action sets; and
2. existence for every finite quitting game.

The second is a strict specialization and is not a known normal form for the
first. Padding state-dependent action sets can introduce observable duplicate
labels and is not silently semantics-preserving. See
[`SEMANTICS.md`](SEMANTICS.md) for the exact quantifier and model contract.

Current proposition and capstone declarations are generated in
[`STATUS.md`](STATUS.md). The declaration index does not substitute for a Lean
build.

## Semantic waist for quitting games

For finite quitting games, the decisive positive interface is terminal
approximate Nash existence at every positive error. The integrated selection
theorem turns such a family into one fixed uniform-equilibrium payoff, and the
reverse implication also holds. Terminal verification, fixed-target selection,
and uniform finite-horizon delivery are separate proof obligations.

The decisive negative interface is a fixed positive terminal exploitability
gap against every behavioral profile. Excluding stationary, periodic,
finite-public, or bounded-controller profiles is only a screen unless a theorem
transfers it to the full behavioral class.

Thus the two accepted endpoints are:

```text
terminal approximate Nash profiles at every positive error
                           |
                           v
              uniform-equilibrium payoff

fixed positive terminal gain against every behavioral profile
                           |
                           v
             no uniform-equilibrium payoff
```

## Established construction boundary

The integrated corpus contains several sound ways to reach the positive
endpoint from supplied structured data:

- target-anchored and diagonal terminal tails;
- support-retaining paths and periodic witnesses;
- essential adaptive-potential systems;
- signed and single-seam projective lassos;
- sufficiently charged finite forward packets;
- punishment-completed absorbing cycles; and
- bounded multi-owner face circulations.

These are conditional producer/compiler strata at their stated inputs. None is
silently a universal grammar for all quitting equilibria. Their exact inputs,
outputs, and nonclaims are indexed in [`TOOLKIT.md`](TOOLKIT.md).

The development also contains sound diagnostics and no-go theorems. A
counterexample to one certificate language closes that route; it does not prove
nonexistence of equilibrium unless it reaches the all-behavior terminal-gap
interface.

## Live formal leaves

The quitting counterexample-regime search is maintained as an explicit finite
antichain of formal leaves. The ledger records each representative, source
producer, obstruction class, and the evidence attached to transitions. This is
a proof-search decomposition inside the formalized regime, not an exhaustive
classification of every equilibrium profile.

<!-- BEGIN GENERATED OPEN LEAVES -->
This table is generated from [`QuittingProofFrontier.json`](QuittingProofFrontier.json).

| Manuscript alternative | GitHub issue | Leaf | Obstruction | Representative | Source producer |
| --- | --- | --- | --- | --- | --- |
| 2 | [#4](https://github.com/elazarg/UniformEquilibrium/issues/4) | `SL-ABSENT-WALL` | `OB-ALIGN` | `packet.owner.1 ∉ packet.terminal.val ∧ HasQuittingPureTimeObserverAbsentForcedOwnerDispatch (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1 (quittingStoppingLawSelfOrientedCarrierQuitTime packet) packet.terminal (quittingStoppingLawSelfOrientedMassLower packet)` | [`QuittingCounterexampleStoppingLawFrontier.threeWayLocalization`](../UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/ThreeWayLocalization.lean) |
| 4 | [#6](https://github.com/elazarg/UniformEquilibrium/issues/6) | `SL-NEG-TARGET` | `OB-ALIGN` | `packet.owner.1 ∈ packet.terminal.val ∧ reward packet.terminal packet.owner.1 < 0 ∧ HasQuittingPureTimeNegativeTargetAtomicDispatch (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1 packet.sourceQuitTime packet.terminal (quittingStoppingLawSelfOrientedMassLower packet)` | [`QuittingCounterexampleStoppingLawFrontier.threeWayLocalization`](../UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/ThreeWayLocalization.lean) |
| 5 | [#7](https://github.com/elazarg/UniformEquilibrium/issues/7) | `SL-POS-TARGET` | `OB-RETURN` | `packet.owner.1 ∈ packet.terminal.val ∧ 0 < reward packet.terminal packet.owner.1 ∧ HasQuittingPureTimePositiveTargetReachedRowLocalization frontier (quittingStoppingLawSelfOrientedBaseProfile packet) packet.owner.1 packet.targetQuitTime packet.terminal (quittingStoppingLawSelfOrientedMassLower packet)` | [`QuittingCounterexampleStoppingLawFrontier.threeWayLocalization`](../UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/ThreeWayLocalization.lean) |

The manuscript numbering has five fixed slots. Alternative 1 ([issue #3](https://github.com/elazarg/UniformEquilibrium/issues/3)) is eliminated by `ELIMINATE-PRESCRIBED-BY-SELF-ORIENTED-PURE-TIME`; Alternative 3 ([issue #5](https://github.com/elazarg/UniformEquilibrium/issues/5)) is eliminated by `ELIMINATE-SINGLETON-BY-SIGNED-ACTUAL-ROW`.

<!-- END GENERATED OPEN LEAVES -->

The obstruction classes have the following durable readings:

- `OB-ALIGN`: a counterfactual payoff or debt atom is not yet a source-matched
  strategic gain;
- `OB-RETURN`: a charged tail or retained law is not yet transported through an
  exact cap/state return.

A change to these leaves belongs first in `QuittingProofFrontier.json`. The
generated table above must not be hand-edited.

## Serious routes that remain available

- **Positive construction:** produce one of the inputs accepted by an
  integrated compiler, or add a new compiler whose output reaches terminal
  approximate Nash existence.
- **Source-matched transport:** carry a local or endpoint gain back to a legal
  reached history while preserving the player, state, payoff, and error budget.
- **Global barrier:** find a forward-invariant coupled semantic barrier with a
  positive debt floor, then consume it through the terminal-gap theorem.
- **Vanishing discount:** decode analytic Bellman data into a strategically
  credible target and executable continuation architecture.
- **Bounded architectures:** verify or synthesize fixed controller classes,
  without inferring completeness for unrestricted behavior.

The current bounded reverse-search questions are indexed in
[`../Reverse/Tasks/README.md`](../Reverse/Tasks/README.md).

## Decisive fences

Any current argument must respect these distinctions:

- quitting games do not settle general finite stochastic games positively;
- a verifier for supplied data is not a producer for arbitrary games;
- an integrated theorem may still be conditional;
- a compact coefficient projection need not be a closed space of realized
  strategic blocks;
- positive debt along one explicit chain is not positivity of the optimized
  minimum;
- terminal, limiting-average, discounted, and uniform finite-horizon notions
  require named bridges; and
- experiments and Research modules are evidence until promoted and consumed.

## What counts as resolution

**Positive quitting resolution:** an unconditional theorem producing terminal
approximate Nash profiles at every positive error for every finite quitting
game, followed by the integrated terminal-to-uniform consumer.

**Negative quitting resolution:** one explicit finite reward table and one
fixed positive gap, with a theorem that every behavioral profile admits a
unilateral terminal gain at least that gap, followed by the integrated
nonexistence transfer.

**Meaningful intermediate resolution:** eliminate or consume a live formal
leaf, produce a substantial new unconditional class, prove a sharp
nonclosedness or no-go theorem that changes the required state, or connect a
producer to a semantic consumer with an actual-data
adapter.

## Where new ideas live

The extracted repository intentionally has no `ideas/` directory. The project
workflow is:

- unresolved derivations and exploratory proof strategies: GitHub Discussion;
- bounded mathematical or engineering obligations: GitHub Issue; and
- checked integration: Pull Request.

Exact reproducible computations remain in `Experiments/`, compileable but
unsettled Lean remains in `Research/`, and reverse proof-search packets remain
in `Reverse/`. See [`PIPELINE.md`](PIPELINE.md) for the promotion contract.
