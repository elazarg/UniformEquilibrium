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
producer, obstruction class, the evidence attached to transitions, and the
evidence seals carried by each. This is a proof-search decomposition inside the
formalized regime, not an exhaustive classification of every equilibrium
profile.

Leaves and transitions are grouped by the cover clause they bear on. The four
clauses are those of the necessary-condition manuscript — (A) periodic block
profiles with fixed hazards, (B) solo tails with exact one-shot roots, (C)
trigger repairs, and (D) player count — and two further groups collect the
results that close a parameterized family of tables and the results about one
named table. A seventh group collects restrictions derived inside the regime
itself, which belong to none of the profile classes. The group definitions are
in the ledger; a transition may bear on more than one.

Seals are recorded per entry in the `M`/`L`/`A`/`C` language of
[`STATUS.md`](STATUS.md) and are independent: `A` and `C` are never inferred
from `L`. An entry marked as unchecked carries no seal at all.

<!-- BEGIN GENERATED OPEN LEAVES -->
This table is generated from [`QuittingProofFrontier.json`](QuittingProofFrontier.json).

| Manuscript alternative | GitHub issue | Leaf | Cover clause | Obstruction | Seals | Representative | Source producer |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 5 | [#40](https://github.com/elazarg/UniformEquilibrium/issues/40) | `IMMEDIATE-SINGLETON-PREEMPTION-CYCLE` | `REGIME-LOCALIZATION`, `COVER-D` | `OB-COLLISION` | `M`, `L` | `Nonempty (QuittingImmediateSingletonCollision reward regime.terminalGap) ∧ Nonempty (QuittingSoloPreemptionCycle reward regime.terminalGap)` | [`QuittingCounterexampleRegime.immediateSingletonCollision_and_soloPreemptionCycle`](../UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/PreemptionCycle.lean) |

The manuscript numbering has five fixed slots. Alternative 1 ([issue #3](https://github.com/elazarg/UniformEquilibrium/issues/3)) is eliminated by `ELIMINATE-PRESCRIBED-AND-NEGATIVE-BY-BOUNDED-SELF-RESET`; Alternative 2 ([issue #4](https://github.com/elazarg/UniformEquilibrium/issues/4)) is eliminated by `ELIMINATE-ABSENT-BY-IMMEDIATE-SINGLETON-COLLISION`; Alternative 3 ([issue #5](https://github.com/elazarg/UniformEquilibrium/issues/5)) is eliminated by `ELIMINATE-SINGLETON-BY-SIGNED-ACTUAL-ROW`; Alternative 4 ([issue #6](https://github.com/elazarg/UniformEquilibrium/issues/6)) is eliminated by `ELIMINATE-PRESCRIBED-AND-NEGATIVE-BY-BOUNDED-SELF-RESET`.

<!-- END GENERATED OPEN LEAVES -->

The obstruction classes have the following durable readings:

- `OB-COLLISION`: the canonical singleton row gives a distinct player a
  source-matched legal collision gain equal to positive semantic debt. The
  remaining task is to consume this geometry using the full counterexample
  regime or characterize a genuine counterexample realizing it.

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
