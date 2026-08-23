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

The full-core deadlock completion family has a sharper integrated carrier
constraint.
[`IsFullCoreDeadlockCompletion.globalDebtFloor_le_sharperBound`](../UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockSharperBound.lean)
constructs an actual carrier point of total semantic debt exactly
`1227/96755` and therefore bounds every global debt floor by that value. The
The terminal exploitability witness consumer
[`HasTerminalExploitabilityGap.fullCoreDeadlock_le_sharperBound`](../UniformEquilibrium/Diagnostics/Quitting/FullCoreDeadlockDebtBound.lean)
then bounds every terminal exploitability gap on this family by `1227/96755`,
with the stored gap of a terminal exploitability witness as a direct corollary. Neither
the minimum debt nor the gap is proved to vanish, and no uniform-equilibrium
payoff is produced.

The flat stopping-law charged-circulation branch now has a frozen actual-source
reset-cube adapter.  Integer rounding gives a balanced finite packet with
`O(1/N)` prefix control (`exists_frozenBalancedResetPacket` in
`UniformEquilibrium/Diagnostics/Quitting/Frozen/BalancedResetPacket.lean`).  Radial scaling absorbs
real circulation coefficients into legal stopping-law weights; the six frozen
modules under `Diagnostics/Quitting/Frozen/` place these resets in one literal
cube, expose the joint and deleted-player clocks, and retain the exact
`O(lambda²)` face remainder.  The strongest static dispatch is
`exists_fixed_frozenRadialStrategicLabel_of_scaleNormalizedLiminfLower` in
`UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialCurvatureStrategicDispatch.lean`, which returns the oriented
strategic square alternative.  These are frozen-source certificates: they do
not provide a chronological carrier path or a renewal return.

Terminal differences between two pure-time witnesses also have an exact
reached-history decoder.
[`quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul`](../UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean)
covers both finite later dates and `Never`, so the source-to-reached-history
transport itself is no longer a gap. What remains is the game-facing
composition of a localized cap square with the appropriate branch consumer,
and, in the common-passport branch, a chronological carrier-path producer
whose ordered Bellman blocks have vanishing Green ratios and divergent
opponent exposure. The static cube does not supply that chronology.

## Current proved dependency DAG

The maintained ledger is now a dependency DAG, not a history of named search
leaves. It begins at positive minimum terminal semantic debt, records the
exact-diagonal stopping-law extraction and finite support-rank exit, and then
shows both the four tagged exit arms and the checked consumers beyond the
remaining producer gaps.

Finite support-rank termination leaves positive total slope, zero-debt support
entry, flat charged circulation, or an eventually paid first-disagreement row.
These are mathematically distinct tags, not an asserted equivalence. There is
also a stronger branch-independent adapter: every extracted frontier already
has fixed vanishing-debt atom access. In the support-entry arm the actual
zero-debt recipient can be retained as the atom observer.

Two concrete producer arrows remain explicit. Static vanishing-debt atom data
must be serialized into chronological debt-shadowing certificates at every
positive accuracy, or an eventually paid row must be re-entered as a positive
exact admissible edge with an exact return. The chronological and
admissible-return consumers themselves are proved in Lean.

Seals use the independent `M`/`L`/`A`/`C` language of
[`STATUS.md`](STATUS.md). An `L` seal on an open producer arrow means its
proposition interface is checked, not that the implication has been proved.

<!-- BEGIN GENERATED OPEN LEAVES -->
This dependency table is generated from [`QuittingProofFrontier.json`](QuittingProofFrontier.json).

| From | Status | To | Seals | Checked declaration or open interface |
| --- | --- | --- | --- | --- |
| `POSITIVE-MINIMUM-DEBT` | `proved` | `EXACT-DIAGONAL-FRONTIER` | `M`, `L`, `A` | [`GameTheory.finiteSupportRankAlternative_of_hasPositiveMinimumTerminalSemanticDebt`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `EXACT-DIAGONAL-FRONTIER` | `proved` | `FINITE-SUPPORT-RANK-EXIT` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.finiteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `POSITIVE-TOTAL-SLOPE` | `M`, `L` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawFiniteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `ZERO-DEBT-SUPPORT-ENTRY` | `M`, `L` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawFiniteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `FLAT-CHARGED-CIRCULATION` | `M`, `L` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawFiniteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `FINITE-SUPPORT-RANK-EXIT` | `proved-branch` | `PAID-FIRST-DISAGREEMENT-ROW` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.HasQuittingStoppingLawFiniteSupportRankAlternative`](../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean) |
| `EXACT-DIAGONAL-FRONTIER` | `proved` | `VANISHING-DEBT-ATOM-ACCESS` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.nonempty_vanishingDebtAtomAccess`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `ZERO-DEBT-SUPPORT-ENTRY` | `proved` | `VANISHING-DEBT-ATOM-ACCESS` | `M`, `L`, `A` | [`GameTheory.QuittingPositiveMinimumDebtTangentFamily.exists_vanishingDebtAtomAccess_of_supportEntry`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `VANISHING-DEBT-ATOM-ACCESS` | `open-producer` | `CHRONOLOGICAL-DEBT-SHADOWING` | `L` | [`GameTheory.VanishingDebtAtomChronologicalConsumer`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `PAID-FIRST-DISAGREEMENT-ROW` | `open-producer` | `POSITIVE-ADMISSIBLE-RETURN` | `L` | [`GameTheory.PaidFirstDisagreementAdmissibleReturnConsumer`](../UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean) |
| `CHRONOLOGICAL-DEBT-SHADOWING` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`](../UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean) |
| `POSITIVE-ADMISSIBLE-RETURN` | `proved-consumer` | `UNIFORM-EQUILIBRIUM-PAYOFF` | `M`, `L`, `C` | [`GameTheory.quittingGame_exists_uniformPayoff_of_positive_admissible_return`](../UniformEquilibrium/Quitting/Bellman/Finite/PositiveAdmissibleCycle.lean) |

The open producer arrows are:

- `VANISHING-DEBT-ATOM-ACCESS` to `CHRONOLOGICAL-DEBT-SHADOWING`: Missing: serialize the static whole-law atom alternatives into executable tails with bounded forcing, vanishing survival, and small initial debt at every accuracy.
- `PAID-FIRST-DISAGREEMENT-ROW` to `POSITIVE-ADMISSIBLE-RETURN`: Missing: re-enter the paid strategic row as a positive exact floor-admissible edge and construct an exact return to its tail state.

The DAG nodes have these mathematical meanings:

- `POSITIVE-MINIMUM-DEBT`: The attainable terminal semantic carrier has strictly positive minimum total debt; for a nonempty finite player type this is equivalent to nonexistence of a uniform-equilibrium payoff.
- `EXACT-DIAGONAL-FRONTIER`: A positive minimum supplies one positive-minimum tangent family whose active mover diagonal is exactly minus base debt and whose full-replacement mover debt tends to zero.
- `FINITE-SUPPORT-RANK-EXIT`: Repeated minimum-fiber re-extraction terminates because positive-debt support cardinality strictly decreases, or an explicit finite-support-rank alternative is reached.
- `POSITIVE-TOTAL-SLOPE`: One active mover has strictly positive total tangent slope.
- `ZERO-DEBT-SUPPORT-ENTRY`: A flat active tangent column has a positive coordinate at an actual zero-debt recipient.
- `FLAT-CHARGED-CIRCULATION`: The flat tangent columns admit normalized positive charged balance.
- `PAID-FIRST-DISAGREEMENT-ROW`: An off-minimum full-replacement cluster carries a fixed-gain exact paid first-disagreement row eventually along one retained subsequence.
- `VANISHING-DEBT-ATOM-ACCESS`: Every extracted positive-minimum tangent family has a fixed positive off-diagonal observer and an eventually available atom alternative whose endpoint observer debt tends to zero. In the support-entry branch the actual zero-debt recipient can be retained.
- `CHRONOLOGICAL-DEBT-SHADOWING`: Certificates at every positive accuracy compile to terminal approximate Nash profiles and one uniform-equilibrium payoff.
- `POSITIVE-ADMISSIBLE-RETURN`: One positive exact punishment-floor admissible edge followed by an exact return path compiles to a uniform-equilibrium payoff.
- `UNIFORM-EQUILIBRIUM-PAYOFF`: Existence of one fixed payoff target satisfying the uniform finite-horizon equilibrium contract.

<!-- END GENERATED OPEN LEAVES -->

A change to this DAG belongs first in `QuittingProofFrontier.json`. The
generated block above must not be hand-edited. Earlier named-leaf censuses,
issue mappings, strengthening chronology, and keep/drop records are
repository-transition provenance and belong only in `TRANSITION.md`, not in
the live mathematical ledger.

## Serious routes that remain available

- **Positive construction:** produce one of the inputs accepted by an
  integrated compiler, or add a new compiler whose output reaches terminal
  approximate Nash existence.
- **Chronological atom production:** serialize the fixed vanishing-debt atom
  access into executable reached tails satisfying the checked shadowing
  certificate at every positive accuracy.
- **Exact return production:** re-enter a paid first-disagreement row as a
  positive punishment-floor admissible edge and construct an exact return.
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

**Meaningful intermediate resolution:** prove or consume one of the open DAG
arrows, produce a substantial new unconditional class, prove a sharp
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
