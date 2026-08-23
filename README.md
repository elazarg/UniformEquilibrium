# UniformEquilibrium

`UniformEquilibrium` is a Lean research project aimed at solving—or, failing
that, sharply characterizing—the uniform-equilibrium conjecture family for
finite stochastic games. It develops formal constructions, obstructions,
examples, and existence results on top of the pinned `GameTheory` submodule.

A uniform-equilibrium payoff is one fixed payoff target such that, for every
positive accuracy, some behavioral profile both approaches that target and
caps every unilateral behavioral deviation over every sufficiently long finite
horizon. The profile may depend on the accuracy; the target may not.

## Status at a glance

<!-- BEGIN GENERATED STATUS -->
This table is generated from [`docs/ProjectStatus.json`](docs/ProjectStatus.json).

| Claim | Status | Exact declaration | Scope |
| --- | --- | --- | --- |
| Finite stochastic games with state-independent action sets | Open proposition | [`uniformDeviationCapConstructorConjecture`](UniformEquilibrium/Conjecture/UniformExistenceConjecture.lean) | General finite stochastic-game existence; padding state-dependent actions is not silently semantics-preserving. |
| All finite quitting games | Open proposition | [`quittingUniformEquilibriumPayoffConjecture`](UniformEquilibrium/Quitting/Conjecture/Basic.lean) | The quitting specialization is distinct from the general conjecture. |
| Two-player finite quitting games | Unconditional theorem | [`quittingGame_exists_uniformEquilibriumPayoff_twoPlayer`](UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean) | All reward tables and all unilateral behavioral deviations. |
| Three-player finite quitting games (`Fin 3`) | Unconditional theorem | [`quittingGame_exists_uniformEquilibriumPayoff_threePlayer`](UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean) | All reward tables on the concrete player type `Fin 3`; reindexing is recorded separately. |
| Terminal approximate Nash existence and uniform-payoff existence | Equivalence theorem | [`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`](UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean) | Finite quitting games; terminal approximate profiles are required at every positive error. |
| Quitting-game nonexistence and a fixed terminal exploitability gap | Equivalence theorem | [`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`](UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean) | A counterexample must quantify over every behavioral profile. |
| Terminal exploitability gaps for four-player full-core deadlock completions | Unconditional family theorem | [`HasTerminalExploitabilityGap.fullCoreDeadlock_le_sharperBound`](UniformEquilibrium/Diagnostics/Quitting/FullCoreDeadlockDebtBound.lean) | For arbitrary nonsingleton coalition rewards, every terminal exploitability gap over a completion of the displayed normalized singleton matrix is at most 1227/96755; this does not prove that the gap vanishes or produce a uniform equilibrium. |
| Exact uniform equilibrium for the literal full-core deadlock completion | Unconditional theorem | [`reward_isUniformEquilibriumPayoff_jointBlock`](UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean) | The named zero-multiquitter completion FullCoreDeadlock.reward has an exact uniform-equilibrium payoff, certified by a three-phase product block with supports {0}, {2}, and {1, 3}; arbitrary full-core completions retain only the separate 1227/96755 bound. |
| Uniform equilibrium on a rational polyhedral full-core deadlock slice | Conditional family theorem | [`isUniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion`](UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockRationalPolyhedralBlock.lean) | For any baseline s, including negative coordinates, a completion satisfying IsDeadlockRationalJointBlockCompletion reward s has target deadlockRationalBlockValue s. The predicate fixes the full-core singleton matrix, requires reward({1,3}) = s, and imposes eight explicit collision-cap inequalities; it describes an unbounded nonlocal polyhedral slice, not all full-core completions. |
| Finite reward-range sufficient condition for stationary quitting equilibria | Conditional theorem | [`exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange`](UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean) | Strict lower and weak upper conditional reward-range comparisons yield a stationary behavioral terminal Nash and a uniform-equilibrium payoff; the hypotheses are a sufficient source-data condition, not a universal classification. |
| Sorin's absorbing-game uniform-payoff segment | Unconditional theorem | [`isUniformEquilibriumPayoff_pair_value`](UniformEquilibrium/Examples/Sorin/UniformPayoffSegment.lean) | Every payoff (a, 2(1-a)) with 1/2 <= a <= 2/3 is realized against all unilateral behavioral deviations; the account strategy may depend on the requested accuracy. |

Declaration kind and umbrella reachability are checked by the documentation gate. Compilation truth still comes from the relevant Lean check or CI run.
<!-- END GENERATED STATUS -->

The table indexes declaration kind and source reachability; it is not a Lean
build report. See [`docs/STATUS.md`](docs/STATUS.md) for that distinction and
[`docs/FRONTIER.md`](docs/FRONTIER.md) for the current dependency boundary and
nonclaims.

## What is worth looking at?

- **Finite stochastic and quitting games:** the integrated development contains
  semantic bridges, exact positive cases, obstruction theorems, and explicit
  fences against false strategy-class completeness claims.
- **Reusable formal mathematics:** [`MathUE/`](MathUE/) contains project-owned
  probability, topology, curve-selection, interval-certification, linear-
  algebra, occupation-flow, and charged-path results independent of the main
  game-semantic layer.
- **Selected theorem statements:** [`Theorems/`](Theorems/) gives short,
  reader-facing restatements of results such as charged-path/potential duality,
  bounded-discrepancy circulation, collision-mass bounds, phase-occupation
  duality, cyclic exposure, and flow holonomy. Canonical proofs remain in their
  original modules.
- **Examples and diagnostic counterexamples:** the integrated tree includes the
  Big Match, Sorin examples, pure-externality cycles, vanishing-discount
  diagnostics, and counterexamples to proposed certificate or continuity
  principles.
- **Computational evidence:** [`Experiments/`](Experiments/) contains
  reproducible exact and numerical searches, including exact-rational CEGIS.
  Its reports are evidence, not proofs.
- **Backward proof search:** [`Reverse/`](Reverse/) works from checked consumers
  toward precise remaining mathematical obligations.
- **Literature coverage:** [`Literature/`](Literature/) provides paper-by-paper
  audit records and catalog infrastructure; its umbrella is the coverage
  inventory.

The repository is organized for mathematical discovery, verification, and
systematic audit, not as a stable downstream library. It makes no compatibility
promise for internal modules.

## Where to start

| Interest | Entry point |
| --- | --- |
| Exact semantic and quantifier contract | [`docs/SEMANTICS.md`](docs/SEMANTICS.md) |
| Headline declaration index | [`docs/STATUS.md`](docs/STATUS.md) |
| Current mathematical boundary | [`docs/FRONTIER.md`](docs/FRONTIER.md) |
| Integrated interfaces and exact nonclaims | [`docs/TOOLKIT.md`](docs/TOOLKIT.md) |
| Reader-facing theorem catalog | [`Theorems/README.md`](Theorems/README.md) and [`Theorems/Catalog.lean`](Theorems/Catalog.lean) |
| Integrated game-semantic areas | [`UniformEquilibrium/README.md`](UniformEquilibrium/README.md) |
| Experiments and their commands | [`Experiments/README.md`](Experiments/README.md) |
| Current reverse-search questions | [`Reverse/Tasks/README.md`](Reverse/Tasks/README.md) |
| Research and formalization method | [`docs/PROGRAM.md`](docs/PROGRAM.md) and [`docs/PIPELINE.md`](docs/PIPELINE.md) |
| Extraction and repository provenance | [`TRANSITION.md`](TRANSITION.md) |

Integrated Lean is the source of exact theorem truth. `STATUS.md` is a generated
declaration index and `FRONTIER.md` is the current mathematical synthesis;
neither substitutes for compilation. Experiments, Research files, comments,
and paper summaries do not become theorems by proximity.

## Repository map

- `UniformEquilibrium/` contains the integrated game-semantic development.
- `MathUE/` contains game-independent mathematics owned by this project.
- `Theorems/` is a correction-friendly showcase delegating to canonical proofs.
- `Literature/` contains paper-audit records and their catalog infrastructure.
- `Research/` contains compileable Lean not yet incorporated into the
  integrated development.
- `Experiments/` contains reproducible counterexample and certificate searches.
- `Reverse/` contains backward proof-search tasks and evidence.
- `docs/` contains the mathematical frontier, methodology, and architecture.
- `GameTheory/` is a pinned git submodule and is not modified here.

The submodule is the dependency boundary. Project-specific generic mathematics
belongs in `MathUE`; the game-semantic layer depends on GameTheory interfaces.
`MathUE` may use Mathlib and GameTheory's generic mathematics, but not
game-semantic `GameTheory.*` modules.

## Lean entry points

The whole integrated development, including `MathUE`, is available through:

```lean
import UniformEquilibrium
```

The game-independent and featured-theorem surfaces can also be loaded directly:

```lean
import MathUE
import Theorems
```

These umbrellas are project-wide build and navigation boundaries, not stable
external APIs. Individual modules use narrow imports to keep focused checks
small.

## Trust and verification

Project Lean sources reject `sorry`, `admit`, explicit axiom declarations,
`native_decide`, `implemented_by`, unsafe declarations, and partial
definitions. They also reject project-owned `set_option` commands and global
linter weakening. Every project library builds with warnings as errors. Open
claims remain definitions of propositions until a kernel-checked proof is
available.

The generated `AxiomAudit.lean` imports every project-owned Lean module and
checks every project-owned declaration transitively. It permits only the
standard `propext`, `Quot.sound`, and `Classical.choice` axioms. As a default
Lake target, it covers orphaned Research and experiment modules as well as the
main umbrellas.

Lean 4.32.2 is the required toolchain. Lean 4.32.0 is excluded because of a
kernel soundness bug.

From a fresh checkout:

```sh
git submodule update --init --recursive
python scripts/generate_axiom_audit.py --check
lake build
python scripts/check_import_graph.py
python scripts/check_proof_duplicates.py
python scripts/check_trust.py
python scripts/check_docs.py
```

`lake build` performs the Lean compilation check. `check_trust.py` is a lexical
escape-hatch scan and is not a substitute for compilation. The static
duplicate check rejects long exact Research copies of maintained MathUE or
UniformEquilibrium declaration bodies; it is a narrow ownership ratchet, not a
semantic proof-equivalence test. Do not run
`lake update` during ordinary setup; it is reserved for intentional dependency
or manifest work.

## Reuse

The project is MIT-licensed; see [`LICENSE`](LICENSE). Definitions, proofs,
mathematics, and tooling may be copied or adapted under that license. Because
the project has no stable API or release surface, citations should identify the
exact declaration or module used, together with the relevant mathematical
source where applicable.
