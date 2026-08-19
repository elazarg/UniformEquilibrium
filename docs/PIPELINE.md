# UniformEquilibrium project pipeline

This document defines the current workflow for mathematical research,
formalization, experiments, and repository integration. It is a process
contract, not a progress log. Headline declarations are generated in
[`STATUS.md`](STATUS.md), current mathematical synthesis belongs in
[`FRONTIER.md`](FRONTIER.md), and exact theorem truth belongs to the integrated
Lean tree.

## Work lanes

- **Integrated:** checked definitions, theorems, and adapters accepted into the
  main research line. This lane is not a compatibility API.
- **Literature:** one plain Lean file per paper, with the paper's own
  statements and citation; unproved claims are left as `sorry`.
- **Research:** compileable Lean that is useful but not yet part of the
  integrated architecture.
- **Experiments:** reproducible searches for counterexamples, boundaries, and
  exact finite evidence.
- **Reverse:** backward searches from verified consumers, following the
  semantic fences and task-packet protocol in the reverse-compilation notes.

The lanes may share mathematics, but evidence does not become a theorem by
proximity. Integrated Lean remains the trusted boundary.

Literature has a strict final boundary: it does not import Research or
Experiments, nothing imports Literature, and it is not a `lean_lib` — no
build target compiles it. A paper's file states its definitions and theorems
in the paper's own order and terms; an unproved theorem ends in `sorry`,
which is the open-claim marker, a proof is the settled record, and a proof
of the negation is the refutation. There is no separate status metadata.

Only papers with complete Lean coverage live directly under `Literature/`;
every other paper lives under `Literature/future/` and is not built. A paper
graduates by finishing its statements, not by proving them.

A paper's file may import production modules to state or discharge a claim.
Reusable mathematics is developed in `MathUE` or `UniformEquilibrium`; a
source-specific definition stays with the paper. When a proof closes, the
reusable proof is promoted to its durable home or written directly in the
paper file, replacing the `sorry`.

`Theorems/` is not a work lane. It is a capped reader-facing index of selected
integrated results believed to have interest beyond the conjecture program;
their canonical statements and proofs remain in `MathUE/` or
`UniformEquilibrium/`.

## Promotion rules

Use the smallest durable record that fits the result:

- a checked integration improvement goes directly to a PR;
- a bounded engineering or proof obligation becomes an issue and then a PR;
- an unresolved derivation or interpretation belongs in a Discussion;
- a reproducible search result gets an experiment record;
- a paper statement and its correspondence get a Literature file;
- compileable but architecturally unsettled Lean stays in Research.

Classify by durable output rather than implementation language or origin. A
reusable Lean theorem, checker, or interface whose meaning survives replacing
an experimental instance stays in Research until integration. A producer,
configuration, concrete input or output, generated payload, report, or
integrity record tied to a bounded run or instance belongs in Experiments.
Experiments may import Research; Research may not import Experiments. A
kernel-checked experimental instance remains bounded checked evidence rather
than an integrated or general theorem.

An experiment record includes its tracked source, exact reproduction command,
assumptions, limitations, and compact evidence. A concrete payload without a
recoverable producer includes an explicit provenance-loss record and a
deterministic integrity checker. Caches, logs, screenshots, raw runs, and other
untracked generated output are not durable records.

GitHub owns the lifecycle of exploratory claims:

```text
Discussion: unresolved derivation, interpretation, or competing approaches
      |
      v
Issue: bounded statement, owner-independent acceptance criterion, and consumer
      |
      v
Pull request: checked implementation, exact scope, and reported validation
```

A Discussion may remain open indefinitely without becoming project truth. Move
it to an Issue only when the obligation can be stated precisely enough that a
future contributor can tell whether it is complete. A PR should link the Issue
or Discussion that supplied its mathematical provenance; the repository file
should carry the durable theorem/interface, not a copy of the conversation.

Reverse-search task packets are the versioned exception: they pin exact open
obligations and acceptance commands needed for reproducible backward search.
They may link to a Discussion or Issue, but are not substitutes for either
GitHub state or current theorem status.

Every promoted theorem must have a precise statement, no `sorry` or explicit
`axiom`, and a use in the research line or a clear reason to integrate it. A
conjecture can be a definition until proved; an unproved theorem declaration
is not a placeholder.

## Pull requests and checks

PRs are the unit of Lean integration. A PR should identify its lane, affected
semantic boundary, source or literature reference, mathematical role, any
closing theorem or adapter, and acceptance command.

Every PR, main-branch push, and manual CI run performs the documentation gate,
trust-scanner regression tests, the exhaustive lexical trust scan, and a full
`lake build`. The build treats project warnings as errors and includes the
generated `AxiomAudit` target, which imports every project-owned Lean module and
checks every project-owned declaration transitively. A changed-file build is
useful for local iteration but is not the CI trust boundary.

Search scripts may use numerical solvers, randomized exploration, or external
tools. Their outputs are evidence until a small, deterministic checker or a
kernel-checked theorem consumes them. Prompts, rankings, and orchestration
traces are never proof objects.

## Documentation ownership

Keep living documents timeless and update them when an interface, theorem
boundary, or process rule changes. Publication years and source dates in the
literature are mathematical provenance.

Research residuals import their maintained owners instead of copying long
proof bodies. `python scripts/check_proof_duplicates.py` enforces exact
cross-lane copies above its documented threshold; semantic duplication still
requires review because the checker intentionally does not attempt theorem
equivalence.

Volatile documentation has structured ownership:

| Change | Owning source |
| --- | --- |
| Headline theorem or open proposition | `ProjectStatus.json`; regenerate `STATUS.md` and the README block |
| Quitting proof-search leaf or transition | `QuittingProofFrontier.json`; regenerate the frontier leaf table |
| Compiler/producer interface | `TOOLKIT.md` and its route record |
| Current mathematical dependency boundary | `FRONTIER.md` |
| Research method | `PROGRAM.md` or `methods/` |
| Promotion and validation workflow | `PIPELINE.md` |
| External theorem or citation confidence | `references/` |
| Extraction, old path, or migration provenance | `TRANSITION.md` |

Do not copy headline status into agent policy or free-standing essays. Run
`python scripts/generate_docs.py` after changing a structured source and
`python scripts/check_docs.py` before hand-off.

Project-owned Markdown filenames use `UPPER_SNAKE_CASE.md`. This includes
`README.md`, `AGENTS.md`, `CLAUDE.md`, and `CONTRIBUTING.md`; there are no naming
exceptions. Stable identifiers remain prefixes, for example
`Q194_SEMIALGEBRAIC_BARRIER_COMPLETENESS.md`.

The project uses Issues for technical debt and bounded high-level work,
Discussions for derivations and exploratory proof strategies, and PRs for
checked additions. The Wiki is optional explanatory output; versioned
documentation remains authoritative.
