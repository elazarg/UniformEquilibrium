# UniformEquilibrium documentation

This directory contains the current mathematical, engineering, and research
documentation for the UniformEquilibrium project. Living documents describe
the present interfaces and rules.

Every Markdown file directly under `docs/` is living documentation and is
checked for snapshot dates, raw commit locators, and changelog-style sections.
Backticked Lean-file references in living documents are repository-root
relative; named line locators are checked against the cited source line.
Ordinary implementation history belongs in Git. Explicitly historical
literature, source-verification, experiment, or audit records may preserve the
evidence they were created to record, but they are never current status
authorities.

## Start here

1. [SEMANTICS.md](SEMANTICS.md) — the stable model, quantifiers, strategy class,
   and payoff-notion contract.
2. [STATUS.md](STATUS.md) — generated headline declarations and their exact
   source modules.
3. [FRONTIER.md](FRONTIER.md) — the current mathematical boundary: established
   results, conditional compilers, open obligations, and decisive falsifiers.
4. [TOOLKIT.md](TOOLKIT.md) — the integrated interfaces and their semantic
   roles.
5. [PROGRAM.md](PROGRAM.md) — the stable research and formalization method.
6. [PIPELINE.md](PIPELINE.md) — how Discussions, Issues, and PRs record and
   promote work.
7. [SOFTWARE_ENGINEERING_REVIEW.md](SOFTWARE_ENGINEERING_REVIEW.md) — the
   current architecture assessment, proof-quality policy, and risk register.
8. [ENGINEERING_ROADMAP.md](ENGINEERING_ROADMAP.md) — current engineering
   priorities, invariants, and acceptance gates.
9. [GAMETHEORY_INTEGRATION.md](GAMETHEORY_INTEGRATION.md) — the dependency,
   semantic-boundary, and ownership contract for GameTheory.
10. [references/README.md](references/README.md) — the external literature of
   record.

Integrated Lean is the source of exact theorem truth. The status page is a
generated declaration index, the frontier is the current mathematical
synthesis, and the pipeline is the current process contract.
Neither a research note nor an experiment result becomes part of either merely
by being linked from this directory.

## Integrated route records

- [ESSENTIAL_APS.md](ESSENTIAL_APS.md)
- [SUPPORT_WITNESS_COMPILER.md](SUPPORT_WITNESS_COMPILER.md)
- [PROJECTIVE_LASSO_PRODUCER.md](PROJECTIVE_LASSO_PRODUCER.md)
- [CIRCULATION_UNIFORM_PAYOFF.md](CIRCULATION_UNIFORM_PAYOFF.md)
- [PAYOFF_PERTURBATION_CLOSURE.md](PAYOFF_PERTURBATION_CLOSURE.md)
- [BOUNDARY_HOLONOMY_TANGENT.md](BOUNDARY_HOLONOMY_TANGENT.md)
- [UNIFORM_CONSEQUENCES.md](UNIFORM_CONSEQUENCES.md)
- [NOTION_LATTICE.md](NOTION_LATTICE.md)
- [LLM_REVERSE_COMPILATION_EXPERIMENT.md](LLM_REVERSE_COMPILATION_EXPERIMENT.md)
- [design/TERMINAL_EXPLOITABILITY_WITNESS.md](design/TERMINAL_EXPLOITABILITY_WITNESS.md)

These files describe current mathematical interfaces and scope boundaries.

## Methods and evidence

- [methods/](methods/) contains the stable methodology.
- [design/](design/) contains current design records and explicitly marked
  historical design studies.
- [case-studies/](case-studies/) contains focused worked analyses and audits.
- [audits/](audits/) preserves explicitly historical mathematical and
  source-verification synthesis that remains useful as evidence but is not
  current authority.
- [references/](references/) records published results, citations, and source
  corrections.
- [manuscript/](manuscript/) contains derivative exposition, including the
  [frontier atlas](manuscript/UniformEquilibriumFrontierManuscript.tex), the
  [semantic frontier guide](manuscript/SemanticFrontierGuide.tex), the
  [semantic-gap note](manuscript/SemanticGapForFiniteQuittingGames.tex), and
  the [four-player calibration](manuscript/FourPlayerPairedSingletonCalibration.tex).

Research notebooks, experiments, reverse-search runs, and literature coverage
belong in their dedicated repository lanes. Promote their conclusions through
the workflow in [PIPELINE.md](PIPELINE.md); do not make a living document into
a hidden archive.
