# Contributing

## Set up and validate

From a fresh checkout:

```sh
git submodule update --init --recursive
lake build
python scripts/generate_axiom_audit.py --check
python scripts/check_import_graph.py
python scripts/check_proof_duplicates.py
python scripts/check_trust.py
python scripts/check_docs.py
```

Do not run `lake update` during ordinary setup. It is reserved for intentional
dependency or manifest changes.

While iterating on Lean, use the narrowest relevant file or module check. A
toolchain, Lake configuration, dependency pin, umbrella, or repository-
structure change requires a full build. Always report exactly which checks
completed. The trust scan and duplicate-body ratchet are static checks and do
not substitute for compilation or proof review.

## Code placement

Keep integrated Lean narrowly imported and keep coherent results reachable
through the `UniformEquilibrium` umbrella for whole-project checks. The
umbrella is not a downstream compatibility API. `MathUE` may depend on Mathlib
and GameTheory's generic `Math` library, but not on game-semantic
`GameTheory.*` modules.

Every project-owned Lean file must compile without warnings, `set_option`,
`sorry`, `admit`, explicit axioms, `native_decide`, `implemented_by`, unsafe
declarations, or partial definitions. Global linter weakening is forbidden.
State an open claim as a `def` returning `Prop`; add a theorem only when its
proof is available. Keep non-import Lean code within 100 characters per line.

`AxiomAudit.lean` is generated from the complete project module inventory and
is a default Lake target. It imports every project-owned Lean module and rejects
every transitive axiom except `propext`, `Quot.sound`, and `Classical.choice`.
Run `python scripts/generate_axiom_audit.py` after adding, moving, or removing a
Lean module. Do not edit the generated file directly.

Use the repository lanes according to the maturity of the result:

- paper coverage belongs in `Literature`;
- compileable but unsettled Lean belongs in `Research`;
- counterexample searches belong in `Experiments`;
- backward proof search belongs in `Reverse`;
- accepted definitions and proofs belong in `UniformEquilibrium` or `MathUE`.

`Theorems/` is a capped catalog, not an ownership lane. Keep at most ten
feature modules there; a broad feature may point readers to related results
without repeating them all. Repeat each lead statement in a short
reader-facing theorem whose proof delegates to the canonical declaration, and
treat novelty or usefulness corrections as ordinary maintenance.

## From idea to integration

The repository intentionally has no `ideas/` directory. Use the workflow in
[`docs/PIPELINE.md`](docs/PIPELINE.md):

- unresolved mathematics or competing interpretations go to a GitHub
  Discussion;
- a bounded obligation with an acceptance criterion becomes an Issue; and
- checked integration is submitted as a Pull Request linked to its provenance.

Experiments retain commands and compact evidence. Research modules may compile
without being integrated. Neither becomes theorem truth until a checked
declaration and any required adapter/consumer are promoted.

## Documentation

Project-owned Markdown filenames use `UPPER_SNAKE_CASE.md`, without exceptions.
`AGENTS.md` is canonical and `CLAUDE.md` is generated from it.

Update only the owning source:

| Change | Update |
| --- | --- |
| Headline declaration | `docs/ProjectStatus.json`, then generate docs |
| Quitting proof-search leaf | `docs/QuittingProofFrontier.json`, then generate docs |
| Compiler or producer interface | `docs/TOOLKIT.md` and its route record |
| Mathematical boundary | `docs/FRONTIER.md` |
| Process or promotion rule | `docs/PIPELINE.md` |
| External citation | `docs/references/` |
| Extraction or old-path provenance | `TRANSITION.md` |

Run:

```sh
python scripts/generate_docs.py
python scripts/check_docs.py
```

Living documentation describes the current mathematics and workflow. Put
repository-transition chronology, old paths, and superseded implementation
approaches only in `TRANSITION.md`. Literature and source-history audits remain
within their explicitly scoped reference or audit records. Every Markdown file
directly under `docs/` is living documentation and must remain free of dated
repository snapshots, raw commit locators, and changelog sections.
