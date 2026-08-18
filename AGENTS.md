# UniformEquilibrium agent context

## Project

UniformEquilibrium is a Lean research project for solving, refuting, or sharply
characterizing uniform-equilibrium conjectures for finite stochastic games. It
is optimized for mathematical research, audit, and rapid iteration, not for a
stable downstream API.

`GameTheory/` is the pinned foundational dependency. Project-owned generic
mathematics belongs in `MathUE/`; integrated game-semantic results belong in
`UniformEquilibrium/`.

## Mathematical orientation

A uniform-equilibrium payoff is one fixed payoff target such that, for every
positive accuracy, some behavioral profile delivers that target and caps every
unilateral behavioral deviation over all sufficiently long finite horizons.
The profile may depend on the accuracy; the target may not.

The general finite-stochastic-game proposition and its finite-quitting
specialization are distinct. Finite quitting games—one live state with Boolean
Continue/Quit actions—are the main direct research front, not a known normal
form for arbitrary stochastic games. The general proposition is formalized for
state-independent action sets; padding state-dependent action sets is not
silently semantics-preserving.

Use `docs/SEMANTICS.md` for the stable model and quantifier contract. Current
headline declaration status is generated in `docs/STATUS.md`, and the current
mathematical dependency boundary is synthesized in `docs/FRONTIER.md`. Inspect
the exact declaration and imports before describing a result as proved in Lean.

## Sources of truth and navigation

Use these sources for different questions:

- exact theorem truth: the Lean declaration under its stated imports;
- generated headline declaration index: `docs/STATUS.md`;
- stable semantic contract: `docs/SEMANTICS.md`;
- current mathematical synthesis: `docs/FRONTIER.md`;
- available integrated interfaces and nonclaims: `docs/TOOLKIT.md`;
- stable research and formalization method: `docs/PROGRAM.md`;
- workflow and promotion rules: `docs/PIPELINE.md`; and
- extraction and repository-transition provenance: `TRANSITION.md` only.

Frontier claims use four independent evidence seals: `M` for rigorous
mathematics, `L` for a checked Lean declaration, `A` for an adapter from actual
source data, and `C` for a checked downstream consumer. Do not infer `A` or `C`
from `L`, or strategy-class coverage from a verifier for supplied data.

## The non-negotiable rule: honesty

Never subvert precise communication of what has and has not been formalized.
Do not turn a definition, conjecture, conditional theorem, experiment, comment,
paper claim, generated computation, or unbuilt file into prose that sounds like
an unconditional checked theorem. Do not hide hypotheses, trust assumptions,
scope restrictions, missing imports, build failures, or the difference between
a local check and a full build.

Precision should read naturally. Prefer ordinary status language:

- **proved in Lean**: a theorem checked by Lean under the stated imports;
- **integrated**: reachable from the appropriate production umbrella;
- **conditional**: checked, but only under hypotheses that remain to be supplied;
- **Research**: compileable Lean outside the integrated production surface;
- **experiment**: reproducible evidence, not a theorem;
- **open proposition**: a stated `Prop`, not a proof; and
- **not checked here**: use when reporting a static audit or targeted check
  without implying a larger build.

Integration records reachability and repository maturity, not unconditionality.
The integrated surface may contain proposition definitions and conditional
theorems as well as unconditional theorems.

These conventions exist to make truthful communication concise, not awkward.
When a more precise description is needed, give it.

## Repository lanes

- `MathUE/`: game-independent mathematics owned by this project.
- `UniformEquilibrium/`: integrated game-semantic development.
- `Theorems/`: reader-facing restatements delegating to original proofs.
- `Literature/`: paper-by-paper Lean audit records and catalog infrastructure;
  inspect its umbrella for actual coverage.
- `Research/`: compileable work not yet integrated.
- `Experiments/`: reproducible systematic searches and generated evidence.
- `Reverse/`: backward proof-search questions and evidence.
- `docs/`: current mathematical interfaces, methodology, and exposition.
- `TRANSITION.md`: the only place for repository-transition history.

Classify Research and Experiments by their durable output, not by implementation
language or provenance. A reusable, human-maintained Lean declaration, checker,
or interface whose meaning survives replacing an experimental instance belongs
in Research until integration. A producer, configuration, concrete input or
output, generated payload, report, or integrity record tied to a bounded run or
instance belongs in Experiments. Thus an experiment may import Research, but
Research must never import Experiments. A kernel-checked experimental instance
is bounded checked evidence, not an integrated or general theorem.

An experiment record is durable only when its tracked source, reproduction
command, assumptions, and limitations are recorded together. A migrated
payload whose producer is unavailable instead needs an explicit provenance-loss
record and a deterministic integrity checker. Caches, logs, screenshots, raw
runs, and untracked generated output are not durable records.

The Lean umbrellas are the authoritative module inventories. READMEs and
manifests explain purpose, policy, and intentional exceptions; they do not
track ordinary file churn.

## Documentation ownership

Keep volatile facts in one structured source:

- headline declarations: `docs/ProjectStatus.json`, which generates the status
  blocks in `README.md` and `docs/STATUS.md`;
- quitting proof-search leaves: `docs/QuittingProofFrontier.json`, which
  generates the live leaf table in `docs/FRONTIER.md`;
- stable semantics: `docs/SEMANTICS.md`;
- compiler and producer interfaces: `docs/TOOLKIT.md` and their route records;
- research method: `docs/PROGRAM.md`;
- GitHub Discussions, Issues, and PR promotion: `docs/PIPELINE.md`; and
- extraction, old paths, and repository-transition history: `TRANSITION.md`.

`AGENTS.md` is the canonical agent policy. `CLAUDE.md` is generated from it;
do not edit the copy independently. Run `python scripts/generate_docs.py`
after changing generated inputs and `python scripts/check_docs.py` before
hand-off.

Project-owned Markdown filenames use `UPPER_SNAKE_CASE.md`, without
exceptions. Stable identifiers remain prefixes, for example
`Q194_SEMIALGEBRAIC_BARRIER_COMPLETENESS.md`.

Cite a Lean result by declaration name and file, never by line number, as in
`exists_cubicAnchor_root_mem_Ioo` (`MathUE/CubicAnchorRoot.lean`). A line
number goes stale as soon as anything is inserted above the declaration, so it
fails for a declaration nobody touched and has to be repinned by hand; the
name is stable and `scripts/check_docs.py` resolves it. That checker rejects a
line-pinned reference in a living document.

## Current conventions

Use narrow imports inside modules and keep coherent work reachable through the
appropriate umbrella. Keep project-specific mathematics in `MathUE`; do not
duplicate GameTheory foundations. `MathUE` may depend on Mathlib and
GameTheory's generic `Math` library, but not on game-semantic `GameTheory.*`
modules.

The project trust policy rejects `sorry`, `admit`, explicit axiom declarations,
`native_decide`, `implemented_by`, unsafe declarations, partial definitions,
and project-owned `set_option` commands. All project libraries compile with
warnings as errors. Global linter weakening is forbidden. State open claims as
proposition definitions until proved.

For a Lean change, use the narrowest relevant checks while iterating:

- `lake env lean path/to/File.lean` checks one source file;
- `lake build Module.Name` checks a named module and its dependency closure;
- `python scripts/check_trust.py` runs the lexical trust scan and does not
  substitute for Lean compilation; it also checks the warning policy and that
  the generated exhaustive axiom audit is current;
- `python scripts/generate_axiom_audit.py` regenerates `AxiomAudit.lean` after
  adding, moving, or removing project-owned Lean modules;
- `python scripts/check_import_graph.py` checks static import reachability for
  the declared Lean umbrellas and reports production-lane boundary violations;
  `python -m unittest scripts/test_check_import_graph.py` runs its regression
  tests;
- `python scripts/check_proof_duplicates.py` rejects long exact Research copies
  of canonical `MathUE` or `UniformEquilibrium` declaration bodies;
- `python scripts/check_derivable_telescope_hypotheses.py --check` rejects
  narrow finite-instance, membership/nonemptiness, and equality/bound
  telescope redundancies; and
- `python scripts/check_docs.py` checks generated status, source references,
  frontier evidence paths, and local documentation links.

`AxiomAudit.lean` is a default Lake target. It imports every project-owned Lean
module, including modules outside the main umbrellas, and audits every
project-owned declaration transitively. Only `propext`, `Quot.sound`, and
`Classical.choice` are permitted axioms.

Run the trust scan whenever Lean changes and regenerate the axiom audit whenever
the module inventory changes. Run a full `lake build` only when the task or risk
warrants it; changes to the toolchain, Lake configuration, dependency pin,
project umbrellas, or repository structure warrant the full build. Report
exactly which checks ran. Do not run `lake update` unless the task actually
requires dependency or manifest work.

Keep non-import Lean code within 100 characters per line.

Lean 4.32.2 is required. Lean 4.32.0 is excluded because of a kernel soundness
bug.

Keep living documentation current and timeless. Put all transition provenance,
keep/drop decisions, old paths, and migration notes only in `TRANSITION.md`.
Do not create commits, remotes, issues, pull requests, or releases unless the
task explicitly asks for them.
