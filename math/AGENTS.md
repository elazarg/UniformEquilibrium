# Math Conference Instructions

These instructions apply to every conference participant working below this
directory. The repository's root `AGENTS.md` remains authoritative for project
semantics, honesty, naming, and Lean trust policy.

## Mission

Make rigorous mathematical progress toward deciding the finite-quitting
uniform-equilibrium conjecture while preserving independent thought. Develop
your own line rather than waiting for a coordinator. Read other work to learn,
stress-test it, and offer concrete help, not to force all agents into one proof
language.

Conference research records belong only in `math/`. Agents inspect the Lean
and literature sources elsewhere in the repository before developing a claim.
Lean implementation is deliberately assigned to external formalization agents
after a result passes the export gate. Cleanup of the gitignored lowercase
`literature/` reading library is source stewardship, not mathematical export;
follow the reversible flat convention in [`SOURCES.md`](SOURCES.md).

## Before working

Read [`SOURCES.md`](SOURCES.md), [`GOAL.md`](GOAL.md), and the existing
conference filenames. Do not survey the entire Lean tree. Use `docs/FRONTIER.md`
or `docs/TOOLKIT.md` to choose one route and obtain its named declarations,
then open those source files and follow only the definitions and imports needed
for the question. Exact theorem truth comes from a Lean declaration under its
imports; a paper claim comes from the paper and its faithful transcription;
current frontier claims come from the generated or maintained project
documents, not from a conference note.

Before proposing a new lemma, run a narrow symbol or phrase search in the
chosen subtree for its definitions, nearby declarations, and existing no-go
results. Stop when the dependencies of the concrete question are understood;
global codebase familiarity is not a prerequisite. Record declaration names
and files inspected in your notebook. For a literature-derived claim, record
the paper, theorem or section, and any mismatch between the paper's hypotheses
and the project's semantics.

Choose a stable, distinctive identity. Create or continue one file in
`notes/` whose name begins with that identity. Do not claim exclusive ownership
of a question. Independent duplication is useful evidence when the arguments
are genuinely independent.

## Research standard

Start with a self-contained question. State all finite data, quantifiers,
probability modes, information, agency, and the exact desired conclusion. Keep
these distinctions explicit:

- a proof, a proof draft, an experiment, an analogy, and a conjecture;
- a supplied-object verifier, a producer from arbitrary game data, and a
  strategy-class completeness theorem;
- terminal, finite-horizon, discounted, and uniform-payoff claims;
- bounded controllers and unrestricted behavioral deviations; and
- a Lean-checked theorem and ordinary mathematics not checked in Lean.

Try small positive and negative examples early. When a statement fails, retain
the minimal failed implication and the strongest statement that survives.
Prefer exact calculations to floating-point evidence. Never silently repair a
false claim by changing its quantifiers or probability mode.

Use the project methods in
[`../../docs/methods/MATH_RESEARCH_METHOD.md`](../../docs/methods/MATH_RESEARCH_METHOD.md)
and
[`../../docs/methods/PARALLEL_RESEARCH_METHOD.md`](../../docs/methods/PARALLEL_RESEARCH_METHOD.md)
without copying their process into conference notes.

## Communication protocol

The protocol is files, not meetings:

1. An author owns their notebook and may revise it freely.
2. Everyone else comments in `feedback/<NOTE_STEM>__BY_<IDENTITY>.md`.
3. A review restates the claim being checked and identifies exact valid steps,
   gaps, counterexamples, or repairs. Cite declarations by name and file, never
   by line number.
4. The author incorporates useful feedback and records which objections remain.
5. If discussion branches into new mathematics, the reviewer starts a new
   owned note and cross-links both files.

Avoid editing shared indexes. Before ending a substantive session, leave your
notebook readable: current status near the top, proved and unproved claims
separated, and one concrete next question or requested check.

## Export boundary

Internal notes may preserve anything of mathematical value when its status is
honest. `exports/` is different. It is not a showcase for promising ideas.

Never self-export an unreviewed result. A packet may enter `exports/` only when
it satisfies every criterion in [`exports/README.md`](exports/README.md), has
no unresolved mathematical objection, and records the independent review that
checked it. A result settling the full conjecture or claiming unrestricted
strategy-class coverage needs two independent reviews, including an explicit
attempt to falsify it.

An export carries mathematical evidence only. Do not give it an `L`, `A`, or
`C` seal unless those exact facts are already established by named, checked
Lean declarations in the repository. The external Lean agent may discover a
real mathematical gap; if so, remove the packet from the export queue, retain
it as an internal note, and address the feedback there.

## Editing discipline

Use project-owned uppercase Markdown filenames. Keep mathematical records
inside `math/` and preserve other agents' files. Source-library cleanup under
gitignored lowercase `literature/` must be reversible: normalize names and
flatten files, but do not delete or rewrite source material merely to tidy it.
Do not create commits, issues, PRs, or Lean files as part of conference work.
Prefer a new note or feedback file over a large coordination document.
