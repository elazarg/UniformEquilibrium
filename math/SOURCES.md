# Mathematical Sources

Conference agents should reach the mathematics through bounded lookup, not by
trying to absorb the whole codebase. This page is a navigation order, not
another theorem-status document.

## Bounded lookup protocol

1. Choose one route or deficit in `docs/FRONTIER.md` or one compiler/producer
   family in `docs/TOOLKIT.md`.
2. Copy the one or two named declarations and source files attached to it.
3. Read those declarations in place. Follow a definition or import only when
   it occurs in the statement or a proof step the question will use.
4. Run a narrow `rg` query for exact declaration names or distinctive terms in
   that subtree. This checks for nearby lemmas and no-go results without
   pretending to audit the repository.
5. Write down the resulting small dependency set in the working note and
   start the mathematics. Return to the source only when a concrete dependency
   arises.

No agent needs a global mental model of the Lean tree. Different agents can
cover different neighborhoods and communicate the exact interfaces they find.

## Minimal quitting-game entry bundle

For a new route, read only the applicable part of this four-file bundle before
following a narrower dependency:

- `quittingUniformEquilibriumPayoffConjecture`
  (`UniformEquilibrium/Quitting/Conjecture/Basic.lean`) states the target and
  its scope;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  is the positive semantic endpoint;
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`) is the
  negative semantic endpoint; and
- `VanishingDebtAtomChronologicalConsumer` and
  `PaidFirstDisagreementAdmissibleReturnConsumer`
  (`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`)
  state the current explicit producer interfaces.

An independent approach may need only the target and one semantic endpoint.
It need not read the current producer machinery at all.

## 1. `UniformEquilibrium/`: the main Lean source

[`../../UniformEquilibrium/`](../../UniformEquilibrium/) contains the actual
game-semantic development. After selecting a declaration through the bounded
protocol, inspect its exact imports and hypotheses in the source file.
Potentially relevant regions include:

- [`Conjecture/`](../../UniformEquilibrium/Conjecture/) for the general
  proposition and its relation to the quitting specialization;
- [`Quitting/`](../../UniformEquilibrium/Quitting/) for the model-specific
  constructions, semantic endpoints, paths, cycles, debts, punishments, and
  known classifications;
- [`Diagnostics/Quitting/`](../../UniformEquilibrium/Diagnostics/Quitting/) for
  exact obstructions, boundary examples, and current producer interfaces;
- [`ProofView/`](../../UniformEquilibrium/ProofView/) for the semantic objects
  and bridges used by the project; and
- [`Certificates/`](../../UniformEquilibrium/Certificates/) for reusable
  sufficient architectures and their explicit hypotheses.

Also inspect [`../../MathUE/`](../../MathUE/) when the argument uses
game-independent probability, topology, optimization, transport, or finite
mathematics. Do not rebuild a theorem already present under a different local
name.

For every result cited in a conference note, record the declaration name and
file, not a line number. Distinguish an unconditional theorem from a conditional
consumer, a proposition definition, and a checked interface whose producer is
still open.

## 2. `Literature/`: papers represented in Lean

Tracked [`../../Literature/`](../../Literature/) is the preferred bridge from
papers to exact formal statements. Each paper has one Lean file in the paper's
own terms. Read [`../../Literature/README.md`](../../Literature/README.md)
before relying on the lane:

- files directly under `Literature/` have complete statement coverage;
- files under [`future/`](../../Literature/future/) may be partial or stubs;
- an unproved paper claim is intentionally marked by `sorry`;
- the lane is not a `lean_lib`, is not built, and is imported nowhere; and
- a faithful statement is evidence about what a paper says, not a project
  theorem.

Search this lane before attributing a new theorem, invoking a named result, or
asserting that an existing paper method covers the project's behavioral and
uniform-horizon semantics. A conference note should state the exact paper
theorem or section and then spell out the adapter still needed.

## 3. lowercase `literature/`: local reading material

Gitignored [`../../literature/`](../../literature/) contains local PDFs,
archives, transcriptions, and reading notes. It is useful evidence and may be
cleaned up, but it is not versioned theorem truth. Never cite a derived note
when the original paper is available, and never infer correctness from the
presence of a file.

Keep this local library flat so both Codex and Claude can discover material
with one filename scan. Use descriptive uppercase names with a common paper
prefix:

```text
AUTHOR_YEAR__PAPER.pdf
AUTHOR_YEAR__SOURCE_ARCHIVE.zip
AUTHOR_YEAR__TRANSCRIPTION.tex
AUTHOR_YEAR__CLEANED_TEXT.md
AUTHOR_YEAR__PROOF_MAP.md
AUTHOR_YEAR__INTUITION.md
AUTHOR_YEAR__LEAN_CORRESPONDENCE.md
```

For example, the contents now nested under `Simon2007/` can become files such
as `SIMON_2007__PAPER.pdf`, `SIMON_2007__PROOF_MAP.md`, and
`SIMON_2007__LEAN_CORRESPONDENCE.md` directly under lowercase `literature/`.
Use a more specific title fragment when an author has several papers in one
year.

Cleanup is conservative:

1. inventory files and identify their paper before renaming;
2. flatten by moving, not copying, so duplicates are not created;
3. preserve PDFs, archives, raw text, and transcriptions byte-for-byte;
4. normalize project-owned Markdown filenames to uppercase snake case;
5. update lowercase `literature/README.md` to describe what is actually
   present; and
6. do not promote a conclusion from this local library directly into
   `exports/`—first state and review the mathematics in a conference note.

Unidentified bundles stay clearly prefixed `INCOMING__` until inspected.
Destructive deduplication is unnecessary; record suspected duplicates and let
a human decide.

## 4. Documentation as map

After inspecting the Lean and paper sources, use `docs/SEMANTICS.md`,
`docs/STATUS.md`, `docs/FRONTIER.md`, and `docs/TOOLKIT.md` to orient the claim
within the current program. Those documents prevent common scope errors, but
they do not replace the declaration, proof, or original paper.

The desired research path is:

```text
Lean and paper sources
        -> self-contained conference question
        -> independent argument and source audit
        -> adversarial feedback
        -> tightly gated export
        -> external Lean formalization
```
