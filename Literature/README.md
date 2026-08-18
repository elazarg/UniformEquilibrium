# Literature

The citation-of-record in
[`docs/references/00_BIBLIOGRAPHY.md`](../docs/references/00_BIBLIOGRAPHY.md)
determines the catalog. Every work there has one Lean module under
`Literature/Papers/` and one `Literature.PaperRecord` in the aggregate catalog.
This makes bibliographic coverage exhaustive and mechanically checked.

Catalog coverage is not claim coverage. A `catalogued` paper can have no audited
source claims. Claim-level work records an exact source locator, a concise
summary, and one of these correspondence states:

- `sourceOnly`: the source claim is recorded but has no Lean statement;
- `openInLean`: a named Lean proposition states the claim without proving it;
- `provedInLean`: a named Lean theorem checks the stated correspondence;
- `refutedInLean`: a named Lean theorem checks its negation or obstruction; or
- `outOfScope`: the claim is deliberately outside this formalization.

Implementation priority follows the mathematical program: finite quitting-game
and uniform-equilibrium claims come first, followed by general stochastic-game
uniform-equilibrium results. Automata, partial-observation, computability, and
finite-memory claims remain catalogued unless their semantics or theorems are
needed by that line of work.

These states form a lifecycle, not interchangeable labels. `sourceOnly` means
that the source claim has been recorded but no Lean statement has been made;
`openInLean` names the proposition while leaving it unproved; and
`provedInLean` or `refutedInLean` require both the named statement and a named
checked theorem. In particular, `refutedInLean` is the explicit audit result
for a wrong source claim: its theorem proves the negation or a precise
obstruction, rather than merely asserting that the source calculation looks
wrong. `outOfScope` records a deliberate boundary and does not refute the
source.

An open claim is represented by a `def` returning `Prop`, and a narrow
`Research.Literature` module must consume that exact proposition while proof
work is active. Reusable definitions and lemmas belong in `MathUE/` or
`UniformEquilibrium/`; definitions meaningful only for one source claim may
remain in its paper module. Once the claim is settled, its final proof is
moved to the durable owner or written in the paper module, the paper module
adds the exact restatement or negation theorem, and the Research proof module
is deleted. A final `provedInLean` or `refutedInLean` record never points into
Research or Experiments. String metadata never substitutes for a Lean
proposition or proof.

Paper modules may depend on `UniformEquilibrium`; integrated modules never
depend on `Literature`. The final Literature lane also never imports
`Research` or `Experiments`. A narrow `Research.Literature` module may import
an individual `Literature.Papers.*` module when it proves the exact open claim
recorded there; it may not import the aggregate catalog, and unrelated
Research modules may not import Literature.

Paper modules own their source-inspection and claim-audit metadata. Run
`python scripts/generate_literature.py` after changing the bibliography; it
creates missing paper templates without overwriting audits and regenerates the
aggregate catalog. `python scripts/check_literature.py` checks catalog
completeness, generated freshness, the no-PDF policy, and that every
declaration name referenced by a non-source claim status exists in the local
Lean tree. It also checks that every open proposition has an active
`Research.Literature` consumer and that final proofs do not point into
Research or Experiments. The declaration check is intentionally only a name
check; Lean checks proposition and proof meaning.
`python scripts/check_import_graph.py` checks the lane boundaries, including
the narrow Research/Literature escape hatch.

Source PDFs are working research material and live outside the tracked
tree, under `ephemeral/`. The repository stores citations, public locators,
source-page or theorem locators, and Lean correspondence; it does not
redistribute PDFs and no tracked path houses them.
