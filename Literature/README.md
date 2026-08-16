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

An open claim is represented by a `def` returning `Prop`. A proved or refuted
claim is represented by a theorem that delegates to the canonical declaration
in `MathUE/` or `UniformEquilibrium/`. String metadata never substitutes for a
Lean proposition or proof.

Paper modules may depend on `UniformEquilibrium`; integrated modules never
depend on `Literature`.

Paper modules own their source-inspection and claim-audit metadata. Run
`python scripts/generate_literature.py` after changing the bibliography; it
creates missing paper templates without overwriting audits and regenerates the
aggregate catalog. `python scripts/check_literature.py` checks catalog
completeness, generated freshness, and the no-PDF policy.

Source PDFs are local research material. They belong in
`Literature/LocalSources/`, which is ignored by Git. The repository stores
citations, public locators, source-page or theorem locators, and Lean
correspondence; it does not redistribute PDFs.
