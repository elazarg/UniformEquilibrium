# Formalization coverage

Current internal headline declarations are generated in
[`../STATUS.md`](../STATUS.md). Reader-facing reusable theorem families are
indexed in [`../../Theorems/README.md`](../../Theorems/README.md), and exact
truth remains the Lean declaration under its imports.

Paper-by-paper Lean correspondence belongs in
[`../../Literature/`](../../Literature/). Each root paper file is its own
coverage inventory: an exact statement with a proof is settled, while an exact
statement ending in `sorry` is visibly open. Incomplete papers stay under
`Literature/future/`.

The former source-repository formalization ledger mixed current internal status,
commit chronology, literature mappings, and a survey of other proof assistants.
It is preserved for provenance in
[`../audits/FORMALIZATION_STATUS_LEGACY.md`](../audits/FORMALIZATION_STATUS_LEGACY.md)
and is not maintained as current status.

New literature formalization coverage should be written in the corresponding
plain paper file with exact source locators and declaration names, rather than
added to a free-form global ledger.
