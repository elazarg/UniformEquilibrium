# Literature

Use one Lean module per paper while that remains readable. Each claimed result
should have a source locator, a normalized statement definition, and a status.
A proved claim gets a small theorem delegating to the integrated declaration.
An open claim remains only a `def` returning `Prop`.

Paper modules may depend on `UniformEquilibrium`; integrated modules never
depend on `Literature`.

Each paper module exports a `Literature.PaperRecord` from
`Literature/Catalog.lean` so
coverage can be enumerated without introducing assumptions or placeholder
proofs.
