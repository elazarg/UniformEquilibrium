# Literature

One plain Lean file per paper: a header docstring giving the citation and
public locator, then the paper's own definitions and theorem statements in
the paper's order and terms. An unproved claim ends in `sorry`; there is no
separate status metadata, since the file itself is the audit — a `sorry`
marks an open claim, a proof marks a settled one, and a proof of the
negation marks a refutation.

`Literature/` (flat, directly under this directory) holds only papers whose
Lean file is complete: every definition and theorem statement from the paper
is present. `Literature/future/` holds every paper not yet at that bar; a
file there may be a stub, partial, or simply not compiling. Nothing in
`future/` is built. A paper graduates to `Literature/` by finishing its
statements, not by proving them — `sorry` is permitted in both places.

Nothing imports the literature lane, and the lane never imports `Research`
or `Experiments`. It is not a `lean_lib`: no build target compiles it, and
no source under `Literature/` enters the compiled axiom audit. Files there
are read, not built.

The no-PDF policy: a paper file carries its citation and public locator; no
PDF enters the repository.
