# Literature

One plain Lean file per paper: a header docstring giving the citation and
public locator, then the paper's own definitions and theorem statements in
the paper's order and terms. An unproved live claim normally ends in `sorry`;
there is no separate status metadata, since the file itself is the audit. A
`sorry` marks an open claim, a proof marks a settled one, and a proof of the
negation marks a refutation. When the exact claim has instead been formally
reduced to a named open problem, the paper-order proposition may remain a
`def` followed by the checked reduction rather than an unjustified theorem
assertion. Likewise, a superseded historical-version claim may remain a named
proposition when a checked version map identifies the weaker corrected current
theorem.

`Literature/` (flat, directly under this directory) holds only papers whose
Lean file is complete: every definition and theorem statement from the paper
is present. `Literature/future/` holds every paper not yet at that bar; a
file there may be a stub or partial. Both areas compile through the default
`Literature` library and its exhaustive `Literature.lean` umbrella. A paper
graduates to `Literature/` by finishing its statements, not by proving them —
`sorry` is permitted in both places.

Nothing outside Literature imports the lane, and the lane never imports
`Research` or `Experiments`. The library keeps warnings as errors and disables
only Lean's dedicated `warn.sorry` diagnostic for intentional open claims. No
paper under `Literature/` enters the compiled axiom audit, so successful
compilation checks syntax, elaboration, and proved terms without certifying
`sorry`-backed claims.

The no-PDF policy: a paper file carries its citation and public locator; no
PDF enters the repository.
