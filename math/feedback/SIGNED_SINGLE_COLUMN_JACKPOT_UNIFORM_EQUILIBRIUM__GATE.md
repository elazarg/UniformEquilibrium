# Signed single-column jackpot: export evidence

## Frozen mathematical content

The self-contained packet is
[`SIGNED_SINGLE_COLUMN_JACKPOT_UNIFORM_EQUILIBRIUM.md`](../exports/SIGNED_SINGLE_COLUMN_JACKPOT_UNIFORM_EQUILIBRIUM.md),
SHA256 `05f2e1b41f817f91c3053aab73d5c1e20f00e32bbddb7fc67445a51633f2e894`.
It is ordinary mathematics, not a new Lean declaration.

The reviewed source is
[`CODEX_EMMY_BOX__ONE_POSITIVE_COLUMN_SINGLE_JACKPOT.md`](../notes/CODEX_EMMY_BOX__ONE_POSITIVE_COLUMN_SINGLE_JACKPOT.md),
SHA256 `8d78c71867cc6348f8e4b95abef6602b15bb57ff96f0e33961029305b0a72506`.

## Independent mathematical reviews

- [CODEX_TURING_BOX](CODEX_EMMY_BOX__ONE_POSITIVE_COLUMN_SINGLE_JACKPOT__BY_CODEX_TURING_BOX.md)
  checked the exact polynomial cancellation, signed root, determinant,
  compact-parameter and scale-thick quantifiers, and full behavioral and
  uniform-payoff conclusions. The review explicitly tested the pair case,
  signed residuals, and growing perturbation box. Its final signed assembly
  check covers the frozen source above.
- [CODEX_NASH_BOX](CODEX_EMMY_BOX__ONE_POSITIVE_COLUMN_SINGLE_JACKPOT__BY_CODEX_NASH_BOX.md)
  independently reconstructed the four-player fixture, checked whole source
  selections rather than a chosen witness, and checked the unrestricted
  terminal-to-uniform consumer. Its final assembly check covers the same
  frozen source. Unknown implicit-function radii and universal novelty are
  explicitly excluded from its verdict.

No strategic object remains assumed: stationary hazards, fixed-point value,
and every player-deleted contraction are produced from the finite raw data.
The scope is an explicit reward-table class, not all Fin4 tables or a
strategy-class completeness assertion.

## Faithful handoff and mechanical checks

Turing's bounded handoff check in Section8 of its review covers assembled
bytes with SHA256
`a1767d7626a347a373c888225131ec75de7af27b3d0501baf6ed5afbfc937ff0`.
The frozen export differs only by removal of the duplicate Section5 heading
and an empty final line. The heading correction was explicitly permitted by
that check; the final-line correction satisfies `git diff --check`.
Its mathematical statement and proof are unchanged. Conference dependencies
and review history are absent from the packet.

The coordinator verified that all cited Lean paths are tracked, inspected
the stationary endpoint consumers and the named matrix/source screens,
and ran `python3 scripts/check_docs.py` and `git diff --check` successfully.
No Lean build or axiom-audit claim is made for the new producer.
