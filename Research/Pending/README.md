# Pending implementation

This directory preserves the unfinished implementation
at a paused checkpoint. It is not part of the compiled Lean module inventory.

`MANIFEST.json` records the checked baseline, portable application plans, source
hashes, and the distinction between active changes and supporting records.
`Sources/` contains proposed new owners as `.lean.draft` files. `Changes/`
contains the original edits, including changes to existing owners: keeping these
edits avoids copying their already checked proofs into Research. `Records/`
contains the frozen handoffs, scope checks, axiom harnesses, and static reviews.
Harnesses also end in `.lean.draft` and have not been run unless their record
explicitly says otherwise. Old build-session references describe the original
inspection, not a current check of these drafts.

All artifact paths in the current manifest are repository-relative. Original
temporary paths in frozen records are provenance only; `legacy_paths` maps them
to their tracked replacements. No file in `/tmp/` is required to resume.

Run `python scripts/check_research_pending.py` after cloning to verify integrity.
Use the manifest's plans and their dependency records to select the next unit.
Do not apply every stored patch: some records retain superseded, optional, or
already applied changes for interpreting a review. Shared umbrella edits were
prepared independently and must be reconciled, not applied blindly in sequence.

Before treating a unit as proved, complete any unfinished review, resolve its
imports to canonical owners, compile it with the project's silent check policy,
and check its actual consumers and axioms. New project modules must obey the
usual inventory and promotion checks. Unchecked Literature edits remain source
audit work; they are not additional proved paper results.

The mathematical queue and its reviewed source packets are tracked under
`math/`. The lowercase reading library is transferred separately. Overleaf is
an independent repository and may be checked out anywhere; no relative path to
this checkout is required or recorded here.
