# Experiments

This directory contains reproducible searches and instance-specific evidence:
producers, configurations, concrete inputs and outputs, compact generated
payloads, reports, and integrity records. It has no archive, cache, raw-run, or
unreviewed generated bulk content. Reusable Lean declarations and checkers
belong in Research or an integrated lane.

An experiment result records its tracked executable source, exact reproduction
command, assumptions, limitations, and compact evidence. A migrated payload
whose producer is unavailable instead records that provenance loss and has a
deterministic integrity checker. Experiments may import Research; Research must
not import this directory.

- `Base/` is the registered standard-library suite. Run it with
  `python Experiments/Base/run_all.py`.
- `certsearch/` contains certificate-guided exact searches; run its gate with
  `python Experiments/certsearch/validate.py`.
- `counterexample_pairwise_consistency/` contains the pair/triple consistency
  campaign.
- `counterexample_search/` contains the focused falsifier programs.
- `quitting_repair_cegis/` is the exact-rational repair-search package; its
  tests run with `python -m pytest Experiments/quitting_repair_cegis/tests`.

Reports retain their commands, assumptions, and exact evidence. The directory
layout above is the current execution layout.
