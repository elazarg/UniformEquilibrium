# Experiments

This directory contains reproducible executable searches and their compact
evidence. It has no archive, cache, raw-run, or generated bulk content.

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
