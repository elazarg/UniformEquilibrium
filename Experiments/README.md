# Experiments

This directory contains reproducible searches and instance-specific evidence:
producers, configurations, concrete inputs and outputs, compact generated
payloads, reports, and integrity records. It has no archive, cache, raw-run, or
unreviewed generated bulk content. Reusable Lean declarations and checkers
belong in Research or an integrated lane.

An experiment result records its tracked executable source, exact reproduction
command, assumptions, limitations, and compact evidence. A checked-in payload
whose generator is unavailable instead has a deterministic integrity checker;
its provenance belongs in `TRANSITION.md`. Experiments may import Research;
Research must not import this directory.

- `Base/` is the registered standard-library suite. Run it with
  `python Experiments/Base/run_all.py`.
- `certsearch/` contains certificate-guided exact searches; run its gate with
  `python Experiments/certsearch/validate.py`.
- `counterexample_pairwise_consistency/` contains the pair/triple consistency
  campaign.
- `counterexample_search/` contains the focused falsifier programs.
- `fin4_exact_search/` contains the self-contained exact, resumable
  per-accuracy Fin4 lower-certificate/profile search, flat certificate checker,
  deterministic remote work regions, and batch runner; validate it with
  `python3 Experiments/fin4_exact_search/validate.py` and launch it with
  `python3 Experiments/fin4_exact_search/run.py`.
- `joint_reset_law/` contains an exact-rational regression of the integrated
  joint-reset semiconjugacy.
- `Probes/` contains standalone bounded probes that are not in the Base suite.
- `quitting_repair_cegis/` is the exact-rational repair-search package; its
  tests run with `python -m pytest Experiments/quitting_repair_cegis/tests`.
- `singleton_collision_candidate_search/` searches four-player tables passing
  the formalized counterexample necessary conditions against a bounded
  architecture attack battery, seeded at the Solan-Vieille boundary table; run
  with `python3 Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py`.

Reports retain their commands, assumptions, and exact evidence. The directory
layout above is the current execution layout.
