# certsearch

## K11 checked-in evidence integrity

`block_pair/k11_generated_data_manifest.json` records the exact K11 dyadic
box, preconditioner, Jacobian-cache, and row-zero-cache payloads checked in
under `block_pair/K11/`. The local Lean umbrella
`Experiments.certsearch.block_pair.K11` assembles those four payload modules
into the parameterized Research checker interface.
Run
`python scripts/check_k11_generated_data.py` from the repository root to check
their full-file and formatting-independent logical hashes, 31-by-31 shapes,
and basic payload invariants. This is an integrity check for checked-in Lean
evidence, not a producer: the original numerical generator is unavailable.
The exact provenance loss and its limitations are recorded in
[`block_pair/K11/MANIFEST.md`](block_pair/K11/MANIFEST.md).

P13 ("certificate-guided weight search", `Experiments/PROPOSALS.md`), slice
one: the exact filter layer and its validation suite. Plain Python 3, stdlib
+ `fractions` only -- no `numpy`, no `sympy`. Exact rational arithmetic
throughout; every filter decision is a `Fraction` computation, never a float
comparison.

## What exists (slice one)

- **`weights.py`** -- the `Weight` representation
  (`dict[frozenset[int], tuple[Fraction, ...]]`), the affine gauge
  (`gauge_normalize`: per-coordinate positive scaling pinning every solo
  value into `{-1, 0, +1}`; see the module docstring for the exact map and
  why translation is unused), the invariant matrix (`invariant_matrix`,
  `B_ij = r_i({j}) - r_i({i})`), and five named reference weights embedded in
  the tracked data. The `ideas/` and `questions/` entries below are provenance
  locators in the predecessor source at revision
  `171e014480bfd59f09403abc68af45b7f2c44fb5`, not live target paths:

  | Name | Source |
  |---|---|
  | `G_EPS` (`eps=1/10`) | source locator `ideas/AbsorbingCycleCarrier/APublishedWeightSitsInTheCycleExistenceHole.md` |
  | `Q154_WEIGHT` | source locator `questions/Question154-DoRelaxedCyclesDivergeWithoutAnExactOne.md`, section 2, equation (9) |
  | `TWO_PLAYER_COUNTEREXAMPLE` | `UniformEquilibrium/Quitting/Boundary/Repair/DisjunctionCounterexample.lean` |
  | `FTV_WEIGHT` | `UniformEquilibrium/Quitting/Examples/Cyclic/ThreePlayer/AdmissibleCycle.lean` |
  | `HOSTILE_WEIGHT` | `UniformEquilibrium/Quitting/Punishment/IsolatedPunishmentCeiling.lean` |

- **`filters.py`** -- four exact deciders, each returning a `Certificate`
  (`ok: bool`, `detail: dict`) rather than a bare boolean, so every
  refutation carries its own trace:

  1. `is_zero_solo(w)` -- `IsQuittingZeroSolo`: every solo value `<= 0`.
  2. `solo_quitter_lp(w, i)` -- `QuittingSoloQuitterCriterion`: the
     period-one no-join affine feasibility test, solved by exact half-line
     intersection over the rate `p`.
  3. `singleton_lcp_feasible(B)` -- Question 154 eq. (5)'s normalized
     singleton LCP, by support-pattern enumeration: exact Gauss-Jordan
     elimination per support, remaining degrees of freedom resolved by
     vertex enumeration (every nonempty bounded polyhedron has a vertex
     where `dim`-many facets are tight).
  4. `stationary_row_search(w, denom_bound)` -- brute-force small-
     denominator rational stationary rows, decided by the exact `Sigma_i`,
     `Gamma_i`, `V` formulas of Question 154 section 1 eqs. (3)-(4)
     specialized to a constant row, checked against both clauses of exact
     complementarity.

- **`validate.py`** -- the gate (see below). Run:

  ```
  python Experiments/certsearch/validate.py
  ```

## What slice two adds

- **`admissibility.py`** -- filter (2b): after `solo_quitter_lp` finds a
  feasible period-one row `p * e_i`, decides ADMISSIBILITY of the cycle it
  generates (`IsQuittingCycleAdmissible`,
  `UniformEquilibrium/Quitting/Cycles/AdmissibleCycleTerminalEquilibrium.lean`).
  `cycle_admissible` is written for an arbitrary constant row, not just solo
  ones, and is reused that way by `sweep.py`. The two-player counterexample
  is reproduced as LP-feasible-but-inadmissible (its defining property);
  FTV comes back "not applicable" at every owner, since `solo_quitter_lp`
  already fails there at every coordinate (its real admissible cycle is
  period-three, never tested by this period-one filter).
- **`certifier_bridge.py`** -- filter (4): wraps
  `Experiments/certsearch/krawczyk_cycle_certifier.py` UNMODIFIED, generalizing
  its `certificate_B`/`certificate_C`/`certificate_A` to an arbitrary
  `weights.Weight` instead of the two hardcoded tables the certifier's own
  `main()` exercises. Period 1 is exhaustive (26 patterns); period 2 is the
  certifier's own limited "one active coordinate per phase" family; period 3
  existence is decided only for weights recognized as a positive uniform
  rescale of `FTV_WEIGHT` (the certifier's only known root), via affine
  invariance.
- **`backward_distance.py`** -- the E64 own-set-shift upper bound
  (`UniformEquilibrium/Quitting/Root/EndpointBackwardStability.lean`) on the distance to the
  exact-cycle stratum `Sigma_1`, searched exactly (no float pre-filter
  needed at these denominators) over the same small-denominator grid
  `stationary_row_search` uses, reporting `bound = C * defect` with
  `C = 1/min(y_i, 1-y_i)`. The per-`L` table is deliberately the SAME
  number at every `L` (Sigma_1 subseteq Sigma_L for every L): a genuinely
  period-`L`-specific search is not attempted.
- **`sweep.py`** -- the first random sweep over gauge-normalized rational
  three-player weights (diagonal in `{-1,0,1}`, off-diagonal entries at
  small denominators) through the full escalation 1 -> 2/2b -> 4 (periods
  1-3) -> backward distance, refusing to run unless `validate.py` passes
  fresh. Found and fixed a real gap while developing it: rows with exactly
  one coordinate pinned pure decouple algebraically into independent linear
  equations in the other two coordinates and are invisible to both the
  solo-row LP and the certifier's fully-pinned-corner existence route, but
  are caught by `backward_distance`'s grid search -- `sweep.py` cross-checks
  admissibility on any such zero-defect row before calling a weight a
  survivor.

Still not built (a future slice): the `F_eps`-orbit-variation profiler, the
label-lock-certificate search, and the punishment-floor refutation sweep.
Slice two consumes slice one's filters as a pre-screen; it does not replace
their correctness obligation.

## Certsearch mode: circulation certificates

The singleton-face circulation certificates form a certsearch mode:

- **`circulation.py`** -- the `L = 1` per-support linear check
  (`circulation_L1`) and a small-`L` (`L <= 3`) search over singleton owner
  sequences on a rational `alpha` grid, with a bounded multi-owner fallback
  (`search_circulation`). The floor `r_i = max(d_i, chi_i)` uses the TRUE
  min-max `chi`; since only bounds are computable here, the module derives
  (and documents at length, since the direction is the one place a filter
  like this is likely to be wrong) that only the solo-clipped-ceiling upper
  bound `chi_upper(w, i) = max(0, d_i)` is sound to certify against -- a
  trivial lower bound is informational only, reported as `unsound_only`
  when it (and only it) finds a witness. `certify_circulation` is the
  three-way (`certified` / `unsound_only` / `empty_at_searched_depth`)
  wrapper.
- **`sweep_circulation.py`** -- runs the mode over the five named reference
  weights and the repaired four-player family `F'(x, eps)`
  repaired four-player family on a small rational grid, gated by a fresh
  `validate.py`
  run exactly like `sweep.py`.
- **`validate.py`'s Part 5** -- the positive control (the scaled cyclic
  weight `FTV_WEIGHT / 3` must reproduce
  `UniformEquilibrium/Quitting/Circulation/SingletonFaceCirculation.lean`'s
  own machine-checked `cyclicCirculation` witness, owners `0, 2, 1`, `alpha
  = 1/2`, exactly) and the negative control (the two-player counterexample
  comes back empty at `L = 1` under the sound floor, by a hand-checked
  argument, while the same check under the unsound floor manufactures a
  witness -- demonstrating why only one direction is safe to certify
  against).

## The validation-gate principle

**No sweep output from slice two -- or from any future extension of this
directory -- is evidence of anything until `validate.py` passes.** A filter
that cannot reproduce a *known* answer on a *named* weight is not trustworthy
on an unknown one; P13's own words: "A checker that cannot fire on known
positives is not evidence." Concretely:

- Every fact `validate.py` asserts is drawn from, and cites, a specific
  document or Lean theorem -- never invented, never eyeballed from a float
  computation.
- Every assertion failure prints the full certificate, not a bare
  `AssertionError`: if a filter and a document disagree, you get the exact
  witness or refutation trace needed to find out which one is wrong.
- The `Sigma_i`/`Gamma_i`/`V` formulas behind `stationary_row_search` are
  independently tested against a hand-derived value (Question 154's own K2
  worked example) *before* being trusted on any of the five named weights --
  "derive them from Q154 section 1 and TEST against known values before
  use," per the dispatch. Getting a sign or an index wrong in these formulas
  would silently poison every downstream stationary-row search; the K2 check
  in `validate.py` Part 0 exists specifically to catch that class of bug.

Building this suite surfaced two places where the natural-language
description of "known facts" (written before the filters existed) disagreed
with what the cited primary sources actually say once decided exactly. Both
are recorded prominently in `validate.py`'s comments and end-of-run summary,
each with the correct fact, its citation, and why the filter's answer -- not
the prose description -- is the one to trust:

1. **`HOSTILE_WEIGHT` is zero-solo**, not "not zero-solo." Both of its solo
   values are exactly `0`, and `IsQuittingZeroSolo`
   (`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`) is a nonpositivity condition
   (`r_i({i}) <= 0`), not equality to `0` -- confirmed independently by the
   `Q154_WEIGHT` case in the same suite, whose solo values are `-1/2` (not
   `0`) and which the same document calls zero-solo.
2. **`solo_quitter_lp(TWO_PLAYER_COUNTEREXAMPLE, owner=1)` is feasible**
   (witnessed at `p=1`), not "infeasible." That witness is exactly the Lean
   file's own `witnessBlock` row: "an absorbing complementary cycle *does*
   exist here." What the same file's "Item 3" then shows is that this
   cycle's deleted survival product is `1` while its solo weight is
   negative, so it fails *admissibility* -- a separate, later check, not the
   period-one no-join existence test `solo_quitter_lp` performs. Existence
   of a complementary cycle and admissibility of that cycle are different
   facts.
