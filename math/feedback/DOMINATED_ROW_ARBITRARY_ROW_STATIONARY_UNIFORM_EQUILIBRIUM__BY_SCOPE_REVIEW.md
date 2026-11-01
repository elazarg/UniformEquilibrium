# Coverage review: dominated row and arbitrary row

Reviewed candidate: `math/exports/DOMINATED_ROW_ARBITRARY_ROW_STATIONARY_UNIFORM_EQUILIBRIUM.md`, SHA256
`f72f6182367c715845eff7ed630cffedc6abcde5ebbee9cc15cf9317d9c45a6e`.
This is a coverage review, not a fresh independent theorem review: I contributed
scope arguments and the analytic strip. The exact producer and geometric checks are contained in the frozen packet.
Supplementary raw-selector calculations, including all repeated-pair role
assignments, are reproduced by
`python math/experiments/CODEX_COORDINATOR__ARBITRARY_ROW_SCOPE_CHECK.py`.
The final theorem/checker reviews are recorded separately.

**Verdict:** the raw producer is a substantive enlargement beyond the named
complete selectors below. The calibration is the entire ray of original tables
`r=1+Z^(8/5,1/2)`, with only `Z_3(0123)=-M`, for every `M>=216`.
This is not an inventory-wide assertion about every export or every local theorem.

## Complete selectors, including all their internal choices

* The conditional-face-range producer fails already in fixed row0: every
  participant reward is at least its own singleton, while a passive singleton
  is smaller by3/5. This excludes every blocker, interval and scale choice.
  Guarded-crossed and one-sided weak-unit guards fail for every ordered pair:
  an outside favorite, an opposite passive pair, or an explicit joining
  comparison gives the wrong sign. Centered stationary boxes, rational face
  boxes and supplied stationary witnesses are certificate consumers, not
  additional raw producers covering the present theorem automatically.
* All14 child-security choices fail by the exact finite duals; the original
  own levels are1, so each child's security floor is at most1. All finite
  invariant-cone pair choices fail, including arbitrary generators, matchings
  and positive recipient scales. The separate asymmetric pair branch and
  inverse-corner schedule fail their raw guards as well. The scope calculation
  also excludes the positive-real triple-mode, marked-orientation, positive
  product-cover-cone, product-low and weighted-leaver selectors.
* `CONTACT_PRESERVING_COALITION_BONUS_UNIFORM_EQUILIBRIUM.md` produces either a
  proper stationary profile with two hazards at least1/2, or its pure-pair
  fallback. Section6.1 excludes the former; every pure pair has an outsider
  joining gain1. Thus every bonus pair, slope, tie choice and base decomposition
  is excluded.
* `WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md` has `c<=1` and
  `t0<=1/(2 rho_+)`, hence every output hazard is at most1/2. Section6.3 excludes
  every such output, for every finite-atlas choice and every positive recipient
  rescaling. This argument replaces the insufficient normalization-dependent
  magnitude estimate; no magnitude-based all-scale claim is retained.
* `THREE_WEAK_QUITTER_COALITION_BONUS_UNIFORM_EQUILIBRIUM.md` and
  `THREE_OWNER_JOINT_POSITIVE_PASSIVE_TRIPLE_UNIFORM_EQUILIBRIUM.md` produce
  exactly three positive proper hazards. Section6.2 excludes every support,
  parameter and recipient scaling in those constructions.

## Non-Q and degree exits

The convention is recipient rows, quitter columns, with standard residual
`b+Gamma z`. At the calibration,
`det Gamma=351951137/500000000>0` and the minimum entry of its inverse is
`2186650/351951137>0`. Consequently Gamma is R0 by
`isR0Matrix_of_strictlyPositiveInverse` in
`MathUE/LinearProgramming/PositiveInverseR0.lean`, has degree+1 by
`r0Degree_eq_sign_det_of_nonnegative_inverse` in `NonnegativeInverseDegree.lean`,
and is standard Q by `isStandardQ_of_r0Degree_ne_zero` in `R0Degree.lean`.
Neither the non-Q nor non-unit-degree exit covers this calibration. Strict
positivity supplies R0 here; a merely nonnegative inverse would not by itself
supply that separate hypothesis.

## Additional literal periodic families

The following comparisons include positive recipient rescaling and relabeling.
Native signs, numbers of positive singleton entries in a row, and within-row
ratios are invariant under those operations.

1. Every proper participant coordinate in the calibration is nonnegative and
   every participant pair coordinate is positive. This contradicts a negative
   proper participant requirement or a nonpositive pair cap in the inspected
   families `ALL_NONNEGATIVE_PAIR_PREMIUMS`, `NO_CHILD_PREMIUM_FAMILY`,
   `SCALAR_SINGULAR_CIRCUIT`, `MONOTONE_PASSIVE_CAP_CHAMBER`,
   `UNORDERED_ROTATING_MIXED_PAIRS`, `PASSIVE_BOUND_TRIPLE_SELECTION`,
   `EXACT_OPPOSED_PAIR_PATH`, `UNBOUNDED_PAIR_PREMIUMS`, `CROSSED_MATCHING`,
   `FOUR_JOINT_PHASE_RECTANGLE`, and the explicit `TEN_PHASE_MIDDLE_REWARD_CUBE`.
   These names abbreviate the corresponding `_UNIFORM_EQUILIBRIUM.md` files.
2. Every singleton row in the calibration has exactly one positive off-diagonal
   entry. At least one row has two in the inspected raw templates
   `THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM`, `UNEQUAL_PREMIUM_CONTRACTION`,
   `NINE_INDEPENDENT_CORE_PREMIUMS`, `UNORDERED_NINE_CORE_PREMIUMS`,
   `TWO_CONTRACTING_BLOCKS` (including its signed chamber), and
   `LARGER_EIGENVALUE_SIGNED_FOUR_CYCLE_UNIFORM_PAYOFF.md`.
   `GLOBAL_ASYMMETRIC_PAIR_PHASE_UNIFORM_EQUILIBRIUM.md` instead requires equal
   crossing singleton losses within every row; the calibration has unequal
   losses in every row. Its explicit small reward cube also retains negative
   native participant coordinates.
3. In `COMPLETE_COMPLEX_SPECTRUM_RAY_UNIFORM_EQUILIBRIUM.md` and
   `COMPLEX_SPECTRUM_PERIODIC_UNIFORM_EQUILIBRIUM.md`, matching the unique positive
   favorite entries101/100 forces every recipient scale to1. Their literal
   tables always have a negative singleton magnitude9/250. The calibration's
   negative magnitudes are `{3/5,9/1000,27/20,1/25,36/25,3/50,7/1000,9/20}`,
   none equal to9/250. Thus no literal point of either family matches.
   `JORDAN_RESET_UNBOUNDED_PERIOD_UNIFORM_EQUILIBRIUM.md` has crossing ratios
   `J/(-Gamma)=1`, whereas the calibration's are9 or1/9. The literal
   `WEAK_CROSSING_UNBOUNDED_PERIOD_UNIFORM_EQUILIBRIUM.md` and
   `THIRTY_THREE_PHASE_RAW_REWARD_UNIFORM_EQUILIBRIUM.md` have unequal favorite
   `J/Gamma` ratios; all four calibration ratios equal1/101.
4. `REPEATED_PAIR_RAW_REWARD_UNIFORM_EQUILIBRIUM.md` has a broader fixed-tube
   algebraic criterion, not just its literal slab. I checked all eight role
   assignments compatible with favorite matching. Three fail M0; two fail a
   required positive passive corner; three fail the G2 boundary signs already
   on the first tube cell. The latter exact margins are respectively greater
   than1/10 at an upper boundary, less than-4/5 at a lower boundary, and greater
   than1/10 at an upper boundary. Positive row scalings cancel the compression
   ratios and active responses and preserve every tested sign. Thus the whole
   stated fixed-tube criterion, not merely its center/slab, is excluded.
   The retained supplementary audit reproduces all eight exclusions.

**Limitations:** literal-family separation does not establish separation from
unspecified maximal neighborhoods of earlier local existence theorems, including
the complete ray's existential raw tube. I do not claim that all existing
periodic architectures are impossible, that no sure stationary equilibrium
exists, or that every one of the export inventory's entries was independently
excluded. These limitations do not affect the new raw stationary producer.
