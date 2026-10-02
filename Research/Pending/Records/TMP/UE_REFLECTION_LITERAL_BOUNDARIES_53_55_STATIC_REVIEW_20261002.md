Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Literal reflection boundaries 53–55: independent static review

Verdict: PASS. The three frozen fixtures match their stated source boundaries without favorable witness inputs or narrowed completion/root quantifiers. This is static-only: no Lean/Lake, compiler, axiom execution, Git, shared edit, build, worktree, cache, or child agent was used. These are next-wave drafts, not part of the currently checking wave or a whole-packet integration seal.

## Frozen inputs

All five files under `/tmp/ue-reflection-literal-boundaries-VxBUGT` were read completely. Initial and final SHA256 checks agree, and the three patch hashes match the parent:

- `53_CONSTANT_SIGNED_NORMAL_TABLE.patch`: `4717204fab5cc4ba22b25a2dcef663beb43cc3870aefc29c451444053a0829c5`.
- `54_POSITIVE_CHARGE_RESCALE.patch`: `91957f4ec748bc92b0719fa25f312e01b03729bf71da29f132f9ad7138d3c6ef`.
- `55_PAIRED_BOUNDED_COMPLETION_FULL_ROOT_EXCLUSION.patch`: `640ecc91da66d4f55ebfa5f28ffd10aa6978177e0432c8855721470953815766`.
- `HANDOFF.md`: `5973367a012dec552719f7e474badc7361caff877dfe71f8a6b386e88108629e`.
- `AXIOM_HARNESS.lean`: `9750fda4929310769e2b93ba96c0278cfeb6fe108b2d0f57e0054676b3f6d0a3`.

Source: `math/exports/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md`, SHA256 `a28b23b400cfef2fce48d0dfd33027b344e00d45a015de549c328dce4f397e69`. The complete source was read in this review sequence; its exact boundary and scope sections were reread here. Units 53, 54, 55 respectively implement boundary tests 4, 6, 5, in conjunction with their existing owners.

## 53: actual constant signed table

New owner: `UniformEquilibrium/Quitting/Examples/ConstantSignedNormalTable.lean`, namespace `GameTheory.ConstantSignedNormalTable`.

`reward` assigns the literal vector (1, −1, 0, 0) to every nonempty coalition, not just to singletons. `singleton_vector`, `rewards_bounded`, and `positive_and_negative_singletons` expose the precise table and its unit bound. No coordinate is restricted by an externally supplied payoff field.

`quit_value_eq` proves the actual independent-product immediate-Quit expectation equals the corresponding target coordinate. It uses supported PMF actions to establish that the owner actually quits and the coalition is nonempty; it does not equate reward values on unsupported empty-coalition actions.

`punishment_eq` concerns the canonical infimum over full behavioral opponent plans of the supremum over full behavioral replies. Its upper leg internally chooses a distinct player, whose singleton pure row forces a nonempty coalition whether or not the owner quits. Both pure-row rewards equal the target, including its negative coordinate. Its lower leg reuses `quittingPunishmentValue_eq_stationaryPunishmentValue`: every stationary cap is at least its immediate-Quit branch, already identified with the target. No attained minimizer, best reply, selected favorable opponent, or stationary restriction on the definition of punishment is assumed.

`punishment_vector` and `singleton_vector` therefore give μ = s = (1, −1, 0, 0). `all_normal` proves the actual all-player normality predicate. The positive singleton at coordinate zero coexists with the negative singleton at coordinate one. `allNever_payoff_zero` retains the zero Never convention, and `positive_scaling_preserves_negative_singleton` covers every strictly positive real scale. Thus normality plus a positive singleton does not supply nonnegative singleton signs, and common positive scaling cannot repair this fixture's negative sign. No UE/no-UE claim for the table is made.

## 54: zero drift and every positive coefficient

New owner: `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialChargeScale.lean`.

`IsQuittingFullExactRootPotentialWithCharge` differs from the existing full-root predicate only by the scalar multiplying the actual absorption charge. It preserves every boxed annotation, every exact independent root against that annotation, and the same exact successor. There is no selected-root branch, punishment floor, realizability requirement, approximate-root substitute, or changed target.

`constant_isQuittingFullExactRootPotentialWithCharge_zero` works for every constant, reward table and box bound without continuity, singleton signs, or cardinality assumptions. This concerns a zero drift coefficient, not an assertion that every exact edge has zero absorption.

`isQuittingFullExactRootPotentialWithCharge_iff_div` is an exact equivalence for every coefficient κ > 0 and arbitrary function P, using the literal function P/κ on the same relation. Division by a positive coefficient preserves the inequality direction and converts κA/κ to A. It adds no differentiability, boundedness of P, selected minimum, or upper bound on κ. It makes no claim at κ = 0 or κ < 0.

The three exclusion corollaries reuse the canonical unit-charge results. Coordinate affinity, continuity and the stated differentiability are preserved under division. Quadratic evaluation is identified with evaluation of κ⁻¹ times the same actual MvPolynomial, and `totalDegree_smul_le` preserves canceled total degree. The multi-affine corollary uses the existing actual evaluation/coordinate-affinity bridge and has no total-degree cap. Arbitrary higher square-free interactions remain covered.

The quadratic corollary uses the existing quadratic owner's `Nonempty` player assumption; the coordinate-affine and multi-affine corollaries retain `Nontrivial`. This is faithful reuse of the current stronger quadratic owner, not a newly derived cardinality extension. None claims the empty-player exclusion. The source's zero-absorption identity is already supplied by canonical all-Continue mass/successor owners and is not re-proved here. This scaling is unrelated to transporting certificate polynomials between different boxes or games.

## 55: every bounded completion, identical paired polynomial

New owner: `UniformEquilibrium/Quitting/Examples/PairedFacePotentialBoundedCompletion.lean`.

`pairedFacePotential_boundedCompletion_face_drift` assumes only that the actual singleton columns equal the printed quarter-shifted matrix. For every owner in Fin4 and every point with all coordinates at least one quarter and that owner's coordinate equal to one quarter, it identifies the actual direction `point − quittingSoloReward reward owner` with the printed direction and applies `translated_face_drift_ge_one`. Thus all four actual face inequalities concern the same `translatedPotential`. No upper cap, reward bound on nonsingletons, or caller-supplied derivative/face certificate is needed for this face statement.

`pairedFacePotential_boundedCompletion_not_fullRoot` quantifies over every real reward table satisfying those singleton equalities and the unit bound. No values of nonsingleton rewards are otherwise constrained. It derives own singleton nonnegativity from the zero diagonal of the literal matrix, then applies the canonical coordinate-affine full-root exclusion using the same fixture's proved coordinate affinity and smoothness. Therefore the identical polynomial fails the full relation for every such bounded completion despite satisfying the four nonnegative face inequalities.

The singleton equalities and table bounds are exactly the advertised completion class, not favorable potential/root/minimizer inputs. No particular completion is selected or required by the universal implication. The patch does not expose a separate existence-of-completion constructor, which is not needed for its requested every-completion theorem. Prior unit 46 already verifies the printed singleton columns are unit bounded.

The literal potential remains Q(v − s), with Q's coefficients −4, 64, 16 and s = (1/4, 1/4, 1/4, 1/4). Unit 46 owns the actual derivatives and all four literal face identities; unit 52 owns the canonical coordinate Hessian joins, coordinate affinity, and an internally produced non-top global minimizing vertex. Unit 55 delegates rather than replacing those with a supplied matrix or arbitrary violating point. No claim is made that any completion is a game counterexample, has no UE, or has a standard-Q property.

## Dependency snapshots and canonical reuse

Frozen earlier dependencies used for the unapplied fixture chain:

- 45, `/tmp/ue-potential-fixtures-xygynp/45_RATIONAL_POLYNOMIAL_COORDINATE_DERIVATIVES.patch`: `05851dcb10bf33ac7466c67fd793dee590674ae627c1c25e1ed28ec3b7ba6e49`.
- 46, `/tmp/ue-potential-fixtures-xygynp/46_PAIRED_FACE_POLYNOMIAL_HESSIAN_FIXTURE.patch`: `e6280f4f42d8fe4e0fa84a69f1080d2f40c7fd225818efafee4580e3d1d2d171`.
- 51, `/tmp/ue-paired-fixture-joins-WMWV4A/51_CANONICAL_COORDINATE_HESSIAN_ENTRIES.patch`: `9ad3d3bb7de80b833af58a75e9129efc83c271c52ceb2b26e67d7ba126fa2820`.
- 52, `/tmp/ue-paired-fixture-joins-WMWV4A/52_PAIRED_CANONICAL_SPECTRUM_AND_MINIMIZING_VERTEX.patch`: `e66135a0c4714ca9ed680f2c6a169291c52bac097ece6189eb8177b041445fc1`.

Current canonical owner hashes:

- `UniformEquilibrium/Quitting/Stationary/MinMax.lean`: `92b3ccc349f07b3a9d118d9289892982cc0e6f71c6d6ea7e398562488c2be9e3`.
- `UniformEquilibrium/Quitting/Punishment/ContinueFloor.lean`: `3a71bf78efc3a53b9e3b47aa2782414c95cacc4666cf1b817ac80d3bef6be66d`.
- `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`: `f118906c54594dfa9ab72904bfff073b85884c8daf76fc90bba64275ca3bacc6`.
- `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialQuadraticExclusion.lean`: `91a177d317c897b26f91df0b8a5cdfd7fe24e9f71db30e7d7d38f805d7894621`.
- `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMultiAffineExclusion.lean`: `8e291161ced7e4486bbf2b4ed5dc479e52b568f81fd773a781d3a486d40551ff`.

Exact relevant declarations/imports were inspected. Searches found no existing literal fixture or coefficient adapter being duplicated. The new proofs reuse punishment equality, pure-row caps, actual supported-product expectations, the original full-root predicate, scalar polynomial degree bounds, and the previously reviewed literal derivative/Hessian fixture chain. All three new modules are correctly game-semantic; no game imports are introduced into MathUE.

## Coverage and validation boundary

These units close the named literal normality/sign, positive-versus-zero drift, and every-bounded-completion joins at the static declaration level. They do not newly prove other source claims about collision corrections, reflection arithmetic, Hessian spectra, minimizing vertices, rational approximate rejection/enumeration, or decision normalization; those remain owned by their separate units. In particular no finite runtime/denominator bound, fixed directional lower bound independent of the potential, all-polynomial exclusion, or solution of the quitting conjecture follows.

Root must apply these only in the intended next wave with their dependencies, add production umbrella imports, regenerate the axiom audit, compile the named modules, execute the representative harness or equivalent transitive audit, and run applicable trust/import/documentation/full-gate checks. Mathematical source alignment and actual-adapter bodies pass this review; L/C and whole-packet completion are not asserted. Unicode notation follows the math-unicode skill solely for readable terminal reporting.
