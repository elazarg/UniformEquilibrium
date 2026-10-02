Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Reflection exact integral and literal fixtures: independent static audit

## Verdict

Mathematical/source STATIC PASS for 44, 45→45A→46, 47, 51→52→55, and 53, with one definite additional warning-policy repair required in 52: replace `push_neg at hnone` by `push Not at hnone`. A separate immutable one-line overlay is frozen below. This is not a Lean/compiler, executed axiom, integration, consumer, full-build, or whole-packet seal.

Original proof bodies, their handoffs and harnesses were read completely. The full reflection export was read in this continuing review lane, with its integral proof and all six printed boundary tests revisited for this audit. Exact current canonical derivative, Euclidean Hessian, spectral-minimum, coordinate-affine vertex, actual punishment and root-exclusion owners were inspected. No shared source, frozen original, cache, worktree or math note was changed; no Lean/Lake, Git, child agent or mathematical research was used. Unicode-math notation follows the loaded skill.

## Useful-claim correspondence

| Source obligation | Literal declaration and owner |
| --- | --- |
| Proof 4: the two half-integral identities | `Math.midpoint_thirdDerivative_half_integrals`, future `MathUE/Analysis/MidpointThirdDerivativeIntegral.lean` (44) |
| Proof 4: exact midpoint identity and nonnegative kernel of weighted mass 1/6 | `midpoint_thirdDerivative_integral_identity`, `midpointThirdDerivativeKernel_nonneg`, `midpointThirdDerivativeKernel_weighted_mass`, same owner |
| Boundary 2: permitted −3 endpoint, failure of fixed cap, failure of removed sign | `allowed_reflection_endpoint`, `fixed_cap_reflection_outside`, `signed_singleton_reflection_outside`, namespace `Math.ReflectionBoundaryArithmetic`, future `MathUE/Analysis/Examples/ReflectionBoundaryArithmetic.lean` (47) |
| Boundary 3: unsigned θ=2/3 gives partial 2/45>0 | `unsigned_multiaffine_partial_positive`, same owner |
| Boundary 4: literal constant table, singleton/punishment vector, all-player normality, positive and negative singleton, failure of positive scaling to repair sign | `singleton_vector`, `punishment_eq`, `punishment_vector`, `all_normal`, `positive_and_negative_singletons`, `positive_scaling_preserves_negative_singleton`, namespace `GameTheory.ConstantSignedNormalTable`, future `UniformEquilibrium/Quitting/Examples/ConstantSignedNormalTable.lean` (53) |
| Boundary 5: literal Q and P, all four face formulas and bounds, bounded singleton columns | `expression`, `translatedExpression_eval`, `face_drift_eq_formula`, `face_drift_ge_one`, `translated_face_drift_ge_one`, `singleton_rewards_bounded`, namespace `Math.PairedFacePotential`, future `MathUE/Analysis/Examples/PairedFacePotential.lean` (46) |
| Boundary 5: actual Hessian entries and full four-vector spectrum | `actual_hessian_entries`, `translated_actual_hessian_entries`, `hessian_hasEigenvector`, `eigenvectors_span`, `eigenvectors_linearIndependent`, `hessian_hasEigenvalue_iff`, same owner |
| Boundary 5: SAME canonical Euclidean Hessian operator and literal least eigenvalue | `translated_coordinateHessian_conjugate`, `translated_coordinateHessian_hasEigenvalue_iff`, `translated_coordinateLeastHessianEigenvalue`, `translated_coordinateMinimumHessianEigenvalue`, future `MathUE/Analysis/Examples/PairedFacePotentialCanonicalJoins.lean` (52) |
| Boundary 5: actual vertex values 1408 and −1136, top not a minimum | `translatedPotential_top_value`, `translatedPotential_countervertex_value`, `translatedPotential_top_not_minimum` (46) |
| Boundary 5: internally produced non-top GLOBAL minimizing vertex with a −3 coordinate | `exists_non_top_minimizing_vertex` (52) |
| Boundary 5: every bounded nonsingleton completion, same polynomial's face drift and failure of the full relation | `pairedFacePotential_boundedCompletion_face_drift`, `pairedFacePotential_boundedCompletion_not_fullRoot`, future `UniformEquilibrium/Quitting/Examples/PairedFacePotentialBoundedCompletion.lean` (55) |

Boundary 1's actual collision/upper-freeze fixture is the already-reviewed shared 49, not re-proved here. Boundary 6's zero/positive drift scaling is already-reviewed 54 and its typed differentiability repair, not re-proved here. The positive absorption/zero-charge logic, player-count scope, no exact-rational-Nash promise and directional T3 quantifiers remain in the already-reviewed canonical analytic/rational groups. Neither optional43 nor optional60 is required or added by this audit.

## 44: exact integral, not merely a bound

The new kernel is literally k(t)=(1−|t−1|)². Its nonnegativity is unconditional. On [0,1] it is t² and on [1,2] it is (2−t)²; continuity supplies integrability and interval concatenation. The split theorem is for every function continuous on the entire closed segment.

Both half identities are obtained from canonical `taylor_integral_remainder` at center 1 and endpoints 0 and 2. The left integral reverses orientation, giving the necessary minus sign. Ordinary `iteratedDeriv 3` replaces the within derivative using local C³ at EVERY segment point, including endpoints, and interval unique differentiability. The result is exactly:

    ∫₀¹ t²f‴ = f″(1)−2f′(1)+2f(1)−2f(0)
    ∫₁² (2−t)²f‴ = −f″(1)−2f′(1)+2f(2)−2f(1).

Their sum gives `(f(2)−f(0))/2−f′(1) = (1/4)∫₀² k(t)f‴(t)`. The kernel mass is established by actual interval integration, with a cubic primitive, and equals 1/6 after multiplication by 1/4. The factor and signs match the packet.

The regularity premise is local `ContDiffAt ℝ 3` on the closed segment, supplied by the source's open-neighborhood C³ scope. It is not merely within-C³ while claiming uncontrolled ordinary endpoint derivatives, and it is not globally C³. No favorable slope, endpoint inequality, minimum or game data is assumed for the identity itself.

44 also removes `private` from current `Math.taylorWithinEval_two_eq` in `MathUE/Analysis/MidpointThirdDerivative.lean`, preserving its existing proof verbatim. This reuses the Taylor-expansion owner rather than copying it. The existing sharp bound and actual directional-chain-rule declarations remain untouched; their Lagrange proof need not be rewritten to consume the integral identity. Pinned Taylor, interval and within-derivative API shapes were checked; no definite additional API failure was found.

## 45/45A/46: literal polynomial and all face calculations

45 identifies coordinatePartial and coordinateMixedPartial with formal derivatives of the SAME canonical rational syntax. 45A is a useful canonical reuse repair: it proves the Pi.single/`Math.piBasisVector` equality and delegates to existing `differential_piBasisVector` (`MathUE/Interval/PolynomialLipschitz.lean`), avoiding another basis-sum calculation. It preserves both public statements.

46 defines exactly Q(y)=−4∑y+64(y₀y₁+y₂y₃)+16(y₀+y₁)(y₂+y₃) and P(v)=Q(v−1/4). `translatedExpression_eval` connects the actual translated rational expression to P. Actual Fréchet derivatives are obtained from `hasFDerivAt_evalReal`, not assumed from the displayed gradient.

The receiver-row/owner-column singleton matrix is the printed quarter-scaled matrix. Each singleton column s+Γᵢ is unit bounded. All four exact face formulas are proved by finite owner cases. For yᵢ=0 they give 1+4t+32t(u+w)+128uw. Under all-coordinate nonnegativity the drift is at least one. The translated statement concerns P at every point above s and the actual shifted columns. It imposes no additional finite upper cap, so includes the complete source faces required by the packet.

Both Q and P have actual second partial matrix with off-diagonal paired entries 64 and cross-block entries 16, diagonal zero. The four literal eigenvectors are nonzero; their explicit spanning decomposition and independent coefficient proof establish completeness, including the repeated −64 eigenvalue. `hessian_hasEigenvalue_iff` supplies the exact distinct spectrum {96,32,−64}; the separate indexed eigenbasis supplies multiplicity information. These vectors are not claimed orthonormal, which is unnecessary.

The values at top and printed countervertex are exactly 1408 and −1136. 46 proves that top is not a global minimum but does NOT pretend the printed lower-valued countervertex itself is minimizing. 52 supplies the missing actual minimum, as reviewed next.

## 51/52: actual Euclidean operator, attained spectral value, actual minimum

51 is generic glue over the existing `coordinateHessian` and `realHessian` definitions, not a supplied-matrix API. `coordinateMixedPartial_eq_secondFDeriv` differentiates evaluation of the first derivative at a constant basis vector. `coordinateHessian_apply_single` pulls the actual function through `EuclideanSpace.equiv`, uses the real Riesz Hessian inner-product identity, and recovers actual mixed-partial entries. `coordinateHessian_conjugate_eq_matrix` establishes whole linear-operator equality by the basis, and `coordinateHessian_hasEigenvalue_iff_matrix` transports nonzero eigenvectors in both directions. The original Pi norm is not silently treated as Euclidean; the canonical coordinate equivalence is explicit.

The generic operator-identification statements deliberately use global C², which the literal polynomial supplies from canonical `contDiff_evalReal`. This is not a restriction on source reward tables or on the actual fixture. The second-derivative scalar application uses the inspected pinned `fderiv_clm_apply` with a genuinely differentiable derivative map and constant vector.

52 connects the SAME P's canonical Hessian to 46's computed matrix at EVERY point. Its `translated_coordinateLeastHessianEigenvalue` is about the actual infimum of nonzero-vector Rayleigh quotients from `MathUE/Analysis/LeastHessianEigenvalue.lean`, not an input lower bound, maximum magnitude or hand-selected negative direction. It reuses the canonical theorem that this infimum is an eigenvalue under C² regularity, the spectrum iff, and comparison with the actual −64 eigenvalue. This forces the genuine least value to equal −64. The infimum over the literal full box is likewise −64; nonemptiness is internally supplied by zero.

The minimizing-vertex producer first invokes compact attainment for P on the actual box [−3,3]⁴. It then invokes canonical `IsCoordinateAffine.exists_vertex_minimum` (`MathUE/Analysis/CoordinateAffineBoxMinimum.lean`) using affinity proved for the literal P. Its produced vertex is globally minimizing, not merely critical, a boundary-local minimum or an arbitrary violating point. Top-not-minimum forces a −3 coordinate, explicitly below the singleton 1/4. All minimizer data is OUTPUT.

Definite compiler-policy issue: the proof still spells `push_neg at hnone`. Pinned `Mathlib/Tactic/Push.lean` emits a deprecation warning for this tactic, prohibited by the repository warning policy. The frozen overlay below changes only that spelling to `push Not`; no hypothesis, formula or argument changes.

## 55: all bounded collision completions

The face theorem quantifies over every actual reward table having the printed singleton columns and every lower-face point. It does not need bounds on the nonsingleton entries because they do not occur in the face direction. The full-root exclusion quantifies over every such table whose ENTIRE reward table is unit bounded. Thus nonsingleton collision rewards remain arbitrary, without standard Q, normality input, no-UE, or favorable completion premises.

It derives own-singleton nonnegativity from the matrix diagonal internally and delegates to current `not_isQuittingFullExactRootPotential_coordinateAffine` (`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMultiAffineExclusion.lean`), using 52's actual affinity/regularity. The polynomial remains the exact P from 46, and the full relation remains on radius three. This is a candidate-potential exclusion for every bounded completion, not a counterexample game or a proof that any table lacks UE.

## 47 and 53: exact signed boundaries

47 gives scalar arithmetic fixtures only: the allowed reflection can equal −3; the fixed-cap misuse gives 11/2>3; the negative-singleton misuse gives −5<−3; and θ=2/3 gives the positive partial 2/45. They deliberately describe failures after changing required hypotheses, not counterexamples to the proved signed theorem. No unproved profile/game realization is inferred from these arithmetic identities.

53 defines EVERY nonempty coalition reward as the same vector (1,−1,0,0). The singleton identity and absolute unit bounds are literal. To prove punishment equals that vector, the upper bound uses canonical `quittingPunishmentValue_le_pureRowCap` with another player quitting, forcing the same payoff whichever action the owner chooses. The lower bound uses the canonical equality of actual and stationary punishment, then the immediate-Quit branch of each stationary unilateral cap. The support lemma forces the owner into every positive-probability quitter set, so `quit_value_eq` remains valid for arbitrary opponent PMFs. Neither the negative coordinate nor the all-Continue/Never case is discarded.

Consequently all four players are normal even though player 1's singleton is negative and player 0's positive. `allNever_payoff_zero` expressly preserves the actual zero Never payoff; the negative target does not redefine Never. `positive_scaling_preserves_negative_singleton` covers EVERY positive common real scale. This correctly prevents the false inference that positive scaling alone repairs singleton signs. It asserts neither no-UE nor a failure of the reflection theorem under its actual hypotheses.

## Repairs, application boundary and nonclaims

Apply 44 to current `MidpointThirdDerivative` plus its new integral owner. Independently apply 45→45A→46 and 47. Apply 51, then 52 after 46 and the existing vertex/regularity owners, then the one-line 52 overlay below. Apply 55 after 52 and the current full-root multi-affine exclusion. 53 is independent of the new analytic fixtures and uses existing semantic punishment owners.

No new derivative, spectral, compact-attainment, vertex-selection, punishment or full-root foundation is needed. The separate handoff/harness inventories are static drafts; the signed-boundary harness also imports shared54, which must use its already-reviewed repair. Axiom-print output has not been executed here. Root's staging should audit all new declarations, including 52's regularity and coordinate-affinity helpers, in the generated exhaustive audit even where a small original harness only lists the main claims.

The group covers the displayed integral and listed literal fixtures; it does not by itself seal the whole reflection packet. Shared49/54, the analytic/core characterization, rational-search and decision-reduction groups have their own reviews/checks. No optional43/60 work is added.

## Hash inventory

Original patch SHA256 values, verified unchanged:

```text
/tmp/ue-midpoint-integral-sKSsQX/44_EXACT_MIDPOINT_THIRD_DERIVATIVE_INTEGRAL.patch
46d2750273815dcea208fd712c4c9fbdc4ee611bc43d5d15cba742deb0f9c168
/tmp/ue-potential-fixtures-xygynp/45_RATIONAL_POLYNOMIAL_COORDINATE_DERIVATIVES.patch
05851dcb10bf33ac7466c67fd793dee590674ae627c1c25e1ed28ec3b7ba6e49
/tmp/ue-potential-next-complete-group-NUcZS5/45A_CANONICAL_BASIS_DERIVATIVE_REUSE.patch
9769e4e1d3cff63205d75192d56b1ff26b43c3990b5dcd569f993a9d53a3c533
/tmp/ue-potential-fixtures-xygynp/46_PAIRED_FACE_POLYNOMIAL_HESSIAN_FIXTURE.patch
e6280f4f42d8fe4e0fa84a69f1080d2f40c7fd225818efafee4580e3d1d2d171
/tmp/ue-potential-fixtures-xygynp/47_REFLECTION_AND_MULTIAFFINE_BOUNDARY_ARITHMETIC.patch
533b3065ed32ac769c22074d6947a87a719220fcd76c5dacdbffa875ef17d1ca
/tmp/ue-paired-fixture-joins-WMWV4A/51_CANONICAL_COORDINATE_HESSIAN_ENTRIES.patch
9ad3d3bb7de80b833af58a75e9129efc83c271c52ceb2b26e67d7ba126fa2820
/tmp/ue-paired-fixture-joins-WMWV4A/52_PAIRED_CANONICAL_SPECTRUM_AND_MINIMIZING_VERTEX.patch
e66135a0c4714ca9ed680f2c6a169291c52bac097ece6189eb8177b041445fc1
/tmp/ue-reflection-literal-boundaries-VxBUGT/53_CONSTANT_SIGNED_NORMAL_TABLE.patch
4717204fab5cc4ba22b25a2dcef663beb43cc3870aefc29c451444053a0829c5
/tmp/ue-reflection-literal-boundaries-VxBUGT/55_PAIRED_BOUNDED_COMPLETION_FULL_ROOT_EXCLUSION.patch
640ecc91da66d4f55ebfa5f28ffd10aa6978177e0432c8855721470953815766
```

New independent review's proof-only 52 repair:

```text
/tmp/UE_PAIRED_MINIMIZING_VERTEX_52_PINNED_PUSH_NOT_20261002.patch
79d18db2c542af02a851b29af53b58eec311878c579433c045958a8695264351
Exact original52 Lean payload/base
119e6eba084f06a65d86523a3a3d6099376342581602e05d3bddfdb6ce60cc34
Result after the sole push_neg → push Not replacement
13d6b2236b42d725465bfd00a18580b4f011299633a7d264897620c51797e0e0
```

The result was computed only in memory. Exactly one replacement site exists. The overlay has not been compiled or independently reviewed by another agent.

Handoff/harness pairs, respectively:

```text
/tmp/ue-midpoint-integral-sKSsQX/
da42efb6310f9c3cb9bac675f311a206aff32dd5b3c382ee3fc17a27a80e4021
fadd4b07ddacf4a0ab157562e1be7aceb819f91b32ec3fad440570be86354126
/tmp/ue-potential-fixtures-xygynp/
402db5a78a66ee4b505e4d5d0524602ad045cc690a7a7526f27fe3acd6aa043e
6a96c0a5842f1f4084d0e2c2767e4e511ee35ef0dbb0fbbbed71d288ba85611b
/tmp/ue-paired-fixture-joins-WMWV4A/
f76e300bdea3a988e95290231d0ed58d48d3b908f0088d6c8b3a58ad1e91e2e1
2eea976c8c42c157f910dda6eaf28566c98e43ba0d95bb8b14007a1d342a2121
/tmp/ue-reflection-literal-boundaries-VxBUGT/
5973367a012dec552719f7e474badc7361caff877dfe71f8a6b386e88108629e
9750fda4929310769e2b93ba96c0278cfeb6fe108b2d0f57e0054676b3f6d0a3
```

The filenames in each pair are `HANDOFF.md` and `AXIOM_HARNESS.lean`. Source export hash remains `a28b23b400cfef2fce48d0dfd33027b344e00d45a015de549c328dce4f397e69`.

Current canonical owner snapshots:

```text
MathUE/Analysis/MidpointThirdDerivative.lean
3142f89aa0b7fbb0cfea047af0ff4e044aebe8f478fe068454fd2bd0fbbb5a2a
MathUE/Analysis/CoordinateHessianExtrema.lean
f9565c9e8ab55cb97f1a377d0ef495039c63657d9b30bcc5f60bd7620169bb22
MathUE/Analysis/LeastHessianEigenvalue.lean
7bbd633eff47b7f4e746e62472cb68346c7aeb32e782957d5ded7509bbb28aa4
MathUE/Analysis/CoordinateResetFTC.lean
88ce78d2c3bfae71477fa37eb89145e208d851b8d6d1796a43efbe7c03a39e9c
MathUE/Analysis/CoordinateAffineBoxMinimum.lean
e42625a8fc515ddbcbd29005eddc7c351af1e033770b6f92fa7352ab9b56e509
MathUE/Interval/PolynomialLipschitz.lean
b1f551aacc0f2d21c8032f1feef012191197a0fa9ff143e1da2d03657ff526cd
UniformEquilibrium/Quitting/Punishment/ContinueFloor.lean
3a71bf78efc3a53b9e3b47aa2782414c95cacc4666cf1b817ac80d3bef6be66d
UniformEquilibrium/Quitting/Stationary/MinMax.lean
92b3ccc349f07b3a9d118d9289892982cc0e6f71c6d6ea7e398562488c2be9e3
```

Root's current check/application record, not stale sentences in old handoffs, determines actual repository status.
