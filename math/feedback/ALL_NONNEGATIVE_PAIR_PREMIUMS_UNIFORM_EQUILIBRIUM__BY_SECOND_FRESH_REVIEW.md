# Second fresh independent whole-artifact review

Verdict: **PASS — ordinary mathematical soundness and export gate.**

Reviewed artifact: [frozen packet](../exports/ALL_NONNEGATIVE_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM.md).
Final SHA-256: `44a1d75abf5306ffc20071e3557f75fdb0761ac5edd183a1a1244512f8225a7d`.
Reviewer identity: `/root/all_positive_second_review`.

This is a fresh review of the entire artifact, including the older branches,
not inherited approval of their previous reviews. My initial complete read
was against SHA-256
`2db0da74557278e1b6011c9dd88ae8ce0a0fa64dced421c15745f3e74588de5c`.
The final version makes two accurate scope clarifications: the pair-surplus
formula with p denominators is restricted to p>0,K>0; the center-return
algebra is stated on all 0<beta<=3/50, separately from the cooperative
connection's interval [3/5000,3/50]. I checked both clarifications in the
pinned final bytes. There is no unresolved objection.

## Exact conclusion and strategic inputs

The proved class is the literal four-player table in Section 1, with its
seven row-0 caps, twenty-one independent unrestricted completion entries,
and four arbitrary own-singleton levels. It proves existence for one common
finite C>=100 on K>=C,p>=0, and separately on the explicit cone
K>=0,p>=max(1,2K). The first conclusion covers the entire nonnegative p/K
half-line, including p=0. It does not settle arbitrary Fin4, and supplies
neither a numerical large-K threshold nor coefficient-perturbation scope.

The raw table produces every strategic input: finite exact cores or the
hybrid predecessor sequence; a legal permanent pair tail; its limiting
entrance; an outer return root; the solo blocks and finite repair; and finite
calendar approximations. There is no assumed equilibrium, continuation law,
shooting orbit, strategic root, recurrence certificate, or behavioral cap.
No conditional export exception is needed.

The finite C is independent of the twenty-one free coordinates and original
own levels. Those coordinates affect the required solo-0 mesh and payoff
bound, which may depend on the fixed game and requested accuracy. They do
not enter the root producers or their uniform parameter thresholds.

## Mathematical audit

Sections 2–4: the pair predecessor equations, finite absorption masses,
limiting entrance, row-0 rectangle test, and row-3 surplus recurrence are
consistent with the original product-game payoffs. I independently derived
the row-3 recurrence by substituting the reciprocal pair recursions. The
pure-3 return polynomials also agree with direct substitution of the pair
entrance and outer hazards. The seven rational Bernstein bounds reproduce
exactly and give existence, uniqueness in the specified box, and a
nonsingular outer Jacobian. The pure-3 branches price every finite prefix.
The fourth-prefix argument handles the beta=3/50 equality boundary, and the
K=0 branch uses nonsingular physical recursions and finite-word continuity.
The singular formal d0=L/K is not played at K=0.

Sections 5–7: the limiting invariant follows directly from
L=3w+(1-w)L_next and X=-w+(1-w)X_next. The center-return polynomial gives
a simple root; its positive-beta algebra extends below the cooperative
connection's interval, as the final clarification states. The positive
cooperative connection uses both the strict triangle invariance and the
monotone unstable tangent. It does not require invertibility in the stable
normal direction when k=0.

The mixed finite boundary problem solves stable and center coordinates
forward and the expanding scalar coordinate backward. Its contraction is
on the complete x-array, including the terminal row. The scaled Green
estimate controls x0/t and its parameter derivatives, rather than dividing
an unscaled O(N alpha) error by t. The normal-form remainder estimates and
the alpha=t Lambda relation give the required polynomial-times-exponential
smallness. Fixed-index physical signs are supplemented by a uniform tail
estimate, so the proof covers every root of the increasing-length core.

The two moving boundaries are precisely w1=0 and the first pair surplus=0.
The exact reciprocal-pair forcing propagates the first surplus to every
later finite prefix. Moving a w=0 root across the core/prefix boundary
preserves the actual entrance and target. Uniqueness in the finite boundary
problem and outer root then identifies the same physical alpha at adjoining
branches. The proof correctly does not identify the auxiliary Lambdas.
Monotone K intervals therefore cover all sufficiently large K uniformly on
the compact middle-ratio interval.

Section 8: I separately checked the three-support selector, its boundary
agreement, the cone inequalities, and all quiet/active comparisons. The
strict f monotonicity is uniform at beta=0 and uses beta+alpha rather than
division by beta. Pair23's quiet row-1 inequality has the correct sign;
pair12's row-3 surplus is the exact nonnegative selector slack. Row 2 is
indifferent throughout. The cone allows W to become positive, as required
by its eventual entrance, and retains the essential lower bound W>=-100L.

The hazard-summability proof is valid for a fixed positive alpha. The
geometric X/L estimate gives a finite switch to a permanent pair12 tail;
at beta=0 its first pair step sends X to zero and subsequent steps are
pure-player-2. Limits are entrance annotations of finite reversed words,
not an infinite chronological prehistory or a continuation after an
infinite calendar.

The positive-beta tail comparison uses contraction of both scalar pair
maps and controls total variation through the sum of physical hazard
errors. It compares only rows 0 and 3, whose rewards remain uniformly
bounded as K,p grow. The joint alpha,beta->0 argument supplies a distinct
beta-independent pure-player-2 comparison with error O(X_M). Its fixed-depth
limit has X'=3X/(4+X), so the subsequent M limit removes that error. This
legitimately covers all ways alpha and beta approach zero, with no hidden
bound on alpha/beta. The compact-subsequence argument combines the interior
and joint-boundary limits into uniform convergence on the whole closed
beta interval. The same estimates preserve every row-0 margin.

The fixed-alpha entrance is continuous across selector switches. The
outer root is then obtained by stability of local nonzero degree under
uniform continuous perturbations; differentiability of the hybrid entrance
is not assumed. I independently computed the beta=0 center Jacobian
[[5/2,-45/14],[0,-10/7]], with determinant -25/7. Compactness supplies one
alpha threshold for this entire small-ratio branch.

Section 9: every root comparison is for the original independent product
hazards. Before absorption there is one surviving public history; an
arbitrary private behavioral replacement induces a law on finite quitting
dates and Never. The Bellman maximum therefore controls the full deviation
class. The solo-0 quiet errors are bounded by the mesh times the positive
parts of the unrestricted joining rewards; Quit errors enter a maximum,
not a sum. The repair's 43-step rational inequality is true, including the
wash equality boundary.

Only the solo-2 junction has an annotation residual after finite prefix
truncation. Opponent-deleted survival is bounded by 1-min(a,b) per period
uniformly in the deviator. This proves the displayed terminal error bounds
and the finite-horizon comparison uniformly over all complete replacements.
A selected outer root and limiting entrance fix A before accuracy. Prefix
length and solo mesh may subsequently vary, but the target kappa+A does
not. Almost-sure opponent absorption justifies adding the native own levels
to terminal payoffs while retaining original zero live and Never payoffs.

## Adverse checks and nonredundancy

I inspected and ran both compact exact checkers:

- `math/experiments/CODEX_POSITIVE__OUTER_BOUNDS_CHECK.py`, SHA-256
  `64181fc70f26b5755066f0e88f7e3659f82d84db9fc8d797cc203c1a311ff4d3`:
  all seven exact tensor-Bernstein bounds passed.
- `math/experiments/CODEX_POSITIVE__CORRELATED_WEDGE_CHECK.py`, SHA-256
  `f1970e8ae5f0f0bae238a8d44248dee1c0ef3c5f9590703d517325111ad45949`:
  all 80 nonzero stationary patterns excluded in 1046 nodes and all 65
  sure-root patterns excluded in 371 nodes.

The wedge check retains the correlation between the unbounded K and p by
its nonnegative polynomial combinations. Its baseline relaxations have the
correct monotone direction, including beta=0. The origin deletion uses the
proved quadratic remainder estimate, and all other box deletions use strict
rational Bernstein signs. Closed mixed-coordinate cubes are safe
supersets. The sure-root lower continuation bound covers arbitrary
behavioral continuations, including the unique-sure-player case; this is
stronger than merely excluding stationary repetition of an induced row.

I independently enumerated all principal inverses and signed inverse
columns of the literal singleton matrix. Its determinant is 25. Its only
nonnegative-inverse principal triple is 023, with exterior inverse row
(-3,6,2)/5. The full inverse has column 0 equal to (8,3,14,10)/25 and column 2
equal to (9,-6,-3,5)/25. The only labeling satisfying the attached-negative-
pair sign template is (3,1,0,2), with m=-2. These confirm the stated
passive-child, inverse-column, and attached-pair obstructions over their
complete relevant choices. The proper-support weighted-column alternatives
cannot use either growing reward coordinate: the negative column needed
for recipient 1 does not occur, and the eligible positive column 2 on 023
omits player 1 from coalition 12. The eligible negative column 2 on 123 is
irrelevant to the positive growing coordinate and does not invalidate this
argument.

The ordered-anchor obstruction uses strong connectivity and the strictly
positive participant vector (11,2,1); it rules out all marked sets, orders,
and positive weights. The same vector excludes every upper-average weight
on the core. The joining charge at 12 is +7, excluding the boxed-charge
alternative there. The three pair partitions each fail a raw positive
mate-difference prerequisite, independently of proof weights. The unique
mutually positive and mutually negative pairs intersect, excluding signed
four-cycle arrangements. These are actual raw-table exclusions, not failure
of a selected witness.

The ray p=K/1000 is beyond the prior small-positive contraction mechanism:
its necessary D=4-9797 beta/2 is already negative. It is also outside the
prior negative and p>=2K regions and cannot be relabeled or positively
row-rescaled to the fixed-K scalar family. Thus the result adds an actual
previously surviving class, even though some parts overlap accepted
existence packets. I inspected the relevant accepted raw criteria, including
central positive wedge, weighted collision dominance, boundary and signed
inverse-column, ordered-anchor, mixed-support upper/charge, attached-pair,
both-joint-premiums, finite-invariant-cone, and unequal/crossed diffuse-core
packets. Their hypotheses or exact stationary/sure-root conclusions do not
supply the separating ray.

## Source and export boundary

Repository policies and the export requirements were read. Exact Lean
sources inspected include:

- `quittingUniformEquilibriumPayoffConjecture`,
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`,
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`,
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`;
- `SignedFourCycleSingletonData` and its raw tests in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean` and
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleLargerRewardAdapter.lean`;
- `exists_stationary_uniformPayoff_targetApproximation_of_weakHalfRaw` and
  `exists_stationary_uniformPayoff_targetApproximation_of_strictRawUnit_nonnegativeInverse`,
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakBoundaryTarget.lean`;
- `stationaryTerminalNash_or_sureSolo_everyHorizon_of_oneSidedWeakUnitRawGuards`,
  `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitFiniteHorizon.lean`.

The nonnegative-inverse boundary approximation consumers fail the literal
inverse test. On the separating completion all own levels equal 1, so the
one-sided sure-owner consumer would yield an exact stationary/sure-solo
profile and is excluded by the complete pattern certificate. No unseen
punishment-tail possibility is inferred away from stationary failure alone.

The packet's definitions, finite-data adapter, positive and negative
boundary checks, complete proof, fixed-target consumer, and proposed Lean
targets satisfy the mathematical gate. Its proof does not depend on the
scratch scripts or other conference files; the polynomial data and exact
finite-check algorithms are contained in the artifact. No strategic input
remains unproduced. This review grants ordinary mathematical evidence only;
it does not grant new L, A, or C seals or claim a Lean build.

I ran no Lean, Lake, Git, or repository mutation. All review artifacts are
in /tmp. Promotion remains the coordinator's action and requires the other
fresh whole-artifact review to PASS these same final bytes.
