# Independent review: crossed premiums, hybrid core and diffuse flows

Reviewer: CODEX_LOCAL_COLLAR_REVIEW. Date: 2026-10-25.

**Verdict: mathematical PASS and export-gate PASS.** No unresolved objection.
This is an ordinary-mathematics review, not a Lean verification. No Lean
build, commit or export operation was performed by this reviewer.

Reviewed the complete 1549-line candidate for
`CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM.md`, SHA256:

`cb596121a3c8518a9c54eaec99faf14bda066a7095df41c8ec12f971869a19b4`.

The verdict pins that complete artifact, including its calibration and
semantic consumer. The independent audit did not use the other review.

## Scope checked

The theorem covers U: `0<a<3,c>1,2a<3c`; L: `a>3,0<c<1`; and
B: `a=3,0<c<1`, with sufficiently small positive beta. Compact uniformity
is asserted separately in each stratum. No uniform finite-prefix bound
or threshold through their joins is claimed. The raw table requires
the reference singleton matrix, seven specified passive entries, nine core
participant entries, six row0 proper-participant upper bounds and its grand
upper bound. Every other nonsingleton coordinate is arbitrary finite data.
The original own-singleton levels are arbitrary signed numbers.

The threshold is independent of those free coordinates and levels. Finite
meshes and horizon thresholds may depend on their magnitudes. The conclusion
has one target before accuracy and covers every unilateral behavioral law,
including Never, over all sufficiently long finite horizons. It does not
claim a boundary-uniform threshold, arbitrary Fin4 closure, or a counterexample.

## Exact hybrid producers

On U, I independently checked the spectral reduction and derivative cone. The
negative eigenvalue is simple; the two remaining eigenvalues have spectral
radius below its magnitude r. Symbolic reduction by the characteristic
polynomial verifies the dissipation identity, theta identity and strict gap
in (4)--(5). In particular `C0=(c-1)(3c-2a)/8>0` has the required sign.

For the weighted norm `P0|Y|+Q0|W|`, both induced column bounds are below r.
The four derivative bounds in (9) preserve the prescribed cone. The less
immediate upper Y bound follows from `r-k+delta=(9c-5)/8`, `k<r` and
`delta<9(c-1)/16`; its margin is strictly larger than the displayed one.
The leading operator is therefore a contraction on the stated complete
function class, rather than an assumed choice of a switching itinerary.

The exact pair surface and quiet2 guard were independently expanded:
`H Psi(u,v)-2y-w=Psi(a beta w,c beta y)` and (11) hold identically.
Its legal region is invariant because the hazard ratio contracts by a
factor tending to `2a/(3c)<1`; shrinking the radius absorbs the quadratic
guard term. The zero-y case introduces no hidden division.

The critical height h vanishes at beta0, so h/beta is analytic. The exact
contact identity follows from the pair identity and the positive factor of
`t-Psi(u,v)`; it preserves the required vanishing at the switching boundary.

The active image-cone margin and dissipation absorb the Taylor errors,
giving one positive root with uniform multiples of f_beta as bounds.
The enlarged derivative cone preserves both previously sharp bounds;
small D_z(F_s/beta) gives strict contraction. The locally bi-Lipschitz
successor justifies the a.e. chain rule; the zero extension preserves the
global coordinate increment bounds.

I specifically attempted to falsify the whole-quadrant assertion. For fixed
nonnegative outer caps, the scalar residual in (18) has initial value at
most zero and slope at least `1-xi Q1/3-o(1)>0`. Its root stays inside the
chosen domain after shrinking the outer radius. This yields a unique
physical representative, the exact lower obstacle, and the claimed upper
bound. On the stopped part, the pair guard is equivalent to the critical
height being nonnegative. Pair invariance and uniqueness place the next
output on that same stopped graph. At contact the pair and triple roots,
including their quiet2 outputs, agree exactly.

On L, I independently recomputed the inverse leading map (P3). Its cone
inequalities give increasing v/u, positive z after the first reverse step,
and a finite crossing to u<0. The number of steps is uniform on parameter
compacts. Truncating the last cone at u=0 preserves physical hazards even
when its unused virtual endpoint is nonphysical. The determinant of the
first three seams is exactly
`-(a-3)^2(2a-3c)^2/[486ac(c-1)]>0`.
Invertibility then proves every needed adjacent-sheet intersection transverse.

The normalized forward iterates are analytic through beta0 and have
derivative N^n at the origin. Their IFT supplies precisely the needed
graphs, without evaluating inverse iterates on a fixed shrinking domain.
Exact ordered seam curves tile the physical quadrant. The extra virtual
ray handles a seam hitting u=0; empty last sectors cause no ambiguity.
The first triple hazard factors along the exact contact curve. Later
sectors have strict physical margins. The exact map sends each sector
to the preceding one, ultimately entering the invariant legal pair region.
Thus all prefixes are produced, and root selection agrees at every seam.
The pair-guard sign gives the exact lower bound by Psi throughout.

On B, the analytic quadratic graph transform requires no normal spectral
dominance: its nonlinear contraction factors are small with beta and radius.
The exact solo3 line forces T(u,0)=u/3. Both T-tcrit and T-Psi therefore
factor by v; their positive derivatives in (B12), with uniform C2 bounds,
give the claimed strict comparison when v>0. This verifies physicality
and continuity at the degenerate axis, rather than importing an a<3 margin.

For all three producers, outer caps contract by O(beta), hazards are
O(u+v), and the passive0 guard has a positive margin. Geometric tails give
the continuous axis and O(u+v) estimate. Constants are uniform separately
on the stated compact subsets; only L needs a finite triple-prefix bound.

## Return and behavioral consumer

I checked the general flow equations (A3)--(A4), both exact zero factors in
(A5), and the pair-slack modification. Taking the maximum enforces
`alpha>=0, v>=0, alpha*v=0` exactly. The projected axis residual is only
auxiliary off E=0; at a simultaneous zero it is the actual core output.

The direct and diffuse return arcs have the claimed signs and meet at the
same corner. Independent exact arithmetic reproduced the corner factor,
the four bivariate Bernstein bounds for P_w, P_z, P_w+P_z and J, and the
displayed rational endpoint. At that endpoint,
`D-V=-39814968789439/495524658000000<0`. On U this gives the negative
entry sign. On L and B, `a>=3` and `D-U=-z_L(1-w_L)/2<0` give that sign.

The ribbon avoids assuming differentiability of the hybrid axis value.
Its transverse direction changes from the w direction to the diagonal only
where both limiting directional derivatives are negative. It remains
physical and has `z*sigma=0`, including its pair/triple join. The maximum
branches have the same strict transverse sign at their corner. Uniform C0
axis convergence preserves both transverse face signs. A fixed finite pair
slack supplies the positive entry face before beta is chosen small.
The clipped Brouwer map has correctly oriented inward signs, yielding both
return and entry simultaneously without a continuous return-root selector.

The finite periodic word reverses the backward wash in the correct order.
Every flow is a nonnegative segment with its active owner's cap zero.
Equal-hazard meshes preserve aggregate survival exactly. Their only error
is a forced-Quit error charged at most once per deviator. The empty seam
cost is summed over at most 1/x expected visits; no exact tail is assumed.
This gives delivery error E_N/x and unrestricted terminal regret
`eta_n+2E_N/x`. Opponent absorption holds uniformly over every complete
deviation, so the remainder vanishes and expected absorption time is at
most L/x. The finite-horizon estimate and fixed-target conclusion follow.
Signed singleton levels are translated only after almost-sure absorption.

The reward-query census is complete: core roots use the seven passive and
nine participant entries plus row0's upper bounds; a deviating player at a
solo flow queries only its own pair reward. Arbitrary pairs containing0
therefore affect the mesh constant only. No other free entry is consumed.

## Coverage, source correspondence and gate

The complete calibrations with `(a,c)=(1/10,2),(4,1/2),(3,1/2)` fit the
raw theorem and stated small-premium audit box. I checked the sure-owner face
census, including the actual row2 lower bound needed for punishment tails;
the complete stationary-support contradiction; protected-set and all-weight
tests; and the fourteen proper-child obstructions. The child023 limiting
debt construction keeps its positive outsider gap against full stopping laws.
The principal minors were independently recomputed. The principal-inverse,
LCP, matching, quotient and role/rescaling tests retain the stated scope.

All three rays fail the quantitative, signed-chamber, pair-contraction,
equal-premium, cone, closed-wedge and preceding diffuse-flow criteria.
The preceding diffuse theorem excludes the first ray by c>1 and the other
two by a>=3; their pair test fails c>=1. These are exact new directions
on both crossed sides and the added boundary. The calibration does not
claim to exhaust all conceivable UE certificates.

I checked the named declarations in the four conjecture/terminal/flow/path
source files and the five classification files cited by the candidate.
Their types agree with the stated interfaces and coverage tests. The
existing finite-flow and supersolution results consume supplied data;
the new graph and return are produced here. The direct periodic argument
also supplies its own all-behavior proof and signed-level translation.

All export criteria are met: explicit finite raw inputs and quantifiers,
complete producer and consumer, probability/agency audit, exact positive
and negative tests, substantive nonredundancy, source correspondence and a
concrete formalization decomposition. No strategic witness is left assumed.
This review supplies one of the two required independent unrestricted-scope
reviews; the coordinator must also retain the second matching-hash review.
