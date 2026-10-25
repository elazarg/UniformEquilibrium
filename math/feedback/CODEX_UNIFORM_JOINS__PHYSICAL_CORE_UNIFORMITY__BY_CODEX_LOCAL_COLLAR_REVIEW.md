# Independent review: uniform physical cores across switching boundaries

Reviewer: CODEX_LOCAL_COLLAR_REVIEW. Date: 2026-10-25.
**Mathematical verdict: PASS.** No unresolved objection.
This is an internal ordinary-mathematics review, not an export-gate approval
or Lean verification. No Lean, commit or export operation was performed.

Complete artifact reviewed:
`math/notes/CODEX_UNIFORM_JOINS__PHYSICAL_CORE_UNIFORMITY.md`, SHA256:

`1805d0fe098483278f20241fc9d525d1ab7896224a83566e79ac1dcfcd6c3b83`.

The verdict covers the complete 1039-line artifact, including all three
local producers, the analytic joins and their common behavioral consumer.

## Exact conclusions checked

The corner theorem supplies one positive radius and scale threshold on a
closed box around (a,c)=(3,1), including both sides of both boundaries.
For each fixed compact c-interval inside (0,1), the second theorem supplies
one threshold on a full two-sided strip around a=3. The right-side number
of triple steps may diverge; the claimed constants do not depend on it.
The third theorem supplies a two-sided c=1 band for compact a-intervals
inside (0,3). These are uniform statements, not pointwise thresholds.

All three conclusions use the stated seven passive entries, nine homogeneous
core entries and row0 upper bounds. Other finite coordinates and signed
own levels are unrestricted. The targets precede accuracy, and all complete
behavioral deviations, including Never, are covered. No threshold on every
positive ratio rectangle or the whole positive premium cube is claimed.

## Dynamic corner graph

I recomputed (C10), the pair identity, residual sign and player2 formula.
The pair correction is exactly h(beta K)/P. On the triple branch the
residual at zero makes J(x,0)>Psi, preserving nonnegativity exactly.
At contact both roots, player2 outputs and guards agree. A pair step may
feed a triple step; pair invariance is not assumed.

The candidate Lipschitz bounds control h(beta K)/beta by finite increments.
Its possible adverse z slope is at most delta*(11/2+O(theta)); the residual
therefore remains strictly decreasing with the displayed m>0. Its positive
value at zero is bounded by C*epsilon*(u+v), giving a unique clipped root
of that size. All trial arguments stay inside the fixed candidate domain.

The coordinate root bounds (C16) hold also when one compared root is zero.
Together with J_z=4/3+O(theta), they give the invariant Lipschitz class.
The positive-part contribution carries an additional beta factor and is
controlled without differentiability or regularity of the contact set.
In the weighted distance, the root comparison uses the selected-root bound
|K|_1<=(1+Ctheta)(u+v). The limiting contraction coefficient is 2/3,
and the stated choices make it uniformly below 3/4. Thus Banach produces
the full graph on the corner box. No beta0 extension of an arbitrary
candidate h(beta K)/beta is required.

At the central ratio (3,1), the exact guard is nonnegative and the zero
correction is fixed, proving T=Psi there. Parameter continuity for beta>0
and continuity in graph inputs follow from the uniform contraction.
All successor caps remain on the graph and contract by O(beta).

## Right-band control at arbitrarily many sheets

The full analytic linearization is legitimate: L_beta is invertible with
norm O(beta) and inverse norm O(1/beta), while the quadratic graph operator
has contraction factor O(beta). Its normalization is removable at beta0.
This argument requires no dominance of the negative eigenvalue modulus,
so it also covers c<5/11. The exact solo3 axis at a=3 gives the transverse
factor J_epsilon and its derivative versions for both K and its inverse.

I symbolically verified the exact reverse map (U4). Each cone inequality
is preserved with the stated uniform margins. In particular the scaled
upper-u constraint has a positive limiting margin over its entire bounded
U,Z domain, including the small negative lower U endpoint. The lower v
bound, positive z bound and u+Mv bound have margins independent of a-3.

The angular descent (U6)--(U7) is valid. For nonnegative next u it follows
by division by the positive lower v multiplier. If next u is negative,
small current tau has a uniformly negative next numerator, while larger
tau supplies its own gap. Continuity extends this to a small negative tau
interval. Thus the final ray has a fixed negative margin and the needed
planes satisfy (U8), even when their number tends to infinity.

The inverse contact curves are controlled by cone order, not by repeatedly
adding local errors. The contact ray has facet margins proportional to
epsilon, and both its point and tangent perturbations are O(epsilon*s).
The positive reverse map preserves their relative order bounds at every
depth. The positive functionals v and ell then give uniform relative
errors and strictly positive radial derivatives. The forward contraction
provides a common covered radial interval for all inverse depths.

On returning to original coordinates, the transverse derivative estimate
uses point and tangent comparisons to the same ray. This justifies
|t|J_epsilon(x)<=C|x|v(t); no factor 1/epsilon appears. Consequently the
exact angular curves have uniform relative errors. The multiplicative
gap between consecutive linear angles keeps every exact seam ordered,
including the last seam beyond u=0.

The normalized sheet remainder in (U11) follows by combining two forward
contraction factors with the lower bound on the linear normal. It decays
as (C3*beta)^n. Uniform projection angles therefore yield a common IFT
radius and C1 bounds for every needed sheet. This avoids a hidden
inverse-domain or depth-dependent radius assumption.

The corrected original-coordinate argument is essential and valid. On
physical sectors, epsilon*u<=Cv and |A_n|u<=Cv. The longitudinal coordinate
error is therefore multiplied by a sufficiently small plane slope. First
absorbing the resulting C*rho*|z| term proves |z|<=Cv; substitution then
gives the needed O(rho*v) value error. It is not claimed off those sectors.
Later sheets keep a positive hazard margin. For the first sheet I verified
the exact contact factor and its limiting positive unit (1-c)/(1+3c).
The comparison between linear cap height and actual hazard has the required
weighted vanishing-axis factor, rather than an unweighted O(beta*u) error.

Normalized pair/first-preimage transversality excludes extra intersections
uniformly at a=3. Exact descent and ordered boundaries put each sheet in
its predecessor. The legal pair sector is invariant with a common ratio
contraction, and the lower bound T>=Psi follows from its exact guard sign.
Adjacent roots agree on every seam. All final root and radius bounds are
independent of the number of sheets.

## Left extension and c=1 crossing

The pulled-back invariant plane on the left has the stated tangent and
uniform analytic bounds. At a=3 its exact solo3 line forces the quadratic
axis remainder to carry the factor 3-a. I checked both threshold subtraction
formulas and the positive v derivatives. Integrating with common C2 bounds
proves both lower comparisons by kappa*((3-a)u+v), including the boundary
axis. This supplies the common left threshold and hence the two-sided band.
No continuity across a=3 is inferred from unrelated existence statements;
the consumer needs input continuity for each game and the proved common bounds.

For the upper c=1 crossing, I verified the derivative table and all scalar
identities in (J7)--(J16). Monotonicity of h in u makes the K1 contribution
help the downward residual slope. The exact c>=1 boundary sign gives
z_h=O(u) and K1<=(3a/(3+2a)+small)u, validating the /u metric even on
arbitrarily thin sectors. Its closed class is complete and its coordinate
comparisons remain within the stated triangular domain.

The residual increases strictly in u, so there is at most one switch on a
fixed-v interval. Exact contact gluing preserves global u monotonicity.
The upper u slope has the positive slack in (J14); the v slope coefficient
3/(3+2a) is uniformly below one. Small D followed by small eta,rho,beta
preserves both bounds. The weighted contraction coefficient is exactly
18a/(3+2a)^2 at the limit; its bound 3/4 follows from (2a-3)^2>=0.
Thus the proof does not assume smoothness across a switch or pair invariance.
Weighted-metric parameter continuity is not asserted: uniform convergence
of the continuous Picard iterates supplies ordinary C0 continuity instead.

The new lower-side analytic argument is complete. The c=1 polynomial
factor and exact solo1 axis give the (1-c)v^2 remainder factor. Uniform
u slope and axis comparison imply physicality, while the nonpositive pair
guard gives T>=tcrit>=Psi on a common lower band. At c=1, the analytic
correction lies in the upper class, with slope-slack numerator
(1-k)(6k+1)>0. Its roots make it a fixed point, so uniqueness identifies
both graphs. Margins are uniform on the fixed compact interval only.

## Common return and behavioral consumer

For every core, the passive0 guard follows from its fixed positive input
margin and the row0 upper bounds. Summable hazards give the common continuous
axis estimate S=p+O(u+v). Unbounded free rewards are not queried there.

The cited return geometry is parameter-independent at beta0. The corner
and c=1 bands use c>2/3; the a=3 strip uses D-U+eta*U/3<0 after shrinking
eta. These give common negative entry faces. Fixed finite pair slack gives
the positive face before beta is chosen. The common axis estimate preserves
both return faces. Miranda produces an actual entrance and return without
a normalized graph limit or continuous return-root selection.

The referenced finite periodic consumer applies with all of its hypotheses
supplied: exact roots, viable singleton segments, fixed target, vanishing
wash seam and opponent absorption at least x per word. Its estimates price
every behavioral law, charge mesh error only at quitting, and sum seam
error over at most 1/x expected visits. The finite-horizon bound and signed
level translation are valid under that uniform opponent absorption.
Only queried pair rewards enter the mesh constant; they do not affect the
common beta thresholds. The cited source interfaces match this usage.

All three uniform theorems follow; broader uniformity remains open as stated.
