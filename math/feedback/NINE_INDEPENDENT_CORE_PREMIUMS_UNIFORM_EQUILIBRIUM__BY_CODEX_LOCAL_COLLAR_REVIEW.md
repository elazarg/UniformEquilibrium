# Independent review: nine independent core premiums

Reviewer: CODEX_LOCAL_COLLAR_REVIEW. Date: 2026-10-25.
**Mathematical PASS and export-gate PASS.** No unresolved objection.
Ordinary mathematics only; no Lean build, commit or export operation ran.

Reviewed the complete 768-line candidate for
`NINE_INDEPENDENT_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM.md`, SHA256:

`5e3a447025554569f49951e1ab113d309e25c9949cfad486e8734f3ae5f6f1ea`.

The verdict covers the whole artifact, including the new raw adapter,
behavioral consumer and nonhomogeneous calibration. The independent audit
did not use the other review.

## Statement and uniformity

The class fixes the reference singleton matrix and seven passive entries.
Its nine core participant entries vary in beta*[1,2], with the sole order
condition d>=h. Row0 has the stated participant upper bounds; all other
nonsingleton coordinates are arbitrary finite, and own levels are arbitrary
signed. This includes the specified nine-dimensional rectangular box.

One positive beta0 works on the entire closed normalized parameter set,
including d=h. It is independent of free rewards and own levels. Meshes
and horizon thresholds may depend on their magnitudes. The payoff target
is fixed before accuracy, and every full behavioral deviation is priced.
The unordered box and arbitrary Fin4 closure are expressly not claimed.

## Independent graph and boundary checks

I symbolically recomputed the characteristic polynomial of PG^-1 and the
left-normal equations. The displayed cubic and remaining scalar equation
are exact. The coefficient estimate L<=-6 is valid on the whole pair cube.
Descartes gives one simple negative root; the other spectral block has
positive real parts. The scalar equation places r between a and k, hence
1<=r<=2. The bounds on A,B, A-1/3, Ab and Bh follow with the stated signs.
These are uniform margins, not checks of a symmetric parameter slice.

The analytic quadratic graph transform has contraction factors O(radius)
and O(beta). It does not require the negative eigendirection to dominate
the other linear eigenvalues. The removable beta0 normalization and common
complex neighborhoods give uniform C2 and parameter-derivative bounds.
Finite parameter patches and uniqueness therefore give the claimed common
graph domain and regularity over the compact nine-parameter box.

At d=h, the line u=0,t=v is exactly invariant, with only owner1 active.
Its output satisfies Q1=0 and Q2=Q3. Starting the graph iteration at zero
preserves this line, so T_beta(0,v)=v exactly. Parameter regularity gives
the factor O((d-h)v^2), rather than an uncontrolled O(v^2) error.
The printed rational hazard formulas and tcrit_beta(0,v) are exact.
The v-axis comparison has positive coefficient multiplying (d-h)v, and
the u derivative has the uniform margin 1/24+O(beta+u+v). These jointly
prove physicality on the entire nonnegative quadrant, including d=h and
unbounded outer-coordinate ratios. No strictly positive d-h is assumed.

All next outer values are nonnegative because the nine actual coalition
premiums are positive. They and all hazards have the claimed small bounds.
Graph invariance supplies every later root, with outer contraction O(beta).
The passive0 recurrence uses only the listed passive entries, while its
Quit upper bound uses only the row0 upper bounds. Geometric hazard tails
keep its guard legal and produce the continuous axis with uniform O(u+v)
error. No axis derivative or supplied tail is needed.

## Generic macro, common zero and full execution

I checked the independent-premium formulas F1,F2,F3, the zero of v and
the affine-in-y alpha numerator. The maximum prescription gives v>=0,
alpha>=0 and alpha*v=0 exactly. On the pair chart, adding sigma changes
the numerator by exactly 3beta*sigma, and the quiet2 guard is beta*sigma.
The pair and triple charts agree at z=sigma=0. The general flow equations
remain valid for these unequal inputs, including omission of flow3 at alpha0.

The limiting return geometry is independent of all nine premiums. Its
direct and diffuse arms, corner factor, Bernstein signs and physical
bounds agree with direct algebra. The transverse coefficient chi lies
in [0,1] and satisfies chi<=8z, preserving z>=0 near the pair junction.
Both active branches have a strict negative transverse derivative at the
max corner. Uniform C0 convergence is therefore enough to preserve the
two return-face signs; no differentiable return-root selection is assumed.

At the pair endpoint, Ab<e<=2 and Bh<=d<=2 give Entry0>1 uniformly.
At the diffuse endpoint, F1>=U, F3>=V, F2<=2D and A>1/3,B>=1 give
the stated upper bound. Independent exact arithmetic reproduced
`2D-U/3-V=-18634684506317/1486573974000000`.
Both margins persist on entire endpoint faces and uniformly over the box.
The signs of (-Entry,-Return) have the orientation required by the cited
rectangular Poincare--Miranda theorem. At its common zero the explicit
middle-coordinate projection is the actual output, making the wash legal.
The passive0 macro margin remains strict on the chosen common tube.

The execution reverses the backward wash in the correct chronological order.
Equal-hazard flow meshes preserve each aggregate survival exactly. Active
owner coordinates stay zero; outsider Quit errors are bounded by the finite
positive pair maximum times mesh size. The empty seam is the only policy
and Continue defect. Every deviator faces opponent absorption at least x
per period, so its expected number of seam visits is at most 1/x.
Its mesh error is charged once, when it first Quits while live. Telescoping
gives delivery E_N/x and full terminal regret C*max(delta)+2E_N/x.
The expected absorption bound L/x yields the common finite-horizon estimate.
This covers complete behavioral laws and Never, rather than only periodic
or one-step deviations. Almost-sure absorption justifies signed own-level
translation without changing the original Never payoff.

The raw query census is sufficient. A core root uses the specified nine
participant entries, seven passive entries and row0 upper bounds. A solo
flow or a unilateral deviation there queries only a singleton or its own
pair. Arbitrary remaining pairs affect the mesh constant; no other free
coordinate or nonzero-owner grand reward enters a guard or prescribed value.

## Nonredundancy, exact tests and source gate

The complete separating table changes only Z1(123) from e to 2e among
proper participant rewards. It lies in the ordered box with d=h, so it
also tests the equality boundary. I independently recomputed its Q1 change,
the double-sure numerator 3e^2+12e-1, both sure-face polynomials Nz,Nw,
their coefficient bounds 76 and107, and the changed child123 joining gap.
All agree exactly. The unchanged sure cases retain their logic, including
the row2 lower bound needed to exclude feasible punishment tails.

For the complete stationary census, the new E1 satisfies 0<=E1<=hD1^2
with h=2e, and Q1<=hD1. The support eliminations and fully mixed bounds
therefore remain valid; their contradiction has ample strict margin on
e<=1/4000. This is not inferred merely by continuity from a homogeneous row.
The protected sets, all nonnegative weight selections, all fourteen child
tests, principal/LCP tests, pair partitions, quotient and role/rescaling
checks also retain their stated necessary-condition scope.

The nonhomogeneous row fails the equal-row premise of the rectangle, cone,
closed-wedge, lower-diffuse and crossed-premium classes. Its pair test and
both quantitative premium bounds fail as stated. Positive row rescaling
cannot identify its unequal entries; the role census allows only identity.
Thus this is new raw-table coverage beyond those prior packets, not merely
a stronger strategy construction on an already covered direction.

The unordered example was independently checked: its normal and outer map
are exactly those printed, and two leading steps exit the physical cone.
It correctly limits the graph construction, without claiming nonexistence
of UE. This and the d=h identity supply relevant exact boundary controls.

I checked the rectangular-zero declaration and its strict face orientation,
the finite-flow compiler and terminal target declaration, and the named
classification interfaces used in the coverage audit. Existing sources
consume finite words or rectangle signs; the candidate produces them all.
Its self-contained finite execution argument prices the deviations directly.

All export requirements pass: exact raw class and quantifiers, produced
graph/return/guards/profiles, probability and agency audit, exact boundary
tests, substantive coverage separation, source correspondence and concrete
formalization decomposition. No strategic witness remains assumed.
This supplies one independent review; promotion also requires the second
matching-hash unrestricted-scope review. Fin4 itself remains open.
