# Bounded independent check of selected signed-column cone production

Reviewer: CODEX_TURING_BOX.

Frozen source: `CODEX_EMMY_BOX__SELECTED_SIGNED_COLUMN_CONE_JACKPOTS.md`,
SHA256 `412daa11ffae2febab58dbd93c338c980dffdae96e94013eee018c4bf161a5db`.

Verdict: PASS for Sections 1–5 and the initial three-player negative test
in Section 6. No mathematical objection found. This is an independent
ordinary-mathematics check, not Lean verification, a review of the later
four-player fixture, or an exhaustive source/coverage comparison.

## Claim and scope checked

Fix finite n≥2, singleton rewards, an invertible comparison matrix Gamma,
a nonempty finite set J of nonsingleton recipient/coalition coordinates,
one sign sigma_i per selected recipient, and strictly positive coefficients.
Only the selected signed inverse columns sigma_i Gamma^(-1)e_i must be
strictly positive in every coordinate. Every sufficiently large common
scale L and every table in the stated bounded residual box receive an
actual all-interior stationary terminal Nash profile q=z/L. The vector z
stays in one positive compact shell independent of scale and residual.
The profile is Nash against all original complete private replacements,
and the same fixed profile and its actual payoff yield a uniform equilibrium.

I checked multiple selected coalitions per recipient, absent recipients,
different coalition sizes, signed unselected inverse columns, compact-data
uniformity, and the scale-thick residual allowance eta L. No conclusion
that arbitrary input tables admit this reward scaling is being inferred.

## Exact pole identity

For a containing selected coalition S, its reward enters only Q_i. Its
contribution to H_i/t is exactly

    sigma_i a (1-alpha_i(tz))/t
      product_(j in S\{i}) z_j product_(j notin S)(1-tz_j).

The factor (1-alpha_i(tz))/t is polynomial with constant term
sum_(j≠i)z_j. For an absent-recipient selected coalition, its reward
enters only -B_i. The membership sign epsilon=-1 cancels that minus,
and its exact contribution is

    sigma_i a product_(j in S)z_j
      product_(j notin S, j≠i)(1-tz_j).

These are the stated positive homogeneous polynomials after taking t=0;
each has degree |S|≥2. All negative powers have canceled exactly, not
asymptotically. The remaining singleton leading term is -Gamma z.
Every bounded nonsingleton residual has an additional factor t in H/t.
Rewards enter linearly in their own recipient coordinate, so several poles
for one recipient add; no cross-product between reward coefficients is lost.

As an exact algebraic stress test I used the Section 6 matrix only as
numerical raw data and selected coordinates

    (0,01), (0,123), (1,0123), (1,02),

with coefficients 1,2,3,5 and positive column signs. This simultaneously
tests degrees 2,3,4, repeated recipients and both membership cases. Direct
finite opponent-coalition expansion over rational data verified that
H(tz)/t - sum sigma_i a e_i P_(i,S)(z) + Gamma z is polynomially divisible
by t. A second expansion put e/t into every nonsingleton residual: the
exact additional field is polynomial in t,z,e and vanishes at e=0.
These finite computations support, rather than substitute for, the general
factor argument above. No fixture coverage conclusion was drawn from them.

## Selected cone, arbitrary residual directions and radial production

For b and B bounding only selected positive columns, a nonzero positive
combination f has each coordinate at least b sum w and total mass at most
nB sum w. Thus every normalized direction is at least b/(nB)=4kappa.
The selected-column assumption is sufficient; the unused inverse columns
need not be nonnegative or have any common sign.

On K, each selected P and coefficient is strictly positive. For rho x,
the output/input mass ratio is a sum of positive coefficients times
rho^(|S|-1). Every exponent is at least one, so one common small inner
radius gives ratio below 1/2 and one common large outer radius gives ratio
above 2. These are uniform directionwise barriers despite mixed degrees.

On the ENTIRE positive compact shell, F_0 has a strictly positive
coordinate minimum, and its normalized directions have the stated strict
distance from the boundary of K. Uniform convergence of the exact signed
perturbation therefore preserves positivity, normalization into K and
both radial barriers. This avoids the false assertion that arbitrary
signed error directions belong to the selected cone: they need only be
small relative to its fixed interior margin.

The fixed-point map acts on the convex product K times [ell,u], not on
the shell itself. At ell its clipped radius is strictly above ell; at u
it is strictly below u. An interior fixed radius forces output mass rho,
and a fixed direction then gives an actual finite-t fixed point F(z)=z.
No root simplicity, branch continuity or degree orientation is needed.

I inspected `Math.exists_fixedPoint_of_normalized_radial_map` in
`MathUE/Topology/NormalizedRadialFixedPoint.lean`. Its radius update differs
from the packet's equivalent update. The packet's outer mass inequality
excludes every outer scaled eigenpoint with scale at most one, exactly
the hypothesis of that existing helper. The ordinary proof is also complete
without invoking the helper as an unproved black box.

## Scale-thick and compact-parameter quantifiers

The exact residual contribution is linear in raw residuals. For a
nonsingleton residual c, its contribution to H/t has a factor at least t,
so setting e=tc leaves a polynomial perturbation continuous at t=0,
linear in e. Consequently |c|≤eta/t is a fixed small error box in e,
not an illicit compactness claim about unbounded c. Choosing eta first
from the strict shell margins, then t small for the remaining fixed
singleton and pole-cancellation errors, proves the scale-thick assertion.
For selected pairs this changes the leading coefficient slightly; the
same strict margins, with eta chosen small, handle that case.

On a compact parameter subset inside the stated strict hypotheses,
selected inverse entries and coefficients have common positive minima,
matrix inverses and singleton rows have common finite bounds, and J and
its signs are fixed. Hence common cone, radii, perturbation bounds and
threshold exist. No uniformity near vanishing selected entries or
coefficients, singular matrices, changing J or changing player count
was used. Bounded singleton rows are explicitly retained here; they
cannot be omitted from an otherwise compact comparison-matrix claim.

## Complete agency and fixed-payoff consumer

All produced hazards are strictly between zero and one, and n≥2. Thus
every deleted-opponent continuation probability alpha_i is below one.
The exact equation H_i=0 gives Q_i=B_i/(1-alpha_i)=V_i. The actual
stationary recursion has this same unique value V_i.

Deadline h has value V_i+alpha_i^h(Q_i-V_i)=V_i; Never has value V_i.
Every complete private replacement on the unique live history is a mixture
of those clocks independent of opponents. This covers arbitrary behavioral
replacements, not only stationary perturbations or supported roots.
Signs of rewards and singleton values are irrelevant to this identity.

For each produced table and profile fixed before accuracy, opponents'
geometric stopping gives a finite expected absorption-time bound uniform
over the entire deviation class. The stated 2C/[N(1-alpha_i)] bound is
sufficient for prescribed delivery and comparison. It need not be uniform
as L or the table changes. Therefore the same actual payoff is a valid
uniform-equilibrium target.

The endpoint implications agree with the inspected declarations
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
No raw-table instance of the new producer is asserted Lean-checked.

## Small negative test and remaining boundary

With three-player Gamma having every off-diagonal entry -1, and only
recipient 0's containing pair selected, the unselected coordinate 1
has leading equation (Gamma z)_1=0. It equals -z_0-z_2<0 at every positive
z, so no positive bounded-z leading root exists. Compactness of any
claimed fixed positive shell would pass an actual sequence to that
impossible root. This correctly falsifies dropping the column hypothesis
for this diffuse all-interior mechanism, not UE existence for that game.

The new selected-cone step is sound under its hypotheses. Whether the
later literal four-player fixture supplies genuinely new raw-table
coverage is outside this review. The conjecture-facing input restriction
still includes invertibility, selected strict signed-column positivity
and the designated large-reward scaling; these are not produced from an
arbitrary finite quitting table by this argument.
