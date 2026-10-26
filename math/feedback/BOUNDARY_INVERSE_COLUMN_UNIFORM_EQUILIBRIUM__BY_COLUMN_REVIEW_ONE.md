# Independent review of the boundary inverse-column producer

Verdict: PASS for the complete stated theorem, including arbitrary bounded
completions, the scale-thick region, the open singleton neighborhood, and
unrestricted behavioral uniform-equilibrium payoffs. No unresolved
mathematical objection remains. This is ordinary mathematics, not new
Lean verification. Arbitrary Fin4 remains open.

Reviewed final artifact: `BOUNDARY_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM.md`,
SHA256 `bf0f1118db106024b6db237f9ceeeccf0ef14679a38f22c35a7ba57ab7ff2e38`.
I reviewed the entire assembled artifact, including the final strengthened
statement and its new proof paragraphs. This verdict follows these bytes
if the file is moved unchanged.

## Exact claim and strategic completeness

At a base singleton matrix Gamma, the theorem assumes a signed nonnegative
inverse column v, a containing selected coalition with P(v)>0, and an
invertible omitted principal inverse block M whose inverse is strictly
semimonotone. The P-matrix alternative is a sufficient finite raw test.
For sufficiently large selected reward magnitude, every bounded completion
has an actual stationary exact terminal Nash equilibrium. The same holds
for a scale-thick nonsingleton box and all sufficiently small independent
perturbations of the original singleton entries. Perturbed inverse columns
need not themselves satisfy the base sign hypothesis.

All inputs concern finite original rewards or finite matrices. No root,
continuation value, strategy, complementary solution, or target is assumed.
The implicit-function step supplies the positive-support variables, Brouwer
supplies the omitted complementary variables, and the endpoint consumer
supplies the actual fixed target and every behavioral deviation bound.
The conclusion is existential uniformly over the raw parameter regions;
it does not assert an explicit numerical large-reward threshold or a
continuous/unique equilibrium selection.

## Independent mathematical audit

I independently derived the exact canceled stationary field, including the
selected participatory pole and the linear term -Gamma z. A nonsingleton
bounded coefficient enters H/t with at least one power of t; the selected
residual enters after scaling with exponent d-1>=0. Thus the scale-thick
substitution is a genuine polynomial parameter extension, not an inference
from bounded-box uniformity.

The leading root and rank-one inverse formula are correct. In particular,
rows of the rank-one correction indexed by the zero set vanish, giving
(J^{-1})_TT=-M. I independently derived the resulting Schur derivative
f_x=M^{-1}. Invertibility of M forces Gamma_SS and J_SS invertible.
The support argument is valid and actually forces at least three positive
base coordinates; in Fin4 the omitted set has exactly one label and the
matrix sign condition becomes a positive omitted inverse diagonal.

The clipped-cube proof uses precisely the needed strict-semimonotone
property. On the nonnegative unit sup sphere the continuous function
max_i x_i(Bx)_i has a positive minimum eta. At a clipped fixed point all
x_i f_i<=0. On the upper boundary the eta estimate and the uniform small
error force one product to be positive, a contradiction. Thus the fixed
point solves unrestricted nonnegative complementarity, with no artificial
upper constraint left active. The same estimate gives x=O(t) for bounded
completions. No P-matrix uniqueness theorem is silently invoked.

I checked the P-matrix sufficient test: the diagonal-perturbation determinant
argument proves sign nonreversal, and complementary principal-minor identities
show that the inverse of a P-matrix is P. This supplies the stated weaker
strict-semimonotone hypothesis without an entrywise positivity assumption.

The open singleton-neighborhood strengthening is valid. Original singleton
perturbations are additional polynomial parameters. The reduced derivative
remains close to B, and the residual at x=0 is O(t+|e|+|delta|), so the same
fixed cube works on one common parameter box. Positive-support coordinates
remain bounded away from zero. The packet correctly restricts the sharper
O(t^2) omitted-hazard asymptotic to fixed base singletons and bounded
residuals. For fixed nonzero singleton perturbation, it only asserts the
weaker O(t+delta) scaled-coordinate estimate.

## Full agency and uniform payoff

At least three base-support hazards remain positive, so every unilateral
replacement faces an independently absorbing opponent. For active players
the endpoint equality gives U=Q; for quiet players H<=0 gives Q<=U, while
Continue equals U. Iterating these inequalities covers every finite deadline,
Never, and arbitrary private behavioral mixtures. Opponent survival is
geometric independently of the deviator's choices, so there is no residual
improper-Never or stationary-only gap.

The original reward field is used throughout; the native notation does not
translate live or Never payoffs. The finite-table reward bound and geometric
opponent absorption bound terminal-versus-horizon payoff error uniformly over
all replacements. One produced stationary profile and its actual terminal
payoff therefore work at every accuracy after a suitable horizon threshold.
The target is fixed for each game before accuracy; no common target is
asserted across changing games.

## Falsification attempts and exact controls

I independently expanded the raw coalition polynomial in Section 7. It gives
exactly E=(25/24,25/576,0,-25b/48-25/24), the displayed active correction,
the reduced coefficient -25b/48, and reduced derivative -5/2. The two signs
b=+1 and b=-1 respectively select quiet and active omitted-label branches.
The active-branch coefficient q3=5t^2/24 is correct.

I checked the exact finite calibration directly: at a=200/39, b=1 and
q=(1/10,1/10,1/4,0), the active endpoint fields vanish; row3 has passive
contribution 9/400 and opponent absorption 157/400. Its terminal value is
9/157, and the active row1 value is 15/13. The stated target is correct.
The general one-parameter H1 and H3 identities also agree with literal
coalition enumeration.

The sign-flipped column control correctly reverses the omitted Schur sign
without changing the restricted active solution. With b=-1 the reduced
field is positive at zero and strictly increasing nearby, ruling out every
nearby nonnegative complementary stationary root. This falsifies an
unrestricted weak-column extension of this mechanism; it does not assert
that the altered game has no other equilibrium.

I independently checked the singleton-perturbation identity. Increasing
Gamma30 by epsilon changes the selected inverse column to
(5,5+epsilon,15-3epsilon,-2epsilon)/(25+3epsilon). For small positive epsilon
it has a negative coordinate, while the open-neighborhood theorem applies.
Thus the robustness clause is stronger than applying the base weak-column
condition to the perturbed matrix.

I also tested possible failures from support size one or two, the sign sigma,
multiple omitted coordinates, non-P strictly-semimonotone matrices, the
scale-thick residual substitution, negative own levels, and a deviation
waiting forever. The proof's explicit hypotheses and estimates address
these cases without adding a strategic assumption.

## Coverage and export gate

The complete four-player table in Section 8 is an actual raw family with
one growing participant reward and all remaining coordinates bounded.
The original Gamma has an unsafe deleted-child inverse row (-3,6,2)/5.
Its recipient1 inverse column has a zero, so the selected growing direction
is outside the preceding strict-column large-reward hypothesis. The unrelated
strict column0 has no growing reward in this ray. The packet does not
pretend to exclude every unspecified implicit-function neighborhood.

I independently audited the cycle completion. For M>14, any sure owner
forces both nonsuccessors to Continue; its successor then strictly joins;
the owner can strictly improve by withdrawing. This excludes all product
sure-owner roots against every continuation. Every proper child has the
stated exact one-quitter child Nash with zero debt/Never mass and a strictly
profitable outside successor. These are full-source arguments, not just
failures of one selected witness or one pointwise certificate.

The positive singleton graph forces the entire marked set. The directed
cycle forces its first ordered block to contain all labels; multiplying
the four positive-weight pair inequalities is impossible. The four
supportwise singleton upper averages sum to the stated strictly positive
linear form, excluding every nonnegative weight choice and the full-trap
singleton upper-charge test. I checked the three pair-partition failures,
all crossed partner choices, unique attached-pair labeling, mixed-sign
inverse column, intersecting signed-pair geometry, and complete deleted
principal-inverse choice.

I recomputed every principal determinant and every vector in the LCP census.
The only feasible root at offset ones is the empty support; its index is +1.
All nontrivial homogeneous supports are excluded as stated, so the actual
R0 degree is +1. Thus the nonunit-degree exit does not already solve this
singleton table. The family is not a claimed counterexample; the new
producer constructs its stationary equilibria for sufficiently large M.

These complete comparisons establish a genuine raw existence-class
increment among the specified implemented and accepted mechanisms. The
result generalizes the strict-column producer through a previously missing
boundary and then to an open singleton neighborhood; it is not merely a
stronger strategy conclusion on the earlier fixed K=100 collision family.
There is no remaining strategic input requiring a conditional exception.

## Source correspondence and handoff

I inspected the actual declarations
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`, and
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`.
The produced fixed point, endpoint comparisons, opponent contraction,
regular offset, and complete root census match their hypotheses.
No Lean commands were run and no new L/A/C evidence is asserted.

The packet is self-contained: matrix lemmas, local complementarity existence,
raw fixtures, boundary controls and full consumer are supplied. The new
formalization obligations are the polynomial cancellation and rank-one
identities, parameter IFT, clipped-cube complementarity lemma, and their
raw-data adapter. The existing stationary endpoint consumer is appropriate.
The artifact passes the mathematical export gate, subject to the required
second independent full review and ordinary final repository checks.
