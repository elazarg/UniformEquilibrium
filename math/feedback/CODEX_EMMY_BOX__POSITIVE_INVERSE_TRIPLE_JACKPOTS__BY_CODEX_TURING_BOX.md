# Independent adversarial check of the positive-inverse jackpot producer

Reviewer: CODEX_TURING_BOX.

Frozen source: `CODEX_EMMY_BOX__POSITIVE_INVERSE_TRIPLE_JACKPOTS.md`,
whole-file SHA256
`1ae6ab3b39e88ff8b76d5de127caaf7996841337c65820d4652a6f2b1a63a49b`.

Verdict: PASS for Sections1–6 and both exact finite-player extensions in
Sections10.1–10.2. No mathematical objection found. This is independent
ordinary-mathematics checking, not Lean verification or an exhaustive
novelty audit. The already checked four-player fixture/full-agency work
was reused where unchanged; the new radial producer and finite-player
quantifiers were independently reconstructed below.

## Exact scopes checked

For EVERY fixed finite singleton table with invertible zero-diagonal
comparison matrix Gamma and EVERY entry of Gamma^(-1) strictly positive,
select positive jackpot coefficients before the table's scale parameter.
For EVERY finite bounded reward box, all sufficiently large scale
parameters and ALL tables in that box receive actual positive stationary
hazards solving the original, exact finite-scale equations. This holds
uniformly over compact subsets of the strict matrix/coefficient region.
The result supplies exact terminal Nash against unrestricted private
complete clock replacements, and one same-profile fixed uniform payoff.

In arbitrary finite size n≥2, each recipient chooses ONE coalition
containing itself and at least one opponent. Equal opponent counts d
use jackpot scale M and hazards M^(−1/d)z. Mixed counts d_i use jackpot
scales a_i L^(d_i) and common hazards z/L. The original table's finite
scale is fixed before equilibrium accuracy. No statement about arbitrary
tables having these scales is inferred.

## Exact polynomial: recipient and exponent tests

Write D_i=S_i\{i}, d_i=|D_i|≥1, t=1/L and q=t z. Recipient i's sole
unbounded coordinate contributes to its immediate-Quit endpoint exactly

    a_i product_(j in D_i)z_j product_(j notin S_i)(1−t z_j)
      +t^(d_i)c_i product_(j in D_i)z_j
                         product_(j notin S_i)(1−t z_j).

It NEVER appears in its own Continue stopping contribution B_i: the
sampled coalition then omits i. Large coordinates belonging to other
recipients do not enter i's payoff coordinate. This remains true when
different recipients select the SAME coalition or different coalition
sizes. Both B_i and1−alpha_i are polynomially divisible by t. Hence

    H_i/t=a_i[(sum_(j≠i)z_j)product_(j in D_i)z_j]
                 −(Gamma z)_i+t E_i

is an EXACT polynomial identity with the claimed sign. All bounded
nonsingleton data disappear from the leading term, including the
selected coordinate's bounded residual since d_i≥1. Multiplication by
A=Gamma^(-1) therefore gives exactly the stated fixed-point field;
there is no dropped finite-t term or reward-transport approximation.

The condition that S_i contain i is load-bearing. A large passive
recipient coordinate would enter B_i and invalidate the displayed field.
The condition d_i≥1 is also load-bearing: the radial argument below
requires all leading degrees d_i+1 to be at least2.

## Whole-shell positivity and radial fixed point

For any nonzero w≥0, coordinate bounds b≤A_ij≤B give

    (Aw)_i/sum(Aw)≥b/(nB).

Thus the chosen inner simplex with coordinate floor b/(2nB) is genuinely
invariant for EVERY positive image, not merely for a hypothetical root.
It is nonempty because its floor is at most1/(2n).

On its positive compact radial shell every P_i has a strictly positive
minimum. The exact signed polynomial remainder E is bounded over the
ENTIRE shell, small t, and the entire finite bounded reward cube.
Consequently diag(a)P+tE is coordinatewise strictly positive throughout
the shell once one common t0 is chosen. No sign is assumed for E, and
no appeal is made to continuity only at an unknown root.

For equal degree d+1 the mass is rho^(d+1)g(x), giving the two asserted
strict radial barriers. For mixed degrees, every summand
A_ij a_j P_j(x) is positive. With ell<1<u and all d_j+1≥2,

    mass F_0(ell*x)≤ell² g_max<ell/2,
    mass F_0(u*x)≥u² g_min>2u.

This comparison is valid term by term despite loss of common
homogeneity. Uniform continuity preserves both STRICT barriers for the
exact finite-t field. It is not necessary that the same term dominate
at the two radii.

The Brouwer map is on the compact CONVEX product of the direction
simplex and a closed radial interval, not on a nonconvex shell. At the
inner boundary h<ell forces clip(2ell−h)>ell; at the outer boundary
h>u forces clip(2u−h)<u. An interior fixed radius therefore has h=rho,
and the fixed direction implies F(rho*x)=rho*x exactly. Its hazards
are bounded below by t*kappa*ell and above by t*u<1.

The inspected existing declaration
`Math.exists_fixedPoint_of_normalized_radial_map` in
`MathUE/Topology/NormalizedRadialFixedPoint.lean` uses a different but
equivalent radius update. The packet's stronger outer mass inequality
implies that declaration's scaled-eigenpoint exclusion, so this is an
honest use of an existing generic topological operation. The neighboring
`Math.exists_positive_fixedPoint_of_coordinate_radial_bounds` in
`MathUE/Topology/PositiveCoordinateRadialFixedPoint.lean` is also a
conditional generic helper, not this raw reward-table producer.

## Uniform quantifiers and finite-player complete agency

Continuous matrix inversion on a supplied compact subset of the strict
inverse-positive region gives common b>0 and finite B. Positive jackpot
coefficients have a common positive minimum. The singleton coordinates
and all polynomial coefficients are bounded there. Therefore one
direction simplex, one shell, one positive preimage margin, one signed
remainder bound and one t0 work across the ENTIRE parameter set. No
uniformity is claimed near zero inverse entries, zero jackpot ratios,
unbounded reward boxes or changing player counts. Coalition choices are
fixed in the asserted compact-uniform version.

For every produced finite table all q_i are strictly positive and n≥2,
so every player's deleted-opponent continuation probability alpha_i is
strictly below1. From H_i=0 the ACTUAL policy value satisfies

    U_i=Q_i=B_i+alpha_i U_i.

Every finite deadline has value U_i and Never has value
B_i/(1−alpha_i)=U_i. Any complete private law is a mixture of these
deadlines and Never on the sole continuing history. Alternatively the
same Bellman identity gives a bounded residual times alpha_i^N for
every replacing law. This proves unrestricted terminal Nash; it does
not only compare stationary replacements. Finite n changes nothing in
this argument. At n=2 the strict-inverse premise may be empty for a
zero-diagonal comparison matrix; that is harmless and not a hidden
existence assertion for such a matrix.

For each fixed table, its finite reward bound and opponents' finite
geometric expected absorption time yield finite-average/terminal error
O(1/horizon), uniformly over complete deviations. Thus one actual
payoff and the same profile satisfy the fixed uniform target contract.
No threshold uniform in accuracy, unbounded finite-table rewards, or
vanishing deleted absorption is silently needed.

## Falsification and inherited coverage boundary

The sign/exponent tests above include arbitrary signed singleton values,
different coalition sizes, a selected grand coalition, coinciding
coalition choices across recipients, and bounded residuals of either
sign. None produces a failure. Dropping inverse positivity genuinely
breaks this producer: own singleton1 and all other singleton rewards0
give Gamma with negative off-diagonal entries, so every component of
diag(a)P−Gamma z is positive at every positive z. The packet correctly
limits this falsifier to its positive bounded-z scale, not all strategies.

The Section8 four-player separating fixture and whole sure-owner/unsafe
child/crossed-lower/quotient/insertion comparisons coincide with the
previous corrected packet, whose bounded review is in
`CODEX_EMMY_BOX__SPARSE_TRIPLE_COLLISION_PRODUCER__BY_CODEX_TURING_BOX.md`.
In particular the actual mate01 outsider insertion sum is2(M−5), not a
participant-withdrawal sum. These unchanged checks are reused here.

The added constant-positive-inverse odds comparison was checked against
`Math.CrossedMatching.exists_positive_odds_of_positive_inverse` in
`MathUE/LinearProgramming/PositiveInverseTwoPairOdds.lean`: its actual
premise includes nonnegative scheduled participant premiums, in addition
to inverse positivity and nonpositive passive increments. Every pair
in the separating fixture has at least one participant premium−2, so
every scheduled pair partition fails that premise. Strict inverse
positivity alone is not an earlier raw-data conclusion of that theorem.
This is bounded source comparison, not exhaustive novelty or absence
of other equilibria.

No unresolved objection remains in the producer, either finite-player
extension, or the bounded inherited comparisons checked here. The
conjecture-facing restriction still present is the strict inverse-positive
singleton matrix together with selected positive participant jackpots;
the result does not select such structure from arbitrary original tables.

## Final mathematical-scope incorporation check

Final clean source SHA256:
`a65d21c08948494a0d0cf595a943af6c6b49edfc2f4adf26484074d326a29290`.

PASS applies to the final producer and both finite-player extensions.
Their exact polynomial, shell, radial fixed point, all-parameter and
complete-agency arguments are unchanged. The revised Section9 accurately
identifies the existing generic topological and semantic consumers without
claiming a checked raw producer.

The added signed inverse-column comparison states genuine necessary
premises of the named earlier raw source: strict positivity of every
inverse column forces all signs+1, and every pair partition then has a
participant premium−2 violating its signed-premium requirement. These
premises were compared directly with the tracked standalone
`SIGNED_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM.md`. The added singleton-word
argument is the previously checked global positive-hazard uniqueness
proof and its0/1 inactive caps; its final scope remains that named word
and mate-preserving relabelings, not arbitrary calendars or boundary
hazards. No new full audit or exhaustive novelty claim is attached to
this final assembly check, and no incorporation objection remains.
