# Independent adversarial review: weighted collision dominance

Reviewer: MINIMUM_BEST_RESPONSE.

## Artifact and verdict

Reviewed the ENTIRE585-line packet WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md,
“Weighted collision dominance produces stationary uniform equilibria”,
at SHA256
`2bf6944fe0f6d42de865fd8cb2e4647b42eb5aa8312a512e38572a95be24fe5a`.

**PASS: complete raw-data producer, explicit sufficient constants,
proper active sets and strict outside guards, simultaneous participant
and passive poles, mixed coalition sizes,
all coefficient-support boundaries, unrestricted behavioral consumer,
fixed target, and the stated complete coverage comparison. No mathematical
objection remains.** This is ordinary mathematical approval of these exact
bytes, not a Lean verification.

The proof is self-contained. It correctly attributes radial Brouwer and
mixed coalition-size scaling as existing mechanisms. Its increment is the
partial signed-column hypothesis, arbitrary numbers of poles per recipient,
passive poles, coefficient support-switch boundaries, and a uniform weighted
dominance collar. It does not claim that stationary existence itself or
the radial fixed-point method is new.

## Exact theorem and strategic production

For any finite n>=2, choose an active set S of size m>=2 with invertible
Gamma_SS, a nonempty recipient set J subset S and signs sigma_i with
v_i=sigma_i Gamma_SS^(-1)e_i strictly positive and Gamma_TS v_i strictly
positive for inactive set T. The full Gamma may be singular. Favorable
positions require D subset S. For each coalition of size k>=2,
the scale is the(k-1)st root of the oriented native reward. Favorable
orientation is sigma_i for a participant and -sigma_i for a passive
recipient. Unfavorable signs and every coordinate outside the favorable
positions are included in B.

The conclusion is uniform over every raw table satisfying G>=L0 and
B<=cG, where L0,c depend only on the chosen singleton and support data. No continuation,
limiting root, response optimizer or nondegeneracy hypothesis is supplied.
The theorem produces active hazards strictly in(0,1), zero inactive
hazards, an exact terminal Nash
against all behavioral replacements, and the one same-profile uniform
payoff. Own singleton levels are arbitrary independently.

## Exact algebra and scale audit

I independently derived the contribution of every collision coordinate to
F_i=(1-H_i)Q_i-P_i. With q=t z and a coalition of size k, a participant
term has k-1 opponent factors plus the factor1-H_i; a passive term has
k opponent factors. In both cases reward scaling t^(-(k-1)) leaves an
order-t contribution to F. Division by t therefore has no negative power.

The participant leading polynomial is
(sum_(j!=i)z_j) product_(j in D\{i})z_j; the passive leading polynomial
is product_(j in D)z_j. The passive sign reverses because its contribution
is -P_i. The definitions of A and E reconstruct the original signed
collision reward exactly, including sigma_i=-1. Singleton passive terms
give -Gamma z at t=0, and native own singleton is zero.

For proper support, I separately checked the inactive-recipient expansion.
An inactive participant coordinate with D\{i} subset S still has exactly
|D|-1 active opponent factors and the additional1-H_i factor. If any
other inactive label occurs, the term vanishes. Passive terms vanish
unless D subset S. Thus no bad coefficient introduces a negative t power.
The inactive singleton term is -Gamma_TS z; all its collision terms are
small E errors, not unpriced favorable poles.

The coefficient bound is also exact: B<=cG with c<=1 gives
|E_iD|<=c^(k-1)<=c. At least one favorable A_iD equals1; all others
lie in[0,1]. After multiplication by Gamma_SS inverse, the exact active equation is
z=T_A(z)+E_t(z), with T_A a positive combination of the selected signed
strict columns and error bounded by C0 t+CE||E||.

As a separate falsification check, symbolic rational polynomial expansion
verified all188 oriented participant/passive coordinate positions for
n=2,3,4,5. Every leading term matched the displayed polynomial, and no
negative t power remained. This finite test supports, but does not replace,
the general algebraic derivation above. A further exact symbolic check
verified cancellation for all1000 nonzero active/inactive collision
positions across proper supports at n=3,4,5. No numerical root search was used.

## Cone, explicit constants, and Brouwer

The normalization w_i=v_i/s_i has a common positive coordinate lower bound
eta. The normalized T_A image lies in their convex hull, with every
coordinate at least eta. Thus K with floor eta/2 is a compact convex
simplex section with a strict image margin. For proper S, the extra linear
conditions Gamma_TS x>=gamma_out/2 preserve compact convexity and contain
every normalized selected column. Their positive margins are supplied
by the raw outside-column inequalities, not by an assumed outsider cap.

On K the common monomial bound m_-=(eta/2)^m is valid for BOTH kinds of
terms: each favorable leading polynomial has degree k<=m, and its factors are
positive; the participant sum is at least eta/2. The upper bound1 is
valid because the total coordinate sum is1. For rho<=1, every degree is
at least2 and the total mass is at most N s_+ rho^2. For rho>=1, one
A_iD=1 gives total mass at least s_-m_-rho^2. These prove the uniform
inner and outer radial barriers without a common degree.

The explicit rho_-,rho_+,gamma0 choices satisfy the claimed stronger
barriers. The annular sum is bounded below by gamma0 because all degrees
lie between2 and m. Perturbations of size delta keep each numerator at
least3eta/4 times its old sum and the new sum at most5/4 times that sum;
normalized coordinates are therefore at least3eta/5>eta/2. The radial
margins remain strict as well. I checked the additional normalization
estimate: perturbing the vector by delta changes its normalized vector
by at most2(m+1)delta/H in sup norm. Multiplying by the outside row norm
M_out and using the new delta bound changes every outside inequality by
at most gamma_out/4. Thus the angular outside constraints remain strict.

For rational Gamma all stated constants can be obtained by finite rational
arithmetic. Bounding coefficients of the finite polynomials after factoring
out t gives C0 and the total CE. The displayed t0,c make the error at most
delta/2 and ensure t0 rho_+<=1/2. No hidden collision-reward bound or
selected root enters these constants.
The additional D0,DE bounds cover every inactive-row polynomial. The
tau restrictions in both c and t0 make their combined error at most
tau/2, as required for the strict quiet comparison.

The clipped radial Brouwer map is a continuous self-map of the compact
convex product. At the inner radius S<rho forces its radial output
strictly upward, and at the outer radius S>rho forces it downward.
Consequently a fixed point is interior in radius, has S=rho, and satisfies
z=T(z) exactly. All its coordinates have a positive lower bound and its
scaled active hazards lie below1. The outside polynomial bound
||R_T||<=tau/2 with tau=rho_-gamma_out/4 gives
F_T/t<=-rho_-gamma_out/2+tau/2<0. This supplies the quiet-player
inequalities in the actual finite table. Degeneracies and changes in which coefficient
is maximal do not impair this argument.

For compact varying singleton data, principal matrix inversion and the
finitely many signed column entries have common bounds, including positive
eta and gamma_out. The same polynomial construction gives uniform
constants. The angular set itself may vary with Gamma; its common margins
suffice. No such uniformity is claimed when the selected principal matrix
becomes singular or a required strict column/outside inequality vanishes.

## Complete agency and fixed target

All players have a proper opponent because |S|>=2, so H_i<1 even for an
active deviator. Put U_i=P_i/(1-H_i). Active equations give Q_i=U_i;
inactive inequalities give Q_i<=U_i. Every finite forced deadline pays
at most U_i and literal Never pays exactly U_i. An arbitrary behavioral
replacement is a mixture of these stopping responses on the unique live
history, so this is the full unilateral cap. Active owners mix only
indifferent actions, while inactive owners Never; their actual prescribed
stationary payoff is U_i in both cases.

Absorption occurs almost surely after every unilateral replacement.
Adding kappa_i to every nonempty native reward therefore adds exactly
kappa_i to both prescribed payoff and every response value. The
opponents-only geometric clock gives a finite expected absorption time
uniformly over replacements, yielding the stated O(1/T) terminal/horizon
comparison. The actual target is kappa+U; both target and stationary
profile are fixed before accuracy.

The necessary asymptotic constraint is thus valid for each fixed active
support and signed-column choice on its compact strict singleton set:
every counterexample with G>=L0 must have
B>cG. This removes the whole favorable projective face and a collar, not
just its strictly positive coefficient interior.

## Complete separating-family review

I checked the full original table and the exact native scales

    G=max(23,sqrt(L^2-4),(L^3-4)^(1/3)), B=22.

For L>=2, G>=L/2. Hence the displayed large-L sufficient bound follows.
The growing triple and grand coordinates belong to recipient0, whose
inverse column is strictly positive; other inverse columns have mixed
signs, so a wholly positive-inverse assumption is unavailable.

The sure-owner exclusion was checked for ALL four choices. If1 is sure,
player2 is forced quiet before checking0; if2 is sure, player3 is forced
quiet before checking0. These implications remove both new poles. If0
or3 is sure, their nonsuccessors are directly quiet. In every case the
successor then quits surely for a gain20, and the original sure owner
prefers Continue to its payoff-1. This is independent of continuation
values and covers mixed and multiple-sure supports as well.

For every proper child, the cycle supplies a player whose successor is
outside. The specified solo child equilibrium is full behavioral Nash;
a unilateral deviation can form only a pair, so neither new pole affects
the proof. Its missing successor gains20 with zero child debt and Never
mass. This excludes the stated UNIVERSAL outsider-gain bounds, not an
unstated assertion that every child equilibrium is unsafe.

The complete ordered-anchor test reduces to the full block by predecessor
closure, then fails by multiplying all four strict pair inequalities.
The nonnegative-weight upper-average expression is positive for every
nonzero weight. The two new recipient0 positive coordinates still require
player3, so the full cycle remains the only premium trap. Pair comparisons
for every partner choice, all three partitions, and the unique attached
negative-pair labeling are unchanged.

I recomputed the singleton determinant and inverse exactly. I also
independently enumerated every nonempty principal support for the LCP at
offset1. The only support with all-positive active coordinates is13; it
has the stated omitted row2 residual-1/3. Every other support has a
nonpositive active coordinate. Singleton support cannot satisfy its active
equation. The empty root has strict residual and index+1, so the degree
claim uses the complete actual-root census with the correct sign convention.

One coverage ambiguity was identified and repaired before this pin.
Rigidity of relabelings preserving this particular Gamma would not by
itself exclude a variable-singleton core theorem. The final packet adds
the stronger direct test: EVERY recipient has a positive native participant
pair, respectively23,21,22,18. Thus no relabeling can supply a recipient
with the seven nonpositive participant caps required by those core
families, even when their singleton matrix varies.

## Nonredundancy, sources, and limits

I read the arbitrary-player and mixed-size sections of the existing
POSITIVE_INVERSE_COALITION_JACKPOTS_UNIFORM_EQUILIBRIUM result. That proof
already has the radial clipped Brouwer mechanism and differing coalition
degrees, but assumes the whole inverse is positive and one selected
participant coordinate per recipient. The packet correctly distinguishes
the new hypotheses from that existing mechanism.

For the separating ray, selecting the triple pole leaves a grand reward
of order L^3 outside every fixed residual O(L) box; selecting the grand
pole leaves a triple reward of order L^2 outside that box. No other entry
grows, and neither growing coordinate is passive. This is a valid
asymptotic comparison with the complete stated one-pole and boundary-column
regions; it is not a claim to decide membership in every unspecified
local threshold or neighborhood. Combined with the explicit other selector
failures, it supplies a previously unproduced raw existence class.

The cited stationary compiler declarations and
`exists_finset_r0Degree_eq_sum_sign_det` were inspected in their tracked
source files. The fixed-point, endpoint Nash, and deleted-opponent
contraction hypotheses are all supplied here. No Lean build was run.

The complete packet passes the export gate as a raw class exclusion with
an actual-data adapter and full consumer. It does not eliminate either
global-minimum branch, handle all unfavorable dominant directions, provide
uniform bounds on singleton-boundary limits, or solve arbitrary Fin4.

## Proper-support scope checks

I independently recomputed both examples in Section7.6. For S=023 the
principal inverse is the displayed positive matrix and its outside row
is(-3,6,2)/5. Choosing only recipient columns2,3 therefore gives strictly
positive outside images even though the full outside row fails the
complete nonnegative-child selector. Both corresponding full inverse
columns are mixed-sign. For S=123, the negative signed column at recipient2
is(3/8,3/4,1/4), with outside image9/8>0. The final theorem therefore
includes the stated negative participant and positive passive pole signs.

These proper-support additions received a fresh full audit. Approval of
the earlier full-support draft was not inherited. The retained review
pins only the final expanded artifact above and supersedes that draft's
review text.

## Final finite-atlas addition

The final Section6.1 received a separate exact check. Zero-diagonal principal
blocks of size1 are singular; inverse columns of nonsingular size2 blocks
each have a zero coordinate. Thus only the four triples and full set can
pass strict positivity. Each inverse column has at most one admissible sign.
Enumerating all nonempty subsets of admissible recipients gives at most
4(2^3-1)+(2^4-1)=43 tests, with the outside guards included before enumeration.

For a maximal favorable magnitude g of degree d, comparison with g' of
degree d' is g^(d')>=(g')^d. The bad-coordinate inequality is exactly
b^d<=c^(d d')g^(d'). Together with g>=L0^d, these are rational comparisons
at rational input. The finite rational formulas, absolute values, maxima
and minima for the constants make these regions semialgebraic after the
finite sign choices. The count does not assert exhaustive coverage; the
packet explicitly preserves failed strict tests and the atlas complement
as unresolved. The final585-line bytes, including this addition, pass the
whole-artifact review; the earlier548-line pin is superseded.
