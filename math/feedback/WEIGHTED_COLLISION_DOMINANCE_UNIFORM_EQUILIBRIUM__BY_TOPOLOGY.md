# Full independent review of weighted collision dominance

Reviewer: MINIMUM_GLOBAL_TOPOLOGY.

## Artifact and verdict

Whole artifact reviewed: `/tmp/WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md`, SHA256
`2bf6944fe0f6d42de865fd8cb2e4647b42eb5aa8312a512e38572a95be24fe5a`.

**PASS** for the complete raw theorem, exact producer, compact-uniform and
computable bounds, unrestricted behavioral and fixed-target consumer, and
conjecture-facing export increment. No unresolved mathematical objection
remains at these bytes. This review includes an attempt to falsify the
separating family by finding a sure-owner equilibrium. The final family
passes that test by a complete finite argument.

This is ordinary mathematical review. No Lean build was run. Arbitrary Fin4,
unfavorable dominant directions and singular singleton boundaries remain open.

## Exact expansion and weighted scales

The normalization changes nonempty rewards only. Original own-singleton
levels cancel in the stationary comparison F=(1-H)Q-P. For a coalition of
size k, multiplying its reward by t^(k-1) is the correct common scale both
for participant and passive occurrences:

- A participant term has k-1 opponent hazards and the additional factor
  (1-H)/t after division of F by t.
- A passive term has k opponent hazards and the minus sign from P.

The displayed eps_iD convention therefore gives the same favorable sign
sigma_i in the two cases. The E decomposition reconstructs every actual
collision reward exactly. There are no residual negative powers of t.
Singleton terms give -Gamma z plus a polynomial divisible by t. The whole
remainder has the asserted form t R0+sum E_iD R_iD.

All favorable coefficients lie in [0,1], and at least one is exactly one.
The bad scale hypothesis gives |E_iD|<=c^(k-1)<=c when c<=1. This handles
arbitrarily different growth rates and changes of the largest coefficient.
No common coalition degree or positive lower bound on every favorable
coefficient is needed.

Multiplication by the principal inverse Gamma_SS inverse gives exactly
z=T_A(z)+E_t(z) on the active coordinates. Each favorable summand is a
positive monomial times a selected signed strictly positive principal column.
Mixed signs in unselected full columns cause no error; the full matrix need
not be invertible. Its outside rows are controlled separately below.

## Uniform cone, radii and explicit constants

After normalizing the selected columns, every unperturbed image direction
has coordinates at least eta, whereas K only requires eta/2. K is nonempty
because eta<=1/m. For x in K each monomial is bounded below by
(eta/2)^m and above by one, including the participant sum factor.

For rho<=1 every degree is at least two, so the upper radial estimate is
linear in rho after division by rho. For rho>=1 the coefficient equal to
one supplies the lower radial estimate. This proves uniform inner
compression and outer expansion throughout the full compact coefficient
face max A=1, including its coordinate-zero strata.

The proposed gamma0=s_- m_- rho_-^m is a valid positive lower bound on total
image mass over the entire annulus. An entrywise perturbation <=delta with
delta<eta gamma/4 preserves positive total mass and leaves normalized
coordinates at least 3eta/5>eta/2. The radial tolerances also preserve strict
inner and outer inequalities. I checked the factors m=|S| in all sum bounds.

The explicit rational choices have sufficient slack. With the displayed
coefficient-sum bounds C0,CE, the final choices of c and t0 make the total
error at most delta/2; t0 rho_+<=1/2. Thus every produced physical hazard is
strictly below one. These constants are computed from finite polynomial
coefficients and rational matrix inversion when Gamma is rational, rather
than from a numerical equilibrium root.

On compact singleton sets with the same signed strict columns, s_-, eta
stay positive, s_+ and inverse norms stay bounded, and polynomial coefficient
bounds stay finite. Every estimate can therefore be chosen uniformly.
No uniformity is claimed at singular matrices or vanishing column entries.

## Proper active sets and outside guards

I checked the expanded theorem as a whole, including its new proper-support
case. Favorable coalitions lie inside S and their recipients lie in S.
Therefore no favorable coefficient enters an inactive payoff row. Its exact
scaled comparison is -Gamma_TS z+R_T. A bad joining reward for an inactive
recipient has |D|-1 active opponent factors and the extra (1-H_i) factor;
its scaled expression is polynomial. A second inactive coalition member
makes the term zero. Passive terms likewise have no negative t power.

The angular set adds the linear constraints Gamma_TS x>=gamma_out/2.
Every normalized selected column satisfies the stronger gamma_out bound,
so K remains nonempty, compact and convex. If the image error is delta,
the normalized-vector error is at most 2(m+1)delta/H. Applying an outside
row costs at most its absolute row sum M_out; the additional delta bound
therefore leaves outside images at least 3gamma_out/4. This explicitly
controls signed outside rows rather than presuming their entries positive.

The separate R_T constants D0,DE and tau=rho_- gamma_out/4 give inactive
comparisons at most -rho_- gamma_out/2+tau/2<0. Thus the same fixed point
supplies the required strict quiet inequalities. When T is empty these
constraints are correctly omitted. Uniform compact constants retain both
positive active directions and positive outside images; no nonsingularity
of the full Gamma is used.

I independently checked the two proper-support examples on the reference
matrix: the 023 inverse and outside row (-3,6,2)/5, and the signed 123
column (3/8,3/4,1/4) with outside image 9/8. Their selected full inverse
columns need not be sign definite. These examples demonstrate actual
additional principal-support scope without altering the full-support
separating family's coverage proof.

## Fixed point and behavioral consumer

The clipped radial map is a continuous self-map of the compact convex
product [rho_-,rho_+] times K. At the inner endpoint its radial output is
strictly larger, and at the outer endpoint strictly smaller. A Brouwer fixed
point is therefore interior in radius and satisfies S(rho x)=rho, hence
z=T(z) exactly. There is no appeal to an isolated root, nonsingular Jacobian,
or a continuous choice among equilibrium branches.

Every active q_i is positive and every inactive hazard is zero. Since
|S|>=2, every player nevertheless has proper opponents, with geometric
success probability 1-H_i>0 independent of that player's replacement.
Writing U_i=P_i/(1-H_i), active equalities give Q_i=U_i and inactive
inequalities give Q_i<U_i. Every finite forced deadline therefore pays at
most U_i; Never pays exactly U_i. Their mixtures cover unrestricted
unilateral behavioral strategies on the unique live history. Every
prescribed positive hazard is indifferent and prescribed play gives U.

Opponent properness justifies adding kappa_i to every prescribed and
deviating terminal payoff; it does not shift literal AllNever by fiat.
The geometric absorption-time bound is uniform over all replacements and
controls terminal versus finite-horizon payoffs. Thus one actual stationary
profile and one target work for every accuracy, with only the horizon
threshold varying. This establishes the stated UE quantifiers.

I inspected the hypotheses of the two stationary endpoint compiler theorems
cited in Section8 and the terminal-to-uniform selection theorem. The produced
root supplies their fixed-point, zero endpoint-regret and deleted-opponent
contraction requirements. These citations are source correspondence, not a
claim that the new raw producer has been formalized.

## Complete separating family

The final family has two favorable poles of different degrees in recipient0:
r0(023)=L^2 and r0(0123)=L^3. Direct native subtraction gives exactly

    G=max(23,sqrt(L^2-4),(L^3-4)^(1/3)), B=22.

Hence its entire sufficiently large-L tail meets the new criterion. Every
other parameter and original own-singleton level is fixed in the comparison.

I checked every sure-owner case. For sure1, owner2 is forced off before
both exceptional row0 rewards become impossible; then owner0 is forced off.
For sure2, owner3 is first forced off, again disabling both exceptions and
forcing owner0 off. Sure0 directly forces1,3 off; sure3 directly forces1,2
off. In each case exactly the stated successor is then forced to Quit by a
strict gain20, and the supposed sure owner prefers withdrawal. The argument
covers all product supports and every continuation vector. It does not merely
check pure profiles or one selected observer equilibrium.

For every proper child, choose a member whose cycle successor is absent.
The stated sure-solo child law is exact against all behavioral deviations,
has zero child debts and joint Never, and gives the absent successor gain20.
The exceptional poles cannot occur under a single child deviation. Thus the
universal child-debt criterion fails for every possible child. This is the
claimed universal-selector exclusion, not a claim about all conceivable
existential child mechanisms.

The anchor comparison forces the first block to be predecessor-closed, hence
all four players. The four necessary weight inequalities multiply to the
false 191268<=625, which I recomputed. The upper-average and full-trap
obstructions also check: the four positive row sums are 13,11,12,8.

I independently recomputed all eleven nontrivial principal determinants,
all active-support candidates -Gamma_CC^-1 1, the inverse matrix and the
one surviving nonnegative proper candidate's omitted residual. They agree
with Section7.4. Every homogeneous nonzero support is excluded, proving R0;
the unique offset-one root is the empty support with positive residual and
index+1. I inspected `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`; its offset and index conventions
match the calculation.

The mixed inverse column rules out all sign choices in the whole-inverse
criteria. The complete triple and pair-partition comparisons, attached-pair
labeling and crossed-face lower-guard failure use unchanged fixed cells.
Every recipient has a strictly positive participant pair, so no relabeling
can satisfy the seven nonpositive participant bounds of the compared
nonstationary singleton/core families.

## Finite atlas and exact comparisons

I checked the added Fin4 atlas as part of the full final artifact. A principal
set of size one is singular. An invertible zero-diagonal 2 by 2 matrix has
zero inverse diagonal, so neither signed column is strictly positive. Thus
only the four triples and the full set qualify. Each column has at most one
admissible sign; the stated bound 4(2^3-1)+(2^4-1)=43 is correct, including
all nonempty selected-column subsets and outside tests.

On each fixed sign/support cell, the explicit constants are finite rational
functions combined with absolute values and finite extrema. Their coefficient
bounds can be computed from the finite polynomial expansion, so the claimed
sufficient regions are semialgebraic. For a maximizing good magnitude g of
degree d, comparison with degree-d' magnitude g' uses g^(d') versus (g')^d.
The bad comparison b^(1/d')<=c g^(1/d) is exactly
b^d<=c^(d d')g^(d'). No root approximation is needed at rational inputs.
Discarding singular/failed strict tests and retaining an unresolved complement
is faithful to the proved coverage. Forty-three sufficient tests do not
constitute a proof that all forty-three or their complement close Fin4.

## Increment and limits

I compared the full-inverse coalition-jackpot theorem, signed passive-coalition
producer, signed one-column jackpot theorem and boundary inverse-column
extension. The first two require all appropriately signed full columns positive;
the full-support separating family fails that hypothesis. The latter two select one participant
pole and allow bounded or O(M^(1/d)) residuals. Selecting the triple here
leaves an L^3 residual outside every fixed O(L) box; selecting the grand pole
leaves an L^2 residual outside every such box. No other growing pole is
available, and there is no growing passive coordinate.

The radial mechanism itself was already used for wholly positive inverses,
and the packet acknowledges this. The new result is the simultaneous selected-principal-column
participant/passive criterion with outside guards, compact coefficient-support
faces, arbitrary relative weighted growth, and a uniform bad-coordinate collar. The complete family above supplies coverage beyond the applicable
prior selectors rather than merely a new conclusion for a supplied root.

Its necessary counterexample condition B>cG applies only above L0 and within
the fixed strict-column singleton domain. It supplies a finite raw asymptotic
exclusion, not an exhaustive partition of all games or a solution to either
global-minimum branch. The artifact states these limits accurately.
