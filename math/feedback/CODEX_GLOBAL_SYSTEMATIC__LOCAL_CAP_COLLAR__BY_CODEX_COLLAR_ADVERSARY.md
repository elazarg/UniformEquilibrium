# Adversarial review of the signed local cap collar

Reviewer: CODEX_COLLAR_ADVERSARY.

**Mathematical verdict: PASS.** No unresolved mathematical objection remains
in the signed-pair theorem, its semantic-closure conclusions or its strict
nonredundancy example. No other review was read. This is ordinary mathematics;
no Lean command ran and no new Lean theorem or UE existence class is claimed.

Reviewed artifact:
[CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR.md](../notes/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR.md).
Exact SHA256:

    0a579ac7f2a3b06fd74daad481637c84f844ed21623bbd865556ce40926d1406

## Exact accepted claim

Own-singleton, live and Never rewards are zero. A probability weight z with
support S satisfies strictly positive weighted singleton and participant-pair
drifts, z*Gamma>=gamma*1 and z*J>=mu*1. The supported forced-Quit polynomials
have no common nonpositive point except q=0. Individual pairs and full caps
may have either sign. Every actual independent stopping-law profile then has

    max_(i in S) B_i >= delta * Pr(absorption), delta>0.

Every actual absorbing profile has supported maximum strictly above delta;
its semantic closure has maximum at least delta. The augmented closure
retaining Never masses has only the AllNever tuple at supported maximum zero.
No Nash, observer, global-minimum or realization hypothesis is imposed.

The calibration excludes its B0=B1=B3=0 face for the full stated premium
range. The signed example and nearby tables exclude the all-zero face and
strictly extend both earlier tests. Other boundary faces, actual partial-Nash
minima and arbitrary Fin4 remain open.

## Independent signed proof audit

The collision estimates are valid without participant signs. Replacing
singleton-opponent event probabilities by q_j costs at most M*s squared;
multiple-opponent events cost at most M*s squared/2. Thus the two linear
expansion errors are at most 3M*s squared/2. The stated rho implies

    zQ>=kappa*s, zP>=gamma*s/2, Q_i>=-M*s, |P_i|<=M*s.

Root isolation gives a strictly positive minimum of max_S Q_i outside the
rho ball. Thus b=max_S B_i<=eta forces s<rho, including possible sure roots.
Every supported cap need not be nonnegative. Instead the weighted negative
part is at most M*s, which gives

    w=zB>=kappa*s>=0,
    sum_i z_i*|B_i|<=C*w,
    B_i<=A*w for i in S.

The last bound divides only by positive supported weights; sparse weights
cause no missing coordinate condition. The inequality B_i>=-M*w/kappa
also holds outside S, but the upper bound A*w is used only inside S.

The exact complete-response recursion is
B_i=max(Q_i,P_i+H_i*B_i^+). Conditioning independent stopping laws on
survival preserves independence; s<1/4 ensures each conditional law exists.
Suprema need not be attained. Since B_i+M*s>=0 and H_i>=1/2,

    B_i^+ <= 2(B_i+M*s) <= K*w <= eta, i in S.

The local estimates therefore apply afresh to the actual tail. Writing
v=zB^+, they give v>=0 and sum z_i*|B_i^+|<=C*v. The signed transport bound

    sum z_i*H_i*B_i^+ >= v-s*sum z_i*|B_i^+|

is valid for negative as well as positive tail caps. Hence

    w>=gamma*s/2+(1-C*s)*v,
    w-v>=s*(gamma/2-C*w)/(1-C*s)>=gamma*s/4.

Here C*s<=1/2 and w<=gamma/(4C). The invariant is supported maximum<=eta
and weighted cap<=delta. The maximum is not asserted to decrease or stay
below delta; the tail upper bound and weighted decrease together close the
bootstrap. All displayed constants are positive and supply the needed bounds.

Summing gives total conditional hazard at most 4w_initial/gamma. Product
survival and the union bound imply 1-nu<=4b/gamma. Small b thus implies
nu>=1/2; large b gives the global estimate directly. No bounded support,
finite period or eventual absorption is assumed. Coordinate inequalities
pass continuously to the stated closures.

For any deviation, the payoff is zero when every opponent chooses Never;
its absolute magnitude otherwise is at most M. Opponent non-Never probability
is at most 1-nu for the prescribed profile. Thus |B_i| and |U_i| are bounded
by M*(1-nu). This verifies the AllNever conclusion even for signed caps.

## Strict signed example and robustness

Exact symbolic checks reproduced all four Quit factorizations from the raw
participant formula, by expanding every opponent coalition. Their positive
second factors reduce root isolation to two cyclic inequalities with products
6/7 and 3/5, forcing every q_i=0. Exact rational multiplication gives

    z*Gamma=(16,23,2,10)/30,
    z*J=(1/20,1/30,3/50,1/210).

Every row has a negative previous-neighbor pair, so no nonempty support
passes the former individual-positive-pair hypothesis. I independently
reconstructed the four coalition vectors and verified their weighted sum
is (-166,-166,-166,-166). Therefore the displayed positive combination
of global tests is -166 for every probability weight, including sparse ones.
No alternative global weight can pass; positive singleton drift is not
needed for this impossibility.

The open-family conclusion is justified. Strict zJ controls all sufficiently
small nonzero roots uniformly under small participant perturbations; on the
remaining compact cube, max_i Q_i has a strictly positive minimum. The drift,
negative pair in each row and negative certificate coefficients persist.
All participant coordinates may vary independently near the example, and
passive nonsingleton coordinates are arbitrary finite values. The latter
alter numerical constants, not the structural tests. Positive original own
levels add the missing free dimensions, giving the stated open original-table
family without preserving the factorized participant formula.

## Calibration, bridge and source correspondence

The calibration weight gives z*Gamma=(6,11,6,6)/24. Positive supported pairs
imply zJ>0, and the positive row0 anchor proves root isolation on the whole
cube. Negative caps outside the collar are allowed. The retained global-test
contradiction quantifies over every weight: v1<epsilon/2, v3<epsilon,
v0<3epsilon/2 and v2<9epsilon/4 would sum to less than 21epsilon/4<1.
Arbitrary finite passive rewards and the stated free participant entries
remain admissible under the anchor and pair tests.

For each ell_i>=0, every finite deadline absorbs surely and adds exactly
ell_i to its native offer. Native Never is the bounded limit of finite
deadlines because own native singletons vanish. Original Never adds only
ell_i times opponent absorption, so cannot exceed ell_i+B_i(native).
This proves exact cap translation for every profile; prescribed payoffs
translate by ell_i*(1-nu). On absorbing closures both vectors translate by
ell. Nonnegative ell is essential to this bridge and is explicitly assumed;
literal live and Never payoffs are unchanged.

The all-behavior recursion in
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and the exact
`quittingTerminalSemanticPrefix` / `quittingTerminalSemanticPair_rootThenContinuation`
interfaces (`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`)
were inspected statically. Their scopes match the proof. The incoming
boundary source lies in the absorbing carrier, so the excluded faces are
actually unavailable to it, without making its head fully Nash. This is a
boundary reduction, not a UE producer or a closure of the remaining branches.
