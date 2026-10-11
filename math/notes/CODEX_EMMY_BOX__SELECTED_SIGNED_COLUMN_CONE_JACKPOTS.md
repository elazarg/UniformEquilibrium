# Selected signed inverse columns and coalition reward poles

Status: COMPLETE ORDINARY PROOF DRAFT, with a bounded independent soundness
PASS on Sections1–5 and the initial negative test. The later four-player
fixture and whole-source coverage claims remain unreviewed. Not Lean checked,
not exported. This is a global raw-table producer, not a supplied
root verifier. It requires strict positivity only in the inverse columns
carrying large rewards. Other columns can have arbitrary signs. A degree-one
two-column fixture and bounded whole-source comparisons are given below;
their admission significance is not claimed before independent checking.

## 1. Raw inputs and actual-game conclusion

Let I be finite with n>=2. The first nonempty quitting coalition S absorbs
at a finite vector r(S). Live dates and Never pay0. All randomization is
private and independent. Deviations are arbitrary complete behavioral
replacements, including every finite deadline and Never; payoffs are expected.

Fix arbitrary singleton rows and write s_i=r_i({i}), Gamma_ii=0 and
Gamma_ij=r_i({j})-s_i for i!=j. Assume Gamma is invertible. Let J be ANY
nonempty finite set of recipient/coalition coordinates (i,S), with |S|>=2.
Write A for its recipient projection. For every i in A choose sigma_i in
{-1,1}, and require ONLY

    v_i=sigma_i*Gamma^-1*e_i >0 in EVERY coordinate.          (1)

No condition is imposed on the other columns of Gamma^-1. Choose arbitrary
positive a_(i,S) for (i,S) in J and set

    d_(i,S)=|S|-1>=1,
    epsilon_(i,S)=+1 if i belongs to S, -1 otherwise.

For every finite residual bound R there is L0 such that EVERY L>L0 and
EVERY raw table with the fixed singleton rows and

    r_i(S)=epsilon_(i,S)*sigma_i*a_(i,S)*L^d_(i,S)+c_(i,S)
                  at (i,S) in J,          |c_(i,S)|<=R,
    |r_i(S)|<=R at EVERY unselected nonsingleton coordinate              (2)

has an actual ALL-interior stationary terminal Nash equilibrium against
every complete behavioral replacement. Its hazards are q=z/L, with z in
a fixed compact subset of the positive orthant, independent of L and all
bounded residuals. The SAME profile supplies a uniform-equilibrium payoff
equal to its actual terminal payoff.

No limiting root, continuation target, nondegenerate Jacobian, strategic
witness, degree condition or own-singleton sign is an input. There can be
several selected coalitions for one recipient, arbitrary mixed sizes, and
both containing and absent-recipient poles. This changes a reward class;
it does not alter the rewards of a fixed arbitrary conjecture input.

The threshold is uniform on compact parameter sets preserving invertibility,
(1), positive a, and bounded singleton rows. The finite set J and signs are
fixed. Uniformity does not extend to a selected column entry or coefficient
approaching0, or to singular Gamma.

## 2. Exact cancellation, including absent recipients

For stationary opponent hazards q_-i let

    alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(B union{i})],
    B_i=E[r_i(B)*1_(B nonempty)],
    H_i=(1-alpha_i)*Q_i-B_i.

B in these expectations is the independently drawn opponent coalition.
Define one positive homogeneous polynomial per selected coordinate:

    P_(i,S)(z)=(sum_(j!=i)z_j)*product_(j in S\{i})z_j,
                                              if i belongs to S;
    P_(i,S)(z)=product_(j in S)z_j,             if i is absent from S.

Both have degree |S|=d_(i,S)+1>=2 and are strictly positive when z>0.
Put t=1/L and q=t*z. There is an EXACT polynomial remainder E such that

    H(t*z)/t = sum_((i,S) in J) sigma_i*a_(i,S)*e_i*P_(i,S)(z)
                         -Gamma*z+t*E(t,z,c).                (3)

The bounded singleton contribution at t=0 is-Gamma*z. A containing pole
enters only Q_i: its exact canceled factor is

    sigma_i*a_(i,S)*[(1-alpha_i(t*z))/t]
      *product_(j in S\{i})z_j*product_(j notin S)(1-t*z_j).

An absent-recipient pole enters only-B_i, and epsilon=-1 cancels that minus
sign. Its exact factor is

    sigma_i*a_(i,S)*product_(j in S)z_j
                       *product_(j notin S, j!=i)(1-t*z_j).

The raw power t^(-(|S|-1)) has therefore completely canceled in both cases.
All other nonsingleton terms have a remaining factor t after division by t.
Multiple selected coordinates for the same recipient add linearly; they do
not create cross-products of reward coefficients. On fixed compact z sets
E is uniformly bounded over every bounded residual box.

Define the exact continuous fixed-point field

    F_(t,c)(z)=sum_((i,S) in J) v_i*a_(i,S)*P_(i,S)(z)
                                      +t*Gamma^-1*E(t,z,c).   (4)

A fixed point of(4) is equivalent to H(t*z)=0, without multiplying by any
hazard coordinate or discarding an inactive equation.

## 3. A uniform direction cone and mixed-degree radial barriers

Let b be the smallest entry and B the largest entry among the SELECTED
positive vectors v_i, i in A. Put

    kappa=b/(4*n*B),
    K={x>=kappa coordinatewise: sum_j x_j=1}.

This compact convex simplex is nonempty because kappa<=1/(4n). For every
nonnegative nonzero family w_(i,S), the vector f=sum v_i*w_(i,S) has

    f_j/sum_k f_k >= b/(n*B)=4*kappa.                        (5)

Thus every normalized positive cone image lies strictly inside K. For
x in K define

    C_(i,S)(x)=a_(i,S)*(sum_j(v_i)_j)*P_(i,S)(x)>0.

These finitely many continuous positive functions have strictly positive
minima and finite maxima on K. By homogeneity,

    sum_j F_0(rho*x)_j /rho
          =sum_((i,S) in J) C_(i,S)(x)*rho^d_(i,S).           (6)

Since EVERY d>=1, choose 0<ell<u with the right side <1/2 at rho=ell
and >2 at rho=u, uniformly over x in K. The shell

    Z={rho*x: x in K, ell<=rho<=u}

is compact and lies strictly in the positive orthant. F_0 has a positive
minimum in every coordinate on Z, and its normalized directions have the
strict margin in(5).

Uniform convergence in(4), over the WHOLE shell and bounded residual box,
therefore gives for every sufficiently small positive t

    F_(t,c)(z)>0,           F_(t,c)(z)/sum F_(t,c)(z) in K,
    sum F_(t,c)(ell*x)<ell, sum F_(t,c)(u*x)>u               (7)

for all x in K and all residual c. This uses proximity to an interior cone,
NOT positivity of Gamma^-1 on unselected signed error coordinates. Those
columns may be negative or mixed; their exact perturbation is still small.
Choose the same t threshold so that t*u<1.

## 4. Global joint production without root regularity

Fix an allowed t,c, and let f=F_(t,c)(rho*x), h=sum f>0. The continuous map

    (x,rho) |-> (f/h, clip_[ell,u](2*rho-h))                 (8)

takes K times[ell,u] to itself by(7). Brouwer gives a fixed point. It cannot
have rho=ell: then h<ell, so the clipped value of2ell-h is strictly ABOVE
ell. Nor can rho=u: h>u makes the clipped value strictly BELOW u. At an
interior fixed radius, clip(2rho-h)=rho forces h=rho. The direction equality
then gives f=rho*x. Thus z=rho*x is an ACTUAL fixed point of(4), with

    kappa*ell <= z_j <= u,
    0<t*kappa*ell <= q_j=t*z_j <1 for EVERY j.                (9)

This proves the raw quantifiers in Section1. No selected zero, simple root,
continuation of a root, positive degree, or convexity of the independent-law
image was used. Compact-parameter uniformity follows by choosing common b,B,
shell radii and polynomial bounds under the hypotheses stated there.

### Scale-thick residuals

There is also a fixed eta>0 such that the same conclusion holds with EVERY
unselected nonsingleton coordinate and EVERY selected residual bounded by
eta*L instead of a fixed R, for all sufficiently large L. To see this, the
bounded-residual contribution in(3) is linear in c. Write e=t*c. Then the
exact perturbation in(4) is a continuous sum linear in e plus a singleton
term tending to0 with t. Choose eta so its norm on Z is smaller than the
strict cone and radial margins in(7). Then choose t small for the remaining
singleton term. No unbounded residual parameter is put into a compact set.
For selected pair poles this allows a small relative coefficient change;
positivity is retained by the same strict-margin argument.

## 5. Complete terminal agency and a fixed uniform payoff

Every produced profile has all hazards positive, so alpha_i<1 for every
i. Since H_i=0, write V_i=B_i/(1-alpha_i)=Q_i. The actual stationary policy
payoff is also V_i: its one-step recursion is

    U_i=q_i*Q_i+(1-q_i)*(B_i+alpha_i*U_i).

Every finite deadline h earns V_i+alpha_i^h*(Q_i-V_i)=V_i; Never earns V_i.
Any complete behavioral replacement on the unique live history is a private
mixture of those deadline/Never laws, independent of its opponents, and also
earns V_i. Thus terminal Nash is against ALL unrestricted replacements,
not only the stationary menu. Neither raw reward signs nor payoff signs
are restricted in this step.

For the fixed finite table let C bound all terminal reward magnitudes.
Every replacement still faces independently terminating opponents with
geometric survival alpha_i^h. Its terminal/finite-average discrepancy is
at most2C/[N*(1-alpha_i)], uniformly over that entire replacement class.
Apply this bound to both sides of Nash and to prescribed payoff delivery.
The SAME profile and its actual terminal payoff supply every accuracy at
sufficiently long horizons. L and the table are fixed before taking that
horizon; no cross-table target is asserted.

The matching actual semantic declarations are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

## 6. Two selected columns with mixed remaining columns

An early negative test keeps the scale claim honest. For three players with
own singletons1 and every passive singleton0, Gamma has every off-diagonal
entry-1. Select only recipient0's containing pair01 for a large positive
reward. Any positive leading root would need (Gamma*z)_1=0 at the unselected
recipient1, but this equals-z0-z2<0. Thus no all-positive bounded-z leading
root exists. This falsifies dropping(1) for this diffuse all-interior
mechanism, not existence of UE by another strategy.

The following entire raw family illustrates the omitted-column freedom.
Set all own singletons to5 and

    Gamma=[ 0, 1, 3,-1;
            2, 0,-3, 3;
           -2,-4, 0, 4;
            3,-2,-2, 0 ],                   det Gamma=168,

    Gamma^-1=(1/168)[48,24, -6, 36;
                     8,32,-22,-36;
                    64, 4, 13,  6;
                    32,44, 17,-18].                         (10)

Exactly columns0 and1 are strictly positive; columns2 and3 have mixed signs.
The literal singleton rows are

    0:(5,7,3,8),  1:(6,5,1,3),
    2:(8,2,5,3),  3:(4,8,9,5).

Let successor be the cycle0->2->1->3->0. For every pair {i,succ(i)}, pay-1
to i, r_succ(i)({i})+20 to succ(i), and1 to outsiders. The opposite pairs
in this cycle pay-1 to members and1 to outsiders. Explicitly:

    01:(-1,-1,1,1), 02:(-1,1,23,1), 03:(24,1,1,-1),
    12:(1,22,-1,1), 13:(1,-1,1,23), 23:(1,1,-1,-1).

Triples pay-1 to members and1 to the outsider. Set

    r(I)=(M,2M,-12,-13).                                    (11)

Apply Section1 with J={(0,I),(1,I)}, positive signs, coefficients1,2,
L=M^(1/3), and residual bound24. This gives actual all-interior stationary
Nash/UE for EVERY sufficiently large M, with no limiting root input.

### 6.1 Actual R0 degree and selective-child screens

Every off-diagonal column of Gamma has a negative entry. All principal
matrices of sizes2,3,4 are nonsingular. These two facts imply R0: a nonzero
homogeneous complementary vector cannot have singleton support because of
the negative outside entry, and any larger active support would lie in a
nonsingular principal kernel. For offset ones the active equation is
Gamma_CC*x=-ones. The complete census is:

| C | det Gamma_CC | Candidate x |
|---|---|---|
| 01 | -2 | (-1/2,-1) |
| 02 | 6 | (1/2,-1/3) |
| 03 | 3 | (-1/3,1) |
| 12 | -12 | (1/4,1/3) |
| 13 | 6 | (1/2,-1/3) |
| 23 | 8 | (1/2,-1/4) |
| 012 | -18 | (-3/2,1,-2/3) |
| 013 | 13 | (-11/13,-10/13,3/13) |
| 023 | 32 | (-11/16,-17/32,-19/32) |
| 123 | 48 | (5/24,7/24,-1/24) |
| 0123 | 168 | (-17/28,3/28,-29/56,-25/56) |

The sole positive candidate12 has outside residual-1/6 at3, so is infeasible.
Thus only the empty offset root exists, with index+1, and actual R0degree=1.
This uses `IsStandardLCPSolution.exists_box_localDegree_eq_sign_det` in
`MathUE/LinearProgramming/LocalDegree.lean`, with no extra support sign.

All four selective raw passive-child inverse sources fail. Deleted0 has
inverse entry(0,1)=-1/8; deleted2 has entry(1,2)=-2/13; deleted3 has
entry(1,0)=-1/3, in increasing retained-label order. Deleted1 DOES have
strict positive inverse, but its actual outside row times that inverse is

    (-1/4,11/16,9/8),

with a negative entry. This checks the conjunction in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`,
not merely a sufficient pointwise child safety test.

### 6.2 Whole sure-owner and universal child-source exclusions

No root Nash has a sure quitter, for ANY continuation and M>5. Fix owner i.
Its two nonsuccessors contain at least one of2,3: positive-grand labels0,1
are OPPOSITE in the chosen successor cycle. That nonsuccessor's joining
rewards are always-1 or a negative grand entry, while absent terminal rewards
are positive, so it must Continue. Grand is now unreachable, and the second
nonsuccessor must Continue by the same proper-row comparison. The successor
strictly joins, gaining20 over its passive singleton. Owner i receives-1
and strictly improves by withdrawing to its positive passive singleton at
the successor. This excludes every nonempty sure-base/free-set source, not
only pure quitting coalitions.

Every proper nonempty child C has an unsafe EXACT child Nash: choose d in C
with succ(d) outside C, let only d Quit0 and all others choose Never. Owner d
earns5 versus0. Every other child member gets a positive passive singleton
and loses by joining for-1. All child debts and joint Never mass are0, while
the absent successor gains20 by Quit0. This defeats every universal
child-debt plus bounded Never-slack withdrawal/future-join bound on EVERY
proper child; it is separate from the selective-child check above.

### 6.3 Entire weight sets and actual face tests

The only premium trap is all4: in a proper set a player's only above-own
participatory reward is its incoming pair, which forces its predecessor
into the set. For every nonzero nonnegative w, summing the four actual
singleton inserted-premium tests gives

    7*w0+5*w1+6*w2+6*w3>0.

The ENTIRE support-upper-average arm therefore fails, including zero-weight
selections. So do the boxed singleton negative-insertion requirements.
For actual absent insertion-leave sums the analogous coefficients are
(4,3,8,7), all positive. For participant premiums summed on cycle pairs they
are(13,11,12,12), again all positive. Conversely the inserted-premium vector
at012 is(-6,-6,-6,-18), excluding every nonnegative positive-floor weighting.
These use different subtractions and are not conflated. The relevant raw
definitions are `HasBoxedQuittingNashCharges` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`
and the named boxed/mixed-support packet predicates.

Every player fails both global participant protection directions: its
incoming pair pays above own5, and its outgoing donor pair pays-1 below5.
The common-leaver condition `IsCommonQuittingPremiumLeaver` in
`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`
uses >=own. Every pair has a below-own donor. Every triple contains a negative
ordered pair joining gain, and every triple-member join from the other pair
gains-2. Thus the both-above-own pair and six-positive-join triple predicates
fail over every selection.

For each ordered pair(i,p), choose j among successor(i) and the cycle-opposite
label with j!=p. The outsider sole-sure row has actual residual

    H_i=r_i({i,j})-r_i({j})=-1-r_i({j})<0.

This defeats the WEAK lower crossed face for every pair and height, not only
coefficient sufficient guards. The actual definitions are
`QuittingCrossedSourceGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`
and `QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.

### 6.4 Singleton, quotient and pole-architecture scope

The full positive inverse and full signed-inverse-column hypotheses fail
mixed column2. The standard non-Q exit fails because actual degree1 implies
standardQ, and every row has a negative blocker so the recursive normal core
is all4. The all-principal projective-Q side fails at pair12, with two negative
off-diagonal entries. No column is wholly negative externally, excluding the
literal negative-pivot cyclic-child singleton pattern.

The only directed negative Hamilton cycle, up to cyclic start, is
0->3->1->2->0. Its reverse edge at2 has Gamma_21=-4, so the necessary
positive-predecessor condition of `SignedFourCycleSingletonData` fails.
This excludes both signed spectral choices and every relabeling. Rows0 and1
each have two positive off-diagonal entries, excluding weak-matching singleton
rows with a unique positive favorite. At the all-sure root the complete
response differences are(M-1,2M-1,-13,-14), pairwise distinct for M>5.
Thus any actual full-response-invariant quotient must be injective.

Both selected large grand rewards have the SAME positive field sign. They
do not satisfy the opposite-field-sign two-pole source. Nor is this a family
with one selected large pole and other residuals bounded, or bounded by
a fixed eta*L: its second grand pole has size comparable to L^3. This is
a comparison of literal raw-family hypotheses, not a claim excluding every
pointwise invocation with an unspecified residual threshold, unknown IFT
radius, or a different strategy architecture.

## 7. Exact next checks and nonclaims

Requested independent falsification: exact membership signs/pole powers,
multiple poles per recipient, WHOLE-shell cone margins with arbitrary signs
on unselected inverse columns, mixed-degree radial exclusion, scale-thick
uniformity, and all complete terminal/finite-average deviations. Separately
check every named whole selection-set comparison on(10)–(11), especially
degree orientation and the selective passive-row conjunction.

This may strengthen a one-column producer into a global selected-column cone
source; it does not prove any such inverse-column condition for an arbitrary
Fin4 table or settle Fin4 UE. No producer claim relies on the fixture screens.
