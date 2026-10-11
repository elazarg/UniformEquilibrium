# Independent check of synchronized passive reward cancellation

Reviewer: CODEX_TURING_BOX.

Reviewed source: `CODEX_EMMY_BOX__SYNCHRONIZED_PASSIVE_REWARD_VECTOR.md`,
SHA256 `a39eb261a2b7f91ddb977b843ecea82830be01d2fbb737f2646b8461934848cc`.

## Verdict and scope

Bounded independent mathematical PASS for Sections1–4: the finite-player
raw producer, fixed-box and scale-thick residual quantifiers, all complete
terminal deviations, and the same-profile fixed-target uniform conclusion.
Also independently checked the matrix, positive net vector, ratio interval,
leading root and determinant in Section5, equations(7)–(9). No mathematical
objection found within that scope.

Section5.1 degree census, Section6 whole-source comparisons, exhaustive
novelty, and Lean implementation are OUTSIDE this review. This is ordinary
mathematics, not a Lean check or admission to exports.

## 1. Passive membership, sign, and exact scale

For i outside S, the selected coordinate contributes only to B_i, with
opponent-set probability

    t^k * product_(j in S) z_j
         * product_(j notin S, j!=i)(1−t*z_j).

Its raw reward is−t^(−(k−1))*b_i. The minus in H_i=(1−alpha_i)Q_i−B_i
therefore gives the positive term stated in the source after dividing by t.
For i in S there is no selected pole, precisely because b_i=0 there. This
support restriction is essential; a participatory coordinate would have a
different leading polynomial.

With fixed singleton levels, the bounded-data linear term is−Gamma*z.
An absent-player nonsingleton has at least two opponent quits, hence at
least t² before division by t. A participatory nonsingleton has at least
one opponent quit in Q_i and the additional factor1−alpha_i, hence again
at least t². The selected survival-factor remainder is divisible by t.
Thus the exact polynomial extension(5), including the exponent d=k−1,
holds for arbitrary signs and every finite n with2<=k<n.

As an independent small exact test, expanded all four H_i/t polynomials for
the Section5 matrix and S={1,3}, allowing separate symbolic pole coefficients
b0,b2 and nonzero bounded rewards at every other coalition. Every constant
coefficient was b_i*z1*z3−(Gamma*z)_i; no negative power of t remained.
This computation supports the direct general argument rather than replacing it.

## 2. Net positive root and uniform production

Write v=Gamma^-1*b>0 and rho=P(v)^(−1/(k−1)). Then
rho^k*P(v)=rho, so z*=rho*v is an exact positive root. The determinant lemma
gives

    det(−Gamma+b*grad(P)^T)
      =det(−Gamma)*(1−grad(P)(z*) dot v)
      =(1−k)*det(−Gamma).

Euler's identity applies to the homogeneous degree-k monomial even though
b and its individual inverse columns have arbitrary signs. No selected
column positivity or externally supplied regular root is being smuggled
into the input.

The displayed contraction argument supplies one ball and one positive
t-threshold for the ENTIRE residual box. Its derivative at the center
vanishes uniformly in that box at t=0, its center error is O(t), and its
derivative and center estimates are uniform by polynomial compactness.
Positivity of the fixed ball and t*max z<1 give actual independent hazards
strictly between0 and1.

For compact singleton/b data preserving the stated strict conditions,
z*, J^-1 and the positive orthant margin vary continuously and are uniformly
bounded. Own singleton levels are explicitly kept bounded in the source,
so no omitted unbounded reward coordinate invalidates the common threshold.

## 3. Scale-thick residuals

Every residual collision coordinate enters Phi with at least one factor t,
and the dependence on that coordinate is linear. Substituting c=e/t therefore
leaves a polynomial perturbation bounded with its z-derivative by O(|e|)
on the common ball. Taking |e|<=eta small first, then t small, preserves
both the contraction and the inward ball margin. This applies also to
participatory pair residuals, whose leading perturbation need not vanish.

Consequently the stated allowance |c|<=eta*M^(1/d) is justified. The source
correctly does NOT retain the z→z* or target→s conclusion for this enlarged
box unless e=t*c→0. It does not interchange fixed-table horizon limits
with the large-M or residual-box limits.

## 4. Full behavioral and uniform payoff consumer

At H_i=0, positive opponent absorption gives Q_i=B_i/(1−alpha_i)=V_i.
The stationary payoff recursion has the unique solution U_i=V_i. A deadline h
has payoff

    B_i*(1−alpha_i^h)/(1−alpha_i)+alpha_i^h*Q_i=V_i,

and Never has payoff V_i as well. Complete private behavioral replacements
on the sole surviving history are mixtures of these stopping times,
independent of opponent randomness. Thus no deadline, Never, nonstationary
clock, or behavioral mixture is omitted.

Because2<=|S|<n, n>=3 and every opponent hazard is positive, each deleted
profile contracts. For each FIXED table the finite reward bound C is finite,
including all large selected coordinates. The opponent first-quit time has
mean at most1/(1−alpha_i), uniformly over the replacing player's strategy.
The stated O(C/[N*(1−alpha_i)]) terminal-to-average comparison is therefore
uniform over the full deviation class. It yields one fixed actual target
for that fixed table/profile before choosing the accuracy cutoff.

Read the actual declarations
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`, including
their fixed-point, endpoint-Nash, joint-absorption and deleted-contraction
hypotheses. The produced profile satisfies all of them; no boundary value
is asserted from a noncontracting player. These checked consumers do not
formalize this note's raw producer.

For fixed bounded residuals, no selected passive coordinate enters any Q_i,
so Q_i=s_i+O(t) as stated. This need not hold uniformly in the scale-thick box.

## 5. Limited exact calibration check

Independently inverted the displayed matrix: det Gamma=265 and the stated
inverse is correct. Its columns0 and2 each contain positive and negative
entries. For b=e0+4e2 their sum is(188,230,18,29)/265, strictly positive.
The four coordinate inequalities for e0+x*e2 reduce exactly to
14/5<x<109/20. With S={1,3}, the resulting leading root is precisely
(9964,12190,954,1537)/1334 and det J=−265.

These checks establish the advertised joint-column cancellation example,
not its separation from every other original-game producer.

## 6. Bounded check of the distinct-coalition extension

Reviewed NEW Sections8–10 at whole-source SHA256
`ab0508ee6c7106665dae14fb91816ac4cf9700f8cc00fb2258123854e2a36e73`.
The preceding Sections1–4 review is reused, not repeated.

Verdict: bounded mathematical PASS after the following required factual
wording correction in Section10. Its statement that w>0 is false:

    u=Gamma^-1*e2=(-20,15,15,-20)/265,
    w=Gamma^-1*e1=(171,150,-9,118)/265.

BOTH directions have strict mixed signs. The author independently identified
this correction before review. The theorem assumes only positivity of
u+x*w on its bracket, so its proof and all displayed scalar formulas are
unaffected. No other mathematical objection found in the new producer,
its exact bracket, or the new whole sure-owner argument.

### Exact field, partial inverse, and scalar

The coalitions are distinct, so their passive raw coordinates do not
conflict. With independent powers L^(k_l−1), each selected contribution
to H/t has precisely the leading monomial b_l*P_l. The residual polynomial
argument from Section1 of this review applies separately to each pole,
including mixed sizes. Applying the fixed reward-space basis inverse gives
exactly(17). No strategic coordinates are projected away.

At y=0, h0=P1(V)^(−1/d1) is uniformly positive on the closed bracket.
The radial derivative of P1(h*V)−h is d1, while the transverse equations
are exactly−y at t=0. Hence the displayed block inverse(18) is valid
even at a multiple angular root; no derivative of G is assumed nonzero.
The remaining equation, after dividing by positive h, is

    −Psi2/h -> x−h0^d2*P2(V).

Thus the exponent d2/d1 in(13) is correct. Affine endpoint positivity
provides positivity throughout the bracket and a uniform face margin.

A contraction centered at the continuously varying(h0(x),0), using its
continuous partial inverse and a common sufficiently small radius, gives
uniform existence, local uniqueness and continuity over the whole bracket
and residual box. The strict endpoint signs survive; scalar IVT gives
an interior solution. This justifies the global chart gluing without
claiming angular uniqueness or selecting a continuous angular root.

The same substitution e=t*c gives a continuous polynomial small
perturbation for the eta*L residual class, including selected size-two
coordinates. Taking eta first and t second preserves the partial inverse,
positive compact branch and endpoint signs. Finite basis charts over a
compact set of independent b1,b2 suffice for a UNIFORM threshold. Their
coordinate branches need not be globally identified across changing
complements; the theorem claims uniform existence, not a global selection.
Singleton levels are explicitly part of the compact data.

The produced q is all-interior. Consequently the full-deadline/Never and
same-profile fixed-table uniform proof reviewed above applies unchanged.
There is no public seed or retained correlation introduced by the basis.

### Exact Section10 bracket and whole owner-face check

Independent symbolic computation gives

    V=(-20+171x,15+150x,15−9x,−20+118x)/265,
    G=(5900x³+103x²−1015x+100)/[10(10x+1)(59x−10)].

The positive interval is exactly10/59<x<5/3. At1/5 and1 the scalar
values are respectively−646/675 and2544/2695. Both endpoints are strictly
inside the interval. All signs, the equal-degree normalization, and both
passive penalty coordinates in(19) are correct.

For ANY sure owner a and arbitrary mixed choices of the others, its
opposite player o=a+2 obtains at most−1 by joining. Continuing gives
strictly positive rewards: a selected passive opposite pair cannot occur
because it either omits a or would include o, who is continuing. Singleton,
other-pair and outsider-triple rewards in that comparison are at least1.
Therefore o strictly Continues over the ENTIRE induced mixed domain.

Once o Continues, neither opposite pair can occur, so no selected penalty
enters any remaining nonowner comparison. The predecessor strictly
Continues since its joining rewards are at most−1 and its Continue rewards
are positive. The successor then surely Joins for40, strictly above its
singleton Continue reward. The owner now prefers withdrawal from its
donor payoff−1 to a singleton payoff at least4. This excludes ALL induced
sure-owner Nash components, not only pure or selected roots, for every M>0.

The modified coordinates are absent-recipient opposite-pair entries.
Thus the claimed inheritance of comparisons using ONLY singletons and
recipient-present pairs is logically sound. This review does not repeat
Section6's entire named-source census or admit exhaustive novelty. The
source's explicit caveat about unknown pointwise scale-thick thresholds
must be retained; failure of fixed-residual hypotheses alone cannot bound
those thresholds.

## 7. Bounded check of the macroscopic three-pole producer

Reviewed ONLY the new Section12 at whole-file SHA256
`3393051b39b6dbaef9e8592706b5150f26c8807479723bdf28dbe7e286f86617`.
Verdict: PASS, no mathematical objection found. This is ordinary independent
mathematics, not a Lean check or a new full source census. The previous
all-interior stationary full-cap and fixed-profile uniform consumers are
reused. The new cancellation, all-a branch, exact Jacobian, local/uniform
quantifiers, all-small comparison and whole sure-owner inheritance were
checked directly.

### Exact substitution and finite root

I independently enumerated all eight opponent quitter sets for EACH player
in the literal Section12 table, with q=(x,t*y,c,1-t*z) and M=1/t.
All four H_i have polynomial extensions at t=0; none has a remaining
negative power. The selected terms are exactly

    +x*c*z,  +y*(1-t*z)*(1-x),  -a*x*y*(1-c)

in H1,H2,H3 respectively. In particular the third raw PASSIVE positive
reward has the negative field sign. The four differences between the
independently expanded constant terms and(26) simplify identically to0.
This is genuine private joint-root enumeration, not an exogenous-stopper
approximation.

Substitution of c=33/35, y=(5-3x)/(1-x), z=(304x+96)/(33x) gives precisely
the displayed scalar F3_base-aD. On(0,x_star), K>0, K'<0, and the derivative
of(1-x)/(x(5-3x)) is strictly negative. Hence a(x) is strictly decreasing
from infinity to0; its endpoint derivative at a=0 is nonzero. Every fixed
a>=0 therefore has an actual positive limiting solution, not merely a
formal branch for small a.

The successive pivot derivatives in unknown order(c,z,y,x) are

    -35,  x*c,  1-x,  D(x)*a'(x),

with the last one evaluated at the fixed parameter a=a(x). All are
nonzero, including a=0. The Schur-complement argument therefore proves
the full Jacobian is invertible. Exact symbolic reconstruction at(31)
reproduced every displayed Jacobian entry and determinant2933667/6860.
The limiting Q_i also reproduce(30), including the negative target
coordinates. Those signs do not obstruct the contracting full-cap proof.

### Actual-table and uniform quantifiers

On a compact a interval, x(a) stays away from0 and1, c is fixed in(0,1),
and y(a),z(a) stay positive and bounded. The inverse matrices of the
limiting Jacobians are uniformly bounded. The THREE bounded selected-pole
residuals appear only multiplied by t; small perturbations of the other57
coordinates appear continuously at order one. A parameter-uniform local
IFT gives a common sufficiently small t and a common proper-coordinate
neighborhood for each finite residual bound and compact a interval.

This verifies the stated LOCAL57-coordinate tube. It would not verify
arbitrary bounded boxes there, a uniform threshold over unbounded a, or a
single payoff target across different raw games; none is claimed. At each
actual selected game, t*y and t*z are positive and less than1, so every
hazard lies strictly between0 and1. Each deleted-opponent continuation
probability is consequently below1. H=0 then makes ALL finite deadlines
and Never exactly indifferent, giving unrestricted terminal Nash and the
same-profile finite-horizon equilibrium contract with that game's target.

### Exact auxiliary comparisons and scope

Using the note's convention Gamma_ij=r_i({j})-s_i, the small-scale field
is Gamma*w=e1*w0*w2+e2*w1*w3-a*e3*w0*w1. Its first two equations give
w1=(3+3r/2)Y and w0=4(1+r)Y/(1+Y), with r=w3/w2 and Y=w2. The fourth
equation gives(32) exactly. For a>=1/4 its left coefficient is at most
-1-3r^2/2, so a positive all-small leading root is impossible. This is
only a scale comparison, not stationary nonexistence.

The whole sure-owner exclusion also survives: the owner's opposite player
strictly Continues over every mixed opponent domain. Its joining reward
is at most-1, while its Continue rewards are nonnegative; the new positive
passive coordinate can only strengthen this comparison. With the opposite
player absent, both negative passive opposite-pair poles are impossible.
The predecessor then strictly Continues, the successor surely Joins for40,
and the owner strictly benefits by withdrawing from-1 to a positive
singleton. The successor's sure participation removes continuation-value
dependence from this last comparison. This excludes the ENTIRE sure-owner
root correspondence for every a>=0 and M>0, not just chosen pure roots.

No independent admission of exhaustive novelty is made. Section6's other
source census was not repeated, unknown scale-thick thresholds remain
unknown, and no arbitrary-table macroscopic producer follows from this
explicit raw family.

## 8. Bounded check of the arbitrary raw-endpoint extension

Reviewed ONLY the new Section13 at whole-file SHA256
`4033a7d23312c0781f9c7474de09f4ad352e58e57069d9bdf18d128bd4c3fd3b`.
Verdict: PASS, no mathematical objection found. This is an ordinary
independent producer check, not Lean verification or whole-source admission.
The previously reviewed all-interior full-cap/uniform consumer is reused.

I independently enumerated all eight opponent quitter sets for each player
using SYMBOLIC variables for every one of the57 fixed raw coordinates,
and the three selected pole entries exactly as(33). After substitution
q=(x,t*y,c',1-t*z), the four H_i have polynomial extensions at t=0.
All four differences from(36) vanish identically, with no reward signs or
singleton relations imposed. In particular F is genuinely quadratic in x,
both expressions in(35) equal its literal endpoints, and none of the
eight guards depends on a selected pole coordinate.

A0>0>B0 gives a unique c in(0,1). A2,B2<0 give positive y(x) for
EVERY interior x; L0,L1<0 give positive z(x) there. The denominator
constants beta1,beta2,x,c and1-x are strictly positive, as needed.
Substitution gives D=K*x*(b+d*x/(1-x)) with precisely the stated positive
b,d,K. No raw root or implicit complementarity condition has entered.

The ratio lemma is correct also for a concave F that initially increases.
Opposite endpoint signs give a unique simple root in(0,1): two simple roots
there would preserve, rather than reverse, endpoint sign; a double root
cannot reverse it. At this root F'<0. If its quadratic coefficient is
nonpositive, F/x decreases strictly while D/x increases strictly, and both
are positive before the root. If the quadratic coefficient is positive,
F'<F'(x_star)<0 before the root and D'>0. Both cases give STRICT negativity
of(F/D)', including its one-sided value at x_star. The required range is
infinity down to0. Thus every a>=0 has exactly one produced scalar root,
with nonzero derivative also at a=0.

The three triangular pivots and the final derivative in(38) are nonzero.
The full limiting Jacobian is therefore invertible without any Gamma,
degree or singleton-sign premise. Dependence on the finite raw parameters
is locally smooth; at a=0 the simple interior scalar root also admits a
local extension, so the endpoint of the allowed a domain causes no IFT
problem. Over a compact admissible parameter set the root is uniformly
away from x=0,1; c is uniformly interior, y,z are positive bounded, and
the inverse Jacobians are uniformly bounded. Bounded selected residuals
occur only with t. A uniform local IFT therefore gives the stated common
M0 and an actual all-interior stationary full Nash branch. No unbounded
parameter uniformity or arbitrary-game transformation is inferred.

The Section12 calibration values of all eight guards and F are correct.
Section13.5's no-endpoint-sign test correctly refutes only that particular
boundary-scale equation, not game existence. Its explicitly separate
whole-source admission remains outside this bounded review.
