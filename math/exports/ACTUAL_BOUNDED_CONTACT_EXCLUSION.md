# Actual all-END SUM minima have unbounded finite cap contacts

Ordinary mathematics. No new Lean
verification is claimed. All finite-control, timing and quadratic arguments
needed for the conclusion are included below.

## Exact statement and source case

Let I={0,1,2,3}. A native quitting table gives a finite real reward Z_i(T)
for every nonempty coalition T. Own singleton, live and literal Never rewards
are zero. Each owner independently draws a complete first-Quit law on the
natural dates and a distinct Never point. The first nonempty finite quitting
coalition absorbs. Every unilateral replacement of an entire law is allowed.

For an actual profile write U_i for its prescribed payoff, B_i for the
supremum over ALL finite-deadline and Never responses, e_i for its literal
Never response, N_i for its ORIGINAL Never probability, and

    d_i=B_i-U_i, D=sum_i d_i, nu=product_i N_i.

Fix M>=1 bounding all sixty rewards and assume

    A=inf{D(P):P actual,nu(P)=0}>0.

Let Gamma_ii=0,Gamma_ij=Z_i({j}) for i!=j. Suppose Gamma is invertible, every
off-diagonal entry is nonzero, and one column v=Gamma^-1 e_h is strictly
positive. Here e_h in this matrix formula is a coordinate unit vector.

**Theorem.** The finite native data and A produce a FIXED positive price
vector theta and t0>0 such that, for EVERY0<t<t0, the following actual source
case is impossible:

* P attains the unrestricted actual minimum of
  F_(theta,t)=sum_i theta_i(B_i-U_i)+t(sum_i theta_i)nu;
* all native caps at P are END: B_i(P)=e_i(P) for every i;
* the set of finite pure deadlines attaining any owner's native cap is bounded.

Equivalently, every ACTUAL all-END global minimum for these fixed prices
has arbitrarily late finite cap contacts. Contacts may be unused prescribed
actions. The theorem does not assert actual attainment of a compact minimum,
produce all-END activity, consume unbounded contacts, or prove Fin4.

The objective is the ORIGINAL full-SUM debt for the raised table
r_i(T)=theta_i[Z_i(T)+t] on nonempty coalitions, still with live/Never0.
Indeed native late finite replies tend to e_i because own singleton is0.
Thus finite replies determine B_i. Every finite reply at r adds theta_i t;
its late limit dominates raised Never. Consequently

    B_i^r=theta_i(B_i+t),
    U_i^r=theta_i[U_i+t(1-nu)], sum_i d_i^r=F_(theta,t).

Thus no native m or alpha minimum is substituted for the actual original
objective. An actual profile realizing a compact full-SUM minimum satisfies
the stated minimum hypothesis; such realization is not inferred here.

## Conjecture-facing change and strategic inputs

The restriction is that finite cap contacts occur at arbitrarily late dates.
It removes the ENTIRE actual bounded-contact source case, including arbitrary
sparse schedules with two persistent owners and the three-persistent,
four-contact rank-collapse case. The proof places no bound on the number of
empty dates or on the number of finite contacts being excluded.

The actual global-minimum and all-END properties are explicit source-case
PREMISES. This theorem does not produce either property from a closure point.
The fixed prices, positive original-Never floor, finite comparison profiles,
legal timing directions and normal multipliers are OUTPUTS of the proof.
No recurrent controller, favorable row, endpoint rank, continuous selector,
tail minimum, prescribed contact action or PSD multiplier is supplied.

## 1. Fixed prices and the produced original-Never floor

Write w^j=Gamma^-1 e_j for j!=h and put

    L_j=max_i |w_i^j|/v_i,
    lambda_j=1/[2(1+L_j)], lambda=min_(j!=h)lambda_j>0,
    c=(A/(28M))^4.

Both v+lambda_j w^j and v-lambda_j w^j are strictly positive: each coordinate
is greater than v_i/2. Also A<=8M because each of the four debts is at most
2M and absorbing profiles exist, so0<c<1.

Choose prices z_j in(1,2) for the three j!=h such that

    z_i Gamma_ij-z_j Gamma_ji!=0 for all distinct i,j!=h.

This is an explicit finite producer. Take four equally spaced interior
values in(1,2) for each coordinate. Each of the three nonzero linear forms
vanishes at at most4^2 points of the4^3 grid. Since3*4^2<4^3, inspection
produces a point avoiding all three. Let delta>0 be the minimum absolute
value of those discrepancies. Define

    epsilon=min(c lambda/4,
                c lambda delta/(8M),
                min_(j!=h)c |Gamma_jh|/(8M))>0,
    theta_h=3epsilon/4, theta_j=z_j for j!=h,
    Theta=sum_i theta_i, t0=epsilon A/32.

These choices precede t and every minimum. They give theta_min>=epsilon/2
and Theta<=8. For any actual profile, moving its smallest Never mass n to
one finite deadline forces absorption. Four prescribed values and the other
three response caps change by at most2Mn each; the mover's cap is unchanged.
The bound is uniform over whole-law responses. Hence

    A<=D+14M nu^(1/4).

At the proposed global minimum, AllNever comparison gives F<=tTheta, so
D<=16t/epsilon<A/2. Therefore nu>=c, and EACH original N_i>=c. In particular
all actual conditional hazards are strictly below1.

Only the explicit all-END premise is used below. Its independent source
production is not assumed as a strategy witness, local tail minimum or
realization field. The present theorem consumes precisely that source case.

## 2. Complete caps under finite late changes

Let q_i(a) be the conditional hazard at date a. For a product row q define
Q_i(q) as the forced-Quit offer, P_i(q) as its passive absorbing contribution,
H_i(q)=product_(j!=i)(1-q_j), and h(q)=product_j(1-q_j). For a fixed suffix
with prescribed payoff u, full cap b and Never offer e,

    U_i'=q_i Q_i+(1-q_i)P_i+h u_i,
    B_i'=max(Q_i,P_i+H_i b_i), e_i'=P_i+H_i e_i.

Every response quits now or continues to a complete suffix response. These
identities therefore price the full behavioral menu. Every conditional tail
of an actual all-END profile is all-END: an improved tail response would
improve original Never after multiplying by positive opponent survival.

Suppose all finite contacts occur before a fixed date A0. Let C be their
owner set. Choose finitely many controls after A0. Controls at positive
hazards are interior and allow both small signs; controls at zero hazards
allow nonnegative increases. All other hazards, including the conditional
suffix after the last changed date, are fixed.

In a legal neighborhood of the original profile the EXACT cap functions are

    B_i(z)=max(b_i,e_i(z)) for i in C, b_i=old B_i=old e_i;
    B_i(z)=e_i(z) for i notin C.                          (CAP)

Earlier contact offers stay fixed. Between A0 and the last control there
are only finitely many finite queries, each with a strict original gap;
continuity keeps them below b_i on C and below new e_i off C. After the last
control, END-minus-query equals its fixed conditional suffix gap multiplied
by NEW positive opponent survival. Its sign cannot reverse. Literal Never
and the earlier attained b_i give equality in(CAP). No uniform margin for
infinitely many later queries is needed.

Changing finitely many positive atom masses within a finite block, keeping
its zero atoms zero and its conditional suffix fixed, is also legal. The
positive atom probabilities and positive Continue-past-block probability
are smoothly equivalent to the block's positive conditional hazards.

## 3. A common bounded normal multiplier

Write x for the interior controls and y>=0 for zero controls. For gamma_i
in[0,1] on C and gamma_i=1 outside C define the smooth finite-control function

    L_gamma=sum_i theta_i gamma_i e_i-sum_i theta_i U_i+rho nu,
    rho=tTheta>0.

The directional derivative of F at the original profile is the support
function of the compact convex gradient box {D L_gamma}. Local minimality
on the legal cone therefore gives at least one common gamma satisfying

    D_x L_gamma=0, D_y L_gamma>=0.                        (KKT)

For clarity, if the gradient box missed {0 on x,nonnegative on y}, strict
finite-dimensional separation would give a direction with nonnegative
y coordinates and negative maximum derivative. That would be a legal
first-order descent. Thus(KKT) follows before any constraint qualification.
The gamma values are dual multipliers, not a randomizer in the game.

Let S be the owners with unbounded finite stopping support. For each owner
in S choose arbitrarily late positive controls; for every owner outside S
choose a zero control after its last finite atom. All these controls can be
included in one finite family. Positive original N implies q_i(a)->0 and
all conditional future finite masses tend to0. With n_i(a)=Pr(T_i>=a),
n_i(a)->N_i and original joint survival tends to nu. Thus the whole-source
first derivatives at late controls satisfy

    partial_j e_i ->(nu/N_i)Gamma_ij,
    partial_j U_i ->nu Gamma_ij, partial_j nu ->-nu.

For example, varying q_j(a) changes its complete law by
n_j(a)[delta_a-mu_j^(>a)], where mu_j^(>a) is its fixed conditional law after
a. This law tends to literal Never in total variation; earlier absorption
cancels, leaving the singleton Gamma contribution. Bounded rewards control
the error uniformly. Never of recipient j ignores its own law, and the
zero diagonal includes this case.

Take a subsequence of bounded multipliers for the late families. The SAME
limiting gamma yields

    r_i=theta_i(gamma_i/N_i-1), a_i=theta_i+r_i=theta_i gamma_i/N_i,
    r^T Gamma>=rho one^T, equality on columns S.          (KT)

No stationarity is imposed at a missing finite action: its inequality has
the correct one-sided sign.

## 4. Every limiting effective-price pair is unbalanced

Multiply(KT) by v>0 to obtain r_h>=rho sum v_i>0. The cap multiplier bound
gives r_h<epsilon/c and, directly,0<a_h=theta_h gamma_h/N_h<=epsilon/c.
Apply(KT) to BOTH positive directions v plus or minus lambda_j w^j. Then

    r_h plus or minus lambda_j r_j>0,
    |r_j|<epsilon/(c lambda_j)<=epsilon/(c lambda) for j!=h.

In particular a_j>3/4 off h. For two nonpivot owners, changing z to a changes
their fixed discrepancy by strictly less than

    (|Gamma_ij|+|Gamma_ji|)epsilon/(c lambda)<=delta/4.

For h,j, |a_h Gamma_hj|<=|Gamma_jh|/8 whereas
|a_j Gamma_jh|>3|Gamma_jh|/4. Consequently EVERY pair satisfies

    a_i Gamma_ij!=a_j Gamma_ji.                           (UNBAL)

These bounds are uniform over all limiting multipliers satisfying(KT),
using the already fixed prices and the original source Never floor.

## 5. Mixed finite-control derivatives

We record the second derivatives needed later. For distinct controlled
owners j,k at dates a<b tending to infinity, the limits are

    partial_j partial_k U_i /nu ->-Gamma_ik for every i,
    partial_j partial_k e_i /nu ->-Gamma_ik/N_i if i outside{j,k},
    partial_j partial_k e_j=partial_j partial_k e_k=0,
    partial_j partial_k nu/nu ->1.                       (MIX-LAW)

Indeed each control replaces the owner's remaining law by current Quit minus
its conditional future law. In the four signed outcomes, the earlier
singleton j cancels and removes the later singleton k. The prescribed
singleton coefficient is -Gamma_ik. Never of i omits its own law; outside
j,k its reach factor is nu/N_i instead of nu. Any additional finite clock
after a has vanishing probability. This controls all errors uniformly even
if b-a tends to infinity. The exact Never mixed derivative is
nu/[(1-q_j(a))(1-q_k(b))].

For TWO dates a<b of the SAME owner j, its mixed signed-law derivative is

    -n_j(b)/(1-q_j(a)) [delta_b-mu_j^(>b)].

It follows that the limits of the prescribed and Never mixed derivatives
are -nu Gamma_ij and -(nu/N_i)Gamma_ij respectively, with recipient-j Never
derivative0. The Never-product mixed derivative again tends to nu. Individual
second derivatives in one hazard are0 exactly, by affinity in that hazard.

For a common multiplier with limiting r as in(KT), these formulas give

    same persistent owner j: H/nu ->-sum_i r_i Gamma_ij+rho=0;
    earlier persistent j, later persistent k:
        H/nu ->theta_j Gamma_jk-sum_out r_i Gamma_ik+rho
              =a_j Gamma_jk.                            (HESS)

The last equality uses the persistent column k in(KT). The conclusions hold
for varying bounded multipliers by compactness; only a fixed finite number
of controls is involved in each mixed calculation.

## 6. At most one persistent owner is impossible

If |S|<=1, choose that owner, or any owner if S is empty. All its opponents
have bounded finite stopping supports. Every sufficiently late own finite
deadline agrees with Never on all opponent exits; on the all-opponent-Never
event both pay its own singleton zero. Hence ALL those deadlines attain its
END cap. Their dates are unbounded, contradicting the proposed source case.

## 7. Exactly two persistent owners: an exact timing derivative

Let S={j,k}. Cut after A0 and after the last finite atom of outside owners.
Those outside conditional laws are literally Never. Put

    f_j=Pr(j finite), f_k=Pr(k finite),
    A_jk=Pr(T_j<T_k), C_jk=Pr(T_j=T_k<infinity),
    A_kj=Pr(T_k<T_j), L=f_j+f_k-f_j f_k=A_jk+A_kj+C_jk.

Never is ordered after every finite date. There is a legal interior finite-law
direction with d f_j=d f_k=d C_jk=0 and d A_jk!=0.

If only finitely many dates have both first-Quit masses positive, cut after
them. All changes of existing positive atoms preserve C_jk=0. Choose positive
j atoms a<c with a positive k atom between them; moving j mass from a to c
changes A_jk by -Pr(a<T_k<=c)<0 and preserves its finite mass.

Otherwise take an arbitrarily late positive tie a. Move j mass to a later
positive own atom c with p_k(c)<p_k(a) and a positive k atom in(a,c]. The
timing derivative has d A_jk<0,d C_jk<0. Move k mass from a to a later positive
own atom d with p_j(d)<p_j(a). Its derivative has d A_jk>0,d C_jk<0. Both
preserve the marginals. Their vectors are independent, so a linear combination
has d C_jk=0,d A_jk!=0. All necessary atoms exist by persistence and p_i(a)->0.
These are two-sided finite-block variations; only their derivatives, not an
exact curve of constant tie probability, are required.

Include this timing direction and dedicated late controls in one finite
family, and take the common multiplier from(KKT). Let n_i be original
Continue probability through the fixed cut and sigma=product n_i. For
outside owners n_i=N_i EXACTLY, because no finite mass remains after the
cut. This equality is not assumed for persistent j,k. The exact suffix values
are

    e_j=Gamma_jk f_k, e_k=Gamma_kj f_j,
    U_j=Gamma_jk A_kj+Z_j({j,k})C_jk,
    U_k=Gamma_kj A_jk+Z_k({j,k})C_jk,
    U_i=e_i=Gamma_ik L+(Gamma_ij-Gamma_ik)A_jk
                                +(Z_i({j,k})-Gamma_ik)C_jk for outside i.

The old head contributes constants, factor sigma on prescribed values and
factor sigma/n_i on Never offers. Stationarity along the timing direction,
divided by sigma d A_jk, therefore gives the EXACT finite-family identity

    0=sum_out r_i(Gamma_ij-Gamma_ik)+theta_j Gamma_jk-theta_k Gamma_kj,
    r_i=theta_i(gamma_i/N_i-1) for outside i.             (TIMING)

Persistent Never terms and nu depend only on the fixed marginals. No
approximate prefix survival is substituted for an original Never coordinate.
Pass to a subsequence of arbitrarily late families. Subtracting persistent
columns j,k of(KT) yields

    sum_out r_i(Gamma_ij-Gamma_ik)=r_j Gamma_jk-r_k Gamma_kj.

Together with(TIMING) this gives a_j Gamma_jk=a_k Gamma_kj, contradicting
(UNBAL). Thus the entire two-persistent bounded-contact mode is excluded.

## 8. At least three persistent owners: a low-dimensional multiplier set

Assume |S|=3 or4. Choose twenty late positive hazards in chronological word
(j,k,j,k) repeated FIVE times for two distinct j,k in S. Add one positive
control for every other owner in S and one zero control for every outside
owner. Persistence produces these finite words arbitrarily late. Let x,y
be the resulting interior and zero coordinates.

For one such finite family define

    g_gamma=D L_gamma, H_gamma=D_x^2 L_gamma,
    Lambda={gamma in the contact box:g_gamma,x=0,g_gamma,y>=0}.

It is nonempty by(KKT), compact and convex. The END gradient columns of one
late positive control per persistent owner tend to
diag_(C)(nu/N_i)Gamma_[C,S]. Gamma's rows C have full rank|C|; deleting
4-|S| columns lowers rank by at most4-|S|. Thus sufficiently late families
have rank D_x e_C>=|C|-(4-|S|). The affine gradient equations leave

    dim Lambda<=4-|S|<=1.

The box and inequality cuts cannot enlarge dimension. Lambda is a point or
a segment, without any full contact-row-rank or regularity assumption.

## 9. A second-order LP and a two-quadratic-form alternative

Put K=ker D_x e_C. For d in K all smooth vertex branches of the cap maximum
have first derivative0 on d. Their gradient differences are weighted END
derivatives, zero on K, and a member of Lambda has zero interior gradient.
For arbitrary w_x and w_y>=0 the quadratic path

    x(tau)=tau d+(tau^2/2)w_x, y(tau)=(tau^2/2)w_y

is legal. Taylor expansion and local minimality imply

    max_(gamma vertex)[d^T H_gamma d+g_gamma dot w]>=0
                             for EVERY w_x,w_y>=0.        (Q)

This yields an exact finite linear program. Minimize z subject to
z>=d^T H_v d+g_v,x dot w_x+g_v,y dot w_y for all contact-box vertices v,
with w_x free,w_y>=0. The dual has p_v>=0,sum p_v=1,
sum p_v g_v,x=0 and sum p_v g_v,y>=0. Its objective is sum p_v d^T H_v d.
Gradient and Hessian are affine in gamma, so the dual is exactly
max_(gamma in Lambda)d^T H_gamma d. It is feasible; weak duality bounds the
primal below, and finite LP strong duality applies. By(Q),

    max_(gamma in Lambda)d^T H_gamma d>=0 for EVERY d in K.  (ALT)

If Lambda is a point its Hessian is PSD on K. Otherwise take its two endpoints.
For two homogeneous quadratic forms q0,q1 the joint range Q(d)=(q0(d),q1(d))
is a convex cone. Here is a direct proof of additivity. For x,y put
z=x cos t+y sin t,w=-x sin t+y cos t, so Q(z)+Q(w)=Q(x)+Q(y)=p. If p!=0,
det(Q(z),p) changes sign after t increases by pi/2 and therefore vanishes.
There Q(z)=lambda p,Q(w)=(1-lambda)p; one coefficient is positive and
rescaling that vector produces p. If p=0 use d=0. Nonnegative scaling is
immediate, proving convexity.

If max(q0,q1)>=0 everywhere, this cone avoids the open negative quadrant.
Separation gives a nonnegative convex combination of q0,q1 which is PSD.
Apply this to(ALT). There is ONE gamma* in Lambda with

    H_gamma* PSD on K.                                  (PSD)

This is a bounded normal multiplier, with the correct zero-control inequality;
no abnormal multiplier or unconstrained smooth minimum is presumed.

## 10. Five negative blocks defeat all four contact constraints

For each late family take gamma* from(PSD), then a convergent subsequence.
Its limit satisfies(KT) and(UNBAL). Write D0=a_j Gamma_jk-a_k Gamma_kj!=0.
By(HESS), the normalized Hessian on the twenty selected coordinates has
zero diagonal and same-owner mixed limits, and ordered different-owner
entries a_j Gamma_jk or a_k Gamma_kj.

Within each of the five chunks, swap its two j coordinates and swap its two
k coordinates. On these TEN vectors the limiting quadratic matrix is block
diagonal with FIVE blocks[0,D0;D0,0]. Between separate chunks every term
cancels: the earlier chunk precedes the later and each swap has sum0.
Each block has a strictly negative direction. Hence for sufficiently late
FINITE families the Hessian has a five-dimensional negative definite
subspace, by continuity. Extra interior coordinates are zero there.

But K has codimension rank D_x e_C<=|C|<=4. It intersects that negative
five-dimensional space nontrivially, contradicting(PSD). Neither convergence
of kernels nor a lower singular-value bound is needed. This excludes every
|S|>=3 bounded-contact mode and completes the theorem.

## Scope, perturbations and the sharp quadratic boundary

Only nonzero off-diagonal singleton entries are used as a genericity gate.
They can be imposed by an arbitrarily small native reward perturbation:
changing every reward by at most eta changes any full cap and prescribed
value by at most eta, so A changes by at most8eta. Invertibility and the
strict positive inverse column are open as well. Prices and sources are
then selected afresh. No old contact pattern or minimum is transported.

The theorem is a complete exclusion of the ACTUAL bounded-contact case of
the supplied all-END global-SUM source. It does not assert that any compact
minimum is actual, that contact actions are played, or that unbounded finite
contacts yield an equilibrium. Those two source branches remain open.

The two-form restriction in Section9 is substantive. On R^2 take
q_r(x)=(u_r dot x)^2-(2/3)|x|^2 for unit lines at0,pi/3,2pi/3. Their maximum
is at least |x|^2/12, but every convex combination has trace -1/3 and is
not PSD. Thus the point/segment argument is not improperly extended to a
two-dimensional multiplier polygon; Section7 uses an independent exact
timing argument for that case. All randomness in the proof's convex duality
is algebraic: every comparison profile uses independent private laws.

## Operational correspondence and implementation handoff

The operational stopping-law model and the unrestricted behavioral model
agree by
`quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
and `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
The canonical conditional-hazard realization returns each complete law
exactly by `quittingBehaviorStoppingLaws_stoppingLawProfile` in that file.
These declarations include arbitrary finite deadlines and the literal Never
atom; they do not replace original Never by escaping finite mass.

The arbitrary root-prefix full-cap maximum used in Section2 is represented
by `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`. Its prescribed
counterpart is `quittingTerminalPayoff_rootThenContinuation_eq` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`.
The native late-finite/Never limit used for the row-raise identity is
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`; own
singleton0 removes its additional singleton term.

Those named source statements were statically inspected. They establish
the operational meanings and existing prefix interfaces; none proves the
finite-control, second-order or bounded-contact conclusion of this packet.
No new Lean compilation, unrestricted class seal or implementation credit
is claimed. In particular the Nash-root-specific debt recursion is not
silently used for these arbitrary non-Nash finite competitors.

A suitable primary theorem takes a native table on four owners, a bound M,
its positive absorbing SUM infimum A, and the raw matrix hypotheses. It
PRODUCES theta,c,t0. For each smaller t and each ACTUAL global full-SUM
minimum with native caps END, its conclusion is an unbounded set of finite
cap-contact dates. Positive N_i>=c must be derived by Section1, not assumed
as an extra source field. A compact minimizing annotation without an actual
law does not satisfy this theorem's strategic premise.

Implementation can separate the finite pieces: whole-law prefix/cap
transport; exact cap envelopes after bounded contacts; cone separation and
its compact normal multipliers; fixed-price estimates and signed-law
derivative limits; the two-owner timing producer; the rank/point-or-segment
bound; the explicit quadratic-path LP dual and two-form convexity lemma;
and the five-negative-block linear algebra. The final consumer must combine
these produced objects with the SAME original objective and Never values.
It must not accept fields asserting that the timing direction is legal,
that a small endpoint map is controllable, or that a PSD multiplier exists:
those are the mechanisms proved above, with the two-owner argument needing
no endpoint-map rank and the quadratic argument needing no regular-level
manifold. Actual attainment and the unbounded-contact consumer stay open.
