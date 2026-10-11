# Incoming pair rewards and a degree defect

Status: COMPLETE ORDINARY PROOF, with a bounded independent soundness PASS
on Sections1–5; the compact-singleton uniformity clarification below is
incorporated. Section10 also has a bounded independent soundness PASS,
including its whole-orthant homotopies, boundary supports and full-agency
alternatives. Section13 and its exact expansion(19) have a separate bounded
independent soundness PASS at snapshot
`e9562446507108506f008c9e32562b17db8e79c96381c0a20017367fb5508c77`,
including whole-orthant homotopies, boundary supports, actual degree
orientation, higher-coalition residual powers, compact uniformity and full
agency. Sections7–9 remain ordinary proof drafts awaiting a separate
fixture/coverage check; Sections11–12 are outside those reviews.
Section12 is a different explicit-root producer for row-proportional signed
pair coefficients, without R0, degree or inverse assumptions.
Section13 replaces weighted coercivity by a GLOBAL difference between the
singleton degree and the negative pair-coefficient degree.
The signed-pair extension's nonnegative-own or singleton-blocker agency hypothesis is
essential to the stated consumer. Not Lean checked, not exported. This produces actual stationary equilibria
from raw reward data, with arbitrary positive incoming-pair coefficients.
Neither a matrix inverse, a limiting strategic witness, a positive target
vector, nor a nonsingular selected-root Jacobian is an input. A correct
degree-one separating fixture is proposed in Sections8–9, but new named
reward-class admission is not yet claimed. Earlier local-IFT calibrations with degree-1 are
already covered by the implemented nonunit-degree source.

## 1. Self-contained raw-data theorem

Let I be finite, |I|=n>=2, and let pi be one cyclic permutation of ALL n
labels. A nonempty first-quitting coalition S absorbs at r(S) in real
I-space. Live dates and perpetual continuation pay0. Randomization is private
and independent; deviations are unrestricted complete behavioral replacements,
including every finite deadline and Never. All payoffs are expectations.

Fix arbitrary singleton data and put

    s_i=r_i({i}),   Gamma_ii=0,
    Gamma_ij=r_i({j})-s_i for j!=i.

Assume Gamma is R0: the only z>=0 with Gamma*z>=0 and
z_i*(Gamma*z)_i=0 for every i is z=0. Let d_Gamma denote the ordinary
degree at0 of the minimum-complementarity map min(z,Gamma*z), and assume

    d_Gamma!=0.                                      (1)

This is the actual R0 degree convention of the tracked project. A strictly
complementary offset root has index sign(det Gamma_CC), with NO extra
factor(-1)^|C|. The defining declarations are `r0Degree` in
`MathUE/LinearProgramming/R0Degree.lean` and
`IsStandardLCPSolution.exists_box_localDegree_eq_sign_det` in
`MathUE/LinearProgramming/LocalDegree.lean`.

Fix ANY positive coefficients kappa_i. For every finite residual bound R,
there is M0 such that for EVERY M>M0 and EVERY raw table satisfying

    r_i({i,pi(i)})=kappa_i*M+c_i,        |c_i|<=R,
    |r_i(S)|<=R at every OTHER nonsingleton recipient coordinate,

there is an actual stationary profile with at least two positive hazards,
all hazards strictly below1, which is EXACT terminal Nash against all
complete unilateral behavioral replacements. The SAME profile is a uniform
equilibrium at its actual terminal payoff. Some players may have hazard0.

More precisely, the produced hazard vector has q=z/M, where z lies in a
fixed compact annulus independent of M and of the bounded residuals. No
continuous selection of z is asserted. The conclusion is uniform over
compact positive coefficient sets and compact R0 singleton-matrix sets
on which the actual degree is nonzero, provided the own-singleton vector s
is fixed or also ranges over a compact set.

The already checked general theorem
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
covers degrees other than1 regardless of collision rewards. Thus the new
conjecture-facing source regime of this draft is degree1 together with
large positive incoming-pair rewards, not the previously covered degree-1
calibrations. This comparison does not yet establish a separating fixture.

## 2. The exact canceled nonlinear complementarity field

For stationary opponent hazards q_-i define

    alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A union{i})],
    B_i=E[r_i(A)*1_(A nonempty)],
    H_i=(1-alpha_i)*Q_i-B_i.

Here A is the independently drawn opponent coalition at one date; the
empty contribution to B is0. These are finite polynomials in hazards.
Set t=1/M,q=t*z and

    P_i(z)=(sum_(j!=i)z_j)*z_(pi(i)).

The selected containing-pair reward contributes only to Q_i, giving the
EXACT polynomial identity

    H_i(t*z)/t=kappa_i*P_i(z)-(Gamma*z)_i+t*E_i(t,z,c),
    G(t,z,c):=-H(t*z)/t
             =Gamma*z-diag(kappa)*P(z)-t*E(t,z,c).     (2)

E is polynomial in t,z and the bounded nonsingleton residual coordinates c.
For fixed compact z regions it and its derivatives are uniformly bounded.
Indeed1-alpha_i(t*z)=t*sum_(j!=i)z_j+O(t^2), the selected pair mass in Q
is t*z_pi(i)*product_(j!=i,pi(i))(1-t*z_j), and all nonselected collision
terms have at least two powers of t in H. This cancels the apparent pole.

The relevant zero condition is the FULL closed-orthant complementarity

    z>=0,   G(t,z,c)>=0,   z_i*G_i(t,z,c)=0.           (3)

It is not an all-interior equation. Its minimum map N_t(z)=min(z,G(t,z,c))
is continuous on the whole ambient real space; any zero automatically lies
in the nonnegative orthant and satisfies(3).

## 3. The incoming-pair map on the positive orthant

**Lemma.** For any fixed-point-free permutation pi, P is a proper smooth
diffeomorphism of the positive orthant onto itself. Its Jacobian determinant
has sign(pi).

In logarithmic coordinates its derivative is

    D_log P=Pi+S,
    Pi_ij=1_(j=pi(i)),
    S_ij=z_j/(sum_(k!=i)z_k) for j!=i,   S_ii=0.

S is row-stochastic. C=Pi^-1*S is row-stochastic and EVERY C_jj is
strictly positive, since j=pi(pi^-1(j)) differs from pi^-1(j). Its eigenvalues
have modulus at most1, and -1 is not an eigenvalue: every Gershgorin disc
has positive center C_jj and radius1-C_jj, so excludes -1. Real eigenvalues
therefore give positive factors1+mu; conjugate pairs give positive squared
moduli. Consequently det(I+C)>0 and sign(det DP)=sign(pi).

Properness is elementary. If every P_i lies in[a,b] with0<a<=b, then

    z_(pi(i))^2<=P_i<=b,
    z_(pi(i))=P_i/sum_(j!=i)z_j >=a/[(n-1)*sqrt(b)].

The preimage of a compact positive box is therefore compact and remains
strictly positive. The image is open by the nonzero Jacobian and closed
relative to the positive orthant by properness; it is nonempty, hence all
of that connected orthant.

For injectivity suppose P(x)=P(y)>0. Let r=max_j x_j/y_j and
m=min_j x_j/y_j. If r>m, choose i with x_pi(i)/y_pi(i)=r. The weighted
average of the opponent ratios in P_i contains this maximum with positive
weight, so1=P_i(x)/P_i(y)>r*m. Choosing an owner whose selected predecessor
has the minimum gives1<r*m instead. This is impossible. Thus every ratio
is the same and homogeneity of degree2 forces that common ratio to be1.
The inverse is smooth by the nonsingular Jacobian. This proves the lemma.

## 4. Exact degree deficit: zero outside, nonzero inside

Write G_0(z)=Gamma*z-diag(kappa)P(z), and N_0=min(z,G_0).

### 4.1 A common large boundary and total degree zero

Homotope Gamma away through G_u=u*Gamma*z-diag(kappa)P(z),0<=u<=1.
At a complementary root let r=max_j z_j and choose j attaining r, then
i=pi^-1(j). Since i!=j, P_i(z)>=r^2. Nonnegativity of G_u implies

    kappa_min*r^2<=C*r,
    C=max_i sum_j max(Gamma_ij,0).

All roots thus lie in one common bounded region. On a sufficiently large
ambient ball the total degree equals that of min(z,-diag(kappa)P(z)).

Homotope its offset from0 to ones. At a root of
min(z,u*ones-diag(kappa)P(z)),0<=u<=1, the same maximum-coordinate argument
gives kappa_min*r^2<=1. This homotopy also has a common large solution-free
boundary.

At offset ones there are EXACTLY two roots. One is z=0, strictly inactive,
with index+1. For any nonempty active support C, active equations require
P_i(z)=1/kappa_i>0, hence pi(i) belongs to C whenever i does. Because pi
is ONE cycle, C=I. The lemma gives exactly one full positive root. It is
regular, with index

    sign(det[-diag(kappa)*DP])
       =(-1)^n*sign(pi)=(-1)^n*(-1)^(n-1)=-1.

The total outer degree is therefore1-1=0. This argument uses the true
ambient index, not a cardinality correction to an LCP principal index.

### 4.2 A common small boundary with degree d_Gamma

Homotope G_0 to Gamma*z through Gamma*z-u*diag(kappa)P(z). R0 supplies
a solution-free punctured neighborhood of0, uniformly in u. Otherwise a
sequence of nonzero complementary roots z_k->0, normalized by their maximum
coordinates, would have a limit y>=0 with max y=1, Gamma*y>=0 and
y_i*(Gamma*y)_i=0. Quadratic terms vanish after normalization, contradicting
R0. Hence one sufficiently small ball has inner degree d_Gamma.

Choose its radius rho and a common large radius L as above. On the compact
annulus between the two balls the degree is

    degree_outer-degree_inner=-d_Gamma!=0.             (4)

Thus G_0 has at least one nonzero complementary root in the annulus. More
importantly, both boundaries have a positive minimum-map distance from0.
The exact uniform convergence in(2) preserves those boundaries and the
degree(4) for all sufficiently small positive t and ALL bounded residual c.
It produces an ACTUAL complementary root z(t,c) in the SAME annulus,
without a nondegeneracy assumption or a supplied limiting root.

The argument is uniform on compact positive kappa sets and compact R0
matrix sets: maximum-coordinate bounds are uniform, and normalization
compactness supplies uniform inner isolation. A nonzero degree at each
matrix suffices; no continuous root selector is used.

## 5. At least two proper clocks and every complete deviation

A nonzero leading complementary root cannot have singleton support. R0
implies that every column j has some strictly negative external entry
Gamma_kj; otherwise e_j is a nonzero homogeneous complementary vector.
For z=a*e_j,a>0, one has

    (G_0)_k=a*Gamma_kj-kappa_k*P_k(a*e_j)<0,

since P is nonnegative on the nonnegative orthant. This contradicts(3).
By compactness of the fixed annulus, actual complementary roots for all
sufficiently small positive t likewise cannot have singleton support:
any contrary sequence would converge to a forbidden leading singleton root.
They also cannot be zero because they lie outside the inner ball.

Choose t small enough that every q_i=t*z_i<1. At least two hazards are
positive, so EVERY recipient has a proper geometric opponent and alpha_i<1.
From(3), H_i<=0 and q_i*H_i=0. Put V_i=B_i/(1-alpha_i). Then Q_i<=V_i,
with equality for each active player. An arbitrary finite deadline h earns

    f_i(h)=V_i+alpha_i^h*(Q_i-V_i)<=V_i,

and Never earns V_i. An active player's prescribed clock earns V_i because
its two endpoints agree; an inactive player's prescribed Never earns V_i.
Every complete behavioral replacement is a mixture of these stopping laws
on the only live history, independent of the opponents. Thus the profile
is full exact terminal Nash, including all Never deviations.

For the fixed finite table, let R_table=max_(S,i)|r_i(S)|. Uniformly over
every replacement, the opponents' geometric first quit bounds the expected
live duration, so terminal and N-date-average payoff differ by at most

    2*R_table/[N*(1-alpha_i)].

Apply this on both sides of terminal Nash. The SAME stationary profile is
a uniform equilibrium at its actual terminal payoff. The horizon threshold
may depend on M and the actual table. The tracked actual semantic consumers
are `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
and `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

## 6. Exact calibration, nonclaim and remaining gate

Dropping the nonzero-degree hypothesis is not justified. For n=2 and
Gamma=[0,-1;-1,0], the limiting field Gamma*z-diag(kappa)P(z) has NO
nonzero complementary root. The actual R0 degree is0: offset ones has
the empty root index+1 and full root(1,1) index-1. A raw game with a large
both-participant pair reward can still have a sure-pair Nash; this example
falsifies the diffuse annulus implication, not UE existence.

For degree1 a positive-inverse matching matrix is a positive calibration,
but is already covered by the exported positive-inverse coalition-jackpot
theorem. A separating fixture must not repeat that overlap, the passive-row
triple lift, or the mistaken index of a negative-determinant active triple.
Sections8–9 propose one, without claiming admission before its whole-source
comparison is independently checked.

The exact polynomial, P-map, both homotopy boundaries, degree orientation,
perturbation, support and full behavioral consumer have passed the bounded
independent check recorded in
`feedback/CODEX_EMMY_BOX__INCOMING_PAIR_DEGREE_DEFECT_PRODUCER__BY_CODEX_TURING_BOX.md`.
The remaining requested check concerns Sections7–9 and source applicability.
The raw theorem changes reward-class coverage; it does not authorize changing
the rewards of an arbitrary fixed conjecture input or claim all Fin4 UE.

## 7. Fin4 consumer with NO singleton-matrix hypothesis

**Corollary (ordinary proof draft).** Fix ANY four-player singleton reward
rows, one cyclic permutation pi of the four labels, positive kappa_i, and a
finite bound R. There is M0 such that EVERY raw table with those singleton
rows, r_i({i,pi(i)})=kappa_i*M+c_i, |c_i|<=R, and all other nonsingleton
recipient coordinates bounded by R has a uniform-equilibrium payoff whenever
M>M0. No R0, degree, inverse, normality, sign, or strategic witness is an
input. A stationary full terminal Nash profile is asserted by Sections1–5
only on their R0/nonzero-degree source branch, not on every exit below.

Here is the complete reduction, whose matrix cases depend ONLY on the fixed
singleton rows. If Gamma is R0 with degree1, Sections1–5 give a common M0
and an actual stationary terminal Nash/UE for every allowed completion.
If Gamma is R0 with degree different from1, the tracked singleton-degree
criterion already gives UE for EVERY completion and every M. If Gamma is
not R0, suppose any completion had no UE. The tracked four-player reduction
gives full normal core; full normal core gives punishment normality for every
player; punishment normality and no UE imply R0 for the SAME Gamma. This
contradicts the matrix case. Thus this last case also has UE for every
completion and every M, so M0 can be0. These three cases prove the corollary.

The actual declarations, reopened for this deduction, are:

- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`;
- `all_punishmentNormal_of_normalCore_eq_univ` in
  `UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`;
- `isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff` in
  `UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`;
- `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
  `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`.

There is no circular choice of M0 after assuming no UE for a particular
completion: the cases and, in the degree1 case, the threshold are chosen from
the fixed singleton data, kappa and R before the completion is quantified.
No matrix-free stationary conclusion follows on the other two branches.

## 8. A boundary-support calibration and an interior-root obstruction

The following degree-one matrix is the literal tracked shared fixture:

    Gamma = [ 0, 1, 1,-1;
             -1, 0,-1, 2;
             -1, 2, 0,-1;
             -1,-1, 2, 0 ],                 det Gamma=7,

    Gamma^-1=(1/7)[7,1,-5,-3;
                  7,3,-1,-2;
                  7,2,-3,1;
                  7,5,-4,-1].

`matrix_eq`, `matrix_det`, `matrix_isR0`, and `matrix_r0Degree_eq_one`
in `MathUE/LinearProgramming/CyclicChildSharedFixture.lean` certify these
matrix facts and the actual degree1. Set pi(i)=i-1 modulo4 and

    kappa=(epsilon,1,1,1),   0<epsilon<=1/128.

Then the leading complementary field G_0 has the EXACT boundary root

    z=(0,1/2,1,1/2),       G_0(z)=(1-epsilon,0,0,0).       (5)

The active Jacobian on coordinates1,2,3 is

    [ 0, -1,  2;
      1/2,0,-3/2;
      -2,-1/2,0 ],                         determinant=-7/2.

Thus this particular boundary root could also be continued by an active-face
IFT. That is a calibration, not the input of the global theorem.

**Lemma (ordinary exact proof draft).** For the SAME kappa range, G_0 has
NO fully positive root. This does not assert that the actual raw game has
no all-interior stationary equilibrium at another hazard scale.

Write a=z0,x=z1,y=z2,w=z3, and suppose all are positive. The four equations
Gamma*z=diag(kappa)P(z) give

    x+y-w=epsilon*w*(x+y+w)=:e,
    a*(a+y+w+1)=2w-y=2x+y-2e,
    x*(a+x+w)=2x-w-a,
    y*(a+x+y)=2y-a-x.                         (6)

The last two equations imply x,y,w<2, w<2x, and y>x/2. Put
r=y/x>1/2 and beta=16*epsilon<=1/8. Then

    0<e<=12*epsilon*x<=beta*x,
    w=(1+r)*x-e,
    a<(1-r+beta)*x,        r<1+beta,
    a+x+w<=1-r+beta.

Consequently

    a+y+w+1 <= 2-r+beta+(r-1)*x <= 2+3*beta.

For the last bound, if r<=1 discard the nonpositive final term; if r>1
use x<2 and r<1+beta. The second equation of(6) would therefore require

    (2+r-2*beta)*x
      <= a*(a+y+w+1)
      <= (2+3*beta)*(1+beta-r)*x.

This is impossible, since r>1/2 and

    (2+3*beta)*(1/2+beta)-(5/2-2*beta)
       =-3/2+(11/2)*beta+3*beta^2<0   for0<=beta<=1/8.

This proves the lemma. It distinguishes closed-orthant global selection from
an all-positive limiting-root premise. It does NOT exclude a pointwise
application of every earlier UE source, all possible stationary profiles,
or an unquantified IFT neighborhood merely by geometric distance.

## 9. Proposed raw-family separation: exact bounded screens

These are author-checked ordinary calculations awaiting independent review,
not an exhaustive accepted-source census. Take epsilon=1/1000 in Section8,
own singletons1, and the literal singleton rows

    0:(1,0,0,0),  1:(2,1,3,0),
    2:(2,0,1,3),  3:(0,3,0,1).

For each directed adjacent pair {i,i+1}, pay -1 to i, kappa_(i+1)*M to
i+1, and1 to both outsiders. At opposite pairs pay -1 to members and1
to outsiders. At triples pay -1 to members and1 to the outsider. Set the
grand row to(-10,-11,-12,-13). All indices are modulo4. This is precisely
the incoming-pair family of Section1, with all unselected nonsingleton
coordinates bounded by13. Assume M>7000 in the following strict screens;
the existence threshold remains the possibly larger M0 from Section1.

### 9.1 All sure-owner/free-set selections and all proper children

There is NO exact root Nash with any sure quitter, irrespective of its
continuation. Fix a sure owner i. Every nonsuccessor j strictly prefers
Continue: every containing joining reward is -1 or a negative grand entry,
whereas every absent nonempty reward is nonnegative. Those two players
must Continue. The successor then strictly joins, since its pair reward
kappa_(i+1)*M exceeds its passive singleton reward at i. Owner i earns-1
and strictly improves by withdrawing to a nonnegative passive singleton
reward at the successor. This contradiction excludes every sure-owner and
every nonempty persistent-base/free-set Nash source selection at once.

Every proper nonempty child C has an unsafe EXACT child Nash. Choose d in C
with d+1 outside C, possible because no proper nonempty set is successor
closed. Prescribe Quit0 only to d and Never to the others in C. Joining d
pays-1 to every other child member, while Continue receives a nonnegative
singleton payoff. Player d earns its own1 rather than Never0. Thus the child
full debts and its joint-Never probability are all0. The absent successor's
Quit0 gain is kappa_(d+1)*M-r_(d+1)({d})>0. Hence no universal child-debt
plus bounded Never-slack withdrawal/future-join comparison can hold for ANY
proper child. This does not purport to exclude a selective passive-row lift.

That selective lift is instead excluded by the actual singleton screens:
`only_nonnegative_child_inverse` and
`no_nonnegative_deleted_inverse_and_passive_row` in
`MathUE/LinearProgramming/CyclicChildSharedFixtureScreens.lean`.
The actual raw source requiring BOTH a nonnegative child inverse and its
nonnegative outside row is
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

### 9.2 Entire nonnegative-weight sets

The only participatory premium trap is all4: a player in a proper trap needs
its incoming pair, forcing its predecessor into that trap, hence all labels.
For w>=0,w!=0 define the actual inserted-premium test

    H_w(S)=sum_i w_i*[r_i(S union{i})-1].

Summing its four singleton tests gives

    sum_d H_w({d})=sum_i (kappa_i*M-5)*w_i>0.        (7)

Thus the ENTIRE support-upper-average arm fails, including every selection
with some zero weights. The boxed-charge alternative also fails its required
negative singleton insertion charges by(7) at w=ones. With the actual
insertion-leave subtraction, the summed weighted singleton tests are

    (epsilon*M-6)*w0+(M-5)*(w1+w2+w3)>0.             (8)

This uses absent insertion gains, not participant withdrawal. Summing the
four weighted participant-premium tests on adjacent pairs instead gives
sum_i(kappa_i*M-3)*w_i>0, so all nonpositive participant-weight certificates
fail. Conversely the inserted-premium vector at023 is(-2,-12,-2,-2), so
every nonzero nonnegative global positive-floor weighting fails there.
These are opposite-sign conditions and are not conflated.

The raw definitions compared are `HasBoxedQuittingNashCharges` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`
and the actual upper-average/charge and floor statements of the named
`MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md` and
`BOXED_NASH_CHARGES_UNIFORM_EQUILIBRIUM.md` packets.

### 9.3 Remaining explicitly tested source predicates

The full inverse has mixed-sign columns, excluding the full positive-inverse
and full signed-column-positive inverse hypotheses. Its positive column0
does NOT by itself produce an all-interior diffuse root for these FOUR
arbitrary leading poles: Section8 disproves that implication exactly.
This is not a blanket claim that a one-pole theorem cannot apply pointwise
after choosing an unspecified residual bound and threshold.

Every player has an incoming participant reward above own1 and an outgoing
participant reward-1 below own1. Thus both global participant-at-most-own
protection and participant-at-least-own common-leaver conditions fail for
every player. `IsCommonQuittingPremiumLeaver` in
`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`
has direction >=own. Both-above-own pair sources fail for EVERY pair.
Every triple has a member whose joining reward is-1 while its pair-of-others
passive reward is1, so every six-positive-joining-gap triple source fails.

For any ordered partner selection(i,p), choose j from successor(i) and i+2
with j!=p. At the outsider sole-sure row, q_j=1 and all others0,

    H_i=r_i({i,j})-r_i({j})=-1-r_i({j})<0.

Thus the actual weak crossed lower face fails for EVERY ordered pair and
height, independently of sufficient coefficient guards. The compared actual
definitions are `QuittingCrossedSourceGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`
and `QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.

Column0 of Gamma is strictly negative off diagonal. Therefore every signed
four-singleton cyclic ordering violates its necessary positive-predecessor
comparison at the player whose predecessor is0. This includes both spectral
root choices from `SignedFourCycleSingletonData` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`.
The ordinary non-Q exit fails: degree1 implies standardQ, and the recursive
normal core is all4 since every row has a negative blocker within all4.
The projective all-principal-Q condition also fails at pair03, whose matrix
is[0,-1;-1,0].

Finally, the all-sure complete response differences are(-11,-12,-13,-14),
pairwise distinct. Any actual full-response-invariant player quotient must
therefore be injective. Failure of quotient symmetry is checked at a whole
response vector, not inferred from asymmetric-looking raw rows alone.

The requested next check is the whole selection-set applicability of these
named sources on this explicit family, together with the Fin4 deduction in
Section7. The main degree producer does not depend on these comparisons.

## 10. A whole-orthant quadratic account for general signed pair poles

Status: COMPLETE ORDINARY PROOF DRAFT, not independently reviewed. This
removes the prescribed-cycle restriction from the large-pair mechanism.
The signed version does not inherit the earlier automatic two-active-player
conclusion; the exact replacement for that step is stated explicitly below.

### 10.1 Finite raw data and the stronger source condition

Keep the finite-player, zero-Never, private-independence and unrestricted
agency semantics of Section1. Fix singleton rows with R0 comparison matrix
Gamma and nonzero actual degree d_Gamma. Let C be ANY real n-by-n matrix
with zero diagonal. At EVERY recipient/pair coordinate prescribe

    r_i({i,j})=M*C_ij+c_ij,     |c_ij|<=R,   i!=j,

and bound every other nonsingleton coordinate by R. Zeros of C simply leave
that coordinate bounded. There is no sign restriction on its nonzero entries.
Write

    P_C,i(z)=(sum_(j!=i)z_j)*sum_(j!=i)C_ij*z_j.

Assume there is a nonnegative nonzero vector w such that the explicit
quadratic polynomial

    Phi_C,w(z)=sum_i w_i*P_C,i(z)

is STRICTLY COPOSITIVE:

    Phi_C,w(z)>0 for every nonzero z>=0.               (12)

This is a finite raw-coefficient condition, not a supplied strategic root
or a continuation/cap assumption. Equivalently, for some m>0,

    Phi_C,w(z)>=m*(sum_i z_i)^2 for every z>=0.

Normalize sum_i w_i=1 if desired. The minimum giving m is taken on the
ordinary closed nonnegative unit simplex, not on an attainable-law set.

Assume in addition EITHER

    (a) every own singleton s_i is nonnegative; OR
    (b) for every column j there is k!=j with
        Gamma_kj<0 and C_kj>=0.                       (13)

Then for every finite residual bound R, every sufficiently large M and
EVERY allowed completion, there is an actual stationary FULL terminal Nash
profile q=z/M in a fixed nonzero compact annulus, with all q_i<1. The SAME
profile is a uniform equilibrium at its actual terminal payoff. Under(b),
at least two hazards are positive. Under(a), a singleton-support profile
is allowed and is consumed directly below.

Uniformity holds on compact singleton/coefficient/weight sets with uniform
R0 isolation, nonzero degree, bounded s, and a common positive copositivity
margin m. For the two-active conclusion using(b), its strict negative
blockers must also persist uniformly. No continuity of a selected root,
invertibility, inverse-column sign or root Jacobian is an input.

### 10.2 Exact field and a common root bound

The same finite expansion as Section2 gives the EXACT polynomial identity

    H(t*z)/t=P_C(z)-Gamma*z+t*E(t,z,c),   t=1/M.

Pair rewards enter linearly, so this identity holds for arbitrary signed
C, including several large pair coordinates in the same recipient row.
All remaining coordinates are bounded; E is polynomial and uniformly
bounded on the required compact sets. Set G_0=Gamma*z-P_C(z).

At ANY complementary root, G_0>=0. Therefore, without imposing that all
players are active,

    m*||z||_1^2 <= w*P_C(z) <= w*Gamma*z
                 <= ||w*Gamma||_infinity*||z||_1.      (14)

The same argument bounds all roots when Gamma is multiplied by a parameter
in[0,1], and when a bounded constant offset is added. This is a GLOBAL
bound on the whole closed orthant; no conditioning by a small survival
probability or summation of individual equilibrium errors is involved.

### 10.3 Global degree zero without a positive P_C or a P_C inverse

Let C* have every off-diagonal entry1. Condition(12) forces w to have at
least two positive coordinates: if w were supported only at i, its value
at z=e_i would be0. Consequently

    Phi_C*,w(z)=sum_i w_i*(sum_(j!=i)z_j)^2

is strictly copositive. To see this, at a zero every positive-weight i
would require sum_(j!=i)z_j=0, so a nonzero z would have to be supported
on EACH of two distinct singleton labels. Compactness gives its positive
unit-simplex minimum m*.

Homotope C to C* by convex interpolation. Since Phi is linear in C, the
same w gives a common lower bound min(m,m*)*||z||_1^2 throughout. Applying
(14) to Gamma*z-P_Ctheta(z) bounds every complementary root along this
homotopy. All minimum-map degrees on one common large ambient ball agree.

Next homotope C* to the matrix of ANY single cyclic permutation pi with
pi(i)!=i. Every intermediate matrix is nonnegative, and every column
has a positive sum uniformly in the homotopy parameter. For a maximum
coordinate z_j=r one has

    sum_i P_Ctheta,i(z)
       >=r^2*sum_(i!=j)(Ctheta)_ij >=a*r^2

for a common a>0. At a complementary root, summing G_i>=0 bounds this
quantity above by a constant times r. Thus this second homotopy also has
one common bounded root set, including every boundary support.

At its cyclic endpoint Section4.1 computes the WHOLE large-ball degree0,
using the exact empty/full root census of ones-P_pi. Hence the original
signed field has large-ball degree0 as well. It is not being asserted that
P_C is positive, injective, surjective or proper on the positive orthant.
Only its nonnegative weighted scalar account is coercive.

As in Section4.2, the quadratic order of P_C and R0 give small-ball degree
d_Gamma. The annulus degree is therefore-d_Gamma!=0. Uniform convergence
of the EXACT finite-t field preserves both boundary separations and gives
an ACTUAL nonzero complementary root in the same annulus for all small
positive t and every bounded completion.

### 10.4 Full agency, including a possible sole proper clock

Under(13b), a leading singleton root z=a*e_j would have

    (G_0)_k=a*Gamma_kj-a^2*C_kj<0,

so is impossible. Compactness then excludes actual singleton roots for
all sufficiently small t. Section5 supplies the complete terminal and
uniform-payoff conclusion with no singleton sign restriction.

Under(13a), a produced profile with at least two active players is consumed
by the same Section5 argument. If instead only j is active, all opponents
of j are Never. Its actual prescribed terminal payoff is s_j>=0, EVERY
finite deadline pays s_j, and Never pays0. Thus its complete full cap is
exactly s_j and its stationary clock is optimal. Every other recipient
has the proper geometric opponent j, so H_i<=0 gives Q_i<=B_i/(1-alpha_i)
and its prescribed Never attains the full cap as before.

For finite averages, every deviation of j yields at most s_j, because its
only possible finite reward is s_j>=0. Its prescribed geometric law has
finite expected absorption time, so its delivered average tends to s_j.
For the other recipients, opponent j gives the same uniform geometric-tail
bound over every complete deviation as in Section5. This proves SAME-profile
UE in the sole-active case too, without falsely invoking alpha_j<1.

For signed C one may NOT copy Section5's singleton exclusion merely from
R0: a negative C_kj can reverse the blocker at a*e_j. This is the precise
reason for retaining(a) or(b). No theorem with both hypotheses deleted is
claimed.

### 10.5 Two concrete raw families

First, EVERY nonnegative C with a nonzero entry in EVERY column satisfies
(12) with w=ones. Indeed, for a largest coordinate z_j=r,

    sum_i P_C,i(z)>=r^2*sum_i C_ij
                     >=(min_j sum_i C_ij)*r^2.

Condition(13b) follows from R0 and C>=0. Thus the new theorem covers
arbitrary positive incoming-pair networks with no uncovered quitting label,
not only permutation networks or a cycle cover. Some recipient rows may
be identically0, and the produced equilibrium can lie on a boundary face.
Arbitrary signs of own singleton rewards are still permitted in this case.

Second, for n>=3 and any single cycle pi, set

    C=(1+B)*Pi-B*Pi^-1,     B>=0.

Both matrices select off-diagonal pair coordinates. For B>0 this includes
negative large participant rewards, whose magnitudes need not be small.
Nevertheless

    sum_i P_C,i(z)
      =(sum_i z_i)^2-sum_i z_i*z_pi(i)
      >=sum_i z_i^2,

because the forward and reverse adjacent-product sums agree exactly. The
coercivity bound is INDEPENDENT of B, although the perturbation threshold
may depend on the fixed B. Therefore the nonnegative-own theorem produces
actual full equilibria for every fixed B, with negative outgoing reward
-B*M and positive incoming reward(1+B)*M. No signed inverse-column
condition is imposed on Gamma.

For Fin4 these two families, and the full signed theorem under(a), also have
a matrix-free UE conclusion: split the fixed singleton matrix into R0
degree1, R0 other degree, and non-R0 exactly as in Section7. The all-own
nonnegative hypothesis is retained for the signed family. A stationary
conclusion on the degree/non-R0 exits is not asserted.

### 10.6 Exact calibration and current question

Take Fin4 singleton own1, mate payoff4 and both other singleton payoffs0,
so Gamma=4*P_mate-J+I. Use a four-cycle pi, the signed C of Section10.5,
and set ALL nonselected nonsingleton coordinates0. At a uniform hazard q,
the positive and negative pair contributions cancel their B-dependence:

    Q=(1-q)^3+M*q*(1-q)^2,
    B_i=4*q*(1-q)^2,
    H_i/[q*(1-q)^2]
      =(3-3q+q^2)*[(1-q)+M*q]-4.                   (15)

The last polynomial is-1 at q=0 and M-4 at q=1. For every M>4, IVT gives
an interior q with H=0 for ALL four recipients, hence an actual full
stationary Nash and SAME-profile UE. This is an exact positive calibration,
not new coverage for this already well-understood singleton matrix. The
leading scaled root is z=(1/3)*ones.

The zero field C=0 shows why mere quadratic order cannot replace(12):
Gamma*z-P_C(z)=Gamma*z has ONLY the zero complementary root under R0,
and its large-ball degree is d_Gamma, not0. This is a failure of the outer
homotopy mechanism, not a no-UE example.

Current requested check: independently falsify the signed whole-orthant
homotopy and the sole-active nonnegative-own consumer. The original
Sections7–9 fixture review remains separate. No new raw-family admission
claim is based only on failure of an inverse-column hypothesis.

## 11. An exact failed matrix-taxonomy test

A numerical candidate for a degree-one matrix with EVERY inverse column
mixed was

    A=[0,-4,-7,-9; -8,0,-8,-2; 8,-7,0,7; -4,-2,8,0].

It is R0: all proper principal blocks of size>=2 are nonsingular, every
column has a negative external entry, and det A=9544. Its inverse columns
are indeed all mixed, and all four nonnegative-deleted-inverse tests fail.
But offset ones is NOT a regular root census. Support01 has x=(1/8,1/4)
and inactive residuals(1/4,0); support013 describes the SAME boundary root
with its third active coordinate0. Counting only strictly positive roots
there wrongly reports degree1.

At the generic positive offset b=(101,103,107,109), the only nonempty
complementary root has support01, x=(103/8,101/4), and positive inactive
residuals. Its index is sign(det A_01)=-1. Together with the empty root
index+1 this gives ACTUAL degree0, so the matrix is already in the known
nonunit-degree UE class. This is an exact falsifier of that proposed
separation, not evidence that mixed inverse columns force degree0.

Additional source declarations inspected in narrowing that question were
`quittingPunishmentNormalPathStrategicFork`,
`quittingPunishmentNormalPathDecoder_of_snell`,
`exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_snell`
and `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.
The latter theorem is an actual unconditional projective-Q-bar consumer;
conditional decoder wrappers elsewhere must not be mistaken for its
full hypothesis list.

## 12. A distinct signed-pair source with an explicit balanced root

Status: complete ordinary proof draft, NOT covered by the preceding
independent reviews. This removes R0, degree and inverse hypotheses by
using a different actual raw-coefficient restriction. It does not drop
those hypotheses from the arbitrary-C coercivity theorem.

### 12.1 Raw statement, including higher-coalition growth

Let I be finite, n>=2, with arbitrary singleton data s_i=r_i({i}) and
Gamma_ij=r_i({j})-s_i, Gamma_ii=0. Live dates and Never pay0. All random
clocks are independent and private, and unilateral replacements are
unrestricted complete behavioral strategies.

Choose arbitrary a_i>0 and DEFINE, from this raw vector alone,

    b_i=1/a_i,
    Z=(sum_i b_i)/(n-1),
    z*_i=Z-b_i.

Assume only the explicit strict rate balance and image nonvanishing

    z*_i>0,       (Gamma*z*)_i!=0       for EVERY i.          (16)

No matrix inverse, R0, degree, supplied root or strategic target is an
input. In particular a_i=1 is allowed whenever every row sum of Gamma
is nonzero; then z*=ones/(n-1).

For EVERY finite residual bound R there are epsilon>0 and M0 such that
EVERY M>M0 and EVERY original table satisfying the following raw conditions
has an actual ALL-interior stationary exact terminal Nash equilibrium:

    r_i({i,j})=s_i+M*C_ij+c_ij,   |c_ij|<=R,
    |C_ij-a_i*Gamma_ij|<epsilon    for EVERY i!=j;             (17)
    |r_i(S)|<=R                   if |S|=2 and i notin S;
    |r_i(S)|<=R*M^(|S|-2)         for EVERY |S|>=3.           (18)

The produced q=z/M has z in a fixed compact subset of the positive
orthant, uniformly over the entire permitted coefficient and residual
sets. Its actual terminal payoff is a fixed uniform-equilibrium target,
witnessed by the SAME profile. All own and collision rewards may have
arbitrary signs. No player is forced to quit surely.

For exact C_ij=a_i*Gamma_ij, one can select z(M)->z* uniformly in the
normalized residual box. For C varying in the fixed epsilon neighborhood,
only uniform closeness of z to z* is asserted, not convergence to z*.
All parameters remain fixed before equilibrium accuracy is chosen.

### 12.2 Exact polynomial and pole cancellation

Put t=1/M and q=t*z. Normalize every higher reward by

    e_(i,S)=t^(|S|-2)*r_i(S)     for |S|>=3.

These e, the passive-pair rewards, and c_ij lie in one fixed finite
compact box. The selected containing pair contributes M*C_ij times
the opponent singleton mass to Q_i, and hence a leading term
(sum_(k!=i)z_k)*(C*z)_i to H_i/t. The singleton contribution is
-(Gamma*z)_i. Therefore there is an EXACT polynomial identity

    H_i(t*z)/t
      =(sum_(k!=i)z_k)*(C*z)_i-(Gamma*z)_i
                              +t*E_i(t,z,C,c,e).            (19)

This includes all simultaneous coalitions. A containing coalition of
size k>=3 has opponent mass divisible by t^(k-1); multiplication by
1-alpha_i and division by t leaves a factor t^(k-1). Its raw reward
t^(-(k-2))*e therefore leaves at least one factor t. An absent coalition
of size k similarly contributes t^k/t times t^(-(k-2))*e, again with
one factor t. Thus no hidden pole survives in E. The original singleton
and pair terms also have polynomial cancellations. E and its first
z derivatives are uniformly bounded on every fixed compact z region.

### 12.3 An explicit nondegenerate root, regardless of matrix degree

At C0=diag(a)*Gamma the leading field in(19) factors as

    L_i(z)=[a_i*(sum_(k!=i)z_k)-1]*(Gamma*z)_i.              (20)

Since sum_i z*_i=Z, the opposite sum is Z-z*_i=b_i. Hence z* is an
ACTUAL leading zero for every Gamma. Its Jacobian is

    J_ii=0,
    J_ij=a_i*(Gamma*z*)_i      for j!=i,
    det J=(-1)^(n-1)*(n-1)*product_i[a_i*(Gamma*z*)_i]!=0.   (21)

The second differentiated factor drops out because its multiplier is0.
The nonzero determinant follows from(16), not an imposed root-regularity
condition on an unknown selected zero.

Choose a small closed ball around z*, contained in the positive orthant,
so that the derivative of z-J^-1*L(z) has norm<1/4 there. By uniform
continuity of(19) and its derivative on that ball and the compact residual
box, first shrink epsilon, then choose t small, so that the exact map

    T(z)=z-J^-1*[H(t*z)/t]

has derivative norm<1/2 throughout the ball and moves the center by less
than half its radius. It maps the ball to itself and is a contraction.
Thus it has an exact zero of H(t*z). This proves(17)–(18) for EVERY
allowed raw completion, without assuming continuity of a strategic
equilibrium correspondence. Shrinking the ball for exact C0 gives the
uniform z(M)->z* assertion. One may equivalently use the parameterized
implicit-function theorem; the contraction explains the compact-box
quantifiers directly.

### 12.4 All deadlines, Never and one fixed target

For small t every hazard lies strictly between0 and1. Thus alpha_i<1
for every deleted opponent set. Equation H_i=0 gives
Q_i=B_i/(1-alpha_i)=V_i. Prescribed play, every finite pure deadline and
Never all earn V_i. Every complete unilateral behavioral replacement is
an independent mixture of these endpoints and therefore earns V_i too.

For the fixed produced table/profile, the geometric opponent stopping
bound is uniform over the entire deviation class. With C_table the
finite actual reward bound, the error2C_table/[N*(1-alpha_i)] tends to0.
Thus its same actual payoff V is a uniform-equilibrium target. The bound
need not be uniform as M grows, since accuracy is chosen only AFTER the
table and profile are fixed. This is the full-agency consumer of Section5,
not a stationary-menu equilibrium assertion.

### 12.5 Exact positive and negative tests; relation to the ratio source

For the paired-hard Gamma in Section10.3 and a=ones, every row sum is1.
The explicit leading root is z*=ones/3. Here the signed pair C=Gamma
does NOT satisfy the preceding global coercivity hypothesis for ANY
nonnegative nonzero weight: its values on the two mate-face test vectors
are(3,3,-4,-4) and(-4,-4,3,3). Positivity on both would require
3(w0+w1)>4(w2+w3) and its reverse with the blocks swapped, impossible.
Thus this producer is not a specialization of that weighted account.

The membership-ratio family in
`CODEX_EMMY_BOX__MEMBERSHIP_RATIO_CLOCK_BALANCE.md` has exactly these
containing pair coefficients when a=ones. Its containing triples grow
only as M, permitted by(18), and its grand rewards grow only as M, also
permitted. That family's explicit finite-M formula is stronger on its
exact identities; the present theorem permits arbitrary signed higher
coalition coefficients on(18) and an open neighborhood of the containing
pair slopes. Its current candidate fixture comparisons remain independent
admission obligations, not hypotheses of this raw producer.

Nonvanishing in(16) is necessary for THIS nondegenerate-root argument,
not asserted necessary for equilibrium. If Gamma=0 and all higher data
vanish, L is identically0 and J=0, so the construction cannot invoke(21).
The original zero table nevertheless has every profile as an equilibrium.
Similarly failure of strict rate balance makes the displayed z* illegal
but does not imply any unrestricted exploitability gap.

Concrete next check: independently falsify the exact growth exponents,
signed determinant, compact-uniform contraction and full-cap consumer
before treating this stronger coefficient cone as admitted mathematics.

## 13. Global signed-pair selection by two different matrix degrees

Status: COMPLETE ORDINARY PROOF DRAFT, unreviewed. This is not just a
new name for the weighted account: its explicit C=Gamma calibration has
no strictly copositive nonnegative weighted account at all.

### 13.1 Raw theorem

Fix finite n>=2, arbitrary finite singleton rows, and their comparison
matrix Gamma with diagonal0. Fix ANY real matrix C with diagonal0.
Assume BOTH Gamma and -C are R0 and their ACTUAL minimum-map degrees differ:

    d_Gamma != d_(-C).                                     (22)

Neither degree must be nonzero individually. No inverse, positive column,
nonnegative quadratic field, weighted coercivity, selected root or root
Jacobian is an input. Require EITHER all own singleton rewards nonnegative
OR the singleton-exclusion condition

    for EVERY j there is k!=j with Gamma_kj<0 and C_kj>=0.   (23)

For EVERY finite R there is M0 such that EVERY M>M0 and EVERY raw table
with these fixed singleton rows and

    r_i({i,j})=s_i+M*C_ij+c_ij,        |c_ij|<=R;
    |r_i(S)|<=R                       if |S|=2, i notin S;
    |r_i(S)|<=R*M^(|S|-2)             if |S|>=3              (24)

has an actual stationary exact terminal Nash equilibrium against EVERY
complete behavioral replacement. Its hazard vector q=z/M has z in a
fixed compact annulus independent of M and all normalized residuals,
and every q_i<1. Under(23), at least two q_i are positive. Under the
nonnegative-own alternative a sole-active player is allowed and is
handled by its actual finite/Never cap. The SAME profile supplies one
fixed uniform-equilibrium payoff. All other reward signs are arbitrary.

The theorem is uniform on compact singleton/coefficient sets preserving
both R0 conditions and unequal degrees, with bounded own singletons and
fixed R. No quantitative threshold near a non-R0 matrix is asserted.

### 13.2 A quadratic minimum map with an exactly known degree

Define for z>=0

    s_-i(z)=sum_(j!=i)z_j,
    P_C,i(z)=s_-i(z)*(C*z)_i,
    N_C(z)=min(z,-P_C(z)).

The only zero of N_C is0. In fact its complementarity zeros coincide
EXACTLY with those of min(z,-Cz). If z has at least two positive
coordinates, every s_-i(z)>0, so multiplying each row by s_-i preserves
its sign and the active equalities. If z=a*e_j with a>0, every inactive
row has multiplier a>0, while the sole active row already has
(Cz)_j=C_jj*a=0. The potentially zero active multiplier therefore loses
no condition. The origin is a zero of both maps. R0(-C) proves isolation.

More precisely, use the ambient continuous homotopy

    K_u(z)=min(z,-diag((1-u)+u*s_-i(z))*Cz),     0<=u<=1.    (25)

Every zero of a minimum map has z>=0. On that orthant the preceding
support argument applies for EVERY u, so0 is the only zero of every K_u.
Thus on ANY ball around0, the degree of N_C is exactly d_(-C).
No proper-face determinant, positive inverse or root census is required.
Possible negative row factors away from the nonnegative orthant create
no zeros, since a negative coordinate of z already makes that coordinate
of min(z,...) strictly negative.

The degree identification used here is the literal ambient minimum-map
identification `ambientDegree_lcpMinMap_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0AmbientDegree.lean`, previously inspected.
The row-scaling homotopy(25) is ordinary mathematics, not a claim of a
new checked declaration.

### 13.3 Whole-orthant outer bound and inner degree

Consider ALL complementary roots of

    G_lambda(z)=lambda*Gamma*z-P_C(z),     0<=lambda<=1.     (26)

They are uniformly bounded. Otherwise normalize a sequence with
r_k=||z_k||->infinity by x_k=z_k/r_k and take a unit nonnegative cluster
x. Divide G_lambda>=0 by r_k^2 and the complementary equalities by the
same positive scale. Homogeneity of P_C and bounded lambda give

    -P_C(x)>=0,       x_i*P_C,i(x)=0.

This is a nonzero zero of N_C, contradicting13.2. The argument retains
inactive recipients and every proper support. On a sufficiently large
ball, (26) therefore homotopes the leading full map
min(z,Gamma*z-P_C(z)) to N_C without boundary zeros. Its OUTER degree
is d_(-C).

Near0, P_C=O(||z||^2). R0(Gamma), homogeneity and compactness of the
unit sphere give a positive lower bound for
||min(z,Gamma*z)||/||z||. Therefore the homotopy subtracting theta*P_C,
0<=theta<=1, has no zero on every sufficiently small sphere. The INNER
degree is d_Gamma. The leading annulus degree is consequently

    d_(-C)-d_Gamma !=0.                                  (27)

This proof does not need d_Gamma!=0, nor d_(-C)=0.

### 13.4 Exact finite scale and complete agency

The exact polynomial expansion is(19), so its NEGATIVE field is

    G_t(z)=Gamma*z-P_C(z)-t*E(t,z,c,e).

The normalized residuals from(24) form one finite compact box. The exact
minimum maps converge uniformly to the leading map on both fixed annulus
boundaries. Hence(27) persists for every sufficiently small positive t,
uniformly over all completions. An ACTUAL nonzero complementary zero
exists in the fixed annulus. Taking t small gives q=t*z in[0,1)^n.

Under(23), a hypothetical singleton leading zero a*e_j has inactive row

    G_k=a*Gamma_kj-a^2*C_kj<0,

impossible. Compactness of the annulus then excludes actual singleton
zeros at all small t. There are at least two proper geometric quitters,
so Section5 gives every player's full deadline/Never cap.

Under the nonnegative-own alternative, a singleton zero gives one proper
geometric player j against all-Never opponents. Its actual payoff and
every finite deadline payoff equal s_j>=0; Never pays0. Thus it is fully
optimal despite alpha_j=1. All other recipients have the proper opponent
j and their complementarity inequalities give complete caps as before.
Uniform finite-average transfer is exactly the separately checked
sole-active consumer in Section10. No saturated-coordinate inequality
is silently discarded.

Compact parameter uniformity follows by the same normalization
contradictions on both R0 conditions, compactness of the coefficient
sets, and the exact uniform polynomial remainder. The degrees are locally
constant on R0 sets; unequal degrees stay unequal on the compact source
set under consideration. Bounded own singletons remain essential.

### 13.5 Exact discriminators

For C>=0 with every column nonzero, -C is R0. It cannot be standard Q:
offset-minus-ones would require C*z<=-ones, impossible. Since nonzero
R0 degree implies standard Q, d_(-C)=0. This recovers the earlier
nonnegative-pair outer-degree calculation without a cycle selection.

For the paired-hard singleton matrix

    Gamma=[0,3,-1,-1;3,0,-1,-1;-1,-1,0,3;-1,-1,3,0],

take C=Gamma. Both Gamma and -Gamma are R0: every nonsingleton principal
block is nonsingular, and every column of each matrix has a negative
external entry. The earlier tracked matrix theorem gives d_Gamma=1.

For -Gamma, use offset ones. The ONLY strictly complementary roots are:

    empty:                     index+1;
    support01: z=(1/3,1/3,0,0), index-1;
    support23: z=(0,0,1/3,1/3), index-1;
    full:      z=(1,1,1,1),     index+1.

Singleton roots are impossible. A harmful cross-pair has positive entries
in -Gamma and cannot solve its offset equation with positive atoms.
For any triple, its mate-pair atoms solve to-1/2 and so are illegal.
The displayed inactive residuals at both mate roots are5/3>0.
Thus the ACTUAL support-sum degree is1-1-1+1=0. This calculation uses
sign(det(-Gamma)_CC), with NO extra active-cardinality sign. Consequently
(22) holds although Section12.5 proves that EVERY weighted quadratic
copositivity account fails for this C. It is a genuine extension of that
global account, not a better choice of its weight.

Conversely take C=-Gamma for ANY R0 Gamma. Then -C=Gamma has the SAME
degree and the leading residual factors as

    G_i(z)=[1+s_-i(z)]*(Gamma*z)_i.

Every multiplier is strictly positive on the nonnegative orthant, so the
ONLY complementary leading zero is0. This exact falsifier shows that
some genuinely different outer information is necessary; signed large
pair rewards alone do not force a nonzero leading root. It is not a UE
counterexample or a claim excluding finite-scale boundary effects.

### 13.6 Matrix-free Fin4 consequence and current check

Fix ANY C for which -C is R0 and d_(-C)!=1, and fix ANY nonnegative
own-singleton data and arbitrary passive singleton coordinates. Then
every sufficiently large raw family(24) has a uniform-equilibrium payoff,
without a singleton-matrix premise. Indeed bare Fin4 no UE supplies full
R0 Gamma of degree1 through the actual declarations in Section7; the
present theorem contradicts that no-UE premise on its residual branch.
The threshold on the residual branch is fixed from the singleton/C data,
not selected after a completion or after a no-UE witness. On other matrix
exits the previous unconditional consumers apply. Only the residual branch
is asserted to produce this stationary equilibrium.

Requested bounded falsification: the zero-equivalence and row homotopy(25),
the uniform outer normalization including singleton supports, the actual
degree orientation/census and exact finite-scale/full-agency transition.
No independent PASS, Lean implementation or export admission is claimed
for this new section.
