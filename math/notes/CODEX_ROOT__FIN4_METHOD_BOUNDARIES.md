# Full-cap source constraints and exact proof boundaries

Maintainer: `CODEX_ROOT`. Ordinary mathematics, not a new Lean verification.

## Status and role

The rigorous method boundaries below guide the parallel attack in the
[coverage map](CODEX_ROOT__FIN4_COVERAGE_MAP.md). Neither closes a reward
class or a Fin4 capstone. The first controls arbitrary finite and infinite
homogeneous paths, beyond a bounded search for expanding words. The second
shows why two pair–triple certificates cannot spend their shared pair index
twice, even with the old full-support orientation premise.

The later sections add an actual boundary-source constraint from stationary
security and a sound shared-anchor criterion whose additional coverage beyond
older methods remains unestablished. These distinctions are kept explicit.

These are internal research results. Complete behavioral deviations and
actual source provenance remain necessary for any UE conclusion. In
particular the linear paths below are tangent systems, not actual strategies.

## 1. A global activity bound for homogeneous Nash paths

Let Gamma be a real four-by-four matrix with zero diagonal. At phase t choose
arbitrary b_i^t>1, q^t>=0 and w^t, satisfying

    c^t=w^t+diag(b_i^t) Gamma q^t>=0,
    q_i^t c_i^t=0,
    w^(t+1)=w^t+Gamma q^t.                         (1)

For fixed b_i this is the first-order native Nash-prefix system with
singleton matrix Gamma and participant matrix
J=diag(alpha_i)Gamma, alpha_i=1-b_i<0. The q coordinates are tangent
hazards, with no artificial probability upper bound.

Put v=(1,1,0,1), u=(1,10,14,0), a=(95,46,127,170),
a_T=(37,34,50), and T={1,2,3}. Consider the following explicit open
polyhedral region of zero-diagonal Gamma matrices; rows are denoted Gamma_i:

1. Gamma20,Gamma03,Gamma30,Gamma21,Gamma13,Gamma32>0 and Gamma31<0.
2. a^T Gamma>0 and a_T^T Gamma_TT>0 coordinatewise.
3. (v^T Gamma)_j<-1/8 for j in{0,1,2}.
4. (v^T Gamma-(11/8)Gamma_0-(19/24)Gamma_1)_j<-1/8
   for j in{0,1,3}.
5. (u^T Gamma+43 Gamma_3)_j<-1/8 for j in{0,1,3}.

This region is nonempty. An exact interior point is

    G=[ 0,-2,-5, 4;
       -6, 0,-4, 6;
        1, 3, 0,-5;
        1,-1, 4, 0].

At G the products in condition2 are21 times the four-vector of ones and52
times the three-vector of ones. Conditions3–5 have, respectively, entries
(-5,-3,-5), (-1/4,-1/4,-1/4), and(-3,-3,-6).

**Theorem.** For every path(1) with w^0>=0, finite or infinite, and every
Gamma in this region,

    sum_t sum_i q_i^t <=112 ||w^0||_1.               (2)

The bound is uniform in phase count and in all row factors b_i^t>1.

### Proof

Write theta_i^t=1-1/b_i^t in(0,1). The exact identity

    w_i^(t+1)=theta_i^t w_i^t+c_i^t/b_i^t            (3)

preserves nonnegativity. A positive coordinate stays positive. An active
coordinate has (Gamma q)_i=-w_i/b_i<=0.

The only possible nonsingleton active supports are01 and013. For the other
pairs02,03,12,13,23, condition1 supplies a strictly positive active row,
contradicting Gamma_SS q_S<=0. It does the same for triples012 and023.
The positive left witnesses in condition2 exclude123 and full support.
A singleton j requires w_j=0, since Gamma_jj=0.

Put V=v dot w=w0+w1+w3 and W=u dot w=w0+10w1+14w2.
For a regular phase supported on01 or013, both rows0 and1 satisfy
Gamma_i q<=0. Subtracting the positive multiples of those rows in condition4
therefore proves

    Delta V<=-(sum_i q_i)/8.                        (4)

Condition3 gives the same estimate for singleton phases0,1,2. When w3>0,
singleton3 is impossible, so(4) holds for every phase.

If w3=0 and remains zero after the phase, (3) gives Gamma_3 q=0.
Singleton0 or2 would make that coordinate positive, and singleton1 would
make it negative. Thus q2=0 and the support is contained in013. Condition5
then gives

    Delta W=(u^T Gamma+43 Gamma_3)q<=-(sum_i q_i)/8.  (5)

If a phase leaves the face w3=0, then q3=0: activity at coordinate3 would
keep it zero by(3). Such a phase is covered by(4). On the face V<=W.
Consequently the nonnegative, positively homogeneous function

    Psi(w)=8W(w) if w3=0, and8V(w) if w3>0

decreases by at least sum_i q_i at EVERY phase, including the first face
exit. The face cannot be reentered. Telescoping proves(2), since
Psi(w^0)<=112||w^0||_1. Taking suprema of the finite partial sums proves
the infinite-path assertion. At G directly, (4) improves to a factor1/4,
and the analogous potential4W/4V gives the bound56.

### Signed paths with bounded row factors

The signed case also has a global budget. Add the strict linear condition
(u^T Gamma)_2<-1/8, which holds at G with value-45, and fix B>1 with
1<b_i^t<=B at every phase. Define

    r=min_j(a^T Gamma)_j, r_T=min_j(a_T^T Gamma_TT)_j,
    C_V=max(0,(v^T Gamma)_3+1/8),
    C_W=max(0,(u^T Gamma)_1+1/8),
    D=max{13/6,C_V/Gamma03,C_V/Gamma13,C_W/Gamma21,
          438C_V/r,121C_V/r_T,438C_W/r,121C_W/r_T},
    E=max(8D,200).

All denominators are strictly positive. For EVERY signed initial state and
every finite or infinite path(1),

    sum_t sum_i q_i^t
       <=112||w^0||_1+EB||(w^0)^-||_infinity.       (8)

Here x^- is its coordinatewise negative part. Thus arbitrary signed seeds
tending to zero cannot reach a fixed nonzero amplitude by homogeneous
switching, with Gamma and B fixed.

To prove this, put theta=1-1/B and delta_t=||(w^0)^-||_infinity theta^t.
Equation(3) gives w_i^t>=-delta_t. The nonnegative support catalogue alone
is insufficient now; the following estimates cover ALL fifteen nonempty
supports. Write Q=sum q and delta=delta_t for one phase.

| State / support | Bound controlling the exceptional activity |
| --- | --- |
| Any full support | Q<=438delta/r, by the positive left witness and active equations |
| Support123 | Q<=121delta/r_T, by its left witness |
| w3>0, q3=0 | All coefficients of v^T Gamma on the support are below-1/8 |
| w3>0, support03 or13 | q3<=delta/Gamma03 or delta/Gamma13, respectively |
| w3>0, support013 | Condition4 and active rows0,1 give Delta V<=-Q/8+(13/6)delta |
| w3>0, support3,23 or023 | Impossible: the active coordinate3 equation has a positive left side |
| w3<=0, q2=0 | Gamma_3 q>=0; condition5 gives Delta W<=-Q/8 |
| w3<=0, q2>0, q1=0 | All coefficients of u^T Gamma on0,2,3 are below-1/8 |
| w3<=0, support12 or012 | Active row2 gives q1<=delta/Gamma21 |

For the full and123 cases, multiply Gamma_SS q_S<=delta one by their
positive witnesses. The sums of witness coordinates are438 and121.
All other exceptional positive coefficients are bounded by C_V q3 or
C_W q1. This proves Delta V<=-Q/8+Ddelta when w3>0 and
Delta W<=-Q/8+Ddelta when w3<=0.

Use Psi=8W on w3<=0 and8V on w3>0. A phase leaving the former halfspace
has q3=0, so Delta V<=-Q/8; moreover V-W=-9w1-14w2+w3<=23delta there.
Its potential change is at most-Q+184delta. A positive coordinate3 never
returns to the other halfspace. Consequently every phase satisfies

    Psi(w^(t+1))<=Psi(w^t)-Q+E delta_t.

We have Psi(w^0)<=112||w^0||_1 and Psi(w^T)>=-200delta_T. Summing the
geometric errors gives
Q_total<=112||w^0||_1+200delta_0 theta^T+EB delta_0(1-theta^T),
which implies(8) since EB>=200. Infinite partial sums obey the same bound.

### What this excludes, and what it leaves

No positive-activity finite word in(1) can return w^L=lambda w^0 for
lambda>=1, even if w^0 was not initially assumed nonnegative. Iterating(3)
gives(lambda-product_t theta_i^t)w_i^0>=0, hence w^0>=0. Positive
homogeneity of Psi and its strict activity charge then give a contradiction.
Equation(2) also controls arbitrary nonperiodic switching with unbounded
phase counts; this is stronger than excluding expanding eigenwords.
In particular ||w^L||_1<=(1+112||Gamma||_(1 to1))||w^0||_1:
vanishing nonnegative seeds cannot reach a fixed nonzero amplitude by
arbitrarily lengthening these homogeneous paths.

This is not a Lyapunov function for the full actual-source problem. Psi has
an upward discontinuity on the face w3=0. A compact-limit regeneration at
that face may change its value. Nonlinear higher-order terms may also cross
faces that(3) makes invariant. Neither operation is charged by this theorem.
The signed extension controls exact homogeneous trajectories, not nonlinear
or approximate-root errors accumulated along actual source changes.

For the exact matrix G,

    det G=42,
    42 G^-1=[52,17,62,82;76,41,110,136;
              6,6,12,24;56,28,70,98]>0.

In fact every Gamma in the polyhedral region is R0. A nonzero x>=0 with
Gamma x>=0 and x perpendicular to Gamma x would be a legal phase from
w=0, choosing q=x and b_i=2, contradicting the zero activity budget.
The region is convex and contains G, so R0 homotopy invariance gives
complementarity degree1 throughout it, and nonzero degree gives standard Q.
At G the degree is computed at offset-minus-ones: positive inverse forces
the unique solution x=G^-1 one>0, with index sign(det G)=1.

Thus J=diag(alpha_i)G, alpha_i<0 independently, passes the full scalar-pencil
inverse-positivity test: G-tJ=diag(1-t alpha_i)G for0<=t<=1. The matrix
family can vary in an open neighborhood of G while retaining the budget
and positive inverse. It is lower dimensional in the full pair-data space:
row proportionality imposes relations between Gamma and J. The stronger
pencil-resultant genericity in the global least-Never export fails because
principal pencil determinants share the row factors1-t alpha_i.
Positive row scaling preserves R0, degree and Q, so every such row-negative
pencil throughout the polyhedral region passes those three tests as well.

For G, the participant-positive graph has only edge01. Its two joining
entries are positive, so no pair–triple anchor satisfies(F2), which requires
both anchor joins negative. Any completion outside the map's S5 registry
therefore lies in `R_F` or `R_T`, not `R_O` or `R_S`. All other reward
coordinates remain arbitrary for this method obstruction; no A_Z>0 or
absence of UE is asserted for any completion.

The earlier finite-word clock producer is in
[negative participant boxes](../exports/NEGATIVE_PARTICIPANT_BOX_EXCLUDES_ALLNEVER.md).
The unresolved nonmatching proportional ray is recorded in Section19 of
[bounded crossing](CODEX_COORDINATOR__BOUNDED_CROSSING_SELECTION.md).
The new activity bound excludes using arbitrary homogeneous switching to
repair that particular producer on the displayed region. Finite-amplitude
or nonlinear source constructions remain legitimate targets.

## 2. The shared-anchor arm has only two graph shapes

Use the FULL(F1)–(F3) hypotheses in
[pair–triple cancellation](../exports/PAIRED_SUPPORT_INDEX_CANCELLATION_UNIFORM_EQUILIBRIUM.md).
Suppose required triples012 and023 both use anchor02. F1 implies
J02,J20>0, T1=Z1(012)>0, T3=Z3(023)>0, and both directed participant
entries on01,03,12,23 are nonpositive. Hence the participant-positive graph
has just edge02 or the matching{02,13}.

Full support cannot pass Low. At odds x=z=L,y=t=0 its Quit numerators are

    R0=J02 L, R2=J20 L,
    R1=(J10+J12)L+T1 L^2,
    R3=(J30+J32)L+T3 L^2.

All are positive for sufficiently large finite L, and remain so for small
positive y,t. Full support cannot pass Charge either: its middle coefficient
at02 is T1+T3>0. Thus the map's entire `R_S` arm uses full support
**Orientation**. The other nine graph shapes and both other full-support
gates cannot contribute to this arm.

Under A_Z>0, both anchor columns must also receive positive joining pressure
from a central owner:

    max(L10,L30)>0 and max(L12,L32)>0.                (6)

Otherwise, since F2 already gives L20,L02<0, a pure sure anchor owner is
absorbing Nash against every behavioral deviation, with native debt zero.
This proves(6) under the positive-gap hypothesis. It need not hold for every
point of the conservative R5 queue, which can retain older solved games.

## 3. Complete shared-anchor gates can have only bad boxed roots

This exact countermodel retains the full raw support gates and positive
incoming anchor pressure. It rules out a universal boxed good-root
replacement based on those premises alone. The actual payoff-domain
theorem already solves its game; excluding all S5 games is an additional
hypothesis that this example does not refute.

### Complete bounded game

Players are cyclic0,1,2,3. Native own singletons vanish. Fix T=4/3 and
cyclic singleton and participant-pair rows

    Gamma0=(0,-1,3,-1), J0=(0,-2,2,-3/4).

Every passive pair/triple entry is T+1=7/3; every participant triple and
grand entry is T. These rules specify all60 native rewards Z, bounded
in absolute value by3 and below by-2. Live/Never pay zero.

The joining gaps have cyclic row(0,-1,-1,1/4); every higher joining
gap is-1. Thus the only participant-positive pairs are02 and13, with
negative joining gaps in both directions. For a repeated anchor02,
the positive central incoming gaps are d10=d32=1/4, so the previously
derived positive-gap pressure condition is satisfied.

Each of the four triples admits Pair--Triple(F1)--(F3), assigned to its
favorite pair. For012 in roles(0,1,2): alpha=-1,beta=gamma=-1,eta=1/4,
B0=B2=-1, central participant T1=4/3, and K=2/T=3/2. Its central map
and quiet map are

    f=x/4-z-xz,
    g=-x-y+z/4-xy-xz-yz-xyz.

The cleared F3 polynomial with lambda=0 and x=K+u is

    H=(1+y)(1+z)[(1+y)u+(K-1/4)y+K-3/2]>=0.       (1)

Cyclic rotations give the other three certificates. F1--F2 are literal
signs of the displayed table; K>=1/4. Thus the only missing old paired
premise is distinctness of anchors: both pairs are used twice. These
certificates have zero tilts, so the reciprocal product gate does not apply.

### Full global strict Orientation

We prove the stronger statement for every0<T<=4/3 in this same family.
Put w=(x,y,z,t), S=sum w_i. The full Quit numerators satisfy

    sum_i R_i=-(3/4)S+T[2 sum_pairs w_iw_j+sum_triples w_iw_jw_k].

If P=product_i(1+w_i)<=25/16, then S<=9/16. Cauchy gives
2 sum_pairs<=3S^2/4, and expansion of S^3 gives sum_triples<=S^3/6.
Consequently

    sum R_i <= S[-3/4+(4/3)(3S/4+S^2/6)]
             <=-(15/128)S<0

for S>0. Thus all R_i>0 forces P>25/16.

Let v_i=1+w_i and c_i=(5/4)/(v_{i+1}v_{i+2}), with cyclic indices.
Positive diagonal row/column scaling of D Phi gives

    N=I-11^t+diag(c_i)C,

where C is the cyclic predecessor permutation. Precisely det D Phi=P^2
det N. Write d=c0*c2=c1*c3=(25/16)/P<1 and q=sqrt(d) in(0,1).
Since0<c_i<=5/4, the sums a=c0+c2,b=c1+c3 belong to

    [L,U]=[2q,5/4+4q^2/5].

Direct determinant expansion reduces to

    det N=(d+1)(a+b)-ab-d^2-3.

This is bilinear in a,b, so its maximum on[L,U]^2 is at a corner.
The three corner values are

    F(L,L)=-(q-3)(q-1)(q^2+1)<0,
    F(L,U)=-(q-1)(4q^3-4q^2-45q-35)/20<0,
    F(U,U)=-(16q^4-840q^2+825)/400<0.

For the last inequality the numerator decreases on[0,1] and is1 at1.
Hence det D Phi<0 wherever all full Quit premiums are positive. This is
the complete strict GLOBAL full-support Orientation premise.

### All seven Nash roots at the boxed source are bad

Use native annotation v=(-5,-5,-5,-5).

**No sure roots.** With two sure owners, one has a negative reciprocal
singleton joining gap toward the other; all higher joining gaps are-1,
so it strictly prefers Continue. Three or more sure owners also fail.
With exactly one sure owner h, every other owner except h+1 has a
negative conditional joining gap and must Continue. Owner h+1 then faces
only h and has gap1/4>0, so must Quit surely, contradiction.

AllContinue and singleton supports cannot be roots at v<0. No adjacent
pair can solve its two negative active annotations, because one joining
gap is positive. Each favorite pair has its unique root with both odds5.
Their quiet inequalities are strict. Active successor outputs are5/3,
and each quiet successor has positive numerator

    (T+1)*25-3*5=130/3>0.

Both pair roots are bad and have index-1.

**Exactly one root on each triple.** On012 the anchor equations give

    x=(5+y/4)/(1+y), z=(5-y)/(1+y).

The remaining equation is

    101y^2+177y-380=0.                              (2)

It has exactly one positive root, with5/4<y<63/50. The resulting bounds
are47/20<x<12/5 and33/20<z<5/3. They imply all active Quit numerators
are positive; in particular

    R1=(4/3)xz-(3/4)x-2z>43/400>0.

Both anchor derivatives along the fiber are negative, and f_x=1/4-z<0,
f_z=-1-x<0. Thus f'>0 and the triple's ambient index is+1.

Its quiet map is
Phi3=-x-y+z/4-xy-xz-yz-xyz<-5, so the quiet test is strict. The quiet
Continue numerator is

    -x+3y-z+(7/3)(xy+xz+yz+xyz)-5
      >-12/5+15/4-5/3+(7/3)(47/20)(33/20)-5
       =4477/1200>0.

Hence all four successor coordinates are positive. Cyclic rotation gives
the other three unique triple roots, also bad and of index+1.

**Exactly one full root.** For v_i=1+w_i and P=product v_i, the full
equations Phi_i=-5 are

    P/v_i-(5/4)v_{i-1}=19/4.

Thus the four v_i form a period-four orbit of f(s)=P/(19/4+(5/4)s).
The map f^2 is increasing, so a period-two point of f^2 must be fixed.
The equation f^2(s)=s reduces to one quadratic with exactly one positive
root, which also solves f(s)=s. Therefore all four odds equal u.
The unique uniform equation is

    u^3+3u^2+(7/4)u=5,

with9/10<u<1. Its Quit numerators are
u[-3/4+(4/3)u(3+u)]>0. Thus it is bad, and the full-support calculation above gives index-1.

This exhausts every support and sure boundary. There are exactly seven
roots, all proper, regular and bad. Their total index is

    2*(-1)+4*(+1)+(-1)=+1,

as required by full cube degree. Each shared pair/triple bundle has
index+1; the full root cancels only one unit of the total shared excess.

### Stationary profiles also have a strict gap

This family has no absorbing stationary equilibrium for ANY fixed T>=0,
so the raw shared-anchor premises do not imply a stationary producer.
Here are exact reductions to the already-exported cyclic stationary proof.

The sure-root argument above excludes sure profiles. A nonzero singleton stationary
support h is defeated by h+1: its Never payoff is-1 and its immediate
Quit payoff is-(3/4)q_h>-1. On an adjacent proper stationary pair the
two necessary hazards are Gamma_ij/J_ij, one of which is4/3>1. On a
favorite pair both necessary hazards are3/2>1. Thus no pair works.

For a triple012 put D_i=product_{j in support-i}(1+w_j), let R_i and P_i
be its Quit/passive odds numerators, and E_i=(D_i-1)R_i-D_iP_i. Every
active stationary owner must have E_i=0. Direct expansion gives

    E0=y-y^2-3z-z^2-(T+3)yz-2y^2z-2yz^2-y^2z^2,
    E1=x+z+x^2/4-z^2-3x^2z/4-2xz^2
                         -(T+7/4)xz-x^2z^2.

E0=0 implies3z<y-y^2<=1/4, so z<1/12. But the exact identity

    4(yE1-xE0)=x^2y(1-3z-4z^2)+4xy^2(z+1)^2
                        +5xyz+4xz(z+3)+4yz(1-z)>0

then contradicts E0=E1=0. Every triple is a cyclic rotation.

For full support compare the original cyclic favorite-pair table of
[the cyclic favorite-pair proof](../exports/CYCLIC_FAVORITE_PAIRS_UNIFORM_EQUILIBRIUM.md), Section4, at the same T. Its
singleton/passive rewards are identical. Only participant-pair entries
have decreased: the next-owner entry by1/2 and the previous-owner entry
by1. Hence for every full proper odds vector

    E_i(new)=E_i(old)-(D_i-1)(w_{i+1}/2+w_{i-1}).

The old exported complete positive-coefficient identity says sum_i E_i(old)<0.
Thus sum_i E_i(new)<0, excluding every full proper stationary profile.

This exclusion includes approximate stationary profiles. At a nonzero
limiting hazard, payoff is continuous and full caps are lower
semicontinuous (suprema of continuous finite-deadline responses), so
vanishing stationary debt would give an excluded Nash profile. At
hazards tending to0, normalize p=q/sum q. Its limiting native payoff is
w=Gamma p. Immediate Quit gives w>=0; a singleton p is impossible since
its Gamma column has negative entries. Every p_i<1 then has limiting
Never-response value w_i/(1-p_i), forcing p_iw_i=0.

The unchanged Gamma has strictly positive inverse

    Gamma^-1=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2].

If w!=0, p=Gamma^-1 w is strictly positive, so complementarity forces
w=0, contradiction. If w=0, p=0, also impossible. Hence nonzero native
stationary profiles have a strictly positive debt infimum for each fixedT.
They all absorb; original Z+one shifts each prescribed payoff and full
finite-deadline cap by1, so their debts are unchanged. Original AllNever
has total debt4. Thus Z+one has a strict gap over ALL stationary profiles.
No unrestricted behavioral gap or uniform constant across unboundedT is
inferred.

### Precise implication falsified and actual payoff frontier

For original rewards r=Z+one the reward bound is M=4. The corresponding
original annotation is v+one=(-4,-4,-4,-4), strictly inside every boxed
source region[-B,B]^4 with B>4. All original successor outputs exceed
their own singleton1. Thus this is an exact falsifier to the proposed
GLOBAL BOXED selector obtained by dropping distinctness in the old
paired theorem, even while retaining full Orientation and the incoming
pressure condition. The universal conclusion A_Z=0 is not falsified.

In fact this entire game is already solved by payoff-hull Orientation.
H has coordinate floor-2. At a high012 triple with active source in the
projection of H, the two anchor equations imply x,z<=2. But positive
central Quit requires

    T>(3/4)/z+2/x>=11/8>4/3,

impossible. All other triples are cyclic rotations. Favorite pairs have
negative index, adjacent high pairs are impossible, and the full-support calculation above handles
full support. The singleton matrix is invertible (the unchanged Gamma
has determinant45), so the hull adapter has the required interior.

Consequently native absorbing debt zero and original UE follow from an
OLD raw theorem; its equilibrium approximations must be nonstationary at
sufficiently small error, by the stationary argument above.
The bad source(-5)^4 is outside the actual reward hull
(floor-2), and hence outside N1. This countermodel closes a proposed
global-selector route, not a reward class or an actual positive-gap source.
Any remaining R_S closure must use actual payoff/cap geometry or another
genuinely global mechanism; full raw gates and boxed root counting alone
cannot supply that closure. An argument deducing stationary existence from
these raw gates is false as well. This does not contradict a theorem using
the additional exclusion of ALL S5 games: the present game is in S5.

## 4. Security floors separate attained and unattained boundary sources

For a native table suppose, for every owner i, some a_i>0 satisfies

    Z_i(T+i)+a_i Z_i(T)>=0 for every nonempty T excluding i. (S)

Hazard p_i=1/(1+a_i) gives a legal unilateral strategy guaranteeing
nonnegative payoff against every complete opponent law. Its conditional
absorption payoff is p_i[Q_i+a_i P_i]>=0 at every date; its own positive
hazard ensures absorption. AllContinue opponents give upper value0.
Thus every actual full cap, and its closure limits, is nonnegative.
In particular no negative-payoff zero-debt source is possible on(S).

This is an application of the existing stationary-security mechanism, not a
new security producer: see `deadlineWithdrawalSecurityRow` and
`DeadlineWithdrawalSecurityFeasible`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`),
and `deadlineWithdrawalSecurityRestartLaw_terminal_floor`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityPayoff.lean`).
These code interfaces use child indices; the direct argument here is for the
native full game and does not claim a new Lean adapter.

There is a stronger source consequence when all comparisons in(S) are strict
and Gamma is R0. Put theta_i=a_i/(1+a_i) and
kappa_i=min_T[Z_i(T+i)+a_i Z_i(T)]/(1+a_i)>0. If tau is the opponents'
first finite quitting date, the same legal strategy gives

    B_i>=kappa_i E[theta_i^tau 1_(tau finite)].       (9)

Indeed own earlier Quit pays0, survival until tau has probability
theta_i^tau, and the conditional mixture at tau pays at least kappa_i.

If an ACTUAL cap B_i=0, (9) forces all opponents to Never. If its own
finite probability f were positive, R0 supplies j!=i with Gamma_ji<0:
otherwise the nonnegative column Gamma e_i would make e_i a nonzero
homogeneous complementary vector. Owner j's Never reply is then
e_j=f Gamma_ji<0, while its cap is nonnegative by(S). Hence an actual
ALL-END profile, meaning B=e at every coordinate, with any zero cap must
be AllNever. A full Nash profile with any zero payoff must likewise be
AllNever, since that Never-playing j would have negative prescribed payoff.

Consequently any other ALL-END zero-cap closure point is unattained.
The statement applies to inherited ALL-END endpoints as well as zero-debt
sources; it does not identify either with a global minimizer.
Moreover (9) gives
Pr(tau<=K)<=B_i/(kappa_i theta_i^K). Along any realizing sequence whose
limit has TWO zero caps, every owner's finite stopping probability before
each fixed K tends to0. Original Never probabilities need not tend to1:
finite mass can escape to moving dates. That unrealized continuation is the
remaining seam, not an actual strategy produced by this bound.

## 5. Reciprocal tilts permit one shared pair budget

Use all FULL raw tests of the
[pair–triple theorem](../exports/PAIRED_SUPPORT_INDEX_CANCELLATION_UNIFORM_EQUILIBRIUM.md).
Its requirement of distinct assigned pairs can be replaced by this sufficient
condition: whenever both triples containing one pair use that pair, their
fixed nonnegative F3 witnesses lambda,mu have lambda*mu>=1. All other
support, pair and full-support premises are retained.

Here is the complete new index step. At a generic fixed source under the
all-bad contradiction, label a repeated pair02 and its central owners1,3.
If either triple has a root, F2 gives the same unique positive pair anchor.
Let f0,g0 be the two quiet offers there, b,d the source coordinates, and
B=b-f0,D=d-g0. If the pair is a full Nash root, B,D>0. A012 root has
f=b and quiet g<d. Integrating F3 along its entire positive-Quit fiber back
to the pair gives D>lambda B. A023 root similarly gives B>mu D.
Both cannot occur when lambda*mu>=1. Strict quiet comparisons also cover
the equality case.

For either individual family, the old scalar crossing calculation says
its index sum minus1_(pair present) is nonpositive. In detail, monotonicity
of g-lambda f retains an initial interval of quiet-admissible roots, whose
scalar index sum is1_(f(cut)>b)-1_(f0>b). If a triple exists and b>f0,
its tilted quiet guard forces g0<d, so the pair is indeed a full Nash root.
If b<f0, it is absent and the scalar sum is nonpositive. Source genericity
excludes equality; no triple exists without a valid positive pair anchor.

Thus when the pair is absent both sums are nonpositive. When it is present,
at most one family occurs and spends its index-1 once. Each repeated group
has nonpositive total index. Groups partition the assigned triples, even
with two repeated anchors in a matching. All other support counts, degree+1
contradiction, generic limits and actual full-cap UE/A_Z=0 consumer of the
old theorem are unchanged. This proves the sufficient criterion.

This proof has not established a new UE class beyond the full older atlas.
Prospective separating examples defeated the conservative S5 tests but
admitted exact mixed stationary equilibria. Enlarging the claimed coverage
on that basis would double-count already solved games. The criterion stays
internal; no whole `R_S` closure or export admission follows from it.

## 6. Penalty-scale errors do not supply chronological progress

On the compact actual carrier C let d_i=B_i-U_i>=0, E={d=0},
alpha=min_E nu, and

    mu_p(r)=min_{X in C, d_i=0 for i!=p}(d_p+r nu), r>0.

An alpha-minimizer is feasible, so mu_p(r)<=r alpha. Every choice of
minimum Y_r has d_p(Y_r)<=r alpha and nu(Y_r)<=alpha. Its cluster points
belong to E; hence uniformly over these choices,

    nu(Y_r)->alpha, mu_p(r)/r->alpha, d_p(Y_r)=o(r).

Put f(r)=mu_p(r)/r. Testing the minimum at2r on Y_r gives
mu_p(2r)<=2mu_p(r)-d_p(Y_r), and therefore

    d_p(Y_r)/r<=2[f(r)-f(2r)].

For any R>0 and r_n=R/2^n, summation gives
sum_(n>=1)d_p(Y_(r_n))/r_n<=2[alpha-f(R)], which tends to0 as R tends to0.
This is an exact budget over prices, not over dates of one play.

An improvement cr over the selected objective requires a fixed positive
Never release: nonnegative pivot debt gives nu(new)<=mu_p(r)/r-c.
An o(1) Never change can improve the objective only by o(r). Thus this
normalization does not turn local head corrections into the missing global
move. Nor are minima at different prices successor-linked sources. A
chronological construction preserving those fields remains unproduced.
