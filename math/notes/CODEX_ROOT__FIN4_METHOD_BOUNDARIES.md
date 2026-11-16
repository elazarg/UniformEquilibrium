# Full-cap source constraints and exact proof boundaries

Maintainer: `CODEX_ROOT`. Ordinary mathematics, not a new Lean verification.

## Status and role

The rigorous method boundaries below guide the parallel attack in the
[coverage map](CODEX_ROOT__FIN4_COVERAGE_MAP.md). Neither closes a reward
class or a Fin4 capstone. The first controls arbitrary finite and infinite
homogeneous paths, beyond a bounded search for expanding words. The shared-anchor calculations
show why two pair–triple certificates cannot spend their shared pair index
twice, even with the old full-support orientation premise. Both surviving
participant-graph shapes admit boxed countermodels.

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


## 7. A single positive pair also defeats the boxed selector

The single-edge arm does not force a good boxed face or a missing full-root
cancellation. Here is a second exact countermodel, complementary to the
matching model in Section3. Put T=4/3 and use the complete native table:

| S | Z0 | Z1 | Z2 | Z3 |
| --- | ---: | ---: | ---: | ---: |
| 0 | 0 | -1 | 3 | -1 |
| 1 | -1 | 0 | -1 | 3 |
| 2 | 3 | -1 | 0 | -1 |
| 3 | -1 | -1/100 | -1 | 0 |
| 01 | -2 | -3/4 | 7/3 | 0 |
| 02 | 2 | 7/3 | 2 | 7/3 |
| 03 | -3/4 | 0 | 7/3 | -2 |
| 12 | 7/3 | -2 | -3/4 | 0 |
| 13 | -2 | -101/100 | -2 | 2 |
| 23 | 7/3 | 0 | -2 | -3/4 |
| 012 | 4/3 | 4/3 | 4/3 | 0 |
| 013 | -1 | -1 | 7/3 | -1 |
| 023 | 4/3 | 0 | 4/3 | 4/3 |
| 123 | 7/3 | -1 | -1 | -1 |
| 0123 | 4/3 | -1 | 4/3 | -1 |

The sole positive participant pair is02. In proper odds(x,y,z,t), joining
polynomials are

    Phi0=-y-z+t/4-yz+yt-zt-yzt,
    Phi1=x/4-z-t-xz-xt-zt-xzt,
    Phi2=y/4-x-t-xy+yt-xt-xyt,
    Phi3=-x-y+z/4-xy-xz-yz-xyz.

Both anchors have positive incoming pressure1/4. The unused triples013,123
are Low. The two anchored triples012,023 satisfy all full pair–triple
premises with K=3/2,lambda=0. For012 the active/quiet polynomials are
f=x/4-z-xz,g=Phi3. With x=K+u, the cleared F3 polynomial is

    (1+y)(1+z)[(1+y)u+(K-1/4)y+K-3/2]>=0.

The023 certificate is the rotation by two. The F1–F2 data are
alpha=beta=gamma=-1,eta=1/4,B0=B2=-1,J02=J20=2,
J01=-2,J21=J10=-3/4,J12=-2,T1=4/3; these give all signs and thresholds.

Full high-Quit implies x,z>3/2 and0<y,t<4/3. Indeed
R1=(T-t)xz-3x/4-2z-t(x+z+101/100)>0 gives t<T,x>3/2,z>9/16.
Then R3=(T-y)xz-2x-3z/4+y(2-x-z)>0 gives y<T,z>3/2.
For u=x-3/2,v=z-3/2 the exact determinant expansion is

    -det D Phi=P00+u A(y,t)+v A(t,y)+u² B(y,t)+v² B(t,y)
                     +uv C+(u²v+uv²)D+u²v² E,
    A=25/64[48t²y²+148t²y+94t²+148ty²+380ty+223t
                                    +118y²+271y+150],
    B=5/16(1+y)[28t²y+34t²+62ty+71t+42y+45],
    C=5/16[112t²y²+256t²y+141t²+256ty²+576ty+314t
                                    +141y²+314y+170],
    D=(1+y)(1+t)(44ty+47t+47y+50)/4,E=3(1+y)²(1+t)²,
    P00=125/256[-16t²y²+48t²y+68t²+48ty²+200ty
                                    +180t+68y²+180y+125].

Every coefficient is positive except the first monomial of P00, which
combines with48t²y to give16t²y(3-y)>0. This proves GLOBAL Orientation.

At v=(-5)^4 every root is proper. Sure0 forces2 and3 Continue, then1
Quit, making0 prefer Continue; sure2 rotates this. Sure1 forces3 and0
Continue, then2 Quit; sure3 rotates this. AllContinue and singletons fail.
Adjacent pairs have opposite joining signs. Pair13 would have odds5,5 but
its quiet0 joining offer85/4 violates its comparison. Pair02 has odds5,5,
active outputs5/3, strict quiet joining offers-115/4 and positive quiet
Continue numerators130/3. Its index is-1.

The unique012 triple is determined by
x=(5+y/4)/(1+y),z=(5-y)/(1+y),101y²+177y-380=0.
Its positive root lies in(5/4,63/50), with47/20<x<12/5 and33/20<z<5/3.
These give all active Quit numerators positive (central one>43/400),
strict quiet joining offer Phi3<-5 and quiet Continue numerator
-x+3y-z+(7/3)xz-5>19/400+3y. The anchor functions strictly decrease,
so f'>0, giving regular index+1. Rotation gives023, whose quiet1 numerator
is>19/400-63/5000=349/10000>0. Both triples are bad.
For013 the owner3 equation gives x+y+xy=5 and owner1 gives
t=(5+x/4)/(1+x), but Phi0=-y+t(1/4+y)>-5;123 rotates this contradiction.
Full equations imply x=z=a,y=t=b by subtracting opposite rows. Eliminating
a yields64b^4-36b^3+116b²-133b+380=0, impossible: it equals
b²(64b²-36b+6)+(110b²-133b+380), with both quadratics positive.
Thus exactly three roots exist, all bad, total index-1+1+1=1.

The table is already solved by old hull Orientation: H has coordinate
floor-2, so high012 anchor equations force x,z<=2, while central positive
Quit would require T>3/(4z)+2/x>=11/8>4/3. The rotated triple is identical;
other triples are Low, pair02 has negative index, and full Orientation was
proved above. The singleton determinant-1821/100 makes H full-dimensional.
For original Z+one, M=4 and the annotation(-4)^4 lies in every box[-B,B]^4
with B>4. This is a boxed-selector obstruction in the single-edge shape,
not an actual source, a new UE class, or a counterexample to a theorem
additionally excluding all old S5 games. Both graph shapes require actual
source geometry or additional global input.

## 8. Strict-security two-zero sources can be unattained

The nonattainment permitted in Section4 genuinely occurs even with R0,
joining genericity and positive inverse pivot columns. Take

    Gamma=[0,-1,2,-1;-1,0,-1,2;2,-1,0,1;-1,2,1,0].

Every nonsingleton participant reward is1 and every passive reward3, except
Z2(23)=3/2,Z3(23)=3/4,Z0(023)=2,Z2(023)=7/2,Z3(023)=5/4.
All strict security tests hold at a_i=1/2. Gamma has determinant20 and
inverse(1/10)[-2,-3,4,1;-3,-2,1,4;4,1,2,3;1,4,3,2], so columns2,3
are positive. Principal pair determinants are(-1,-4,-1,-1,-4,-1), triples
(4,4,-4,-4); every column has a negative entry. This proves R0 by supports.
All off-diagonal joining entries are nonzero and principal triple joining
determinants are(-8,-8,-1/2,-1/2).

Above AllNever, row(1/2,0,1/2,1/2) is exact Nash and ALL-END with
U=B=e=(1,3/2,3/2,3/4),N=(1/2,1,1/2,1/2). Its three active Quit offers
equal their Continue offers; quiet1 has Quit7/8<3/2.
Given tail caps(x,y,w2,w3), prepend01 hazards q0=y/(2+y),q1=x/(2+x).
Their active caps become x'=x/(2+x),y'=y/(2+y). For outsiders,

    P2=2q0-q1+2q0q1,P3=-q0+2q1+2q0q1,
    H2=H3=(1-q0)(1-q1),Q2=Q3=q0+q1-q0q1.

After n such prepended rows, writing r=2^n, the exact caps are

    b0=1/(2r-1),b1=3/(5r-3),
    b2=(11r²-7r-1)/[(2r-1)(5r-3)],
    b3=(13r²-8r-2)/[2(2r-1)(5r-3)].

Direct substitution proves these recurrences from the base values.
For n>=1 the quiet gaps are respectively
(11r²-18r+8)/[(2r-1)(5r-3)] and
(13r²-30r+16)/[2(2r-1)(5r-3)], both positive for r>=2.
Thus every finite profile is exact Nash against all behavioral deviations,
and its cap equals its Never response. Its ORIGINAL Never vector is

    N=(r/(5r-3),r/(2r-1),1/2,1/2),

by telescoping the Continue products. The augmented tuples converge to

    U=B=e=(0,0,11/10,13/20),N=(1/5,1/2,1/2,1/2),nu=1/40.

For each fixed date, the first finitely many hazards tend to0; the final023
row moves to date n. Finite mass escapes dates, while original Never stays
as displayed. The compact tuple is unattained: a realized cap0=0 would,
by strict security, force all its opponents to Never, contradicting N.

This supplies a strengthened boundary regression, not a stronger existence
theorem. The game has an absorbing Nash sure pair01: its participants get1
versus passive-1, and outsiders get3 versus joining1. Thus A_Z=0. Strict
security and compactness alone cannot supply the additional global comparison
needed under A_Z>0; nor do they imply original Never tends to1. No attained
law, positive-gap game, global least-Never property, or extra Q/degree/pencil
hypothesis is supplied by the example.


## 9. A zero2 minimum-source cone has a complete cofinal consumer

Use the raw opposed family and actual(U,B,e,N) carrier in the
[whole-head source theorem](../exports/OPPOSED_PAIR_WHOLE_HEAD_TRIPLE_ENTRY.md).
Let X minimize original joint Never over E with min U<=0 under A_Z>0.
Its negative-owner2 case has

    U(X)=(-A,B,0,D),A,B,D>0,
    A<1/4,D>5A/(1-4A),B>6(D-A).

The all-bad03-root argument produces these inequalities at X, not its
continuations. Write k=-Z0(02),c=Z3(23). Suppose

    Z2(02)<0,Z2(23)<0,Z2(023)<0,                 (ST2)
    k>0,(c<=D OR c<4),4A/k<D<(62-10k)A/(3k).    (ZC2)

Then this entire selected-source region is impossible. It is not a new UE
reward class, a statement about every zero2 source, or a closure of caseII.
The scalar cone is nonempty, e.g.k=1,A=1/100,D=1/10,B=1,c=0; this does
not assert existence of a selected source there.

Combining the upper D bound with D>5A/(1-4A) yields
k<62(1-4A)/(25-40A)<62/25<5. The incoming rule(IN) forces q1=0 and
q2>0. Since its active Q2=0, (ST2) forces q0=q3=0. The singleton2
hazard s is proper because sure2 would give payoff1=-4. Its genuine E tail is

    w=((-A+5s)/(1-s),(B+4s)/(1-s),0,(D-4s)/(1-s)).

The head inequalities say ks>=A,cs<=D. The latter is strict on the
whole union in(ZC2). For c<=D this uses s<1,D>0. For the new part
0<D<c<4, equality would give a genuine tail with positive1, zero2 and
negative3, which is impossible by the following full-source lemma.

If c>=0, no E point can have U1>0,U2=0,U3<0 under(ST2). Its incoming
row has q1=0 because Q1<=0. If q2=0, then Q3=2q0>=0, contradicting
Q3<=U3<0. If q2>0, active Q2=0 and(ST2) force q0=q3=0, so instead
Q3=cq2>=0, the same contradiction. This uses every incoming support,
not an assumed pure2 continuation. At initial saturation cs=D with
0<D<c<4, the actual tail has w1>0,w2=0 and
w3=D(c-4)/(c-D)<0, exactly the forbidden source. If ks>A, all quiet gaps are strict; increasing s slightly
at fixed tail retains Nash and a negative0 payoff while decreasing positive
original Never. Original m-minimality therefore gives s=A/k. Consequently
w0,w1,w3>0 and

    S1=w1+3w3-2w0>0,S2=5w0/3-w3/2>0.

The second follows exactly from(ZC2). For the first,
(1-s)S1=B+3D+(2k-18)s>9D-(18+4k)s>(18-4k)s>0.

Here is the full cofinal pure2 argument; a prescribed compression is not
silently used as a Nash identity. Given any such w in E, choose M bounding
rewards, kappa=min(w0,w1,w3)>0 and delta>0 small enough to preserve all
three positive buffers under at most4delta prior absorption, with
4delta<w3/2,18delta<S1/2 and2c_+delta<kappa/16. Choose epsilon>0 with
4M epsilon<kappa/16. Along actual approximants of debt D_n->0 stop at
the first date when unconditional finite mass2 reaches delta or q0 or q3
reaches epsilon; provisionally also stop at cumulative non2 mass delta.
Prior survival is>1-4delta>1/2 and positive buffers stay>=kappa/2.
The reached-debt sum bounds all accumulated q1 by O(D_n), because Q1<=0.
Before the intended stop q2<=delta/(1-delta)<=2delta, and

    Q0<=2M(q1+q3),Q3<=c_+q2+2M(q0+q1).

These are below kappa/4, so the same reached-debt sum bounds accumulated
q0,q3 by O(D_n). The provisional stop cannot occur first, since its last
stage satisfies those same bounds. At the selected date q1->0. The date
must be finite: otherwise all non2 finite mass is O(D_n) and payoff0 is
at most O(D_n), since singleton2 pays it-5, contradicting w0>0.

A subsequential moving-cut E source W therefore has predate pure2 mass
beta in[0,delta], with

    W=((w0+5beta)/(1-beta),(w1+4beta)/(1-beta),0,
       (w3-4beta)/(1-beta)),
    S1(W)=(S1-18beta)/(1-beta)>0,
    S2(W)=(S2+31beta/3)/(1-beta)>0.

Original Never conditions by the same Continue factor; no escaped finite
mass is renamed Never. At W, positive1 forces q1=0. If q2>0, (ST2)
forces q0=q3=0. Otherwise a nonzero0/3 row must be proper03, with hazards
W3/2,W0/3. Its genuine E tail has negative0 and positive1,2 by the guard
sums, contradicting that tail's own incoming rule. Thus the macro-row is
pure2 (or AllContinue), and proper since sure2 would give payoff1=-4.
The large0/3 stopping alternative disappears, so cumulative pure2 mass
through this date is g>=delta>0. It gives a genuine E tail Y with

    w_i=g Gamma_i2+(1-g)U_i(Y),
    N2(w)=(1-g)N2(Y),Nj(w)=Nj(Y) for j!=2.

This relation is ONLY prescribed payoff and original Never. Combining with
the initial s gives G=s+(1-s)g>s and the SAME U(X),N(X). Now the compressed
row is Nash at Y: owner2 endpoints are0, Q0=-kG<-A, Q1=Z1(12)G<=0<B,
and Q3=cG<D throughout the union. For c<=D this is immediate. For
0<D<c<4, if cG>=D the genuine tail instead has
Y1=(B+4G)/(1-G)>0,Y2=0,Y3=(D-4G)/(1-G)<0, forbidden by the same
full-source lemma. Thus all quiet gaps are strict. Increasing G
slightly therefore gives an E whole source with negative payoff0 and lower
original Never, contradicting m. No minimum was assigned to w,W or Y.

The strict c<4 extension uses feasibility of the GENUINE final source
to protect quiet3 after cumulative compression, not merely the initial
D>4s comparison. It does not add c=4 unless the old c<=D branch applies.
Outside this union cone, zero2 and strict-negative2 remain open.

One old stationary filter must be enforced throughout this family:
A_Z>0 implies Z2(23)>-5. Otherwise pure3 is absorbing Nash: owners0,1
prefer passive4,6 to joining3,-1, and2 prefers passive-5 to joiningZ2(23).
This is existing stationary coverage, with no new-class credit. In particular
the earlier geometric23 boundary fixtures with Z2(23)=-10 do not lie in
the genuine positive-gap domain.


## 10. First013 has two histories and an automatic quiet2 comparison

The [first-triple normal form](../exports/OPPOSED_PAIR_FIRST_TRIPLE_NORMAL_FORM.md)
classifies EVERY finite first013 entry in the selected caseI mode. Together
with the existing whole-head finite-entry producer, the only histories are
01,013 and01,03,01,013. Their genuine tail Y=(V,-E,T,F) has E>F>0 and
must satisfy respectively V<0 and V<3(E-F). No extra quiet2 guard remains.

The mechanism uses two produced stationary013 child roots to bound the
free passive entries Z2(13),Z2(013) by affine interpolation at the ACTUAL
triple hazard. Under A_Z>0 this makes the explicit01 replacement's quiet2
comparison automatic whenever V>=E-F. In the remaining immediate sector
0<=V<E-F, stronger ORIGINAL all-bad bounds force T>0 and a third genuine013.
The same stationary families supply the passive bound there; a full01 row
at its actual tail absorbs the ENTIRE three-row history. Thus EVERY
immediate V>=0 is excluded, including V=0. The four-row absorption
proof derives its small hazard domain from ORIGINAL all-bad bounds and
uses exact rational coefficient certificates. It does not assign those
bounds or a minimum to any tail. A finite exact Nash-head core shows why
the two-row coefficient1 cannot simply replace3 in the four-row comparison;
it is no actual selected-source or positive-gap witness.

This supersedes the earlier immediate013 consumer requiring a supplied
quiet2 inequality. The canonical complete proof is retained only in the
packet. The immediate V<0 and four-row V<3(E-F) sectors are not consumed;
this does not close caseI, the whole raw opposed family or arbitrary Fin4.

## 11. A raw criterion excludes nonnegative selected sources

For any native quitting table on a nonempty finite player set I put
Gamma_ij=Z_i({j}),
J_ij=Z_i({i,j}) off the zero diagonals and L=J-Gamma. Use full behavioral
caps, actual closure E={U=B}, original Never nu, positive absorbing gap
A_Z>0 and m=min{nu(X):X in E,min U(X)<=0}. The following RAW conditions
force EVERY m-minimizer to have a negative payoff coordinate:

* For every nonempty proper zero set T there is a mover j in T such that
  either Gamma_ij>=0 for all i in T minus{j}, or Gamma_ij>=J_ij for all
  those i. These are respectively diffuse and exact solo covers.
* There are S subset I, t in(0,1),v_S>0 with L_SS invertible,
  (Gamma_SS-t J_SS)v_S=0, and (Gamma_kS-t J_kS)v_S>0 for every k outside S.
  Some active coordinate also satisfies (J_SS v_S)_i<0.

These conditions concern singleton and participant-pair data; passive-pair
and higher rewards are arbitrary finite numbers. The proof below uses
old finite-prefix and expanding-clock mechanisms, with no new UE-class
claim or universal capstone. The fixed opposed family satisfies this
criterion, so its nonnegative selected-source modes are all absent.

### Exact and diffuse finite solo comparisons

Suppose u>=0 is an E source with at least one zero and one positive
coordinate. For a diffuse-cover mover j prepend N solo-j dates of
unconditional mass f/N, where f>0 is fixed and small. Conditional hazards
are at most f/[N(1-f)]. Apply these finite words to actual approximants,
then take a compact limit as approximation error and maximum atom vanish.
Owner j has payoff and cap0. Each zero observer i has prescribed payoff
f Gamma_ij>=0. An internal deadline gets at most this value plus M f/N:
joining can change only its current atom. Continuing into the tail gives
that prescribed value, so all zero-observer debts vanish. Positive outsiders
have fixed tail buffers and remain on Continue for sufficiently small f.
The E limit still has payoff j=0 and ORIGINAL Never (1-f)nu<nu.
No infinite prefix followed by a tail is executed.

For an exact-cover mover j, one small solo-j row is already full Nash:
zero observers compare f Gamma_ij>=f J_ij, the mover stays exactly0,
and positive outsiders remain quiet. Both comparisons preserve a zero
payoff and therefore compare against the ORIGINAL RESTRICTED minimum m.

The fixed opposed family has the following exhaustive proper-zero-set cover:

| T | mover j | comparison |
| --- | ---: | --- |
| one owner | that owner | small exact solo |
| 01 | 0 | Gamma10=-6>J10=-7 |
| 02 | 0 | diffuse, Gamma20=1>0 |
| 03 | 3 | diffuse, Gamma03=4>0 |
| 12 | 1 | diffuse, Gamma21=3>0 |
| 13 | 3 | diffuse, Gamma13=6>0 |
| 23 | 2 | diffuse, Gamma32=4>0 |
| 012 | 0 | Gamma10=-6>-7; Gamma20=1>J20 |
| 013 | 3 | Gamma03=4>3; Gamma13=6>-1 |
| 023 | 0 | diffuse, Gamma20=Gamma30=1>0 |
| 123 | 1 | Gamma21=3>J21; Gamma31=-1>-2 |

The owner2 participant signs supply J20,J21<=0. Diffuse comparison on23
needs no bound on the free J32; replacing it by an exact single-date
comparison would be wrong.

### An actual negative clock gives m<1

The raw clock conditions imply L_SS^(-1)J_SS v=v/(1-t), with
rho=1/(1-t)>1. The existing positive backward-orbit construction from
[global least-Never reduction](../exports/GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md),
Sections7 and9, gives proper positive hazards

    q_n=epsilon rho^n v+O(epsilon^2 sigma^n), n<=0,
    rho<sigma<rho^2, chronological order q0,q_-1,q_-2,... .

Its active finite replies and Never telescope to Q(q0). The virtual terminal
annotations tend to0, so this is an ACTUAL full-cap Nash clock with original
Never strictly between0 and1, not a profile played after an infinite prefix.
For each outside owner k, Never minus current Quit at suffix n is

    (epsilon rho^n/t)(Gamma_kS-t J_kS)v+O(epsilon^2 sigma^n)>0

uniformly in n for small epsilon. All earlier common absorption cancels,
and mixtures price every complete reply. The negative active J-row gives
a strictly negative actual payoff for small epsilon. Thus this clock is
eligible for the ORIGINAL m and proves m<=nu_clock<1 directly.
No different global minimum is substituted for m.

The fixed opposed family has a wholly rational clock on S=013:

    det(J_SS-Gamma_SS)=-8,
    t=1/2, v=(39,25,15), (Gamma_SS-J_SS/2)v=0,
    J_SS v=(20,-288,28).

For its outside owner2,

    (Gamma_2S-J_2S/2)v
       =39-(39J20+25J21+15J23)/2>=39>0,

by the participant2 signs. All free higher rewards affect only the bounded
quadratic errors and the small amplitude chosen for the given finite table.
The endpoint payoff1 is negative; in the exact fixed family it is
Q1(q0)=-7(q0)_0-(q0)_3<0. This credits the existing expanding-clock
producer, not another stationary or clock existence class.

### All-zero sources and the generalization beyond the fixed family

At u=0, the resulting0<m<1 permits two independent copies of finite actual
approximants. With an unused separator date the exact formulas are

    U_i(P*P)=(1+nu(P))U_i(P),
    B_i(P*P)=max(B_i(P),e_i(P)+H_i(P)B_i(P)),
    N_i(P*P)=N_i(P)^2, H_i(P)=product_(j!=i)N_j(P).

Finite approximants follow by moving late finite mass to Never, uniformly
in full replies. At the limit B=U=0 and e<=B=0, so concatenation is in E
with payoff0 and Never m^2<m. This is the old two-copy argument, applied
to the SAME nonpositive-payoff minimum. Together with the proper-zero-set
comparisons it proves the raw criterion.

If the chosen off-diagonal cover comparisons and outside clock residuals
are strict and the expanding eigenvalue is simple, these RAW conditions
persist on an open neighborhood of the singleton/participant-pair data.
That applies here: the displayed cover is strict and the rational mode
rho=2 is simple, as det(Gamma_SS-t J_SS)=-2(2t-1)(11t^2-21t+6).
All other rewards remain arbitrary finite; no exact triple identities are
needed for this source-branch exclusion. The fixed-family negative-source
dispatch and first013 analysis still have their own stronger hypotheses.


## 12. The proper-zero source seam has an actual repair

The canonical [negative-dual/actual-repair proof](../exports/NONNEGATIVE_MINIMUM_SOURCE_PENCIL_REDUCTION.md)
applies to arbitrary native Fin4 tables. A proper nonnegative ORIGINAL-m
source has a strict negative left singleton certificate on its zero set;
under joining genericity its principal joining pencil has degree0.
These raw conditions produce nonzero small Nash roots by degree excision,
then an actual positive-to-zero repair by iterated finite prefixing and
compact limits. It retains original Never and supplies an explicit gain.

For A_Z>0,m<1 and the stated joining genericity, the positive part P_m of
the native E sublevel is compact with one kappa_m>0 THROUGH m. A given
point in P_m has a uniformly bounded macroscopic actual head reaching
eligibility at m or crossing above m. This supersedes a possible vanishing
kappa_s at s-up-to-m; finite-amplitude jumps above m and m=1 remain open.
The positive sublevel has finite nonzero-Nash-prefix height too. None of
these carrier conclusions identifies the stronger literal source atlas
fields or completes its two universal consumers. The complete proof is
retained only in the packet, not duplicated here.


## 13. Two initial23 modes have original-source consumers

Continue on the fixed opposed raw family of Sections9--10, using complete
independent stopping laws, full caps and the original(U,B,e,N) carrier.
Let X minimize original joint Never over E with min U<=0 under A_Z>0,
and suppose its initial dispatch is

    U(X)=(-A,B,-C,D), A,B,C,D>0,
    A<1/4,D>5A/(1-4A),B>6(D-A),
    C<D(1-4A)-5A.                               (II)

These inequalities are produced at the ORIGINAL selected source only.
Every genuine tail used below is in E, but no tail is called minimizing.

### Closed entire incoming23 regime

Put w=-Z2(23), c=Z3(23), K=Z1(23). Suppose the FIRST actual incoming
support is23. Then0<w<5,c>D, and its hazards are

    q=(0,0,s,t), s=D/c in(0,1),t=C/w in(0,1).

**Theorem.** If0<c<4, then necessarily

    (4+6c)w<c max(6,K+4).                       (BUDGET)

Hence the entire initial23 branch is impossible on the RAW regime
0<c<4,(4+6c)w>=c max(6,K+4), for every free completion. In particular,
if K<=2 it is excluded whenever w>=3c/(2+3c). This is a complete selected
source-branch exclusion, not a new UE class or closure of all caseII.
The weak boundary equality in the excluded raw comparison is included.

### Exact full-source proof

First A_Z>0 forces Z2(23)>-5. Otherwise pure3 Quit, everyone else Never,
is absorbing Nash: recipients0,1 prefer passive4,6 to joining3,-1,
recipient2 prefers passive-5 to joining Z2(23), and3 gets own0. This old
stationary exclusion receives no new coverage credit. Participant2 signs
therefore give0<=w<5, and active2 with negative payoff forcesw>0.
Positive original Never makes the incoming23 row proper, so s,t<1.
Its active cap equations are-C=-wt,D=cs, giving the displayed hazards.

Extract the genuine E tailY behind this PROPER actual row. Fixed passive
singletons and active equalities give exactly

    Y2=(5-w)t/(1-t)>0,
    Y3=(c-4)s/(1-s)<0.

NecessarilyY1<=0. Indeed ifY1>0, its own incoming rule suppresses1
because all its participant rewards are nonpositive, and positiveY2
similarly suppresses2. The forced-Quit offer of3 on that face is2q0>=0,
contradicting Q3<=Y3<0. This checks ALL subsequent incoming supports,
not an assumed pure continuation; no original minimum is transferred.

The full original-head prescribed identity, with h=(1-s)(1-t)>0, is

    B=P1+hY1<=P1=-4s+6t+(K-2)st.

Let M=max(K-2,0). Thus B<=-4s+(6+M)t. On the ORIGINAL selected source,
(II) gives C<D and

    A<(D-C)/(5+4D)<(D-C)/5,
    B>6(D-A)>(24/5)D+(6/5)C.

Substitute D=cs,C=wt. We obtain

    (4+24c/5)s<[6+M-6w/5]t.

The bracket is strictly positive because0<w<5. Also C<D gives
t<cs/w. Substitution and division by positives,w yield

    (4+24c/5)w<c(6+M-6w/5),
    (4+6c)w<c(6+M)=c max(6,K+4),

which is(BUDGET). Every constraint used at X remains at X; the only tail
fact is actual E feasibility, and the FULL original23 head is retained.

### A complete zero1-return sector: whole-head variation

The following is a second, genuine original-m consumer, beyond(BUDGET).
Keep initial23,0<c<4,0<w<5 and suppose its genuine tail is

    Y=(V,0,T,-F), V>=0,T>0,F>0.                 (RETURN)

**Theorem.** This selected source is impossible if the RAW comparisons

    Z0(02)<=-5, Z0(023)<=Z0(23),
    w>=8c/(c+3)                               (RETURN-RAW)

hold. This closes the entire indicated source/parameter sector, including
V=0 and equality in each raw comparison. It does not presume Y is minimal.

Write u=4-c>0,v=5-w>0,alpha=-Z0(02)>=5,
xi=Z0(23)-Z0(023)>=0. The original23 indifferences equivalently give

    s=F/(u+F), t=T/(v+T).

At Y, positive2 forces its next incoming q2=0. Negative3 forcesq1>0,
and zero1 with activeq1 gives0=Q1=-7q0-q3. Thus that next row is pure1,
with hazardr>0, and its quiet3 condition is2r>=F. It is proper: original
Never is positive, and alternativelyr=1 would give V=-2<0. Extract its
genuine E tailZ; Z1=0 because its prescribed pure1 prefix has own payoff0.

Hold Z fixed and increase r slightly. Its new outputY(r) remains E.
Owner1 stays indifferent0. Quiet0 is initially strict since its gap is
V+r>0; quiet2 is strict sinceT>0 andQ2<=0. For quiet3, the gap2r-F(r)
is initially nonnegative, and the fixed-Z identities give

    (1-r)V'(r)=-2-V,
    (1-r)T'(r)=3-T, (1-r)F'(r)=1-F,
    (1-r)(2r-F(r))'=1+F-2r.

At a binding quiet3 conditionF=2r the last expression equals1. Therefore
a sufficiently small one-sided increase ofr preserves every full root
deviation inequality. Strict signT,F>0 also persists by continuity.

Reconstruct the ORIGINAL23 root aboveY(r) using
s(r)=F(r)/(u+F(r)),t(r)=T(r)/(v+T(r)). These are proper and enforce both
active indifferences. Original quiet1 is strict: B>0 whereasQ1<=0.
Original quiet0 is also strict. Indeed its full gap divided by the23
joint survivalh=(1-s)(1-t), in oddsx=F/u,y=T/v, is exactly

    (U0-Q0)/h=V+(alpha-5)x+y+xi xy>0.

Thus all original-head root Nash inequalities persist under the same
small increase, even whenV=0 or a raw comparison binds. The recomposed
whole source stays eligible for the original minimum since its owner2
payoff is-wt(r)<0. This step uses the whole23-plus-pure1 head, not a
minimum atY orZ.

The resulting ORIGINAL joint Never is

    nu(r)=(1-r)nu(Z) u/(u+F(r)) v/(v+T(r)).

Its exact logarithmic derivative, scaled by1-r, is

    L=-1-(1-F)/(u+F)-(3-T)/(v+T)
     =-(u+1)/(u+F)+(T-3)/(v+T)
     =-(5-c)/(4-c)(1-s)+t-3/(5-w)(1-t).

The ORIGINAL dispatch has C<D, so wt<cs. Substitute the strict bound
t<cs/w intoL, whose t coefficient is positive. The resulting affine
function of s has positive slope, ands<1. Consequently

    L<[c(8-w)-3w]/[(5-w)w]<=0,

where the last inequality is exactlyw>=8c/(c+3). The strictness survives
equality in the raw bound. Hence increasingr strictly reduces the WHOLE
Never fromm, contradicting its original minimizing property. No tail
minimum or prescribed finite-time tail realizer was used.

The source split still retains c=4, where the genuine tail3 is zero,
and c>4, where it is positive. Strict-negative1 after the23 head can
enter a13 run with E_next=7E/(1-E), but positive2 can be lost through an
unrestricted passive13 reward before that run's core exit. Its inherited
tail is not an initial all-bad minimum. No whole23 or caseII closure is
inferred from a finite13 run or a favorable supplied insertion.


## 14. Negative immediate tails require a genuine global change

### Exact scope

Suppose the source has immediate01 then013, the latter with hazards
(a,b,0,c), and genuine E tail Y=(V,-E,T,F). The proved source bounds give
0<b<a<1,0<c<1,E>F>0, and the surviving case has V<0. Write k=Z0(13).
Restrict this lemma to the entire k<=0 sector. All statements below concern
the THREE-PLAYER auxiliary game on owners0,1,3 with owner2 held quiet.
Additional full-game roots involving owner2 are not ruled out.

### The current013 root is the only core Nash root at Y

Eliminating hazards0,1 from the three proper active equalities gives the
quadratic for hazard z at3,

    A z²+B z+C=0,
    A=k(E+7F+7)-E-7F-14+7V,
    B=-Ek+Fk-8F-6V-8, C=E-F-V.

Here A<0 and C>0, so exactly one root is positive. The actual c is that
root; its other two hazards are uniquely determined. Hence no alternate
positive proper013 root exists, independent of the free passive2 entries.
Proper01 or13 would require positive input0 or negative input3 respectively;
proper singletons require a zero input, absent here. AllContinue fails.

The only other possible proper support03 fails its owner1 quiet test.
Indeed its threshold is V<=-(E-F)/(7+8F). For the actual013 data,
(7+8F)V+E-F is positive. A direct factorization proves this: its numerator,
after multiplying by the positive denominator
(1-a)(1-b)^2(1-c), is minus b times

    k c[(a-b)(7b+1)+7(1-b)^2]
      -8[(1-b)^2+b(a-b)]
      -c[14(1-a)(1-b)+8(a-b)]<0.

Sure roots are impossible. Sure3 makes1 Continue, then0 Continue, then3
Continue because F>0. Sure0 with1 not sure forces3 Quit, reducing to that
case. Sure1 gives owner0 gap1+(1-k)q3>0, forcing0 sure, but owner1 then
has strictly negative gap-1-7q3. This exhausts the sure supports. Thus
current013 is the UNIQUE full child Nash root at Y.

### Upstream01 is most absorbing among all core roots at its input

The current triple produces

    w=(3c-b,-7a-c,2a-2b),
    w0>0,w1<0,w3>0,S=w0+w1+w3>0.

The upstream01 row has odds(-w1,w0), survival
h01=1/[(1-w1)(1+w0)]. All proper competing core roots must be013:
03 requires negative input0,13 requires negative input3,singletons need a
zero input, and AllContinue fails at negative1. The same sure-root census
applies. Let a competing013 root have odds(x,y,z), so x=y+w3,
-w1=x+7z+8xz, and w0=y-z+(2-k)yz. Since z>0,

    y<-w1-w3<w0, hence (2-k)y>1.

Let Dtr=(1+x)(1+y)(1+z), D01=(1-w1)(1+w0). Exact expansion gives

    (Dtr-D01)/z
      =z(8x+7)[1-(2-k)y]+k y(1+x)
                               -9xy-6x-8y-5<0.

Thus every competing013 root has STRICTLY LARGER survival than01.
Consequently two-layer core rerooting at this same genuine Y cannot lower
the old whole01->013 survival. This is a complete local-root obstruction,
not an actual positive-gap counterexample or a proof that no global
replacement exists. It makes no assumption that Y is minimizing.

The scope is an entire proof-method boundary, not a new source exclusion:
for k<=0 an immediate V<0 consumer must involve owner2, change the genuine
tail or use a longer controlled return. Extrapolating two stationary upper
planes outside their bracketing interval does not produce that change.
No algebraic jackpot limit is asserted to be an actual E source.


## 15. Actual full-SUM minima require contact or support geometry

The complete [contact/support reduction](../exports/ACTUAL_MINIMUM_CONTACT_AND_SUPPORT_REDUCTION.md)
applies to the actual-calendar case of the universal all-END SUM minimum.
Its objective is

    F=sum_i theta_i(B_i^Z-U_i^Z)+rho nu,
    rho=t sum_i theta_i.

It is not the observer-constrained pivot minimum or the native restricted
m. Finite small hazard changes are legitimate competitors without an
observer-debt repair. At a fully slack finite response menu, all END caps
remain active in an open finite-control rectangle: earlier queries have
finitely many strict gaps, and every later gap transports by positive
opponent survival. The exact bilinear mixed term and late stationarity
then force reciprocal singleton zeros between persistent owners. No
reciprocal zero pair therefore excludes the entire actual no-contact case.

Finite cap contacts need not be prescribed actions. With their dates
bounded and all four owners persistent, eight late controls in order
01230123 give max(fixed contact offer,END) cap geometry. Compact multipliers,
the exact END-level manifold and the positive semidefinite tangent Hessian
force

    (theta_i+rho s_i)Gamma_ij=(theta_j+rho s_j)Gamma_ji,
    s_i=sum_j(Gamma inverse)_ji.

For ANY supplied positive weight box with interior, one fixed theta can be
chosen before rho to violate this identity for every sufficiently small
rho. Gamma invertibility suffices; the universal old all-END box permits
this price choice at the SAME native positive-gap table. A generic
singleton-cycle condition is unnecessary.

The actual global minimum case also has a finite-event producer. Increase
one existing hazard until the first new finite cap contact. Its full-SUM
objective stays affine and constant while caps remain END; the absorbing
endpoint is excluded by mu<min(theta_i)A_Z. A finite earliest-contact-time
descent then aligns a contact with the first prescribed joint atom. The
positive quadratic cap margins and solo-first collision ledger already
exist; no common debt vector or special cube table is imported.

Consequently actual sources may be selected with a paid date0 contact and
at least two owner atoms. The support/price theorem leaves bounded finite
support for some owner OR unbounded contact dates. The finite modifications
preserve these support and contact-tail classes. The actual-source
hypothesis is explicit: compactness does not supply a realizing calendar.
Nonrealized minima and the remaining contact consumers remain open. A root
degree or finite positive-prefix height is not a substitute for either.


## 16. Every actual bounded-contact source case is excluded

The [complete actual bounded-contact exclusion](../exports/ACTUAL_BOUNDED_CONTACT_EXCLUSION.md)
unifies the finite contact-incidence arguments. After avoiding only the
singleton zero hyperplanes and selecting the native table afresh, it
constructs ONE fixed positive price vector before t and before any minimum.
Every ACTUAL all-END global minimum at every sufficiently small raise then
has UNBOUNDED finite cap-contact dates. No2x2/3x3 minor gate, simultaneous
support date, regular endpoint map or tail minimum is assumed.

The old universal strict inverse-column/all-END source provides the raw
matrix and source case. The new finite4^3 price grid and smaller cheap
weight produce a common cone-KKT bound Gamma^T r>=rho one, with equality
on persistent columns. Positive inverse-column directions bound the
possibly signed r and keep every effective price close to the selected
price. No reciprocal pair can balance at those effective prices.

All persistent-support cases are consumed at the same prices. With at most
one persistent owner, every sufficiently late query of that owner already
attains Never, so contacts cannot be bounded. With exactly two, legal
finite-atom transfers have zero first derivatives of both finite masses
and tie probability while varying the first-quitter race. The common KKT
timing coefficient and two
persistent-column equalities force the forbidden reciprocal balance.

With at least three persistent owners, the finite normal-multiplier set
has dimension at most4-|S|<=1. Quadratic legal paths and a finite LP dual
give a point/segment quadratic alternative. A self-contained two-form
convexity argument supplies ONE normal multiplier whose Hessian is PSD
on the critical subspace. Five interleaved pair blocks give five negative
directions, exceeding its codimension of at most4. This uses neither a
constraint-kernel convergence claim nor an unproduced constant-rank map.
The exact three-form counterexample explains why the two-clock case needs
its separate timing proof.

The intermediate contact-surplus and three-persistent/cycle-only stages
are subsumed and are not retained as duplicate proofs. Their useful price,
cone and timing mechanisms are reproduced in the completed export. The
older exact PRICE identity for arbitrary invertible matrices retains its
distinct same-table, no-singleton-genericity scope.

The all-END ACTUAL global minimum remains an explicit source case, not an
attainment theorem. Unbounded contacts can be unused finite replies and
need not coincide with prescribed atoms or distinct payoff kernels.
Thus this class exclusion does not give a UE. The remaining consumer must
handle those contacts and, separately, the genuine possibly nonrealized
suffix of the compact normal form. Inserting empty dates is not generally
cap-preserving when a conditional native END is negative.


## 17. The first joint contact does not require an actual calendar

The [compact first-joint-contact reduction](../exports/COMPACT_MINIMUM_FIRST_JOINT_CONTACT_REDUCTION.md)
extends the first-head normal form to the full actual closure. At the fixed
raised full-SUM minimum, choose least ORIGINAL nu among the compact all-END
minima. A proper first product row with at least two positive hazards and
a native current-Quit/END contact is produced at that SAME source, even
when neither the whole source nor its suffix has an actual calendar.

The strict cap margins give a uniform activity charge. A sufficiently tiny
leading row has every cap on its Continue branch; deleting it lowers the
full-debt excess by a fixed multiple of its activity. The TOTAL deleted
activity in a realizing sequence tends to zero, irrespective of the number
of dates. Thus reindexing the first macro row preserves the same entire
(U,B,e,N), retaining original Never when the cut dates escape. The old early
collision/solo ledger is credited rather than counted as a new class.

The new step is an exact finite-prefix ray on C. If all four current Quit
queries are strict, increase one existing hazard with its genuine compact
suffix fixed. The all-END objective is affine and constant until a contact
or a sure-Quit endpoint. The weighted absorbing gap excludes that endpoint;
a proper contact would strictly lower original nu, contradicting the
secondary selection. No infinite prefix is executed, and the suffix is
not assumed minimizing or realized. The prescribed row is not asserted Nash.

Every owner is paid in the original raised game. Native Never attains its
native cap, while raised literal Never is strictly below the raised cap;
it is not identified with a late finite query. The finite paid-contact
consumer is now the common target for actual and nonrealized minima.
Actual-calendar assumptions remain essential to the separate persistent
support/Hessian arguments. This normal form alone neither supplies that
calendar nor closes the contact consumer.


## 18. The entire low nonnegative four-row mode is excluded

The [finite-nine-row consumer](../exports/OPPOSED_PAIR_LOW_NONNEGATIVE_FOUR_ROW_EXCLUSION.md)
closes0<=V<E-F at the genuine tail of the actual01,03,01,013 head in the
fixed opposed family. The original selected native m, full four-player
caps and original Never factors are retained. No tail is declared
minimizing or all-bad.

The original AB/Cfloor produces sharper hazard bounds and a global outsider
budget. This forces positive owner2 caps through the eight-row word
01,03,01,013,013,03,01,013. The exact finite classifier proves the last
source ratio, which forces the ninth013 row, its stationary bracket and
FULL01 comparison. That comparison strictly reduces Never across ALL NINE
old rows. The endpoint V=0 is included. Every phase support and required
bracket is produced; a small recurring cone is never assumed indefinitely.

Both independent whole mathematical/export reviews executed all four printed
standalone programs. The interval proof exhausts35087 exact nodes with
zero pending or unresolved boxes, using outward dyadic arithmetic and
necessary source contractions. No generated coefficient or leaf payload
is retained. The full proof is in the export, rather than duplicated here.

The remaining raw-family targets are negative-V immediate tails, four-row
V<0 or E-F<=V<3(E-F), and the surviving negative-owner2 chamber. The new
actual full-SUM contact theorems concern a DIFFERENT minimum from native m;
no continuation or counterfixture is transferred between those objectives.


## 19. The fixed family's full-SUM source has exactly a first03 row

This is a complete compact-source reduction for the full fixed13 family of
[negative-source dispatch](../exports/OPPOSED_PAIR_NEGATIVE_SOURCE_DISPATCH.md).
It concerns the ORIGINAL raised full-SUM objective, not the native m minimum.
The first-row statement and every source hypothesis were independently
reviewed. It is retained as one internal theorem, not another UE class or
export. The following proof retains all fixed entries and the original N.

### Source and precise conclusion

Use the native four-owner compact carrier C of (U,B,e,N), native own-singleton
and literal Never rewards zero, and the full independent complete-law response
caps B. Put d_i=B_i-U_i, D=sum d_i, nu=product N_i and E=C intersect{D=0}.
Assume the native absorbing gap A>0, and put alpha=min_E nu. Retain the
fixed13 opposed-pair family: its singleton matrix is

    [0,-2,-5,4; -6,0,-4,6; 1,3,0,-5; 1,-1,4,0],

all participant rewards of owners1,2 are nonpositive, and in particular
Z0(03)=3,Z3(03)=2. We retain the full fixed13 data throughout. Its other
entries enter the alpha-collar producer and the optional q2=0 identities;
the final two-contact deformation uses the displayed0/3 data and
participant signs.

Fix ONE theta>0 from the old all-END weight box, BEFORE t. For every
sufficiently small t>0 let rho=t sum theta_i and

    F_t(X)=sum theta_i d_i(X)+rho nu(X), mu_t=min_C F_t.

The old source theorem makes every minimum all-END with positive Never.
Choose X_t among its minima with least ORIGINAL nu. The compact contact
producer gives X_t=prefix(q,Y), Y in C all-END, q proper and joint, and
at least one current native contact Q_i(q)=B_i(X_t).

Then for ALL sufficiently small t, EVERY such displayed contact factorization
has

    q=(p,0,0,s), 0<p,s<1,
    Q0=B0(X_t), Q3=B3(X_t),
    B0(Y)=-s/(1-s)<0, B3(Y)=p/(1-p)>0.             (03)

Both p,s and their Continue probabilities are uniformly bounded away from
zero. This is a produced first-row normal form; q is NOT asserted Nash
against the prescribed continuation U(Y).

The needed strict positivity of EVERY alpha-minimizer is produced below
for the literal fixed family, without genericity or perturbation of its31
free rewards. The proof more generally applies to any fixed native table
having this alpha-cap property, the two nonpositive participant owners and
the displayed0/3 singleton and participant entries.

### The alpha-cap collar is produced in this literal raw family

The already established raw criterion in Section11 above
has two conclusions for this family: m<1 and EVERY restricted-m minimizer
has some strictly negative payoff coordinate. It uses the exhaustive proper
zero-set solo covers, the all-zero two-copy comparison, and an actual
negative clock. Its exact clock data are S=013,t=1/2,v=(39,25,15),
det L_SS=-8, (Gamma_SS-J_SS/2)v=0, J_SS v=(20,-288,28); the outside2
residual is at least39 by participant2 signs. In particular that actual
negative clock belongs to E and has nu<1. Hence alpha<=m<1. All these
facts hold for every finite free completion of the fixed13 family.

Every global alpha-minimizer X is nonnegative, with no genericity needed.
Indeed, if some U_i(X)<0, AllContinue is not a Nash root over its payoff
annotation. Finite-game Nash existence supplies a nonzero root q. The
full-cap Nash-prefix identity keeps prefix(q,X) in E. A sure component
would contradict A>0 by the repair bound, and a proper nonzero root
strictly lowers its positive ORIGINAL nu below alpha. Either case is
impossible. Thus U(X)>=0.

If any coordinate of an alpha-minimizer were zero, that point would be
eligible for the restricted minimum m. Since alpha<=m always, it would
give m=alpha and itself be a NONNEGATIVE m-minimizer, contradicting the
raw criterion. Every alpha-minimizer is therefore strictly positive, and
its caps equal its payoffs. This completes the genericity-free production
needed below, keeping alpha and m distinct throughout.

### Two general compact contact lemmas

Write g_i=e_i(X)-Q_i(q)>=0, H_i=product_(j!=i)(1-q_j), h=product(1-q_j).
Because Y and X are all-END, their exact full-cap prefix identities give

    d_i(X)=h d_i(Y)+q_i g_i,
    F_t(X)=h F_t(Y)+sum theta_i q_i g_i.           (1)

Here nu(X)=h nu(Y), with ORIGINAL Never throughout. In particular F_t(Y)
is at least the same global minimum; it is not asserted equal to mu_t.

At a positive raised full-SUM minimum the existing quadratic margin theorem
gives theta_i B_i(X)>=mu_t+eta_t, eta_t>0. If every active j had Q_j<=0,
then (1) and F_t(Y)>=mu_t would imply

    mu_t(1-h)>=sum theta_i q_i g_i
                  >=(mu_t+eta_t)sum q_i>mu_t(1-h),

a contradiction. Therefore some active prescribed owner has Q_j>0. In this
family that owner is0 or3, since Q1,Q2<=0 for EVERY product row.

Also, every positive prescribed column must affect some current contact gap.
Indeed, if q_j>0 and all contact gaps have derivative0 in q_j, these gaps,
being affine in q_j, stay exactly zero under a small two-sided variation.
Every noncontact gap stays positive. The source therefore stays all-END.
Its F_t is affine in this one hazard, so global minimality forces it constant.
Increasing q_j strictly lowers nu, violating the selected least-nu property.
In particular a SINGLE current contact i forces q_i=0, because its own gap
does not depend on its own hazard. No dual atom at the contact is inferred.

As a useful exact consequence, if q2=0 then Q0=-q1+3q3,Q3=2q0-2q1.
The positive active Q above forces BOTH q0,q3>0. Since contacts can only
belong to0,3, the singleton rule forces BOTH contacts. Consequently

    q2=0 implies contact set{0,3}, q0,q3>0,
    q1<min(q0,3q3).

### Uniform native source collar as t decreases

An alpha-minimizer is a competitor of value rho alpha. Thus

    mu_t<=rho alpha, D(X_t)<=rho alpha/min theta_i, nu(X_t)<=alpha. (2)

The repair bound A<=D+14M nu^(1/4) gives alpha>0. Every cluster of X_t as
t decreases to0 belongs to E; by (2) it has Never product alpha. Compactness
and strict positivity at EVERY alpha-minimizer therefore produce kappa>0
and t0>0 such that

    B_i(X_t)>=kappa for ALL i, 0<t<t0.             (3)

This is uniform over all selected minima and their head factorizations.
Also nu(X_t)->alpha. Since nu(X_t)=h nu(Y)<=h<=1-q_i, after shrinking t0,

    h>=alpha/2, 1-q_i>=alpha/2, N_i(Y)>=alpha/2.    (4)

By (1), g1,g2>=kappa and Q1,Q2<=0 give

    q1,q2=O(t), F_t(Y)<=mu_t/h=O(t),
    sum theta_i q_i g_i<=mu_t=O(t).                (5)

All constants depend only on the fixed table and fixed theta. In particular
there is no division by the vanishing raised cap-margin eta_t.

### Both good hazards and both contacts are uniformly present

At least one current contact belongs to0 or3, since (3) and Q1,Q2<=0
exclude bad contacts. Suppose along a sequence t->0 it is0. At q1=q2=0,
Q0=3q3; bounded polynomial coefficients and (5) give

    kappa<=Q0=3q3+O(t),

so q3 is bounded below. Equation(5) then gives g3=O(t), and hence

    Q3=B3(X_t)-g3>=kappa-O(t), Q3=2q0+O(t).

Thus q0 is bounded below as well. If the initial contact is3 the same
argument starts with q0 and then gives q3. This compact subsequence argument
produces ONE uniform lower bound epsilon>0 for BOTH good hazards, regardless
of which initial contact was supplied. Together with(4), p=q0,s=q3 lie in
[epsilon,1-alpha/2].

There cannot now be just one contact: singleton0 would force q0=0, and
singleton3 would force q3=0 by the incidence lemma. Thus EXACTLY0 and3
contact for every sufficiently small t. Their gaps are zero, not merely O(t).

### Exact two-contact deformation removes every bad hazard

Fix such a source and its compact suffix Y. Set V=B0(Y)=e0(Y),
F=B3(Y)=e3(Y), and z=(q1,q2). With z=0 the two gaps are

    g0=V+(1-V)s, g3=F-(1+F)p.                    (6)

For general z, g0 is independent of p and affine in s, while g3 is
independent of s and affine in p. Their coefficients and their first
derivatives in z are uniformly bounded polynomials in the compact data.
At a sequence of sources with z->0 and both contacts, limits in (6) give

    V=-s/(1-s)<0, F=p/(1-p)>0.

Thus the coefficients in s,p tend respectively to1-V>=1 and -1-F<=-1.
Uniformly at all small-t sources, their absolute values are at least1/2.
The two contact equations consequently solve separately as explicit ratios
of affine polynomial coefficients:

    s=s(z), p=p(z),                               (7)

with all first z derivatives uniformly bounded. Their current values lie
strictly inside the product cube with the uniform margins above. Small
one-sided decreases of any positive bad coordinate are therefore legal,
keep both good contacts, and keep g1,g2>=kappa/2. Hence the entire changed
prefix remains all-END over the SAME Y in the SAME compact carrier.

On this exact two-contact surface (1) reduces to

    F_t(z)=h(z)F_t(Y)+theta1 z1 g1(z)+theta2 z2 g2(z).

For j=1,2, its derivative at the source is

    partial_j F_t=theta_j g_j+F_t(Y)partial_j h
                 +sum_(i=1,2)theta_i q_i partial_j g_i
                =theta_j g_j+O(t)>0.             (8)

The error is uniform by(5),(7); the positive leading term is at least
theta_j kappa. If q_j>0, decreasing just that bad coordinate slightly
STRICTLY lowers the original full-SUM objective, contradicting its global
minimum. Therefore q1=q2=0 exactly. Equations(6) now prove(03).

All comparisons use finite-prefix maps on actual-tuple closures. No actual
calendar, source dual law, Nash first row, minimizing suffix, native-m
minimality, or compact suffix played after an infinite prefix is used.

### Dependencies and remaining research target

There is one further exact whole-source consequence. Let r be ANY finite-game
Nash root over the genuine tail CAP annotation b=B(Y), and write h_r for its
joint Continue probability. This annotation is not its prescribed payoff.
Nevertheless the full-cap ledger gives

    d_i(prefix(r,Y))=h_r d_i(Y),
    F_t(prefix(r,Y))=h_r F_t(Y).                  (9)

Indeed, set C_i=P_i(r)+H_i(r)b_i and B'_i=max(Q_i,C_i). The general ledger
is q_i(B'_i-Q_i)+(1-q_i)(B'_i-C_i)+h_r d_i(Y); the first two terms vanish
by the finite-game Nash conditions, including boundary hazards. A sure row
would make(9) zero and contradict mu_t>0, so every such r is proper. Properness
also gives C_i>=Q_i for every owner, and hence its prefix is all-END.
Original global minimality and the produced03 contact row therefore give

    h_r>=h_03 for EVERY Nash root r over B(Y).     (10)

The actual source head is a MOST ABSORBING cap-Nash root of its genuine
compact tail. This is a comparison supplied by the original full-SUM minimum;
it does not give Y a native-m minimum or an all-bad-root property.

The exact fixed-weight all-END source is
[strict-column/all-END theorem](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md), PartII. The compact
contact producer is [compact first-contact theorem](../exports/COMPACT_MINIMUM_FIRST_JOINT_CONTACT_REDUCTION.md). The
genericity-free fixed-family alpha-cap producer above uses the already
reviewed raw criterion in Section11 above; its
actual clock uses [global least-Never reduction](../exports/GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md), Sections7 and9.
The margin input is `positive_minimum_fourPlayer_allOwner_quadraticMargins`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
The full-cap and payoff prefix declarations inspected are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`,
`quittingTerminalDeviationDebt_rootThenContinuation_eq` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, and
`quittingTerminalPayoff_rootThenContinuation_eq` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`.

The first03 geometry is proved above. It is not a full counterexample-class
exclusion: the compact tail has negative0 and positive3 cap, and its own
minimization or any native-m property remains unavailable. The concrete
next question is whether the exact two-owner source head can be consumed
against this genuine tail, using the ORIGINAL source F_t and Never.


## 20. Global-alpha consumers of the fixed-family first03 source

These are consumers of the global-alpha limit PRODUCED in Section19.
They retain its OUTERMOST03 row and original Never; the continuation is
not assigned native-m minimality or original full-SUM minimality. They
close source branches, rather than proving a new UE reward-table class.

### A. Entire finite later-zero1 exit branch

#### Produced source and exact branch

Use the complete native fixed13 family, full independent complete-law caps,
the compact actual-tuple closure C of(U,B,e,N), E={U=B}, and A_Z>0.
Keep original Never nu=product N_i. Set alpha=min_E nu>0. The first03
producer in Section19 above, applied along t->0,
produces a GENUINE factorization

    X=prefix03(Y), X,Y in E, nu(X)=alpha,
    B(Y)=(-A,b,c,D), A,D>0,
    q03=(D/(1+D),0,0,A/(1+A)).                 (1)

All original Never coordinates survive this compact extraction. The two
outer hazards and their Continue probabilities are bounded positive.
Every cap of X is strictly positive. The exact quiet outputs therefore give

    b>6(D-A), c>5A+4AD-D.                       (2)

No minimum, all-bad property or actual realization is assigned to Y.

The branch treated here is b<=0,c>0, writing b=-B. When B>0,(2) gives
the old caseI bounds B<6(A-D), c>5A+4AD-D. Its actual incoming rule gives
the unique01 row(B/7,A,0,0); this deduction uses(2), not a minimum at Y.
Follow the genuine01/03 pair cuts until a zero1 starting point

    Z=(-a,0,c0,d), a,c0,d>0                      (3)

is reached, after k complete01,03 cycles. Initial B=0 is included as k=0.
All cuts are actual-closure cuts, retaining ORIGINAL N. The theorem states
that this branch is impossible, for EVERY such finite zero1 exit.

#### Scope of the previously checked pair geometry

The pair algebra, charged outsider ledger and backward feasibility proofs in
[whole-head pair geometry](../exports/OPPOSED_PAIR_WHOLE_HEAD_TRIPLE_ENTRY.md) are used here under their precise raw
inputs, not by importing their selected-m conclusion. Their proofs use only
the following data already present in(1)--(3): genuine E points, positive
Never, original bounds(2), and the actual pair supports before the zero1 exit.

* The full-path outsider ledger keeps owner2 strictly positive at EVERY cut.
  At(3) it gives c0>3a and c0-11a/6-d/2>0. For k=0 these follow directly
  from d<a,c0>5a+4ad-d>4a.
* The standalone NO7 certificate excludes seven-cycle zero-ending suffixes
  WITHOUT an inherited outer bound. Thus k<=6.
* The original bound B<6(A-D) excludes k=6 and makes EVERY non2 quiet
  comparison strict for k<=5. These are the exact NO6AB/quiet certificates,
  not a transfer of the original bound to an internal suffix. Owner2 quiet
  comparisons are strict separately by its positive full-path cap.

Consequently k is in{0,...,5}, and every quiet comparison along the previous
pair head is strict. For k=0 the outer03 quiet1,2 comparisons are strict
because both source caps are positive; there is no previous pair head.
All formulas remain valid when the final01 row is a pure1 row.

#### A genuine extra pure1 row at a positive zero1 point

The compact cofinal-pure1 lemma of [negative-source dispatch](../exports/OPPOSED_PAIR_NEGATIVE_SOURCE_DISPATCH.md),
used exactly as in the zero1 representation section of
[whole-head pair geometry](../exports/OPPOSED_PAIR_WHOLE_HEAD_TRIPLE_ENTRY.md), applies to(3) by the inequalities above.
It produces W in E and a proper singleton1 row of hazard G>a, with the SAME
endpoint prescribed payoffs and ORIGINAL N as Z. No actual calendar for Z
or W and no endpoint minimality is assumed. The cofinal lemma initially
gives prescribed payoff/N identities; these verify all full Nash inequalities:
owner1 is indifferent0, Q0=-G<-a,Q2<=0<c0,Q3=-2G<d.

Split this one singleton1 row into a row of hazard a and a row of hazard

    g=(G-a)/(1-a), 0<g<1.

The intermediate point w=prefix1(g,W) has

    w=(v,0,T,f),
    v=a/(1-a)>0, T=(c0-3a)/(1-a)>0,
    f=(d+a)/(1-a)>0.                            (4)

This split preserves all prescribed payoffs and ORIGINAL N, since the only
absorbing coalition in either singleton row is1. The second row is full
Nash: W1=0, and its outputs0,2,3 are positive whereas their current Quit
offers are nonpositive. Its three quiet comparisons are strict. The first
row has owner0 equality and all other necessary quiet inequalities, also
checked directly from(3),(4). Thus both rows and all prior rows are genuine
full Nash prefixes over W; splitting has introduced no uncontrolled deadline.

Hold W fixed and vary this residual g in a two-sided neighborhood. Then

    (1-g)v'=-2-v, (1-g)f'=-1-f, w1=0.           (5)

The positive signs in(4) persist. The canonical preceding singleton hazard
a(v)=v/(1+v) is reconstructed; its owner0 equality is preserved exactly.

#### Exact whole-head recurrence, including the OUTERMOST03 row

For core caps(x,y,z) in player order0,1,3, the cap-Nash root maps are

    Phi01(x,y,z)=(-x/(1+x),7y/(1-y),
                  (z-x-y)/[(1+x)(1-y)]),
    Phi03(x,y,z)=(-3x/(1-x),
                  (y-6x-6z)/[(1-x)(1+z)],2z/(1+z)).

Only their actual sign domains and proper roots are used. Define
Psi=Phi03 after Phi01, and start(x0,y0,z0)=(v,0,f). The ENTIRE original
head above w is Psi^n with n=k+1 in{1,...,6}: chronologically it is
(03,01)^n, its final01 being the canonical pure1 row. In particular the
new OUTERMOST03 factor is retained; none of the old isolated endpoint
Never derivatives is substituted for it.

If R_n is this whole joint Continue factor, put L_n=1/R_n. Direct algebra
gives, at a step with core(x,y,z),

    xnew=3x/(1+2x), Tcore=1-(2+x)y+z,
    h=(1+x)/[(1+2x)Tcore],
    ynew=h[(13+x)y+12x-6z],
    znew=2(z-x-y)/Tcore.                         (6)

Here xn=3^n v/[1+(3^n-1)v]. The whole original Never is

    nu_whole(g)=R_n(v(g),f(g))(1-g)nu(W).

By(5) its logarithmic derivative, scaled by1-g, is J_n/L_n, where

    J_n=(2+v)partial_v L_n+(1+f)partial_f L_n-L_n. (7)

For n=1,

    L1=(1+2v)(1+f)/(1+v),
    J1=(v+2)(1+f)/(1+v)^2>0.                    (8)

For n=2,...,6 the exact certificate below proves J_n<0 on the ENTIRE
relevant domain v,f>0,y_n>0. The last condition is precisely the original
source's positive owner1 cap, not a sign assumed at a suffix.

#### Seventeen exact ordinary-coefficient checks

This finite certificate has no algebraic sign subdivision and no payload.
Write ell_j=1+(3^j-1)v,m_j=3^j v,a_j=ell_j+m_j,b_j=ell_j+2m_j.
Let the vector(Y_j,Z_j,P_j) start at(0,f,1), and E0=1. Iterate

    [a_j(13ell_j+m_j), -6a_j ell_j, 12a_j m_j;
     -2b_j ell_j,       2b_j ell_j, -2b_j m_j;
     -b_j(2ell_j+m_j),  b_j ell_j,   b_j ell_j],

and E_(j+1)=E_j a_j ell_j. All components are affine in f. Equation(6)
gives y_j=Y_j/P_j and L_j=P_j/E_j; E_j>0 and P_j>0 on every actual head.
Let the numerator of E_n^2 J_n be C(v)f+D(v), and write
Y_n=A(v)f+B(v). The accompanying checker proves, for each n=2,...,6:

    B(v)>0, D(v)<0, B(v)C(v)-A(v)D(v)<0 for EVERY v>0. (9)

Each fact follows because every nonzero ordinary monomial coefficient has
the indicated strict sign. There are only three checks per n. Since

    B*(E_n^2 J_n)=D*Y_n+[BC-AD]*f,

source y_n>0 and P_n>0 imply Y_n>0, and(9) gives J_n<0. For n=1 two
positive-coefficient checks corroborate(8). The exact standard-library
integer program printed below runs all17 checks from the displayed
raw recurrence; it stores no generated polynomials and uses no CAS.

#### Rebuild the genuine whole source and contradict alpha

Vary g slightly, holding its genuine E tail W fixed. Reconstruct every prior
proper pair root by its rational cap-Nash formula, and the OUTERMOST03 root
by(1). Every internal non2 quiet comparison is strict by the old geometric
certificate; owner2 quiet comparisons are strict by the full-path cap ledger.
The original source's quiet1,2 caps were strictly positive. All these
inequalities and all proper hazards persist by continuity. The final
canonical pure1 keeps its one binding quiet0 comparison EXACTLY by its
reconstruction. Thus every altered row remains a full Nash prefix.

Finite continuous prefix maps on actual approximants of W produce genuine
E points. At baseline their whole prescribed payoff and ORIGINAL N are
those of the global-alpha point X. For n=1 choose a slightly SMALLER g;
for n>=2 choose a slightly LARGER g. Equations(7)--(9), nu(W)>0 and
g in(0,1) give original Never STRICTLY below alpha in either case.
This contradicts the definition of alpha. No nonpositive-payoff eligibility
test is needed at this global minimum.

Therefore the ENTIRE inherited caseI zero1-exit branch of the compact first03
global-alpha source is impossible, including the initial-zero1 case k=0.
First013 exits and the negative-owner2 branch remain open. This conclusion
does not claim a finite-t full-SUM descent or give any compact tail a minimum.

The complete integer program for the seventeen sign checks is:

```python
def norm(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p)


def add(p, q):
    return norm([(p[i] if i < len(p) else 0) +
                 (q[i] if i < len(q) else 0)
                 for i in range(max(len(p), len(q)))])


def scale(c, p):
    return norm([c * x for x in p])


def sub(p, q):
    return add(p, scale(-1, q))


def mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return norm(out)


def diff(p):
    return norm([i * p[i] for i in range(1, len(p))] or [0])


def affine_combine(row, vec):
    return tuple(sum_poly(mul(c, x[j]) for c, x in zip(row, vec))
                 for j in range(2))


def sum_poly(polys):
    out = (0,)
    for p in polys:
        out = add(out, p)
    return out


checks = 0


def sign(p, wanted):
    global checks
    assert any(p), "zero polynomial"
    assert all(wanted * c >= 0 for c in p), (wanted, p)
    checks += 1


# Every vector component is (constant-in-f, coefficient-of-f).
vec = [((0,), (0,)), ((0,), (1,)), ((1,), (0,))]
E = (1,)
for j in range(6):
    ell = (1, 3 ** j - 1)
    m = (0, 3 ** j)
    aa = add(ell, m)
    bb = add(ell, scale(2, m))
    matrix = [
        [mul(aa, add(scale(13, ell), m)),
         scale(-6, mul(aa, ell)), scale(12, mul(aa, m))],
        [scale(-2, mul(bb, ell)), scale(2, mul(bb, ell)),
         scale(-2, mul(bb, m))],
        [scale(-1, mul(bb, add(scale(2, ell), m))),
         mul(bb, ell), mul(bb, ell)],
    ]
    vec = [affine_combine(row, vec) for row in matrix]
    E = mul(E, mul(aa, ell))
    Y, Z, L = vec
    # E^2 * [(2+v)Lactual_v + (1+f)Lactual_f - Lactual].
    J = [add(mul((2, 1), sub(mul(diff(L[i]), E), mul(L[i], diff(E)))),
             mul(E, sub(L[1], L[0])) if i == 0 else (0,))
         for i in range(2)]
    if j == 0:
        sign(J[0], 1)
        sign(J[1], 1)
        print("n=1: whole Never derivative strictly positive")
    else:
        B, A = Y
        D, C = J
        cross = sub(mul(B, C), mul(A, D))
        sign(B, 1)
        sign(D, -1)
        sign(cross, -1)
        # B*J = D*Y + (B*C-A*D)*f, with B>0,Y>0,f>0.
        print("n=%d: whole Never derivative strictly negative; degrees %s" %
              (j + 1, (len(B) - 1, len(D) - 1, len(cross) - 1)))

print("Exact ordinary-monomial sign checks passed:", checks)
```

### B. Immediate first013 must have V<-a

#### Exact source and inherited bounds

Use the complete fixed13 raw family, independent complete stopping laws,
full unilateral complete-law caps, and A_Z>0. Let C be the compact actual
(U,B,e,N) carrier, E={U=B}, nu=product N_i and alpha=min_E nu>0. The first03
producer Section19 above, followed along t->0, supplies
X=prefix03(Y), X,Y in E, nu(X)=alpha and EVERY cap of X strictly positive.
In its caseI branch write Y=(-A,-B,C2,D), A,B,C2,D>0. Then

    B<6(A-D), C2>5A+4AD-D.

Suppose the genuine immediate word below Y is01,013, the last row having
hazards(a,b,0,c) and genuine E tail Z=(V,-E,T,F). The [first-triple raw geometry](../exports/OPPOSED_PAIR_FIRST_TRIPLE_NORMAL_FORM.md), which uses these original bounds without tail minimality, gives

    0<a<1/242, 0<b<a/23,
    103a/23<c<(9a-b)/2,
    E=(a+7c)/[(1-a)(1-c)]>29a and >29F,
    F=(a-b)/[(1-a)(1-b)],
    22a/23<F<5a/4, E<34a.                    (1)

The cap of owner2 just ABOVE this first013 is strictly positive, by the
full previous-head outsider ledger. All tails retain ORIGINAL marginal N.
Put k=Z0(13), kappa=2-k. Its active0 equation is

    V(1-b)(1-c)=b-c+kappa*b*c.                 (2)

The theorem proved here is V<-a. Its proof uses the following whole-head bound, independent of V,T,k:

    Lold=(Hout*H0)^-1<1+(97/2)a,              (3)

where H0 is survival through01,013 and Hout is the ORIGINAL outer03
survival. The raw two-row bound is H0^-1<1+33a, and exact reconstruction gives

    A=(3c-b)/(1-b+3c)<27a/2,
    D=(9a-b-2c)/[(1+7a+c)(1-b+3c)]<a/23,
    Hout=1/[(1+A)(1+D)].

Thus Lold<(1+33a)(1+27a/2)(1+a/23). After subtracting1 and dividing by a,
this positive-coefficient expression is increasing. At a=1/242 it is
11851657/244904, less than97/2 by26187/244904. This proves(3), pricing
every original row.

#### The stationary bracket is produced uniformly for V>=-a

Assume V>=-a. Treat kappa as the affine function of V in(2), and
put kappa0=(c-b)/(bc)=1/b-1/c. Since c-b>102a/23, at V=-a we have

    kappa(-a)>(c-b-a)/(bc)
              >(79/102)kappa0
              >(7189/408)/a>2/a.             (4)

Here kappa0>91/(4a) follows from b<a/23,c>4a. Thus kappa>2/a uniformly,
and k=2-kappa<-22. The old stationary013 families are genuine produced
stationary roots, not assumed rows: their positive root d(t) satisfies

    (t-1)d^2+(7t^2-8t-6)d+t(6-7t)=0,

and K(s,d)=s+4-3d+(2-s)/d+(3d-4)/s equals the raw k. On the symmetric
family s=t, K(t,d(t))->-infinity at0 and
K(a,d(a))>-2/a+3-2a>2-kappa=k. On the hyperbola family
s=(1-2t)/(2(1-t)), K(1/6,d(2/5))>-11>k and K->-infinity at1/2.
IVT therefore produces t_-<a and2/5<t_+<1/2 with these SAME raw k.

As proved from the stationary full behavioral cap tests in the [first-triple geometry](../exports/OPPOSED_PAIR_FIRST_TRIPLE_NORMAL_FORM.md), A_Z>0 forces, for l=Z2(13),R=Z2(013),

    L(t)=(1-t)l+tR<-k/2

at each of these two roots. Affinity gives

    L(u)<-k/2 for every t_-<=u<=t_+.           (5)

This is why the bracket remains available when V is mildly negative;
positivity of T has not been assumed.

#### High V: produce and consume the direct FULL01 replacement

Suppose V>=E-F. The passive2 offer at the first013 is

    P2=a+3b-5c+2bc-abc+bc L(a).

Using(2),(5),

    P2<a+(5/2)b-(9/2)c+bc(1-a)
                         +(V/2)(1-b)(1-c)
       <(V/2)(1-b)(1-c).                     (H1)

For the last inequality, b<1/4 implies bc(1-a)<c/4, and b<a/23,c>4a give

a+(5/2)b-(17/4)c < [1+5/46-17]a<0. Since the owner2 cap just above
this actual row is positive, its genuine tail satisfies

    T>-V/[2(1-a)].

Consequently

    T+E+3V+4EV
      >E+[3-1/(2(1-a))]V+4EV>0.              (H2)

Here E>0,V>=E-F>0,a<1/242. At the genuine Z use the canonical01 root
with odds(E,V). Its two active equalities hold exactly; quiet3 has gap
F-E+V>=0. Quiet2 has Continue numerator T+E+3V+4EV>0 by(H2), whereas
its Quit offer is nonpositive by participant2 signs. This is FULL Nash.
Its survival is1/[(1+E)(1+V)]. Equation(1) gives

    (1+E)(1+V)>1+2E-F>1+(227/4)a>Lold.

Prefixing the genuine Z therefore gives an E point with ORIGINAL Never
strictly below alpha, a contradiction. The endpoint V=E-F is included.
This retains the old high-sector comparison with its full quiet2 proof.

#### Produce T>0 in the remaining low sector from the actual owner2 cap

It remains to treat -a<=V<E-F. The passive2 offer at the first013 is

    P2=a+3b-5c+2bc-abc+bc L(a).

Using(2),(5),

    P2<a+(5/2)b-(9/2)c+bc(1-a)
                         +(V/2)(1-b)(1-c).   (6)

Replace V by E-F, which is strictly larger. Twice1-a times the resulting
upper bound equals

    N=2a-2a^2+6b-6ab
       +c[-2+10a-6b-4ab+2a^2b]
     <2a+6b+c(-2+10a)<0.                    (7)

For the last sign use b<a/23,c>4a and a<1/242: the c coefficient is
negative and -2+10a<-19/10, so the expression is less than
[2+6/23-38/5]a<0. All discarded terms are nonpositive; in particular
-4ab+2a^2b<0. Hence P2<0. The owner2 cap w2 just above this actual row is
positive and w2=P2+(1-a)(1-b)(1-c)T, so T>0 is PRODUCED.

#### Produce the next actual013 and all quantitative guards

The genuine tail Z has an incoming row. Its positive Never makes the row
proper; its negative1 cap excludes an all-zero row. Since T>0, owner2 is
quiet. On q2=0 the fixed forced-Quit polynomials are

    Q0=-q1+3q3,Q1=-7q0-q3,Q3=2q0-2q1.

Its q0 cannot be0: negative1 would then require q3>0, but active3 would
have F=-2q1<=0. If q3=0, owner0 equality gives q1=-V<=a, while quiet1
gives q0>=E/7. Quiet3 would require
F>=2q0-2q1>=2E/7-2a>F by E>29a,F<5a/4. Thus q3>0.
If q1=0, active3 gives q0=F/2 and active0 gives V=3q3. Quiet1 then
requires E<=7F/2+V/3<E/3+19F/6, contradicting E>29F.
Every core owner is therefore active. The UNIQUE actual row is(p,q,0,r),
with

    q=(6E-21F-2V)/44,
    p=q+F/2, r=(V+q)/3.                      (8)

It has a genuine E tail Z1=(W,-E1,T1,F1). Uniformly on[-a,E-F],

    q>97F/44>97a/46>2a,
    q<(204a+2a)/44=103a/22,
    p<(103/22+5/8)a=(467/88)a<1/40,
    p<5q/4,
    r<(34+103/22)a/3<1/4.                    (9)

The first bound follows by evaluating q at the upper endpoint V=E-F,
where q=(4E-19F)/44>97F/44.

The affine function r(V) is increasing. At V=-a,
q(-a)=q0+a/22, where q0=(6E-21F)/44>591a/176. Consequently

    r>141a/176.                              (10)

Also r>q/5: for V>=0 it is at least q/3; for V<0, q>q0>3a and
V>=-a imply r>2q/9. The same roots t_- and t_+ bracket p, by p>2a
and p<1/40, so(5) also gives L(p)<-k/2.

The product kappa(V)q(V) is a concave quadratic in V. At V=-a,
by(4) and q(-a)>599a/176,

    kappa*q>(7189/408)(599/176)>59.

At V=E-F the exact inequality E-F>7c/(1-c) gives
kappa>8/b-1/c-7>100/a, while q>2a, hence kappa*q>200.
Concavity now proves the uniform strict bound

    kappa*q>59 throughout[-a,E-F].            (11)

#### Full01 at Z1, including owner2, is produced

The exact next-tail identities are

    W=[q-r+kappa*q*r]/[(1-q)(1-r)],
    E1=(p+7r)/[(1-p)(1-r)],
    F1=(p-q)/[(1-p)(1-q)]>0,
    h=(1-p)(1-q)(1-r).

Equations(9)--(11) give

    hW=(1-p)[q+(kappa*q-1)r]
        >(39/40)[q+58q/5]>12q>0.             (12)

Moreover W>E1-F1: after multiplication by the positive common denominator,
this difference has numerator

    r[kappa*q*(1-p)-8(1-q)]>0.                (13)

The passive2 offer Pi at this actual fourth row obeys, using L(p)<-k/2,

    Pi<p+(5/2)q-(9/2)r+qr(1-p)
                            +(W/2)(1-q)(1-r)
       <4q+(W/2)(1-q)(1-r),                  (14)

by p<5q/4,r<1/4. Since T>0, hT1=T-Pi>-Pi. Thus

    h[T1+E1+3W+4E1W]
      >[3-1/(2(1-p))]hW-4q
      >2hW-4q>0.                            (15)

At the genuine Z1 use the canonical01 root with odds(E1,W). Its active
indifferences hold exactly. Quiet3 holds strictly by(13). Its quiet2
Continue value has numerator T1+E1+3W+4E1W, positive by(15), while its
Quit offer is nonpositive by participant2 signs. This is a FULL four-owner
Nash row over Z1. No sign of T1 was assumed or inferred.

#### Its gain pays for every original row

The exact survival identity for the fourth row and the replacement is

    h(1+E1)(1+W)
      =(1+6r+pr)[1-2r+(kappa+1)qr]/(1-r)
      >(1+6r)[1+(kappa*q-1)r]
      >1+(kappa*q+5)r
      >1+(564/11)a>1+(97/2)a>Lold.            (16)

The penultimate inequality uses(10),(11), since64*141/176=564/11 and
564/11-97/2=61/22>0. This compares the FULL replacement at the genuine Z1
against ALL FOUR old rows03,01,013,013. Their old original Never is
Hout*H0*h*nu(Z1)=alpha. The replacement Never is
nu(Z1)/[(1+E1)(1+W)]<alpha. Continuous finite prefixing of actual
approximants to Z1 gives an E point with this ORIGINAL Never, contradicting
its global minimum.

The high sector and(16) exclude every V>=-a. Therefore any genuine
immediate013 tail of the global-alpha first03 caseI source has V<-a.
This is an original-global-alpha consumer. It does not give Y,Z,Z1 a
minimum, change the full-SUM objective, or close the remaining V<-a,
longer first013 or negative-owner2 branches.


The rational constant comparisons can also be reproduced directly:

```python
from fractions import Fraction as F

checks = {
    "kappa endpoint identity": F(79, 102) * F(91, 4) == F(7189, 408),
    "kappa endpoint bracket": F(7189, 408) > 2,
    "coupled lower endpoint": F(7189, 408) * F(599, 176) > 59,
    "upper endpoint kappa": F(735, 4) - F(7, 242) > 100,
    "q lower bound": F(97, 46) > 2,
    "p proper small": F(467, 88 * 242) < F(1, 40),
    "r below quarter": (34 + F(103, 22)) / (3 * 242) < F(1, 4),
    "r lower identity": (F(591, 176) - F(21, 22)) / 3 == F(141, 176),
    "first passive coefficient": -2 + F(10, 242) < -F(19, 10),
    "first passive negative": 2 + F(6, 23) - F(38, 5) < 0,
    "second positive W": F(39, 40) * (1 + F(58, 5)) > 12,
    "second quiet2 coefficient": 3 - 1 / (2 * F(39, 40)) > 2,
    "whole gain identity": 64 * F(141, 176) == F(564, 11),
    "whole gain strict": F(564, 11) > F(97, 2),
    "high gain strict": F(227, 4) > F(97, 2),
}
for name, valid in checks.items():
    assert valid, name
print("PASS: %d exact rational constant checks" % len(checks))
```

### Surviving source modes

The new global-alpha branch has no inherited caseI zero1 exit and every
immediate01,013 tail has V<-a, where a is its first013 owner0 hazard. Longer first013 heads, the remaining V<-a continuations
and the negative-owner2 chamber still need a whole-source consumer.
These statements do not transfer the native-m four-row exclusion to alpha,
or assert that first013 has only the two native-m histories.


## 21. One whole-law contact dual and an integrated two-clock consumer

Part A concerns ACTUAL complete laws. Parts B-C use bounded variations at
a compact marked source; actual attainment is not inferred.

### A. A common contact multiplier for the entire calendar

#### Actual data and conclusion

Let I be a nonempty finite player set (Fin4 in the application). Native
own-singleton, live and literal Never rewards are zero, and all rewards
are bounded. Stopping laws P_i on natural dates plus Never are independent;
every complete-law unilateral replacement is allowed. Retain native payoff
U, full cap B, native Never offer e, and ORIGINAL N_i=P_i(Never)>0. Assume
P is an ACTUAL global minimum, over all independent complete laws, of

    F(P)=sum_i theta_i[B_i(P)-U_i(P)]+rho nu(P),
    theta_i>0,rho>0,nu=product N_i,

and every native cap is END: B_i=e_i. Write A_i for the set of finite pure
deadlines attaining B_i, together with native Never. This is a compact
subset of the one-point compactification of the natural dates: native own
singleton zero makes finite response values tend to the Never offer.

**Producer.** There are probability laws mu_i supported on A_i such that
ONE common tuple mu satisfies ALL of the following whole-law inequalities.
Define H_j=product_(k!=j)N_k and the bounded action cost

    W_j(a)=sum_(i!=j)theta_i u_i(mu_i,delta_a,P_(-i,-j))
                  -sum_i theta_i u_i(delta_a,P_(-j))
                  +rho H_j 1_(a=Never).                    (1)

In the first term i uses mu_i, j uses delta_a and all others their P laws;
in the second term j uses delta_a and all others P. Then

    W_j(a)>=W_j(Never) for EVERY finite a,
    W_j(a)=W_j(Never) whenever P_j(a)>0.                 (COMP)

Thus P_j minimizes this LINEAR cost over all complete laws, while mu_i is a
native best-response law. The two laws are not asserted equal, and mu_j
need not minimize W_j. In particular mixing P_j toward mu_j is not silently
treated as a two-sided stationary variation.

Mu is a DUAL native response law, not a prescribed law at the raised table.
Its Never atom represents an available native END response. It is never
substituted for the ORIGINAL prescribed N_i. Raised finite caps and raised
literal Never remain distinct in the source application.

#### Finite-dimensional separation and global consistency

For each owner and each action a consider the complete-law direction
delta_a-P_j. Positive small mixtures are always legal; both signs are legal
when P_j(a)>0. Every finite collection of these directions has a common
small legal parameter cone: the modified law is
(1-sum z_a)P_j+sum z_a delta_a, with z_a>=0 only at unsupported targets.
All selected supported masses stay positive on a sufficiently small box.

On such a finite family, every fixed response payoff is a smooth polynomial
in its parameters. Its gradient, as a function of the tester date, is
continuous at native Never. Indeed each direction involves only fixed
finite target dates, Never, and old laws; the late finite response limit
and its finite-parameter derivatives agree with native Never, uniformly on
the finite parameter box. Bounded rewards and vanishing finite law tails
prove these assertions. Consequently the derivative of the complete cap
is the maximum of response derivatives over its ACTUAL active set A_i.

The directional derivative of F is therefore the support function of the
compact convex gradient image obtained by averaging each owner's active
response derivatives against a probability law mu_i on A_i. If this image
missed the dual legal cone (zero on two-sided coordinates, nonnegative on
one-sided coordinates), finite-dimensional separation would give a legal
direction with negative derivative. Global minimality forbids it. Hence
there is a tuple of laws mu for this finite family satisfying all its
stationarity/equality and one-sided inequality constraints.

The product of the spaces of probability measures on compact A_i is compact
in the weak topology. Each coordinate constraint is closed: the relevant
tester-gradient function is continuous, including at native Never. The
finite-family result supplies the finite intersection property. Compactness
therefore produces ONE tuple satisfying every countable pure-target
constraint simultaneously. This is an actual multiplier producer, not an
assumption of a common dual chosen separately for different windows.

The averaged cap functional is sum_i theta_i u_i(mu_i,P_-i). Its derivative
with respect to P_j in direction delta_a-P_j is exactly
W_j(a)-sum_b P_j(b)W_j(b). The constraint equals zero at every supported
action, including Never since N_j>0, and is nonnegative at every other
action. This proves(COMP).

#### Exact occupation at persistent owners

Put gamma_i=mu_i(Never). For an owner j with unbounded finite stopping
support choose positive hazards at arbitrarily late dates. These finite
hazard directions can either be included in the same finite-family/FIP
construction or expressed as signed complete-law variations supported on
P_j's existing support, so their averaged derivative is zero for this SAME
mu. For a fixed finite tester, its payoff ignores all sufficiently late
hazard changes. Tester derivatives are uniformly bounded by a fixed reward
constant, while the native Never derivative tends to
(nu/N_i)Gamma_ij. Bounded convergence against the FIXED measure mu_i gives

    r^T Gamma>=rho one^T, with equality at every persistent column,
    r_i=theta_i(gamma_i/N_i-1).                          (2)

Finite dual-contact mass is allowed at arbitrarily late dates; its total
tail mass tends to zero. No pointwise comparison of that mass to a physical
hazard is assumed or concluded. This passage does not discard a moving
window's multiplier mass: mu was made globally consistent first.

The inequality at EVERY column, including nonpersistent owners, follows
directly from whole-law(COMP). Send the pure target a to infinity. A late
finite target instead of Never has limiting extra payoff Gamma_ij only
when every other relevant prescribed clock and the dual responder Never.
Consequently

    W_j(a)-W_j(Never)
       ->H_j[(r^T Gamma)_j-rho]>=0.

At persistent prescribed atom dates the left side is exactly zero, proving
the equality. This also gives(2) without a separate hazard calculation.

If all four owners are persistent and Gamma is invertible, let
s_i=sum_j(Gamma^-1)_ji. Equation(2) gives the EXACT identities

    gamma_i=N_i(1+rho s_i/theta_i),
    mu_i(finite)=1-N_i-rho N_i s_i/theta_i.              (OCC)

These hold even with an unbounded set of finite cap contacts. They are not
the bounded-contact reciprocity/PRICE identity.

Let C be the owners having any finite cap contact. If i notin C, gamma_i=1,
so i must have s_i>0 and

    1-N_i=rho s_i/(theta_i+rho s_i)<=rho s_i/theta_i.     (3)

Here all-four persistence excludes s_i<=0. If additionally nu(P)<=alpha<1,

    sum_(i in C)(1-N_i)
       >=1-alpha-rho sum_i s_i^+/theta_i.                (4)

For sufficiently small rho, finite-contact OWNERS therefore carry a fixed
positive amount of prescribed finite mass. Moreover any owner with
1-N_i>=delta has positive finite DUAL contact mass at least
delta-rho s_i^+/theta_i, by(OCC). These are quantitative occupation
constraints on the actual source, not a new UE theorem.

#### Exact small sanity test

Take two owners with Gamma12=Gamma21=1 and joining rewards J12=J21=2.
Let P_i put mass f_i/2^(a+1) at every a>=0 and N_i=1-f_i,0<f_i<1.
Every native finite response and Never has payoff f_(-i), so these are
actual native Nash clocks. They CANNOT be a global minimum of F for any
rho>0, and the global multiplier equations detect the failure.

The owner1 whole-law equalities in(COMP) imply, for every a,

    gamma_2+mu_2(>a finite)+2mu_2(a)
          =N_2(1+rho/theta_2)+3f_2/2^(a+1).

The late limit gives gamma_2=N_2(1+rho/theta_2), agreeing with(OCC).
Writing T_a=mu_2({a,a+1,...}), the remaining equations are

    2T_a-T_(a+1)=3f_2/2^(a+1), T_a->0.

Their unique summable solution is T_a=f_2/2^a; thus finite mu_2 mass is f_2
and gamma_2=N_2, contradicting rho>0. This exact test uses neither a
positive absorbing gap nor a claimed Fin4 counterexample. It checks that
the full atom-complementarity equations contain more than the scalar
occupation identity alone.

#### Boundary of the argument and bounded overlap

The finite-window cap and multiplier principles are already used in the
actual-minimum contact/support packet. The new item here is ONE globally
consistent dual tuple, whole-law complementarity and(OCC) for UNBOUNDED
contact sets. No published/exported producer with these whole-law fields
was found in the bounded source neighborhood inspected here.

One cannot infer the old bounded-contact Hessian conclusion by treating
the finite mu tail as negligible. Tiny positive contact weights can still
pin arbitrarily small physical hazard variations. Exact level-manifold
tangency or a quantitative mu-tail/hazard comparison is needed before a
PSD limit. No PRICE identity, symmetrizability, support closure or strict
SUM improvement for the full unbounded-contact branch is claimed here.
### B. A compact deletion identity removes persistence and actual attainment

#### Exact data and result

There are four owners. Native rewards Z are finite, own-singleton, live and
literal Never rewards are zero. The stopping laws are independent. Every
complete behavioral replacement is allowed; equivalently the cap is over
all finite pure queries and native Never. Let C be the compact closure of
actual tuples (U,B,e,N), retaining each ORIGINAL marginal Never mass N_i.
Write nu=product_i N_i and d_i=B_i-U_i>=0.

Fix ONE positive weight vector theta before rho. For rho>0 consider the
TRUE full objective

    F_rho=sum_i theta_i d_i+rho nu.

Let X be a global minimum on C with B=e and N_i>0. Use the canonical marked
ordered-clock representation of X and the fixed bounded-density
transport theorem in the [compact contact dichotomy](../exports/COMPACT_END_SEPARATED_CONTACT_EXCLUSION.md), Sections2-3. Its finite
query carrier is compact T with final finite END c; native Never is a
separate isolated label. All physical laws q_i have bounded densities with
respect to the common marked mixture law, and q_i({c})=0. The whole native
tuple of every fixed bounded-density reweighting belongs to the SAME C.
These are the only clock-compiler inputs used below.

**General identity.** There are probability tester laws mu_i supported on
the native cap contacts on the represented calendar in T union {Never}, one common tuple for all
four owner directions, such that for EVERY owner j,

    F_rho(X)=rho H_j
      +sum_(i!=j) theta_i u_i(mu_i-q_i, Never_j, q_(-i,-j)),       (DEL)
    H_j=product_(k!=j)N_k.

The payoff with a signed first law denotes its linear extension. The mu are
dual response laws, and no assertion says that mu_i is a prescribed-law
optimizer. This identity needs neither persistence nor a pointwise
whole-law complementarity law.

**Consumed subcase.** Suppose exactly two physical owners a,b have finite
mass, so q_k=Never for k outside {a,b}, and suppose every outside owner's
native cap contacts are contained in {c,Never}. Then

    N_a=N_b=N,
    nu(X)=N^2,
    F_rho(X)=rho N,
    sum_i theta_i d_i(X)=rho N(1-N).                         (TWO)

In particular fix the native table and theta, put

    E={Y in C:d_i(Y)=0 for every i}, alpha=min_(Y in E)nu(Y),

and assume 0<alpha<1. There is rho_0>0 such that NO global minimum of
F_rho, 0<rho<rho_0, can satisfy the displayed consumed-subcase hypotheses.
The pair a,b may depend on rho. This excludes that entire compact source
configuration, including last atoms and nonrealized clocks. It does not
exclude outside interior contact mass, three/four physically active owners,
or the alpha=1 endpoint.

#### Four legal two-sided directions and one common dual

For each owner set, at the level of complete marked laws,

    q_j(z_j)=(1-z_j)q_j+z_j delta_Never.

Both signs of sufficiently small z_j are legal because N_j>0. More
explicitly retain the old density r_j on the finite part and on the separate
Never region, and multiply it by

    1-z_j on the finite part,
    1-z_j+z_j/N_j on the Never region.

These factors are positive near zero, integrate to one, and give exactly
the stated complete law. The densities remain bounded. This also works
when N_j=1, when the law direction is simply zero. Hence the bounded
transport compiler puts the WHOLE changed tuple in C for every z in one
open rectangle around zero. The represented X is therefore a local minimum
on this finite four-dimensional family, without an actual realization.

For each owner i and query x in K=T union {Never}, its response value
v_i(x,z) is a polynomial in z, since each opponent law is affine. Its
coefficients, and therefore its z gradients, are continuous in x: this is
the marked query-kernel continuity for fixed bounded densities. K is compact
and Never remains a separate component. Consequently the complete cap is

    B_i(z)=max_(x in K)v_i(x,z),

and its directional derivative at zero is the maximum of the directional
gradients over the compact ACTUAL active set A_i={x:v_i(x,0)=B_i(X)}.
This is the elementary finite-dimensional maximum derivative: uniform
polynomial Taylor expansion gives the upper bound after extracting an
active limiting maximizer, while any fixed active query gives the lower
bound.

Let G be the compact convex set of gradients obtained by choosing one
probability law mu_i on each A_i and taking the gradient of

    L_mu(z)=sum_i theta_i u_i(mu_i,q_(-i)(z))
               -sum_i theta_i U_i(q(z))+rho nu(q(z)).

Compactness can equivalently be obtained by convex hulls of the compact
gradient images in R^4; finite support of at most five queries per owner
suffices by Caratheodory. The directional derivative of F_rho is the
support function h_G. If 0 were absent from G, strict finite-dimensional
separation would provide a direction v with h_G(v)<0. The open legal
rectangle would then give a strict decrease of the full objective. Thus
0 belongs to G. Choose ONE corresponding tuple mu. It satisfies

    L_mu(0)=F_rho(X), grad L_mu(0)=0.                       (STAT)

This is only one finite common-dual construction; no countable finite
intersection argument or limiting contact multiplier is needed.

#### Exact deletion algebra

For this fixed mu define the bounded action cost

    W_j(x)=sum_(i!=j) theta_i u_i(mu_i,delta_x,q_(-i,-j))
              -sum_i theta_i u_i(delta_x,q_(-j))
              +rho H_j 1_(x=Never).

In the second sum owner j uses delta_x. The derivative of L_mu in the
jth displayed law direction is exactly

    W_j(Never)-integral W_j(x) dq_j(x)=0.                  (1)

The two sides can be evaluated without any timing decomposition. Active
dual support gives u_i(mu_i,q_-i)=B_i. Therefore

    integral W_j dq_j
        =sum_(i!=j) theta_i B_i-sum_i theta_i U_i+rho nu
        =F_rho(X)-theta_j B_j.                            (2)

At the Never target, recipient j's payoff is its native Never offer
e_j=B_j, while every other recipient uses its original physical law:

    W_j(Never)
        =sum_(i!=j) theta_i u_i(mu_i-q_i,Never_j,q_(-i,-j))
              -theta_j B_j+rho H_j.                      (3)

Equating (2) and (3) proves (DEL). In particular no dual Never mass is
identified with any ORIGINAL N_i, and no equality is imposed at a
dual-only finite atom.

#### Removing outside dual END atoms and consuming two physical clocks

For every bounded-density variation above, all physical finite mass is
strictly before c, with zero physical atom at c. A native pure query at c
therefore has exactly the SAME payoff kernel as native Never. If an
opponent exits before c both replies see that exit; when every opponent is
Never, the c reply quits alone at own-singleton reward zero, matching the
literal Never reward zero. This holds throughout the four-parameter
family, not merely at X.

For each outside owner k, the assumed contact restriction puts mu_k on
{c,Never}. Replace it by delta_Never. The averaged functional L_mu(z) is
unchanged for every z, so the same common stationarity and (DEL) survive.
Since q_k=Never as well, mu_k-q_k=0 for all outside owners.

Now apply (DEL) with j=a. All terms with outside recipient i vanish. The
only remaining recipient is b; after replacing a by Never all its
opponents are Never. Every pure b query, finite or Never, then pays zero,
so u_b(mu_b-q_b,Never_-b)=0. Thus F_rho=rho H_a=rho N_b.
Interchanging a,b gives F_rho=rho N_a. Since rho>0 the original Never
masses agree. Their product and the definition of F give (TWO).

The assumption on outside contacts is substantive. An outside finite
interior tester may stop before a future active physical clock and changes
the averaged functional. Merely prescribing that outside owner Never
does not erase its dual term in (DEL).

#### The fixed-table small-price contradiction

All native debts are nonnegative on C. E is nonempty because native
AllNever has zero cap and payoff. Compactness gives an alpha-minimizer.
For every global minimum X_rho, comparison with it gives

    0<=D_theta(X_rho)<=rho alpha,
    nu(X_rho)<=F_rho(X_rho)/rho<=alpha,
    D_theta=sum_i theta_i d_i.

As rho tends to zero, every cluster of X_rho lies in E, since all theta
are fixed and positive. Hence every cluster has nu>=alpha. The displayed
upper bounds then imply, for EVERY selection of global minima,

    nu(X_rho)->alpha,
    F_rho(X_rho)/rho->alpha.                              (ENV)

If arbitrarily small rho admitted the consumed subcase, select such a
sequence. Formula (TWO) gives nu=N^2 and F_rho/rho=N on that sequence.
Equation (ENV) would force simultaneously N->sqrt(alpha) and N->alpha.
Thus alpha=sqrt(alpha), impossible for 0<alpha<1. This sequential
contradiction proves one rho_0 excluding every minimum in the class.

No continuous selection of minima, fixed contact gap, persistence,
unbounded physical support or comparison of a dual tail to a physical tail
was used. The argument remains valid when the physical clock support is
bounded and when the represented compact minimum has no actual calendar.


### C. Every surviving two-active source needs a genuine outside contact

Retain the preceding data and its four-dimensional Never-mixing family.
For an owner i and pure query x in T union {Never}, write k_(i,x)(t_-i)
for its native payoff kernel as a bounded measurable function of all
opponents' complete marked clock draws. Call x a KERNEL ALIAS of Never at
the source if

    k_(i,x)=k_(i,Never) q_-i-almost surely.                 (ALIAS)

This is an equality of payoff kernels on the independent product law. An
equality of expected response values alone is insufficient.

**Strengthened consumed class.** In the two-physical-active-owner conclusion
of the preceding deletion theorem, replace the hypothesis that every
outside owner's cap contacts lie in {c,Never} by the weaker hypothesis that
EVERY outside native cap contact is a kernel alias of Never. Then the same
conclusions hold:

    N_a=N_b=N, nu=N^2, F_rho=rho N,

and, for the fixed-table 0<alpha<1 branch, all sufficiently small rho
exclude the entire strengthened source class. Thus every surviving
two-physical-active source at those prices has an outside native best
response whose payoff kernel differs from Never on an event of positive
original product probability. That is a necessary source restriction,
not a completed consumer of such a genuine outside contact.

Proof. Since N_j>0, the pure Never law is absolutely continuous with
respect to q_j. In the four legal directions the exact Radon--Nikodym
factors of the changed laws q_j(z_j) relative to q_j are

    1-z_j on the finite part,
    1-z_j+z_j/N_j at Never.

They are positive and bounded on one open parameter rectangle. Hence
every changed opponent product q_-i(z) is absolutely continuous with
respect to the ORIGINAL q_-i. Any equality (ALIAS) therefore holds almost
surely under EVERY q_-i(z) in that rectangle, giving

    u_i(delta_x,q_-i(z))=u_i(Never_i,q_-i(z)).              (1)

The common-dual construction can choose each mu_i with finite support of
at most five active queries. Under the strengthened hypothesis every
query in the support of an outside mu_i satisfies (1). Averaging shows
that replacing this entire mu_i by delta_Never leaves its averaged cap
functional unchanged throughout the rectangle. The other averaged terms
are untouched. Thus the SAME L_mu(z) and its four stationarity equations
survive after every outside dual law is made literally Never.

The exact deletion algebra and two-owner cancellation in the preceding proof
now apply verbatim. This proves the strengthened claim. There is no need
to equate a dual law with a primal optimizer, no simultaneous choice of
pointwise null sets over the full query carrier, and no insertion of an
off-mixture physical atom. Native c is automatically an alias because
all physical laws have zero c atom and native own singleton is zero.

This weakening also permits unused finite aliases after all physical
finite mass. It does not permit a finite contact that merely has the same
expected value as Never while paying differently on some positive-mass
opponent event; such genuine contact kernels are precisely what remains.

### A precise limit of the multiplier argument

The dual law is a native best response, while the prescribed law minimizes
the team cost W. Those are distinct optimization problems. For example, set

    Gamma=[0,3,-1,-1;3,0,-1,-1;-1,-1,0,3;-1,-1,3,0].

Own singletons and allQuit pay0. Another singleton pays Gamma_ij. A pair
containing i pays (7Gamma_ij+1)/8; a triple containing i and missing l
pays (Gamma_il-1)/8. Passive pairs and triples pay0. This specifies all60
rewards; detGamma=45 and its inverse is strictly positive. Take every
prescribed law P_i=(delta0+deltaNever)/2. Then U_i=B_i=e_i=1/8 and N_i=1/2.
Every finite query is a contact. For arbitrary theta>0 and
0<rho<min(theta)/4, the native contact laws

    mu_i(0)=1/2-rho/theta_i, mu_i(1)=rho/(4theta_i),
    mu_i(Never)=1/2+3rho/(4theta_i)

satisfy the EXACT whole-law team-cost gaps

    W_j(0)-W_j(Never)=0,
    W_j(1)-W_j(Never)=9rho/64,
    W_j(a)-W_j(Never)=rho/16 for every a>=2.

These follow by splitting the remaining physical clocks between0 and Never;
the needed column sums are sum_i Gamma_ij=1 and
sum_(i!=j) Z_i({i,j})=5/4. Thus COMP holds for every target action, but
mu_j gives positive mass to the STRICTLY suboptimal team-cost action1.
Pure allQuit is absorbing Nash, so A=0 and the example is not globally
minimizing: its F=rho/16 exceeds the global value0. This exact obstruction
shows why a global consumer must use more than COMP; it makes no claim
about a positive-gap counterexample.


## 22. A global compact dichotomy without an actual-attainment branch

The [compact END-separated-contact exclusion](../exports/COMPACT_END_SEPARATED_CONTACT_EXCLUSION.md)
contains the complete comparison compiler and consumer. Its finite-data
inputs are native A>0, invertible Gamma with a strict positive inverse
column, and generic nonzero off-diagonal Gamma entries. It chooses ONE
cheap positive theta before t and the source. The all-END global minimum
is the incoming premise; the old source proof allows the smaller positive
epsilon used for these prices, with t0=epsilon A/32.

Every such minimum, including nonrealized ones, has a canonical marked
representation retaining full U,B,e and EACH ORIGINAL N. At any fixed
bounded latent densities, pushing through its OLD actual calendars
produces comparison tuples in the SAME carrier and preserves every old
query. This supplies positive-mass block hazards, timing transfers and
one-sided missing-owner insertions without inserting an atom at an
atomless cut or recompressing the response menu.

If interior native cap contacts are bounded away from finite END c, two
cofinal owners admit an exact fixed-marginal/fixed-tie first derivative
forcing forbidden reciprocal prices. Three or four cofinal owners give
a normal multiplier set of dimension at most1. Finite quadratic-path LP
duality and the two-form theorem produce a PSD normal; five chronological
negative directions defeat its critical space of codimension at most4.
One cofinal owner already produces interior contact accumulation. With
zero cofinal owners, the last retained positive mixture interval ends at c
and c is isolated. Existing four-player quadratic margins exclude the
all-Never degeneracy. Thus EVERY chosen representation has exactly one
of two surviving modes:

* Distinct interior cap-query locations accumulate at finite END c.
* Finite END c is isolated after a last positive mixture atom.

Neither mode is consumed. The second can have nonrealized or nonatomic
earlier history; the first can include unused physical replies. This
replaces actual attainment as a frontier partition, while retaining the
original table, objective and Never coordinates. It does not close Fin4.


## 23. Ambient singleton faces classify cofinal tail calendars

This is one general tail theorem with an explicit positive-inverse
corollary. It excludes complete diffuse/thin-atom source modes and realizes
a RESTARTED late suffix; it supplies no minimum for that suffix.

The accepted [general late-tail debt bound](../exports/GENERAL_LATE_TAIL_DEBT_AND_END_CAP_MINIMUM_REDUCTION.md),
Theorem A, already gives at every offered query with R_h>0 and all END caps
active

    sum_(j!=h) R_j/R_h >= nu A/(18M)>0.

It therefore already excludes exactly ONE cofinal owner at A>0, without
any inverse hypothesis. For two cofinal owners their tails are comparable
in both directions. This older consequence is reused, not a new exclusion.

The accepted [native collision floor](../exports/NATIVE_COLLISION_FLOOR_AND_GLOBAL_MASS_DICHOTOMY.md)
is a second, stronger input on native zero-debt tails. For ANY actual law
with total finite mass 0<beta<=1/2, write C for the sum over dates and
unordered owner pairs of their finite atom products. It gives

    A<=400M [D/(M beta^2)+4sqrt(C)/beta]^(1/9).

Its actual-realizer transport applies at EVERY old conditional cut of a
retained E source with positive original Never. Thus every such nontrivial
small suffix satisfies

    C_cut>=c_A beta_cut^2,
    c_A=(1/16)[A/(400M)]^18>0.

The elementary bound C<=3 beta times the largest second-owner atom at a
date then produces, in EVERY such suffix, one date carrying TWO DISTINCT
conditional owner masses each at least c_A beta_cut/3. In particular these
joint bursts occur cofinally whenever finite tail mass tends to zero.
The pair and date may change from suffix to suffix. This excludes purely
nonatomic, singleton-only and vanishing-relative-collision terminal tails
without any matrix or genericity hypothesis. It does not put a joint burst
at every query, or consume dense shared bursts. At original raised minima
the same packet gives either total finite mass O(t), or a pair-macroscopic
burst. All these facts are already accepted results; they are recorded here
to prevent rediscovering their weaker consequences as new coverage.

### Exact source restriction

There are four independent stopping laws q_i on a canonical marked finite
query set T contained in [0,c], together with a separate Never label. T
is compact, c=max T, and q_i({c})=0. Every law has a bounded density
relative to the canonical physical mixture mu=(sum_i q_i)/4=pi_*dx.
Each positive finite mixture atom is a retained isolated point of T;
all other points of T have zero mixture atom. Every pure query in T and
Never is legal and its literal earliest-coalition payoff is retained.

Native own singleton, live and all-Never rewards are zero. Let M>=1 bound
the absolute value of every native reward. Let B_i be the COMPLETE cap
over all T queries and Never, and e_i the Never response. Assume B_i=e_i
for every owner. ORIGINAL Never masses N_i=q_i(Never) satisfy N_i>=n0>0.
An owner is cofinal when q_i((u,c))>0 for every u<c. Let S be the
nonempty proper set of cofinal owners. Let Gamma_ii=0 and Gamma_ij=Z_i({j}).
For this support S,
define the ambient finite linear feasibility set

    K_S={y>=0:y_j=0 outside S, sum_j y_j=1, Gamma y>=0}.

For the general theorem assume K_S is EMPTY. No matrix invertibility is
needed. Define delta_S as the minimum of max_i(-(Gamma y)_i)^+ on this
simplex face. Compactness and continuity give delta_S>0: its zero set is
exactly K_S. By homogeneity every nonnegative y supported WITHIN S obeys

    max_i(-(Gamma y)_i)^+>=delta_S sum_j y_j.          (SEP-S)

Thus delta_S is produced from the finite table and support, not supplied
as a strategic witness. Any positive lower bound delta<=delta_S suffices
below. A relative tail limit need not have support equal to S; the closed
support condition is essential. ALL FOUR ambient recipient rows are used,
including physically inactive owners. This differs from a principal
Gamma_[S,S] or R0 complementarity test.

For the stated empty-face hypothesis there are a<c and kappa>0 such that
EVERY legitimate finite query x in T intersect (a,c) satisfies

    mu({x}) >= kappa mu([x,c)) > 0.                    (ATOM)

In particular the entire late finite query set is a strictly increasing
sequence x_1<x_2<... tending to c, with no empty test points or nonatomic
mass there, and

    mu([x_(n+1),c)) <= (1-kappa) mu([x_n,c)).           (GEOM)

For an entrywise-positive-inverse table, a nontrivial atomless cofinal
suffix, or arbitrarily late legal queries whose physical atom is a
vanishing fraction of inclusive finite tail mass, forces ALL FOUR owners
to be cofinal. This excludes an entire proper-
cofinal diffuse/thin-atom source class, not the geometrically atomic
proper-cofinal case. It requires no global dual, contact multiplier,
regular level set or actual natural-date realization.

If Gamma^-1 is entrywise strictly positive, every nonempty proper K_S
is empty and a common explicit separation constant is produced below.
This includes the studied literal opposed-pair matrix. A positive inverse
COLUMN alone does not imply that every proper K_S is empty. Global full-SUM
sources supply the canonical clock and their fixed original-N floor.

### Thin atoms force an ambient semipositive support

If a proper cofinal source admits legal queries x_n->c with
mu({x_n})/mu([x_n,c))->0, the ambient feasible set K_S MUST be nonempty. In the GAP
notation below, z/m is at most that physical ratio divided by n0. Hence
z/m->0. Divide GAP by m, take a subsequential limit of y/m in the compact
simplex face, and use m->0. The limit has Gamma(y/m)>=0, nonnegative
coordinates supported WITHIN S and unit sum, so belongs to K_S. Thus the
finite ambient face test classifies an actual remaining source geometry;
feasibility by itself does not produce an all-END source or thin atoms.

### An explicit common constant for entrywise positive inverse

For this corollary assume P=Gamma^-1 is entrywise strictly positive. Put

    Smax=max_j sum_i P_ij,
    R=max_k [(sum_i P_ki)/(min_i P_ki)],
    delta=1/(Smax R)>0.

For every y>=0 having at least one zero coordinate,

    max_i (-(Gamma y)_i)^+ >= delta sum_j y_j.         (SEP)

Here a^+=max(a,0). To prove this, choose k with y_k=0, let
w=Gamma y, and set eta=max_i(-w_i)^+. Then w+eta one>=0. The k-th
row p of P is strictly positive and

    sum_i p_i(w_i+eta)=eta sum_i p_i,

because p w=y_k=0. Hence

    sum_i w_i^+ <= sum_i(w_i+eta)
                     <= eta (sum_i p_i)/(min_i p_i) <=eta R.

Since y=P w and its coordinates are nonnegative,

    sum_j y_j = sum_i (sum_j P_ji)w_i
                   <= Smax sum_i w_i^+ <=Smax R eta.

This proves (SEP), including eta=0. It is an exact raw matrix inequality,
not an assumed cone-separation witness at the source.

For

    Gamma=[0,-2,-5,4; -6,0,-4,6; 1,3,0,-5; 1,-1,4,0],

direct multiplication gives

    42P=[52,17,62,82; 76,41,110,136;
          6,6,12,24; 56,28,70,98].

Its maximal column sum is Smax=170/21. The four row ratios are
213/17,363/41,8,9, so R=213/17. Thus

    delta=7/710.                                    (RAW)

No restriction on the other thirty-one raw-family rewards is needed for
this calculation; they enter only through their finite common bound M.

### The exact all-END query inequality with its retained tie term

Fix a LEGITIMATE query x in T below c. For every owner j define physical
inclusive finite tail and current atom

    f_j=q_j([x,c)), a_j=q_j({x}), n_j=N_j+f_j,
    y_j=f_j/n_j, z_j=a_j/n_j,
    m=sum_j y_j, z=sum_j z_j.

Thus n_j is the original probability of surviving to x, including the
current atom and original Never; n_j>=N_j>=n0 and n_j<=1. The vectors
y,z are conditional probabilities after that survival, with 0<=z<=y.
Let J_ij=Z_i({i,j}) off the zero diagonal.

Compare responder i's native Never query with its pure finite query at x.
If some opponent stops before x, the two replies see the identical first
coalition and payoff. Conditional on every opponent surviving to x, the
opponents remain independent, with the probabilities y_j,z_j above.
If exactly ONE opponent j has a finite draw, the payoff difference is
Gamma_ij for its later-than-x draw and Gamma_ij-J_ij for its draw at x.
Therefore the contribution of all such events is exactly

    sum_(j!=i) (Gamma_ij y_j-J_ij z_j)
                         product_(k outside {i,j})(1-y_k).

All events with at least two finite opponents have total probability at
most m^2/2, and each reply-payoff difference has magnitude at most 2M.
Replacing the products in the preceding display by one changes that
display by at most 2M m^2, since |Gamma_ij y_j-J_ij z_j|<=2M y_j.
Consequently the complete conditional gap has the exact form

    [e_i-response_i(x)]/product_(j!=i)n_j
        =(Gamma y)_i-(J z)_i+E_i, |E_i|<=3M m^2.      (GAP)

The all-END FULL cap gives e_i-response_i(x)>=0 for EVERY i. Hence

    (Gamma y)_i >= -M z-3M m^2 for every i.           (LOWER)

The FIRST-ORDER J z term is essential. We have not inserted an arbitrary
atomless cut into T or treated a tied finite query as an untied query.
No assumption about which replies are cap contacts was used: the complete
cap inequality applies to each actual legal query.

### From a missing cofinal owner to a uniform atom floor

For each k outside S choose u_k<c above all its physical finite mass,
and take u=max_(k outside S) u_k<c. Thus f_k=y_k=0 for EVERY k outside S
at every query x>u, so y is supported within S. By (SEP-S), or the explicit
corollary (SEP), and (LOWER),

    delta m <= M z+3M m^2.                            (1)

All finite q_i tails tend to zero as x tends to c because q_i({c})=0.
Since n_j>=n0, m tends to zero uniformly over queries approaching c.
Enlarge u so every x in T intersect (u,c) satisfies m<=delta/(6M).
Equation (1) then gives

    z >= delta m/(2M).                               (2)

Translate back to ORIGINAL physical masses:

    sum_j a_j >= n0 sum_j z_j = n0 z,
    m=sum_j f_j/n_j >= sum_j f_j.

Thus

    sum_j a_j >= [n0 delta/(2M)] sum_j f_j.            (3)

Take kappa=min(1/2,n0 delta/(2M)). Dividing both sides by four proves
(ATOM). Its strict positivity follows from S nonempty: a cofinal owner
has positive finite mass after every x<c. For the literal raw matrix one
may use the concrete common constant

    kappa=7 n0/(1420M),

which is below 1/2. At a global full-SUM source n0 may be the fixed repair
floor c0=(A/(28M))^4; it is ORIGINAL Never, not escaped finite probability.

### Canonical sequence geometry and geometric decay

Every late T point is a positive mixture atom by (ATOM), and hence is
isolated in T by the canonical representation. There is no accumulation
point of these queries inside (u,c): compactness would put the
limit in T, while (ATOM) would make it a positive atom and therefore
isolated. Since a cofinal owner exists, there are nevertheless T points
arbitrarily close to c from below.

Choose one late query x_1. Successive minimum T points above it exist by
compactness and isolation, are below c by cofinality, and enumerate the
whole tail. They form x_n increasing to c. No other finite physical mass
can lie between them because all physical laws are supported on T. Hence

    mu([x_(n+1),c))=mu([x_n,c))-mu({x_n})
                           <=(1-kappa)mu([x_n,c)),

proving (GEOM). This also rules out diffuse physical mass in the late
tail, not just extra empty query points.

### The conditional late suffix has an actual natural-date realization

Condition each owner's clock on belonging to [x_1,c) together with Never.
Its normalizing probability is the ORIGINAL n_i(x_1)=N_i+f_i(x_1)>0.
Independence is retained under this product conditioning. Relabel x_n as
the natural date n-1 and retain literal Never. These are actual complete
natural-date laws. Their first-coalition kernels preserve every strict
order and retained tie exactly, and their marginal Never masses are
exactly N_i/n_i(x_1). No escaped finite probability is relabeled Never.

Every actual pure finite deadline is one of the enumerated x_n queries.
The only extra old suffix query is c. Its kernel equals native Never
because there is no physical atom at c and own singleton is zero. Thus
all conditional prescribed payoffs, full caps, Never offers and individual
Never masses agree with those of this actual suffix. No bound on the
number of its dates or controller size is claimed.

The conditional full caps here are taken over the restarted suffix menu
T intersect [x_1,c] together with Never; earlier old queries are not part
of that restarted game. Conditioning while retaining earlier old queries
could add a zero response and is not asserted to preserve these caps.

This realizes the conditional late suffix, NOT the possibly nonrealized
earlier compact head or the whole source. It gives the suffix no minimum
property. Conditioning at x_1 is an exact probability decomposition,
not a proposed game action after an infinite prefix.

### Source adapter, limitation and next question

For the original full-SUM all-END source, use its exact canonical marked
representation, the full payoff-kernel query menu and the produced lower
bound for every original N_i. If its ambient face K_S is empty, the raw table and support produce
delta_S and kappa as above; the positive-inverse hypothesis supplies a
common constant for every proper support. Every such source must have
an eventually geometric atomic calendar with an actual conditional natural-date suffix, regardless of
unused cap contacts or actual attainment of the whole source.

Combined with the compact contact dichotomy, the accumulating-contact
branch for the studied raw matrix therefore separates into all-four
cofinal sources and a rigid proper-cofinal geometric-atom branch. The
isolated-END zero-cofinal case remains separate. This does not consume
the all-four branch or the geometric atomic branch, and it is not an
equilibrium-existence result.

The next concrete question is whether the exact all-END inequalities on
this geometric atomic tail, now with a uniform ratio of current atom to
remaining finite mass, force a three-player absorbing exit or an original
full-F/N improvement. Such a consumer must retain the J atom term; its
sign cannot be discarded as a diffuse-tail error.

### Exhaustive two-cofinal support map for the fixed13 family

Suppose exactly two owners i,j are cofinal. Above the bounded finite
activity of the other two, the END-minus-current-query gap for responder i
is EXACTLY

    product_(k outside{i,j}) N_k * [Gamma_ij R_j-J_ij a_j],
    R_j=q_j([x,c)), a_j=q_j({x}).

All earlier first coalitions cancel, every inactive opponent must be
original Never, and only one finite opponent remains. Thus all-END gives
Gamma_ij R_j>=J_ij a_j at EVERY offered late query. Cofinality makes
0<=a_j/R_j<1. In particular Gamma_ij<0 requires J_ij<Gamma_ij and
a_j/R_j>=Gamma_ij/J_ij. If Gamma_ij>0 and J_ij<=Gamma_ij, the gap is
strictly positive, so i has NO sufficiently late finite cap contact.

For the literal fixed13 family all six possible pair supports are covered:

| Cofinal pair | Necessary guard or exclusion | Additional exact late restriction |
| --- | --- | --- |
| 01 | Impossible: Gamma01=-2,J01=-1 | The owner0 gap is negative |
| 02 | Z0(02)<-5 | a2/R2>=5/(-Z0(02)); owner2 has no late cap contact |
| 03 | Not excluded here | a0/R0<=1/2; owner0 has no late cap contact |
| 12 | Z1(12)<-4 | a2/R2>=4/(-Z1(12)); owner2 has no late cap contact |
| 13 | Not excluded here | a1/R1>=1/2; owner1 has no late cap contact |
| 23 | Impossible at A>0 | The owner2 gap is negative |

For the last exclusion, if Z2(23)<=-5 then pure3 is absorbing Nash:
own3 and withdrawal both pay0; outsiders0,1 prefer passive4,6 to joining3,-1;
and outsider2 prefers passive-5 to joining Z2(23). Hence A>0 forces
Z2(23)>-5, contradicting the necessary strict negative-Γ guard for23.
The no-contact statements in the other rows use participant1/2 rewards
nonpositive, Gamma20=1,Gamma21=3, and fixed Gamma03=4,J03=3,
Gamma13=6,J13=-1. No tail minimum, restricted-m eligibility, or sign of
a missing owner's continuation is assumed.

There is a further literal-family consequence when the source is in E,
so U=B. Retained Fubini gives

    d_i=integral [B_i-response_i(x)] dq_i(x).

For each remaining pair02,03,12,13, the table supplies a COFINAL physical
owner whose gap is strictly positive at EVERY sufficiently late query.
That owner has positive late physical mass; integrating the nonnegative
strict gap gives d_i>0, even without a uniform gap. Pairs01 and23 were
already excluded. Thus NO literal fixed13 E source at A>0 has exactly two
cofinal owners, with no row-distinctness or pair-ratio genericity imposed.
The accepted [uniform three-owner dispersion](../exports/UNIFORM_THREE_OWNER_TAIL_DISPERSION.md)
already excludes collared pair Nash sources under its generic hypotheses;
the direct table argument here retains the literal fixed entries. This E
corollary is not applied to full-SUM minima having positive native debt.

### Owner2 cofinality requires owner3 in a literal E source

There is a stronger exclusion for one proper triple. In the literal
fixed13 family, assume q_i({c})=0, each ORIGINAL N_i>0 and U=B=e.
If owner3 is noncofinal, choose one real cutoff u<c above ALL its finite
mass. For any old legal query x>u, let response2(x) be the original
whole-source forced-Quit value. Earlier opponent coalitions cancel between
this response and native Never. On survival to x, every possible subsequent
opponent coalition belongs to {0,1,01}, paying owner2 respectively1,3,4.
These are nonnegative, whereas every current participant2 reward is
nonpositive. Retaining just the events in which one opponent quits strictly
after x and the other two are original Never gives the unconditional bound

    e2-response2(x)
      >=N3 [N1 q0((x,c))+3N0 q1((x,c))].       (DOM2)

If owner0 or owner1 is cofinal, this is strictly positive at EVERY such
query. Cofinal owner2 would put positive own physical mass on these
strict-gap queries. Retained Fubini would then give

    d2=integral [B2-response2(x)] dq2(x)>0,

contradicting E. Consequently the cofinal sets02,12,012 are impossible
even without A>0. If A>0 and owner2 were the sole cofinal owner, the older
late-tail debt theorem above would exclude it. Thus at A>0,

    owner2 cofinal => owner3 cofinal.

Together with the complete pair map, the proper three-cofinal possibilities
are exactly the still-unexcluded supports013,023,123;012 is removed.
This argument uses no row perturbation, source minimality, suffix minimum,
or actual realization of the earlier compact history. The canonical empty
END q_i({c})=0 is essential when choosing the cutoff above owner3's mass.

This support table concerns COFINAL END activity, not the first finite
root support or the native-m caseI/II histories. The positive inverse makes
all surviving proper supports geometrically atomic with actual restarted
suffixes. Their entire source is still allowed to have earlier compact
history. Two-/three-cofinal geometric calendars at positive native debt,
the surviving E triples013,023,123, and all-four-cofinal contact accumulation
remain open; the isolated-END case remains separate.


## 24. One pair-ratio theorem unifies the dispersion mechanisms

This is an internal synthesis, not another export or another solved raw
reward class. It combines the [oriented-pair bound](../exports/ORIENTED_PAIR_UNIFORM_THREE_OWNER_DISPERSION.md)
with the normalized-pair lemma in Sections5.1--5.3 of the accepted
[three-owner dispersion proof](../exports/UNIFORM_THREE_OWNER_TAIL_DISPERSION.md),
and closes the previously unnecessary ratio-one boundary between them.
All payoffs, full caps, independent complete laws and ORIGINAL N have the
native meanings above. Fix one bounded table with A>0 and Gamma_ij!=0
for every i!=j. For each unordered pair set

    r_i=J_ij/Gamma_ij, r_j=J_ji/Gamma_ji.

Assume no unordered pair has EQUAL ratios r_i=r_j>=1. Equivalently, each
pair satisfies min(r_i,r_j)<1 OR r_i!=r_j. Then there is c(Z)>0 such that
EVERY actual profile and its augmented closure obey

    D+beta epsilon>=c beta^2,
    beta=sum_i(1-N_i), epsilon=f_(3)+f_(4).        (UNIFY)

No recipient-row distinctness or blanket J_ij!=Gamma_ij assumption is
needed. The strict-orientation packet gives an explicit constant on its
own subdomain. This unified statement gives a qualitative constant and
the same zero-debt, old-suffix and raised full-SUM consequences. For
retained old suffixes, use the actual conditional realizers of Section8
of the native collision-floor packet, already summarized in Section23;
the carrier bound alone does not execute an abstract suffix. Equal
viable ratios r_i=r_j>=1 remain outside THIS argument.

### Common original-debt reduction for every mass regime

If (UNIFY) failed, a sequence at this SAME table would satisfy

    beta>0, D/beta^2->0, epsilon/beta->0.

Fix labels i,j for the largest two finite masses along a subsequence.
The one-owner comparison A f_(1)<=D+14M(f_(2)+epsilon) implies
f_i,f_j>=kappa beta for some fixed kappa>0. Since beta<=4, D->0.
Absorbing repair A<=D+14M(product N)^(1/4) gives EVERY N_k>=eta>0.
These statements hold whether beta tends to zero or stays macroscopic.

Let F_i,F_j be the normalized SURE FINITE parts on their original natural
dates. With all other owners Never, let b_i be the full cap against F_j
and p_i the response averaged under F_i. The original Fubini/censorship
estimates of the oriented-pair packet give

    0<=b_i-Gamma_ij<=D/(N_i f_j)+4M epsilon/f_j,
    0<=b_i-p_i<=D/(f_i f_j)+4M epsilon/f_j.

Both errors tend to zero; the same holds for j. Thus b_i,p_i->Gamma_ij
and b_j,p_j->Gamma_ji. For independent X~F_i,Y~F_j put
a=Pr(X<Y), b=Pr(Y<X), z=Pr(X=Y), a+b+z=1. Exactly,

    Gamma_ij-p_i=Gamma_ij[a+(1-r_i)z],
    Gamma_ji-p_j=Gamma_ji[b+(1-r_j)z].           (TRI)

If min(r_i,r_j)<1, the strict timing-triangle separation excludes these
two vanishing errors. This is the entire first branch of the proof.

For the other branches reuse Theorem B of the accepted
[unrestricted every-cut bound](../exports/GENERAL_LATE_TAIL_DEBT_AND_END_CAP_MINIMUM_REDUCTION.md):
at EVERY original natural query x and every owner h,

    D>=C_h A R_h(x)-18M sum_(k!=h)R_k(x),
    C_h=product_(k!=h)N_k>=eta^3.               (CUT)

It needs no END activity, Nash profile, or suffix minimum. R is the
inclusive ORIGINAL finite tail, not a normalized or escaped mass.

### Ratio one versus a strictly larger ratio

Suppose r_i=1<r_j. From (TRI), a->0 and z->z0=1/r_j in(0,1).
For any two sure finite laws, z<=2 sup_x min(F_i{x},F_j{x}); assign each
atom product to its larger factor and sum those factors, at most2.
Choose a common original atom x_n with both masses at least z0/8.
Independence then gives

    F_i(<x_n)<=a/F_j{x_n}->0,
    F_j(>x_n)<=a/F_i{x_n}->0.

The nonnegative pure-response deficit at this macroscopic j atom is at
most (b_j-p_j)/F_j{x_n}, hence tends to zero. Its exact response value is
Gamma_ji F_i(<x_n)+J_ji F_i{x_n}. Since b_j->Gamma_ji and J_ji!=0,

    F_i{x_n}->z0, F_i(>x_n)->1-z0>0.

The original legal query y_n=x_n+1 therefore has R_i(y_n)>=c1 beta,
R_j(y_n)=o(beta), and total other tails at most epsilon=o(beta).
Applying (CUT) and dividing by beta contradicts D/beta->0, because
eta^3 A c1>0. No empty response before an old atom has been invented:
x_n+1 belongs to the original complete natural-date query menu. The case
r_j=1<r_i is symmetric. This consumes the entire ratio-one boundary.

### Distinct ratios strictly above one

If both r_i,r_j>1 and are unequal, the accepted normalized-pair lemma
applies to the same F_i,F_j sequence and its full-cap contacts above.
Its compact-clock proof retains the ORIGINAL query witnesses. It gives
common successive atoms tau_m and geometric inclusive tails rho_i^m,
rho_j^m, where rho_i=1-1/r_j and rho_j=1-1/r_i are distinct in(0,1).
The lemma's row-distinctness uses are exactly Gamma!=0 and the strict
ratios in this branch; no other reward-row entry occurs in that proof.

Let s be the slower owner and w the faster, rho_s>rho_w. At every FIXED
m take the actual old query witnesses x_(n,m) for tau_m. Their normalized
inclusive tails converge to rho_s^m and rho_w^m. Along a further subsequence
f_w/f_s->lambda in(0,infinity). Divide (CUT) at x_(n,m) by f_s and first
let n tend to infinity. The original debt and minor-tail terms vanish,
giving

    eta^3 A rho_s^m<=18M lambda rho_w^m.

Now divide by rho_s^m and let m tend to infinity: contradiction. The
limits are taken in that order; there is no moving-depth uniformity
assumption. This replaces the older outsider first-order argument by
the unrestricted original-debt bound. The three branches exhaust every
pair admitted by (UNIFY), proving the stated uniform constant exists.


## 25. A global core barrier forces substantial owner2 activity

The [positive-head barrier](../exports/OPPOSED_PAIR_POSITIVE_HEAD_FORCES_OUTSIDE_ACTIVITY.md)
uses only the fixed core0,1,3 reward restriction; rewards involving owner2
are arbitrary finite values. Put k=Z0(13). At k>=2, any faithful retained
zero-debt core-only clock with positive ORIGINAL Never satisfies

    w1<=0, w3>0 => Psi(w)<=0,
    Psi(w)=w1/6+w3-min(w0,0)+(w1/6)max(w0,0).     (CORE)

The proof treats EVERY atomic support switch and boundary solo row, then
the continuous part and accumulations by the exact conditional-value BV
equations. A positive Psi cannot decrease and cannot reach its terminal
value0. The zero0/positive1 trap is consumed by the zero-tail endpoint,
without a cofinal-owner assumption. No source attainment or tail minimum
is needed. The full proof is in the packet, rather than duplicated here.

### Direct original-head consumer, without a first013 assumption

For ANY genuine proper03 E head X=prefix03(Y) with positive U1(X), let
its hazards be (r,0,0,s). The genuine full-cap equations give

    Y0=-s/(1-s)=-A<0, Y3=r/(1-r)=D>0,
    U1(X)=[Y1+6(A-D)]/[(1+A)(1+D)].              (HEAD)

If N2(Y)=1 and Y1>0, at the FIRST retained legal query positive1 forces
its own hazard b=0. Then the immediate owner0 offer is3c>=0, contrary to
its negative cap Y0. If Y1<=0, instead

    Psi(Y)=Y1/6+A+D
          =[(1+A)(1+D)/6]U1(X)+2D>0,

contradicting (CORE). Thus the ENTIRE N2(Y)=N2(X)=1 branch is excluded
at k>=2, for every tail1 sign and every subsequent history. No preceding01
or first013 row, history-length bound or outside2 payoff sign is needed.
This generalizes the intermediate immediate013 adapter and is counted
as ONE source-class exclusion. It forces finite activity, not cofinal2;
a finite owner2 excursion followed by cofinal013 remains possible.

### Fixed-table activity floor at the selected original minima

For the fixed13 family with A_Z>0, fix the table and the produced theta
of Section19. That section supplies epsilon,kappa>0 and the original
alpha>0 so that all selected source heads at small t have r,s in
[epsilon,1-alpha/2], output B1>=kappa, and cluster at E sources of Never
product alpha. Their genuine tails also have debt tending to zero.

Consider the closed family of tuples (X,Y,r,s) satisfying

    X,Y in E, nu(X)=alpha, X=prefix03(r,s,Y),
    r,s in[epsilon,1-alpha/2], U1(X)>=kappa.

It is compact and contains every cluster of those selected factorizations;
such clusters exist, so the family is nonempty.
Positive nu(X) and properness give all original Never coordinates of X,Y
positive. By the head theorem, EVERY member has N2(Y)=N2(X)<1 at k>=2.
The continuous coordinate N2 therefore attains a maximum strictly below1.
There is delta>0, depending on this FIXED table, theta and collar, with
N2<=1-delta on the entire family. Compactness then gives, for all
sufficiently small t and EVERY selected factorization,

    1-N2(X_t)=1-N2(Y_t)>=delta/2>0.              (MASS2)

This is a TOTAL original finite-mass floor despite the first hazard q2=0.
It applies to the original positive-debt full-SUM minima through their
native E limits, rather than applying (CORE) directly at positive debt.
No numerical delta or uniformity over varying finite reward tables is
claimed. Finite owner2 excursions and the k<2 core-only branch remain open.
