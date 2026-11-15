# Linear Nash paths and shared-anchor counting: exact boundaries

Maintainer: `CODEX_ROOT`. Ordinary mathematics, not a new Lean verification.

## Status and role

Two rigorous method boundaries guide the parallel attack in the
[coverage map](CODEX_ROOT__FIN4_COVERAGE_MAP.md). Neither closes a reward
class or a Fin4 capstone. The first controls arbitrary finite and infinite
homogeneous paths, beyond a bounded search for expanding words. The second
shows why two pair–triple certificates cannot spend their shared pair index
twice, even with the old full-support orientation premise.

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

## 3. Full Orientation and two F3 certificates do not bound the bundle index

Here is an exact complete native table. Put epsilon=beta=1/100 and T=20;
all own singleton, live and Never rewards vanish.

| S | Z0 | Z1 | Z2 | Z3 |
| --- | ---: | ---: | ---: | ---: |
| 0 | 0 | 0 | 2 | 0 |
| 1 | 99/100 | 0 | -1/50 | -1/100 |
| 2 | 2 | 0 | 0 | 0 |
| 3 | 99/100 | -1/100 | -1/50 | 0 |
| 01 | -1/100 | -1 | 1 | 1 |
| 02 | 1 | 2001/100 | 1 | 2001/100 |
| 03 | -1/100 | 1 | 1 | -1 |
| 12 | 1 | -1 | -1/100 | 1 |
| 13 | 0 | -1 | 0 | -1 |
| 23 | 1 | 1 | -1/100 | -1 |
| 012 | 0 | 20 | 0 | -99/100 |
| 013 | 0 | 0 | -1 | 0 |
| 023 | 0 | -99/100 | 0 | 20 |
| 123 | -1 | 0 | 0 | 0 |
| 0123 | -1 | -1 | -1 | -1 |

At odds(x,y,z,t), put D=1+y+t and A=-x-z-beta xz. The joining maps are

    Phi0=-y-t-Dz, Phi2=epsilon(y+t)-Dx,
    Phi1=(1+t)A+(epsilon-1)t,
    Phi3=(1+y)A+(epsilon-1)y.                        (7)

For012 use roles(i,j,k)=(0,1,2). Its(F1) data are
J01=J21=-1/100, J10=J12=-1, J02=J20=1, T1=20.
Its(F2) data are(alpha,beta_join,gamma,eta)=(-1,-1,-1,epsilon),
B0=B2=-1 and K=1/20>=epsilon. On its fixed-anchor fiber,

    x'=(epsilon-x)/(1+y), z'=-(1+z)/(1+y).

With lambda=0 its(F3) polynomial is exactly

    H=beta(1+y)^2[(x-epsilon)z+x].

Substituting x=K+u gives nonnegative coefficients. Exchanging1 and3 proves
the023 certificate. Both triples fail Low and Charge: their large anchors
make all active R positive, and a required strictly negative singleton
Charge coefficient equals J02+J12=0, respectively J02+J32=0. They fail
Orientation since A'>0 on the positive-Quit fiber. The other two triples
pass Low, having an active row with only nonpositive participant rewards.

Full strict Orientation nevertheless holds. Direct differentiation gives

    det D Phi=-D L V,
    L=beta xz+1-epsilon+x+z,
    V=L+beta(y+t)[x(z+1)-epsilon z]
                         +2beta[x(z+1)-epsilon z].

Full R1=-x-z-t+20xz-xzt>0 implies x,z>1/20>epsilon. Thus D,L,V>0
throughout the full positive-Quit region, giving det D Phi<0.

Now take v=(-1/2,-3/5,-1/2,-3/5), in the reward hull as
v=(1/2)Z(0123)+(1/10)Z(13)+(2/5)0. The02 root has x=z=1/2,y=t=0,
active outputs1/3, positive quiet outputs, and strict quiet inequalities
because A=-401/400<-3/5. Its index is-1.

On012 the anchors are x=(1/2+epsilon y)/(1+y), z=(1/2-y)/(1+y).
The remaining equation A=-3/5 becomes

    31802 y^2+23899 y-8050=0.

It has exactly one positive root y in(1/4,13/50), with
39/100<x<41/100 and19/100<z<21/100. Hence R0=z-y/100>0,
R2=x-y/100>0 and R1=20xz-x-z>0. Its quiet inequality is strict since
Phi3=v3+y(v1+epsilon-1)<v3. Its quiet payoff numerator is
R1+y(3/5-epsilon-xz)>0. Thus this is a bad triple root, of index+1
because A'>0. The023 root is symmetric, also bad and of index+1.

There is no full proper root at v. Its free equations force y=t=u,
since Phi1-Phi3=(t-y)(A+epsilon-1) and A+epsilon-1<0.
The anchors require0<u<1/4. But beta>=0 gives

    Phi1<=(-1-epsilon u)/(1+2u)<-3/5,

contradicting its active equation. The shared bundle therefore has total
index-1+1+1=+1, despite both full F3 certificates and full Orientation.

This does not make all Nash roots bad. The adjacent01 root
x=3/5,y=1/2,z=t=0 has both quiet inequalities strict and owner0's forced
Quit payoff negative. Pure sure0 and sure2 are good too. They are actual
absorbing Nash profiles under nonnegative recipient-row raises, so A_Z=0.
The example violates(6); it is not a positive-gap source or a counterexample.

Thus a universal shared-anchor argument must control good sure/adjacent
roots or other anchor-dropout faces under its full source hypotheses.
The unconditional nonpositive joint-index shortcut is false. The existing
[rectangle theorem](../exports/SHARED_ANCHOR_RECTANGLE_UNIFORM_EQUILIBRIUM.md)
retains additional capture and outer-edge conditions, which this calculation
does not remove.
