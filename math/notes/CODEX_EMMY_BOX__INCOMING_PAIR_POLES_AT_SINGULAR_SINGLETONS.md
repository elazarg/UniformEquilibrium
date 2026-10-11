# Incoming pair poles at singular singleton data

Status: INTERNAL ONLY, not Lean checked and not exported. The actual producer
has one independent ordinary check. The proposed separating fixture is
ALREADY COVERED: its correct active-triple index is-1 and full R0 degree-1,
not1. The implemented nonunit-degree source covers all its collision rows.
No new reward-class admission is claimed for this calibration.
This is not a further inverse-column construction: its singleton matrix may
be singular. The source consists of finite reward coefficients and an explicit
finite Jacobian test, not a supplied equilibrium or an assumed exact root of
the original game. The bounded source comparisons in Section6 do not claim
an exhaustive census of every existing local existence neighborhood.

## 1. Self-contained question and raw source

Let I be finite, |I|=n>=2. Every nonempty first-quitting coalition S absorbs
at r(S) in real I-space. Live dates and perpetual continuation pay0.
Randomization is private and independent. All equilibrium comparisons below
allow EVERY complete unilateral behavioral replacement, including finite
deadlines and Never. Payoffs are expectations.

Fix arbitrary singleton rewards, and put

    s_i=r_i({i}),     Gamma_ii=0,
    Gamma_ij=r_i({j})-s_i for j!=i.

Fix a permutation pi of I without fixed points and a vector v>0. Neither
Gamma invertibility nor any inverse sign is assumed. Define finite data

    P_i(z)=(sum_(j!=i)z_j)*z_(pi(i)),
    kappa_i=(Gamma*v)_i/P_i(v),
    J=diag(kappa)*DP(v)-Gamma.                         (1)

Assume the explicit inequalities and determinant test

    Gamma*v>0,              det J!=0.                  (2)

The vector v is fixed algebraic class data; it is not a strategy of the
original game. In particular(1)-(2) use only singleton coefficients.

**Theorem.** For every finite R>=0, all sufficiently large M have the
following property. EVERY raw table with the fixed singleton entries and

    r_i({i,pi(i)})=kappa_i*M+c_i,       |c_i|<=R,
    |r_i(S)|<=R for every OTHER nonsingleton recipient coordinate

has an actual independent stationary exact terminal Nash profile with

    q_i=v_i/M+O(M^-2),             0<q_i<1.             (3)

The remainder is uniform over the displayed residual box. The SAME profile
is a uniform-equilibrium profile at its actual terminal payoff: for every
accuracy it works over all sufficiently long finite-average horizons.
The theorem allows arbitrary signs of bounded rewards and own singletons.

Reciprocal pi choices may select two DIFFERENT recipient coordinates of one
pair; these coordinates never conflict. The singular four-player example
below uses pi(i)=i-1 modulo4, so all four selected pair rows are different.

There is also an open raw-coefficient version: sufficiently small independent
changes of the singleton coefficients and of all leading kappa coefficients
preserve the conclusion, with a positive leading root near v. One must then
replace the exact leading vector in(3) by that selected nearby root. Thus
the displayed ray is not the entire class.

## 2. Exact polynomial and actual root production

For opponent hazards q_-i let

    alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A union{i})],
    B_i=E[r_i(A)*1_(A nonempty)],
    H_i=(1-alpha_i)*Q_i-B_i.                            (4)

Here A is the independently drawn opponent quitting coalition at one date;
the empty-coalition term in B is0. Every expression is a finite polynomial
in the opponent hazards, even for arbitrary real hazards when formally
extended. H does not depend on the owner's own hazard coordinate.

The singleton part has H_i(q)=-(Gamma*q)_i+O(|q|^2). The ONLY selected
large coefficient for recipient i is at the containing pair{i,pi(i)}. It
contributes

    kappa_i*M*(1-alpha_i)*q_(pi(i))
        *product_(j!=i,pi(i))(1-q_j).

It contributes nothing to B_i because that pair contains i. Put t=1/M
and q=t*z. The finite polynomial therefore cancels its apparent pole:

    Phi_i(t,z,c)=H_i(t*z)/t
      =kappa_i*P_i(z)-(Gamma*z)_i+t*E_i(t,z,c),         (5)

where E is a polynomial in t,z and all bounded residual coordinates c.
For example1-product(1-t*z_j)=t*sum z_j+t^2*(polynomial), so the selected
term in H/t has exactly the degree-two leading term in(5). All other
nonsingleton terms are at least quadratic in hazards before division by t.
No asymptotic strategic witness is supplied.

At t=0 the limiting field F=diag(kappa)P-Gamma*z satisfies F(v)=0 by(1),
and D_z F(v)=J. By(2) the finite-dimensional parameter implicit-function
theorem produces z(t,c) near v with Phi=0. Compactness of the residual box
gives a common t0>0 and uniform z=v+O(t). One can obtain this uniformity
either from a quantitative inverse-function neighborhood with bounded
derivatives, or by finitely many parameter neighborhoods and uniqueness
in a common small z-ball. For0<t<t0, z>0 and q=t*z lies strictly inside
the unit cube. This proves an ACTUAL H=0 profile and(3).

The same IFT with singleton coefficients and the n leading coefficients
as additional parameters proves the open-coefficient assertion. In this
version F's positive root, not the prescribed v, is solved by the theorem.
No promise about an unknown neighborhood radius is used in source separation.

## 3. Full terminal Nash and same-profile uniform payoff

For a stationary profile q with all coordinates in(0,1), every player has
alpha_i<1. From H=0, B_i=(1-alpha_i)Q_i. If player i Continues until t
and Quits at t, its terminal expectation is

    f_i(t)=B_i*sum_(k<t)alpha_i^k+alpha_i^t*Q_i=Q_i.

Never has value B_i/(1-alpha_i)=Q_i as well. Every complete private
behavioral replacement induces a stopping-time law on dates and Never,
independent of the opponents' clocks on the only live history. Its payoff
is the corresponding mixture of these values, hence exactly Q_i.
The prescribed stationary action law also earns Q_i. This proves full
terminal Nash, not merely a stationary best-reply check. No reward sign
enters the calculation.

Let R_table=max_(S,i)|r_i(S)|, which is finite for each fixed M. Against ANY
replacement the opponents' first quit has geometric tail alpha_i^t.
The difference between terminal reward and its N-date average is at most

    2*R_table/[N*(1-alpha_i)].                         (6)

Indeed the number of live dates before absorption is bounded by the time
to the first opponent quit, independently of the replacing player's law.
The same estimate holds for the prescribed profile. Applying(6) to both
sides of terminal Nash proves the same-profile uniform-equilibrium claim
at the actual terminal payoff. The horizon threshold may depend on M and
the actual reward table; no uniformity in M is claimed or needed.

## 4. Exact small calibration and failure boundary

For two players, Gamma=[0,a;b,0], pi interchanges the labels, and v>0.
Condition Gamma*v>0 means a,b>0. Then

    kappa=(a/v1,b/v0),     J=[0,a;b,0],    det J=-a*b.

The theorem produces the actual proper stationary component. The large
pair rewards also supply an easier sure-pair equilibrium here; this is a
calibration of the formulas, not new two-player coverage.

The two assumptions in(2) are actual hypotheses. An arbitrary positive v
does not force Gamma*v>0 or det J!=0; no automatic global selection of v
has been proved. At Gamma=0, formula(1) gives kappa=0 and J=0, so the
displayed IFT mechanism supplies nothing, even though that special game
may have easy equilibria. A vanishing determinant is not a no-UE conclusion.

## 5. A singular four-active exact source

Choose own singleton rewards1 and

    Gamma=[0,-69/20,-1,3;-3,0,4,-2;-3,-3,0,2;-4,-1,1,0],
    v=(1,1,6,4),        pi(i)=i-1 modulo4.

The matrix has rank3 and determinant0. Its right kernel is spanned by
(-2,20,12,27), and its left kernel by(20,-1,-31,24); BOTH have mixed
signs. Direct rational calculation gives

    Gamma*v=(51/20,13,2,1),
    P(v)=(44,11,6,48),
    kappa=(51/880,13/11,1/3,1/48),
    J=[0,81/22,271/220,-375/176;
       189/11,0,-31/11,35/11;
       10/3,16/3,0,-5/3;
       33/8,9/8,-17/24,0],
    det J=-228865/7744!=0.                            (7)

Thus the raw source assumptions hold at a SINGULAR singleton matrix. One
literal completion is

    0:(1,-2,-2,-3), 1:(-49/20,1,-2,0),
    2:(0,5,1,2), 3:(4,-1,3,1),
    01:(-4,(13/11)*M,1,1), 12:(1,-4,M/3,1),
    23:(1,1,-4,M/48), 03:((51/880)*M,1,1,-4),
    02:(-4,1,-4,1), 13:(1,-4,1,-4),
    012:(-4,-4,-4,1), 013:(-4,-4,1,-4),
    023:(-4,1,-4,-4), 123:(1,-4,-4,-4),
    I:(-10,-11,-12,-13).                               (8)

For every sufficiently large M the theorem gives a proper full terminal
Nash and same-profile UE, with q=(1,1,6,4)/M+O(M^-2). Every player is
active. The nonsingleton residual box can be R=13. The following screens
use M>600, solely to make every displayed strict coefficient comparison
immediate; this is not an explicit IFT threshold.

## 6. Bounded whole-source comparisons

### 6.1 Singleton and all deleted-triple tests

All proper principal blocks of size at least two are invertible. Every
column has a strictly negative external entry, and the full kernel is
mixed. Thus Gamma is R0: support of size2 or3 cannot annihilate its
invertible active block, size1 is blocked externally, and full support
cannot lie in the kernel. At offset ones the only regular LCP roots are

    empty: z=0, residual=ones, index+1;
    02: z=(1/3,0,1,0), residual=(0,4,0,2/3), index-1;
    123: z=(0,2,1,5/2), residual=(3/5,0,0,0), index-1.

The remaining two- and three-label active candidates fail as follows:

    support     determinant     one failed coordinate
    01          -207/20        F2=-20/23
    03           12            z3=-1/3
    12           12            z2=-1/4
    13           -2            F2=-1
    23           -2            z2=-1
    012          162/5         z0=-1/27
    013          -93/5         F2=-12/31
    023          -1            z0=-1.

Singleton support requires1=0. Full support Gamma*z=-ones is inconsistent
because the left kernel has nonzero sum12. The two remaining principal
determinants are det Gamma_02=-3 and det Gamma_123=-2. Hence R0 degree is
1-1-1=-1, already covered by the implemented nonunit-degree criterion.
The actual local index is sign(det Gamma_CC), with NO extra factor
(-1)^|C|, by `IsStandardLCPSolution.exists_box_localDegree_eq_sign_det`
in `MathUE/LinearProgramming/LocalDegree.lean`. The relevant raw consumer
is `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`.
Each row has a negative blocker, so the normal core is all4;
nonzero R0 degree gives standard-Q, not the ordinary non-Q core exit.
Pair01 is not projective-Q: at offset(-1,-1), projective nonnegative
variables would require-c-(69/20)*y>=0 and-c-3*x>=0, forcing all zero.

In natural increasing child order the actual four deleted inverses are

    delete0: [1,1,-4;1,1,-3;3/2,2,-6],
    delete1: [2,-3,2;8,-12,9;3,-4,3],
    delete2: [10/93,5/31,-23/62;-40/93,-20/31,15/31;
              -5/31,-23/31,69/124],
    delete3: [10/27,5/54,-23/54;-10/27,-5/54,5/54;
               5/18,23/72,-23/72].

EVERY inverse has a negative entry. Thus the ENTIRE child selection in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
fails its literal inverse prerequisite; no outside-weight shortcut is used.
The declaration is in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
Singularity separately excludes all full inverse-column sources, including
the signed one-column, full-positive-inverse, and opposite-two-column inputs.

Column0 is strictly negative off its diagonal, which excludes the positive
predecessor required by either signed once-per-owner four-cycle branch under
EVERY order. Every row has TWO negative off-diagonal entries, excluding
`QuittingCyclicSingletonOpenSignData.first_neg/later_nonneg` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`.
The only all-negative pivot columns are0 and1; neither child123 nor023
has a positive directed three-cycle. Therefore no pivot supplies
`CyclicChildSingleton.RawRows` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`.

### 6.2 All sure owners and universal quiet-child certificates

Given a sure owner i, both nonsuccessors strictly Continue: joining pays
at most-4, whereas every passive reward is at least-3. The successor alone
profits by joining for M>600. The owner then receives-4 but can withdraw
to its passive singleton at that successor, at least-3. There is NO Nash
root with a sure player, regardless of continuation. This excludes all
nonempty sure bases and all induced-Nash free-player selections, not just
one pointwise leave-safe sufficient screen.

Every nonempty proper child C has an unsafe EXACT child Nash. Choose d in C
with d+1 outside C; only d Quits0, the others Never. The owner earns1 rather
than Never0; each other child member gets a passive singleton at least-3,
whereas joining gives-4. Later changes cannot alter the absorbed outcome.
All child full debts and joint Never mass are0; the absent successor has
strictly positive join gain kappa_(d+1)*M-r_(d+1)({d}). This falsifies every
universal all-outsider child bound by child debts plus finite Never slack,
including the five withdrawal/advancing kinds. It does NOT alone exclude a
selective singleton-cycle lift; the actual all-deletion calculation above
performs that separate test.

### 6.3 Whole nonnegative weight sets, guards and quotients

The only strict premium trap is I: an above-own participant premium occurs
only at the incoming pair, so a proper trap would have to be closed under
the predecessor four-cycle. For w>=0 nonzero define the literal forced-Quit
test H_w(S)=sum_i w_i[r_i(S union{i})-1]. Then

    sum_d H_w({d})=sum_i w_i*(kappa_i*M-11)>0.         (9)

The actual weighted outsider INSERTION-leave tests have sum

    sum_d sum_(i!=d)w_i*[r_i({d,i})-r_i({d})]
       =sum_i w_i*[kappa_i*M-(191/20,10,7,7)_i]>0.    (10)

Thus every nonnegative upper-average weight, including weights with zeros,
fails, and some singleton leave charge is positive. The boxed charge arm
requires ALL proper singleton leave charges strictly negative, so fails
independently of every auxiliary threshold or box. The four directed-pair
PARTICIPANT tests instead sum to sum_i w_i*(kappa_i*M-6)>0.
No passive/own/participant subtraction is interchanged here.

A global nonnegative inserted floor fails at123, whose vector is
(-11,-5,-5,-5). Every player has an above-own incoming pair and an outgoing
donor-4<own1, excluding both participant-at-most-own protection and the
participant-at-least-own condition of `IsCommonQuittingPremiumLeaver`.
Every pair has one participant-4, excluding both-positive participant pair
sources; every triple has a negative ordered pair join, excluding the
six-positive-join triple-singleton raw condition.

For any ordered owner i and partner p choose j in{i+1,i+2} different from p.
At the sole-j-sure, zero-partner row the actual lower-face displacement is

    H_i=r_i({i,j})-r_i({j})=-4-r_i({j})<=-1<0.

Thus every weak lower face already fails, independently of all heights;
the stricter crossed polynomial/half/raw-unit guard variants also fail.
No favorite matching exists: row0's only positive singleton favorite is3,
but row3's only favorite is2, not0. The four incoming positive participant
edges cannot all fit in two disjoint pairs, so the cross-participant cap
shortcut also fails. All-sure actual response differences are
(-11,-12,-13,-14), pairwise distinct, excluding every nontrivial literal
response-invariant quotient.

The relevant tracked definitions include `quittingTrapLeaveSum` and
`QuittingTrapChargeCoefficients` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`;
`IsCommonQuittingPremiumLeaver` in
`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`;
`normalCore_eq_univ_of_fixed_blocker` in
`UniformEquilibrium/Quitting/Classification/LCP/ElementaryMatrixObstructions.lean`;
`Math.LinearProgramming.isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`;
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
and `DeadlineWithdrawalRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`.
These are bounded actual-source comparisons, not a universal novelty claim.

## 7. Exact remaining gate and next mathematical question

Independently falsify the canceled pair field, determinant(7), compact-box
quantifiers and ALL complete deviations. Independently check whole source
selection sets for the literal singular family(8), especially all deleted
triple choices rather than one unsafe child witness. No result should enter
exports before these checks pass.

The substantive open question remains how to select a closing mechanism for
an arbitrary FIXED raw table. This theorem designs a large incoming-pair
region; it does not allow changing the rewards of the conjecture's input
game. Nor does its Jacobian test prove that a usable positive v exists for
every singleton matrix. A new raw class is a reduction of potential
counterexamples, not a solution of arbitrary Fin4 existence.
