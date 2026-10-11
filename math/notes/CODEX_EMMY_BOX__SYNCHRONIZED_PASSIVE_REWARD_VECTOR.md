# Joint passive reward vectors and projective selection

Status: COMPLETE ORDINARY PROOF DRAFT, not Lean checked. Sections1–4 and
Section5 equations(7)–(9) have one bounded independent soundness PASS at
snapshot `a39eb261a2b7f91ddb977b843ecea82830be01d2fbb737f2646b8461934848cc`;
the degree census and whole-source comparisons remain unreviewed. Sections8–10
give a distinct two-coalition projective extension with one bounded
independent PASS at snapshot
`ab0508ee6c7106665dae14fb91816ac4cf9700f8cc00fb2258123854e2a36e73`,
subject to the incorporated correction that BOTH inverse directions in
Section10 are mixed. That review includes the whole sure-owner argument,
not a repeated audit of the Section6 census. Section11 retains an exact
covered-fixture kill of a further star extension. No export is requested
before a separate relevant whole-source comparison.

Section12 gives a macroscopic stationary producer with three passive poles
and one bounded independent PASS at snapshot
`3393051b39b6dbaef9e8592706b5150f26c8807479723bdf28dbe7e286f86617`.
Its exact limiting root and full Jacobian are supplied by ordinary
mathematics, not a numerical witness. It permits every fixed
nonnegative strength of the third pole, with a proper-coordinate neighborhood
and bounded pole residuals. It does NOT claim an arbitrary bounded box at
the macroscopic coordinates or a uniform threshold over unbounded strengths.
Section13 is a NEW, UNREVIEWED global raw-endpoint extension of this scale;
it removes every inverse/singleton-matrix prerequisite, replacing the local
bounded-coordinate tube by eight explicit strict endpoint inequalities.

The mechanism is cancellation BETWEEN inverse columns. Positivity of every
carrying signed column, a small error around one positive column, a prescribed
strategic witness, and a chosen nondegenerate root are not hypotheses.

## 1. Finite raw question and theorem

Let I be a finite player set of size n. Each nonempty quitting coalition T
absorbs at a finite reward vector r(T). Live dates and perpetual continuation
pay0. At each live date players use independent private randomization. A
unilateral deviation replaces one player's complete behavioral strategy,
including every finite quitting deadline and Never. All claims are expected
payoff claims; there is no public correlation device.

Fix arbitrary singleton rows. Put

    s_i=r_i({i}),    Gamma_ii=0,
    Gamma_ij=r_i({j})-s_i for j!=i.

Assume Gamma is invertible. Choose one proper coalition S with
2<=k=|S|<n. Choose a vector b with b_i=0 for every i in S and require ONLY

    v=Gamma^-1 b>0 coordinatewise.                         (1)

The nonzero entries of b can have arbitrary signs. In particular, carrying
columns of Gamma^-1 may each have mixed signs. Put d=k-1.

**Theorem.** For every finite residual bound R there is M0 such that EVERY
M>M0 and EVERY raw completion with the fixed singleton rows and

    r_i(S)=-M*b_i+c_i,       |c_i|<=R, for i outside S,
    |r_i(T)|<=R at every OTHER nonsingleton coordinate       (2)

has an all-interior stationary terminal Nash equilibrium against all complete
behavioral replacements. This SAME stationary profile delivers its actual
terminal payoff as a uniform-equilibrium payoff over all sufficiently long
finite horizons. There is no own-singleton sign restriction.

Writing t=M^(-1/d), its hazards satisfy

    q=t*z(t,c),
    z(t,c) -> z*=rho*v uniformly over the residual box,
    rho=(product_(j in S)v_j)^(-1/d)>0.                    (3)

No root, continuation, Nash selection, inverse-column sign, degree or
Jacobian is supplied as raw input. The threshold and convergence are uniform
on compact sets of singleton rows and b that preserve invertibility and(1),
with S fixed and R bounded. Own singleton levels must themselves remain
bounded in that compact-uniform statement.

At n=3 only one recipient can lie outside S, reducing(1) to the familiar
signed-column condition. The genuinely joint case begins at n=4, |S|=2.
The theorem changes a reward class; it is not a transformation of an arbitrary
fixed conjecture input into that class.

## 2. Exact canceled polynomial

For stationary opponent hazards q_-i write

    alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(B union{i})],
    B_i=E[r_i(B)*1_(B nonempty)],
    H_i(q)=(1-alpha_i)*Q_i-B_i,                         (4)

where B is the independent opponent quitter set at one date. The selected
coordinate r_i(S) is PASSIVE: i is absent from S. It enters only -B_i, not
Q_i. For i outside S its exact large contribution to H_i(t*z)/t is

    b_i*product_(j in S)z_j
         *product_(j notin S, j!=i)(1-t*z_j).

Indeed its raw size is t^(-d), its opponent probability has k powers of t,
and division by t leaves t^(k-d-1)=1. The negative raw sign in(2) cancels
the minus in -B_i. For i in S there is no selected pole.

Put P(z)=product_(j in S)z_j. Expanding all finite products gives an EXACT
polynomial extension

    Phi(t,z,c)=H(t*z)/t=P(z)*b-Gamma*z+t*E(t,z,c).           (5)

The singleton constant term is -Gamma*z. Every bounded nonsingleton term
has at least one remaining power of t after division by t. The extra
survival factors in the displayed pole are1 at t=0 and their difference
from1 is divisible by t. Thus E is polynomial and uniformly bounded with
all derivatives on compact(t,z,c) sets. Formula(5) is not merely an
asymptotic expansion. For actual t>0 its zeros are exactly H(t*z)=0.

## 3. Explicit net root and automatic nonsingularity

By(1) P(v)>0. Since P has degree k, the rho in(3) satisfies

    P(rho*v)=rho,       Gamma*(rho*v)=rho*b.

Therefore Phi(0,z*,c)=0 for EVERY residual vector c. Its derivative is

    J=-Gamma+b*(gradient P(z*))^T.

The matrix determinant lemma and Gamma^-1 b=v give

    det J=det(-Gamma)*[1-gradient P(z*) dot v]
         =det(-Gamma)*(1-k)
         =-d*det(-Gamma)!=0.                            (6)

The middle equality is Euler's identity:
gradient P(z*) dot v=k*P(z*)/rho=k. There is no positivity assumption on
individual inverse columns and no regularity assumption beyond Gamma's
invertibility.

For completeness, a uniform local production argument need not choose a
different implicit neighborhood for each residual. Fix a small closed ball
X about z* lying strictly in the positive orthant. The map

    T_(t,c)(z)=z-J^-1*Phi(t,z,c)

has derivative0 at(t,z)=(0,z*) for every c. Choose X small enough that the
derivative norm on X at t=0 is<1/3. Polynomial compactness then makes its
norm<1/2 on X for all sufficiently small t and EVERY |c|<=R. Its center
displacement is uniformly O(t), so, after reducing t, it maps X into itself.
Banach's theorem gives a zero z(t,c) in X, unique there. Its distance from
z* is O(t) uniformly. Finally choose t so that t*max_(z in X,i)z_i<1.
All produced hazards are strictly between0 and1.

The same compact argument gives the stated parameter uniformity, using
continuous z*, continuous J^-1 and a common strictly positive distance of
the limiting roots from every coordinate face.

There is also a fixed eta>0 such that ALL residuals in(2) can instead obey
|c|<=eta*M^(1/d), for every sufficiently large M. Write e=t*c; the bounded
coordinate contribution in(5) is linear in c, hence becomes a continuous
small perturbation linear in e. Choose eta first to preserve the strict
ball/contraction margins, then t small. This scale-thick conclusion does
not assert the limiting z* or payoff in(3) when e fails to tend to0.

## 4. Complete agency and the actual fixed uniform target

All hazards are positive and n>=3, so alpha_i<1 for every i. At a produced
zero H_i=0 put

    V_i=B_i/(1-alpha_i)=Q_i.

The actual stationary payoff satisfies

    U_i=q_i*Q_i+(1-q_i)*(B_i+alpha_i*U_i),

and joint absorption is proper. Its unique solution is U_i=V_i. Every pure
finite deadline h earns

    V_i+alpha_i^h*(Q_i-V_i)=V_i;

Never also earns V_i. On the unique live public history, any complete private
behavioral replacement is an independent mixture of these stopping laws,
so also earns V_i. Thus this is FULL terminal Nash, not just Nash among
stationary hazards or a bounded deadline menu. Arbitrary signs of b, s and
the terminal rewards cause no agency exception.

For each FIXED table and fixed produced profile let C bound all its terminal
reward magnitudes. Under every replacement of player i, independent opponents
terminate no later than their own geometric first-quit time, with mean at
most1/(1-alpha_i). Terminal and N-date average payoffs differ by at most
2C/[N*(1-alpha_i)], uniformly over that entire replacement class. Applying
this estimate to both sides of Nash and to prescribed payoff delivery gives
the SAME-profile uniform-equilibrium conclusion with target V fixed before
accuracy. M and the table are fixed before N grows.

For bounded residual boxes the selected passive rewards never enter any
Q_i. Consequently Q_i(t*z)=s_i+O(t), uniformly, and the cross-table family
of actual targets tends to s. This last statement is an asymptotic
calibration, not a common target assigned to distinct games.

The corresponding actual semantic consumers, inspected with their hypotheses,
are `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`. This note has
not implemented its raw-data producer in Lean.

## 5. Exact four-player joint-cancellation family

Take all own singletons10 and

    Gamma=[ 0, 2,-6,-3;
           -1, 0, 4, 4;
           -2, 7, 0,-6;
            3,-3, 7, 0 ],                 det Gamma=265,

    Gamma^-1=(1/265)[268,171,-20,132;
                     170,150, 15, 60;
                     -42, -9, 15,  7;
                     109,118,-20, 26].                       (7)

The literal singleton vectors, owner first, are

    0:(10,9,8,13),   1:(12,10,17,7),
    2:(4,14,10,17),  3:(7,14,4,10).

Select S={1,3}, b=e0+4e2. BOTH carrying inverse columns0 and2 have strict
mixed signs, even after an arbitrary sign flip. Nevertheless

    Gamma^-1 b=(188,230,18,29)/265>0.                         (8)

More generally Gamma^-1(e0+x*e2)>0 holds EXACTLY when

    14/5 < x < 109/20.                                    (9)

This interval is separated from both individual column rays; it is not a
small perturbation of a positive carrying column. The four coordinate
inequalities from(7) give(9) directly.

For the fixed ratio4 the explicit leading root is

    z*=(9964,12190,954,1537)/1334,
    det J=-265.

For every M>0 complete the other rows as follows. On each cycle pair
{i,i+1}, labels modulo4, pay-1 to donor i,40 to recipient i+1, and1 to
outsiders. Opposite pairs pay-1 to participants and1 to outsiders, EXCEPT
for the two selected passive entries. Thus

    01:(-1,40,1,1), 12:(1,-1,40,1),
    23:(1,1,-1,40), 03:(40,1,1,-1),
    02:(-1,1,-1,1), 13:(-M,-1,-4M,-1).

Triples pay-1 to members and1 to the outsider. The grand coalition pays
(-10,-11,-12,-13). All residual nonsingleton data lie in[-40,40]. The theorem
therefore gives actual all-interior stationary Nash/UE for EVERY sufficiently
large M, and uniformly over arbitrary residual perturbations in a fixed box.

### 5.1 Exact R0 and degree calibration

Every off-diagonal column of Gamma has a negative entry. All eleven principal
blocks of sizes2,3,4 are nonsingular, as the census below shows. A nonzero
homogeneous complementary vector cannot have singleton support, because of
the negative outside column entry. A larger support would give a nonzero
kernel of its principal block. Hence Gamma is R0.

At offset ones, the candidates x=-Gamma_CC^-1*ones are:

| C | det Gamma_CC | candidate x |
|---|---:|---|
| 01 | 2 | (1,-1/2) |
| 02 | -12 | (1/2,1/6) |
| 03 | 9 | (-1/3,1/3) |
| 12 | -28 | (-1/7,-1/4) |
| 13 | 12 | (1/3,-1/4) |
| 23 | 42 | (-1/7,1/6) |
| 012 | 26 | (31/13,7/13,9/26) |
| 013 | 15 | (-29/15,-8/5,-11/15) |
| 023 | 150 | (-19/50,1/50,22/75) |
| 123 | 268 | (-23/134,-29/134,-9/268) |
| 0123 | 265 | (-551/265,-79/53,29/265,-233/265) |

Exactly02 and012 are positive candidates. Their outside residuals are,
respectively,(7/6,11/3) and233/26, all strictly positive. Singletons cannot
solve the active equation at positive offset. Thus the ENTIRE root set is
empty-support0, support02, support012. Its degree is

    1 + sign(-12) + sign(26) = 1.                           (10)

The index sign is sign(det Gamma_CC), with NO additional support-cardinality
factor. The declaration `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`IsStandardLCPSolution.exists_box_localDegree_eq_sign_det` in
`MathUE/LinearProgramming/LocalDegree.lean` were inspected for this convention.
Consequently this family does not leave the bare Fin4 no-UE singleton degree
class by its singleton data. The applicable original-game necessary condition
is `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`.

## 6. Bounded whole-source comparisons on this family

These are ordinary exact comparisons. They do not classify every conditional
certificate or every unknown quantitative neighborhood in the repository.

### 6.1 EVERY sure-owner and nonempty-base root fails

There is no root Nash with any sure quitter, for ANY continuation annotation
and ANY M>0. Fix a sure owner a. A nonowner's complete root comparison has
no continuation term, since a surely absorbs at that date.

If a is outside{1,3}, no nonowner can see opponent coalition13: its opponent
coalition contains a. Hence the selected passive penalties never enter a
nonowner's Continue comparison. Every nonsuccessor nonowner has joining
reward at most-1, but Continue receives a singleton reward>=4, or passive
pair/triple reward1. It strictly Continues.

If a belongs to{1,3}, the OTHER member of{1,3} is its cycle-opposite
nonsuccessor and is itself NOT a carrying recipient. The same strict
comparison first forces that player to Continue. Coalition13 is now
impossible, after which every other nonsuccessor strictly Continues as well.

In both cases only a and successor(a) can Quit. The successor earns40 by
joining, rather than its passive singleton<=17, so it surely Quits. Owner a
then earns-1 but withdrawing earns its passive singleton at the successor,
which is>=4. This contradicts Nash. The argument covers ALL probabilities
of the three free players and ALL nonempty sure bases, not only pure roots
or pointwise leave-safe screens.

### 6.2 Universal child bounds fail; selective inverse lifts fail separately

For every nonempty proper child C choose d in C with d+1 outside C. Only d
Quits0; other child members Never. The owner earns10 instead of Never0.
Every other child member receives a passive singleton>=4, while joining
would pay-1. The actual child profile is exact full Nash and has joint
Never mass0. The absent successor gains at least40-17=23 by joining.
Therefore no universal all-outsider bound by child debts and finite Never
slack holds. This defeats the broad raw reward certificates whose semantic
consequence is such a bound, not merely their advancing-only subcone.

One can also falsify the literal F/J-only withdrawal rows directly, without
invoking that semantic consequence. For the same child C and A={d}, the
outsider joining gain is at least23. Every child member i other than d is
not successor(d), so its advancing gain is

    r_i({d,i})-r_i({d})=-1-r_i({d})<=-5.

The owner's advancing gain is0. For each of the five withdrawal kinds,
members outside A have withdrawal gain0, and the owner's singleton
withdrawal gain is a restart floor minus its own10, hence is nonpositive.
Indeed the patient floor is at most max(10,0)=10; the deadline/cancellation
floor is at most0; the evaluated-security floor is truncated at0; and the
terminal-security floor is the maximum of a nonpositive zero floor and a
security value at most the own singleton10. Thus the right side of the
join row is nonpositive for EVERY pair of nonnegative weight arrays, whereas
its left side is strictly positive. This excludes all five kinds over ALL
nonempty proper children, including F/J-only certificates without an N row.

The exact definitions reopened for this calculation are
`WithdrawalFutureJoinKind.gain` and
`WithdrawalFutureJoinRewardCertificate.join_row` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`,
`deadlineWithdrawalGainFloor` in `DeadlineWithdrawalRaw.lean`,
`patientWithdrawalFloor_le_ownNeverAlternative` in `PatientWithdrawalRaw.lean`,
`deadlineSecurityGainFloor` in `DeadlineWithdrawalSecurityMixedPointwise.lean`,
`deadlineSecurityGainFloorWithRestart` in
`DeadlineWithdrawalRestartPointwiseCore.lean`, and
`deadlineWithdrawalSecurityValue_le_singleton` and
`deadlineWithdrawalSecurityFloor` in `DeadlineWithdrawalSecurityLP.lean`.
The last five filenames share that same `Classification/QuietExtension/`
directory.

The DISTINCT selective inverse criterion also fails for every deleted label.
In increasing retained-label order, the deleted0 inverse has entry(0,2)
-6/67, deleted1 has entry(0,1) -7/50, and deleted3 has entry(0,0) -14/13.
The deleted2 inverse is strictly positive, but its actual outside row times
that inverse is

    (14/5,3/5,-7/15).

Thus the conjunction in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`)
fails over ALL four child choices. This actual declaration was reopened;
mere existence of a positive child inverse would not be a sufficient screen.

### 6.3 Entire weight sets and actual pair faces

The only premium trap is all4: the only above-own PARTICIPANT row for i is
its incoming cycle pair, so any trap would have to be closed under the full
predecessor cycle. Passive negative penalties create no additional
participant premium.

For arbitrary nonzero weights w>=0 let
H_w(T)=sum_i w_i[r_i(T union{i})-s_i]. Summing the four singleton tests gives

    sum_d H_w({d})=8*sum_i w_i>0.                         (11)

Thus the ENTIRE supportwise upper-average weight set, including zero weights,
fails. The actual unweighted singleton outsider INSERTION-leave sums are
(8,2,3,13), all positive, so the boxed strictly negative singleton leave row
fails as well. Weighted insertion-leave sums across all four singletons are

    15*w0+w1+9*w2+w3>0.

Weighted PARTICIPANT premiums across the four cycle pairs sum to19*sum w_i>0.
These three subtractions are distinct. At background012 the global inserted
own-premium vector is(-11,-11,-11,-23), excluding every positive global floor
weighting. The definitions checked are `HasBoxedQuittingNashCharges` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`
and the raw hypotheses in the boxed/mixed-support exported statements.
In particular `QuittingTrapChargeCoefficients.leave_nonpos` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
requires nonpositive leave sums for every nonempty proper subcoalition of
the all-player trap, already contradicted by each displayed singleton.

Every player fails participant-at-most-own protection at its incoming40 pair,
and participant-at-least-own common-leaver protection at its outgoing-1 pair.
Every pair has a below-own participant; every triple contains a negative
ordered pair joining gain. Thus the both-above-own pair and six-positive-join
triple raw predicates fail over their whole selections.

For ANY owner i and partner p choose j in{i+1,i+2} different from p. At the
sole-sure outsider row and zero partner hazard the actual owner residual is

    r_i({i,j})-r_i({j})=-1-r_i({j})<=-5<0.                (12)

This violates even the weak lower crossed face, for every pair and height;
it is not merely failure of a sufficient coefficient guard. The relevant
definitions are `QuittingCrossedSourceGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`
and `QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.

### 6.4 Singleton, quotient and literal pole-source hypotheses

Each Gamma row has a negative blocker, so the recursive normal core is all4.
Degree1 gives full standardQ by `isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`; the ordinary non-Q core exit is
therefore unavailable. The all-principal projective-Q side fails at03:
for matrix[0,-3;3,0] and offset(-1,-1), the first residual is ALWAYS negative
on the nonnegative orthant.

No column is wholly negative off-diagonal, excluding the raw negative-pivot
cyclic-child pattern. No cyclic ordering supplies simultaneously positive
predecessor and negative successor singleton entries. Up to cyclic start the
orders0123,0132,0213,0312 fail a predecessor sign at0; order0231 fails it
at2; order0321 fails the negative-successor sign at3. These are the literal
requirements in `SignedFourCycleSingletonData` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`, before
either spectral branch. The cyclic open-sign producer also fails: row0 has
two negative entries. Multiple positive favorites in rows1 and3 exclude
the weak-matching singleton row pattern.

At the all-sure root the complete Quit-minus-Continue differences are
(-11,-12,-13,-14), pairwise distinct. Any actual full-response-invariant
quotient must therefore be injective; asymmetry alone is not the argument.

The two carrying columns0 and2 in(7) have mixed signs under BOTH sign choices.
Hence the positive/signed INDIVIDUAL inverse-column prerequisite of the
one-column and selected-column-cone raw producers fails at every growing
coordinate. An unselected positive column3 does not turn either actual pole
into that recipient's pole. Both actual field signs are positive, since both
large rewards are passive and negative. The opposite-FIELD-sign two-pole
source fails this literal input, independently of any projective bracket.
The selected large rewards are passive; a participatory-only pole theorem
also does not describe this raw family.

This is a comparison of explicit raw hypotheses and whole stated selections.
No assertion excludes every possible pointwise use of an unspecified residual
threshold, an unknown IFT radius, or an unenumerated strategy architecture.

## 7. Concrete falsification request and next question

The completed independent producer check covered the passive sign and pole exponent in
(5), Euler determinant(6), uniform compact-box and scale-thick quantifiers,
ALL finite deadlines/Never, the fixed-table/same-profile uniform target, and
only the matrix/net-vector/root arithmetic in(7)–(9). It found no objection;
see `feedback/CODEX_EMMY_BOX__SYNCHRONIZED_PASSIVE_REWARD_VECTOR__BY_CODEX_TURING_BOX.md`.
The still-unreviewed fixture question is the actual degree census, the WHOLE
sure-owner proof at the selected negative passive pair, all deleted inverse
conjunctions, and entire weight/guard selections.

The single-vector theorem uses an exact common monomial. Sections8–10
answer one part of the next question by an independent two-monomial
projective selector; no claim about unrestricted collections of changing
directions follows.

## 8. A distinct two-coalition projective producer

Status: COMPLETE ORDINARY PROOF, with one bounded independent soundness
PASS within the scope recorded at the top; not Lean checked. This removes the common
monomial restriction in Sections1–4. It is not a consequence of positivity
of either aggregate inverse direction, and the field coefficients do not
have to have opposite signs. The exact new fixture is in Section10.

Fix finite singleton data as before, with invertible Gamma. Choose distinct
proper coalitions S1,S2, each with k_l=|S_l|>=2, and put d_l=k_l-1.
Choose linearly independent vectors b1,b2 satisfying

    (b_l)_i=0 whenever i in S_l,     l=1,2.

Thus each selected vector is purely PASSIVE for its selected coalition.
Neither the vectors b_l nor their inverse images need be positive. Define

    u=Gamma^-1 b1,        w=Gamma^-1 b2,
    V(x)=u+x*w,          P_l(z)=product_(j in S_l)z_j,
    G(x)=x-[P1(V(x))]^(-d2/d1)*P2(V(x)).                 (13)

Assume finite numbers0<a<b satisfy

    V(a)>0, V(b)>0 coordinatewise,       G(a)*G(b)<0.     (14)

Affine positivity implies V(x)>0 throughout[a,b]. These are finite raw
singleton/coefficient inequalities, not a supplied strategic witness or
a chosen polynomial root. For equal coalition sizes, the scalar reduces
to G=x-P2(V)/P1(V), and its signs can be checked by positive denominator
clearing. No inverse-column sign assumption is imposed.

**Two-coalition theorem.** For every finite R>=0 there exists L0 such that
EVERY L>L0 and EVERY raw completion with the fixed singleton rows and

    r_i(S_l)=-L^d_l*(b_l)_i+c_(i,l),  |c_(i,l)|<=R,
                                               i outside S_l, l=1,2,
    |r_i(T)|<=R at every other nonsingleton coordinate             (15)

has an ALL-interior independent stationary terminal Nash equilibrium
against EVERY complete behavioral replacement, including all finite
deadlines and Never. The SAME profile supplies its actual terminal payoff
as a uniform-equilibrium payoff. Own singleton signs are unrestricted.
The hazards are q=z/L in a fixed compact positive set of z values.

The threshold is uniform over compact sets of the displayed finite data
retaining invertibility, linear independence, endpoint positivity and the
strict endpoint sign difference. Singleton levels are included in that
compact data. Labels and coalitions are fixed. There is also an eta>0
for which all nonsingleton residual bounds may instead be eta*L for all
sufficiently large L. No limiting strategic target or uniqueness is claimed.

## 9. Complete two-coalition production proof

Put t=1/L and q=t*z. The passive cancellation in Section2, applied separately
to the two distinct selected coalitions, gives the EXACT polynomial field

    Phi(t,z,c)=H(t*z)/t
             =b1*P1(z)+b2*P2(z)-Gamma*z+t*E(t,z,c).     (16)

Different pole degrees cause no negative residual powers: k_l-d_l-1=0
for each l separately. All other nonsingleton coordinates contribute a
factor t or higher. The selected survival factors also differ from1 by a
factor t. Hence the remainder E is polynomial and uniform on compact boxes.

Extend b1,b2 to any fixed basis B=[b1,b2,W] of the reward-coordinate space.
Use coordinates h>0, x in[a,b], y in R^(n-2):

    z=Gamma^-1[h*b1+h*x*b2+W*y].

Apply B^-1 to(16), and denote the result Psi. At t=0 it is exactly

    Psi1=P1(z)-h,
    Psi2=P2(z)-h*x,
    Psi_rest=-y.                                         (17)

At y=0, z=h*V(x)>0. The explicit radial branch

    h0(x)=[P1(V(x))]^(-1/d1)

solves Psi1=0 and every transverse equation, for EVERY x in[a,b]. The
Jacobian of these n-1 equations with respect to(h,y) has block form

    [ d1   * ]
    [  0  -I ],                                          (18)

because the radial derivative at this positive branch is
(d1+1)*h0^d1*P1(V)-1=d1. Thus it is nonsingular. This is an automatic
partial Jacobian, not a hypothesis about a fully selected angular root.

The compact-parameter implicit function theorem supplies continuous
h(t,x,c)>0 and y(t,x,c), uniformly near(h0(x),0), solving these n-1
equations for every x and every bounded residual. A common contraction
neighborhood on the compact branch proves uniform existence and local
uniqueness; overlapping local charts agree. There is no angular uniqueness
claim. The remaining scalar residual satisfies uniformly

    -Psi2(t,z(t,x,c))/h(t,x,c)
         -> x-h0(x)^d2*P2(V(x))=G(x).

Its endpoint signs remain opposite by(14). The intermediate value theorem
therefore gives an interior x where Psi2 also vanishes. Uniform closeness
to the positive compact branch ensures z>0, bounded, and then q=t*z is
strictly between0 and1 for t sufficiently small. Since B and Gamma are
invertible, no equation of H has been discarded. This produces the actual
terminal stationary profile from the raw rewards.

For scale-thick residuals write e=t*c. Every residual contribution to H/t
has at least one factor t before this substitution, including selected
coalitions of size2. The extension is polynomial in(t,z,e); at(t,e)=(0,0)
its branch, partial inverse and strict endpoint signs are exactly those
above. A fixed sufficiently small eta preserves all strict margins for
|e|<=eta. This proves the eta*L statement. Compact singleton/coefficient
uniformity follows by finitely many basis charts: linear independence
permits a fixed complement W on each sufficiently small parameter
neighborhood, and finitely many such neighborhoods cover a compact set.

Every produced coordinate is interior, so the ENTIRE agency and fixed-table
uniform-payoff proof in Section4 applies without alteration. In particular
EVERY pure deadline and Never earn the actual stationary Q_i, and deleted
opponent contraction controls ALL complete behavioral deviations uniformly
over long finite horizons. The two-vector projection is solely an algebraic
coordinate change, not public randomization or a convexification of laws.

## 10. Exact degree-one four-player test with distinct monomials

Use EXACTLY the singleton rows and Gamma in(7), but replace the two opposite
pair rows by

    r(02)=(-1,-M,-1,1),       r(13)=(1,-1,-M,-1).         (19)

All four adjacent pair rows, all triple rows and the grand row are exactly
those in Section5. Take S1=13,b1=e2 and S2=02,b2=e1, with L=M and d1=d2=1.
Then

    V(x)=(1/265)(-20+171x, 15+150x, 15-9x, -20+118x).

This vector is strictly positive EXACTLY when10/59<x<5/3. BOTH directions
u and w are mixed; no common monomial combines the poles.
The scalar is

    G(x)=(5900*x^3+103*x^2-1015*x+100)
                          /[10*(10*x+1)*(59*x-10)],

    G(1/5)=-646/675<0,          G(1)=2544/2695>0.         (20)

Both endpoints lie strictly in the positivity interval, so the theorem
produces actual all-interior stationary terminal Nash for EVERY sufficiently
large M and every fixed bounded perturbation box. Neither pole is of opposite
FIELD sign: both raw coefficients are negative, both recipients absent, and
both leading field coefficients are positive. The actual inverse column2
remains mixed under BOTH signs. Thus this raw asymptotic family does not
satisfy the displayed fixed-residual hypotheses of the columnwise-positive
cone source, the literal opposite-field-sign two-pole source, or the
common-monomial net-vector source. This comparison does NOT bound any
unspecified scale-thick threshold from those theorems and does not exclude
a separate pointwise application of such a threshold.

The singleton degree and ALL four selective deleted-inverse tests remain
EXACTLY those already calculated, since singleton data did not change.
The entire singleton upper-weight, leave-weight, boxed singleton and crossed
face contradictions in Section6 also remain unchanged: those rows use only
singletons and recipient-PRESENT pair rewards. The two modified entries are
PASSIVE. The global inserted floor, participant protections, signed-cycle
singleton screens and all-sure quotient residuals likewise are unchanged.

The whole sure-owner argument requires a new check rather than an appeal
to the earlier single-pair proof. Given a sure owner a, first consider its
cycle-opposite player a+2. A passive selected opponent pair not containing a
is impossible because a is sure; the opposite pair containing a also contains
a+2, so cannot be a PASSIVE payoff coordinate for that player. Thus its
joining rewards are at most-1 while its Continue rewards are at least1
(and at least4 at singleton absorption). It strictly Continues. The
opposite pair containing a is now impossible; the other opposite pair was
already impossible because it omitted a. No selected penalty remains in
ANY nonowner comparison. Every nonsuccessor therefore strictly Continues,
the successor surely Joins for40, and the owner strictly withdraws from-1
to a passive singleton>=4. This excludes EVERY sure-owner/free-player Nash
component for every M>0, not just pure profiles or pointwise guards.

All14 bad child singleton witnesses are unchanged as well. Their child
member and outsider advancing rows use recipient-present pairs, so the
strict outside gain and nonpositive child gain proof still excludes all
five raw withdrawal kinds over all children and all nonnegative weights.
No exhaustive comparison with unspecified neighborhoods or pointwise
residual thresholds is inferred. The new construction is an asymptotic
raw-class result, not proof that the original singleton matrix alone is
uncovered, nor a universal reduction of arbitrary four-player tables.

The bounded independent check reconstructed the basis-coordinate partial
IFT, equal/mixed-degree scalar normalization in(16)–(18), the WHOLE sure-owner
argument for both passive pairs, and the exact bracket in(20), without an
unresolved mathematical objection after the mixed-w correction. See the
same feedback file cited in Section7. Separate whole-source admission and
any further number of independently varying monomials remain open.

## 11. Early kill of a three-coalition star fixture

Status: exact ordinary calculation, not independently reviewed. This is a
DISTINCT attempted extension, not an objection to Sections1–10. The test
shows why a plausible angular Perron mechanism must still earn new coverage.

Keep the same singleton Gamma and all own rewards10. Keep the four cycle
participant pairs as in Section5, the opposite-pair participant rewards-1,
triple members-1/passive outsiders1, and grand(-10,-11,-12,-13). Set all
passive pair rewards1 except the following five penalties:

    r2(01)=r3(01)=-M,       r1(02)=-M,
    r1(03)=-M,             r2(03)=-6M.                   (21)

The grouped passive directions on the three star pairs01,02,03 are

    Gamma^-1(e2+e3)=(112,75,22,6)/265,
    Gamma^-1 e1=(171,150,-9,118)/265,
    Gamma^-1(e1+6e2)=(51,240,81,-2)/265.

Their leaf block is Metzler with positive off-diagonals and positive row
sums. This suggests a positive Perron angular construction without positive
individual columns. No general Perron producer is claimed here: before
developing one, the proposed fixture already has a simple full equilibrium.

For EVERY M>=1 let player3 Quit0 surely, player1 Never, and let players0,2
independently Quit0 with probabilities

    a=5/(6M+4),          c=33/35,

and otherwise Never. Their full root gains are

    Delta0=33-35c=0,
    Delta2=-5+(6M+4)a=0,
    Delta1=[-96+a*(2M-302)]/35<0.                       (22)

The last strict sign holds for all M>=1: if2M-302<=0 it is immediate;
otherwise a*(2M-302)<5/3<96. Thus the three nonowners are full best replies,
not merely stationary or root-restricted replies: the sure owner absorbs
at date0 under every nonowner replacement.

Against the displayed opponents, player3's best post-date0 continuation
quits alone at date1 on the event that both opponents selected Never; own
solo10 dominates Never0 on that event. All later finite deadlines have the
same terminal value. Its exact Quit0-minus-this-complete-cap gain is

    Delta3=23c-a*(14+11c)=(759-853a)/35>0,               (23)

since a<=1/2. Therefore player3 also has no full profitable replacement.
This is an actual terminal Nash profile with a sure owner, for every M>=1.

Consequently this proposed star fixture does not separate a new existence
class from the sure-owner architecture. No spectral scaling analysis or
broader source-screen enumeration is needed for it. The failed inference
is that mixed inverse directions and a positive angular Perron pattern
alone certify new raw coverage; the actual root game must still be tested.

Concrete next question: can a genuinely joint angular selector handle
three or more distinct coalition monomials on an actual raw family for
which the ENTIRE sure-owner correspondence is excluded, without reducing
to the already proved two-direction bracket? The test(21) is not such a
family; it is deliberately not being weakened into another proposed class.

## 12. Three poles and a macroscopic boundary-scale producer

Status: complete ordinary proof draft with one bounded independent PASS at
the snapshot named above; not Lean checked. The review checked the exact
raw cancellation, scalar branch, Jacobian, quantifiers and whole sure-owner
inheritance, not a new whole-source census. This is a new scale and an actual
raw-table producer, rather than a requested root or a low-hazard remainder
estimate.

### 12.1 Raw question, data and quantifiers

There are four players0,1,2,3. Live rewards and Never are0; all randomization
is independent and private. A replacement may be any complete behavioral
strategy, including every finite deadline and Never. Keep the singleton
rows

    r(0)=(10,9,8,13),    r(1)=(12,10,17,7),
    r(2)=(4,14,10,17),   r(3)=(7,14,4,10).

Fix a>=0 and a scale M>0. The nonsingleton center is

    r(01)=(-1,40,1,a*M),     r(12)=(1,-1,40,1),
    r(23)=(1,1,-1,40),       r(03)=(40,1,1,-1),
    r(02)=(-1,-M,-1,1),      r(13)=(1,-1,-M,-1).

Every triple pays-1 to its members and1 to its absent player. The grand row
is(-10,-11,-12,-13). The ONLY large coordinates are passive:

    r1(02)=-M,     r2(13)=-M,     r3(01)=a*M.             (24)

**Theorem draft.** For every fixed a>=0 this center has an all-interior
stationary terminal Nash equilibrium for every sufficiently large M. The
SAME profile is a uniform equilibrium with its actual payoff as fixed target.
Moreover, for each finite A and R there exist eta>0 and M0 such that the
conclusion holds simultaneously for ALL a in[0,A], ALL M>M0, ALL three
selected coordinates(24) with arbitrary additive residuals of magnitude<=R,
and ALL other57 reward coordinates within eta of their displayed centers.
Those57 include the singleton coordinates. No strategic witness is input.

The neighborhood assertion is genuinely LOCAL at the bounded coordinates.
Their order-one effects survive in the limiting equations; this theorem
does not permit an arbitrary bounded box there. The threshold may depend
on A and R, and no uniform M0 over unbounded a is asserted.

### 12.2 Exact pole cancellation at a different scale

Put t=1/M and use coordinates

    q0=x,     q1=t*y,     q2=c,     q3=1-t*z.             (25)

As in(4), H_i=(1-alpha_i)Q_i-B_i. Each selected passive pole enters only
-B_i. Its exact contribution is respectively

    H1: +x*c*z,
    H2: +y*(1-t*z)*(1-x),
    H3: -a*x*y*(1-c).

In particular there is NO negative power of t after substitution(25).
All other raw entries contribute polynomials in t,x,y,c,z. At the displayed
bounded center, setting t=0 gives the exact limiting equations

    F0=33-35*c,
    F1=x*c*(z-10)-2-13*(1-x)*(1-c),
    F2=-5+3*x+y*(1-x),
    F3=(1-(1-x)*(1-c))*(10+30*c-x*(11+30*c))
          -(13*x+17*c-29*x*c)-a*x*y*(1-c).             (26)

These identities follow by enumerating the opponent quitter set in Q_i and
B_i, not by treating the near-sure player as an exogenous public stopper.
For example player3's Quit endpoint at t=0 is
10+30*c-x*(11+30*c), whereas its bounded Continue stopping term is
13*x+17*c-29*x*c. The additional pole is negative in H3, even though its
raw passive reward is positive.

Bounded additive residuals at the three pole coordinates contribute terms
divisible by t. Small changes in the other57 coordinates change(26)
continuously at order one. This explains the different quantifiers in
Section12.1.

### 12.3 A global scalar branch for every a>=0

The first three equations of(26) give, for0<x<1,

    c=33/35,
    y=(5-3*x)/(1-x)>0,
    z=(304*x+96)/(33*x)>0.                             (27)

Substituting these into F3 gives

    F3_base= (4917-5025*x-550*x^2)/245,
    D=x*y*(1-c)=2*x*(5-3*x)/(35*(1-x))>0,
    F3=F3_base-a*D.

Let x_star be the unique root in(0,1) of

    K(x)=4917-5025*x-550*x^2=0.

Existence and uniqueness follow from K(0)>0,K(1)<0,K'<0. Its exact value is

    x_star=-201/44+sqrt(1442721)/220.

On0<x<x_star define

    a(x)=(1-x)*K(x)/(14*x*(5-3*x)).                    (28)

This function is strictly decreasing, tends to infinity at0, and tends to0
at x_star. For the strict derivative, K is positive and strictly decreasing
on this interval, while

    d/dx [(1-x)/(x*(5-3*x))]
       =-[3*(x-1)^2+2]/[x^2*(5-3*x)^2]<0.

Therefore EVERY a>0 has exactly one solution x(a) in(0,x_star). Set
x(0)=x_star. Its derivative at the a=0 endpoint is still nonzero: the
derivative of(28) there is the positive prefactor times K'(x_star)<0.
Thus x(a),y(a),z(a) are continuous, indeed locally smooth, on[0,infinity),
and remain strictly inside their required positive ranges on every compact
a interval. This is a global scalar selection, not an assumed IFT root.

### 12.4 Automatic nonsingularity and actual production

Use unknowns(c,z,y,x), in that order. The first equation determines c with
derivative-35. With c fixed, the second determines z with derivative x*c>0.
The third determines y with derivative1-x>0. After these eliminations the
last derivative, at a=a(x), is

    d/dx [F3_base(x)-a*D(x)] = D(x)*a'(x)<0.           (29)

All four factors are nonzero. Successive Schur complements therefore show
that the full4 by4 Jacobian of(26) is nonsingular. This argument includes
a=0. No generic nondegeneracy assumption is needed.

The polynomial implicit function theorem now gives, for each fixed a and
all sufficiently small positive t, an actual zero H(q)=0 near(25)–(27).
Continuity makes0<q0,q1,q2,q3<1: x and c stay in(0,1), y,z stay positive,
and t*y,t*z are small. The three bounded pole residuals occur only multiplied
by t. Compactness of a in[0,A] and of those residuals in[-R,R]^3, together
with uniform invertibility of(29), gives a common eta and t0 for the57
remaining coordinates. Equivalently M0=1/t0. The usual finite-chart IFT
cover is enough; no uniqueness of all equilibrium branches is asserted.

Because all four hazards are interior, every deleted-opponent survival
alpha_i is below1. At H=0 the actual terminal value is Q_i=B_i/(1-alpha_i).
Every finite deadline and Never earns exactly that value, and mixtures of
deadlines represent every complete behavioral replacement on the unique
live history. Thus the produced profile is FULL terminal Nash. The
geometric opponent absorption estimate in Section4 proves SAME-profile
uniform payoff delivery and deviation safety for all sufficiently long
finite horizons, with M and the actual table fixed first. No sign condition
on the resulting value is required.

At the exact displayed center the actual targets tend, as M grows, to

    (47/35, -(66*x(a)+7)/7, -1, (268-275*x(a))/7).      (30)

This is a cross-table calibration only, not one target for different games.
The actual consumer declarations inspected are the two contracting endpoint
compilers in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
named in Section4. The new raw producer is ordinary mathematics only.

### 12.5 Exact rational positive test and scale distinction

Choose

    a=2267/49,    x=1/2,    c=33/35,
    y=7,         z=496/33.                              (31)

All four equations(26) are exactly zero. In variables(c,z,y,x), their
Jacobian is

    [-35,       0,       0,          0;
     595/66,    33/70,   0,          192/35;
     0,         0,       1/2,       -4;
     5133/28,   0,      -2267/1715, -10109/245],

whose determinant is2933667/6860, not zero. This provides an exact finite
calibration of the macroscopic asymptotic branch without decimal search.

For comparison the all-small ansatz q=M^-1*w, with ALL w_i>0 fixed, has
limiting equations

    Gamma*w=e1*w0*w2+e2*w1*w3-a*e3*w0*w1.

Put r=w3/w2>0, Y=w2 and C=3+3*r/2. Rows0,1 give
w1=C*Y and w0=4*(1+r)*Y/(1+Y). Row3 then requires

    Y*[2+9*r/2-4*a*(1+r)*C]=10+15*r/2.                (32)

For a>=1/4 the bracket on the left is at most-1-3*r^2/2<0,
while the right side is positive. There is NO positive finite root of this
all-small leading field. This excludes that specific interior scale, not
every stationary equilibrium or every possible multiscale branch. In
particular it is consistent with the actual macroscopic producer(25).

### 12.6 Whole sure-owner test and exact remaining questions

The whole sure-owner exclusion of Section10 survives for every a>=0 at
this exact raw center and every M>0. First force the sure owner's opposite
player to Continue. Neither negative opposite-pair pole is passive for that
player on a possible opponent coalition. The additional pole is POSITIVE,
so it can only strengthen Continue. Then both negative opposite pairs are
impossible. Every nonsuccessor strictly Continues, the successor surely
Joins for40 rather than a singleton<=17, and the owner strictly prefers
withdrawing from-1 to a singleton>=4. This covers ALL free-player root
probabilities and ALL continuation vectors, not just pure equilibria.

The other Section6 screens involving only singleton data, recipient-present
pairs, triples or the grand row are unchanged. No new complete source census
is claimed from that observation, and no unknown pointwise thick threshold
or unknown IFT radius is excluded. Separate whole-source admission remains
pending.

Concrete requested check: independently falsify the exact pole cancellation,
the scalar branch including a=0, the Jacobian elimination, the compact-local
quantifiers and the unrestricted behavioral consumer. A next mathematical
question is whether macroscopic boundary balances admit a more general
raw-data producer beyond this explicit three-pole region; this note does
not treat that open generalization as a premise of the theorem draft.

## 13. A global raw-endpoint producer without a singleton-matrix condition

Status: NEW COMPLETE ORDINARY PROOF DRAFT, independently unreviewed.
This is a direct four-player raw-table class, not a verifier for a strategic
witness. It generalizes Section12 by removing the local tube at the bounded
coordinates; no invertibility, degree, inverse sign or singleton normalization
is required. Its hypotheses are eight finite strict inequalities.

### 13.1 Finite input and exact theorem

There are four players0,1,2,3. Continue dates and perpetual Never pay0.
Each live date uses independent private coins, and a deviation may replace
one player's ENTIRE behavioral strategy. Fix arbitrary finite raw rewards
at all coordinates EXCEPT the following three passive coordinates:

    r1(02)=-beta1*M+e1,
    r2(13)=-beta2*M+e2,
    r3(01)=a*M+e3,                                      (33)

where beta1,beta2>0, a>=0, and M tends to infinity. Here e1,e2,e3 are
arbitrary bounded residuals. Every other57 reward coordinate is fixed raw
input. No own-singleton sign condition is imposed.

Define the following numbers from the FIXED coordinates only:

    A0=r0(03)-r0(3),      B0=r0(023)-r0(23).

Require A0>0>B0 and put

    c=A0/(A0-B0) in(0,1).

Next put

    A2=r2(23)-r2(3),      B2=r2(023)-r2(03),
    L0=(1-c)*(r1(13)-r1(3)) +c*(r1(123)-r1(23)),
    L1=(1-c)*(r1(013)-r1(03))+c*(r1(0123)-r1(023)).

Require A2<0, B2<0, L0<0 and L1<0. Finally define the quadratic

    Q(x)=(1-x)*(1-c)*r3(3)+x*(1-c)*r3(03)
             +(1-x)*c*r3(23)+x*c*r3(023),
    W(x)=x*(1-c)*r3(0)+(1-x)*c*r3(2)+x*c*r3(02),
    F(x)=(c+(1-c)*x)*Q(x)-W(x).                       (34)

The last two strict inequalities are

    F(0)=c*((1-c)*r3(3)+c*r3(23)-r3(2))>0,
    F(1)=(1-c)*(r3(03)-r3(0))
                    +c*(r3(023)-r3(02))<0.            (35)

All eight conditions are explicit inequalities on the57 fixed coordinates.
No coordinate in(33) appears in them.

**Theorem draft.** For EVERY such input, EVERY fixed a>=0 and EVERY finite
residual bound R, there is M0 such that ALL M>M0 and ALL |e1|,|e2|,|e3|<=R
have an all-interior stationary FULL terminal Nash equilibrium. Its actual
payoff is a uniform-equilibrium target delivered by the SAME profile against
ALL complete behavioral replacements over all sufficiently long horizons.
The threshold and the constructed branch are uniform on compact sets of the
57 raw coordinates, beta1,beta2 and a that preserve the eight strict
inequalities and beta1,beta2>0. Own singleton coordinates are part of that
compact raw data, not an implicitly unbounded shift.

In particular the arbitrary singleton rows may be singular, non-R0, or of
any degree. This theorem does not require changing or normalizing them.
It is a reward-class producer, not a transformation of every fixed game
into this class.

### 13.2 Literal limiting equations and triangular elimination

Use t=1/M and q=(x,t*y,c',1-t*z). Exact raw opponent-set enumeration gives
a POLYNOMIAL system in t,x,y,c',z: each large reward in(33) is multiplied
by a probability divisible by t. At t=0 its equations are

    H0=(1-c')*A0+c'*B0,
    H1=(1-x)*L0(c')+x*L1(c')+beta1*x*c'*z,
    H2=(1-x)*A2+x*B2+beta2*y*(1-x),
    H3=F(x,c')-a*x*y*(1-c').                           (36)

Here L0(c'),L1(c') and F(x,c') are the displayed raw formulas with c
replaced by c'. No continuation annotation has been substituted for the
actual stationary payoff. The selected bounded residuals contribute only
terms divisible by t. The zero in(36) forces c'=c and then

    y(x)=[-A2-x*B2/(1-x)]/beta2>0,
    z(x)=-[(1-x)*L0+x*L1]/(beta1*x*c)>0.              (37)

Both formulas are valid for EVERY0<x<1. Let

    D(x)=x*y(x)*(1-c)>0.

The only remaining equation is F(x)-a*D(x)=0.

### 13.3 The quadratic ratio lemma

**Elementary lemma.** Suppose F is a real polynomial of degree at most2,
F(0)>0 and F(1)<0. Let b,d,K be positive and put

    D(x)=K*x*[b+d*x/(1-x)],        0<x<1.

There is exactly one zero x_star of F in(0,1), it is simple and has
F'(x_star)<0. On(0,x_star) the ratio F(x)/D(x) is strictly decreasing,
with derivative STRICTLY negative, from infinity to0. The same nonzero
derivative holds at x_star.

Proof. Opposite endpoint signs give a zero, and a quadratic cannot have
two zeros in(0,1) while reversing sign between the endpoints. A double
zero cannot reverse sign. Hence F is positive before its unique root and
F'(x_star)<0. Write F=h0+h1*x+h2*x^2, with h0>0. If h2<=0 then

    (F(x)/x)'=-h0/x^2+h2<0,
    (D(x)/x)'=K*d/(1-x)^2>0.

Both quotients are positive before x_star, so their ratio has strictly
negative derivative. If h2>0 then F' is increasing and
F'(x)<F'(x_star)<0 for x<x_star; also D'>0. Again the ratio has strictly
negative derivative. At x_star its derivative is F'(x_star)/D(x_star)<0.
The limits follow from F(0)>0,D(x)~K*b*x near0 and F(x_star)=0. This
argument does NOT assume F itself decreases when h2<=0: a concave quadratic
may initially increase. For example F=1+10x-12x^2 still satisfies the lemma.

Apply the lemma with

    b=-A2>0, d=-B2>0, K=(1-c)/beta2>0.

For EVERY a>0 there is a UNIQUE x(a) in(0,x_star) satisfying a=F(x)/D(x).
At a=0 take x=x_star. Thus all of x,c,y,z are produced from the raw input,
with no root or strategic continuation supplied. They are smooth locally
in the raw parameters, including a=0, and stay in positive compact ranges
over compact admissible parameter sets and bounded a.

### 13.4 Automatic full Jacobian and actual equilibrium

Order unknowns(c',z,y,x) in(36). Successive eliminations have pivots

    B0-A0<0,    beta1*x*c>0,    beta2*(1-x)>0.

After those three eliminations the fourth pivot is

    d/dx [F(x)-a*D(x)]
       =D(x)*d/dx[F(x)/D(x)]<0                        (38)

at the selected root. Thus the complete limiting Jacobian is nonsingular
AUTOMATICALLY. The exact polynomial IFT gives an actual zero H=0 for all
sufficiently small positive t, with q0,q2 strictly between0 and1, q1=t*y>0
and q3=1-t*z<1. Positivity and the remaining strict inequalities persist.
Uniformity over compact admissible raw data and bounded residuals follows
by a finite compact-parameter IFT cover. This is a producer, not an IFT
whose required root or nonsingularity is itself an input assumption.

All four produced hazards are interior, so each player has a contracting
opponent. The equation H_i=0 gives Q_i=B_i/(1-alpha_i), which is its actual
terminal payoff. Every pure finite deadline AND Never earns exactly that
value. Their independent private mixtures exhaust the allowed complete
behavioral replacements. Thus the root is full terminal Nash even for
arbitrary signed own and terminal rewards. For each FIXED table the
geometric opponent absorption bound yields the SAME-profile uniform
equilibrium at that actual fixed target, exactly as in Section4. Large
rewards do not need an M-uniform horizon threshold.

### 13.5 Exact stress tests and remaining scope

The complete raw center in Section12 satisfies all eight conditions:

    A0=33, B0=-2, c=33/35,
    A2=-5, B2=-2,
    L0=-96/35, L1=-80/7,
    F(x)=(4917-5025*x-550*x^2)/245.

It recovers the reviewed rational calibration(31) and its exact determinant.
Its WHOLE sure-owner exclusion remains valid for every a>=0, as already
proved in Section12.6. Relevant unchanged bounded singleton/child screens
are not being promoted to a completed new whole-source census.

The endpoint assumptions have an actual role. If Q(x)=0 and W(x)>0 on
(0,1), then F<0 and the last equation in(36) has NO solution for a>=0,
since D>0. Thus a universal boundary-scale root without an endpoint sign
condition is false, even though such a table may have other equilibria.
Likewise the local-coefficient tube in Section12 is not being silently
upgraded to arbitrary data: it is replaced by the explicit guards(35)
and the six preceding strict inequalities.

Concrete next requested check: independently falsify the general raw
enumeration(36), the quadratic-ratio lemma when F initially increases,
the automatic Schur pivots including a=0, and compact-data/full-agency
quantifiers. The fixed-center review of Section12 is not yet a review of
this broader raw theorem. Whole reward-source admission remains separate.
