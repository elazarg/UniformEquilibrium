# Two opposite field poles and a projective interval

Admission status: INTERNAL ONLY; BOTH fixture generations are already covered.
The producer proof and membership/mixed-size extension have independent
ordinary checks. The earlier determinant63 fixtures were covered by the
passive-row triple producer. The replacement determinant49 matrix fails all
four deleted inverse tests, but its actual R0 degree is-1, not1, so the
implemented nonunit-degree source covers EVERY collision completion. Its
claimed triple-root index contained an orientation error, independently
confirmed after reopening the actual degree declaration. No export is
authorized and no new reward-class coverage is claimed for these fixtures.

This is an ordinary mathematical raw-table producer, not a Lean-checked
theorem. It gives an actual all-interior stationary terminal Nash profile and
a same-profile uniform-equilibrium payoff. A scalar interval selects the
angular parameter after the radial and transverse equations are solved; no
inverse column need have a uniform sign. Selected recipients may be absent
from their selected coalitions, and the two coalitions may have different
sizes. Section6 gives exact raw Fin4 data outside the named inverse-column,
projective-Q-bar, sure-owner, quiet-child, weighted-upper and boxed-charge
hypotheses. These are bounded comparisons, not an exhaustive census or a
solution of arbitrary Fin4 existence.

## 1. Self-contained question and raw-data theorem

Let I be a finite player set, n=|I|>=2. Every nonempty first-quitting
coalition S absorbs at a finite reward vector r(S). Live dates and perpetual
continuation pay0. Randomization is private and independent. A complete
unilateral replacement may be any behavioral strategy, including every finite
deadline and Never. All payoffs below are expected payoffs.

Fix arbitrary singleton entries and define

    s_i=r_i({i}),    Gamma_ii=0,
    Gamma_ij=r_i({j})-s_i for j!=i.

Assume Gamma is invertible. Select distinct recipients a,b and ANY coalitions
S_a,S_b with |S_i|=d_i+1>=2. A selected recipient need not belong to its
selected coalition; the coalitions may coincide or have different sizes.
Select coefficients A,B>0. Define epsilon_i=1 if i in S_i and epsilon_i=-1
otherwise, for i=a,b. Put

    u=Gamma^-1 e_a,       w=Gamma^-1 e_b,
    v(x)=u-x*w,
    P_i(z)=(sum_(j!=i)z_j)*product_(j in S_i\{i})z_j, if i in S_i,
    P_i(z)=product_(j in S_i)z_j,                     if i notin S_i,
    G(x)=x-B*[A*P_a(v(x))]^(-d_b/d_a)*P_b(v(x)).       (1)

Each P_i is positive on the positive orthant and homogeneous of degree
d_i+1. If d_a=d_b=d, the scalar simplifies to
G=x-(B/A)*P_b(v)/P_a(v).

Assume there are explicit numbers 0<l<r for which v(x) is coordinatewise
strictly positive on [l,r], and

    G(l)*G(r)<0.                                       (2)

These are finite singleton/coefficient inequalities, not strategic witnesses.
Since v is affine, its positivity is tested just at the two endpoints. Each
P_i is positive there and throughout the interval. The inequality(2) can be
checked directly from finite singleton/coefficient data. In the equal-degree
case they can be checked after multiplying by positive endpoint denominators.

**Theorem.** For every finite R>=0 there is L0<infinity such that
for every L>L0 and EVERY original raw reward table with these singleton
entries and

    r_a(S_a)= epsilon_a*A*L^d_a+c_a,
    r_b(S_b)=-epsilon_b*B*L^d_b+c_b,
    |c_a|,|c_b|<=R,
    |r_i(S)|<=R for every OTHER nonsingleton coordinate(S,i),    (3)

there is an independent stationary profile with all hazards in(0,1) which is
exact terminal Nash against every complete unilateral behavioral replacement.
Its actual terminal payoff is a uniform-equilibrium payoff; the SAME profile
works for every accuracy over all sufficiently long finite horizons.

The selected terms have opposite FIELD signs; their raw reward signs need
not be opposite. No sign assumption is imposed on own singleton rewards or
on any bounded coordinate. No sign assumption is imposed on any inverse
column. The theorem is uniform over compact sets of the displayed
singleton/coefficient/bracket
data on which invertibility, endpoint positivity and the strict opposite
signs are retained, with labels and selected coalitions fixed.

For fixed singleton/coefficient/bracket data there are also kappa>0 and L1
such that all residual bounds R in(3) may simultaneously be replaced by
kappa*L, provided L>L1. This scale-thick conclusion is proved in
Section4; no asymptotic payoff formula is claimed uniformly on that larger
region.

## 2. Exact pole cancellation, not a formal expansion

For stationary hazards q define the literal endpoints

    Q_i(q)=sum_(T subset I\{i}) r_i(T union{i})
                 product_(j in T)q_j product_(j outside T union{i})(1-q_j),
    B_i(q)=sum_(nonempty T subset I\{i}) r_i(T)
                 product_(j in T)q_j product_(j outside T union{i})(1-q_j),
    alpha_i=product_(j!=i)(1-q_j),
    H_i(q)=(1-alpha_i)*Q_i(q)-B_i(q).              (4)

Set t=1/L and q=t*z. Let sign_a=1, sign_b=-1 and C_a=A,C_b=B. A selected
pole affects only its recipient's payoff. If i in S_i, its raw coefficient
is sign_i*C_i*t^(-d_i), it enters Q_i only, and its term in H_i is exactly

    (1-product_(j!=i)(1-t*z_j)) * sign_i*C_i*t^(-d_i)
      * product_(j in S_i\{i})(t*z_j)
      * product_(j outside S_i)(1-t*z_j).

If i notin S_i, its raw coefficient is -sign_i*C_i*t^(-d_i) and it enters
B_i only. Because H_i subtracts B_i, its term in H_i is instead

    sign_i*C_i*t^(-d_i) * product_(j in S_i)(t*z_j)
      * product_(j outside S_i union{i})(1-t*z_j).

In EITHER case division by t gives a polynomial in(t,z), whose constant
term is sign_i*C_i*P_i(z). All bounded nonsingleton contributions to H have degree
at least2 in q. The singleton contribution at degree1 is -Gamma*z.
Consequently H(t*z)/t has the EXACT polynomial extension

    Phi(t,z)=A*P_a(z)*e_a-B*P_b(z)*e_b-Gamma*z+t*E(t,z,c),       (5)

where c denotes all bounded residual data and E is polynomial. On every
fixed compact set of(t,z,c), E and all its derivatives are uniformly bounded.
The pole terms contribute only nonnegative powers of t; no cancellation of
an uncontrolled remainder is being assumed.

## 3. Solve the transverse and radial equations, then one scalar equation

Let C=I\{a,b}. Introduce coordinates h,x,y with h>0, x in[l,r],
y in R^C, by

    z=Gamma^-1(h*e_a-h*x*e_b+sum_(j in C)y_j*e_j).       (6)

At y=0 this is h*v(x)>0. Define the explicit positive continuous branch

    h0(x)=[A*P_a(v(x))]^(-1/d_a).                      (7)

At t=0,y=0,h=h0(x), all coordinates Phi_j with j in C vanish, and
Phi_a=A*h^(d_a+1)*P_a(v(x))-h=0. Consider precisely these n-1 equations,
not yet the b equation, as equations for(h,y). At this branch their
Jacobian has block form

    [ d_a     * ]
    [ 0      -Id_C ].                                  (8)

Indeed the transverse equations are exactly -y_j at t=0, and the h
derivative of the a equation at its positive root is
(d_a+1)*A*h0^d_a*P_a(v)-1=d_a. Thus(8) is nonsingular, including when C is empty.

The uniform parameter implicit-function theorem on the compact interval
[l,r] and compact residual box produces continuous functions

    h(t,x,c)>0,       y(t,x,c),

for all sufficiently small |t|, with

    h(t,x,c)->h0(x),     y(t,x,c)->0 uniformly in(x,c),   (9)

and with all n-1 selected equations zero. The compact-parameter version
here follows from the ordinary local theorem: the zero branch(7) is compact,
the inverse matrices(8) are uniformly bounded, and a common tubular
contraction neighborhood gives existence and uniqueness near that branch.
Local solutions on overlapping parameter charts therefore agree. There is
no asserted uniqueness of the remaining angular root.

Define the remaining continuous scalar residual

    g_t(x,c)=Phi_b(t,z(t,x,c))/h(t,x,c).

At t=0, using(7),

    g_0=x-B*h0^d_b*P_b(v)
       =x-B*[A*P_a(v)]^(-d_b/d_a)*P_b(v)=G(x).         (10)

The convergence to G is uniform on the whole parameter rectangle. The two
strict opposite endpoint signs in(2) persist for sufficiently small positive
t. The intermediate-value theorem gives an x(t,c) in(l,r) with g_t=0.
Equation(9) and the positive minimum of h0*v on the compact interval ensure
that the resulting z is coordinatewise positive and uniformly bounded.
After decreasing t, q=t*z belongs to(0,1)^I and Phi=0, hence H(q)=0.

This completes the actual finite-parameter root producer. It uses no
convexification of independent law sets, no random selection of correlated
profiles, no supplied equilibrium and no nonsingular-angular-root premise.

## 4. Scale-thick residuals

Write each bounded nonsingleton residual coordinate as e/t. In H/t each
such residual multiplies a monomial of degree at least2 in q before the
division, so after q=t*z the resulting t exponent is nonnegative. This
includes each selected residual c_i: its lowest exponent is d_i-1>=0,
whether its recipient belongs to its coalition or not.
The extended field is therefore polynomial in(t,z,e), and at(t,e)=(0,0)
its branch and transverse/radial Jacobian are exactly(7)-(8).

Use e as an additional small parameter. A common kappa-neighborhood of e=0
retains positivity, the inverse bound, and both strict scalar endpoint signs.
The same n-1 equation solver and IVT produce H=0 for all |e|<=kappa and
all sufficiently small positive t. This proves the stronger bounds in
Section1, including d_i=1, when some residual e terms survive at t=0 but
vanish at e=0. The argument does not replace e by an uncontrolled parameter.

## 5. Complete behavioral caps and same-profile uniform payoff

At the produced hazards, all opponents of every i have positive hazards, so
0<=alpha_i<1. Equation H_i=0 gives B_i=(1-alpha_i)*Q_i. A unilateral
pure finite deadline t receives

    B_i*(1+alpha_i+...+alpha_i^(t-1))+alpha_i^t*Q_i=Q_i.

Never receives B_i/(1-alpha_i)=Q_i as well. A behavioral strategy on the
unique live continuation history induces an arbitrary private stopping law
on N union{Never}; integrating these constant pure-clock payoffs gives Q_i.
The prescribed stationary law also earns Q_i. Thus ALL complete replacements
are indifferent, without any payoff-sign restriction.

For a fixed resulting table let Rtable bound its finite rewards. Under any
unilateral deviation by i, absorption is no later than the first opponent
quit, whose tail is alpha_i^t. Hence terminal payoff versus N-date average
payoff differs by at most 2*Rtable/[N*(1-alpha_i)], uniformly in the entire
replacement law. The analogous bound holds for prescribed play. Therefore
the SAME fixed profile has vanishing finite-average regret and its finite
average payoff tends to its actual terminal payoff. This proves precisely
the uniform-payoff claim, not merely a terminal-equilibrium surrogate.

An exact small calibration is the two-player matrix

    Gamma=[0,a;-b,0],       a,b>0.

Take S_0=S_1={0,1}, positive pair reward A*M+c0 for0 and negative pair
reward -B*M+c1 for1. Then(1) has v=(x/b,1/a)>0 and
G=x-(B/A)*a^2*x^2/b^2, with an ordinary positive sign-changing root.
Here d_a=d_b=1 and L=M. The actual field has the exact interior solution

    q1=a/(A*M+c0-s0),       q0=b/(B*M-c1+s1)

for all sufficiently large M. This verifies the scaling q~M^-1 and the
opposite-sign ordering directly. It is only a solved-game calibration.

The positive-cone hypothesis is substantive. For the two-player comparison
matrix Gamma=[0,1;1,0], own singletons1, and selected pair rewards(M,-M),
the second recipient's actual field is

    H_1=q0*[(-M-1)*q0-1]<0 whenever q0>0 and M>0.

There is no all-interior stationary endpoint Nash profile. Correspondingly,
Gamma^-1*e0-x*Gamma^-1*e1=(-x,1) is never positive for x>0. This is a
negative test of dropping a source hypothesis, not a no-UE example. Strict
opposite endpoint signs likewise cannot be replaced by an assertion that an
unspecified scalar stationary point or a same-signed endpoint pair suffices.

## 6. Exact four-active fixtures and bounded source comparisons

The replacement fixtures in this section are already covered by nonunit degree.
The earlier determinant63 calibration was covered by a passive-row child
producer; its complete data and containment are preserved in the author's
internal research record. That failed comparison is not counted as new coverage.

Choose own singleton rewards1 and the comparison matrix

    Gamma=[0,-1,-1,3;-3,0,4,-2;-3,-3,0,2;-4,-1,1,0],
    det Gamma=49,
    Gamma^-1=(1/49)[-2,5,8,-22;20,-1,-31,24;12,19,1,-15;27,6,-10,3].

EVERY inverse column has both strict signs. Thus neither a signed one-column
nor a full-positive/signed-inverse producer applies for any selected recipient
or sign. Relabeling and positive playerwise finite-terminal affine changes
only permute inverse rows/columns and multiply columns by positive factors.
No strategic equivalence of arbitrary finite-terminal shifts at Never is used.

Take a=1,b=2,S_a=S_b=I,d_a=d_b=3,A=B=1 and L=M^(1/3). Then

    v(x)=(5-8*x,31*x-1,19-x,6+10*x)/49,
    v(x)>0 for 1/31<x<5/8,
    G(x)=(x^3+1034*x^2-293*x-10)/[(x-19)*(x+30)].

Use l=3/10 and r=8/25. The positive endpoint vectors and exact signs are

    v(l)=(13/245,83/490,187/490,9/49),
    v(r)=(61/1225,223/1225,467/1225,46/245),
    G(l)=4813/566610>0,       G(r)=-16831/4424825<0.     (11)

These raw data produce actual all-interior stationary terminal Nash/UE for
every sufficiently large M, uniformly over all bounded residual completions.

One full completion is

    0:(1,-2,-2,-3), 1:(0,1,-2,0),
    2:(0,5,1,2), 3:(4,-1,3,1),
    01:(-4,12,1,1), 12:(1,-4,12,1),
    23:(1,1,-4,16), 03:(18,1,1,-4),
    02:(-4,1,-4,1), 13:(1,-4,1,-4),
    012:(-4,-4,-4,1), 013:(-4,-4,1,-4),
    023:(-4,1,-4,-4), 123:(1,-4,-4,-4),
    I:(-10,M,-M,-13).                                  (12)

All nonselected nonsingleton coordinates are bounded by18. Each directed
pair{i,i+1} pays-4 to donor i and r_(i+1)({i})+14 to its successor.
Passive nonsingleton rewards are1; the smallest passive singleton is-3.

### 6.1 Complete singleton and all-deletion screens

Every column has a strictly negative off-diagonal entry, and every principal
block on at least two labels is nonsingular. A nonzero homogeneous
complementary vector cannot have support of size>=2 because its invertible
active block would annihilate that support; singleton support is blocked
by its negative external column entry. Thus Gamma is R0.

At offset ones there are exactly THREE regular complementarity roots:

    support empty: z=0, residual=ones, index+1;
    support02: z0=1/3,z2=1, residual=(0,4,0,2/3), index-1;
    support123: z1=2,z2=1,z3=5/2, residual=(11/2,0,0,0), index-1.

Every other support is excluded exactly by its active-system candidate
z_C=-Gamma_CC^-1*ones and residual F=ones+Gamma_.C*z_C:

    C       det Gamma_CC     failed coordinate
    01      -3               F2=-3
    03      12               z3=-1/3
    12      12               z2=-1/4
    13      -2               F2=-1
    23      -2               z2=-1
    012      3               z0=-11/3
    013      1               z1=-11
    023     -1               z0=-1
    I       49               z1=-12/49.

Singleton supports require1=0. The two remaining principal determinants
are det Gamma_02=-3 and det Gamma_123=-2, as used by the two nonempty root
indices. All inactive inequalities at those roots are strict. The canonical
R0 degree is therefore1-1-1=-1. The actual index is the sign of the active
principal determinant, with NO extra(-1)^cardinality. This is exactly
`IsStandardLCPSolution.exists_box_localDegree_eq_sign_det` in
`MathUE/LinearProgramming/LocalDegree.lean`. Consequently
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
already covers every collision completion of this singleton matrix. The
remaining screens below retain correct comparisons but establish no admission.

Every ROW has a distinct negative blocker. Recursive normal-core deletion
retains all four players; nonzero R0 degree makes the full matrix standard-Q.
Thus the ordinary non-Q NORMAL-CORE producer is unavailable. The exact source
facts are `normalCore_eq_univ_of_fixed_blocker` in
`UniformEquilibrium/Quitting/Classification/LCP/ElementaryMatrixObstructions.lean`
and `Math.LinearProgramming.isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`.

Projective Q-bar fails on pair01, whose matrix is[0,-1;-3,0]. At projective
offset(-1,-1), nonnegative cemetery c and singleton masses x,y would require
-c-y>=0 and -c-3*x>=0. This forces c=x=y=0, contradicting normalization.

Critically, the implemented PASSIVE-ROW TRIPLE lift fails on ALL FOUR
deletions, not merely on an arbitrarily chosen child. In natural increasing
child order the four actual child inverses are

    delete0: [1,1,-4;1,1,-3;3/2,2,-6],
    delete1: [2,-3,2;8,-12,9;3,-4,3],
    delete2: [-2,-3,2;8,12,-9;3,4,-3],
    delete3: [4,1,-4/3;-4,-1,1;3,1,-1].

Each has a strictly negative entry, so NONE satisfies even the nonnegative
inverse prerequisite, independently of the outside-row weights. This checks
the entire three-player-child selection in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`,
not a universal-debt bound substituted for its selected singleton-cycle input.
The declaration is in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

For both signed once-per-owner four-cycle branches, column0 is strictly
negative off its diagonal. Whichever player has0 as predecessor therefore
violates the positive predecessor requirement, under every cyclic relabeling.
The cyclic open-sign producer also fails: it requires exactly one negative
off-diagonal entry per row, whereas every row here has TWO. This is a literal
failure of `QuittingCyclicSingletonOpenSignData.first_neg/later_nonneg` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`.

The raw cyclic-child resonance family has no admissible pivot either.
Only columns0 and1 have all three negative off-diagonal entries, as required
by its positive harm input. In child123 and child023 respectively the
strictly positive directed graph contains no three-cycle: in each, two
vertices point only at the same last vertex, and the latter points back to
one of them. Thus the required positive cyclic child entries cannot be
supplied. The relevant literal definition is `CyclicChildSingleton.RawRows`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`.

### 6.2 Whole sure-owner and quiet-child selections

For M>=4 there is NO root Nash with any sure quitter, whatever continuation
is supplied. Given sure i, each nonsuccessor j other than the positive grand
recipient1 gets at most-4 when joining, at every containing coalition, whereas
Continue receives at least-3. One such nonsuccessor exists and must Continue,
making the grand coalition impossible. The other nonsuccessor, even if it
is1, then strictly Continues as well. The successor gains14 by joining the
owner's singleton. The owner receives-4 but can withdraw to its passive
singleton at that successor, >=-3. This contradicts Nash and excludes EVERY
sure-owner or persistent nonempty-base/free-set root selection.

Every nonempty proper child C has an unsafe EXACT child Nash witness.
Choose d in C with d+1 outside C; only d Quits0, all other child members
Never. The owner earns1 rather than Never0. Any other child member gets its
passive singleton>=-3, whereas joining gives-4; every later replacement
leaves the already absorbed outcome unchanged. All child full debts and joint
Never mass are0. The absent successor gains14. This falsifies all universal
all-outsider bounds by child debts plus finite Never slack. It does NOT by
itself falsify a SELECTIVE singleton-cycle lift; that distinct source is
excluded by the explicit all-deletion inverse calculation above.

### 6.3 Whole weight, guard and quotient selections

The only premium trap is I. In a proper coalition each player's only
above-own participant reward is at its incoming directed pair, so a proper
trap would be closed under the predecessor four-cycle, which is impossible.

For every nonzero nonnegative weight w, define the literal inserted upper
test H_w(S)=sum_i w_i[r_i(S union{i})-s_i]. Summing the four singleton tests
and the four actual outsider INSERTION-leave tests gives respectively

    sum_d H_w({d})=7*w0+w1+w2+5*w3>0,
    sum_d sum_i w_i[r_i({d,i})-r_i({d})]
       =6*w0+2*w1+5*w2+9*w3>0.                        (13)

The unweighted singleton outsider charges are(1,1,5,7), all strictly
positive. Thus the ENTIRE upper-average weight set, including zero entries,
fails, and the strictly negative boxed singleton-charge row fails regardless
of every auxiliary threshold or box. There is no alternative trap selection.

The four directed-pair weighted PARTICIPANT premiums sum to
12*w0+6*w1+6*w2+10*w3>0. A GLOBAL NONNEGATIVE inserted floor fails at123,
whose vector is(-11,-5,-5,-5). These own-, passive- and participant-subtraction
conditions are different conditions and are not conflated.

Each player has an incoming above-own pair and an outgoing donor reward-4<1.
Both participant-at-most-own protection and participant-at-least-own common
leaver conditions fail for EVERY player. Every pair has a participant-4<1,
excluding both-above-own joint-pair raw sources for every choice. Every
triple has a negative ordered pair join, excluding the six-positive-join
triple-singleton raw condition.

For ANY owner i and selected partner p choose
j in{i+1,i+2} different from p. At its sole-sure row and zero partner hazard,
the literal owner displacement is

    H_i=r_i({i,j})-r_i({j})=-4-r_i({j})<=-1<0.         (14)

This violates even the WEAK lower face for every ordered pair and every
height, hence also each stricter polynomial/raw-unit/half guard. It is an
actual face failure, not only a sufficient-coefficient screen.

Each singleton row now has one positive favorite, but no MATCHING can
supply them: row0 forces partner3, whereas row3's positive favorite is2,
not0. The participant cross-cap also fails for every matching, since four
positive incoming directed edges cannot all fit in two disjoint pairs.
For M>13 the all-sure response differences(-11,M-1,-M-1,-14) are pairwise
distinct, excluding every nontrivial actual response-invariant quotient.

### 6.4 Exact declarations and named raw statements inspected

The following are source definitions or existing results, not claims that this
new producer is Lean checked:

- `quittingSingletonMatrix`, in
  `UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`;
- `IsProjectiveQBarMatrix` and
  `isProjectiveQMatrix_iff_standard_or_homogeneous`, in
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`;
- `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one`, in
  `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`;
- `normalCore_eq_univ_of_fixed_blocker`, in
  `UniformEquilibrium/Quitting/Classification/LCP/ElementaryMatrixObstructions.lean`,
  and `Math.LinearProgramming.isStandardQ_of_r0Degree_ne_zero`, in
  `MathUE/LinearProgramming/R0Degree.lean`;
- `SignedFourCycleSingletonData` and `StrictTests`, in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`;
- `Math.SignedFourCycleCoefficients.LargerBranchTests`, in
  `MathUE/SignedFourCycleLargerEigenvalue.lean`, and the raw statement
  `LARGER_EIGENVALUE_SIGNED_FOUR_CYCLE_UNIFORM_PAYOFF.md`;
- `HasBoxedQuittingNashCharges`, in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`,
  and raw statements `BOXED_NASH_CHARGES_UNIFORM_EQUILIBRIUM.md` and
  `MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md`;
- `IsCommonQuittingPremiumLeaver`, in
  `UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`;
- `exists_uniformPayoff_of_persistentBase_inducedNash_signs`, in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`,
  and `DeadlineWithdrawalRewardCertificate`, in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`;
- `QuittingCrossedSourceGuards`, in
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`,
  and `QuittingOneSidedWeakUnitGuards`, in
  `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`;
- named raw statements `SIGNED_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM.md`,
  `CROSSED_MATCHING_UNIFORM_EQUILIBRIUM.md`,
  `TRIPLE_SINGLETON_COLLISION_BOX_UNIFORM_EQUILIBRIUM.md`,
  `CYCLIC_CHILD_WITH_ONE_JOINT_PHASE.md`, and
  `GLOBAL_TWO_JOINT_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`.

The source comparisons are bounded named comparisons. No claim is made to
exclude unknown radii of unrelated local IFT neighborhoods merely by comparing
centers. There is no omitted strategic input to the displayed producer.


### 6.5 Two negative raw poles

The same matrix supports two negative RAW poles of opposite FIELD sign.
Retain all singleton, pair and bounded triple rows of(12), but set

    S_a=S_b=023,       a=1, b=2,
    r1(023)=-7*M,      r2(023)=-2*M,
    r0(023)=r3(023)=-4,
    grand=(-10,-11,-12,-13).                           (15)

Take L=M^(1/2),d_a=d_b=2,A=7,B=2. Recipient1 is absent and2 is present.
Then

    P_a=z0*z2*z3,       P_b=(z0+z1+z3)*z0*z3,
    G=x-(2/7)*(10+33*x)/(19-x)
     =(7*x^2-67*x+20)/[7*(x-19)],
    G(3/10)=-53/13090<0,
    G(8/25)=452/81725>0.                              (16)

The SAME positive v interval supplies the actual producer, with both growing
original rewards negative. All singleton and all-deletion tests remain
unchanged. The pair/weight/floor/guard tests also remain unchanged, and the
unsafe child witnesses still use only singleton and pair rows.

The sure-owner proof needs explicit erasure of the passive penalty. A
nonsuccessor j!=1 still strictly Continues: its join reward is<=-4 for
M>=4 and its passive rewards are>=-3. One such j exists and belongs to023.
Its Continue makes023 impossible, so any remaining nonsuccessor1 likewise
Continues without facing the passive penalty. The successor joins with
gain14 and the owner withdraws from-4 to its singleton>=-3. No sure-owner
root Nash has been introduced.

The actual all-sure response differences are(-11,7*M-11,-13,-14), not
grand minus own singleton. They remain pairwise distinct for M>=4. This
checks the changed withdrawal reward rather than silently reusing the old
grand residual. The all-deletion inverse failures exclude the previously
missed passive-row source on this entire second family as well.

## 7. Narrow formalization handoff

The required actual-data adapter takes the finite reward table, its singleton
comparison matrix, two recipient/coalition labels, A,B, and the explicit
positive interval inequalities(1)-(2). It must construct the exact canceled
polynomial(5), the compact partial solver(6)-(9), one angular root by IVT,
and the actual interior stationary hazards. A structure field asserting
existence of that root or of a Nash profile would not implement the producer.

The main new analytic lemma is the compact-parameter partial implicit solver
with an invertible transverse/radial block(8), followed by the continuous
scalar sign selection. Mixed sizes and absent recipients change only the
polynomials, radial exponent and scalar in the displayed formulas; do not
replace their distinct raw signs by an unproved utility transformation.

Existing tracked semantic consumers are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`, in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`. The produced
H=0 supplies endpoint Nash, the stationary numerator gives its fixed point,
and all-positive opponent hazards supply every deleted-opponent contraction.
Section5 proves the complete behavioral and Never content directly, so no
stationary-response restriction is left for a downstream assumption.
