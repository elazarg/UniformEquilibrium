# A negative opposite chord in a four-player singleton cycle

## Exact reward-class theorem

Let I={0,1,2,3}. A quitting game assigns an arbitrary finite real vector
r(S) to every nonempty coalition S. Each live date the players independently
choose Continue or Quit using private randomness and the observed history.
The first nonempty quitting coalition absorbs; live and literal Never
payoffs are zero. Every unilateral behavioral replacement is allowed.
Put s_i=r_i({i}), Gamma_ii=0, and Gamma_ij=r_i({j})-s_i for i!=j.

Suppose, after relabeling, the four cyclic adjacent pairs satisfy

    Gamma_(j+1),j<=0<=Gamma_j,(j+1)  for j modulo4,

the opposite pair02 satisfies Gamma_02<=0 and Gamma_20<=0, and the
other opposite pair satisfies Gamma_13>=0 or Gamma_31>=0.

**Theorem.** The original game has a uniform-equilibrium payoff. One
target vector is fixed before accuracy: for every epsilon>0 there are a
behavioral profile and a horizon threshold such that every longer finite
horizon delivers that target within epsilon and no complete unilateral
behavioral deviation gains more than epsilon. Own levels and every higher
coalition reward are arbitrary. No strategic witness, continuation, inverse,
Q condition, determinant sign or root selector is an input.

This is ordinary mathematics, not a new Lean declaration and not arbitrary
Fin4 closure. In the strict interior, the negative pair is an opposite
chord of a legal singleton Hamiltonian cycle. The proof supplies the
expanding eigenray from the original-game no-UE source, including when the
other chord has opposite signs. The older larger-eigenvalue sign pattern
requires that other chord to be mutually positive; the opposite-sign
case is the new raw completion class.

## 1. Strict normalization and actual source

First suppose all specified adjacent signs and both entries of pair02
are strict, and both entries of the other chord are nonzero. Rotating the
cycle twice if needed makes Gamma_13>0. Positive scaling of entire payoff
rows puts the singleton matrix in the form

    Gamma=[ 0   a   e  -1 ]
          [-1   0   b   g ]
          [-f  -1   0   c ]
          [ d  -h  -1   0 ],                          (1)

where a,b,c,d,f,g>0, e<0, and h!=0. The other chord is opposite-sign
when h>0 and mutually positive when h<0. Row scaling preserves all
original preferences, signed own levels, and UE existence.

Assume the original game has no uniform-equilibrium payoff. The same-table
full-normal-core reduction gives standard Q for Gamma: every offset has a
nonnegative complementary solution. The precise source declarations are
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`)
and `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`).
All applications below use this same original reward table; auxiliary
native games are not assumed to have no UE.

For an offset -y with y>>0, a solution with active support S satisfies
Gamma_SS*x_S=y_S with x_S>0, and Gamma_(I\S),S*x_S>=y_(I\S).
This simple support equation will produce the necessary inverse column.

## 2. Opposite-sign second chord

Suppose h>0 and put Delta=adg-h. The only possible proper support at a
strictly negative offset is013 with Delta>0. Indeed a singleton, an
opposite-sign pair, or the negative pair02 cannot map a nonnegative vector
strictly above zero. Triple012 has a negative row2, triple023 a negative
row0, and triple123 a negative row3. The adjugate of cyclic013 is strictly
positive. If Delta<0 its inverse is strictly negative; if Delta=0 a
positive left kernel precludes a positive image.

If Delta<=0, Q supplies a full positive solution Gamma*x=y for every y>>0.
The range contains an open set, so Gamma is invertible. Taking y toward
each positive coordinate ray gives Gamma^(-1)>=0. Its diagonal cofactor
at1 is cde-f<0, hence det Gamma<0. The existing theorem
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`
(`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`)
gives original-game UE, a contradiction.

It remains that Delta>0. The exterior adjugate row of the good child013 is

    n=(ch-dg-fgh, acd-d-fh, ac-afg-1).                 (2)

If n>=0, the child inverse and its nonnegative exterior inverse row give
the existing consumer
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`).
This also contradicts no UE. Otherwise n0<0: if n0>=0, then
c>=dg/h+fg, which gives n2>=Delta/h>0 and
n1>=(d/h+f)Delta>0.

Fix y0,y1,y3>0 and send y2 to infinity. The only possible proper root013
stays fixed and cannot meet the exterior inequality. Thus every solution
has full support for all sufficiently large y2. These bounds are uniform
when the three fixed coordinates range over a small compact positive box.
Q forces the range of Gamma to contain an open set and hence invertibility.
Letting y2 tend to infinity in its positive full solution gives

    Gamma^(-1)e2>=0,       det Gamma>0,               (3)

where the determinant sign follows from the positive diagonal cofactor
Delta. The exact adjugate column is

    adj(Gamma)e2=(B,1-d(b+ge),Delta,a-abd-eh),
    B=ga-h(b+ge).                                    (4)

Thus B>=0 and d(b+ge)<=1. Equality B=0 would imply
d(b+ge)=adg/h>1, impossible. Therefore B>0.

## 3. Produce the expanding legal cycle

From v=(0,1,r,0), successive column moves0,1,2,3 have durations

    t0=1, t1=r-f, t2=d-h(r-f), t3=a(r-f)+e*t2.        (5)

The two surviving endpoint coordinates are given by

    M=[ga b+ge; ca ce]*[-f 1; d+hf -h]=[A B; C D].   (6)

Direct expansion gives det M=abcd>0 and
det(I-M)=-det Gamma<0. The characteristic polynomial chi is negative
at1 with positive constant term, so it has two positive roots
0<lambda_minus<1<lambda_plus. Write lambda=lambda_plus and

    r=(lambda-A)/B.

The characteristic equation gives M(1,r)=lambda(1,r). From
A+Bf=d(b+ge)<=1<lambda one gets r>f>0. Put R=f+d/h and
ell=A+BR=adg/h>1. Equation(2) gives c/g<R. The exact endpoint identity is

    chi(ell)=B*ell*(R-c/g)>0.                         (7)

Since ell>1>lambda_minus, it follows that ell>lambda_plus, hence r<R.
Thus t1,t2>0. The second eigenvector equation is

    c*t3=lambda*r>0,

so t3>0 despite the negative chord coefficient e. All intermediate
vectors are nonnegative: each potentially decreasing coordinate has a
nonnegative final endpoint on its straight segment. Every moving owner's
coordinate is zero. The final vector is lambda*v, and all four durations
are strictly positive.

## 4. Mutually positive second chord

Suppose h<0. Triples012 and023 still have a negative row. The positive
pair13 and triple013 have fixed roots when y2 varies. Triple013 has
determinant adg-h>0. On triple123 its row1 equation
b*x2+g*x3=y1 bounds x2,x3, and its row3 equation -h*x1-x2=y3 then
bounds x1. Thus for sufficiently large y2 every proper support fails.
The open-box Q argument again gives (3) and the column(4), now with
Delta=adg-h>0 automatically.

The last entry of (4) gives a-eh>=abd>0, so

    B=g(a-eh)-bh>0, C=c[-f(a-eh)+ed]<0,
    A+Bf=d(b+eg)<=1.

Use the same two positive eigenvalues and r=(lambda_plus-A)/B>f.
Now t2=d-h(r-f)>0 automatically, and c*t3=lambda*r>0 again proves
t3>0. Thus the same legal expanding cycle is produced without a finite
upper endpoint for r. Equivalently, D=c(a-eh)>1 follows from A<1,
BC<0 and chi(1)<0. After chronological relabeling(0,3,2,1), these
are the familiar larger-branch tests with opposite chords negative and
positive. This branch supplies a complete sign-class reduction to that
older mechanism, while the h>0 branch supplies its missing sign chamber.

## 5. Full behavioral and finite-horizon consumer

Let T=sum t_j and alpha=(lambda-1)/T. Starting from native continuation
alpha*v, prepend owner j with hazard

    q_j=alpha*t_j/(1+alpha*sum_(k<=j)t_k).             (8)

The value follows the unnormalized column path divided by one plus
accumulated scaled time. It remains nonnegative and the moving owner's
value is zero. At the end the value is alpha*lambda*v/(1+alpha*T)=alpha*v.
Reverse construction order to obtain the chronological periodic strategy.
Its joint survival is1/lambda<1, and every player faces positive opponent
hazard in every period.

For arbitrary simultaneous rewards subdivide each singleton block into
proper microhazards at most delta, retaining its total survival. All
intermediate values stay on the same nonnegative segment. Write H for
the maximum of zero and the finitely many native participant pair rewards.
If d_i is complete-cap excess, an inactive owner's exact next excess is

    max{q*Z_i({i,j})-U_i', (1-q)*d_i}<=max{H*delta,d_i}.

For the moving owner its singleton value and prescribed value are both
zero, and its excess stays d_i. First allow deviations only before a finite
calendar cutoff and require the prescribed tail thereafter; the terminal
cap at that cutoff is its prescribed value, so its excess is zero.
Iterating gives a bound H*delta with no factor depending on word length.
Every finite forced date is covered by some such cutoff.
Deleted-opponent survival tends geometrically to zero, so taking the limit
also covers Never and every behavioral mixture of complete stopping dates.

Under any unilateral replacement the opponents absorb surely. Therefore
adding the original own level s_i shifts both prescribed and deviating
terminal payoffs by exactly s_i. The uniform opponent-tail bound also
transfers the terminal bound to all sufficiently long finite averages.
The target s+alpha*v is fixed before delta and accuracy. The corresponding
checked supplied consumer is
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`).
Its balanced arcs, all singleton floors, owner equalities and opponent
divergence have just been produced from the raw sign conditions.

For weak signs in the theorem, perturb only literal off-own singleton
coordinates to the strict adjacent signs and strictly negative pair02.
Perturb zeros on pair13 toward a positive value so this pair never becomes
mutually negative. The other own and higher coordinates stay fixed. The
strict theorem gives UE for every approximant. The exact closure theorem
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`)
then supplies the original fixed-payoff conclusion. No common target
across different perturbed tables is asserted or needed.

## 6. Exact original-table calibration

Set all own levels to one and define

    G=[0 1 -1/2 -1; -1 0 1/4 1; -1 -1 0 14/5; 2 -1 -1 0],
    L=[0 -2 -2 1; 1 0 -2 -2; 9/10 1 0 -2; -2 9/10 1 0],
    C=(4,3,1,1).

For every nonempty S and receiver i set

    r_i(S)=1+sum_(j in S)G_ij
             +1_(i in S)sum_(j in S)L_ij
             +C_i*1_(I\{i} subset S)+E_i(S),          (9)

where E=1 exactly at(0,013),(0,023), and is zero elsewhere. This
specifies every one of the sixty original absorbing coordinates. The
complete native vectors Z=r-1 are

| S | Z(S) |
| --- | --- |
| 0 | (0,-1,-1,2) |
| 1 | (1,0,-1,-1) |
| 2 | (-1/2,1/4,0,-1) |
| 3 | (-1,1,14/5,0) |
| 01 | (-1,0,-2,1) |
| 02 | (-5/2,-3/4,-1/10,1) |
| 03 | (0,0,9/5,0) |
| 12 | (1/2,-7/4,0,-2) |
| 13 | (0,-1,9/5,-1/10) |
| 23 | (-3/2,5/4,4/5,0) |
| 012 | (-7/2,-7/4,-1/10,1) |
| 013 | (0,-1,9/5,-1/10) |
| 023 | (-3/2,13/4,7/10,0) |
| 123 | (7/2,-11/4,4/5,-1/10) |
| 0123 | (1/2,1/4,17/10,9/10) |

The determinant is1/20 and

    G^(-1)=[6 -64 25 -19; 8 -76 30 -23;
            4 -52 20 -16; 5 -50 20 -15].              (10)

Every nontrivial principal determinant is nonzero, and each column has a
negative entry; hence G is R0. At offset-minus-ones, exact enumeration
gives only support013, with x=(3,5,0,4), exterior residual11/5, and
active determinant1. The R0 degree is one and G is standard Q. The exact
degree facts are `exists_finset_r0Degree_eq_sum_sign_det`
(`MathUE/LinearProgramming/R0DegreeSum.lean`) and
`isStandardQ_of_r0Degree_ne_zero` (`MathUE/LinearProgramming/R0Degree.lean`).

The only nonnegative-inverse triple is013, whose exterior inverse row is
(-1/5,13/5,4/5). It fails the passive-child criterion. The negative
principal012 has a negative row and is R0, so projective Q-bar fails.
The full inverse is not nonnegative. There is no mutually positive pair,
so no positive-pair inverse child is available. The sole positive-inverse
triple has missing pivot2 with G12=1/4>0, excluding cyclic-child joint
families requiring every child comparison against its pivot to be negative.

The return matrix is

    M=[-7/4 5/4; -7 21/5],
    lambda_plus/minus=(49 plus/minus sqrt161)/40,
    r=(119+sqrt161)/50 in(1,3).

The four durations are1,r-1,3-r,(3r-5)/2, all strictly positive.
The unique negative Hamiltonian cycle and its rotations have smaller
eigenvalue below one, so the named smaller-branch reward adapter does not
apply. The other opposite chord is opposite-sign, so the old larger
raw sign pattern requiring a mutually positive opposite pair also fails.
The smaller-branch implementation is `SignedFourCycleSingletonData.StrictTests`
in `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`.

## 7. Complete finite selector comparisons

### 7.1 Quiet children

For child A and outsider o the literal capped-clock rows require
nonnegative weights satisfying

    F_S: sum_i w_i[1-r_i(S)]>=1-r_o(S),
    J_S: sum_i w_i[r_i(S+i)-r_i(S)]>=r_o(S+o)-r_o(S).

They are the fields of `CappedClockParentRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`.
Every complete child has the following explicit impossible outsider:

| A | o | Positive combination | Coefficients | Lower bound |
| --- | --- | --- | --- | --- |
| 0 | 1 | F0 | (0) | 1 |
| 1 | 2 | F1 | (0) | 1 |
| 2 | 0 | F2 | (0) | 1/2 |
| 3 | 0 | F3 | (0) | 1 |
| 01 | 2 | J01 | (0,0) | 19/10 |
| 02 | 3 | J2 | (-2,0) | 1 |
| 03 | 1 | F0 | (0,-2) | 1 |
| 12 | 0 | F2 | (-1/4,0) | 1/2 |
| 13 | 0 | F3 | (-1,0) | 1 |
| 23 | 0 | F23 | (-4/5,0) | 3/2 |
| 012 | 3 | J12 | (-4,0,0) | 19/10 |
| 013 | 2 | J01 | (0,0,-11/10) | 19/10 |
| 023 | 1 | 2J0+F03 | (0,0,-4) | 2 |
| 123 | 0 | F23 | (-5/4,-4/5,0) | 3/2 |

No Never row is used, so arbitrary Never slack cannot repair any of these
contradictions. This is the complete fourteen-child selection set, not a
claim that every individual child/outside pair is infeasible.

### 7.2 Entire sure-owner and punishment correspondences

The exact native forced-Quit minus Continue polynomials at continuation
zero, derived from all sixty rewards, are

    F0=-2q1-2q2+q3+q1q3(1-q2)+q2q3(1-q1),
    F1=q0-2q2-2q3,
    F2=(9/10)q0+q1-2q3,
    F3=-2q0+(9/10)q1+q2.                             (11)

Their complete complementary Nash correspondences are

| Sure owner | All complementary points | Owner floor excess |
| --- | --- | --- |
| 0 | (1,0,1,0) | 2 |
| 1 | (t,1,0,1), 0<=t<=9/20 | 2-t>=31/20 |
| 2 | (t,0,1,1), 0<=t<=1/2 | 2-(9/10)t>=31/20 |
| 3 | (1,0,0,1) | 2 |

For owner0, q1>0 would imply q2+q3<=1/2, hence F3<0 forces q3=0
and F2>0 forces q2=1, a contradiction. Thus q1=0, then q3=0,q2=1.
For owner1, F0=-2-2q2+2q3-q2q3<=-3q2. If q0>0 it forces
q2=0,q3=1; if q0=0, F3>0 and then F2<0 give the same conclusion.
The remaining inequality is9/10-2q0>=0. Owner2 is identical with q1
in place of q2 and remaining inequality1-2q0>=0. For owner3, F1<0
forces q1=0, then F2<0 forces q2=0, and F0>0 forces q0=1.
Substitution gives the converse, including both singular segments.

Every point has a sure opponent of its fixed owner. The coefficient of
every punishment continuation in that owner's floor is zero. Thus every
smaller free-set choice and every punishment value fails as well. The
literal interfaces are `quittingSingletonBaseOwnerFloorExcess_nonpos_iff`
and `nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
A persistent base of at least two players satisfying all its endpoint
conditions would be a full Nash root with a sure owner, already excluded.
This checks all selections in `nonempty_quittingPersistentBaseCertificate_of_inducedNash`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.

### 7.3 Premium, weighted, phase and pole families

The grand participant premiums (1/2,1/4,17/10,9/10) are all positive.
They refute product-low-premium and every nonzero nonnegative weighted
Quit upper average. The relevant implemented theorem is
`exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
The only premium trap is I. The middle-size joining sum against01 over
outsiders2,3 is4/5>0, defeating the boxed-charge alternative on this trap.
Every player has a below-own participant pair, respectively01,12,02,13.

For inserted native premiums k(S)_i=Z_i(S+i) and passive h(S)=Z(S),
the exact strictly negative duals are

    34k(01)+k(02)+k(12)=(-40,-7/2,-7/2,-7/2),
    125h(01)+226h(12)+70h(012)=(-257,-518,-257,-257).

Thus all nonzero nonnegative global floor and passive-ledger weights fail.
Joining by0 against3 gains one, while joining against123 loses three,
so no-strict-background-reversal also fails. Each pair partition has a
negative scheduled joining comparison; every triple has a negative
internal pair comparison, defeating the six-positive-joining triple family.

The unique inverse-column signs in(10) are(+,-,+,-). For the signed
inverse two-pair producer, partitions01|23 and02|13 fail the required
signed joining sign at owner0. Partition03|12 fails the signed passive
condition because its K0=Z0(12)=1/2>0 and sigma0=1. This exhausts that
existential pair selection despite the signed-inverse baseline passing.
There is only one same-sign singleton pair, and it is negative. Matching
families requiring two same-sign pairs, positive-favorite matchings, and
negative-pair-funded families requiring two negative pairs therefore fail
under every relabeling.

For each ordered role choice(i,j,k,l), the earlier three-passive-pole
finite guards are

    A=join_i(l)>0, B=join_i(kl)<0, z=A/(A-B),
    join_k(l)<0, join_k(il)<0,
    (1-z)join_j(l)+z*join_j(kl)<0,
    (1-z)join_j(il)+z*join_j(ikl)<0,
    z[(1-z)r_l(l)+z*r_l(kl)-r_l(k)]>0,
    (1-z)join_l(i)+z*join_l(ik)<0.

The complete twenty-four-role rational census in the appended program
finds no passing role. It uses only these finite guards, with no unknown
large-pole threshold.

## 8. Exact scope of the overlap comparison

The inverse in(10) DOES pass the inverse baseline of signed passive-coalition
asymptotic producers, and its positive columns pass the baseline of a
single-column participant-jackpot producer. Those theorems guarantee
stationary equilibrium beyond an implicit threshold when specified passive
or participant coordinates diverge and all other coordinates remain in a
fixed bounded box, with a scale-thick variant for the participant pole.
No finite-threshold exclusion or admission for table(9) is claimed here.
In particular the inverse column by itself proves neither.

The new theorem supplies UE for EVERY finite higher-coalition completion
of the strict sign class, and its weak closure. It requires no selected
large coordinate, bounded remainder, or asymptotic parameter. The complete
finite comparisons above separate its explicit calibration from the named
finite raw criteria. This is an arbitrary-completion improvement over the
asymptotic mechanisms; the comparison is not a claim that the fixed table
has no stationary equilibrium or that no unknown large-parameter threshold
could include it. Supplied balanced-cycle certificates are expected to
accept the newly constructed cycle and are not being excluded.

For table(9) the produced coarse cycle is itself exact Nash: every inactive
Quit endpoint lies below its prescribed continuation, as the quadratic-field
verifier checks. To test the arbitrary-higher-reward step, change ONLY
native Z2(02) to4. This leaves all raw singleton hypotheses intact, but
at the first owner0 macrostep the owner2 Quit advantage becomes

    alpha/(1+alpha)*(5-r)>0.

Thus the unrestricted theorem really needs the full-law subdivision
argument. This second completion is a collision stress test, not another
complete coverage calibration. The exact singleton matrix of a different
one-negative-pair graph can admit no finite balanced singleton cycle at all;
the present result makes no claim about those non-Hamiltonian chambers.

## 9. Formalization handoff

The raw theorem should accept a Fin4 reward table and the six weak pair
conditions in the opening statement, then return existence of an original
uniform-equilibrium payoff. The main finite lemmas are the negative-offset
proper-support census, Q-to-one-inverse-column forcing, adjugate column(4),
the characteristic endpoint identity(7), and positivity of t3 from the
second eigenvector equation when e<0. Existing same-table Q, inverse-child,
balanced-cycle and reward-closure declarations supply the named source and
consumer steps. No desired strategy is introduced as a hypothesis.

The theorem is a complete sign chamber with arbitrary signed own levels
and arbitrary higher rewards. Other one-negative-pair graphs, more general
negative-pair patterns, and arbitrary Fin4 remain open here. The code below
checks exact finite calibration data; it does not replace the universal
support and strategic arguments.

## Appendix: complete exact verifier

Save the following as a Python file and run with SymPy installed.

```python
"""Exact negative-chord control; run with Python and SymPy installed.

This checks the literal reward calibration and finite comparisons. The
universal reward-class proof and completeness of the complementary Nash
correspondences are supplied in the associated mathematical manuscript.
"""
from itertools import combinations, permutations, product
import sympy as s

R = s.Rational
I = tuple(range(4))
COAL = tuple(A for n in range(1, 5) for A in combinations(I, n))
G = s.Matrix([[0, 1, -R(1, 2), -1], [-1, 0, R(1, 4), 1],
              [-1, -1, 0, R(14, 5)], [2, -1, -1, 0]])
L = s.Matrix([[0, -2, -2, 1], [1, 0, -2, -2],
              [R(9, 10), 1, 0, -2], [-2, R(9, 10), 1, 0]])
C = (4, 3, 1, 1)
EXTRA = {(0, (0, 1, 3)), (0, (0, 2, 3))}


def reward(i, coalition):
    coalition = tuple(sorted(set(coalition)))
    assert coalition
    return (1+sum(G[i, j] for j in coalition)
            +(sum(L[i, j] for j in coalition) if i in coalition else 0)
            +(C[i] if set(I)-{i} <= set(coalition) else 0)
            +int((i, coalition) in EXTRA))


def native(i, coalition):
    return reward(i, coalition)-1


def join(i, coalition):
    return reward(i, set(coalition) | {i})-reward(i, coalition)


assert len({(i, A): reward(i, A) for i in I for A in COAL}) == 60
assert all(reward(i, [i]) == 1 for i in I)
assert all(native(i, [j]) == G[i, j] for i in I for j in I)
assert G.det() == R(1, 20)
assert G.inv() == s.Matrix([[6, -64, 25, -19], [8, -76, 30, -23],
                           [4, -52, 20, -16], [5, -50, 20, -15]])
assert all(G.extract(T, T).det() != 0 for n in (2, 3, 4)
           for T in combinations(I, n))
assert all(any(G[i, j] < 0 for i in I) for j in I)
positive_children = [T for T in combinations(I, 3)
                     if all(x >= 0 for x in G.extract(T, T).inv())]
assert positive_children == [(0, 1, 3)]
child = (0, 1, 3)
assert list(G.extract([2], child)*G.extract(child, child).inv()) == [
    -R(1, 5), R(13, 5), R(4, 5)]
assert G[1, 2] > 0  # The sole inverse child lacks an all-negative pivot column.
solutions = []
for n in (2, 3, 4):
    for T in combinations(I, n):
        x = s.zeros(4, 1)
        for i, value in zip(T, G.extract(T, T).inv()*s.ones(n, 1)):
            x[i] = value
        residual = G*x-s.ones(4, 1)
        if min(x) >= 0 and min(residual) >= 0:
            solutions.append((T, list(x), list(residual)))
assert solutions == [((0, 1, 3), [3, 5, 0, 4], [0, 0, R(11, 5), 0])]
assert G.extract(child, child).det() == 1

q = s.symbols('q0:4')
F = s.Matrix([-2*q[1]-2*q[2]+q[3]+q[1]*q[3]*(1-q[2])+q[2]*q[3]*(1-q[1]),
              q[0]-2*q[2]-2*q[3], R(9, 10)*q[0]+q[1]-2*q[3],
              -2*q[0]+R(9, 10)*q[1]+q[2]])
for i in I:
    others = [j for j in I if j != i]
    value = 0
    for bits in product((0, 1), repeat=3):
        A = [j for j, bit in zip(others, bits) if bit]
        probability = s.prod(q[j] if bit else 1-q[j] for j, bit in zip(others, bits))
        value += probability*(native(i, A+[i])-(native(i, A) if A else 0))
    assert s.expand(value-F[i]) == 0
for bits in product((0, 1), repeat=4):
    value = sum(q[i]*F[i] for i in I).subs(dict(zip(q, bits)))
    assert value == 0 if sum(bits) <= 1 else value < 0

t = s.symbols('t', real=True)
segments = [(0, [1, 0, 1, 0], 0, 2),
            (1, [t, 1, 0, 1], R(9, 20), 2-t),
            (2, [t, 0, 1, 1], R(1, 2), 2-R(9, 10)*t),
            (3, [1, 0, 0, 1], 0, 2)]
for owner, point, upper, floor in segments:
    gaps = F.subs(dict(zip(q, point)))
    assert s.expand(-gaps[owner]-floor) == 0
    assert any(point[i] == 1 for i in I if i != owner)
    for i in I:
        if i == owner:
            continue
        if point[i] == t:
            assert gaps[i] == 0
        else:
            sign = 1 if point[i] == 1 else -1
            assert min((sign*gaps[i]).subs(t, z) for z in (0, upper)) >= 0
    assert min(s.sympify(floor).subs(t, z) for z in (0, upper)) >= R(31, 20)


def row(kind, A, child, outside):
    if kind == 'F':
        return [1-reward(i, A) for i in child], 1-reward(outside, A)
    assert kind == 'J'
    return [join(i, A) for i in child], join(outside, A)


BLOCKERS = [
    ((0,), 1, [('F', (0,), 1)]), ((1,), 2, [('F', (1,), 1)]),
    ((2,), 0, [('F', (2,), 1)]), ((3,), 0, [('F', (3,), 1)]),
    ((0, 1), 2, [('J', (0, 1), 1)]), ((0, 2), 3, [('J', (2,), 1)]),
    ((0, 3), 1, [('F', (0,), 1)]), ((1, 2), 0, [('F', (2,), 1)]),
    ((1, 3), 0, [('F', (3,), 1)]), ((2, 3), 0, [('F', (2, 3), 1)]),
    ((0, 1, 2), 3, [('J', (1, 2), 1)]),
    ((0, 1, 3), 2, [('J', (0, 1), 1)]),
    ((0, 2, 3), 1, [('J', (0,), 2), ('F', (0, 3), 1)]),
    ((1, 2, 3), 0, [('F', (2, 3), 1)])]
assert {A for A, _, _ in BLOCKERS} == {A for A in COAL if len(A) < 4}
for child, outside, terms in BLOCKERS:
    rr = [(weight, row(kind, A, child, outside)) for kind, A, weight in terms]
    coeff = [sum(w*data[0][j] for w, data in rr) for j in range(len(child))]
    lower = sum(w*data[1] for w, data in rr)
    assert max(coeff) <= 0 < lower

assert [native(i, I) for i in I] == [R(1, 2), R(1, 4), R(17, 10), R(9, 10)]
traps = [A for A in COAL if all(any(i in B and set(B) <= set(A) and native(i, B) > 0
                                  for B in COAL) for i in A)]
assert traps == [I]
assert join(2, (0, 1))+join(3, (0, 1)) == R(4, 5)
assert all(any(i in A and native(i, A) < 0 for A in COAL) for i in I)
floor_dual = [(34, (0, 1)), (1, (0, 2)), (1, (1, 2))]
assert [sum(w*native(i, set(A) | {i}) for w, A in floor_dual) for i in I] == [
    -40, -R(7, 2), -R(7, 2), -R(7, 2)]
ledger_dual = [(125, (0, 1)), (226, (1, 2)), (70, (0, 1, 2))]
assert [sum(w*native(i, A) for w, A in ledger_dual) for i in I] == [-257, -518, -257, -257]
assert join(0, (3,)) == 1 and join(0, (1, 2, 3)) == -3
partitions = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
assert all(any(join(i, [j]) < 0 for A in P for i, j in (A, A[::-1])) for P in partitions)
assert all(any(join(i, [j]) < 0 for i in A for j in A if i != j)
           for A in combinations(I, 3))
# The unique signs making every inverse column positive are (+,-,+,-).
sigma = (1, -1, 1, -1)
assert min(G.inv()*s.diag(*sigma)) > 0
signed_pair_passes = []
for P in partitions:
    mate = {i: j for A in P for i, j in (A, A[::-1])}
    ok = True
    for i in I:
        j = mate[i]
        opposite = set(I)-{i, j}
        ok &= sigma[i]*join(i, [j]) > 0
        ok &= sigma[i]*native(i, [i, j]) >= 0
        ok &= sigma[i]*native(i, opposite) <= 0
    if ok:
        signed_pair_passes.append(P)
assert signed_pair_passes == []
assert native(0, (1, 2)) == R(1, 2)
assert sum(int(bool(G[i, j] < 0 and G[j, i] < 0)) for i, j in combinations(I, 2)) == 1
assert not any(G[i, j] > 0 and G[j, i] > 0 for i, j in combinations(I, 2))

passing = []
for i, j, k, l in permutations(I):
    a, b = join(i, [l]), join(i, [k, l])
    if not (a > 0 and b < 0):
        continue
    mix = a/(a-b)
    tests = [join(k, [l]), join(k, [i, l]),
             (1-mix)*join(j, [l])+mix*join(j, [k, l]),
             (1-mix)*join(j, [i, l])+mix*join(j, [i, k, l]),
             (1-mix)*join(l, [i])+mix*join(l, [i, k])]
    f0 = mix*((1-mix)*reward(l, [l])+mix*reward(l, [k, l])-reward(l, [k]))
    if all(x < 0 for x in tests) and f0 > 0:
        passing.append((i, j, k, l))
assert passing == []

# Exact quadratic-field arithmetic avoids uncontrolled radical expansion.
K = s.QQ.algebraic_field(s.sqrt(161))
to = lambda x: K.from_sympy(s.sympify(x))
zero, one = K.zero, K.one
lam = to((49+s.sqrt(161))/40)
small = to((49-s.sqrt(161))/40)
ratio = to((119+s.sqrt(161))/50)
assert 0 < K.to_sympy(small) < 1 < K.to_sympy(lam)
assert 1 < K.to_sympy(ratio) < 3
durations = [one, ratio-one, to(3)-ratio, to(R(3, 2))*ratio-to(R(5, 2))]
assert all(K.to_sympy(z) > 0 for z in durations)
alpha = (lam-one)/sum(durations, zero)
u = [zero, alpha, alpha*ratio, zero]
accumulated, survival = zero, one
for j, duration in enumerate(durations):
    hazard = alpha*duration/(one+accumulated+alpha*duration)
    assert u[j] == zero
    u = [(one-hazard)*u[i]+hazard*to(G[i, j]) for i in I]
    assert all(K.to_sympy(z) >= 0 for z in u)
    # This particular completion even makes the unsplit coarse cycle Nash.
    assert all(K.to_sympy(hazard*to(native(i, (i, j)))-u[i]) <= 0
               for i in I if i != j)
    accumulated += alpha*duration
    survival *= one-hazard
assert u == [zero, alpha, alpha*ratio, zero]
assert survival == one/lam
# Raising only native Z2(02) to4 stays in the raw sign class and makes
# the first macro collision harmful, so refinement is genuinely needed
# for the unrestricted-higher-reward theorem.
assert K.to_sympy(to(5)-ratio) > 0
print('PASS: full60, R0/degree-one, complete finite raw-family blockers,')
print('all14 quiet children, all24 pole roles, exact complementary endpoints,')
print('and exact larger-eigenvalue Bellman cycle with fixed target.')
```
