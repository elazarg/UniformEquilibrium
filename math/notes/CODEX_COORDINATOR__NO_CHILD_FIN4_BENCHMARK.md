# A no-child benchmark with exact stationary and sure-root exclusions

This is a benchmark and a coverage audit, not a counterexample to UE.
The M=14 table below has an exact finite certificate excluding every
stationary terminal Nash profile and every sure-first terminal Nash profile
with arbitrary behavioral continuation. Several complete raw producer
families also fail. Arbitrary nonstationary strategies remain unresolved. The
[finite-profile descents](CODEX_COORDINATOR__FINITE_GLOBAL_DESCENT.md)
exclude every actual selected minimum with at most one occupied date and
force every two-date minimum to begin with all four owners. These are
whole-profile comparisons, not additional local feasibility tests.

## Table

Original absorbing rewards are r_i(D)=4+Z_i(D), with live/Never zero.
Own native singleton rewards are zero, and the singleton matrix is

 Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0].

For every nonsingleton D, put Z_i(D)=-5 when i belongs to D and Z_i(D)=0
otherwise. With successor cycle

                 0 -> 1 -> 3 -> 2 -> 0,

replace precisely four participant entries by

          Z_successor(j)({j,successor(j)})=M-1.

Take M=14, so those four entries are13. Every remaining native participant
nonsingleton is-5, and every passive nonsingleton is0. These rules specify
all60 original absorbing reward coordinates.

The matrix has determinant11 and

 Gamma^-1=(1/11)[3,-2,4,5; 1,3,5,-2; -2,5,1,4; 5,4,3,1].

Its unique positive inverse column is2. All other columns are mixed. The
principal triple determinants are1,1,3,3. The reciprocal opposition graph
is the path0--2--3--1, hence there is no positive-inverse triple. All columns
have a negative entry. Principal nonsingularity gives R0, and the unique
full root at offset-e2 gives degree+1, as proved in the
[residual partition](CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md).

## Exact stationary certificate

For q in[0,1]^4, let H_i be opponent survival, P_i the expected native
reward from their nonempty quitter coalition, and Q_i the native reward
from quitting against that coalition. Put

                  F_i=(1-H_i)Q_i-P_i.

Every stationary terminal Nash profile has F_i<=0 at q_i=0, F_i>=0 at
q_i=1, and F_i=0 at0<q_i<1. All Continue is not Nash because a solo quit
pays4 instead of0. Enumerate the other80 patterns in{quiet,sure,mixed}^4.
For a pattern, set quiet coordinates0, sure coordinates1, and bound the
mixed coordinates on their closed unit cube.

The checker uses these sound rules:

1. A pure pattern is rejected by an exact violated scalar sign.
2. For one mixed player and no sure player, an actual quiet-row restricted
   polynomial has nonnegative coefficients and is not zero. It is strictly
   positive at every positive free coordinate. The checker verifies this
   property from the new table. In fact the designated successor's field is
   q+(M-1)q^2, but no inherited family shortcut is assumed.
3. For at least two mixed players S and no sure player, write the active
   field as -Aq+R(q), where A=Gamma_SS and every monomial in R has degree
   at least2. The checker verifies all constant and linear coefficients.
   If V=A^-1 and C_j is the coefficient absolute sum of R_j, then an
   active zero satisfies ||q||infty<=K||q||infty^2, where
   K=max_i sum_j|V_ij|C_j. Thus a nonzero zero is outside the dyadic origin
   cube of side2^-E<1/K. If K=0, no nonzero zero exists. This is the only
   analytic removal of a box that has no strict polynomial contradiction.
4. Add the exact active equations V F_S=0. Convert all restricted
   polynomials to tensor Bernstein coefficients at their maximum occurring
   coordinate degree, with minimum degree1. Strict one-sided coefficients
   contradict an opposing weak sign or equality. Clear the common positive
   denominator and bisect using exact integer de Casteljau formulas.

For degree d on a fiber, the coefficients on the left and right halves,
multiplied by2^d, are

 left_r=2^(d-r) sum_(j=0)^r binom(r,j)b_j,
 right_r=2^r sum_(j=0)^(d-r) binom(d-r,j)b_(r+j).

These are exact restrictions, and the two child boxes cover their parent.
Patterns, free axes and coefficient indices are lexicographic; split the
free axis with least subdivision depth, break ties in player order, and
visit the left child first. Choose the first positive E with2^-E<1/K.
Abort before subdividing if node count exceeds100000 or coordinate depth
exceeds35. A failure makes no exclusion claim. For M=14 every box is
removed, totaling560 nodes including analytic shortcuts.

The standard-library checker is
[CODEX_NO_CHILD__BENCHMARK_EXACT_CHECK.py](../experiments/CODEX_NO_CHILD__BENCHMARK_EXACT_CHECK.py).
Its default command reports exactly:

```
EXACT RATIONAL PASS: M=14; all80 nonzero stationary patterns excluded; 560 nodes
EXACT RATIONAL PASS: M=14; all65 sure-root patterns excluded; 65 nodes
```

## Sure-first exclusion with unrestricted continuations

The same checker forms G_i=Q_i-P_i+4H_i. The value-4 is a valid native
lower bound for a player's full response in any continuation: never quit
gives only passive absorbing original rewards at least3, or Never0.
On a root containing a sure quitter, every other player has H_i=0. If
there is just one sure quitter, replacing its continuation response by
this lower bound increases its quitting advantage, preserving its necessary
nonnegative sign. Thus the usual quiet/sure/mixed signs for G are necessary.
All65 sure-root patterns fail immediately by exact Bernstein signs, without
subdivision. This prices arbitrary continuation laws rather than only
stationary continuations.

There is also a direct proof for every M>0. If j surely quits, every player
other than j and successor(j) strictly Continues: joining gives original-1,
whereas remaining outside any nonempty opponent coalition gives at least3.
The successor must then surely join, gaining M against j. Player j can
withdraw from the pair payoff-1 to a passive singleton payoff at least3.
This contradicts root Nash and exhausts every possible sure owner.

## Complete raw criteria and a solved boundary control

The same construction at M=10 is already solved. Its only premium trap is the full
player set, since every positive participant pair follows the single4cycle.
At uniform weights, its support-local forced-Quit upper averages are0 on
empty, -1 on singletons, -6 on cycle pairs, and-20 otherwise. Therefore
[the mixed-support upper-average theorem](../exports/MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md) proves UE there.
The exact stationary/sure-root exclusions at M10 remain valid, but they
do not separate that older nonstationary producer.

For M14 the following complete premise failures hold:

* **Upper averages and boxed charges.** The full set is still the only
  premium trap. Summing its four singleton upper-average tests gives
  (M-11)sum_i w_i=3sum_i w_i>0 for every nonzero nonnegative w.
  No such upper certificate exists. Its singleton boxed-charge quantity
  P_I({j})=M-11=3 is positive, so the required strictly negative range
  fails. This rejects the full-trap alternatives in the mixed-support and
  mixed-premium-trap theorems.
* **Every nonnegative joining ledger.** Summing the four singleton joining
  charges gives3w0+2w1+w2+2w3>0 for any nonzero nonnegative weight vector.
  Thus J({j})<=0 cannot hold for all four j. This rejects every weight
  support in the scalar and support-filtered ledger criteria. The stronger
  unfiltered H>=0 condition also fails independently: each passive triple
  has native reward0 outside and-5 inside, so nonzero weights make some
  proper-triple H strictly negative. Hence no finite family of such H
  ledgers can evade that obstruction.
* **All ordered anchor blocks.** If a marked player i lacks its predecessor
  in the marked set, their pair has only the positive marked premium13,
  violating its first-block cap. Marked sets must therefore be closed
  under the4cycle and equal I. For blocks, a predecessor cannot occur in
  a later block than its successor, so all players must share one block.
  The four pair caps then require13 lambda_successor<=5 lambda_owner;
  multiplication contradicts13^4>5^4. This also rejects calendar-polytope
  criteria requiring a proper marked subset and the same first-block caps.
* **General finite-invariant-cone alternating pairs.** Every pair has at
  least one participant premium-5, so that endpoint has
  c_i=Z_i(pair)-Gamma_i,mate<=-4<0. No pair partition satisfies the
  criterion c_i>0 for every player, irrespective of its proof-weight V.
* **Stationary producers.** Any claimed application of an exact stationary
  producer contradicts the complete stationary certificate. This covers
  the weighted dominance, strict/boundary inverse-column jackpot and
  contact-preserving bonus criteria when their full hypotheses hold.
* **Cyclic-child and full-positive-inverse hypotheses.** The matrix has no
  inverse-positive triple and has three mixed full inverse columns. These
  exact failures are invariant under all player relabelings and positive
  recipient scalings. Families requiring four opposite-sign cycle edges
  also fail because the opposition graph is only a three-edge path.
* **A protected participant row.** Every recipient has a positive native
  participant pair13. Thus no relabeling meets any theorem requiring one
  recipient's seven nonsingleton participant coordinates all nonpositive.
* **Scalar singular circuit.** Its four positive participant entries force
  roles along the displayed4cycle. Its negative singleton C3 and positive
  join at13 pin the unique mutually negative pair, leaving only role order
  (0,1,2,3)=(2,1,3,0). In that order its required denominator is
  D_X=M-5Z+(M-1)(-4-5Y)=4-3M-5Z-5(M-1)Y<0 for positive Y,Z,
  contrary to the criterion D_X>0. This rejects all relabelings of that
  finite scalar criterion, not just one natural role assignment.

These are exact premise failures, not claims that the corresponding broader
strategy architectures cannot solve the table. Unspecified qualitative
neighborhoods and arbitrary supplied-controller certificates have not been
classified. Proper-child singleton equilibria have an outside successor who
profits by joining; this rejects raw universal safety bounds, but by itself
does NOT rule out every possible nonstationary child equilibrium selection.
The table is therefore a useful no-child research target, not a proved
unrestricted counterexample and not a claim of universal producer coverage.

## Exact remaining source partition

The [open four-owner tail theorem](CODEX_COORDINATOR__FOUR_OWNER_TAIL_REGION.md)
applies throughout M>11. Every actual ALL-END profile with positive marginal
Never masses and zero observer debts on013 has either finite support F or
all four infinite owners I4. No absorbing-gap, genericity or dispersion
hypothesis is needed for this support theorem. Its strict finite inequalities
also give an open region in the twenty-four singleton and participant-pair
entries, with the remaining thirty-two native entries arbitrary finite.

At a hypothetical actual global minimum, the first root has support02,
012 or0123, while a finite last root has support012 or0123. This leaves six
first/last support combinations on the finite side. The proofs below give
further contact and hazard inequalities. Both finite and four-owner local
controls satisfy positive-cap conditions, so local feasibility does not
eliminate either branch. Inherited semantic endpoints remain separate.

The [cyclic joining-cap region](CODEX_COORDINATOR__CYCLIC_JOINING_CAP_REGION.md)
gives a further global constraint. Positive continuation vectors admitting a
nonzero Nash root form a bounded, downward-closed, logarithmically convex
region D, with an explicit polynomial feasibility test and Perron boundary.
A positive global minimum must have its full cap outside D: a nonzero Nash
prefix would multiply both its debt and Never product by a number below one.
The exact M14 boundary vector in that proof yields four concrete weak
inequalities that cannot all hold at such a minimum. This is a constraint
on the complete minimum cap, not a replacement inside an inherited head.

## Exact last-root classification and finite controls

This concerns the native no-child benchmark with parameter M>11, pivot2,
observer set{0,1,3}, and continuation equal to literal Never. It classifies
its complete admissible last-root relation. It does not assert a positive
absorbing gap, global minimization, or a UE counterexample.

The singleton matrix is

 Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0].

Every native nonsingleton participant reward is-5, except successor premiums
M-1 on the cycle0->1->3->2->0; all native passive nonsingleton rewards are0.
Own singleton, live and Never rewards are0. Write q_i in[0,1),
x_i=q_i/(1-q_i), H_i=product_(j!=i)(1-q_j), and let P_i,Q_i be the
Continue/Never and immediate-Quit payoffs at the last occupied date.

The relevant necessary and sufficient conditions for a one-date actual
profile to be ALL-END with zero observer debts are:

 P_i-Q_i>=0 for all i;
 P_i-Q_i=0 whenever q_i>0 and i!=2.                    (1)

They are sufficient because every finite query after this date gives P_i,
as does Never, while querying at this date gives Q_i. Prescribed observer
laws then average equal full responses. No pivot indifference is imposed.

### 1. Four exact polynomial gaps

Put g_i=(P_i-Q_i)/H_i. The complete formulas are

 g0=4x1-Mx2+7x3+5(x1x2+x1x3+x2x3+x1x2x3),
 g1=-Mx0+6x2+6x3+5(x0x2+x0x3+x2x3+x0x2x3),
 g2=6x0+7x1-Mx3+5(x0x1+x0x3+x1x3+x0x1x3),
 g3=6x0-Mx1+6x2+5(x0x1+x0x2+x1x2+x0x1x2).           (2)

Indeed P_i/H_i=sum_j Gamma_ij x_j, while

 Q_i/H_i=-5[product_(j!=i)(1+x_j)-1]+(M+4)x_pred(i).

Every nonempty admissible root has at least three active owners, directly
from(1): a singleton j gives g_successor(j)=-Mx_j<0. For the six pairs
01,02,03,12,13,23, respectively use the nonzero active-observer gaps
4x1,-Mx2,7x3,6x2,6x3,6x2, on rows0,0,0,1,1,3.
Among supports with at least three owners, only012 and0123 are possible:

* on013, the active observer0 has g0=4x1+7x3+5x1x3>0;
* on023, the active observer3 has g3=6x0+6x2+5x0x2>0;
* on123, the active observer1 has g1=6x2+6x3+5x2x3>0.

Each contradicts its contact equality in(1). These exclusions hold for
all M>0 and need no tail-dispersion input.

### 2. Exact triple-support branch

Set z=x2 and x3=0. Active observer contacts give exactly

 x0=6z/(M-5z),       x1=Mz/(4+5z),       0<z<M/5.       (3)

The pivot gap g2 is strictly positive. The remaining quiet condition g3>=0
is equivalent to A_M(z)>=0, where

 A_M(z)=5M z^2+(10M^2+60M+180)z-M^3+24M+144.          (4)

Precisely,

 g3=z A_M(z)/[(M-5z)(4+5z)].

For M>11, A_M is strictly increasing on z>=0, its constant term is
negative, and A_M(M/5)>0. Let z_*(M) be its unique positive root. Then all
triple-support last roots are exactly(3) with

                         z_*(M)<=z<M/5.               (5)

Every one of them has a strictly negative observer0 cap, since

             P0/H0=-x1-z<0.

This is a last-root fact only; descendants of a positive-cap minimum may
have negative caps.

### 3. Exact full-support observer-contact branch

Fix z=x2>0 and abbreviate

 L=5(1+z), h=M-5z, C=6+5z, K=6z, T=M+6=C+h,
 phi(y)=(K+C y)/(h-L y),
 d=h^2-LK, e=LT, a=C^2-LK, b=KT.                     (6)

The observer1 and observer3 contact equations in(2) are exactly

             x0=phi(y), x1=phi(phi(y)), y=x3.          (7)

Every positive solution must have h>0 and

                  0<y<d/e,

which also guarantees 0<x0<h/L. Direct composition gives

                 x1=(a y+b)/(d-e y).                 (8)

The remaining observer0 equation is the single scalar equation

 F_z(y)=(4+5z)x1+(7+5z)y+L x1 y-Mz=0.                (9)

On the legal interval, phi and phi composed with itself are strictly
increasing: phi'=(Ch+LK)/(h-Ly)^2>0. Consequently F_z is strictly increasing.
At the right endpoint x1 tends to positive infinity, so F_z tends to
positive infinity. At y=0,

 F_z(0)=z A_M(z)/d,

using A_M(z)=6(4+5z)(M+6)-Md. Therefore a positive observer-contact root
exists exactly when

                         0<z<z_*(M).                 (10)

For these z, d>0 follows from that same identity. There is exactly one
y=y(z) in(0,d/e), and(7) determines x0,x1 uniquely. Conversely every full
positive observer-contact root is obtained in this way. The boundary
z=z_* has y=0 and joins the triple-support branch.

This is an explicit algebraic parametrization, not a supplied strategic
root. Multiplying(9) by d-e y gives

 -A2 y^2+A1 y+A0=0,
 A2=L[5z^2+5Mz+7M+6]>0,
 A1=(4+5z)a+Lb+(7+5z)d+Mz e,
 A0=z A_M(z)<0.                                      (11)

The unique legal root is the smaller positive quadratic root. The existence
argument above also proves the discriminant is positive and A1>0, so it
may equivalently be evaluated as

 y=(-2A0)/(A1+sqrt(A1^2+4A2 A0)).

The complete full-support last-root class consists of the points(7),(10)
for which the one remaining explicit expression

 6x0+7x1-My+5(x0x1+x0y+x1y+x0x1y)>=0                (12)

holds. Thus the full last-root relation has been reduced to two explicitly
parametrized one-dimensional branches, with one scalar inequality remaining
on the full branch. Conditions(3)–(12) are necessary AND sufficient for(1)
with a nonempty root.

### 4. A positive-cap full-support control at M14

The tempting stronger assertion that every admissible last root has a
nonpositive observer cap is false. Set M=14,z=1/8, and let y be the unique
root in the rational interval

             13828/100000<y<13829/100000

of

                 324945y^2-919862y+120986=0.            (13)

Set

 x3=y, x2=1/8,
 x0=(53y+6)/(107-45y),
 x1=(2539y+960)/(11179-7200y),
 q_i=x_i/(1+x_i).                                    (14)

The quadratic is positive at the left endpoint and negative at the right,
and its derivative is strictly negative there. This selects one exact real
y. The denominator signs are positive, and direct substitution gives

 g0=0, g1=0, g3=0.

Exact rational interval bounds give

 13225/100000<x0<13228/100000,
 12874/100000<x1<12877/100000,
 0.03596<g2<0.03660.

Every native cap is strictly positive. In particular the four normalized
Never payoff numerators have the rational lower bounds

 P0/H0>2279/100000,
 P1/H1>131/1000,
 P2/H2>3143/12500,
 P3/H3>803/6250.                                     (15)

The accompanying standard-library checker verifies these signs and the
three exact contact identities using rational polynomial arithmetic.

This is an ACTUAL one-date finite profile, followed by Never. Every player
has positive marginal Never mass; all full caps are positive and ALL-END;
all observer debts are zero; the pivot has strictly positive debt. Thus
positive caps cannot exclude F even for a one-date actual tail.

One can additionally satisfy the displayed scalar source inequalities
without global minimization. Put nu=product_i(1-q_i), r=1/20, and write
b2=P2/H2. Since q2H2=nu z and H2=nu(1+z),

 d2=nu z g2, J_r=nu(r+z g2),
 B2=nu(1+z)b2, U2=nu[(1+z)b2-z g2].

The exact interval checks give

 0<J_r<r, B2>J_r, U2>r nu,
 N2=8/9 < 1/(1+r*13/11).

Here13/11 is the sum of the positive inverse column Gamma^-1 e2.
No relation between this chosen r and the table's unknown absorbing
partial-Nash minimum m is asserted. The
[one-date global descent](CODEX_COORDINATOR__FINITE_GLOBAL_DESCENT.md)
proves that this profile is NOT globally minimizing for any r>0.
It remains a precise barrier to purely local exclusions: the last-root constraints,
positive caps, positive Never masses, observer optimality, and these scalar
inequalities do not by themselves eliminate F. Any exclusion must use a
further global variational argument or another genuinely stronger property.

### 5. Complete M14 sign partition of the last-root curve

For M14 the last scalar filter can be removed explicitly. Define

 R(z)=33173125z^8+1623635000z^7+12936067000z^6
      -15895969500z^5-307529649300z^4-629973729300z^3
      -333138223960z^2+40832208960z+1080998816,
 C0(z)=125z^6+3875z^5+625z^4-510200z^3
       +936360z^2+7107160z-1094208,
 C3(z)=2375z^6+38750z^5+137825z^4+320325z^3
       -506370z^2-597660z+476672.

Let alpha be the unique zero of R in(0,1), rho0 the unique zero of C0
in(0,1), and rho3 the unique zero of C3 in(0,3/4). Exact isolations are

 3/25<alpha<121/1000<1/8<3/20<rho0<4/25
             <3/5<rho3<7/10<74/100<z_*<3/4.

The complete admissible full-support branch is exactly

                     alpha<=z<z_*.

On this branch the two caps P1,P2 are always positive, P0 is
positive exactly for z<rho0 and zero at rho0, and P3 is positive exactly
for z<rho3 and zero at rho3. In particular the complete all-positive-cap
admissible full-support subbranch is exactly[alpha,rho0).

Here is an exact proof requiring only polynomial arithmetic and sign rules.
Clear the positive denominators h-Ly,d-ey in the quadratic contact
equation(11), g2, and the four cap numerators. Eliminating y by a resultant
gives, after discarding factors z,z+1,5z^2+70z+84 that never vanish on this
branch, respectively R,C0,C1,C2,C3, where

 C1=475z^6+7750z^5+60245z^4+97695z^3
       +4062z^2-11916z+49248,
 C2=3500z^6+2960500z^5+120049675z^4+357877500z^3
       +421691860z^2+225435280z+34281968.

The supplementary exact checker verifies these resultant identities.
C1>0 on z>=0 because the quadratic last three terms have negative
discriminant -658190448; C2 has all positive coefficients. R has precisely
two coefficient sign changes. Its signs at3/25,121/1000,1,5 are+,-,-,+,
so Descartes' rule gives exactly one positive root below1 and exactly one
above1. C0'>0 on[0,1], since its sole negative derivative term is bounded
below by-1530600 while the constant derivative term is7107160. C3'<0 on
[0,3/4], since

 C3'(z)<=(13356105/128)z-597660<0.

The displayed rational brackets are direct evaluations. The limits at the
origin, obtained by linearizing the three observer contact equations, are

 (x0,x1,y)/z -> (405,336,566)/379,
 g2/z -> -3142/379,
 (P0/H0,P1/H1,P2/H2,P3/H3)/z -> (417,540,511,448)/379.

At z=z_* the pivot gap is positive and P0 is negative. Also P3 is negative:
its boundary formula is

 P3/H3=z(25z^2-150z+116)/[(5z-14)(5z+4)]<0

for74/100<z<3/4. Continuity forces each of the indicated unique zeros to
occur on the legal contact branch, while the resultant excludes any other
zeros. This proves every stated sign interval without selecting numerical
solutions or asserting a global minimum.

## Global-minimum first-root restrictions

This uses genuine global minimality, unlike the local last-root controls.
It is a necessary partition, not exclusion of the finite-clock branch.
No new source realization or minimum attainment is asserted.

Fix the no-child benchmark with M>11, native own singleton0, participant
reward t=M-1 on the cycle2->0->1->3->2, participant reward-5 otherwise,
and passive nonsingleton reward0. Select the canonical pivot2. Suppose
an ACTUAL global minimum P of J_r=d2+r nu on the exact-observer carrier is
given, with value mu. Retain the universal source conclusions

 0<mu<r<m, observer caps B_i>=0, B2>mu, every Never mass positive,
 every observer has zero debt, and all players are ALL-END.

Here m is the absorbing exact-observer minimum. The tail after any finite
cut has zero observer debts and is an admissible competitor for J_r, even
though it need not itself minimize and its caps may be negative.

For this benchmark, EVERY minimum has all caps strictly positive without
any row-distinctness assumption. Indeed, if the zero-observer set
T subset{0,1,3} is nonempty, select its latest member j in the chain
0->1->3. For every other i in T, the joining increment
L_ij=Z_i(ij)-Gamma_ij is strictly negative: the only relevant entries are
L01=-4,L03=-7,L13=-6. Prepend a sufficiently small solo-j root. Player j
is indifferent because its own singleton and continuation cap are zero;
other zero observers strictly Continue; positive-cap observers and the
pivot strictly Continue for small enough hazard. This is an exact-observer
prefix, and since the pivot remains quiet both d2 and nu multiply by its
common survival1-epsilon. It produces J_r=(1-epsilon)mu<mu, a contradiction.
The argument works at EVERY minimum, including every selected minimum
in the compact one-root slice below. No perturbation of the benchmark is
used, and repeated higher-coalition rewards cause no difficulty.

**First-support theorem.** After deleting initial empty dates, the first
occupied root of P has support exactly02,012,or0123. If P has finite
supports, it can be replaced by another actual finite-support global
minimum whose first support still belongs to this list and which, in the
02 case, satisfies both

 observer1 is indifferent at that date although q1=0,
                         mu>=6q2.                     (1)

At either first support02 or012, one also has

                  mu>5q2/(1-q2), hence q2<r/(5+r).    (1a)

In the selected02 case q2<r/6 as well. The same selection argument works without the finite
support assumption; finiteness is preserved when it is present.

### Positive caps force a cycle prefix

At the first root, an active observer i receives its immediate Quit payoff
Q_i=B_i>0. Its only positive native participant reward is the designated
pair with predecessor(i). All other participant rewards are nonpositive,
including the own singleton0. Hence predecessor(i) must also have a
positive current hazard. Iterating backwards around2->0->1->3->2 shows
that every nonempty support containing an observer is02,012,or0123.
The only other possible nonempty support is the pivot singleton2.

That singleton cannot occur at a global minimum. Write q=q2, and let
B2^T,U2^T,nu_T,J_T be the corresponding tail quantities. Pivot opponents
all Continue in this first round, so B2=B2^T>mu. The pivot's current Quit
payoff is0 and its prescribed payoff is(1-q)U2^T. Consequently

                 mu=q B2+(1-q)J_T.

The tail is exact-observer feasible, so J_T>=mu. Since q>0 and B2>mu,
this gives mu>mu. Thus the first occupied support is one of the three
claimed cycle prefixes. Empty initial dates have no effect on any tuple.

### Selecting a tight next observer in the pair case

Suppose the first support is02. Fix q=q2 in(0,1) and the entire actual
conditional tail, and vary only alpha=q0. Observer0's two root endpoints
are independent of its own hazard, so its exact indifference is preserved.
Its root cap remains the same positive constant. The other observers remain
quiet provided their Continue endpoints dominate their Quit endpoints.
The set of alpha in[0,1] for which the resulting actual profile is an
exact-observer global minimum of value mu is nonempty and compact: all
root endpoints, prescribed values, caps and Never masses are continuous,
and the exact-observer constraints are closed. Choose its largest alpha.

This selected alpha cannot equal0: its profile would have a pivot-only
first occupied root, already excluded. It cannot equal1: the profile would
absorb surely, and its objective would be at least m>mu. Thus0<alpha<1.
Every selected profile is still an actual global minimum, so its source
cap conclusions continue to hold.

If observer1's quiet inequality were strict, all other relevant inequalities
would be strict too. Observer3 cannot obtain its positive pair premium
because predecessor1 is quiet; hence Q3<=0<B3. The pivot likewise lacks
its premium predecessor3, so Q2=-5alpha<0<B2. Near the selected alpha,
all observers stay optimal and the pivot's Continue cap is its full cap.
In that neighborhood the objective is affine in alpha. A local minimum
of an affine function at an interior point makes it constant. Increasing
alpha slightly would therefore produce another global minimum, contrary
to its maximal choice. Observer1 must be indifferent.

This variation changes only the first root and keeps the conditional tail
fixed. It uses independent private hazards and preserves the finite-clock
property. It neither conditions a global minimum into another minimum nor
silently preserves a positive cap at an arbitrary tail.

### The exact objective bound

Let c=B2^T be the fixed pivot tail cap and k=J_T its tail objective. As long
as the pivot Continue endpoint remains its cap, direct root recursion gives

 B2(alpha)=alpha+(1-alpha)c,
 Q2(alpha)=-5alpha,
 J(alpha)=(1-alpha)[q c+(1-q)k]+6q alpha.             (2)

These use Gamma20=1 and the participant reward Z2(02)=-5.
At the selected pair minimum, observer1 is indifferent. Its joining gap
is strictly increasing in alpha, so decreasing alpha preserves its quiet
inequality. Here is an exact sign check, which does not assume a positive
tail cap. Write b=B1^T, z=q/(1-q). The joining gap is

 g1(alpha)=(1-q)[M alpha-(1-alpha)b]-(6-alpha)q.

At g1=0,

 partial_alpha g1=(1-q)(M-5z)/(1-alpha)>0.

Indeed B1=Q1=t alpha(1-q)-5q>0 gives t alpha>5z and hence
5z<t<M. All other root inequalities are strict as above. Thus sufficiently
small decreases of alpha are feasible exact-observer variations.
Global minimality and the affine formula(2) imply

 6q-[q c+(1-q)k]<=0.

Taking the convex combination in(2) yields mu>=6q. Since mu<r, this gives
q<r/6 and proves(1).

### The tail comparison and the next inward direction

At any first root with support02 or012, the pivot's premium predecessor3
is absent. Write H=product_(i!=2)(1-q_i), c_root=(1-q2)H. Then
Q2=-5(1-H), and ALL-END gives the exact debt recursion

 mu=q2(B2-Q2)+c_root J_T,          J_T>=mu.

Since B2>mu and 1-H>0, this implies

 mu(1-c_root)>q2 mu+5q2(1-H),
 mu(1-q2)>5q2,

which proves(1a). This uses global optimality of the complete source,
not an optimality claim about its conditional tail.

The selected02 minimum also has a concrete one-sided inward test. Put
a=q0/(1-q0), z=q2/(1-q2), c=B2^T and k=J_T. Let b=x1 increase from0,
keeping the conditional tail and all observer contacts fixed. If v0,v1
are the fixed observer tail caps, their exact root contacts are

 v0=Mz-(4+5z)b,              v1=(M-5z)a-6z.

Thus z(b)=(v0+4b)/(M-5b) and a(b)=(v1+6z(b))/(M-5z(b))
are a feasible local branch, since M-5z>0 at the selected pair root.
Observer3 and the pivot retain strict Continue inequalities. At b=0,
write

 eta=z'(0)=(4+5z)/M,
 xi=a'(0)=(6+5a)eta/(M-5z).

The exact objective along this branch is

 J(b)=[k+z(c+6a+7b+5ab)]/[(1+a)(1+b)(1+z)].

Its nonnegative right derivative gives the rational necessary inequality

 eta(c+6a)+6z xi+z(7+5a)
 >=mu[(1+z)xi+(1+a)eta+(1+a)(1+z)].                 (3)

This does not exclude02. In fact, if mu=6q2, then B2=(c+a)/(1+a)>mu
forces the numerator of J'(0) to exceed

 5a eta+z(1-a)=z+a[20/M+z(25/M-1)]>0

whenever11<M<=25. Therefore activating the next observer strictly raises
the objective at this lower-bound equality. The exact KKT test(3), rather
than an unsupported improvement claim, is the surviving conclusion.

### Combined finite-branch partition and limits

The independent last-root classification says that a nonempty final root
can have support only012 or0123. Combining it with the selected first root
above leaves six possible first/last support pairs: first02,012,0123 and
last012,0123. The first02 case has the additional exact contact and bound(1).
Intermediate dates and their number remain unrestricted. These are necessary
endpoint restrictions, not six solved strategy classes or a bound on the
number of phases. The
[one-date global descent](CODEX_COORDINATOR__FINITE_GLOBAL_DESCENT.md)
excludes the entire one-occupied-date actual minimum class, including the
positive-cap control. Every remaining finite minimum has at least two
occupied dates. Applying that variation to a descendant still requires
pricing its earlier head; the longer finite branch remains open.

The same canonical proof now excludes first02 at exactly two occupied dates
for every r>0, and first012 for the selected r=m/2. The latter uses the
existing inverse-axis bound m<=11/156, together with exact first-root
monotonicity and the quiet observer's comparison. The full-first/triple-last case also fails: positive first Quit payoffs
give root survival>25/324, while the triple last debt exceeds1/2; their
product exceeds11/312>=r. Thus only full/full remains at two occupied dates.
For three or more dates the original six endpoint pairs remain necessary.
No feasibility claim is made for any surviving pair.

## Exact four-owner local profiles

This is an ordinary mathematical local construction, not an equilibrium
existence theorem for the original shifted game and not a global-minimum
source. It proves that the surviving I4 pattern cannot be excluded from
ALL-END, zero observer debt, positive Never masses and small-tail contact
conditions alone. At M14 a stronger construction below has zero debt for
all four owners and strictly positive native caps.

### Statement and native table

Fix any M>11 and put t=M-1. Use the native table with singleton matrix

    Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0].

Own singleton and Never rewards are zero. Every nonsingleton participant
reward is -5 except the premium t on the four successor pairs of the
cycle `0 -> 1 -> 3 -> 2 -> 0`; every passive nonsingleton reward is zero.
Let J be the participant pair matrix, with zero diagonal:

    J=[0,-5,t,-5; t,0,-5,-5; -5,-5,0,t; -5,t,-5,0].

For this exact table there is epsilon>0 and a C2 curve of hazard vectors
`q(s)`, 0<=s<=epsilon, with q2(s)=s, such that for each 0<s<=epsilon
the actual profile using

    q(n)=q(lambda^n s), n=0,1,...,
    z=1/(2M), lambda=1-z,

has all four hazards strictly positive at every date, strictly positive
Never masses, and the following full behavioral properties:

- Every observer i in O={0,1,3} is indifferent between every finite date
  and Never. Its prescribed payoff equals its full response cap.
- Pivot2 strictly prefers Never to every finite deadline. Its prescribed
  law has strictly positive debt.
- Every conditional whole tail has these same properties.

Thus this is an exact executable I4 tail, not merely a formal linear cone
or a profile whose observer debts are small. No positive absorbing gap is
asserted, and no claim places it in a globally minimizing fibre.

### Positive tangent and expanding observer block

Let H=Gamma-zJ and v=H^-1 e2. At z=1/(2M), direct cofactor expansion gives

    det H=(167M^4+1812M^3+3336M^2+1532M-451)/(16M^4)>0.

The entries of adj(H)e2, with common denominator 8M^3, are

    (2M+5)(25M^2+5M-29),
    (2M+5)(26M^2+54M+15),
    28M^3+M^2+24M+130,
    47M^3-11M^2-116M-101.

They are strictly positive for M>11. Normalize `h=v/v2`, so h2=1.
Then `(Gamma-zJ)h=e2/v2` and h is strictly positive.

The observer principal block J_OO is invertible, with determinant
`-5(t^2+25)`. Define

    A=I-J_OO^-1 Gamma_OO.

The characteristic polynomial of I-A, multiplied by its positive
denominator, is

    5(t^2+25)u^3+(2t^2+10t+25)u^2+4t u+1.            (1)

Its coefficients are positive, and

    (2t^2+10t+25)(4t)-5(t^2+25)
       =8t^3+35t^2+100t-125>0.

Consequently all roots of(1) have negative real parts. For completeness,
if a cubic with positive coefficients has a conjugate root pair x+-iy
with x>=0, its remaining root is -b with b>0. Writing its normalized
coefficients as c2,c1,c0 gives
`c2 c1-c0=-2x[(b-x)^2+y^2]<=0`, contrary to the displayed inequality.
Nonnegative real roots are excluded by positive coefficients directly.
Thus every eigenvalue of A has real part greater than one. In particular
there is a vector norm in which `||A^-1||=kappa<1`.

### Exact contact map and a contracting graph equation

For a root hazard q near zero, write

    H_i(q)=prod_(j!=i)(1-q_j),
    P_i(q)=H_i(q) sum_(j!=i) Gamma_ij q_j/(1-q_j),
    Q_i(q)=-5(1-H_i(q))+(M+4)H_i(q)
                                  q_pred(i)/(1-q_pred(i)).

P_i is the native passive offer and Q_i the native forced-Quit offer.
These are exact multilinear polynomials. An observer active at consecutive
roots is indifferent exactly when

    Q_i(q)=P_i(q)+H_i(q) Q_i(q_next).                 (2)

Prescribe `(q_next)2=lambda q2`. Since the derivative of Q_O with respect
to q_O at zero is J_OO, the finite-dimensional implicit function theorem
solves(2) uniquely for

    (q_next)_O=F(q2,q_O)=A q_O+b q2+R(q2,q_O),
    b=J_OO^-1(z J_O2-Gamma_O2), R=O((|q2|+|q_O|)^2).

The positive vector h satisfies `lambda h_O=A h_O+b`. Seek an invariant
graph `q_O(s)=h_O s+u(s)`. Its exact equation is

    u(s)=A^-1[u(lambda s)-R(s,h_O s+u(s))].            (3)

On C2 functions with u(0)=u'(0)=0 use the norm formed by
`sup |u(s)|/s^2`, `sup |u'(s)|/s`, and `sup |u''(s)|`, with the vector norm
above. The linear composition term in(3) has norm at most kappa lambda^2.
The nonlinear difference has norm O(epsilon): R has zero value and first
derivative at the origin, and direct differentiation through order two
gives this bound on a fixed bounded ball. The fixed quadratic forcing has
finite norm. Choosing the ball sufficiently large and then epsilon small
makes(3) an invariant strict contraction. This proves a unique C2 graph
with `u(s)=O(s^2)`, without an unproduced stable-manifold input.

After decreasing epsilon, every component of q(s) lies strictly between
zero and one for s>0. The exact graph identity proves(2) at every date of
the prescribed infinite calendar. The sum of all hazards is finite, so
each player has positive Never mass and infinitely many positive finite
atoms. Its conditional law after date n is the same construction starting
at `lambda^n s`.

### Complete-response verification

Fix an observer i. Equation(2) says that immediate Quit and Continue with
next value `Q_i(q_next)` agree. The annotations Q_i tend to zero at the
tail. Iterating the Continue recursion therefore proves that pure Never
has value exactly `Q_i(q(s))`: the remainder is bounded by the supremum
of the annotations beyond a late date and tends to zero. Iterating until
any finite deadline gives the same value. Every private mixed replacement
is an average of these finite/Never responses, so its full cap equals
that value. Fubini then identifies its prescribed payoff with the cap.

For pivot2, let W2(s) denote its actual Never payoff. The remaining finite
mass of player j satisfies

    f_j(s)=s h_j/z+O(s^2).

The error is uniform because the quadratic graph remainder and the
probabilities of two or more finite clocks have summable geometric bounds.
Only singleton passive outcomes contribute to first order, so

    W2(s)-Q2(q(s))
       =(s/z)[(Gamma-zJ)h]_2+O(s^2)
       =s/(z v2)+O(s^2)>0.                           (4)

This holds at every conditional date after one uniform decrease of epsilon.
Comparing a finite deadline with Never discards the identical earlier-exit
outcomes and multiplies(4) by the positive opponent-survival probability.
Thus Never strictly dominates every finite deadline. Its payoff is the
full response cap; the pivot's positive finite atoms give strictly positive
prescribed debt. Arbitrary private mixed deviations are again priced by
averaging. This completes the actual-tail statement.

### Scope of the obstruction

At M14 the selected tangent is proportional to
`(4565484,5421108,2169832,3502436)`. Its observer0 cap has negative leading
coefficient, since the numerator of `(Jh)_0` is -16409904. This explicitly
distinguishes the constructed small tail from a positive-cap global minimum.
Such negative descendant caps are permitted by the actual-source reduction.
The construction does not preserve an inherited head's observer caps and
does not produce a variation inside that head's minimizing fibre.

### At M14: exact native Nash, positive caps, and four infinite owners

At M14 even positive native caps are compatible with an actual full-contact
I4 profile. Put

    p(z)=13611z^4+248z^3-1076z^2-204z-11.

It has exactly one positive root r by its single coefficient sign change.
Exact substitution gives `p(349/1000)<0<p(7/20)`, so
`349/1000<r<7/20`. This is the positive singularity of Gamma-rJ.
Its positive nullvector can be chosen as

    w0=(5r+1)(209r^2+57r+4),
    w1=(5r+1)(155r^2+64r+5),
    w2=970r^3+493r^2+52r+1,
    w3=1747r^3+457r^2+57r+3.

These are adj(Gamma-rJ)e2. Every component is strictly positive.
Let `A4=I-J^-1 Gamma`. It has eigenvector w with eigenvalue
`lambda*=1-r` in (13/20,651/1000). Its other three eigenvalues have real
parts greater than one. To verify the latter assertion without a numerical
spectrum, factor

    p(z)=(z-r)(13611z^3+Bz^2+Cz+E),
    B=248+13611r, C=-1076+rB, E=11/r.

The bracket on r gives B>4998, C>668 and `13611E<429000`, hence
`BC>4998*668>13611E`. The positive-coefficient cubic criterion proved
above puts all three remaining z-roots in the open left half-plane.
The corresponding A4 eigenvalues are 1-z, proving the claim.

The full contact map is well defined near zero: solve

    Q(q_next)=(Q(q)-P(q))/H(q)

coordinatewise on the right. Since `det J=-13611`, the map is analytic
and has the form `q_next=A4 q+R4(q)`, with R4 quadratic at zero. Choose a
vector norm with `||A4^-1||=kappa4<1/(lambda*)^2`; this is possible because
the inverse spectral radius is `1/lambda*<1/(lambda*)^2`. Equation

    u(s)=A4^-1[u(lambda* s)-R4(w s+u(s))]

is then exactly the same weighted C2 contraction as(3). It constructs
`q(s)=w s+O(s^2)>0` and the actual calendar `q(n)=q((lambda*)^n s)`.
The complete-response argument above now applies to every player. All
finite deadlines and Never are exact full maximizers, all four prescribed
debts are zero, and every conditional tail is ALL-END.

All four native caps are strictly positive for small s. Their leading
vector is Jw. Its entries at r satisfy

    (Jw)0=1749r^2-54r-27>167,
    (Jw)1=8(209r^2+57r+4)>0,
    (Jw)3=8(155r^2+64r+5)>0,
    r(Jw)2=(Gamma w)2=848r^3+987r^2+198r+11>0.

The first bound uses `r>349/1000` in its positive quadratic term and
`r<7/20` in its negative linear term. Thus these are exact signs.

This strengthens the local obstruction, but does not produce a global
minimum. Indeed its Never product satisfies

    nu(s)=1-s sum_i w_i/r+O(s^2),

so increasing a sufficiently small s strictly decreases every objective
`d2+rho nu=rho nu`, for rho>0, on the full zero-observer-debt carrier,
which imposes no fixed observer caps. No point in a sufficiently small open
piece of this family is that original global minimum. This makes no
comparison inside an inherited head's fixed-cap fibre. Nor does native Nash prove
UE for the original table `4+Z`: the exact raise identities make every
player's debt in that shifted game equal to `4 nu(s)>0`. The construction
does not place a continuation after infinitely many dates and does not
assert that repeating this positive-Never profile preserves Nash.

Both exact constructions show why a future I4 exclusion must use additional
global-minimum information, rather than claiming that local contact,
ALL-END, or even positive-cap native Nash conditions are inconsistent.

## Global restrictions on the eventual full-support I4 branch

The [fixed-cap controlled-window theorem](../exports/FIXED_CAP_CONTROLLED_WINDOW_MINIMUM_EXCLUSION.md)
now supplies such a global comparison. At every sufficiently late fixed
window passing its control-rank test, some marked pivot date must be tied.
It preserves all four entrance full caps, so an arbitrary earlier history
does not obstruct this particular variation. Tied unmarked dates are kept
exactly tied.

For every M>=14, an actual minimum with eventual full support therefore has
geometrically decaying remaining finite masses. At M14, strict pivot-Never
dates must further have zero upper Banach density. The finite rank and
curvature checks, the entire premium-ray polynomial certificate, and the
all-power spectral arithmetic are reproduced by
[one exact checker](../experiments/CODEX_NO_CHILD__CONTROLLED_WINDOW_CHECK.py).
The complete proof has two independent whole reviews linked from the
portfolio. No inference eliminates all-contact tails, sparse owner
calendars, or inherited endpoints. The unresolved long-window extension
requires control of normal multipliers in addition to geometric tail decay.

## Verification and retained scope

The original complete-pattern checker remains
[the stationary/sure-root certificate](../experiments/CODEX_NO_CHILD__BENCHMARK_EXACT_CHECK.py).
The [positive finite control](../experiments/CODEX_NO_CHILD__POSITIVE_LAST_ROOT_CHECK.py)
uses standard-library rational arithmetic; the
[complete M14 last-root partition](../experiments/CODEX_NO_CHILD__LAST_ROOT_PARTITION_CHECK.py)
uses exact SymPy polynomial arithmetic. Run each with Python3.

Independent component reviews cover the
[original raw benchmark and selector comparison](../feedback/NO_CHILD_FIN4_BENCHMARK__BY_TOPOLOGY.md),
the [complete last-root algebra](../feedback/NO_CHILD_FIN4_BENCHMARK_LAST_ROOT__BY_ADVERSARY.md),
the [global first-root surgery](../feedback/NO_CHILD_FIN4_BENCHMARK_FIRST_ROOT__BY_LASTROOT.md),
and the [four-owner actual controls](../feedback/NO_CHILD_FIN4_BENCHMARK_I4__BY_FRESH_REVIEW.md).
Their exact source hashes identify the mathematical components assembled
here; only headings and canonical references were changed in assembly.
The general support theorem has its separate full review.
The [consolidated scope review](../feedback/NO_CHILD_FIN4_CONSOLIDATION__BY_SECOND_REVIEW.md)
checks the combined benchmark and general support theorem before the
additional cap-region cross-reference above.

No result here proves global-minimum realization for a local control,
positive absorbing gap, a UE counterexample, or arbitrary Fin4 closure.
The next finite obligation is a whole-profile variation for at least two
occupied dates; the inherited branch requires a replacement respecting the
head's full observer comparisons. The one-date result and its exact
certificate have a
[fresh whole-proof review](../feedback/ONE_DATE_GLOBAL_DESCENT__BY_FRESH_REVIEW.md).
