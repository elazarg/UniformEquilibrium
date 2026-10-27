# A no-child benchmark with exact stationary and sure-root exclusions

This is a benchmark and a coverage audit, not a counterexample to UE.
The M=14 table below has an exact finite certificate excluding every
stationary terminal Nash profile and every sure-first terminal Nash profile
with arbitrary behavioral continuation. Several complete raw producer
families also fail. Arbitrary nonstationary strategies remain unresolved. The
[complete finite-mode theorem](../exports/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14.md)
excludes every finite-calendar actual selected minimum for sufficiently
small selectable penalties, without a bound on the number of dates.
Together with the four-owner support theorem, it leaves only I4 on the
actual side. Eventual full support then forces a finite head followed by
a native Nash tail. Inherited semantic endpoints remain a separate branch.

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
[complete finite-mode theorem](../exports/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14.md)
excludes finite actual source minima for sufficiently small selectable
penalties. This control remains a precise barrier to purely local exclusions:
the last-root constraints,
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
These are necessary endpoint restrictions at an arbitrary prescribed penalty,
not six strategy classes or a bound on the number of phases. The
[complete finite-mode theorem](../exports/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14.md)
now removes the entire finite actual branch when the source penalty is chosen
sufficiently small. Its compactness argument handles unbounded calendar
lengths: last roots approach the unique nonempty native Nash root; its cap
forbids a nonempty Nash prefix; an intervening pivot-only block cannot evade
that obstruction. A produced semantic tail supplies the remaining one-date
descent. The theorem uses global minimality at the entrance, never at a
conditional tail.

The penalty remains selectable throughout `0<r<m`; the result gives one
range `0<r<min(m,r0)`, not a new bound at the specific choice r=m/2. No
actual-source realization or inherited-endpoint replacement is inferred.

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
geometrically decaying remaining finite masses. The finite rank and
curvature checks, the entire premium-ray polynomial certificate, and the
all-power spectral arithmetic are reproduced by
[one exact checker](../experiments/CODEX_NO_CHILD__CONTROLLED_WINDOW_CHECK.py).
The complete proof has two independent whole reviews linked from the
portfolio.

At M14, the stronger
[eventual native Nash-tail theorem](../exports/EVENTUAL_NATIVE_NASH_TAIL_AT_ACTUAL_M14_MINIMUM.md)
excludes infinitely many strict pivot dates. Its uniform storage estimate,
finite regular anchor and compact normal-multiplier argument handle windows
of arbitrary length. Thus eventual full support forces a finite head followed
by an actual native Nash tail, with positive Never mass. The earlier
zero-density result is subsumed here. Sparse owner calendars, the finite
head before that Nash tail, and inherited endpoints remain unresolved. The
[adversarial](../feedback/EVENTUAL_NATIVE_NASH_TAIL_AT_ACTUAL_M14_MINIMUM__BY_ADVERSARY.md)
and [fresh](../feedback/EVENTUAL_NATIVE_NASH_TAIL_AT_ACTUAL_M14_MINIMUM__BY_FRESH_REVIEW.md)
reviews cover the complete frozen proof.

## Canonical tails, calendar compression and finite-head transversality

These ordinary mathematical lemmas refine the M14 actual-source branch.
They do not exclude finite heads followed by native Nash tails, or prove UE.

### Empty dates can be removed without changing an ALL-END source tuple

Delete every date at which all four prescribed hazards vanish, preserving
order and simultaneity at the retained dates. Pushing forward the four
independent stopping laws preserves their terminal outcome law and Never
atoms, hence U,e,N. Every compressed unilateral response lifts to the original
retained dates, so B_compressed<=B_original. With finitely many retained dates,
a response after the last one lifts to any later original date; sole-Quit
native payoff is zero. Since Never attains e=B_original and e is unchanged,
B_compressed>=e=B_original as well. Thus the full augmented tuple is unchanged.
In particular an actual ALL-END global minimum remains the same minimum.

Apply the [eventual-contact theorem](../exports/EVENTUAL_NATIVE_NASH_TAIL_AT_ACTUAL_M14_MINIMUM.md)
to this compressed calendar. Its eventual-full-support case has a finite head
followed by full native Nash. The remaining sparse case therefore requires
infinitely many NONEMPTY proper-support dates; inserted blank dates do not
create another residual mode. No finite-horizon time bound is transported.

### Every late full-contact, full-support tail is canonical

Use the actual C2 full-contact curve constructed above and the M14 root maps.
The local analytic forward map is T(q)=Q^-1(H(q)^-1[Q(q)-P(q)]), with
DT(0)=A=I-J^-1 Gamma. The cited theorem's exact spectrum gives one stable
real eigenvalue lambda in(13/20,2/3), one real eigenvalue u>1, and a nonreal
pair of modulus R>u. Rescale the curve's positive amplitude so that

    q(0)=0, q'(0)=h>0, sum h=1-lambda,
    T(q(s))=q(lambda s), Gamma h=(1-lambda)Jh.                 (C1)

This EXISTING construction contains every sufficiently late actual
full-contact, full-support tail. Indeed choose a left lambda eigenfunctional
ell with ell(h)=1 and unstable invariant complement U. Reparametrize the
curve by t=ell(q(s)), writing q_graph(t)=ht+chi(t), chi in U. In coordinates
q=q_graph(t)+z, z in U, invariance and differentiation give
z_next=A_U z+b(t,z), where b(t,0)=0 and D_z b(0,0)=0. Choose an equivalent
norm with ||A_U^-1||<1. On a small neighborhood |b(t,z)|<=delta|z| therefore
implies |z|<=c|z_next| for one c<1. Positive Never mass gives q_n->0; iterating
on its actual contact orbit yields z_n=0. Injectivity of the curve then gives,
after a finite cut K, q_n=q(lambda^(n-K)s) for one s>0.

Write e(s)=Q(q(s)) and nu(s)=prod_(n>=0)prod_i[1-q_i(lambda^n s)]. Contact
recursion telescopes: every finite deadline and Never has payoff e_i(s),
hence this is native Nash against all behavioral deviations. The logarithmic
product and its first two derivative series converge uniformly, so nu is C2.
With w^T=1^T Gamma^-1 the normalization gives

    e'(0)=Jh, nu(0)=1, nu'(0)=-1, w^T e'(0)=1.               (C2)

Thus the eventual-full-support actual branch, after calendar compression,
has a finite head followed by this one-parameter family. Positive Never
mass remains; native Nash is not UE for the shifted original table.

### A free amplitude still leaves late fixed-cap windows isolated

Use the cited theorem's analytic backward chart q=Psi(t,g),
F(t,g)=Q(Psi(t,g))+g e2, defined by Q(q)-P(q)-H(q)t+g e2=0. At zero,
M=F_t=J(J-Gamma)^-1 and b=F_g=-Gamma(J-Gamma)^-1e2. On the canonical tail
set M_n=F_t(e(lambda^(n+1)s),0), b_n=F_g(e(lambda^(n+1)s),0).
They converge geometrically. The proved spectrum and asymptotic conjugacy
produce a nonzero real homogeneous adjoint z_(n+1)=M_n^T z_n with
z_n=(1/u)^(n-K)[z_*+o(1)], where z_* is a 1/u eigenvector of M^T.
The proved cyclicity gives b^T z_*!=0. Choosing its sign and a late K gives

    b_n^T z_n>0 for every n>=K.                              (C3)

The amplitude derivative X_n=lambda^n e'(lambda^n s) satisfies
X_n=M_n X_(n+1). Hence z_n^T X_n is constant and, since both factors tend
to zero, is exactly zero. In particular z_n^T e'(lambda^n s)=0.
Fix finite N>K, vary controls g_K,...,g_(N-1)>=0 and terminal amplitude
a near lambda^N s, and let E(g,a) be the backward entrance map. Then

    z_K^T partial_(g_n)E=b_n^T z_n>0,
    z_K^T partial_a E=z_N^T e'(lambda^N s)=0.                 (C4)

A linearized feasible direction fixing E has delta g_n>=0; pairing with
z_K forces all delta g_n=0. Invertibility of M_n and e'!=0 then force
delta a=0. The entire linearized feasible cone is {0}. Consequently this
fixed-entrance point is locally isolated for EACH finite N: normalized
secants of a distinct convergent feasible sequence would contradict that
cone. No uniform neighborhood in N or infinite-dimensional isolation follows.
A useful global variation must also change the head or its cap requirements,
or use a different observer-exact continuation family.

### Exact whole-head transversality, including the boundary term

Take a finite head q_0,...,q_(N-1) followed by canonical amplitude s>0.
Let rho>0 be the source penalty, C=prod_(k<N)prod_i(1-q_i,k),
A_i,k=prod_(k<=ell<N)H_i(q_ell), and A_i=A_i,0. On the ALL-END stratum,

    J(q,s)=J_head(q)+(A_2-C)e_2(s)+rho C nu(s),
    partial_s G_i,k=A_i,k e'_i(s), G_i,k=e_i,k-Q_i(q_k).      (C5)

Indeed tail contributions to pivot Never and prescribed payoff are A_2 e_2
and C e_2; backward Never recursion gives the second identity. Eliminate the
head's zero-hazard coordinates, impose G_i,k=0 at active observers and
G_i,k>=0 elsewhere, and vary the remaining open hazards and s. These are
legitimate ALL-END observer-optimal comparisons. A source minimum is a local
minimum here, so Fritz John gives alpha>=0 and contact prices eta, not all
zero: eta is unrestricted at equality contacts, nonpositive at binding
inequalities and zero at strict inequalities. Interior amplitude stationarity is

    Xi^T e'(s)+alpha rho C nu'(s)=0,
    Xi_i=alpha(A_2-C)1_(i=2)+sum_(k<N)eta_i,k A_i,k.          (C6)

Observer equality prices have no automatic sign. Nor can one invert an
arbitrary head contact Jacobian without checking its rank; the previously
proved chart only guarantees sufficiently late invertibility.
For the storage Phi of the cited theorem, set

    V(s)=rho nu(s)-rho+rho w^T e(s)-Phi(e(s)),
    mu_N=Xi-alpha rho C w+alpha C grad Phi(e(s)).

Then(C6) becomes mu_N^T e'(s)+alpha C V'(s)=0. The boundary term matters:
globally J=V_0+rho-rho w^T e_0+Phi(e_0), so free entrance caps do not allow
minimizing V_0 alone. Formally extend mu by the exact storage adjoint
mu_(n+1)=M_n^T mu_n+alpha pi_n l_t,n, where pi_n is joint survival from the
original entrance and l_t,n the stage derivative including its continuation
cost. Put X_n=lambda^(n-N)e'(lambda^(n-N)s) and
Y_n=lambda^(n-N)V'(lambda^(n-N)s). Differentiated recursion makes
mu_n^T X_n+alpha pi_n Y_n constant, hence zero by transversality.
Since V(s)=O(s^2), Y_n=O(lambda^(2(n-N))). The growing adjoint mode 1/lambda
pairs nontrivially with e'(0), so this identity kills that mode. Remaining
homogeneous modes and geometric forcing decay. This FORMAL extension need
not satisfy the switch inequalities of newly added one-sided gap controls;
compatible multiplier feasibility still needs proof. Even a feasible extension
can retain the decaying real-stable mode(C3).

The open task is a global head comparison or a different continuation family.
These identities alone exclude no finite head or inherited endpoint.

Independent whole review: [canonical tails and head transversality](../feedback/NO_CHILD_FIN4_CANONICAL_TAIL__BY_FRESH_REVIEW.md).

### Canonical-tail amplitude can have an interior minimum after repairing a head

This is an exact obstruction to one proposed descent, not a source-minimum
construction or a UE counterexample. There exists a continuous family of
actual M14 full native Nash profiles, consisting of41 full-support roots
followed by the canonical tail, whose joint Never probability has an interior
minimum as that tail's amplitude varies. Every member has positive caps and
admits no nonempty native Nash prefix. Thus neither monotone amplitude repair
nor a Nash-prefix graft closes the finite-head case.

Let theta be the unique positive zero of

    p(t)=13611t^4+248t^3-1076t^2-204t-11, lambda=1-theta.

Use the positive polynomial vector

    v0=(5theta+1)(209theta^2+57theta+4),
    v1=(5theta+1)(155theta^2+64theta+5),
    v2=970theta^3+493theta^2+52theta+1,
    v3=1747theta^3+457theta^2+57theta+3,
    h=theta v/(sum v).

Exact evaluation gives
34954025/10^8<theta<34954026/10^8,
13/20<lambda<2/3, 3/40<h_i<1/10, (Jh)_i>1/10,
sum h=1-lambda, and Gamma h=(1-lambda)Jh.

We first make the local canonical-tail bounds explicit. With the benchmark's
hazard polynomials P,Q,H, set

    W(q,t)=Q(q)-P(q)-H(q)Q(t)=Lq-Jt+R(q,t), L=J-Gamma.

In each row of R, the sums of absolute coefficients at degrees2,...,6 are
at most133,188,155,70,13 respectively. Direct rational multiplication gives
||L^-1 J||_infinity=2529/1571 and ||L^-1||_infinity=843/1571.
On the complex disk |s|<=epsilon0=1/1000 take the radius4 ball of analytic
u vanishing to order2, with norm sup||u(s)||_infinity/|s|^2. The map

    K(u)(s)=L^-1 J u(lambda s)
       -L^-1 R(hs+u(s),h lambda s+u(lambda s))

is an invariant strict contraction. Both arguments of R are bounded by
a|s|, a=11/100. Writing c_d for the five coefficient bounds above,

    sum_(d=2)^6 c_d a^d epsilon0^(d-2)<2,
    (2529/1571)(4/9)4+(843/1571)2<4,
    (2529/1571)(4/9)
       +(843/1571)sum_(d=2)^6 d c_d(a epsilon0)^(d-1)<.732.

The fixed point gives q(s)=hs+u(s), ||u(s)||_infinity<=4s^2 and the exact
contact recursion q(s),q(lambda s). Positivity and summability produce actual
independent clocks. Telescoping contact shows every finite deadline and Never
has payoff e(s)=Q(q(s)), so all behavioral responses are priced. The local
curve agrees with the canonically normalized curve already constructed above.
The row norm of J is23 and Q's nonlinear coefficient sums are31 and13;
therefore

    ||e(s)-Jh s||_infinity<=93s^2,
    |nu(s)-(1-s)|<=30s^2.                                    (T1)

For the second inequality, summing all four hazard errors gives at most
16s^2/(1-lambda^2)<=28.8s^2. Summing
|log(1-z)+z|<=z^2/[2(1-z)] adds less than.1s^2. Hence
|log nu+s|<=29s^2; exponentiation adds at mosts^2/2.

Now let the exact seed amplitude range over

    I=[65/10^10,75/10^10], s_mid=70/10^10.

Start with the actual seed tail just produced. For each seed, prepend40
small positive solutions of C(x)=e_tail and then one larger positive solution,
where C(x)=Lx-R_old(x) is the exact odds contact polynomial from the benchmark.
At every step set

    e_new=Q_odds(x), nu_new=nu_tail/prod_i(1+x_i).

Each such root is full native Nash against its tail. The finite construction
therefore remains actual full native Nash against all behavioral deviations.
No endpoint is placed after an infinite head.

The accompanying single fail-closed rational interval checker certifies these
41 root maps continuously on ALL of I. Its existence test is explicit: at a
nominated positive center x0 and a fixed rational matrix B, it verifies that
x -> x-B(C(x)-v) maps the root box strictly into itself for every cap v in
the input box, and ||I-B DC||_infinity<1 on that box. Banach gives the unique
root there, and the analytic implicit theorem gives its cap derivative.
The inverse enclosure uses

    DC^-1=(I-E)^-1 B, E=I-B DC,
    |(DC^-1-B)_ij|<=kappa/(1-kappa) max_k |B_kj|.

For the output cap it bounds Q'_odds DC^-1 over the box and integrates from
the verified center cap C(x0). The input box is enlarged to contain this
center cap before applying the mean-value argument. Direct root survival
products propagate nu. All arithmetic used to assert these inequalities is
rational with outward dyadic rounding; floating arithmetic only nominates
centers and cannot make a failed inclusion pass.

The parameter interval is covered by its ten rational subintervals with
endpoints k/10^10, k=65,...,75. At every root depth, a common convex hull of
all ten root boxes also passes ||I-B DC||_infinity<1. Consequently any two
roots there with the same cap coincide, so the branches on neighboring
subintervals glue continuously. The local seed is analytic; thus the complete
actual Nash family is continuous. Its exact three-value certificate is

| Seed amplitude | Joint Never bound |
|---|---|
|65/10^10|nu>5694/10000|
|70/10^10|nu<5689/10000|
|75/10^10|nu>5704/10000|

Continuity and compactness now give a minimum attained strictly inside I.
This is a minimum only along this produced family, not over the source C.

Uniformly on I the same checker gives entrance caps

    e>b0=(1,8,16,8)/100.                                   (T2)

The existing exact inverse A=L^-1 satisfies A b0>(37/1000)1 and
A1>(12/25)1. Any nonempty proper Nash prefix at positive e must have full
support by predecessor closure. A solution C(x)=e would then give, for
t=min x_i,

    t>37/1000+(36/5)t^2,

impossible because the discriminant is-41/625. If j were a sure quitter,
every owner except j and its premium successor would strictly Continue:
every joining increment against a coalition containing j is negative there.
The successor would then strictly Quit, making j's own joining increment
strictly negative and contradicting its sure Quit. Thus sure-quitter Nash
prefixes are impossible as well, for any continuation. No member of this
family admits a nonempty Nash prefix at all.

This refutes monotone canonical-amplitude descent even when the finite head
is repaired exactly and all player debts stay zero. It differs from the
fixed-entrance isolation above: entrance caps vary here. It is also distinct
from generic local/component traps because it occurs inside the exact M14
canonical-tail architecture. It does not show a local minimum against other
head-gap directions, a global minimum in C, positive absorbing gap, or absence
of original-game UE. A nonlocal comparison remains possible.

Exact reproduction: [canonical-head interval checker](../experiments/CODEX_NO_CHILD__CANONICAL_HEAD_TURN_CHECK.py).
Independent [whole review](../feedback/NO_CHILD_FIN4_CANONICAL_HEAD_TURN__BY_INTERVAL_REVIEW.md).

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

The [finite-source checker](../experiments/CODEX_NO_CHILD__FINITE_SOURCE_CHECK.py)
reproduces the native Nash algebra, strict no-prefix certificate and all472
positive Bernstein coefficients for the complete finite-mode theorem. Its
[adversarial](../feedback/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14__BY_ADVERSARY.md)
and [fresh](../feedback/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14__BY_FRESH_REVIEW.md)
reviews cover the entire frozen proof.

No result here proves global-minimum realization for a local control,
positive absorbing gap, a UE counterexample, or arbitrary Fin4 closure.
At sufficiently small penalties the actual branch consists of calendars with
infinitely many nonempty proper-support dates, or finite heads followed by
canonical native Nash tails. The
inherited branch requires a replacement respecting the head's full observer
comparisons.
