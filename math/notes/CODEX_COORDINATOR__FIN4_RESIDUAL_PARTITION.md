# Fin4 residual partition: singleton cells and global source cases

Owner: CODEX_COORDINATOR. Ordinary mathematics; no Lean check. Fin4 remains
open. Sections1–8 reorganize established necessary matrix restrictions into
ten pointed sign templates and explicit polygon tests. Section9 partitions
the actual global source and inherited endpoints; Section10 adds a necessary
raw pair test for one actual-source branch. These are different axes, with
no unproved exclusions between them. None of the ten matrix templates or
the ten global-source cases is universally solved for arbitrary tables.
The [no-child premium family](../exports/NO_CHILD_PREMIUM_FAMILY_UNIFORM_EQUILIBRIUM.md)
has UE for every real M. For M>=11 and its stated unbounded raw completions,
the native absorbing pivot minimum is zero, so none of these positive-gap
source cases occurs there. No source case is universally closed for
arbitrary tables.

The [weighted collision theorem](../exports/WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md)
separately supplies at most43 finite raw existence tests at each fixed
singleton matrix. Its successful regions are removed before attacking the
remaining collision rewards. The [negative-pair return theorem](../exports/NEGATIVE_PAIR_OUTER_DICHOTOMY_UNIFORM_EQUILIBRIUM.md)
closes its entire displayed outside-weight sign split, including equality.
Neither theorem covers all singleton cells or arbitrary collision rewards.

## 1. Scope and generic source

Let Gamma be a real four-by-four zero-diagonal matrix. Work in the generic
stratum where every off-diagonal entry and every principal determinant of
size at least two is nonzero. Assume

1. every column has a negative entry;
2. Gamma is R0 of degree+1;
3. det Gamma>0 and Gamma^-1 has a strictly positive column;
4. there is a mutually negative reciprocal pair;
5. no principal triple T has both Gamma_TT^-1>=0 and
   Gamma_oT Gamma_TT^-1>=0, where o is its omitted owner.

The R0 condition means that x>=0, Gamma x>=0 and x_i(Gamma x)_i=0 imply x=0.
The degree is that of the complementary map x -> min(x,Gamma x), with the
coordinatewise minimum. Its local index at a strict complementary root of
support S is sign(det Gamma_SS).

These are necessary matrix restrictions already supplied by the current
Fin4 source/exit results, not sufficient conditions for a counterexample.
The no-UE source with its exact hypotheses is the strict-column reduction
and the named declarations
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`),
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`),
and the degree and passive-child sources in the
[strict-column reduction](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md).
The original/native reduction is existential: an original counterexample
produces some own-zero table with positive absorbing full-SUM gap, and any
such native table produces an original counterexample by adding1 to every
nonempty terminal reward. Arbitrary terminal-only row subtraction is not a
same-table UE invariance. Native AllNever is always exact Nash.

Genericity loses no route to proving universal UE: a positive terminal-gap
counterexample has a reward neighborhood of counterexamples. Arbitrarily
small changes of the twelve off-own singleton rewards can avoid the finite
collection of zero polynomials defining the excluded entries and principal
determinants. A line toward the matrix with all off-diagonal entries1 shows
that each polynomial is nonzero. If useful, the sixteen inverse entries can
also be required nonzero by avoiding their cofactor polynomials. Thus a
counterexample anywhere would give a generic counterexample; this does not
assert that every individual counterexample is itself generic. The reward
robustness bridge is
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`).

The argument below is purely matrix algebra and degree. In particular its
column normalization is NOT asserted to preserve quitting-game equilibria.

## 2. Produced pointed normal form

Choose any p with v=Gamma^-1 e_p>0. Relabel p as0 and its other owners as
1,2,3, and put H=Gamma diag(v). Then H1=e0. Positive column scaling preserves
all entry signs, principal determinant signs, complementary support tests,
R0 and degree. It also preserves the passive-child test: the scaling cancels
in the product of the outside row with the child inverse. These are algebraic
invariances only; the full reward table is not being transformed strategically.

Write

    H=[0,c; -r,B],      r=B1,      c1+c2+c3=1.       (1)

Here B is the principal observer triple and c a row vector. It is invertible,
and the Schur complement gives the exact identities

    det H=det B>0,
    H^-1=[1,-R; 1,B^-1-1R],       R=c B^-1.          (2)

The lower-left1 is a three-entry column. Conversely any B,c satisfying (1),
with det B>0, gives an invertible H having strictly positive inverse column0.
Thus this is a produced normal form, not an assumed special matrix class.

For a disjoint partition of labeled source matrices, first choose the least
strict inverse pivot in the original player order. Relabel that pivot as0,
then choose the least pair (sign word of B, full numerical word of H) among
the six observer orderings. Ties give identical recorded words. Every witness
in Section5 already has strict pivot0, so all ten pointed templates remain
nonempty for this rule. Without the original-label choice, the results give
a finite pointed cover up to player permutation. An optional minimization
over all strict pivots would disjointify that cover differently and could
leave fewer nonempty canonical cells; no count of ten is asserted for it.

## 3. Degree+1 becomes at most three linear tests in c

For an observer pair i,j, define

    D_ij=c_i r_j/B_ji+c_j r_i/B_ij,
    E={ij: B_ij B_ji>0, r_i/B_ij>0, r_j/B_ji>0}.     (3)

All denominators are nonzero. Generic principal nonsingularity gives
D_ij!=0. At the LCP offset -e0, the full support root is exactly x=1 and
has index+1. Every other possible root has support {0,i,j}. Such a root
exists if and only if ij belongs to E and D_ij>0. Its exact coordinates and
its one inactive slack, with k the remaining observer, are

    x0=1/D_ij,
    xi=(r_j/B_ji)/D_ij, xj=(r_i/B_ij)/D_ij, xk=0,
    w_k=det B/[B_ij B_ji D_ij]>0.                   (4)

Its principal determinant is

    det H_{0ij}=-B_ij B_ji D_ij<0,                  (5)

so its index is-1. Consequently

    degree(H)=1-#{ij in E: D_ij>0};
    degree(H)=1 iff D_ij<0 for EVERY ij in E.        (6)

This tests the entire degree, not a selected root or one favorable support.

Proof of completeness: a support containing0 and one observer is impossible,
because its observer equation is -r_i x0=0 and r_i=-H_i0!=0. The singleton0
fails its target1. A support omitting0 of size at least two has zero target
on its invertible active observer principal, hence x=0. An observer singleton
cannot satisfy all residuals: its column has a negative entry, and if that
negative entry is in row0 it also cannot meet row0's target1. The empty
support fails row0. These exhaust all supports except the full root and the
three triples in (4).

For a triple, its two observer equations give the ratios in (4), and the
pivot equation gives D_ij x0=1. The omitted observer slack simplifies to

 -r_k+B_ki r_j/B_ji+B_kj r_i/B_ij
   =B_ki B_jk/B_ji+B_kj B_ik/B_ij
   =det B/(B_ij B_ji).

Since det B>0, nonnegative slack forces B_ij B_ji>0; it is then strict.
This proves (4)-(5). Every admitted root is strict and regular, so the exact
degree-sum formula applies. R0 also follows directly from negative columns
and principal nonsingularity: a homogeneous support of size>=2 would give a
nonzero principal kernel, while a singleton violates its negative column.

## 4. Complete passive-child selection collapses to one test

Every inverse-positive child containing0 AUTOMATICALLY fails the passive-row
test. Indeed its inverse is positive only if its determinant is positive.
If T omits observer o, block inversion gives

    H^-1_{o0}=-(det H_TT/det H)(H_oT H_TT^-1)_0.

The left side is1 by (2), so the displayed outside inverse weight equals
-det H/det H_TT<0. Thus it is enough to test the one child B omitting0:

    B^-1 is not positive, OR some coordinate of R=c B^-1 is negative. (7)

For a generic zero-diagonal triple, a nonnegative inverse is automatically
strictly positive: every cofactor is a nonzero product of off-diagonal entries.
A positive inverse has cyclic reciprocal-opposition signs and positive
determinant, by the explicit three-by-three adjugate formula. Hence the
argument covers nonnegative as well as strictly positive child selectors.

A useful pivot-switch consequence: if an inverse-positive child exists,
there is a strict inverse pivot INSIDE that child. If a chosen strict pivot
is already inside it, nothing is needed. Otherwise that child is B and its
passive-row failure supplies R_j<0. Formula(2) then makes the entire j-th
inverse column (-R_j, B^-1 e_j-R_j1) strictly positive. This gives a legitimate
alternative algebraic pivot; it does not produce a strategic calendar.

## 5. Ten observer sign templates

Write the six off-diagonal magnitudes of B as a,b,c,d,e,f>0 in the order
(12,13,21,23,31,32). In the following table a sign word specifies their signs.
The symbol c_j in the last column denotes the OUTSIDE row in (1), not the
magnitude c. Each row is one observer-permutation class.

| Case | Signs at12,13,21,23,31,32 | det B | Forced outside inequalities |
|---|---|---|---|
|1|− − − − − +|−ade+bcf|none|
|2|− − − − + +|ade+bcf|none|
|3|− − − + − +|ade+bcf|none|
|4|− − − + + +|−ade+bcf|none|
|5|− − + − + −|ade+bcf|c1<0|
|6|− − + − + +|ade−bcf|c1<0|
|7|− + − + − +|ade−bcf|c3<0|
|8|− + + − − +|−ade+bcf|none|
|9|− + + − + +|ade+bcf|c1<0|
|10|− + + + + +|−ade+bcf|c1<0,c3<0|

These are ten POINTED observer templates, not a claim that there are only
ten full four-player sign patterns. The signs of r and c further distinguish
the full matrices; Section6 gives their exact membership conditions.

Only case8 has B^-1>0 when det B>0. It is the cyclic reciprocal-opposition
triangle; case6 is the transitive reciprocal-opposition triangle. Every
other row has a reciprocal pair of equal signs and therefore cannot have
a positive inverse.

Here is a direct finite classification proof. A reciprocal pair has type
++, --, or opposite; the latter has two orientations. With zero same-sign
pairs there are the two tournaments. With one same-sign pair there are
three attachment orientations for each of ++ and --, hence six classes.
For --, the two orientations in which the outside vertex has both arrows
pointing the same way give positive determinant monomials, and the remaining
orientation gives two negative monomials. For ++ the remaining orientation
gives positive monomials and the other two give negative ones. With two
same-sign pairs there are four classes: both++, both--, or one of each with
either orientation of the remaining pair. All four have opposite-signed
cycle monomials. With three same-sign pairs there are four classes, by the
number of -- pairs; positive determinant is possible exactly when that
number is even. Thus the sixteen classes reduce to eleven with possible
positive determinant. The extra class is all-positive B. Both observer
entries in every such column are positive, so negative columns of H force
all c_j<0, contradicting sum c_j=1. The ten printed templates are exhaustive.

This is not a list selected by numerical sampling. The accompanying compact
exact checker independently enumerates all64 sign words and their16 orbits,
and verifies the eleven positive-possible representatives. It also gives
one exact generic matrix witness for EACH of the ten remaining templates
satisfying all five conditions of Section1. Thus no listed template is an
empty formal case under those matrix restrictions alone.

## 6. The remaining continuous part is a polygon problem for each B

For a fixed B in one template, the exact admissible outside rows c are given
by the following finite conditions on the plane sum c_j=1:

- at least one r_i>0; otherwise column0 has no negative entry; every r_i must also be nonzero;
- c_j<0 whenever both off-diagonal entries of column j of B are positive;
- D_ij<0 for every eligible pair in E;
- if B has no mutually negative pair, at least one i with r_i>0 has c_i<0;
- in case8, at least one coordinate of c B^-1 is negative;
- the specified genericity inequalities c_i!=0 and D_ij!=0.

These conditions are necessary AND sufficient for all five matrix
restrictions in Section1. Every item involving c is linear once B is fixed.
The mutual-negative-pair alternative has at most three branches; so does
the passive-row alternative. Cases1–5 and7 need neither alternative and
have one basic convex region. Cases6,9,10 need at most three basic regions.
Case8 needs at most nine. Choosing the first negative coordinate, with
earlier tested coordinates nonnegative, makes branches disjoint. Refining
by the equality lines of those tests and removing the required genericity
lines gives a finite partition into relatively open convex polygonal cells,
possibly empty, lower-dimensional or unbounded. Extra inverse-entry genericity also consists only of
finitely many affine lines, by (2).

This is an exact low-dimensional reduction, not a claim that one universal
finite list of rational sample points covers all variable B. The six B
magnitudes still vary under their displayed determinant and row-sum tests.
However every actual raw singleton matrix has a finite, explicit membership
test, and no Nash root or strategic witness is supplied as a class condition.

## 7. A useful coarser partition: zero, one, or two positive-inverse children

There are at most TWO positive-inverse principal triples. A mutually negative
pair belongs to two of the four triples and forbids a positive inverse on
both, leaving at most the other two. Their full test also uses only the same
linear cuts in c. The child B is positive-inverse exactly in case8. For a
child {0,i,j}, put a=B_ij,b=B_ji. It is positive-inverse exactly when

 ab<0, r_i/a>0, r_j/b>0, c_i/a>0, c_j/b>0, D_ij>0. (8)

Indeed its adjugate is

 [-ab,c_j b,c_i a; -a r_j,c_j r_j,-c_j r_i;
  -b r_i,-c_i r_j,c_i r_i],

and its determinant is -ab D_ij. Positivity of these entries is precisely
(8); the positive-inverse zero-diagonal triple must have positive determinant.
Thus the signs of c_i and D_ij already determine every child flag for fixed B.
Count these flags and split into n_child=0,1,2. The checker exhibits all three
possibilities under Section1 and verifies the adjugate criterion.
When n_child>=1, Section4 produces a strict pivot inside a good child. When n_child=0,
any architecture requiring a cyclic inverse-positive triple needs a new
mechanism, regardless of its outer return variations.

An especially small exact no-child witness, with a UNIQUE strict pivot, is

 Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0],
 det Gamma=11,
 Gamma^-1=(1/11)[3,-2,4,5; 1,3,5,-2; -2,5,1,4; 5,4,3,1].

Only inverse column2 is positive; the other three are mixed. The principal
triple determinants, in the order012,013,023,123, are(1,1,3,3), and every
pair principal is nonsingular. Every column has a negative entry. Its
reciprocal pair types are -- at01, ++ at03 and12, and opposite at02,13,23.
The opposite-pair graph is the path0--2--3--1, so there is NO inverse-positive
child. Thus the full passive-child failure condition holds automatically.

For an exact degree certificate, take v=Gamma^-1 e2=(4,5,1,3)/11 and order
the players as(2,0,1,3). Its pointed form has

 c=(4,10,-3)/11, r=(1,-1,-1)/11,
 B=(1/11)[0,-5,6; -4,0,3; 4,-5,0].

The same-sign observer pairs are12 and13; each has opposite r signs, so E
is empty. The root at offset-e2 is therefore uniquely full support, equal to v,
and has index+1. The generic principal-block and negative-column tests give
R0, hence degree+1. This witness satisfies every matrix restriction in
Section1 while leaving no alternative positive full inverse column to select.

These are matrix controls, not completed game counterexamples. No choice of
nonsingleton rewards with a positive behavioral gap is exhibited.

### 7.1. The entire no-child branch with exactly one strict pivot

Impose also the dense generic condition that every full inverse entry is
nonzero. Among Section1 matrices with no positive-inverse child and exactly one positive full
inverse column, there is only ONE off-diagonal sign pattern up to simultaneous
permutation. More precisely, this branch consists exactly of the matrices

 G=[0,-a,-b,c; -d,0,e,f; g,h,0,-i; j,-k,l,0],             (9)

where all twelve magnitudes are positive,

 E=dil+eij-fgl!=0, T=bdh-aeg!=0,

and

 R=cdk-afj>0,
 U=dik-fgk-fhj<0, V=ail+bik-chl<0, W=bdi-bfg-ceg<0.      (10)

Writing D=det G, positivity D>0 follows already from R>0,U<0 by the exact
Jacobi identity

 fk D=(eik+fhl)R-(afl+bfk+cek)U>0.

Its unique positive full inverse column is2. The other principal triple
determinants are D012=T, D023=bij+cgl>0, D123=eik+fhl>0. These two nonzero
tests give ALL remaining genericity conditions: V<0 implies ch>ai, so the
otherwise variable cofactors N03=e(ch-ai)+bfh, N21=cgk+j(ch-ai), and
N23=d(ch-ai)+afg are positive. Every other cofactor has a fixed strict sign
except N10=E and N33=T. Thus this branch has exactly four open sign subcases,
according to(sign E,sign T); the checker supplies small integer witnesses for
all four. This is a complete algebraic description of this generic subcase,
not an additional UE exclusion.

Here is an analytic proof, independent of a finite sign census. Call axis h
covered if some triple C containing h has det G_CC>0 and G_CC^-1 e_h>0.
The coordinate-ray degree argument in
FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION, Part IV Section3,
applies to each full inverse column that is not strictly positive: at offsets
-(M e_h+1), the full support eventually fails, pairs fail their fast column's
negative entry, and omitted-axis supports eventually fail. Degree+1 therefore
forces a positive-index triple with positive inverse column and strictly
positive exterior weight. The three nonpivot axes are covered.

For T=[0,a,b; c,0,d; e,f,0],

 adj T=[-df,bf,ad; de,-be,bc; cf,ae,-ac].                (11)

If det T>0 and two inverse columns are positive, these products force the
third column positive too. Thus under the no-child assumption no two covered axes may use the
same triple. First, the unique uncovered axis lies OUTSIDE every mutually
negative pair. To verify this, label such a pair01 and suppose axes2,3 and
a pair-axis, labeled0, were covered. Axes2,3 must use different triples023
and123; exchanging only the outside labels arranges that order while
preserving covered axis0. Put epsilon=sign G32 and delta=sign G23.
Their positive adjugate columns force

 G02:-epsilon, G03:epsilon, G30:-epsilon,
 G12:delta, G13:-delta, G21:-delta.

If delta=-epsilon, positivity of det023 when epsilon=+1 forces G20>0,
making023 inverse-positive. When epsilon=-1, positivity of det123 instead
forces G31>0 and makes123 inverse-positive. If delta=epsilon=+1, axis0
cannot use023 (negative inverse diagonal),012 (a positive adjugate column
forces both determinant monomials negative), or013 (two adjugate-column
entries have opposite signs). If delta=epsilon=-1, the selected determinants
force G20,G31>0; axis0 then has a negative diagonal in023 and013 and a
negative entry G12 G20 in012. Every alternative is impossible. This is the
three-covered-axis version of the cited Part IV Section4 argument. It also
rules out four covered axes.

Now label a negative pair01 and the uncovered axis2. Axis3 cannot use013;
exchange0,1 so it uses023. Formula(11) gives

 sign G02=sign G23=delta, sign G03=sign G20=-delta.

Axis0 cannot use023, already covering3. If012 covered0, its positive
adjugate column would force G21<0, G12>0 and delta=-1, making both
determinant monomials negative. Hence013 covers0. Its positive column
forces G31<0,G13>0,G30>0, and its positive determinant then forces G03>0.
Thus delta=-1. Axis1 cannot use013, already covering0, or012, whose relevant
adjugate entry G01 G20 is negative. It uses123, forcing G21,G32>0. Finally
G12<0 would make123 inverse-positive, so G12>0. This proves exactly(9).
In that pattern the ONLY positive-determinant covering possibilities are
(013,axis0), (123,axis1), (023,axis3). In particular the pivot is axis2.

Their exterior inverse weights are respectively -U/R, -V/D123 and -W/D023,
by block inversion or direct multiplication of(11). Strict exterior slack
gives precisely the three last inequalities in(10), while det013>0 gives R>0.

Conversely, (9) and(10) imply

 G^-1 e2=(afl+bfk+cek, bfj+cdl+cej, R, adl+aej+bdk)/D>0.

The full inverse entries U/D,V/D,W/D are negative in columns0,1,3,
respectively, so there is only this one strict pivot. The opposite-pair graph
is the path0--2--3--1, excluding every positive-inverse triple. All columns
contain a negative entry, and nonsingular nontrivial principals give R0.
At offset-e2, no triple containing2 has a positive inverse column2: all
three columns are mixed by(11), for either sign of D012. Supports omitting2
of size>=2 give the zero active vector, pairs containing2 cannot have both
active coordinates positive, and singletons fail their negative-column or
axis2 condition. The unique full root is therefore regular of index+1,
proving degree+1. This establishes sufficiency for all Section1 restrictions.

Pointing at the unique pivot gives observer template7, with the eligible-pair
set from(3) empty throughout this chamber. The row signs r=(+,-,-) in observer
order(0,1,3) make both same-sign observer pairs ineligible. There is also a
positive direction for EVERY payoff row, on supports013,123,0123,023,
respectively; the proper-support directions have strictly positive outside
slack. In fact the COMPLETE signed active-set atlas has exactly ten choices,
uniformly across all four E,T sign subcases. On013 its inverse columns have
signs(0+,1−,3−), and the outside inverse row is

    (-U,-N21,-N23)/R.

All three signed outside images are positive because U<0 and N21,N23>0.
Its seven nonempty recipient subsets are therefore eligible. The only
remaining choices are row1+ on123, row3+ on023, and row2+ on the full set.
Every column of the012 inverse is mixed for either determinant sign; all
unlisted columns on023 and123 are mixed, as are the three unselected full
columns. Two-player inverse columns have a zero coordinate. This exhausts
every active set, column and sign. Each of these ten choices gives the
explicit G>=L0,B<=cG raw existence test from the weighted collision theorem.
Every counterexample in this chamber must fail ALL ten. Arbitrary higher
rewards outside these successful regions remain unresolved.

The [observer-attractor theorem](CODEX_COORDINATOR__OBSERVER_ORTHANT_ATTRACTOR.md)
now supplies a general local producer component in this singleton chamber.
The condition R>0 is exactly what gives its signed Lyapunov weights on013.
Under its additional raw joining conditions, every sufficiently small
(-,+,+) observer annotation can be sent to zero by produced01/013 roots,
with arbitrary finite higher rewards. Near a positive pivot axis, further
smallness also prices that player's full comparison. Reaching such entries
from nonnegative seeds and producing a bounded recurrent return family
remain separate obligations; this does not eliminate the entire matrix cell.

### 7.2. Multiple strict pivots remain a finite polygon refinement

For any pointed matrix(1), let V=B^-1 and R=cV. Its observer column j is
strictly positive in H^-1 exactly when

    R_j<tau_j, tau_j=min(0,V_1j,V_2j,V_3j).

This follows immediately from(2). Thus the number of strict full inverse
columns is1 plus the number of these three successful tests. For fixed B,
each test is affine in c. Under inverse-entry genericity equality cannot
occur. The eight possible success/failure patterns cut the already defined
outside-row polygons into at most eight convex pieces per polygon. This
provides exact membership tests for the remaining two-, three-, and
four-pivot cases without introducing a large sign table or asserting that
every formal piece is nonempty. The child tests from(8) refine the same
polygons independently. The one-pivot/no-child refinement in Section7.1 is
stronger: it identifies its unique sign template and four explicit subcases.

### 7.3. The same sign orbit admits a complete all-pivot description

Keep the twelve positive magnitudes and sign form(9), but allow any number
of positive full inverse columns. On the generic stratum, the Section1
residual restrictions in this ENTIRE sign orbit are equivalent to just

    R=cdk-afj>0 and D=det G>0.                         (14)

The complete positive full inverse-column set is

    {2} union {0:U>0} union {1:V>0} union {3:W>0}.      (15)

All eight signs of(U,V,W) occur. This generalizes the one-pivot result inside
its sign orbit; other sign orbits do occur with multiple strict pivots.
Full-cofactor genericity is still required here. The reduction to only E,T
as nonzero tests in Section7.1 applies to its U,V,W<0 subcase.

For the complete pivot test, put N=adj G and

    A2=N02=afl+bfk+cek>0, B2=N12=bfj+cdl+cej>0,
    C1=N11=bij+cgl>0, P0=N00=eik+fhl>0,
    Q1=N31=agl+bgk+bhj>0.

Direct expansion, or the complementary-minor identities, gives

    fk D=P0 R-A2 U,
    B2 N21=C1 R+cj D,
    B2 N03=A2 W+(bf+ce)D,
    B2 N23=R W+cd D,
    C1 N33=W Q1+bg D.                                (16)

Column2 is positive by its formula in Section7.1. If U>0, then
 di-fg>fhj/k>0 and N10=l(di-fg)+eij>0; its other two entries N00,N30 are
positive automatically. Hence column0 is positive exactly when U>0.
Column1 has its fixed positive entries C1,Q1 and N21>0 by(16), so is
positive exactly when V>0. When W>0, the last three identities make all
other entries of column3 positive; the converse is immediate from its
entry W. Division by D>0 proves(15).

Sufficiency of(14) uses the earlier complete support census at offset-e2:
column2 is positive, every proper triple column2 is mixed, and every other
proper support fails. Its only root has positive index. This proves degree1
and uses no sign assumption on U,V,W. Negative columns and principal
nonsingularity give R0. The opposite-pair graph is always the path
0--2--3--1, so there is no positive-inverse child and the passive-child
failure is automatic. The mutually negative pair01 is present.

For necessity, residuality already gives D>0. Suppose R<0. The first
identity(16) forces U<0, so columns0 and2 cannot be positive. A strict full
pivot must be1 or3. On013 the adjugate is

    [fk,-ck,-af; fj,-cj,-cd; dk,-aj,-ad].

Its columns at1 and3 are negative; division by R<0 makes either selected
inverse column positive. Its exterior slack at offset-e_p is
-(D/R)(G^-1)_(2,p)>0. Hence this is a strict complementary triple root
of index-1, in addition to the full root of index+1. At that pivot all other
admissible proper triples also have negative determinant: block inversion
gives outside weight -(D/det G_TT)(G^-1)_(o,p), with a positive full-column
entry. Nontriple proper supports fail as in Section3. Thus degree is1 minus
at least one, contradicting degree1. Genericity excludes R=0, proving(14).

Here are exact witnesses for all eight patterns. Fix a=d=f=j=k=l=1 and
vary the other six magnitudes in the displayed order. The checker verifies
all genericity, the complete full-pivot sets and unique offset-e2 root.

| Signs(U,V,W) | (b,c,e,g,h,i) | R | D |
|---|---|---:|---:|
|−,−,−|(1,2,1,1,2,1)|1|11|
|−,−,+|(2,3,1,1,4,3)|2|26|
|−,+,−|(2,2,1,1,1,1)|1|7|
|−,+,+|(3,2,1,1,2,2)|1|10|
|+,−,−|(1,4,2,1,3,5)|3|29|
|+,−,+|(2,6,1,1,3,5)|5|31|
|+,+,−|(1,3,2,1,1,3)|2|6|
|+,+,+|(2,3,1,1,1,3)|2|2|

The eight sign subcases are not asserted to be connected, and further
cofactor-sign cuts can refine them. Arbitrary collision rewards remain
data to be handled; this is a complete singleton classification inside
one sign orbit, not a UE theorem for that orbit.

## 8. How to use the partition without overclaiming closure

The failed sign, non-Q/homogeneous, degree, strict-column and passive-child
branches are already eliminated by their established matrix-only producers
or source reductions. Sections2–7 reorganize their surviving intersection;
they do not eliminate another game from it.

Within an admitted cell, retain the ORIGINAL reward table and apply the
remaining sufficient criteria with their actual collision hypotheses. In
particular, columnwise uniform signs of Gamma^-1 do not themselves prove UE:
SIGNED_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM additionally requires pair rewards,
passive pair signs and inactive joining bounds, while
SIGNED_PASSIVE_COALITION_REWARDS_UNIFORM_EQUILIBRIUM requires suitable large
passive rewards. The boundary/strict one-column jackpot producers likewise
require their selected reward to grow with the correct sign. Their premises
cannot be inferred from this singleton partition.

The next strategic tasks can therefore be stated exhaustively: handle n_child=0
with an architecture not requiring a positive-inverse child; handle n_child=1,2
using the available child and the possible outside-row polygon cells; and in
each case cover the still arbitrary nonsingleton rewards or find a genuine
full-behavior gap. An outer-calendar theorem for only one polygon cell is
progress in that leaf, not closure of the entire partition or Fin4.


### Every recipient has a proved favorable direction

On the additionally generic stratum where full inverse entries are nonzero,
the axis-degree argument supplies a strict positive active-support column
with positive outside image for EVERY recipient. For a positive full
inverse column choose the full support. For any other column, the large
negative coordinate-ray offsets exclude full support; degree1 forces a
positive-index triple with positive active inverse column and strictly
positive exterior weight. This is exactly an input to the weighted
collision-dominance theorem, with positive sign.

Let m>=1 count the positive full inverse columns. Holding the singleton
matrix and every other reward fixed, the following numbers of signed
collision-coordinate rays are therefore eventually covered by that theorem:

| Coordinate direction | Guaranteed distinct rays |
|---|---:|
|Positive participant pair reward|8+m, at least9 of12|
|Negative passive pair reward|4+2m, at least6 of12|
|Positive participant triple reward|4+2m, at least6 of12|
|Negative passive triple reward|m, at least1 of4|
|Positive grand-coalition reward|m, at least1 of4|

For a full support there are three participant pairs, three passive pairs,
three participant triples, one passive triple and the grand coalition per
recipient. A selected triple supplies two participant pairs, one passive
pair and one participant triple. Counting across recipient rows proves the
table. Along each stated ray the favorable weighted scale G tends to
infinity and all unfavorable scales stay bounded, so the explicit raw
criterion eventually applies. Additional negative signed columns may cover
further directions. This is a consequence of the existing source and the
new dominance producer, not a new independent export. Comparable competing
rewards and singular singleton limits remain unresolved.

## 9. Five actual-source cases and five inherited endpoint cases

Use the augmented semantic carrier and subcritical source proved in
[the zero-observer boundary reduction](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md).
Fix a native positive absorbing-gap table Z, the generic row-distinctness,
pair-contact and triple-joining nonsingularity conditions of that source,
and a strict inverse-column pivot p. Put

    C={Y in closure(actual U,B,N,e): d_i=0 for i!=p},
    C0={Y in C: nu=0}, m=min_C0 d_p>0,
    r=m/2, J_r=d_p+r nu, mu=min_C J_r.

Here B is the full behavioral cap, e the literal Never payoff, d=B-U,
and nu the product of marginal Never masses. The source gives

    0<mu<r<m, nu>0, B=e, B_p>mu, U_p>r nu,
    N_p<=1/(1+r sum(Gamma^-1 e_p))<1

at every minimum. Every cap there is positive under the stated genericity:
the existing bounded observer-only zero-face words multiply both d_p and
nu by their common survival, so the absorbing zero-face contradiction
applies to J_r as well. This is a transfer of that proof, not a positivity
claim about every descendant.

For a disjoint existence split, first ask whether the minimizing fibre
contains an actual tuple. If yes, select one actual minimum. If not, use an
incoming minimum and its inherited endpoint. Different selected minima of
one table can have different support patterns; these are source obligations,
not disjoint raw-table types.

### 9.1. Actual minimum: classify infinite-support owners

Every finite conditional tail has zero observer debts, is ALL-END and has
positive marginal Never masses. Exact prefix debt recursion proves the first
statement, and equality with the Continue/Never option proves the second.
Tail caps need not be positive; tails need not minimize J_r.

After the last finite atom of any finitely supported owner, the following
five cases exhaust the set of owners with infinitely many finite atoms:

| Case | Infinite-support owners | Necessary additional restriction |
|---|---|---|
| F | none | At least three owners act at the last occupied date. |
| I2 | pivot and one observer | Both late finite masses are comparable. |
| I3p | pivot and two observers | Pivot mass is a fixed fraction of total late finite mass. |
| I3o | three observers, pivot excluded | Late tails are full native Nash; all three masses are comparable. |
| I4 | all four | Controlled-window restrictions apply when the additional raw matrix test holds. |

There cannot be exactly one infinite owner. The resulting one-owner tail
would be full native Nash: if the pivot is quiet its prescribed Never is
optimal by ALL-END, and if the pivot is the sole owner its native payoff
and cap are zero. Normalizing that owner's finite law to total mass1 scales
all nonowner payoffs and offers equally and gives absorbing zero debt,
contradicting the positive absorbing gap. Two infinite observers without
the pivot similarly give a full native Nash tail supported on two owners,
contradicting the existing three-owner dispersion bound.

At a last occupied date, a sole active owner could instead quit surely,
producing an absorbing native Nash profile. If exactly two act, an active
observer i must satisfy Z_i(ij)=Gamma_ij because its continuation is Never
and its opponent has positive hazard. This violates row distinctness.
Thus F has at least three last-date owners.

For quantitative restrictions let f_i be conditional finite masses,
beta=sum f_i, M bound absolute native rewards, and epsilon be the sum of
the two smallest f_i. The
[three-owner dispersion theorem](../exports/UNIFORM_THREE_OWNER_TAIL_DISPERSION.md)
and ALL-END pivot coupling give, for one c=c(Z)>0,

    c beta^2 <= d_p+beta epsilon,
    0<=d_p<=2M f_p sum_(i!=p)f_i.

The second inequality couples the pivot's prescribed law with Never;
a payoff can change only when both the pivot and an opponent are finite.
In I2, epsilon=0, hence

    c beta^2<=d_p<=2M f_p f_i,
    f_p,f_i>=c beta/(2M).

In I3p, epsilon<=f_p, so f_p>=c beta/(2M+1). In I3o the pivot also has
zero debt, so d_p=0 and every one of the three finite masses is at least
c beta. This does not justify renewing a three-owner native Nash tail:
its active payoffs need not be zero. None of these five cases is closed.

There is an additional actual-mode reduction under the finite raw criterion
in [the fixed-cap controlled-window theorem](../exports/FIXED_CAP_CONTROLLED_WINDOW_MINIMUM_EXCLUSION.md).
Every qualifying fixed full-support window must eventually contain a pivot
contact at one of its marked dates. For the no-child premium ray M>=14,
eventual full support forces geometric decay of the remaining finite masses.
For every M>=11 in the canonical no-child family and its stated raw
completions, the [direct producer](../exports/NO_CHILD_PREMIUM_FAMILY_UNIFORM_EQUILIBRIUM.md)
constructs actual finite profiles whose four native debts and joint Never
probability all tend to zero. Their augmented limit belongs to C0 and has
pivot debt zero, so m=0. Thus the positive-gap premise of this entire source
partition fails, for both actual and inherited alternatives. No
realization theorem or replacement preserving an inherited head is needed
for these tables. The generic partition above remains open.

### 9.2. Inherited endpoint: classify its zero caps

If the minimizing fibre has no actual tuple, the incoming reduction gives
an actual positive-Never head P and an endpoint Q with Y=Phi_P(Q). The
endpoint belongs to C, has nu(Q)>0 and B(Q)=e(Q)>=0, at least one zero
observer cap and at least one positive cap. There are precisely five cap
patterns up to observer labels:

| Zero observer caps | Pivot cap |
|---|---|
|1|0|
|1|positive|
|2|0|
|2|positive|
|3|positive|

The all-zero endpoint is already excluded at this same subcritical source.
No remaining pattern is universally excluded. Q may be actual even if Y
is nonrealized: an infinite semantic head followed by Q is a limit of finite
prefixes, not a strategy executing Q after infinitely many dates.

With s=nu(P)>0 and h_i=product_(j!=i)N_j(P), ancestry retains

    Phi_P(Q).U_i=U_i(P)+s U_i(Q),
    Phi_P(Q).B_i=max(B_i(P),e_i(P)+h_i B_i(Q)),
    nu(Phi_P(Q))=s nu(Q).

On the slice with the SAME observer caps, Q minimizes the pulled-back
objective

    max(B_p(P),e_p(P)+h_p B_p(Q'))
      -U_p(P)-s U_p(Q')+r s nu(Q').

It need not minimize J_r on C. Dropping that inherited head constraint
would change the problem. Let F0={Q in C:B(Q)>=0,min_(i!=p)B_i(Q)=0}.
Compactness and positive caps at every original minimum give
kappa=min_F0 J_r-mu>0. Prefix debt recursion yields

    mu=R_head+s J_r(Q), R_head>=0,
    nu(Y)<=s<=mu/(mu+kappa)<1.

Thus the incoming head must absorb a fixed positive amount at this fixed
source. This quantitative gap supplies no replacement endpoint.

### 9.3. Three zero observer caps: an inherited ratio restriction

This is a source restriction, not an equilibrium theorem. Use the native
augmented semantic carrier and retained-query graft operation of
`CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md`. Let C be its
zero-observer-debt set at pivot p, let

    m=min{d_p(Z): Z in C, nu(Z)=0}>0,
    0<r<m,  mu=min_(Z in C)[d_p(Z)+r nu(Z)]<m.

Suppose a global minimizer Y is ALL-END and has a representation
Y=Phi_P(Q), where P is an actual head with all marginal Never masses
positive, and Q is in C with positive joint Never mass and ALL-END caps

    B_i(Q)=e_i(Q)=U_i(Q)=0  (i != p),
    b=B_p(Q)=e_p(Q)>0.

Put u=U_p(Q), v=nu(Q), n=N_p(Q), h=v/n, and for the actual head put

    s=nu(P)>0, h_P=s/N_p(P), g=B_p(P)-e_p(P)>=0.

Then h<1 and v<1, and the following exact inequalities hold:

    b/(1-h)-u/(1-v) >= m,                         (1)
    u+r(1-v) >= (h_P b-g)/s >= 0.                 (2)

Consequently b >= (m-r)(1-h). If equality holds, P itself is an actual
global minimizer at r. In particular, after prioritizing the actual
minimum branch, every remaining inherited endpoint in this pattern obeys

    b > (m-r)(1-h).                               (3)

The complete source subbranch b<(m-r)(1-h) is impossible. At the equality
boundary the inherited representation supplies an actual minimum rather
than another irreducible endpoint.

Proof. The native Never payoff satisfies
`|e_p(Q)|<=M(1-h)` for a finite reward bound M, first on actual laws and
then by continuity on the augmented carrier. Thus b>0 gives h<1; also
0<v<=h<1.

All observer caps and payoffs of Q are zero. Retained-query grafting Q
into itself therefore preserves observer feasibility. Its k-fold graft
has, exactly,

    B_p=e_p=b sum_(j=0)^(k-1) h^j,
    U_p=u sum_(j=0)^(k-1) v^j,
    nu=v^k.

For the cap identity, the old finite branch is no larger than the old
Never-through-tail branch because every graft is ALL-END; attaching the
positive cap b increases that branch. Every observer cap/payoff remains
zero. Compactness gives an absorbing point in C with pivot debt equal
to the left side of (1), proving (1).

Replacing Q by literal AllNever leaves all observer caps and payoffs of
Phi_P(Q) unchanged: their tail cap and payoff are both zero. Hence P
itself belongs to C. Moreover, ALL-END of Y implies

    B_p(Y)=e_p(P)+h_P b >= B_p(P),

so 0<=g<=h_P b. The exact full-cap head formula gives

    J_r(P)-J_r(Y)
       =g-h_P b+s[u+r(1-v)] >=0,

which proves (2). No minimization of J_r on Q itself is asserted.
Combining (1) and (2),

    b/(1-h) >= m+u/(1-v) >= m-r.

If equality holds, both inequalities are equalities, so
u+r(1-v)=0. Equation (2) forces g=h_P b and the displayed head objective
difference is zero. Thus J_r(P)=mu. This proves the stated priority
partition without assuming that a selected nonactual minimum excludes
other actual minima.

All replacements retain the three full observer caps exactly. The proof
uses no finite-calendar approximation, local Nash-root surrogate, or
claim that the abstract endpoint is executed after an infinite head.

Independent whole review: [the inherited ratio restriction](../feedback/INHERITED_ZERO_OBSERVER_RATIO__BY_CONTACT_REVIEW.md).

## 10. Finite interval tests for the actual two-owner tail

Fix the I2 source in Section9.1, pivot p and its sole infinite observer i.
Write the four raw entries

    G=Gamma_ip, J=Z_i(ip), A=Gamma_pi, C=Z_p(ip).

The generic source has G,A!=0, J!=G, C!=A and GC-AJ!=0. The letter r
continues to denote the source penalty; the contact ratio below is rho.
For the two quiet observers h,k define

    rho=G/J,
    a_j=Gamma_jp-rho Z_j(jp), b_j(z)=Gamma_ji-z Z_j(ji).

The following is one finite necessary screen, stated in its strongest form.
If any step fails, this partner cannot occur in I2 at the selected source.

1. Require J!=0, 0<rho<1 and A-rho C>0.
2. The two a signs must be strictly opposed. Label them a_h<0<a_k.
3. The following explicit affine interval must be nonempty:

       I={z: rho<=z<1, C z<=A,
               b_k(z)<0<b_h(z),
               a_k b_h(z)-a_h b_k(z)>=0}.              (12)

4. If A<0, require rho in I. If A>0, form the auxiliary test

       O={ (x,lambda): lambda>0,
                0<=x<=rho if J>0, or rho<=x<=1 if J<0,
                Gamma_jp-x Z_j(jp)+lambda Gamma_ji>=0
                               for j=h,k }.           (13)

   If O is empty, again require rho in I.

Test(13) also reduces to an affine interval, so no general linear solver is
needed. Put c_j(x)=Gamma_jp-x Z_j(jp), d_j=Gamma_ji. Intersect its stated
CLOSED x domain with

    c_j(x)>0                         if d_j<0,
    c_j(x)>=0                        if d_j=0,
    d_k c_h(x)-d_h c_k(x)>=0          if d_h<0<d_k,

including the analogous last comparison with h,k exchanged. This is
exactly the result of eliminating lambda>0. Negative d imposes a positive
upper bound on lambda; positive d imposes a lower bound. Every lower bound
must be at most every upper bound. With no upper bound choose lambda large.
All coefficients are raw singleton/pair entries. A rational table gives an
exact rational interval calculation. These tests are necessary, not a
producer for a source with global minimality or a UE criterion by themselves.

### Exact contacts and the first screen

Condition the two independent private laws once at a fixed cut beyond the
other observers' last finite atoms. Within these conditioned laws use
unconditional date probabilities alpha_n=Pr(T_p=n), beta_n=Pr(T_i=n),
and inclusive finite tails P_n=sum_(m>=n)alpha_m, I_n=sum_(m>=n)beta_m.
Both are positive and tend to zero. Their positive Never masses and the
comparability in Section9 give fixed constants 0<L<=U<infinity with

    L<=P_n/I_n<=U                                      (14)

at every sufficiently late date. Conditional finite masses are
P_n/(N_p+P_n), I_n/(N_i+I_n), whose denominators stay bounded away from zero.

Observer i's Never payoff is G P_0; its forced date-n payoff is
G(P_0-P_n)+J alpha_n. Observer optimality and ALL-END therefore give

    J alpha_n<=G P_n, with equality whenever beta_n>0.

Pivot ALL-END similarly gives C beta_n<=A I_n. At every observer atom,
0<alpha_n<P_n because infinitely many pivot atoms remain. Thus

    rho=G/J in(0,1), alpha_n=rho P_n whenever beta_n>0. (15)

In particular observer support is contained in pivot support. The two raw
orders are 0<G<J and J<G<0.

To prove A-rho C>0, first take A>0. If C<=0 it is immediate. If C>0 put
s=A/C. Were rho>s, then s<1. Each observer atom removes rho of the pivot
finite tail and at most s of the observer tail; between these atoms only
the pivot tail can decrease. At successive observer atoms t_m,

    P_(t_(m+1))/I_(t_(m+1))
      <=[(1-rho)/(1-s)] P_(t_m)/I_(t_m),

contradicting(14). Therefore A-rho C>=0. If A<0, the pivot inequality forces
C<A<0 and an observer atom at EVERY date. Put s=A/C in(0,1). Then
P_(n+1)=(1-rho)P_n and I_(n+1)<=(1-s)I_n. Were s>rho, I/P would tend to
zero, again contradicting(14). This again gives A-rho C>=0. Equality is
excluded by GC-AJ!=0, proving step1.

If G<0, the observer deadline inequality also gives alpha_n>=rho P_n at
every date. The pivot then acts at every date, and observer-free gaps have
a fixed finite length bound: a gap of length m leaves I fixed but multiplies
P by at most(1-rho)^m, so(14) forces (1-rho)^m U>=L. If A<0, both owners
act at every date and P_n=P_0(1-rho)^n exactly, while
beta_n/I_n>=A/C and 0<A/C<rho<1. The observer tail need not be geometric.

### Quiet observers give the interval, and the gap forces its signs

At an observer atom put z_n=beta_n/I_n. Then
P_(n+1)=(1-rho)P_n, I_(n+1)=(1-z_n)I_n, so(14) yields

    z_n<=1-(1-rho)L/U<1.                              (16)

The limsup of these rates is at least rho. Otherwise every sufficiently
late observer atom would have z_n<=rho-epsilon for some epsilon>0; I/P
would grow by a fixed factor at each such atom and could only grow between
them. Select a subsequence with z_n->z>=rho. The conditional finite-mass
ratio f_i/f_p has a subsequence converging to some lambda>0. Current hazards
are q_p=rho f_p, q_i=z_n f_i, and the pivot inequality gives Cz<=A.

For a quiet observer j, its Never payoff differs from
Gamma_jp f_p+Gamma_ji f_i by at most3M f_p f_i. Its current Quit payoff
differs from Z_j(jp)q_p+Z_j(ji)q_i by at most3M q_p q_i. Both bounds follow
by separating the event that both active owners choose finite times.
Its END comparison, divided by f_p and passed to the limit, gives

    a_j+lambda b_j(z)>=0, j=h,k.                     (17)

There is no positive-cap premise on these tails. With t=1/lambda>0,
these are the affine inequalities a_j t+b_j(z)>=0.

The positive absorbing gap forces strictly opposed signs. A sure geometric
clock of owner p at rate rho, all other owners Never, has each recipient's
date-n payoff minus Never payoff equal to

    (1-rho)^n[rho Z_j(jp)-Gamma_jp].

Observer i is indifferent by(15). If both a coefficients were nonnegative,
this would be absorbing exact native Nash, impossible. Hence some a_h<0,
and(17) forces b_h(z)>0. Similarly, owner i alone at geometric rate z is
absorbing exact native Nash if both b coefficients are nonnegative; its
pivot comparison is Cz<=A. Therefore b_k(z)<0, and(17) forces a_k>0.
Finally a_h t+b_h>=0 and a_k t+b_k>=0 admit t>0 exactly when

    -b_k/a_k<=b_h/(-a_h),

which is the cross inequality in(12). This proves steps2–3, for either sign
of the raw coefficient A. The positive gap A_abs is distinct from that
coefficient. The argument also proves that(12) is exactly the projection
of(17), together with the rate and pivot inequalities, under these opposed
signs.

### When common support forces the contact rate to pass

For A<0 common support at every late date was already proved. For A>0,
suppose infinitely many pivot atoms have no observer atom. At such a date
put x_n=alpha_n/P_n. The observer comparison gives x_n<=rho if J>0 and
x_n>=rho if J<0. Always x_n in[0,1]. The conditional ratio lambda_n=f_i/f_p
lies in a compact positive interval. Pass to a subsequence. The quiet
observer's current Quit value is Z_j(jp)x_n f_p, whereas its Never value
is Gamma_jp f_p+Gamma_ji f_i+O(f_p f_i). Dividing the END inequality by
f_p produces a point of O. Thus O empty implies only finitely many such
dates. Keeping x=0 in its domain is essential: normalized positive atom
rates can tend to zero.

In either case of step4, list the sufficiently late common atoms t_m.
Between them neither finite tail changes, and

    [P_(t_(m+1))/I_(t_(m+1))]/[P_(t_m)/I_(t_m)]
                           =(1-rho)/(1-z_m).

Comparability forces liminf z_m<=rho<=limsup z_m. It does NOT imply that
rho is an actual atom rate or a subsequential limit; oscillation is possible.
Select subsequences tending to z_-<=rho and z_+>=rho, and on each also pass
to a limit t=f_p/f_i in a compact positive interval. Both limiting points
satisfy t>0, Cz<=A and a_j t+b_j(z)>=0. These inequalities are affine in
(t,z). A convex combination whose z coordinate is rho preserves every
inequality and t>0. Applying the preceding solo-clock exclusion and opposed
sign argument at rho gives precisely rho in I. This proves step4.

For an exact strict comparison, take

    Gamma=[0,3,-1,4;2,0,1,-3;2,-2,0,-1;-1,-2,1,0],
    p=0,i=1, Z1(01)=4, Z0(01)=-2,
    Z2(02)=10, Z3(03)=-4, Z2(12)=-10, Z3(13)=1/10.

Here rho=1/2,A=3,C=-2,a2=-3,a3=1,
b2(z)=-2+10z,b3(z)=-2-z/10. The step3 interval is [80/97,1), hence
nonempty. But O requires simultaneously x<1/5 and x>1/4, so is empty.
At z=rho the cross inequality has left side -63/20<0. Step4 therefore
excludes this partner although steps1–3 pass. The singleton determinant is
35 and its inverse column0 is(8,3,14,10)/35>0. Unspecified finite rewards
do not affect the calculation. This is a strict comparison between necessary
screens, not a positive-gap example or a counterexample to UE.

### Exact debt and the remaining global obligation

Let T=sum_n alpha_n beta_n be the tie probability, a the probability of two
finite times with p first, and b the probability of two finite times with
i first. Independence and integrated contact give

    a+b+T=P_0 I_0, J T=G(b+T),
    d_p=A(a+T)-C T
       =P_0 I_0[A-{C+A(1/rho-1)} T/(P_0 I_0)].       (18)

The tie fraction lies strictly between0 and rho, since b+T=T/rho and a>0.
Thus ALL-END does not imply pivot indifference; its debt remains genuinely
quadratic. Passing the interval tests does not supply the earlier head,
its exact observer comparisons, or global minimality. Changing a late
calendar without retaining these data is not a descent of the selected
source. If all three possible partners fail the tests, I2 is absent at that
pivot; F, I3p, I3o, I4 and the inherited endpoint cases still require work.

## 11. An actual two-owner replacement with extra contacts

The [complete replacement theorem](CODEX_COORDINATOR__TWO_OWNER_CONTACT_REPLACEMENT.md)
retains the entire (U,B,N) tuple of an I2 tail and its original head. Fix the
pivot law and vary the partner only on its existing response-contact set,
retaining its total finite mass and tie probability. Uniform pair-tail
comparability makes this feasible set compact in total variation. An extreme
law has, on every finite physical-date interval,

    positive partner atoms <= 2 + tied pivot/quiet comparisons.

If A<0 or the screen O in(13) is empty, late common support is forced.
Then some quiet observer has infinitely many exact Quit-versus-Never ties
in an equivalent actual minimum. With no quiet ties, the count would make
all late partner atoms pivot ties, forcing its rate A/C to equal rho and
contradicting GC-AJ!=0.

The same theorem gives a generic rigidity obstruction: the three observer
caps determine P,I,T, and hence the pivot debt and Never mass, among
observer-exact ALL-END pair tails. Same-pair cap-preserving edits therefore
cannot descend. The produced quiet contacts permit a new-owner activation
attempt, but no such compensated descent is yet proved. Its objective must
retain the inherited head's full maximum and coefficient
lambda=1/N_p(head); conditional-tail minimality is not supplied.

The converse local calculation is now complete on the strict common-support
screen: when the final cross inequality in(12) at z=rho is strict and the
generic pair reward Z_h({h,i}) is nonzero, the
[exact realization theorem](CODEX_COORDINATOR__I2_STRICT_SCREEN_REALIZATION.md)
constructs an actual infinite pair tail for every finite choice of the higher
rewards. One quiet observer ties at every date, the other is strictly quiet,
and the partner law is extreme in the same retained-moment set. Pivot debt
is positive and quadratic. These are local configurations, without the
required head or global minimality. They show that further local calendar
existence or contact-extremality tests cannot discard any open strict passing
cell. The equality boundary and the global variational obligation remain.

## 12. Complete self-repetition test for three zero observer caps

The following strengthens Section9.3 with a necessary source inequality.
It excludes a subregion of inherited endpoint data and exhausts all
self-repetition comparisons; it does not close the endpoint pattern.

Use the native augmented carrier and retained-query graft from the
[zero-observer boundary reduction](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md). Let C impose zero debt for all observers,
m=min_{C,nu=0} d_p>0, 0<r<m, mu=min_C(d_p+r nu). Let Y be an ALL-END global
minimum represented as Y=Phi_P(Q), with P an actual positive-Never head.
Suppose Q has zero observer payoffs and caps, is ALL-END, and has

 b=B_p(Q)=e_p(Q)>0, u=U_p(Q), v=nu(Q)>0, n=N_p(Q), h=v/n.

Write s=nu(P)>0, lambda=1/N_p(P), and

 g=B_p(P)-e_p(P), A=u+r(1-v).

The existing source gives 0<=g<=s lambda b and 0<v<=h<1. In fact n<1:
if n=1, the complete-law identity |U_p-e_p|<=2M(1-N_p) gives u=b.
Repeating Q then gives an absorbing zero-debt limit (h=v), contrary to m>0.
Thus 0<n<1 and 0<v<h<1.

**Proposition.** Every such inherited endpoint satisfies

    A <= lambda b/n = b/N_p(Y).                          (1)

Together with the already established removal inequality

    A >= lambda b-g/s,                                  (2)

these are exactly the global-minimality comparisons against every competitor
Phi_P(Q^k), k=0,1,2,...,infinity. Here Q^0 is literal AllNever. The separate
comparison of Q^infinity itself to m remains necessary; it is not asserted
to follow from (1)--(2).

If Y is selected with the least pivot Never mass among all global minima,
then (1) is strict. Such a selection exists because the minimizing fibre is
compact and every subcritical minimum has positive joint Never mass.

Proof. Each Q^k is obtained by retained-query grafts and has exactly

 B_p(Q^k)=b sum_{j=0}^{k-1}h^j,
 U_p(Q^k)=u sum_{j=0}^{k-1}v^j, nu(Q^k)=v^k.

All observer caps and payoffs remain zero. Therefore the original head's
three observer comparisons are unchanged. For k>=1, the pivot tail cap is
at least b, so ALL-END of Y implies that the head's continuation-through-tail
cap branch remains maximal. Consequently, exactly,

 [J_r(Phi_P(Q^k))-J_r(Y)]/s
       =sum_{j=1}^{k-1}[lambda b h^j-A v^j].             (3)

At k=2, nonnegativity of (3) gives lambda b h-A v>=0, proving (1).
Conversely, h/v=1/n>=1 and lambda b>0 imply that (1) makes every summand
in (3) nonnegative. Hence every finite k comparison holds. Boundedness and
compactness give the k=infinity comparison by taking limits. The k=0
comparison is exactly g-s lambda b+s A>=0, which is (2). Thus no further
self-repetition inequality remains after these two tests.

If equality holds in (1), k=2 has exactly J_r=mu, while
N_p(Phi_P(Q^2))=N_p(P)n^2<N_p(P)n=N_p(Y). This contradicts the stated
least-pivot-Never selection and proves strictness.

The retained-query operation uses limits of finite grafts on the original semantic
carrier, not execution of a continuation after infinitely many dates. This
proposition has the same interpretation. The retained old-head maximum is
not dropped: its branch is justified separately for k>=1, while k=0 uses
the exact maximum through g.

### Comparison with the prior scalar conditions

Condition (1) is not a formal consequence of the displayed removal,
absorbing-ratio and inverse-axis Never inequalities alone. For an arithmetic
control, take

 m=3/5, r=1/2, n=h=9/10, v=81/100,
 b=u=3/20, lambda=6/5, g=0, S=1/2.

Then b/(1-h)-u/(1-v)=27/38>m, A=49/200>lambda b=9/50,
and N_p(Y)=n/lambda=3/4<1/(1+r S)=4/5. But
A=49/200>lambda b/n=1/5, so (1) fails. This is only a strictness check
between scalar screens, not an actual positive-gap game or endpoint.

After this inequality holds, longer repetitions cannot yield a descent.
Closing this pattern requires a replacement outside that family or a raw
bound forcing the inequality to fail. Independent review is recorded in
[the repetition audit](../feedback/FIN4_INHERITED_SELF_REPETITION__BY_REVIEW.md).

## Verification and next obligations

Independent reviews cover the complete [matrix partition, Sections1–8](../feedback/FIN4_RESIDUAL_PARTITION_MATRIX__BY_FRESH_REVIEW.md)
and the [source partition and pair tests, Sections9–10](../feedback/FIN4_RESIDUAL_PARTITION_SOURCE__BY_CHAMBER.md),
with exact section-byte hashes. A complete
[no-child benchmark](CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md)
illustrates the remaining collision-reward obligation and admits additional
actual-source exclusions for that particular family.

The compact exact matrix checker is
[CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py](../experiments/CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py).
Run it with Python3 from any directory. It uses only rational arithmetic
and finite support enumeration:64 observer sign words,16 permutation orbits,
11 determinant-positive possibilities, ten nonempty pointed templates,
all child counts0/1/2, the no-child controls, all eight pivot patterns in
the classified sign orbit, and the four one-pivot generic subcases. No random
sampling or generated table is required for its claims. The same checker
also verifies the strict/weak interval boundaries in Section10 and exposes
`i2_partner_screen(Z,p,i)` for exact rational native tables. Its result
`passes_necessary` supplies neither a profile nor a counterexample; the
source and genericity assumptions remain mathematical prerequisites.

The next independent tasks are to cover the arbitrary collision rewards in
these singleton cells; to eliminate F, I2, I3p, I3o, I4 using the actual
source rather than local optimality; or to replace one of the five endpoint
patterns while preserving its inherited full-cap comparisons. The new pair
filter removes I2 only at a pivot where all three partners fail its raw test.
No correspondence between a matrix template and a global source case is
claimed without an additional proof.
