# Four-player games without a mutually negative singleton pair

This is an ordinary mathematical raw reward-class theorem, not implemented
in Lean. Arbitrary Fin4 remains open. The new classification includes every
higher-coalition completion of the displayed singleton sign class.

## Exact theorem and semantic scope

For a four-player quitting game, put s_i=r_i({i}) and Gamma_ij=r_i({j})-s_i
for i!=j, with Gamma_ii=0. If every pair has at least one nonnegative
centered comparison, that is,

    Gamma_ij>=0 or Gamma_ji>=0  for every i!=j,

then the game has a uniform-equilibrium payoff. Own levels and all higher
coalition rewards are arbitrary real numbers. The target payoff is fixed
before accuracy; for each epsilon>0 one profile caps every unilateral
behavioral deviation and delivers that target within epsilon over all
sufficiently long finite horizons. Randomization is private and independent,
there is no correlation device, the first nonempty quitting coalition absorbs,
and live and Never payoffs are zero.

All strategic witnesses are produced by the same-table no-UE matrix source,
existing matrix consumers, or the explicit singleton cycle below. In
particular no stationary root, phase schedule, eigenvector, favorable
continuation, or punishment is a supplied input. The new positive-chord and
two-triangle cases are proved in Sections1--7; Section8 exhausts the signs
and closes zero boundaries; Section9 includes the strict-tournament proof.
The result forces any remaining Fin4 counterexample to have a pair
with both comparisons strictly negative. This is ordinary mathematics,
not a claim of a new Lean-checked declaration.

## 1. The positive-chord Hamiltonian class

Consider arbitrary real four-player quitting rewards r_i(S), with live and
Never payoff zero, private independent randomization, and unrestricted
behavioral deviations. Put s_i=r_i({i}) and Gamma_ij=r_i({j})-s_i for
i different from j, with diagonal zero. Suppose positive scaling of
payoff rows and relabeling puts the singleton matrix in the form

    Gamma = [ 0   a   e  -1 ]
            [-1   0   b   g ]
            [-f  -1   0   c ]
            [ d  -h  -1   0 ],

where a,b,c,d,e,g,h>0 and f<0. Thus the opposite pair 02 is mutually
positive, every other reciprocal pair has opposite signs, and there is
a negative Hamiltonian cycle 0,1,2,3. Own levels and all higher coalition
rewards are unrestricted.

Every such original table has a uniform-equilibrium
payoff. The scope differs from the reciprocal-opposition classification:
the strict product Gamma_02 Gamma_20 is positive here. The proof produces
a legal expanding four-cycle using the same direct singleton consumer,
but its support census and lower endpoint argument are different.

## 2. Inherited source and the easy exit

Suppose the original table had no uniform-equilibrium payoff. The exact
same-table full-Q reduction follows from
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
and `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`.
Thus Gamma is standard Q: every offset has a nonnegative complementary
solution. Positive row scaling preserves this assertion and preserves
original-game utility comparisons and UE existence.

Only the triple 013 has a cyclic tournament of reciprocal signs. Its
determinant is Delta1=adg-h. The other triples either contain the positive
pair 02 and have a nonnegative column, or are transitive and have a
nonnegative column. Every proper pair and singleton is also projective Q.
If Delta1>=0, the cyclic triple is standard Q for positive determinant,
or has a positive homogeneous kernel for zero determinant. The full
matrix is standard Q, so every principal is projective Q. The checked
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`
then contradicts nonexistence. The cyclic determinant classification is
`standardQ_and_noHomogeneous_iff_orientation_and_det_pos` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`.

It remains to handle Delta1<0. Define Delta2=cde-f>0.

## 3. A large negative offset forces one inverse column

Write LCP offset as -y, with y strictly positive. Fix y0,y2,y3 and let
y1 tend to infinity. Every complementary solution on an active support S
satisfies Gamma_SS x_S=y_S with x_S strictly positive.

Singleton support is impossible. A reciprocal opposite-sign pair cannot
map a nonnegative vector to a strictly positive vector. The only other
pair is 02; it is invertible and its solution is fixed by y0,y2.
For support 023, the determinant is Delta2>0, so its solution is fixed by
y0,y2,y3. Both such supports have a bounded exterior row at owner 1,
and therefore fail for large y1.

Support 013 is a negative-determinant cyclic triple. Its inverse is
strictly negative, so it cannot map a nonnegative vector to y_S>0.
Support 123 has its owner-3 row nonpositive and also cannot do so.
Finally, on support 012 the two equations

    a x1+e x2=y0,
    (-f)x0-x1=y2

bound all three nonnegative variables independently of y1. Consequently
the equation -x0+b x2=y1 fails for sufficiently large y1. This is an
explicit support argument; no nonsingularity of this triple is needed.

Hence every solution for all sufficiently large y1 has full support.
The same conclusion holds on an open set of y by the uniform bounds
when the other three coordinates range in small positive compact
intervals. Standard Q now implies that Gamma maps an open set onto that
open set of y, and so Gamma is invertible. Letting y1 tend to infinity
in its strictly positive full solution gives

    Gamma^(-1)e1 >= 0.

The diagonal cofactor at owner 1 is Delta2>0. The inverse-column sign
therefore forces det Gamma>0. Exact adjugate expansion gives

    adj(Gamma)e1 =
      (1-ac+ceh, Delta2, d+fh-acd, -af+de+efh).

In particular

    d+fh >= acd > 0,
    c(a-eh) <= 1.

These are produced by the same-table Q source, not additional raw guards.

## 4. Produce the positive expanding Hamiltonian ray

Start from v=(0,1,r,0). Successive column moves 0,1,2,3 have durations

    t0=1,
    t1=r-f,
    t2=d-h(r-f),
    t3=a(r-f)+e[d-h(r-f)].

Every duration is positive and every intermediate vector is nonnegative
when 0<r<R, where R=f+d/h=(d+fh)/h>0. The endpoint is (0,x',y',0),
with return matrix

    M = [ga  b+ge] [-f      1] = [A B].
        [ca   ce ] [d+hf  -h]   [C D]

Direct expansion gives

    det M=abcd>0,
    det(I-M)=-det Gamma<0,
    C=c[-af+e(d+fh)]>0,
    D=c(a-eh)<=1,
    D+C/R=acd/(d+fh)<=1.

The characteristic polynomial is negative at one and has positive
constant term. It has two distinct positive roots
0<lambda_minus<1<lambda_plus. Put lambda=lambda_plus and

    r=C/(lambda-D).

Since C>0 and lambda>D, r>0. Since lambda>D+C/R, r<R.
The second eigenvector equation is immediate; the characteristic equation
then gives the first. Thus M(1,r)=lambda(1,r), and all four durations are
strictly positive. The lower endpoint does not need a passive-row test:
f<0 makes r>0 already stronger than r>f.

## 5. The actual strategic consumer

Let T=sum t_j and alpha=(lambda-1)/T. Starting from native continuation
alpha v, prepend owner j with hazard

    q_j=alpha t_j/(1+alpha sum_(k<j)t_k+alpha t_j),

in construction order 0,1,2,3. The value is the unnormalized column
path divided by one plus accumulated scaled time. It remains nonnegative,
and the moving owner's value is zero. At the end its value is
alpha lambda v/(1+alpha T)=alpha v. The reverse chronological word is
therefore an exact periodic singleton Bellman cycle, with joint survival
1/lambda<1 and positive opponent hazard for every player.

The corresponding supplied-certificate consumer is
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
Its singleton arcs, owner equalities, all singleton floors and opponent
divergence have just been produced. Its arbitrary signed-own and
arbitrary-higher-reward scope is essential here.

Equivalently, subdivide every singleton block into sufficiently small
hazards without changing its survival or coarse value. Every intermediate
value remains on its original nonnegative segment. With H the maximum
positive native joining-pair reward and every microhazard at most delta,
the full-cap excess satisfies

    d_i' <= max(H delta,d_i).

For the moving owner it is unchanged. Iterating this exact maximum
recursion caps every finite deadline without an error proportional to
word length. Opponent survival tending to zero adds literal Never and
every behavioral mixture. Original own levels shift every prescribed and
deviating terminal payoff by the same s_i because opponents absorb surely.
The uniform opponent tail bound transfers to finite-horizon payoffs with
one fixed target s+alpha v, independently of delta. This proves the
core conclusion.

## 6. Exact singleton control

A rational matrix in the remaining chamber is

    Gamma = [ 0    5/4   3/2  -1  ]
            [-1     0   9/4   1/4]
            [ 1/4  -1     0   1/4]
            [ 2   -3/2   -1    0 ].

It has det Gamma=27/16 and Delta1=-7/8. Its return matrix is

    M = [139/32  -29/8]
        [ 11/16   -1/4],

with eigenvalues (131 plus/minus sqrt(11401))/64. The larger-ray
ratio lies between zero and 13/12. The smaller eigenvalue is below one.
This matrix has a mutually positive pair and lies outside the reciprocal-
opposition theorem's raw scope. A bounded random search suggested this
chamber before the support proof was derived; that search is no premise
of the theorem and no exhaustive claim is made from its counts.

Section10 specifies all sixty original reward coordinates and audits the
compared matrix, root, quiet-child, punishment, weighted, phase and pole
families. In particular its grand participant premiums are positive, so it
is not an additive completion already covered by the product-low theorem.

## 7. The non-Hamiltonian two-triangle chamber

The remaining strongly connected five-edge negative graph is

    0->1, 1->2, 2->0, 0->3, 3->2.

Its missing pair 13 is mutually positive. Positive row scaling puts its
singleton matrix in the form

    Gamma = [ 0   a  -1   g ]
            [-1   0   b   p ]
            [ c  -1   0  -e ]
            [-1   q   d   0 ],

with all eight parameters positive. Its cyclic triples are 012 and 023,
with determinants D1=abc-1 and D2=cdg-e. The other triples have a
nonnegative column and so are projective Q. If D1,D2>=0 the full-Q
source again gives the projective-Q-bar exit.

For the good triple 012, meaning D1>0, multiply its exterior inverse row
by D1. The resulting three entries are

    n=(bcq-b+d, acd+cq-1, -ab+ad+q).

This row fails nonnegativity exactly when n2=a(d-b)+q<0. Indeed if
n2>=0 then n1>=abc-1=D1>0. If d>=b then n0>0 directly; if b>d,
q>=a(b-d) implies n0>=(b-d)D1>0. Thus failure requires b>d.
For the good triple 023, meaning D2>0, the corresponding row is

    m=(be+cdp-de, bg-dg+p, bcg+cp-e).

It fails nonnegativity exactly when its middle entry m2=g(b-d)+p<0
(the labels here are the actual coordinates 0,2,3). If m2>=0 then
m3>=cdg-e=D2>0. If b>=d then m0>0 directly; if d>b then
p>=g(d-b) gives m0>=(d-b)D2>0. Thus this failure requires d>b.
These implications alone already prevent both good triples from failing.

Suppose exactly one determinant is positive and the other is negative.
If its passive row is nonnegative, the raw passive-row inverse consumer
already gives UE. Otherwise fix y0,y1,y3>0 and let y2 tend to infinity
in LCP(Gamma,-y). Here is the entire proper-support census:

* A singleton or an opposite-sign pair cannot map a nonnegative vector
  to a strictly positive vector. Pair 13 can do so internally, but its
  exterior row 2 is (-1,-e), which violates the positive residual target.
* Triple 123 has its row 2 strictly negative off diagonal, so cannot
  support such a solution. Triple 013 is invertible, with determinant
  -ap-gq<0; its solution depends only on the fixed y0,y1,y3, so its
  exterior row cannot dominate y2 for large y2.
* A nonpositive-determinant cyclic triple cannot map a nonnegative
  vector to a strictly positive vector. For a positive-determinant
  cyclic triple, the failed passive row has a negative coefficient
  precisely at the varying coordinate 2, by the preceding formulas.
  Its exterior residual therefore eventually fails.

Thus every solution has full support for all sufficiently large y2,
uniformly on a small open box for the other coordinates. Full standard Q
implies invertibility and Gamma^(-1)e2>=0. But exact expansion gives

    adj(Gamma)e2 =
      (-adp-bgq-pq, -bg+dg-p, -ap-gq, ab-ad-q).

The negative diagonal entry forces det Gamma<0. When triple 012 is good
and fails its passive test, the last adjugate entry is -n2>0. When triple
023 is good and fails, the second entry is -m2>0. Either would give a
negative entry of Gamma^(-1)e2, a contradiction. This closes the mixed
case. Cases with one positive and the other zero were already covered by
D1,D2>=0.

It remains that D1,D2<=0 with at least one strictly negative. The same
large-y2 census excludes every proper support: both cyclic triples now
fail internally. We obtain a unique strictly positive full-support root,
invertibility, and again det Gamma<0 from adj(Gamma)_22=-ap-gq<0.
This is incompatible with the actual no-UE degree source. The same-table
no-homogeneous source gives full R0: a nonzero homogeneous nonnegative
complementary vector could be normalized to a homogeneous simplex vector.
The exact equivalence is `isR0Matrix_iff_not_singletonLCPFeasible` in
`MathUE/LinearProgramming/CopositiveQ.lean`. The full-core transport above
identifies this with the original full singleton matrix.

The inspected theorem `singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
says that an R0 singleton matrix of an original no-UE game has degree one.
There is no extra positive-own or auxiliary no-UE assumption. On the other
hand, `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` computes the degree from all
roots at any test offset with strict complementarity and nonsingular
active principals. At the chosen -y there is exactly one root, it has
full positive support, and its active Jacobian is Gamma with negative
determinant. Strict complementarity has no inactive coordinate to check.
The degree is therefore -1, contradicting one. No genericity of other
principals or other offsets is needed. This closes the entire two-triangle
chamber.

## 8. Exhaust the no-mutually-negative singleton sign graphs

The full theorem is: if, for each i!=j, at least one of Gamma_ij
and Gamma_ji is nonnegative, then the original four-player game has UE,
with arbitrary own levels and higher rewards.

First assume every off-diagonal coordinate is nonzero. Form the oriented
negative graph with edge j->i exactly when Gamma_ij<0. It has no reciprocal
edges. A missing edge is precisely a mutually positive pair. Under no UE,
every column has a negative entry, so every vertex has outdegree at least
one. There are between four and six edges.

If the graph is not strongly connected, it consists of a strongly connected
three-cycle and one singleton. To justify this, a finite directed graph
with every vertex of positive outdegree has a terminal strongly connected
component containing a directed cycle. With no reciprocal edges, that
component has at least three vertices. As the whole graph is not strong,
it has exactly three; the remaining vertex has an edge into it. No edge
can leave the terminal component. Consequently the exterior row c of the
triple is strictly positive and its exterior column has at least one
negative coordinate. Let B be the cyclic triple. If det B>0, then B^-1>0
and cB^-1>0 gives the passive-row exit. If det B<=0, choose y_out=1 and
all three child targets equal to a large Y. If x_out=0, every residual
requires Bx_child>=Y*1, which is impossible: for det B<0 its negative
inverse, and for det B=0 its positive left kernel, both rule it out.
If x_out>0, complementarity gives c x_child=1, uniformly bounding every
child coordinate. At a child row i where Gamma_i,out<0, the residual
Gamma_i x is bounded above independently of x_out and Y. For large Y it
cannot reach its target. This contradicts standard Q. Thus the graph
must be strongly connected.

With four edges every vertex has outdegree one, and strong connectivity
makes the graph a directed four-cycle. It has no directed triangle; every
proper principal has a nonnegative column. Full Q then gives Q-bar UE.
With six edges the graph is a tournament, handled by the complete strict
reciprocal-opposition proof in Section9.

With five edges, if there is a directed Hamiltonian cycle, the missing
pair is opposite on that cycle. Rotate it to pair 02. The remaining
opposite chord can be made positive in entry 13 by rotating the cycle
two positions if necessary. Row normalization gives exactly Sections1--5:
f<0 and the other seven parameters positive.

If there is no Hamiltonian cycle, choose a directed triangle, which must
exist: a shortest directed cycle has length three or four, and length four
would already be Hamiltonian. The remaining vertex needs both an incoming
and an outgoing edge for strong connectivity. These use the two remaining
edges, and their triangle endpoints are distinct because reciprocal edges
are forbidden. Write these edges u->outside->v. If u->v is an edge of the
triangle, replacing it by this two-step path gives a Hamiltonian cycle.
Otherwise v->u is the triangle edge, and the graph is precisely the two
triangles sharing that edge in Section7, up to relabeling. This completes
the strict sign census without any computational premise.

For off-diagonal zeros, perturb each literal off-own singleton reward by
arbitrarily little so every reciprocal pair remains free of two negative
entries and both entries become nonzero. For example, replace a zero
opposite a negative entry by a small positive number, a zero opposite a
positive entry by a small positive number, and two zeros by two small
positive numbers. Leave all other coordinates, all own levels and all
higher rewards unchanged. The strict theorem applies to each approximant,
and `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
gives UE for the original table with its required fixed-payoff quantifier.

Every remaining Fin4 counterexample must therefore have a mutually
strictly negative singleton pair. Full Fin4 is not closed by this theorem.

## 9. Complete strict-tournament argument used by the sign census

For completeness the tournament branch is proved here, with no appeal to
another unformalized packet. The source and exits concern the same original
reward table. Besides standard Q, the no-UE source excludes a nonzero
homogeneous LCP vector, as supplied by
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
and the full-core transport in Section2. A nonnegative column would itself
be homogeneous; its exclusion is also the direct conclusion of
`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform` in
`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`.

Only strongly connected tournaments need consideration, because Section8
handles every nonstrong oriented negative graph. Every strongly connected
four-tournament has a directed Hamiltonian cycle: choose a directed triangle
and the fourth vertex; it has both incoming and outgoing triangle neighbors,
so some triangle edge can be replaced by a path through that vertex. Rotate
the Hamiltonian cycle so both opposite chords in entries 02 and 13 are
positive. The four possible orientations of the two chords are interchanged
transitively by the four rotations. Positive row scaling yields exactly
Section1's displayed matrix, now with all a,b,c,d,e,f,g,h strictly positive.
Its only cyclic triples are 013 and 023, with determinants

    Delta1=adg-h, Delta2=cde-f.

Every transitive triple has both a nonnegative column and a nonpositive
row. Every opposite-sign pair and every singleton similarly has a
nonnegative column and cannot map a nonnegative vector to a strictly
positive vector. For a cyclic triple, the adjugate is strictly positive.
Positive determinant gives a strictly positive inverse and standard Q;
negative determinant gives a strictly negative inverse, hence forbids a
positive image of a nonnegative vector. At determinant zero there are
strictly positive right and left kernels; the former is homogeneous and
the latter forbids such a positive image.

If both Delta values are nonnegative, all proper principals are projective
Q. Together with full standard Q this supplies the Q-bar exit in Section2.
If both are nonpositive with at least one negative, every proper support
is impossible at every offset -y, y>>0. Thus standard Q supplies a full
positive solution to Gamma x=y for every positive y. The range contains
an open set, proving invertibility; taking y towards each coordinate vector
then gives Gamma^-1>=0. A negative cyclic determinant is a diagonal
cofactor, so det Gamma<0. The checked theorem
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`
consumes precisely this determinant sign and nonnegative inverse and yields
UE, with arbitrary higher rewards.

The only remaining case has one strictly positive and one strictly negative
Delta. Let S be the good cyclic triple, o its missing owner, B=Gamma_SS,
and R=Gamma_oS B^-1. If R>=0, the passive-row inverse exit applies. The exact
consumer is
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
Otherwise R has a negative coordinate. The good triple is the only proper
principal that can support an LCP at offset -y with y>>0. Fix y_S and let
y_o tend to infinity; its exterior residual R y_S-y_o becomes negative.
Every solution must therefore have full support, uniformly on a small
open box for y_S. Standard Q forces invertibility and

    Gamma^-1 e_o>=0, det Gamma>0,

where the second conclusion follows from the positive diagonal cofactor
Delta_good. Define M=[[A,B0],[C,D]] by the return in Section4. Its determinant
is abcd>0 and det(I-M)=-det Gamma<0, so its eigenvalues satisfy
0<lambda_minus<1<lambda_plus. The legal interval is now f<r<R0=f+d/h.
The following two exact endpoint arguments place the expanding ray inside it.

When Delta1>0>Delta2, the outside row of triple 013, multiplied by Delta1,
is

    (n0,n1,n3)=(ch-dg-fgh, acd-d-fh, ac-afg-1).

If n0>=0, then c>=dg/h+fg, giving n3>=Delta1/h>0 and
n1>=(d/h+f)Delta1>0. Thus the passive-row failure means n0<0.
The omitted inverse column has adjugate entries

    (B0, 1-d(b+ge), Delta1, a-abd-eh).

Hence B0>=0 and d(b+ge)<=1. In fact B0>0: equality implies
ag=h(b+ge), giving Delta1=h[d(b+ge)-1]<=0, a contradiction.
Put r=(lambda_plus-A)/B0. The eigenvector equations follow from the
characteristic polynomial, and A+B0*f=d(b+ge)<=1 gives r>f. At R0 set
ell=A+B0*R0=adg/h>1. The projective return there equals c/g<R0 by n0<0.
Writing chi(t)=det(tI-M), direct expansion gives

    chi(ell)=B0*ell*(R0-c/g)>0.

Since ell>1>lambda_minus, ell>lambda_plus. Thus r<R0.

When Delta1<0<Delta2, the outside row of triple 023, multiplied by Delta2,
is

    (m0,m2,m3)=(bcd-c+fg, bd+deg-1, bf-ce+efg).

If m3>=0 then m2=(d*m3+Delta2)/f>0. Also m0>0: it is direct when
g>=c/f, and otherwise follows from
m0=(cd/f)m3+Delta2(c/f-g)>0. Passive-row failure therefore means m3<0.
The omitted inverse column has the same adjugate entries as Section3,
so C>=0, D<=1 and acd/(d+fh)<=1. In fact C>0: C=0 would imply
a=e(d+fh)/f and acd=(cde/f)(d+fh)>d+fh, a contradiction.
Put r=C/(lambda_plus-D)>0. This is an eigenvector ratio. The identity
D+C/R0=acd/(d+fh)<=1 gives r<R0. At the lower endpoint let
ell=D+C/f=cde/f>1. The failed passive coefficient m3<0 gives
ce/(b+ge)>f, equivalently A+B0*f=d(b+ge)<ell. The exact identity

    chi(ell)=(C/f)[ell-(A+B0*f)]>0

therefore implies ell>lambda_plus, hence
r=C/(lambda_plus-D)>C/(ell-D)=f.

In either mixed case all four durations in Section4 are strictly positive,
all intermediate values are nonnegative, and M(1,r)=lambda_plus(1,r).
The complete singleton consumer of Section5 produces a fixed original-game
uniform payoff. This finishes the strict-tournament branch and makes
Section8's full sign classification self-contained.

## 10. Complete original-table calibration and overlap

### 10.1. The complete original table

Let I={0,1,2,3}, set every own singleton to one and leave live and Never
payoffs zero. Define

    G=[ 0    5/4   3/2  -1  ]
      [-1     0   9/4   1/4]
      [ 1/4  -1     0   1/4]
      [ 2   -3/2  -1     0 ],

    L=[ 0    -2   -2   1 ]
      [ 1     0   -2  -2 ]
      [ 9/10  1    0  -2 ]
      [-2    11/10 1   0 ],
    C=(2,2,1,1).

For EVERY nonempty coalition S and recipient i, put

    r_i(S)=1+sum_(j in S)G_ij
              +1_(i in S) sum_(j in S)L_ij
              +C_i 1_(I minus{i} subset S)+E_i(S),       (1)

where E equals one at exactly (i,S)=(0,013),(0,023), and zero elsewhere.
This is a literal specification of all sixty original absorbing rewards.
The C terms cancel from every joining difference. The E terms change only
two participant triple coordinates. Write Z_i(S)=r_i(S)-1 for nonempty S;
the auxiliary centered game retains its own literal Never payoff zero.
Original AllNever is not a Nash profile, since every own singleton is one.

For audit convenience, the complete native vectors are:

| S | Z(S) |
| --- | --- |
| 0 | (0,-1,1/4,2) |
| 1 | (5/4,0,-1,-3/2) |
| 2 | (3/2,9/4,0,-1) |
| 3 | (-1,1/4,1/4,0) |
| 01 | (-3/4,0,-3/4,1/2) |
| 02 | (-1/2,5/4,23/20,1) |
| 03 | (0,-3/4,1/2,0) |
| 12 | (11/4,1/4,0,-5/2) |
| 13 | (1/4,-7/4,-3/4,-2/5) |
| 23 | (1/2,5/2,-7/4,0) |
| 012 | (-5/4,1/4,23/20,1/2) |
| 013 | (1/4,-7/4,1/2,-2/5) |
| 023 | (1/2,7/2,-3/5,0) |
| 123 | (15/4,-3/2,-7/4,-2/5) |
| 0123 | (3/4,1/2,2/5,3/5) |

### 10.2. Matrix and source screens

The singleton determinant is 27/16, and

    G^(-1)=[-19/54  20/27  -58/27   41/36]
           [-13/27  16/27  -68/27   11/18]
           [  1/54  16/27  -14/27   13/36]
           [-85/54  44/27 -106/27   47/36].             (2)

All eleven principal minors of size at least two are nonzero. Every
singleton column has a negative entry. Consequently G is R0. Its LCP
at offset -1 has exactly one solution:

    support 023, x=(13/8,0,9/4,19/8),
    Gx-1=(0,97/32,0,0).

The active determinant is one, so the finite-support degree formula gives
degree one and standard Q. This uses
`r0Degree_eq_sum_admissible_inverse_supports` in
`MathUE/LinearProgramming/FiniteSupportDegree.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`; the checker exhausts the finite
support census. Thus the elementary non-Q source exit does not settle
this table. G also maps a strictly positive vector to a strictly positive
vector, by slightly increasing the zero coordinate in the displayed x.

The principal triple determinants, in lexicographic order, are
(141/64,-7/8,1,-19/32). Every triple inverse has a negative entry; the
inverse on 013 is strictly negative. That negative cyclic triple is
neither standard Q nor homogeneous, so projective Q-bar fails. The full
inverse has a mixed-sign first column. Neither full positive-inverse nor
signed-inverse-column criteria apply under any relabeling. No triple has
a nonnegative inverse, so the raw positive-inverse child criterion fails
before any exterior-row comparison. For the sole mutually positive pair
02, its exterior inverse rows are (3/2,-4) and (-2/3,8), so a pair inverse
with nonnegative exterior rows fails as well.

These are matrix screens, distinct from a strategy-specific source
condition. The following stronger source screen also holds: every member
M(p)=G-p(G+L), 0<=p<=1, is R0. Here is a complete support proof, without
sampling p. The four cyclic entries M_(j+1),j are identically -1, so a
singleton kernel cannot have nonnegative exterior residuals. No pair has
both entries zero: outside pair02 the entries have opposite strict signs,
and M02=(3+p)/2>0. On triple012 row0 is strictly positive off diagonal;
on triple123 row3 is strictly negative. Neither can have a positive
kernel. On 023 the determinant is

    (35p^2+87p+20)/20>0.

On 013 the first adjugate column is

    (-(4p-15)(7p+1)/40, (7p+1)/2, -(4p-15)/10)>0.

If this triple is singular, it has rank two and that column spans its
kernel. The outside row times this column is

    (7p+1)(92p^2-445p-25)/800<0,

since 92p^2-445p-25<=-353p-25. It cannot support a full homogeneous LCP.
Finally the first and third entries of the full first adjugate column are

    -(7p+1)(4p^2-51p+95)/160<0,
    -(7p+1)(92p^2-445p-25)/800>0.

The first quadratic is at least 44 on [0,1], and the other bound was just
shown. If the full matrix is singular, its nonzero adjugate implies rank
three and its kernel is mixed-sign. This exhausts every support.

One reciprocal polynomial guard DOES vanish:
G03(G+L)30-G30(G+L)03=0. No genericity claim is made for this calibration.
The direct new existence theorem does not require generic guards. Failure
of such a guard is not itself an old unconditional UE producer.

### 10.3. Entire quiet-child family

For any child A and outside o the literal capped-clock certificate needs
nonnegative weights w_i, i in A, satisfying

    F_S: sum_i w_i[1-r_i(S)]>=1-r_o(S),
    J_S: sum_i w_i[r_i(S+i)-r_i(S)]>=r_o(S+o)-r_o(S)

for every nonempty S subset A, as well as its Never row. The fields are
those of `CappedClockParentRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`.
For every child, this table gives a positive combination with nonpositive
coefficients and strictly positive lower bound. Thus no choice of weights
works, even after allowing an arbitrary Never-row slack.

| A | o | Combination | Coefficients in increasing A | Lower bound |
| --- | --- | --- | --- | --- |
| 0 | 1 | J0 | (0) | 1 |
| 1 | 2 | J1 | (0) | 1 |
| 2 | 3 | J2 | (0) | 1 |
| 3 | 0 | J3 | (0) | 1 |
| 01 | 2 | J1 | (-2,0) | 1 |
| 02 | 1 | F0 | (0,-1/4) | 1 |
| 03 | 1 | F0 | (0,-2) | 1 |
| 12 | 3 | F2 | (-9/4,0) | 1 |
| 13 | 0 | F3 | (-1/4,0) | 1 |
| 23 | 0 | J3 | (-2,0) | 1 |
| 012 | 3 | F12 | (-11/4,-1/4,0) | 5/2 |
| 013 | 2 | J01 | (0,0,-9/10) | 19/10 |
| 023 | 1 | 10J0+18F03 | (0,0,-20) | 47/2 |
| 123 | 0 | F3 | (-1/4,-1/4,0) | 1 |

An individual child/outside pair can still pass. The claim is that every
complete child choice has an impossible outsider, which is the required
quantifier for excluding a quiet lift.

### 10.4. Every sure-owner and persistent-base punishment selection

In the native auxiliary game at continuation zero, the exact forced-Quit
minus Continue polynomials are

    F0=-2q1-2q2+q3+q1q3(1-q2)+q2q3(1-q1),
    F1=q0-2q2-2q3,
    F2=(9/10)q0+q1-2q3,
    F3=-2q0+(11/10)q1+q2.                              (3)

Fix owner j surely at Quit. The complementary owners have these same
gaps in the original game, since the sure opponent eliminates any
continuation term. Their COMPLETE Nash correspondences are:

| j | All complementary Nash points | Range | Owner Continue-minus-Quit |
| --- | --- | --- | --- |
| 0 | (1,0,1,0) | one point | 2 |
| 1 | (t,1,0,1) | 0<=t<=11/20 | 2-t>=29/20 |
| 2 | (t,0,1,1) | 0<=t<=1/2 | 2-(9/10)t>=31/20 |
| 3 | (1,0,0,1) | one point | 2 |

The face argument is exhaustive, including the singular segments. For
j=0, if q1>0 then F1>=0 gives q2+q3<=1/2. Therefore
F3<=-9/10+q2<0, forcing q3=0, after which F2>0 forces q2=1, a
contradiction. Thus q1=0. Now F3=-2+q2<0 forces q3=0 and F2>0 forces
q2=1. For j=1,

    F0=-2-2q2+2q3-q2q3<=-3q2.

If q0>0 this forces q2=0,q3=1. If q0=0, then F3>0 forces q3=1,
and F2<0 forces q2=0. The remaining condition is F3=11/10-2q0>=0.
For j=2 the same formula with q1 in place of q2 shows that q0>0
forces q1=0,q3=1. If q0=0, F1<0 forces q1=0 and F3>0 forces q3=1.
The remaining condition is F3=1-2q0>=0. For j=3, F1<0 forces q1=0,
then F2<0 forces q2=0, and F0>0 forces q0=1. Direct substitution proves
the converse in all four cases, including all endpoints.

Every point has a sure opponent of j. The coefficient of EVERY supplied
punishment continuation in j's floor is therefore zero; its strictly
positive floor excess cannot be repaired. This uses the literal criterion
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff` and the premises of
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
Every smaller free-set selection extends to the displayed complementary
game through its outsider inequalities. Thus this is not just a census
of maximal free sets.

There is no full Nash root with any sure owner. A persistent base with
at least two owners satisfying all base-leave, outsider and free Nash
tests would yield such a root, as every base owner has a sure opponent.
Hence all choices in `nonempty_quittingPersistentBaseCertificate_of_inducedNash`
and `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`
fail. This also excludes the induced-owner chambers; their Never variant
additionally requires a nonpositive own level, whereas all own levels here
are one. The structures are in
`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`.

There is no absorbing stationary profile on one or two active owners.
For a lone active owner j, the cyclic successor sees G_(j+1),j=-1 and
L_(j+1),j>0, so forced Quit improves over literal Never at every positive
hazard. For an interior active pair, indifference forces
q_j=G_ij/(G_ij+L_ij) in both directions. In EVERY reciprocal pair at
least one direction has G_ij L_ij<0, making its ratio outside (0,1) or
undefined. A sure hazard is already excluded by the complete census.
No exclusion of all stationary profiles is claimed.

### 10.5. Premium, weighted, ledger, and raw phase criteria

Every native grand participant premium is positive. The sure grand product
therefore refutes `HasProductLowQuittingPremium` and the hypothesis of
`exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
It also defeats every nonzero nonnegative weighted forced-Quit upper
average. The only premium trap is I, by the full finite census. In
particular the premium-core-at-most-two/three exits do not apply.

The boxed-charge and mixed-trap alternative fails independently of its
constants: the joining sum at T=01 over its two outsiders is one, and
the joining increment of owner3 at T=012 is 1/10. These contradict the
required nonpositive middle-size sum and negative penultimate row.

For the inserted native premium vector k(S)_i=Z_i(S union{i}),

    (5/2)k(1)+(4/7)k(3)=(-15/8,-1,-1,-1).

Thus there is NO nonzero nonnegative global forced-Quit floor weight.
Every owner also has a below-own participant pair: respectively 01,13,23,13.
No player has nonnegative participant premiums at all its coalitions;
protected-leaver criteria requiring such a player cannot apply.

For the proper-coalition passive vector h(S)=Z(S),

    5h(3)+h(12)+3h(13)+h(23)=(-1,-5/4,-11/4,-37/10).

Hence no nonzero nonnegative passive-ledger weight satisfies all h(S)
rows. Both the two-ledger and graph-free H/J criteria fail before their
joining tests. The proper joining cycle 0->1->3->0 persists as well.
The no-strict-background-reversal criterion fails for receiver0:
joining against {3} gains one, while joining against {1,2,3} loses three.

The all-partition two-pair joining-cap family needs every scheduled
participant at least its passive partner singleton. Each of the three
partitions fails: use receiver0 against1 in 01|23, receiver0 against2
in 02|13, and receiver3 against0 in 03|12. Their gaps are all -2.
This also defeats the corresponding positive-participant variants.
The signed-inverse-column family is already blocked by (2), regardless
of the scheduled pair selection. Bounded inverse corners, nonmatching
positive-passive inverse cones, and positive-inverse coalition jackpots
all fail their baseline inverse condition. These failures include the
generalized jackpot theorem, without an implicit-threshold argument.

There is exactly ONE mutually same-sign singleton pair, namely positive
02, and no mutually negative pair. The fixed favorite/matching and
opposite-sign-matching phase classes require two disjoint same-sign pairs,
so no relabeling fits. The negative-pair-funded boundary and old larger
eigenvalue class require a mutually negative pair, which is absent. The
one-joint-phase cyclic-child raw classes require a positive-inverse triple,
also absent. The only negative Hamiltonian cycle is 0123 and its cyclic
rotations. Its smaller eigenvalue is (131-sqrt(11401))/64<1, so the named
older smaller-eigenvalue raw adapter does not apply.

These are exact raw-family comparisons. They do not claim that arbitrary
unspecified perturbation neighborhoods, or supplied-profile certificates,
have been excluded. A supplied balanced-cycle consumer is expected to
accept the new produced cycle after that cycle has been constructed.

### 10.6. Every old three-passive-pole role selection

For ordered distinct roles (i,j,k,l), the finite raw guards are

    A=r_i(il)-r_i(l)>0, B=r_i(ikl)-r_i(kl)<0, c=A/(A-B),
    A2=r_k(kl)-r_k(l)<0, B2=r_k(ikl)-r_k(il)<0,
    L0=(1-c)[r_j(jl)-r_j(l)]+c[r_j(jkl)-r_j(kl)]<0,
    L1=(1-c)[r_j(ijl)-r_j(il)]+c[r_j(I)-r_j(ikl)]<0,
    F0=c[(1-c)r_l(l)+c r_l(kl)-r_l(k)]>0,
    F1=(1-c)[r_l(il)-r_l(i)]+c[r_l(ikl)-r_l(ik)]<0.

All twenty-four role choices fail at least one of these finite guards.
The verifier evaluates them literally. There is no comparison with an
unknown asymptotic pole threshold. In the E=0 table only roles0123,0213,
3102 pass. Adding E0(023) makes B=0 for0123 and makes B2=0 for3102;
adding E0(013) makes B=0 for0213. The complete final census, rather than
a monotonicity shortcut, also verifies that no other role begins passing.

### 10.7. Actual produced period and a harmful macro collision

For the produced larger root set

    lambda=(131+sqrt(11401))/64,
    rho=44/(147+sqrt(11401)), v=(0,1,rho,0),
    t=(1, rho+1/4, 2-(3/2)(rho+1/4),
                    (5/4)(rho+1/4)+(3/2)[2-(3/2)(rho+1/4)]),
    alpha=(lambda-1)/sum t.

Then 0<rho<1/5, every t is positive, and the exact original target is
(1,1,1,1)+alpha v. Construction-order hazards
alpha t_j/(1+alpha sum_(k<=j)t_k) yield the owner-zero nonnegative
Bellman cycle, with joint survival 1/lambda. The checker verifies these
equalities exactly in the quadratic field.

The unsplit macrocycle is NOT exact Nash. At its owner0 step, owner2's
native Quit advantage is exactly

    [alpha/(1+alpha)](9/10-rho)>0.

Thus the new proof's microhazard refinement is materially used. The maximum
positive native participant pair reward is 23/20. Subdivision bounds every full-cap
excess by (23/20)delta, with no factor for word length, and the period's
opponent survival still contracts. Section5 supplies the
complete-law and signed-own argument; no new strategic premise is being
hidden in this calibration.

The auxiliary zero-continuation native root has only AllContinue: at every
cube vertex with at least two quitters, sum_i q_i F_i(q)<0; at empty and
singleton vertices it is zero. Multiaffine interpolation makes it strictly
negative when at least two hazards are positive. A lone positive hazard
recruits a positive L-column entry. This auxiliary fact is not a claim
that the original own-positive game has an inert AllNever equilibrium.


### 10.8 Negative boundary stress tests

The degree step uses actual no-UE degree one, not standard Q alone. For
the Section7 matrix take

    a=b=c=d=1/2, e=33/64, g=2, p=1/2, q=2.

Then D1=-7/8, D2=-1/64 and det Gamma=-1/32. All nontrivial principal
minors are nonzero and every column has a negative entry, so this matrix
is R0. At y=(1,1,100,1), exact enumeration of every support gives the
unique LCP root (20147/2,1612,13701,6448), with full support and index -1.
The degree obstruction is therefore substantive. With parameters
(a,b,c,d,e,g,p,q)=(2,2,1,1/2,1,1,1,1), the good012 passive row fails,
and inverse column2=(8/7,5/7,6/7,-4/7). At the same y there is no LCP
solution, confirming the mixed-case Q contradiction's sign direction.
The symbolic and support calculations are included in AppendixA.

## 11. Formalization handoff and remaining scope

The intended theorem takes an arbitrary Fin4 reward table and the six
raw disjunctions Gamma_ij>=0 or Gamma_ji>=0. It returns existence of a
uniform-equilibrium payoff for that same original game. It assumes no
strategy, cycle, genericity, inverse column, principal determinant sign,
joining condition or zero-source hypothesis.

A suitable proof decomposition separates the oriented negative-graph census,
the positive-chord large-offset support exclusion, the two-triangle
adjugate/passive-row classification, its unique-root degree computation,
and the strict-tournament endpoint arguments. Existing no-UE declarations
supply full Q, R0 and degree one; existing Q-bar and inverse consumers
supply their exits. The remaining algebra produces a positive expanding
singleton cycle, consumed either by the named balanced certificate or by
the full microstep proof in Section5. Actual reward closure gives every
zero-coordinate boundary. New algebraic helpers must prove their stated
identities and support exclusions rather than accept the desired cycle
or game equilibrium as a structure field.

The full reward calibration has one vanishing generic polynomial guard,
which is explicitly reported. It satisfies the actual whole-pencil R0
condition and lies beyond the compared earlier raw existence families.
No claim excludes every possible supplied-profile consumer: the produced
cycle is exactly an input to such a consumer. The theorem covers all higher
reward completions of its singleton sign class, but games with a mutually
negative pair remain outside it. No new Lean implementation or full Fin4
resolution is claimed.

## Appendix A. Exact matrix, sign and boundary verifier

Save this code in a Python file and run it with Python and SymPy. It checks
all displayed matrix identities, every one of the 729 strict oriented sign
patterns, and exact positive and negative boundary data. The universal
support and strategy arguments above are its mathematical justification;
the enumeration is not a premise replacing their proofs.

```python
"""Exact algebra/sign-graph checks for the no-mutually-negative candidate.

Run with Python and SymPy installed. Universal Q forcing and strategic
semantics are proved in the accompanying mathematical text; finite
enumeration is a falsification aid, not the proof.
"""
from itertools import combinations, permutations, product
from collections import Counter
import sympy as sp

a,b,c,d,e,g,p,q = sp.symbols('a b c d e g p q', positive=True)
G = sp.Matrix([[0,a,-1,g],[-1,0,b,p],[c,-1,0,-e],[-1,q,d,0]])
D1,D2=a*b*c-1,c*d*g-e
assert sp.expand(G.extract([0,1,2],[0,1,2]).det()-D1)==0
assert sp.expand(G.extract([0,2,3],[0,2,3]).det()-D2)==0
assert sp.expand(G.extract([0,1,3],[0,1,3]).det()+a*p+g*q)==0
n=sp.Matrix([[b*c*q-b+d,a*c*d+c*q-1,-a*b+a*d+q]])
m=sp.Matrix([[b*e+c*d*p-d*e,b*g-d*g+p,b*c*g+c*p-e]])
assert G.extract([3],[0,1,2])*G.extract([0,1,2],[0,1,2]).adjugate()==n
assert G.extract([1],[0,2,3])*G.extract([0,2,3],[0,2,3]).adjugate()==m
assert all(sp.expand(x-y)==0 for x,y in zip(G.adjugate()[:,2],
    [-a*d*p-b*g*q-p*q,-b*g+d*g-p,-a*p-g*q,a*b-a*d-q]))
assert sp.expand(n[1]-c*n[2]-D1)==0
assert sp.expand(n[0]-b*c*n[2]-(b-d)*D1)==0
assert sp.expand(m[2]-c*m[1]-D2)==0
assert sp.expand(m[0]-c*d*m[1]-(d-b)*D2)==0

f,h=sp.symbols('f h', real=True)
H=sp.Matrix([[0,a,e,-1],[-1,0,b,g],[-f,-1,0,c],[d,-h,-1,0]])
M=sp.Matrix([[g*a,b+g*e],[c*a,c*e]])*sp.Matrix([[-f,1],[d+h*f,-h]])
assert sp.expand(M.det()-a*b*c*d)==0
assert sp.expand((sp.eye(2)-M).det()+H.det())==0
assert all(sp.expand(x-y)==0 for x,y in zip(H.adjugate()[:,1],
    [1-a*c+c*e*h,c*d*e-f,d+f*h-a*c*d,-a*f+d*e+e*f*h]))
assert sp.factor(M[1,1]+M[1,0]/(f+d/h)-a*c*d/(d+f*h))==0
A,B0,C0,D0=M[0,0],M[0,1],M[1,0],M[1,1]
chi=lambda z:(z-A)*(z-D0)-B0*C0
ell1=a*d*g/h
assert sp.factor(chi(ell1)-B0*ell1*(f+d/h-c/g))==0
ell2=c*d*e/f
assert sp.factor(chi(ell2)-(C0/f)*(ell2-(A+B0*f)))==0

I=range(4)
edges=list(combinations(I,2))
P=[tuple(x) for x in permutations(I)]
canon={
 'four_cycle':sp.Matrix([[0,1,1,-1],[-1,0,1,1],[1,-1,0,1],[1,1,-1,0]]),
 'positive_chord':sp.Matrix([[0,1,1,-1],[-1,0,1,1],[1,-1,0,1],[1,-1,-1,0]]),
 'bowtie':sp.Matrix([[0,1,-1,1],[-1,0,1,1],[1,-1,0,-1],[-1,1,1,0]]),
 'tournament':sp.Matrix([[0,1,1,-1],[-1,0,1,1],[-1,-1,0,1],[1,-1,-1,0]])
}

def reach(T,j):
 seen={j};todo=[j]
 while todo:
  k=todo.pop()
  for i in I:
   if T[i,k]<0 and i not in seen:seen.add(i);todo.append(i)
 return seen

counts=Counter()
for types in product((0,1,2),repeat=6):
 T=sp.zeros(4)
 for (i,j),kind in zip(edges,types):
  T[i,j],T[j,i]=((1,1),(-1,1),(1,-1))[kind]
 if any(all(T[i,j]>=0 for i in I) for j in I):
  counts['nonnegative_column']+=1;continue
 if all(len(reach(T,j))==4 for j in I):
  matches=[name for name,C in canon.items()
           if any(T.extract(order,order)==C for order in P)]
  assert len(matches)==1,(types,matches)
  counts[matches[0]]+=1
 else:
  terminal=[]
  for S in combinations(I,3):
   o=next(i for i in I if i not in S)
   if all(T[o,j]>0 for j in S) and any(T[i,o]<0 for i in S):
    if all(sum(bool(T[i,j]<0) for i in S)==1 for j in S):terminal.append(S)
  assert len(terminal)==1,types
  counts['terminal_triple']+=1
assert sum(counts.values())==729

R=sp.Rational
X=sp.Matrix([[0,R(5,4),R(3,2),-1],[-1,0,R(9,4),R(1,4)],
             [R(1,4),-1,0,R(1,4)],[2,-R(3,2),-1,0]])
assert X.det()==R(27,16)
assert X.extract([0,1,3],[0,1,3]).det()==-R(7,8)
assert all(z>=0 for z in X.inv()[:,1])
roots=[]
for k in (1,2,3,4):
 for S in combinations(I,k):
  B=X.extract(S,S)
  if k==1:continue
  assert B.det()!=0
  z=B.inv()*sp.ones(k,1);x=sp.zeros(4,1)
  for i,v in zip(S,z):x[i]=v
  w=X*x-sp.ones(4,1)
  if all(v>0 for v in z) and all(v>=0 for v in w):roots.append((S,x,w))
assert len(roots)==1
assert roots[0][0]==(0,2,3)
assert roots[0][1]==sp.Matrix([R(13,8),0,R(9,4),R(19,8)])
assert roots[0][2]==sp.Matrix([0,R(97,32),0,0])
print('PASS: symbolic bowtie rows/adjugate and positive-chord return identities')
print('PASS: all729 oriented/missing-edge patterns:',dict(counts))
print('PASS: exact positive-chord R0/degree-one control and forced inverse column')

# Two exact attempted falsifiers for the bowtie forcing/degree argument.
for vals,y,wanted in [
 ((R(1,2),R(1,2),R(1,2),R(1,2),R(33,64),2,R(1,2),2),
  sp.Matrix([1,1,100,1]),-1),
 ((2,2,1,R(1,2),1,1,1,1),sp.Matrix([1,1,100,1]),0)]:
 Y=G.subs(dict(zip((a,b,c,d,e,g,p,q),vals)))
 roots=[]
 for k in (1,2,3,4):
  for S in combinations(I,k):
   B=Y.extract(S,S)
   if k==1:continue
   assert B.det()!=0
   z=B.inv()*y.extract(S,[0]);x=sp.zeros(4,1)
   for i,vv in zip(S,z):x[i]=vv
   w=Y*x-y
   if all(vv>0 for vv in z) and all(vv>=0 for vv in w):
    assert all(w[i]>0 for i in I if i not in S)
    roots.append((S,x,int(sp.sign(B.det()))))
 if wanted==-1:
  assert Y.det()==-R(1,32)
  assert roots==[((0,1,2,3),sp.Matrix([R(20147,2),1612,13701,6448]),-1)]
 else:assert roots==[]
print('PASS: bowtie negative-index and mixed-passive-failure stress tests')
```

## Appendix B. Exact full reward calibration verifier

The following separate complete program checks the literal sixty rewards,
all listed support and selector families, the complete pencil identities,
and the produced irrational period. The exhaustive induced-Nash face
proof is in Section10.4; checking its endpoints alone would not replace it.

```python
"""Exact full60 calibration for the one-positive-chord singleton class.

Run with Python and SymPy installed. All assertions use exact arithmetic.
The universal matrix theorem and exhaustive Nash-face argument are in the
associated mathematical note; this program checks its finite calibration.
"""
from itertools import combinations, permutations, product
import sympy as s

R = s.Rational
I = tuple(range(4))
COAL = tuple(A for n in range(1, 5) for A in combinations(I, n))
G = s.Matrix([[0, R(5, 4), R(3, 2), -1],
              [-1, 0, R(9, 4), R(1, 4)],
              [R(1, 4), -1, 0, R(1, 4)],
              [2, -R(3, 2), -1, 0]])
L = s.Matrix([[0, -2, -2, 1], [1, 0, -2, -2],
              [R(9, 10), 1, 0, -2], [-2, R(11, 10), 1, 0]])
BONUS = (2, 2, 1, 1)
EXTRA = {(0, (0, 1, 3)), (0, (0, 2, 3))}


def reward(i, A):
    A = tuple(sorted(set(A)))
    assert A
    return (1 + sum(G[i, j] for j in A)
            + (sum(L[i, j] for j in A) if i in A else 0)
            + (BONUS[i] if set(I) - {i} <= set(A) else 0)
            + int((i, A) in EXTRA))


def native(i, A):
    return reward(i, A) - 1


def joining(i, A):
    return reward(i, set(A) | {i}) - reward(i, A)


table = {(i, A): reward(i, A) for i in I for A in COAL}
assert len(table) == 60
assert all(reward(i, [i]) == 1 for i in I)
assert all(native(i, [j]) == G[i, j] for i in I for j in I)
assert G.det() == R(27, 16)
assert G.inv() == s.Matrix([
    [-R(19, 54), R(20, 27), -R(58, 27), R(41, 36)],
    [-R(13, 27), R(16, 27), -R(68, 27), R(11, 18)],
    [R(1, 54), R(16, 27), -R(14, 27), R(13, 36)],
    [-R(85, 54), R(44, 27), -R(106, 27), R(47, 36)]])
assert min(G.inv()[:, 0]) < 0 < max(G.inv()[:, 0])
assert [G.extract(T, T).det() for T in combinations(I, 3)] == [
    R(141, 64), -R(7, 8), 1, -R(19, 32)]
assert all(any(v < 0 for v in G.extract(T, T).inv())
           for T in combinations(I, 3))
assert all(v < 0 for v in G.extract([0, 1, 3], [0, 1, 3]).inv())
assert all(G.extract(T, T).det() != 0
           for n in (2, 3, 4) for T in combinations(I, n))
assert all(any(G[i, j] < 0 for i in I) for j in I)
solutions = []
for n in (2, 3, 4):
    for T in combinations(I, n):
        x = s.zeros(4, 1)
        y = G.extract(T, T).inv() * s.ones(n, 1)
        for i, v in zip(T, y):
            x[i] = v
        residual = G * x - s.ones(4, 1)
        if min(x) >= 0 and min(residual) >= 0:
            solutions.append((T, list(x), list(residual), G.extract(T, T).det()))
assert solutions == [((0, 2, 3), [R(13, 8), 0, R(9, 4), R(19, 8)],
                      [0, R(97, 32), 0, 0], 1)]
# These exact support data give R0 and degree one by the standard degree theorem.

# Every member of the full native pencil is R0. The note proves the interval
# signs by the elementary bounds printed there; these are the exact identities.
p = s.symbols('p')
M = G - p * (G + L)
assert all(M[(j+1) % 4, j] == -1 for j in I)
assert s.expand(M[0, 2] - (3+p)/2) == 0
assert s.expand(M.extract([0, 2, 3], [0, 2, 3]).det()-(35*p*p+87*p+20)/20) == 0
A = M.extract([0, 1, 3], [0, 1, 3]).adjugate()[:, 0]
expected_A = [-(4*p-15)*(7*p+1)/40, (7*p+1)/2, -(4*p-15)/10]
assert all(s.expand(a-b) == 0 for a, b in zip(A, expected_A))
assert s.expand((M.extract([2], [0, 1, 3])*A)[0]-(7*p+1)*(92*p*p-445*p-25)/800) == 0
assert s.expand(M.adjugate()[0, 0]+(7*p+1)*(4*p*p-51*p+95)/160) == 0
assert s.expand(M.adjugate()[2, 0]+(7*p+1)*(92*p*p-445*p-25)/800) == 0
# The reciprocal 03 crossing guard is zero. No generic-guard claim is made.
assert G[0, 3]*(G+L)[3, 0] - G[3, 0]*(G+L)[0, 3] == 0

# Actual root endpoint polynomials, derived independently from all 8 opponent
# coalitions. The C bonuses cancel, and only the two indicated E terms remain.
q = s.symbols('q0:4')
F = s.Matrix([
    -2*q[1]-2*q[2]+q[3]+q[1]*q[3]*(1-q[2])+q[2]*q[3]*(1-q[1]),
    q[0]-2*q[2]-2*q[3], R(9, 10)*q[0]+q[1]-2*q[3],
    -2*q[0]+R(11, 10)*q[1]+q[2]])
for i in I:
    others = [j for j in I if j != i]
    gap = 0
    for bits in product((0, 1), repeat=3):
        A = [j for j, b in zip(others, bits) if b]
        prob = s.prod(q[j] if b else 1-q[j] for j, b in zip(others, bits))
        gap += prob * (native(i, A+[i]) - (native(i, A) if A else 0))
    assert s.expand(gap-F[i]) == 0
for bits in product((0, 1), repeat=4):
    value = sum(q[i]*F[i] for i in I).subs(dict(zip(q, bits)))
    assert value == 0 if sum(bits) <= 1 else value < 0

t = s.symbols('t', real=True)
segments = [(0, [1, 0, 1, 0], 0),
            (1, [t, 1, 0, 1], R(11, 20)),
            (2, [t, 0, 1, 1], R(1, 2)),
            (3, [1, 0, 0, 1], 0)]
floors = [2, 2-t, 2-R(9, 10)*t, 2]
for (owner, vec, upper), floor in zip(segments, floors):
    gaps = F.subs(dict(zip(q, vec)))
    assert s.expand(-gaps[owner]-floor) == 0
    for i in I:
        if i == owner:
            continue
        if vec[i] == t:
            assert gaps[i] == 0
        else:
            sign = 1 if vec[i] == 1 else -1
            assert min((sign*gaps[i]).subs(t, z) for z in (0, upper)) >= 0
    assert min(s.sympify(floor).subs(t, z) for z in (0, upper)) > 0

# Literal capped-clock rows: coefficients dot nonnegative weights >= rhs.
def rows(child, outsider):
    out = {('N', ()): ([s.S.One]*len(child), s.S.One)}
    for A in COAL:
        if set(A) <= set(child):
            out['F', A] = ([1-reward(i, A) for i in child], 1-reward(outsider, A))
            out['J', A] = ([joining(i, A) for i in child], joining(outsider, A))
    return out


BLOCKERS = [
    ((0,), 1, [('J', (0,), 1)]), ((1,), 2, [('J', (1,), 1)]),
    ((2,), 3, [('J', (2,), 1)]), ((3,), 0, [('J', (3,), 1)]),
    ((0, 1), 2, [('J', (1,), 1)]), ((0, 2), 1, [('F', (0,), 1)]),
    ((0, 3), 1, [('F', (0,), 1)]), ((1, 2), 3, [('F', (2,), 1)]),
    ((1, 3), 0, [('F', (3,), 1)]), ((2, 3), 0, [('J', (3,), 1)]),
    ((0, 1, 2), 3, [('F', (1, 2), 1)]),
    ((0, 1, 3), 2, [('J', (0, 1), 1)]),
    ((0, 2, 3), 1, [('J', (0,), 10), ('F', (0, 3), 18)]),
    ((1, 2, 3), 0, [('F', (3,), 1)])]
assert {C for C, _, _ in BLOCKERS} == {C for C in COAL if len(C) < 4}
for C, o, terms in BLOCKERS:
    rr = rows(C, o)
    coeff = [sum(w*rr[k, A][0][j] for k, A, w in terms) for j in range(len(C))]
    rhs = sum(w*rr[k, A][1] for k, A, w in terms)
    assert all(w > 0 for _, _, w in terms)
    assert max(coeff) <= 0 and rhs > 0

traps = [A for A in COAL if all(any(i in B and set(B) <= set(A)
         and native(i, B) > 0 for B in COAL) for i in A)]
assert traps == [I]
assert [native(i, I) for i in I] == [R(3, 4), R(1, 2), R(2, 5), R(3, 5)]
assert joining(2, [0, 1]) + joining(3, [0, 1]) == 1
assert joining(3, [0, 1, 2]) == R(1, 10)
floor_dual = [(R(5, 2), (1,)), (R(4, 7), (3,))]
assert [sum(w*native(i, set(A) | {i}) for w, A in floor_dual) for i in I] == [
    -R(15, 8), -1, -1, -1]
ledger_dual = [(5, (3,)), (1, (1, 2)), (3, (1, 3)), (1, (2, 3))]
assert [sum(w*native(i, A) for w, A in ledger_dual) for i in I] == [
    -1, -R(5, 4), -R(11, 4), -R(37, 10)]
assert all(any(i in A and native(i, A) < 0 for A in COAL) for i in I)
assert joining(0, [3]) == 1 and joining(0, [1, 2, 3]) == -3
partitions = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
assert all(any(joining(i, [j]) < 0 for A in P for i, j in (A, A[::-1]))
           for P in partitions)
assert sum(bool(G[i, j]*G[j, i] > 0) for i, j in combinations(I, 2)) == 1
assert all(not (G[i, j] < 0 and G[j, i] < 0) for i, j in combinations(I, 2))

# Exhaust every role assignment of the old three-passive-pole finite guards.
passing = []
for i, j, k, l in permutations(I):
    a, b = joining(i, [l]), joining(i, [k, l])
    if not (a > 0 and b < 0):
        continue
    c = a/(a-b)
    a2, b2 = joining(k, [l]), joining(k, [i, l])
    l0 = (1-c)*joining(j, [l])+c*joining(j, [k, l])
    l1 = (1-c)*joining(j, [i, l])+c*joining(j, [i, k, l])
    f0 = c*((1-c)*reward(l, [l])+c*reward(l, [k, l])-reward(l, [k]))
    f1 = (1-c)*joining(l, [i])+c*joining(l, [i, k])
    if a2 < 0 and b2 < 0 and l0 < 0 and l1 < 0 and f0 > 0 and f1 < 0:
        passing.append((i, j, k, l))
assert passing == []

# Exact produced larger eigenray and normalized owner-zero Bellman period.
lam = (131+s.sqrt(11401))/64
lam_small = (131-s.sqrt(11401))/64
ratio = 44/(147+s.sqrt(11401))
ret = s.Matrix([[R(139, 32), -R(29, 8)], [R(11, 16), -R(1, 4)]])
assert all(s.simplify(z) == 0 for z in ret*s.Matrix([1, ratio])-lam*s.Matrix([1, ratio]))
assert 0 < lam_small < 1 < lam
assert 0 < ratio < R(1, 5)
durations = [1, ratio+R(1, 4), 2-R(3, 2)*(ratio+R(1, 4)),
             R(5, 4)*(ratio+R(1, 4))+R(3, 2)*(2-R(3, 2)*(ratio+R(1, 4)))]
alpha = s.simplify((lam-1)/sum(durations))
v = s.Matrix([0, 1, ratio, 0])
u = alpha*v
accumulated = 0
survival = 1
for j, duration in enumerate(durations):
    eta = alpha*duration/(1+accumulated+alpha*duration)
    assert s.simplify(u[j]) == 0
    u = ((1-eta)*u+eta*G[:, j]).applyfunc(s.simplify)
    assert all(z >= 0 for z in u)
    accumulated += alpha*duration
    survival *= 1-eta
assert all(s.simplify(z) == 0 for z in u-alpha*v)
assert s.simplify(survival-1/lam) == 0
# At the owner0 macrostep, owner2's exact Quit advantage is positive.
assert R(9, 10)-ratio > 0
print('PASS: full60, matrix/Q data, entire-pencil identities, all quiet children,')
print('sure-owner Nash endpoint checks, premium/ledger/phase screens, all24 poles,')
print('and the exact produced Bellman cycle with a harmful unsplit macrostep.')
```
