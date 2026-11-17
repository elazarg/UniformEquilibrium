# Uniform equilibrium for every proportional additive four-player quitting game

Let Gamma be any real hollow four-by-four matrix, ell any real four-vector,
and u any positive real. Four players use independent private stopping laws
on positive integer dates and Never. Live and joint Never pay zero. When
the first nonempty coalition S quits, each player i receives ell_i plus

    Z_i(S) = sum_{j in S} Gamma_ij       if i is outside S,
           = -u sum_{j in S} Gamma_ij    if i is in S.

**Theorem.** Every game with these rewards has a uniform-equilibrium payoff.
One target is fixed before the accuracy request. For every accuracy there
is a behavioral profile giving that target to within the requested error
and bounding all unilateral behavioral gains by that error at every
sufficiently long finite average horizon. The twelve singleton comparisons,
four signed own levels and common positive factor are unrestricted.

The proof closes the mutually positive singleton pairs left by the
[interleaved return](INTERLEAVED_PAIR_RETURN_WITHOUT_MUTUALLY_POSITIVE_SINGLETONS.md).
It also gives a comparison for **arbitrary coalition rewards** on any
partition into two pairs, and two entire singleton sign patterns where
all higher rewards are unrestricted. The common factor in the main theorem
ties the higher rewards to the singleton matrix.

## Reductions available at a counterexample

It suffices to prove the assertion on generic Gamma with fixed ell and u.
The map to raw rewards is continuous. Absence of UE is open in the
entrywise reward norm by the terminal Nash characterization. Throughout
we may suppose that every off-diagonal comparison, determinant of every
principal block of order at least two and every cofactor of the full
matrix is nonzero. Each excluded polynomial is nonzero on the hollow
matrix space, as is also seen from the permutation expansion.

At a counterexample Gamma is R0 with minimum-map degree one, has positive
determinant and is standard Q. In particular, for every y strictly positive
there is x>=0 such that Gamma x>=y and x_i>0 implies (Gamma x)_i=y_i.
Each row has a positive supplier. Every column has a negative entry by R0.
Every row has a negative entry as well: the checked full-normal-core
condition and its blocker lemma give a distinct j with Gamma_ij<=0.
The exact sources are given in the
[global singleton reduction](FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md)
and in `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`
and `exists_core_blocker_of_mem_normalCore` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`.

A useful exact stationary test for the additive game takes a nonzero
vector of hazards q in the unit cube. With b=Gamma q, require b_i>=0 if
q_i=0, b_i=0 if 0<q_i<1 and b_i<=0 if q_i=1. In the applications here
at least two hazards are positive. Every player faces a positive-hazard
opponent, and absorbs against that opponent even under a Never deviation.
In native coordinates a Quit offer is -u b_i and Always Continue has
stationary value b_i/(1-H_i), with H_i the opponents' one-date survival.
The sign rules therefore give the Bellman optimum under every unilateral
stopping law. Geometric opponent survival restores ell and gives the
finite-horizon uniform target. In particular any sure coalition of at
least two works when all its members have nonpositive row sum on the
coalition and all outsiders have nonnegative row sum there.

## A matching of two pairs

Here allow completely arbitrary real rewards r and put s_i=r_i({i}),
Z_i(T)=r_i(T)-s_i on nonempty T. Fix a partition into two pairs. Denote
i's mate by j and the opposite pair by O. Write Gamma_ij=Z_i({j}),
Pi_i=Z_i({i,j}), c_i=Pi_i-Gamma_ij. The following finite condition
suffices for original UE. For each i there is lambda_i>=-1 with

    c_i>=0,    c_i>=lambda_i Gamma_ij,
    Z_i(T union {i})<=-lambda_i Z_i(T)  for every nonempty T in O.    (1)

Here and below “T in O” means a subset of O. For lambda_i=0 this gives
the earlier two-pair join-cap condition. For proportional additive rewards
take lambda_i=u when both pairs are mutually negative. In fact this last
substitution permits a different positive factor in each recipient row.

To prove (1) first assume every c_i>0. Under the contrary no-UE source
the [two-pair complementary-odds construction, sections 2 and 3](TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md)
produces nonzero odds X>=0 and residuals e>=0, with X_i e_i=0 and at
least two strictly positive hazards q_i=X_i/(1+X_i). Its compactness and
local/global degree argument use only c_i>0 and the singleton matrix
source. The opposite-pair join caps first enter after its equation (11).
In native coordinates its two templates for i are U=Pi_i q_j and W=c_i X_j.
At the phase of O, let H be the opponent survival and P the expected
native passive absorbing reward contribution (zero on no exit). Let Q
be the forced Quit offer. With D=1/H the root identity is

    P+HU=W+e_i/D,       Q<=-lambda_i P.

The second inequality is (1) averaged over the four possible subsets,
using zero native Quit offer on an empty subset. For lambda_i>=0 this gives
Q<=lambda_i(HU-W)<=W. Indeed W>=0 and
(1+lambda_i)c_i>=lambda_i Pi_i by (1). For Pi_i>=0 use
H Pi_i q_j<=Pi_i X_j, and for Pi_i<0 use HU<=0. This proves the
required opposite-phase cap. The scheduled-phase Quit and Continue
identities are exactly the cited equation (10). For an inactive i the
two actual Continue values exceed their templates by the nonnegative
corrections in equation (12). Its two cap inequalities therefore still
hold when lambda_i>=0. For -1<=lambda_i<0 set eta=-lambda_i, so
0<eta<=1 and Q<=eta P. In the passive phase the actual player always
Continues, giving W_actual=P+H U_actual. Thus

    W_actual-Q >= (1-eta) W_actual + eta H U_actual.

Actual values are at least their templates for both active and inactive
owners. If Pi_i>=0 the right side is nonnegative. If Pi_i<0 then
H U_actual>=Pi_i X_j and the right side is at least
[(1-eta)c_i+eta Pi_i]X_j=(c_i+eta Gamma_ij)X_j>=0 by (1).
This completes the passive cap also for this sign. The two true positive hazards give geometric opponent absorption
for every unilateral replacement. The cited construction gives exact
terminal Nash on this branch and the original fixed uniform payoff.
To cover c_i=0 increase only the four scheduled-pair participant
rewards by an arbitrarily small positive amount. This improves both
c inequalities, leaves the opposite comparisons in (1) intact, and
gives the result by reward closure.

## Which singleton signs still need a proof

Write a pair as mutually positive or negative if both strict comparisons
have that sign. If there is no mutually positive pair use the
[complete interleaved sign class](INTERLEAVED_PAIR_RETURN_WITHOUT_MUTUALLY_POSITIVE_SINGLETONS.md).
If there is no mutually negative pair use the
[no-negative-pair theorem](NO_MUTUALLY_NEGATIVE_SINGLETON_PAIR_UNIFORM_EQUILIBRIUM.md).
Remove also the row and column exclusions above, a sign-forced sure
coalition, a [negative-chord Hamiltonian cycle](NEGATIVE_CHORD_HAMILTONIAN_UNIFORM_EQUILIBRIUM.md),
and the negative matching just proved.

For reproducibility the following finite census gives every surviving
case. Encode a strict sign word by its twelve entries in row-major order
omitting the diagonal, with negative smaller than positive. Choose the
lexicographically least of its 24 relabelings. Then record for each row
i the integer mask that has bit j set when Gamma_ij>0. Each line of the
table below is in this convention.

| Remaining masks | Order used below | Proof |
| --- | --- | --- |
| (8,8,2,5), (8,8,2,6), (8,8,3,6), (8,12,1,5), (8,12,1,6) | 0,1,2,3 | Named column S |
| (8,4,10,2), (8,4,10,3), (8,4,10,6) | 2,0,1,3 | Named column A |
| (8,12,3,4), (8,12,3,5), (8,12,3,6) | 0,1,2,3 | Named column B |
| (8,4,2,6), (8,4,9,3) | 0,1,2,3 | Two direct singleton exclusions |

Here is exhaustive pseudocode. All comparisons are on finite sign words.
The loop has 4096 labeled inputs and 218 distinct canonical words.

    for each word in {-1,+1}^12:
      list its 24 simultaneous row and column permutations
      keep the word only if it is the lexicographic minimum
      form the positive and negative reciprocal pair sets
      discard if either set is empty
      discard if any row lacks either sign or any column lacks a negative
      discard if some subset S of size at least 2 has:
        all off-diagonal entries in its principal block negative and
        every outside row positive in every column of S
      discard if some order p0,p1,p2,p3 around a cycle has:
        positive forward and negative backward comparisons at every edge,
        a mutually negative p0,p2 pair and a positive comparison on p1,p3
      discard if the negative pair set contains two disjoint pairs
      return the four row masks

As checks, among the canonical words with respectively 1,2,3,4,5,6
mutually positive pairs there are 72,60,32,9,2,1 before these discards
and 9,4,0,0,0,0 after them. The remaining 42 words have no positive pair.

## The two direct singleton exclusions

For (8,4,2,6) the positive targets in rows 0,1,2 force suppliers 3,2,1
to be active. Hold y1,y2,y3 positive and send y0 to infinity. Support
123 alone is bounded because its principal block is invertible. A full
solution then requires (Gamma^(-1))00>=0 in the limit. But both terms of
the hollow 123 determinant are negative, while det Gamma>0. This is
impossible.

For (8,4,9,3) rows 0,1 force players 3,2 active, and row 3 also requires
some supplier among 0,1. Hold the other positive targets fixed and send
y1 to infinity. The proper support 023 omitting 1 is bounded. Its
principal determinant is strictly negative, as both cyclic products
are negative. Thus also (Gamma^(-1))11<0, ruling out full support
for large y1. Only 123 can recur. In order 1,2,3 its block has signs

    0 + -
    - 0 +
    + - 0.

Its adjugate is strictly positive and feasibility at a positive target
gives positive determinant. Put lambda=Gamma_0,123 times this inverse.
The outside inequality along the unbounded sequence forces lambda_1>=0.
The column-2 equation has signs (+)lambda_1- h lambda_3=-c and the
column-3 equation is -B lambda_1+k lambda_2=A, with h,c,B,k,A>0.
Hence lambda_2,lambda_3>0. The checked
[passive-row inverse criterion](../../UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean)
gives UE. These two contradictions used only singleton entries. They
apply for arbitrary higher rewards, first generically, then on their
entire indicated sign classes by openness.

## A common inverse column on the eleven remaining words

In the indicated ordering write the matrix as

    [ 0 ,-a,-c, A ]
    [-b, 0,-d, B ]
    [ l, n, 0,-k ]
    [-e,-f, h, 0 ].

Here a,b,A,B,k,h>0. Both c and d may be signed, with at least one
positive. The four observer entries l,n,e,f may be signed.
In case S the [named-column test, section 29](../notes/CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#29-a-named-inverse-column-for-unrestricted-higher-rewards)
gives v=Gamma^(-1)e2 strictly positive at a counterexample.

In case A one has Gamma02,Gamma20>0 and Gamma12,Gamma21<0.
At positive targets rows 1 and 2 require 3 and 0 active. Send y2 to
infinity with the other targets fixed. Every support omitting 2 is
bounded or impossible, since its nontrivial active principal is
invertible. On 023 the fixed row 0 bounds x2,x3 by its two positive
coefficients, then fixed row 3 bounds x0 since Gamma30 is nonzero.
No proper support remains. Full solutions force v>=0 in the limit,
strictly positive by genericity.

In case B one has Gamma02<0, Gamma20>0 and Gamma12,Gamma21>0.
Again raise y2. Pair 12 fails the outside row 0, pair 02 or 23 cannot
match two active positive targets, and triple 012 has negative row 0.
In 123, fixed row 1 bounds x2,x3 and the nonzero coefficient Gamma31
in fixed row 3 bounds x1. In 023, if Gamma30>0 the fixed row 3 bounds
x0,x2 and fixed row 0 bounds x3. Otherwise 023 is cyclic with strictly
positive adjugate and positive determinant whenever feasible. Let lambda
be the outside row 1 times its inverse. If this support recurs then
lambda_2>=0. Column 3 gives A lambda_0-k lambda_2=B>0 and column 0
gives l lambda_2+Gamma30 lambda_3=-b<0. Therefore the entire passive
inverse row is nonnegative and the same checked triple criterion applies.
After this exit only full support remains, yielding v strictly positive.

## The return with signed comparisons

We prove a single statement for all eleven words. Retain the preceding
matrix, finite nonzero c,d with at least one positive, and det Gamma>0
with v strictly positive. Let

    A'=A/a, B'=B/b, C=c/a, D=d/b, x(t)=A'-Ct, y(t)=B'-Dt,
    I=e B'+f A', L=h+eD+fC, tau=v2/v3.

The (3,2) adjugate entry is abL, so L>0. The inverse equations give
I=L tau>0, x(tau)=v1/v3>0, y(tau)=v0/v3>0 and
G=l y(tau)+n x(tau)=k+1/v3>k. These conclusions continue to hold
after interchanging 0 and 1 and using the corresponding new labels.

Suppose first e+f<=0. If l+n>=0, pure 01 works. If l+n<0 then G>0
permits exchanging the labels to write l>0, n=-m<0, r=l/m<1. Put
g0=-e, g1=-f, so g0+g1>=0. When -c<=a and -d<=b, pure 012 works.
When -c>a, necessarily d>0. Pure 12 works if g1+h>=0. If g1+h<0
then g1<0 and g0>=-g1, whereas
g0 y(tau)+g1 x(tau)+h tau=0 forces x(tau)/y(tau)>1. This contradicts
x(tau)/y(tau)<r. Finally if -d>b, necessarily c>0. Set
q0=1, q1=r, q2=b/(-d), q3=0. Row 0 is strictly negative, rows 1 and
2 vanish. If g1<=0, row 3 is nonnegative by g0+g1>=0 and r<1. If
g1>0, use r>x(tau)/y(tau) and b/(-d)>tau/y(tau) in the row-3
inverse-column identity. The box test gives UE in every case.

Suppose now e+f>0. The first positive zero of x or y is finite and
strictly after tau. On that interval let c_u=(1+u)/(1+2u) and set

    P=(Lt-I)/[c_u(e+f)x(t)y(t)],     p=P/(1-tP),    T=kp/(1-p).

Stop at the first (1+t)P=1, which exists since P tends from zero to
infinity. As in the [single-block return](NONMATCHING_PAIR_LIMIT_RETURN_UNIFORM_EQUILIBRIUM.md),
solo3 with aggregate hazard p followed in construction order by solo2
with aggregate pt/(1+pt) takes T e2 to pair inputs aX,bY with X=Px,
Y=Py, and to quiet payoffs 0 and hpt/(1+pt). Both solos interpolate
nonnegative endpoints for every quiet player, also when C or D is
negative. The uninterrupted 01 rows have limiting payoff 0 for player
3 by the defining equation for P, and for player 2 they give

    R=[lY+nX+c_u(l+n)XY]/[(1+X)(1+Y)].

The limiting ratio R/T at tau is G/k>1. At the other endpoint R is
bounded (it is a passive block value) while T diverges. Hence an interior
return has R=T. Write K2=c_u(l+n), K3=-c_u(e+f). For a pair row whose
outgoing pair coordinates are aX',bY', the quiet margin for either
owner is its limiting block payoff times (1+X')(1+Y') minus K_i X'Y'.
This follows from the passive limiting formula applied to the remaining
pair rows and X'=u q1,Y'=u q0. Thus every 3 cap holds since K3<0.
All 2 caps hold when K2<=0, or when lY+nX>=0: in the latter case the
limiting R is at least K2 XY/[(1+X)(1+Y)] for K2>0, and X',Y'
decrease from X,Y. If l,n are nonnegative this suffices. They cannot
both be nonpositive since G>k.

It remains to handle l>0, n=-m<0 after possible exchange, with r=l/m>1
and A'D>B'C. If this last inequality fails then x/y is nonincreasing,
and l y-m x stays positive by its value at tau. For the remaining
inequality D>0 since at least one of C,D is positive. The ratio x/y
increases up to tau, giving rB'>A' and d0=rD-C>0 (use
r>A'/B'>C/D). Apply the complete
[interleaved return](INTERLEAVED_PAIR_RETURN_WITHOUT_MUTUALLY_POSITIVE_SINGLETONS.md)
with the following changes for the signed entries.

* In a full round or before release the initial X,Y obey X/Y>C/D
  and X<=rY. Up to s=Y/(Y+D) both transformed coordinates
  X_s=(1-s)X-Cs, Y_s=(1-s)Y-Ds are nonnegative, with X_s positive
  at that endpoint. If X_s is nonincreasing, the strictly increasing
  contact numerator from the cited proof gives a unique contact.
  If X_s increases, q1(s)/q0(s) strictly increases, with q0 decreasing
  to zero. It starts below r and tends to infinity, so again the
  unique contact is continuous. Up to release the outgoing
  X'=u q1<=r u q0=rY', while Y'<=theta Y, theta=u/(1+u). Hence all
  remaining hazards have the same uniform geometric bound, including
  when C<0. After release both pair coordinates contract.
* The degree calculation uses only I,L,d0>0, G>k and e+f>0. In
  particular the zero-solo2 side starts with margin -Ip<0 and each
  pair adds the nonpositive term -(1+u)(e+f)q0q1 in the margin
  recursion. The small-p linear identities and the affine comparison
  are unchanged. The first-full-contact sign and both cases of the
  quiet-3 recurrence use the same quantities, without separate
  positivity of e and f.
* At each full contact q1=rq0. If e+fr>=0, the proved margin gives
  post-contact w3>=u(e+fr)q0>=0. If e+fr<0, the passive increment
  -(e+fr)q0 at each full contact is nonnegative. Starting at zero,
  solo2 and full-contact updates then preserve nonnegative w3.
  Thus every inserted solo2 still has nonnegative endpoints, including
  the release solo. Following release there are only pair rows, whose
  incentive comparisons have already been proved. No sign restriction
  on their prescribed payoff is needed.

This proves every hypothesis needed for the interleaved degree, all
physical-date incentive bounds and the finite truncation on this branch.
In both returns the terminal payoff target on the constructed branch
is ell+T e2. The per-period opponent-survival bound of the cited proofs
applies with a positive first pair hazard and the positive solo3 aggregate.
It controls every deadline, literal Never, and all large finite horizons.
The finite census is exhausted. Reward closure gives the theorem for the
literal matrix, including arbitrary zero comparisons.

## An exact test against the previous producers

Take any common u>0 and the matrix

    Gamma=[0,-1,-1,5; -5,0,2,-1; -2,4,0,-5; 3,-4,2,0].

The mutually positive pairs 03 and 12 and negative pairs 01,02,13 put
this table outside the previous complete no-mutually-positive class and
the no-mutually-negative criterion. The negative matching 02 and 13
is the only partition passing the old mate premium test c_i>=0 at all
four owners. Its opposite-join condition fails already at i=0, T={1},
since Z0(01)=u>0. Condition (1) here holds with lambda_i=u. The full
determinant is 60 and three inverse columns are strictly positive.
In triple order 012,013,123 the respective passive inverse rows are
(-2,0,-3/2), (-104,-5,-77)/103 and (5,-17,-13)/16. On 023 the first
row of the active inverse is (-2,-2,-1). Thus no choice of triple
provides the nonnegative active and passive inverse test.

There is no nonzero solution of the stationary box signs on this table.
A solution without a sure player could be rescaled until some hazard
first reached one, preserving the signs. For a check with a sure player,
partition the players into S sure, A proper active and Q quiet. Set q_S=1,
q_Q=0 and solve Gamma_AA q_A=-Gamma_AS 1. For |A|=1 the right hand
side never vanishes for nonempty S. For |A|=2 or 3 the active blocks
are invertible. The following counts are obtained by the indicated exact
linear systems; the empty system at |A|=0 counts as a solution.

| Number of proper mixers | 0 | 1 | 2 | 3 |
| --- | ---: | ---: | ---: | ---: |
| Partitions with S nonempty | 15 | 28 | 18 | 4 |
| Solutions with q_A strictly between 0 and 1 | 15 | 0 | 2 | 1 |
| Also (Gamma q)_S<=0 and (Gamma q)_Q>=0 | 0 | 0 | 0 | 0 |

These four columns can be reproduced by looping over the 81 words in
{sure,proper,quiet}^4, discarding empty S and applying the displayed
system. In the proportional game the constant hazard 1/(1+u) guarantees
native payoff zero against any opponent calendar, hence the same box
signs are necessary for a sure-quitter Nash head at any genuine
continuation. Any positive stationary equilibrium also requires them.
See the [full-deviation comparison](NONMATCHING_PAIR_LIMIT_RETURN_UNIFORM_EQUILIBRIUM.md#a-separating-nonmatching-proportional-family).
For this example R0 follows as well, since any nonzero homogeneous
complementary solution would give a box solution by positive rescaling.
At target y=(1,1,1,1) enumeration of the eleven principal blocks of
orders 2 through 4 gives the unique complementary solution
(82,191,289,108)/60, of full support. Each proper block is tested by
solving its active equations and checking the outside inequalities;
singletons cannot meet a positive target. The local determinant is
positive, so the R0 degree is one. Here the matching construction
therefore gives an actual period-two equilibrium. Separately, the
common-factor examples in the
[bounded-period separation](NONMATCHING_PAIR_LIMIT_RETURN_UNIFORM_EQUILIBRIUM.md#every-fixed-upper-bound-on-the-period-fails)
require periods tending to infinity as accuracy improves. A fixed
period bound cannot witness the theorem on the entire class.
