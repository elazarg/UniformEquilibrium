# Fin4 essential-APS branching: one-coordinate purification and state loss

Author: SOCIAL_WEIGHT_REVIEW

## Status

The local Fin4 purification lemma and the oriented-graph classification below
are proved ordinary mathematics. They are not Lean-checked. They do not
produce a terminal equilibrium: purification preserves existence of a viable
one-successor segment, but generally changes the current payoff vector. The
two-level rational regression proves that this state loss is real. Section 7
now gives a second exact regression: even in the greatest family of a compact
coordinatewise convex carrier, a deterministic three-owner component can
have only summable positive singleton masses, no homogeneous singleton
balance, and a nonzero common-face value which is lost on the positive Never
event.

The result narrows a direct essential-APS attack only in the greatest APS
family inside a coordinatewise convex carrier. In four players, the mere
nonconvexity of the union of multiple successor fibers is not an obstruction
to finding one proper segment. An arbitrary APS packet can still require
convexification inside a single nonconvex successor fiber. Even after passing
to the convex greatest family, the remaining obstruction is state-compatible
iteration or a summable-mass/common-active-face boundary, not local viability.

## 1. Data and exact question

Let \(I\) have four elements. For each player \(i\), write

\[
s_i=r_i(\{i\}),\qquad R_i=(r_k(\{i\}))_{k\in I}.
\]

A payoff vector \(w\) is viable when \(w_k\ge s_k\) for every \(k\).
The Flesch successor relation is

\[
i\longrightarrow j
\quad\Longleftrightarrow\quad
R_{i,j}>s_j\quad\hbox{and}\quad R_{j,i}<s_i.
\tag{1.1}
\]

It is oriented: \(i\to j\) and \(j\to i\) cannot both hold.

For viable successor sets \(E_j\), the algebraic essential-APS step at owner
\(i\) uses

\[
\operatorname{co}\left(\{R_i\}\cup
\bigcup_{i\to j}E_j\right)
\cap\{v:v_i=s_i\}\cap\{v:v\ge s\}.
\tag{1.2}
\]

An executable singleton segment is stronger: it selects one successor and
one continuation,

\[
v=pR_i+(1-p)w,
\qquad 0<p<1,
\qquad w\in E_j,
\qquad i\to j,
\tag{1.3}
\]

with \(v\ge s\) and \(v_i=s_i\).

The question is whether the convexification in (1.2) creates an essentially
new local obstruction in Fin4.

## 2. The one-bad-coordinate lemma

Define the bad coordinates of the solo row of \(i\) by

\[
B_i=\{k\ne i:R_{i,k}<s_k\}.
\tag{2.1}
\]

### Proposition 2.1

If owner \(i\) has at least two distinct Flesch successors, then

\[
|B_i|\le1.
\tag{2.2}
\]

#### Proof

Every successor \(j\) satisfies \(R_{i,j}>s_j\), so no successor belongs to
\(B_i\). Besides \(i\), there are only three coordinates. Two of them are
already successors, leaving at most one possible bad coordinate. ∎

### Proposition 2.2 (positive-mass local purification)

Assume that \(i\) has at least two successors. Let

\[
\bar w=\sum_{a=1}^m\lambda_a w^a,
\qquad
\lambda_a>0,
\qquad
\sum_a\lambda_a=1,
\tag{2.3}
\]

where each \(w^a\) is viable and belongs to a successor fiber of \(i\). Let
\(0<p<1\), and suppose

\[
v=pR_i+(1-p)\bar w
\tag{2.4}
\]

is viable and satisfies \(v_i=s_i\). Then some \(a\) makes

\[
v'=pR_i+(1-p)w^a
\tag{2.5}
\]

viable and active at \(i\). Consequently the same algebraic owner step
contains a proper one-successor segment point (although \(v'\) need not equal
\(v\)).

#### Proof

Since \(R_{i,i}=s_i\), every \(w^a_i\ge s_i\), and the average in (2.4) is
exactly \(s_i\) at coordinate \(i\), every positively weighted \(w^a\) has
\(w^a_i=s_i\).

If \(B_i=\varnothing\), every \(w^a\) works. Otherwise Proposition 2.1 gives
\(B_i=\{k\}\). Choose \(a\) with

\[
w^a_k\ge \bar w_k.
\]

Then \(v'_k\ge v_k\ge s_k\). At every coordinate other than \(i,k\), both
\(R_i\) and \(w^a\) are at least the baseline; at \(i\), both equal the
baseline. Thus \(v'\) is viable and active. Equation (2.5) is the required
proper segment. ∎

### Corollary 2.3

At a Fin4 owner:

1. with no successor, a viable algebraic prefix is the viable solo endpoint;
2. with one live successor whose fiber is convex, the existing convex-join
   theorem gives an exact one-continuation representation of the same point;
3. with at least two successors, every positive-root-mass algebraic prefix
   certifies existence of a viable proper segment point in the same owner
   step.

The third clause is only set-level existence. It does not preserve the
original current payoff.

## 3. Exhaustive strongly connected graph shapes

### Proposition 3.1

A strongly connected oriented graph on three vertices is the directed
three-cycle. A strongly connected oriented graph on four vertices has one
of the following sorted outdegree lists:

\[
(1,1,1,1),\qquad (1,1,1,2),\qquad (1,1,2,2).
\tag{3.1}
\]

The first case is the directed four-cycle. In the second case exactly one
vertex branches; in the third exactly two vertices branch. Every branching
vertex has exactly two successors and hence at most one bad coordinate.

#### Proof

Strong connectivity forces every vertex to have positive indegree and
outdegree. An oriented four-vertex graph has between four and six edges. If
there are four, every outdegree is one. With five edges the total excess
over one is one. With six edges the graph is a tournament; no vertex can
have outdegree three, since it would have indegree zero, so the excess two is
split between two vertices. The three-vertex statement follows because a
strong oriented graph needs at least three edges and has at most three. ∎

Thus Fin4 multivalued essential-APS behavior is combinatorially binary and
occurs at no more than two vertices of a live strongly connected component.

## 4. Exact two-level state-loss regression

The following normalized singleton matrix has baseline \(s=0\):

\[
R_0=(0,4,1,-3),\qquad
R_1=(-1,0,1,1),
\]

\[
R_2=(-1,-1,0,1),\qquad
R_3=\left(\tfrac32,-1,-1,0\right).
\tag{4.1}
\]

Its Flesch graph has exactly the edges

\[
0\to1,\quad 0\to2,\quad 1\to2,\quad
1\to3,\quad 2\to3,\quad 3\to0.
\tag{4.2}
\]

For the local calculation, set

\[
u_2=(0,0,0,10),\qquad u_3=(4,0,0,0),
\qquad \bar u=\tfrac12(u_2+u_3)=(2,0,0,5).
\]

At owner \(1\),

\[
v_1=\tfrac12R_1+\tfrac12\bar u
=\left(\tfrac12,0,\tfrac12,3\right)
\tag{4.3}
\]

is viable and active. At owner \(0\),

\[
v_0=\tfrac12R_0+\tfrac12v_1
=\left(\tfrac14,2,\tfrac34,0\right)
\tag{4.4}
\]

is also viable and active.

Purifying (4.3) to \(u_2\) gives

\[
\tfrac12R_1+\tfrac12u_2
=\left(-\tfrac12,0,\tfrac12,\tfrac{11}{2}\right),
\]

which is not viable. Purifying it to \(u_3\) gives the viable point

\[
v'_1=\tfrac12R_1+\tfrac12u_3
=\left(\tfrac32,0,\tfrac12,\tfrac12\right),
\]

but then the preceding half-mass segment becomes

\[
\tfrac12R_0+\tfrac12v'_1
=\left(\tfrac34,2,\tfrac34,-\tfrac54\right),
\]

which is not viable.

Hence Proposition 2.2 cannot be iterated by independently purifying each
level: the choice that repairs the current owner's sole bad coordinate can
destroy viability at its predecessor's sole bad coordinate. This is an
exact state-compatibility failure, not a counting issue.

This regression does not rule out other masses or another path. Indeed its
singleton matrix has the positive homogeneous balance

\[
R_0+R_1+2R_2+2R_3=0.
\tag{4.5}
\]

Thus this particular table's randomized two-cycle occupation is already
visible to the homogeneous stationary branch. It is a guardrail for an APS
purification proof, not a counterexample to uniform equilibrium.

### 4.1 Why the greatest convex family is necessary

The branching argument does not repair convexification inside an arbitrary
nonconvex single-successor fiber. With baseline zero, take

\[
R_0=(0,1,-1,-1)
\]

and suppose owner \(0\) has only one live successor fiber containing

\[
w^2=(0,0,2,0),\qquad w^3=(0,0,0,2),
\]

but not their midpoint. At mass \(p=1/2\), the full convexified prefix
contains

\[
{1\over2}R_0+{1\over2}{w^2+w^3\over2}=(0,1/2,0,0),
\]

which is viable and active. Neither one-continuation segment is viable: the
segment to \(w^2\) is negative at coordinate \(3\), and the segment to
\(w^3\) is negative at coordinate \(2\).

Thus a capstone quantified over an arbitrary algebraic APS packet is false
even without branching. The obstruction disappears for
`quittingEssentialAPSGreatestFamily reward carrier` when every carrier fiber
is convex: `convex_quittingEssentialAPSGreatestFamily` makes each live
successor fiber convex, and
`quittingEssentialAPSPrefix_eq_segment_of_convex` gives an exact segment
representation in the one-successor case.

## 5. Exact surviving waist

The local convexification problem in Fin4 is smaller than the general APS
problem:

* positive mass plus branching has only one local viability constraint and
  always exposes a proper segment somewhere;
* a live SCC has at most two branching owners;
* nevertheless, the segment point need not be the supplied current point,
  and successive one-coordinate choices can conflict;
* zero-mass choices preserve every previously attained active face, so an
  indefinitely zero-mass branch lands in a common-active-face obstruction;
* shrinking positive masses can avoid a literal zero step while remaining
  summable, producing the familiar Zeno/ballistic boundary rather than an
  absorbing path.

Accordingly, the useful next theorem must be stated for the greatest family
inside a compact coordinatewise convex carrier. Even there, the honest target
is at least the following trichotomy:

\[
\boxed{
\begin{array}{c}
\text{a nonempty Fin4 greatest essential-APS family}\\
\text{inside a compact coordinatewise convex carrier}
\\[1mm]\Longrightarrow\\[1mm]
\text{an executable path with divergent total absorption}
\quad\text{or}\quad
\text{a homogeneous stationary certificate}
\quad\text{or}\quad
\text{a summable-mass/common-active-face state-loss certificate}.
\end{array}}
\tag{5.1}
\]

This trichotomy is a research target, not a theorem proved here.
Propositions 2.2 and 3.1 only reduce its finite state-compatibility part to at
most two branching owners in a recurrent component. The regression shows
that choices must be coordinated across the whole component; a pointwise
branch selection is invalid. Positive masses tending to zero with summable
total mass need not give an absorbing path, and nothing proved here turns
their common-active-face limit into a homogeneous stationary certificate.

The desired direct decision theorem would consume the third line or prove
that it always refines to one of the first two. Omitting it before such a
proof would conflate a zero/summable-mass APS boundary with stationarity.

## 6. Source correspondence and novelty audit

The inspected production files are:

* UniformEquilibrium/Quitting/EssentialAPS/Basic.lean;
* UniformEquilibrium/Quitting/EssentialAPS/ConvexProgress.lean;
* UniformEquilibrium/Quitting/EssentialAPS/ConvexFixedPoint.lean;
* UniformEquilibrium/Quitting/EssentialAPS/SegmentClosedExecution.lean;
* UniformEquilibrium/Quitting/EssentialAPS/Regression.lean; and
* UniformEquilibrium/Quitting/EssentialAPS/AdaptiveMeshUniformPayoff.lean.

They already distinguish the full convex-hull prefix from one-continuation
segments, prove equality for a convex continuation fiber, record zero-mass
false fixed points, and compile supplied executable terminal-free paths under
active-face progress. I found no declaration or stable note giving the
Fin4 one-bad-coordinate purification of Proposition 2.2 or the graph
classification in Proposition 3.1.

The homogeneous balance in (4.5) is consumed by the existing homogeneous
stationary branch; no novelty is claimed for that consumer. No unrestricted
behavioral equilibrium, fixed target, or direct decision of Fin4 is claimed
here.

Independent review:
[CODEX_DESCENDANT](../feedback/SOCIAL_WEIGHT_REVIEW__FIN4_ESSENTIAL_APS_BRANCHING_AND_STATE_LOSS__BY_CODEX_DESCENDANT.md).

## 7. Exact third mode in a compact convex greatest family

The third line of (5.1) is not merely an unproved possibility. It occurs in
an exact rational Fin4 example, already with no branching owner.

Let the common own-singleton baseline be

\[
s=(1,1,1,1).
\]

Specify the four singleton outcome vectors by

\[
\begin{aligned}
R_0&=(1,3,0,1)=s+(0,2,-1,0),\\
R_1&=(0,1,3,1)=s+(-1,0,2,0),\\
R_2&=(3,0,1,1)=s+(2,-1,0,0),\\
R_3&=(2,2,2,1)=s+(1,1,1,0).
\end{aligned}
\tag{7.1}
\]

For definiteness, give every nonsingleton terminal coalition the payoff
vector \(s\). The Never payoff remains the quitting-game convention \(0\).
Only (7.1) is used by the essential-APS calculation.

The Flesch graph has exactly

\[
0\longrightarrow1,\qquad
1\longrightarrow2,\qquad
2\longrightarrow0,
\tag{7.2}
\]

and no edge incident to player \(3\). Indeed, after subtracting \(s\), every
displayed edge has cross entries \(2\) and \(-1\); all entries involving
player \(3\) on the first three rows are zero, so the required strict
opposite-sign test fails.

Define the coordinatewise compact convex carrier

\[
\begin{aligned}
K_0&=\{s+(0,x,0,0):0\le x\le1/2\},\\
K_1&=\{s+(0,0,y,0):0\le y\le1/3\},\\
K_2&=\{s+(z,0,0,0):0\le z\le1/5\},\\
K_3&=\varnothing.
\end{aligned}
\tag{7.3}
\]

### Proposition 7.1

For the reward table (7.1) and carrier (7.3):

1. the greatest carrier-restricted essential-APS family is exactly \(K\);
2. it contains no terminal point;
3. every executable one-continuation path is the deterministic
   \(0\to1\to2\to0\) path described below and has finite total positive
   absorption mass;
4. there is no nonzero nonnegative homogeneous balance of the singleton
   rows, nor of their normalized effects \(R_i-s\); and
5. every nonzero path converges to the common active-face point \(s\), while
   retaining a positive Never probability. Its algebraic value differs from
   the literal terminal payoff of the same roots by exactly the
   survival-weighted residual \(S_\infty s\).

#### Proof

Take a point \(s+(0,x,0,0)\in K_0\). Put

\[
p_0={x\over2},
\qquad
y={x\over2-x}.
\tag{7.4}
\]

Then \(0\le p_0\le1/4\), \(0\le y\le1/3\), and a coordinatewise calculation
gives

\[
s+(0,x,0,0)
=p_0R_0+(1-p_0)\bigl(s+(0,0,y,0)\bigr).
\tag{7.5}
\]

The current point is viable and active at owner \(0\). Similarly,

\[
p_1={y\over2},
\qquad
z={y\over2-y},
\tag{7.6}
\]

gives

\[
s+(0,0,y,0)
=p_1R_1+(1-p_1)\bigl(s+(z,0,0,0)\bigr),
\tag{7.7}
\]

where \(0\le z\le1/5\). Finally,

\[
p_2={z\over2},
\qquad
x'={z\over2-z},
\tag{7.8}
\]

gives

\[
s+(z,0,0,0)
=p_2R_2+(1-p_2)\bigl(s+(0,x',0,0)\bigr),
\tag{7.9}
\]

with \(0\le x'\le1/9<1/2\). Therefore \(K\) is subinvariant inside itself.
It is contained in the greatest family. The greatest restricted family is
always contained in its carrier, so equality follows.

No \(R_i\) for \(i=0,1,2\) is viable: each has one coordinate below the
baseline \(s\). Although \(R_3\) is viable, its carrier fiber is empty. Hence
the greatest family has no terminal point.

There is one successor at every nonempty fiber. Its fiber is convex, so the
full prefix equals the one-continuation segment prefix. Equations
(7.5)--(7.9) are forced by coordinates: for example, the owner-\(0\)
coordinate \(1\) gives \(x=2p_0\), and coordinate \(2\) then gives
\((1-p_0)y=p_0\). Thus an executable path has no alternative successor,
mass, or continuation. At zero the same equations force \(p=0\) and the
zero continuation.

One full circuit sends

\[
x\longmapsto T(x)={x\over8-7x}.
\tag{7.10}
\]

For \(0\le x\le1/2\),

\[
0\le T(x)\le {2\over9}x.
\tag{7.11}
\]

Moreover

\[
p_0={x\over2},\qquad
p_1={1\over2}{x\over2-x}\le{x\over3},\qquad
p_2={1\over2}{x\over4-3x}\le{x\over5}.
\tag{7.12}
\]

The total mass in one circuit is therefore at most \(31x/30\), while the
successive circuit coordinates decrease geometrically by (7.11). Every
nonzero path has positive mass at every date but

\[
\sum_{n=0}^{\infty}p_n<\infty.
\tag{7.13}
\]

In particular, since every \(p_n\le1/4\), its survival product

\[
S_\infty=\prod_{n=0}^{\infty}(1-p_n)
\tag{7.14}
\]

is strictly positive.

For the homogeneous claim, suppose \(\lambda_i\ge0\) and

\[
\sum_{i=0}^3\lambda_i(R_i-s)=0.
\tag{7.15}
\]

The first three coordinates give

\[
-\lambda_1+2\lambda_2+\lambda_3=0,\qquad
2\lambda_0-\lambda_2+\lambda_3=0,\qquad
-\lambda_0+2\lambda_1+\lambda_3=0.
\tag{7.16}
\]

Thus

\[
\lambda_2=2\lambda_0+\lambda_3,\qquad
\lambda_1=4\lambda_0+3\lambda_3,
\]

and the last equation in (7.16) becomes

\[
7\lambda_0+7\lambda_3=0.
\]

Nonnegativity forces all four coefficients to vanish. For the unnormalized
rows \(R_i\), every coordinate is nonnegative and every row is nonzero, so a
nonnegative zero balance is also impossible.

Let \(v_n\) be the path value, \(i_n\) its owner, and
\(S_n=\prod_{t<n}(1-p_t)\). Iterating the exact arc equations gives, for
every \(N\),

\[
v_0=\sum_{n<N}S_np_nR_{i_n}+S_Nv_N.
\tag{7.17}
\]

The coordinate recursion makes \(v_N\to s\), and (7.14) gives
\(S_N\to S_\infty>0\). Hence

\[
v_0=\sum_{n=0}^{\infty}S_np_nR_{i_n}+S_\infty s.
\tag{7.18}
\]

The literal behavioral profile using exactly these singleton roots has
terminal-law reward moment

\[
U=\sum_{n=0}^{\infty}S_np_nR_{i_n},
\tag{7.19}
\]

because its positive Never event pays \(0\), not \(s\). Therefore

\[
\boxed{v_0-U=S_\infty s\ne0.}
\tag{7.20}
\]

This is an exact state-compatibility failure at temporal infinity. ∎

### 7.1 Unrestricted-deviation and uniform-payoff scope

The roots in this regression are literal product roots, but they are Nash
only against the artificial continuation annotations \(v_{n+1}\). They are
not Nash--Bellman roots against the actual suffix payoffs (7.19). In the
concrete completion above, every coalition containing at least two Quitters
pays \(s\), and quitting alone also pays the deviator its baseline \(1\).
Because the remaining prescribed absorption after a late date tends to zero,
the actual payoff from Continuing late tends to zero, while quitting at that
date guarantees \(1\). Thus the unrestricted terminal exploitability is
bounded away from zero along late suffixes. No terminal or uniform-equilibrium
compiler can consume this annotated APS path.

The game itself is not a counterexample: all players Quitting immediately is
an exact equilibrium, because every nonsingleton coalition pays \(s\).
Accordingly Proposition 7.1 falsifies only the proposed **APS-only**
two-output capstone. It shows that a direct decision proof needs a third
consumer which either:

1. forces the common active-face value to equal the actual Never payoff;
2. replaces the positive-survival residual by an executable continuation
   carrying that value; or
3. leaves the singleton stratum and produces a simultaneous collision/product
   equilibrium, as this completed table does.

The normalized three-cycle in (7.1) also appears in
CODEX_CEDAR__PROJECTIVE_Q_DETERMINISTIC_KILOBLOCK.md, where it tests a
different ordered residual-control construction. The compact carrier, forced
Möbius recursion (7.10), and exact Never-residual identity (7.20) are the
additional content here.

## 8. The smallest missing semantic field: collision insertion toggles

The singleton APS data do not determine whether the common face has an
absorbing exact cap root.  This is already false while keeping the complete
singleton table (7.1), the Flesch graph (7.2), and the greatest APS family
(7.3) literally unchanged.

The first completion used above gives every nonsingleton coalition the payoff
vector (s).  Against cap (s), the pure all-Quit root is exact: each player
gets (s_i), and changing to Continue leaves a three-player quitting
coalition which also pays (s_i).

There is a second completion of the same singleton table for which all
Continue is the unique exact product root against the same cap (s).  Put

\[
L=
\begin{pmatrix}
0&-2&-2&1\\
1&0&-2&-2\\
1&1&0&-2\\
-2&1&1&0
\end{pmatrix}.
\tag{8.1}
\]

For every player (i) and every nonempty opponent coalition
(A\subseteq I\setminus\{i\}), define its Continue payoff base by

\[
c_i(A)=
\begin{cases}
R_{j,i},&A=\{j\},\\
1,&|A|\ge2.
\end{cases}
\tag{8.2}
\]

Complete the reward table by

\[
\begin{aligned}
r_i(\{i\})&=1,\\
r_i(A)&=c_i(A) &&(i\notin A),\\
r_i(A\cup\{i\})&=c_i(A)+\sum_{j\in A}L_{ij}
  &&(A\ne\varnothing).
\end{aligned}
\tag{8.3}
\]

The first two lines of (8.3) preserve every singleton outcome vector (R_j):
the quitter receives (1), and each outsider (i\ne j) receives
(R_{j,i}).

### Proposition 8.1

For the completion (8.3), all Continue is the unique exact product Nash root
against cap (s).

#### Proof

Let (q_i\in[0,1]) be player (i)'s Quit probability.  Write (H_i(q))
for pure Quit minus pure Continue against the opponents' product marginals.
The empty opponent coalition contributes

\[
r_i(\{i\})-s_i=0.
\]

On a nonempty opponent coalition (A), (8.3) gives the insertion toggle

\[
r_i(A\cup\{i\})-r_i(A)=\sum_{j\in A}L_{ij}.
\]

Taking expectation and using only the opponent marginals yields the exact
linear formula

\[
H_i(q)=\sum_{j\ne i}L_{ij}q_j.
\tag{8.4}
\]

At an exact product root, deviating from the displayed marginal to pure
Continue cannot gain.  Therefore

\[
q_iH_i(q)\ge0
\qquad(i\in I).
\tag{8.5}
\]

For every unordered pair, (8.1) has

\[
L_{ij}+L_{ji}=-1.
\]

Consequently

\[
\sum_iq_iH_i(q)
=q^{\mathsf T}Lq
=-\sum_{i<j}q_iq_j.
\tag{8.6}
\]

If at least two coordinates of (q) are positive, (8.6) is strictly
negative, contradicting (8.5).  If exactly one coordinate, say (q_j), is
positive, column (j) of (L) contains a positive entry (L_{ij}=1) with
(i\ne j).  Player (i) is playing pure Continue but has

\[
H_i(q)=q_j>0,
\]

so deviating to Quit is strictly profitable.  This is again impossible.
Thus (q=0), and all Continue is the unique exact root.  At (q=0), every
endpoint difference is zero, so this root is indeed exact. ∎

### 8.1 Exact no-go and surviving compiler input

The two completions have identical singleton rewards.  Hence they have
identical:

* Flesch successor graph;
* essential-APS operator and greatest family for the fixed carrier;
* forced Möbius path and summable absorption calculation; and
* common active-face limit (s).

Nevertheless their exact cap-root sets at (s) differ maximally: one contains
the absorbing all-Quit root, while in the other all Continue is unique.
Thus no theorem using only essential-APS singleton data can decide the
summable common-face branch by asserting an absorbing collision root.

The earliest missing game-semantic datum is the pair insertion-toggle matrix

\[
r_i(\{i,j\})-r_i(\{j\}).
\tag{8.7}
\]

For a general table, the complete datum needed by an exact product-root
consumer is the full opponent-coalition endpoint polynomial

\[
A\longmapsto r_i(A\cup\{i\})-r_i(A).
\tag{8.8}
\]

The additive completion (8.3) shows that the distinction is already visible
at first collision order: (8.8) is generated by (8.7), yet it reverses the
root conclusion without changing any APS field.

There is also no missing late-suffix argument inside the singleton path.
The checked `QuittingSummableExactValueTail.suffixGain_tendsto_max_solo`
theorem says that unrestricted exploitability of a summable exact Bellman
tail converges to the positive part of the singleton self-payoff.  Here every
singleton self-payoff is (1), so the late suffix gap converges to (1), not
to zero.  A direct proof must therefore add a collision/root consumer for
(8.8), or leave the singleton stratum and use a source-attached strategic
packet.  APS compactness alone cannot supply either operation.

The relevant checked files are:

* `UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean`, for the
  endpoint-difference expansion; and
* `UniformEquilibrium/Quitting/Chronology/SummableExactTailTerminalGap.lean`,
  for the exact late-suffix exploitability limit.

The linear unique-root method has a separate checked instance in
`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyCapLimitRootUniqueness.lean`.
The new point of Proposition 8.1 is the same-singleton completion comparison:
the APS carrier and its exact third-mode path are held fixed while only the
collision semantics change.

## 9. Pair toggles still do not suffice

Proposition 8.1 shows that pair insertion toggles are the first missing
field.  They are not the last one.  Keep the completion (8.3), including all
of its singleton and pair-coalition rewards, and put

\[
S=\{0,1,2\}.
\]

Change only the following higher-coalition coordinates:

\[
r'_i(S)=2\quad(i\in S),
\qquad
r'_3(S)=1,
\qquad
r'_3(I)=0.
\tag{9.1}
\]

Leave every other reward coordinate as in (8.3).  In particular, for every
ordered pair (i\ne j),

\[
r'_i(\{i,j\})-r'_i(\{j\})
=r_i(\{i,j\})-r_i(\{j\})
=L_{ij}.
\tag{9.2}
\]

Thus the complete singleton table, Flesch graph, APS carrier, forced APS
path, common boundary, and pair insertion-toggle matrix are unchanged.

### Proposition 9.1

In the modified completion, the pure root in which exactly players
(0,1,2) Quit is an exact terminal Nash profile.

#### Proof

For (i\in S), if (i) Quits its payoff is (r'_i(S)=2).  If it changes
to Continue, the remaining two-player coalition (S\setminus\{i\}) Quits.
That coalition was not modified, and its payoff to the outsider (i) is
the base value (1).  Hence every member of (S) strictly prefers Quit.

Player (3) receives (r'_3(S)=1) by Continuing.  Joining the quitting
coalition gives (r'_3(I)=0), so player (3) strictly prefers Continue.
All four pure actions are strict best responses. ∎

The original completion (8.3) has all Continue as its unique exact product
root at cap (s); the modified completion has the additional fully absorbing
root of Proposition 9.1.  Since the two tables agree through pair insertion
order, no pair-toggle-only theorem can decide the common-face cap-root branch.
The next missing coefficients are already the two-opponent insertion toggles

\[
r_i(\{i,j,k\})-r_i(\{j,k\}).
\tag{9.3}
\]

### 9.1 What the full endpoint polynomial does and does not provide

For a fixed cap (v), the full insertion-toggle family

\[
T_i(A)=
\begin{cases}
r_i(\{i\})-v_i,&A=\varnothing,\\
r_i(A\cup\{i\})-r_i(A),&A\ne\varnothing
\end{cases}
\tag{9.4}
\]

does determine every exact product-root comparison at (v): the endpoint
difference is its product-law expectation.  Thus it can verify a fully
absorbing root, and any such root is immediately a terminal Nash profile.

For a root with positive all-Continue probability, however, (9.4) does not
determine its Bellman predecessor.  For any fixed (i) and nonempty opponent
coalition (A), adding the same constant to both

\[
r_i(A)
\quad\hbox{and}\quad
r_i(A\cup\{i\})
\tag{9.5}
\]

preserves every insertion toggle and hence every exact-root comparison, but
changes the absolute successor payoff whenever (A) has positive root mass.
This common-mode freedom is invisible to the difference polynomial.

Consequently the smallest complete static field is not merely the pair
matrix, nor merely the full difference polynomial.  It is an endpoint pair,
or equivalently:

\[
\bigl(	ext{full endpoint-difference polynomial},
      	ext{one absolute endpoint/intercept polynomial}\bigr).
\tag{9.6}
\]

That field determines both exact root Nash and the Bellman predecessor
(F_q(v)).  It still does not force an absorbing or stationary root at the
displayed common face: completion (8.3), whose absolute rewards are fully
specified, has only the all-Continue root there.  Hence a static augmentation
of the APS boundary stops at the same intrinsic alternative:

\[
\boxed{
\text{absorbing/stationary exact root at the common face}
\quad\text{or}\quad
\text{a fully typed all-Continue inert cap state}.}
\tag{9.7}
\]

The first branch is executable.  The second requires state movement: an
actual source-attached response, paid port, or another dynamically closed
carrier.  No finite list of singleton or low-order collision coefficients can
replace that missing transition.
