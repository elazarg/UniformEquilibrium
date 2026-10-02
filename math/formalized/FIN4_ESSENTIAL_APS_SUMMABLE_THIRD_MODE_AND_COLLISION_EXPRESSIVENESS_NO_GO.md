# Fin4 essential-APS summable third mode and collision expressiveness no-go

Authors: SOCIAL_WEIGHT_REVIEW

Independent reviews:
[PAIRED_HULL_REVIEW](../feedback/SOCIAL_WEIGHT_REVIEW__FIN4_ESSENTIAL_APS_BRANCHING_AND_STATE_LOSS__SECTIONS_7_8__BY_PAIRED_HULL_REVIEW.md),
[CODEX_DESCENDANT](../feedback/SOCIAL_WEIGHT_REVIEW__FIN4_ESSENTIAL_APS_BRANCHING_AND_STATE_LOSS__BY_CODEX_DESCENDANT.md)

## Exact statement

Let \(I=\{0,1,2,3\}\), let the common own-singleton baseline be

\[
s=(1,1,1,1),
\]

and let the four singleton terminal payoff vectors be

\[
\begin{aligned}
R_0&=(1,3,0,1)=s+(0,2,-1,0),\\
R_1&=(0,1,3,1)=s+(-1,0,2,0),\\
R_2&=(3,0,1,1)=s+(2,-1,0,0),\\
R_3&=(2,2,2,1)=s+(1,1,1,0).
\end{aligned}
\tag{1}
\]

For singleton data, define the strict Flesch successor relation by

\[
i\longrightarrow j
\quad\Longleftrightarrow\quad
R_{i,j}>s_j\ \hbox{ and }\ R_{j,i}<s_i.
\tag{2}
\]

A payoff \(v\in\mathbb R^I\) is viable when \(v\ge s\) coordinatewise.  For
an owner-indexed family \(E=(E_i)_{i\in I}\), its essential-APS owner step at
\(i\) consists of:

1. the viable singleton endpoint \(R_i\), when it is viable; and
2. the viable points on the active face \(v_i=s_i\) in

   \[
   \operatorname{co}\left(\{R_i\}\cup
     \bigcup_{i\to j}E_j\right).
   \tag{3}
   \]

For a supplied carrier \(K=(K_i)\), the carrier-restricted greatest
essential-APS family is the greatest family \(E\subseteq K\) contained in its
owner step.  A one-continuation segment is an equality

\[
v=pR_i+(1-p)w,
\qquad 0\le p<1,
\qquad w\in E_j,
\qquad i\to j.
\tag{4}
\]

Define the compact coordinatewise convex carrier

\[
\begin{aligned}
K_0&=\{s+(0,x,0,0):0\le x\le1/2\},\\
K_1&=\{s+(0,0,y,0):0\le y\le1/3\},\\
K_2&=\{s+(z,0,0,0):0\le z\le1/5\},\\
K_3&=\varnothing.
\end{aligned}
\tag{5}
\]

### Theorem A: an exact summable third mode

For (1) and (5):

1. the Flesch graph is exactly

   \[
   0\to1,\qquad1\to2,\qquad2\to0,
   \tag{6}
   \]

   with no edge incident to player \(3\);
2. the carrier-restricted greatest essential-APS family is exactly \(K\);
3. it contains no terminal point;
4. from every nonzero point, every one-continuation execution is forced,
   uses a positive singleton mass at every step, but has finite total mass;
5. there is no nonzero nonnegative homogeneous balance of either the raw
   rows \(R_i\) or the normalized effects \(R_i-s\); and
6. every nonzero execution converges to \(s\), retains a positive Never
   probability, and its annotated value differs from the literal terminal
   payoff by exactly the survival-weighted residual \(S_\infty s\ne0\).

Thus a compact convex greatest essential-APS family need not yield either a
terminal point, divergent executable absorption, or a nonzero homogeneous
singleton balance.  A summable positive-survival common-face branch is an
exact third mode.

### Theorem B: identical APS data have opposite cap-root behavior

There are two complete four-player quitting reward tables with the same
singleton vectors (1), hence the same Flesch graph, carrier-restricted
greatest APS family, forced execution, and common face \(s\), but different
exact product-root sets against cap \(s\).

In Completion A, every nonsingleton terminal coalition pays \(s\).  The pure
all-Quit root is exact against cap \(s\), and all players Quitting at date zero
is an exact behavioral equilibrium.

In Completion B, put

\[
L=
\begin{pmatrix}
0&-2&-2&1\\
1&0&-2&-2\\
1&1&0&-2\\
-2&1&1&0
\end{pmatrix}.
\tag{7}
\]

For every player \(i\) and nonempty opponent coalition
\(A\subseteq I\setminus\{i\}\), let

\[
c_i(A)=
\begin{cases}
R_{j,i},&A=\{j\},\\
1,&|A|\ge2,
\end{cases}
\tag{8}
\]

and define the complete reward table by

\[
\begin{aligned}
r_i(\{i\})&=1,\\
r_i(A)&=c_i(A) &&(i\notin A),\\
r_i(A\cup\{i\})&=c_i(A)+\sum_{j\in A}L_{ij}
  &&(A\ne\varnothing).
\end{aligned}
\tag{9}
\]

Then all Continue is the unique exact product Nash root against cap \(s\).
Nevertheless the same forced singleton APS execution remains an exact
Bellman value path with finite total absorption.  Its literal late-suffix
payoffs tend to zero, while unrestricted exploitability tends to \(1\).

Therefore singleton essential-APS data alone cannot decide the common-face
branch by asserting an absorbing collision root.  The first missing semantic
field is already the pair insertion-toggle table

\[
r_i(\{i,j\})-r_i(\{j\}),
\tag{10}
\]

and in general exact product-root comparisons require the full
opponent-coalition insertion polynomial.

## Conjecture-facing change

This packet removes a purportedly exhaustive direct route to Fin4 uniform
equilibrium:

\[
\text{terminal essential-APS point}
\quad\text{or}\quad
\text{nonzero homogeneous singleton balance}.
\tag{11}
\]

Theorem A gives an exact rational counterexample to (11), even for the
greatest family inside a compact coordinatewise convex carrier and with a
unique live successor at every nonempty fiber.  Theorem B proves that the
third mode cannot be consumed from singleton APS data alone: identical APS
objects can sit over an absorbing cap root or a unique all-Continue cap root.

The direct Fin4 question is not solved.  The surviving direct obligation is
to augment the common-face state by collision/root semantics and then produce
an executable absorbing or stationary object, or to leave the singleton
stratum through an actual source-attached strategic transition.

## Definitions and assumptions

A quitting game has one action, Quit or Continue, for every player at every
reached date.  At the first date with a nonempty quitting coalition \(S\),
the terminal reward is \(r(S)\in\mathbb R^I\).  If nobody ever Quits, the
terminal payoff is \(0\).

A product root is a vector of independent Bernoulli Quit marginals.  It is an
exact root Nash profile against cap \(v\) when no player gains by replacing
its current marginal by pure Quit or pure Continue, where the all-Continue
outcome pays \(v\).  Since a player's payoff is affine in its own marginal,
these two endpoint comparisons cover every one-stage mixed replacement.

The exact behavioral-equilibrium claim for Completion A covers an arbitrary
unilateral behavioral replacement.  The other three players still Quit at
date zero, so no later action, private randomization, or stopping rule of the
deviator can affect the outcome beyond its date-zero Quit/Continue choice.

The late-suffix exploitability statement permits every behavioral deviation,
including Never and arbitrarily late pure stopping times.  It is not a claim
that the displayed singleton APS roots are Nash against their annotations.
They are used only as an exact Bellman value path.

## Source correspondence

The singleton APS definitions correspond to:

* `quittingEssentialAPSPrefix`,
  and `quittingEssentialAPSOperator` in
  `UniformEquilibrium/Quitting/EssentialAPS/Basic.lean`;
* `quittingEssentialAPSGreatestFamily` in
  `UniformEquilibrium/Quitting/EssentialAPS/FixedPoint.lean`;
* `convex_quittingEssentialAPSGreatestFamily` and
  `quittingEssentialAPSPrefix_eq_segment_of_convex` in
  `UniformEquilibrium/Quitting/EssentialAPS/ConvexFixedPoint.lean` and
  `UniformEquilibrium/Quitting/EssentialAPS/ConvexProgress.lean`,
  respectively; and
* `IsQuittingEssentialAPSInfiniteRun` in
  `UniformEquilibrium/Quitting/EssentialAPS/InfiniteRun.lean`.

The exact phantom-boundary identity is already checked as
`quittingValuePath_eq_terminalValue_add_survivalLimit_mul` in
`UniformEquilibrium/Quitting/Cycles/PhantomBoundaryRestart.lean`.  The
unrestricted late-suffix conclusion is checked as
`QuittingSummableExactValueTail.suffixGain_tendsto_max_solo` in
`UniformEquilibrium/Quitting/Chronology/SummableExactTailTerminalGap.lean`.

The product-root expansion used in Theorem B is
`quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle` in
`UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean`.  A different
concrete additive table with a checked unique-all-Continue root appears in
`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyCapLimitRootUniqueness.lean`.

The new mathematics is the exact carrier (5), forced Möbius recurrence,
simultaneous exclusion of terminal and homogeneous outputs, and the
same-singleton two-completion comparison.  No literature theorem is invoked.

## Proof

### 1. Flesch graph and carrier invariance

Subtracting \(s\) from the four rows in (1) gives

\[
(0,2,-1,0),\quad(-1,0,2,0),\quad
(2,-1,0,0),\quad(1,1,1,0).
\]

The strict opposite-sign test (2) gives exactly (6).  Entries involving
player \(3\) in the first three rows are zero, so no strict edge touches
player \(3\).

For \(s+(0,x,0,0)\in K_0\), set

\[
p_0={x\over2},
\qquad
y={x\over2-x}.
\tag{12}
\]

Then \(0\le p_0\le1/4\), \(0\le y\le1/3\), and

\[
s+(0,x,0,0)
=p_0R_0+(1-p_0)\bigl(s+(0,0,y,0)\bigr).
\tag{13}
\]

Similarly, put

\[
p_1={y\over2},
\qquad
z={y\over2-y},
\tag{14}
\]

and

\[
p_2={z\over2},
\qquad
x'={z\over2-z}.
\tag{15}
\]

Direct substitution gives

\[
s+(0,0,y,0)
=p_1R_1+(1-p_1)\bigl(s+(z,0,0,0)\bigr),
\tag{16}
\]

\[
s+(z,0,0,0)
=p_2R_2+(1-p_2)\bigl(s+(0,x',0,0)\bigr),
\tag{17}
\]

with \(0\le z\le1/5\) and \(0\le x'\le1/9<1/2\).  Hence \(K\) is
subinvariant.  It is contained in the greatest carrier-restricted family;
that greatest family is contained in its supplied carrier, so it equals
\(K\).

Each of \(R_0,R_1,R_2\) violates viability in one coordinate.  The row
\(R_3\) is viable, but \(K_3=\varnothing\).  Thus there is no terminal point.

### 2. Forced recurrence and finite charge

There is exactly one live successor at each nonempty fiber, and that fiber is
convex.  Hence every full APS prefix has a one-continuation representation.
The displayed representation is forced by coordinates.  For example, the
owner-\(0\) successor coordinate gives \(x=2p_0\), and the sole negative
coordinate gives \((1-p_0)y=p_0\).  The other two owners are identical after
cyclic relabeling.

One full circuit sends

\[
x\longmapsto T(x)={x\over8-7x}.
\tag{18}
\]

For \(0\le x\le1/2\),

\[
0\le T(x)\le{2\over9}x.
\tag{19}
\]

The three masses in that circuit satisfy

\[
p_0={x\over2},
\qquad
p_1={1\over2}{x\over2-x}\le{x\over3},
\qquad
p_2={1\over2}{x\over4-3x}\le{x\over5}.
\tag{20}
\]

Thus one circuit uses mass at most \(31x/30\), and successive circuit
coordinates contract by at least \(2/9\).  Every mass stays positive from a
positive start, but

\[
\sum_{n=0}^{\infty}p_n<\infty.
\tag{21}
\]

Every \(p_n\le1/4\), so the standard infinite-product estimate gives

\[
S_\infty:=\prod_{n=0}^{\infty}(1-p_n)>0.
\tag{22}
\]

At the boundary \(x=0\), the same coordinate equations force the zero-mass
self-continuation.  This is the exact false-progress endpoint of the family.

### 3. No homogeneous certificate

Suppose \(\lambda_i\ge0\) and

\[
\sum_i\lambda_i(R_i-s)=0.
\]

The first three coordinates give

\[
-\lambda_1+2\lambda_2+\lambda_3=0,
\quad
2\lambda_0-\lambda_2+\lambda_3=0,
\quad
-\lambda_0+2\lambda_1+\lambda_3=0.
\tag{23}
\]

Therefore

\[
\lambda_2=2\lambda_0+\lambda_3,
\qquad
\lambda_1=4\lambda_0+3\lambda_3,
\]

and the last equation in (23) becomes

\[
7\lambda_0+7\lambda_3=0.
\]

Nonnegativity forces every coefficient to vanish.  For the raw rows \(R_i\),
every fourth coordinate is \(1\), so a nonnegative zero balance is immediately
trivial.

### 4. Exact Never residual

Let \(v_n\) be the forced APS value, \(i_n\) its owner, and

\[
S_n=\prod_{t<n}(1-p_t).
\]

Iterating the exact arc equations gives, for every \(N\),

\[
v_0=\sum_{n<N}S_np_nR_{i_n}+S_Nv_N.
\tag{24}
\]

The recurrence gives \(v_N\to s\), while \(S_N\to S_\infty>0\).  Therefore

\[
v_0=\sum_{n=0}^{\infty}S_np_nR_{i_n}+S_\infty s.
\tag{25}
\]

The literal root sequence has only the displayed singleton absorptions.  Its
terminal reward moment is

\[
U=\sum_{n=0}^{\infty}S_np_nR_{i_n},
\tag{26}
\]

because Never pays zero.  Hence

\[
v_0-U=S_\infty s\ne0.
\tag{27}
\]

This is an exact infinite-boundary mismatch, not an error in any finite
Bellman identity.

### 5. Completion A

Set \(r(S)=s\) for every nonsingleton coalition \(S\).  If all four players
Quit at date zero, each receives \(1\).  After an arbitrary unilateral
behavioral replacement, the other three still Quit at date zero.  Whether the
deviator Quits or Continues there, the terminal coalition has size at least
three and pays that deviator \(1\).  Thus the profile is an exact behavioral
equilibrium.

### 6. Completion B and root uniqueness

Definition (9) preserves every singleton vector: the singleton quitter gets
\(1\), while outsider \(i\ne j\) gets \(R_{j,i}\).

Let \(q_i\in[0,1]\) be player \(i\)'s Quit probability in a product root, and
let \(H_i(q)\) be pure Quit minus pure Continue against the opponents.  The
empty opponent coalition contributes \(r_i(\{i\})-s_i=0\).  Conditional on a
nonempty opponent coalition \(A\), (9) gives

\[
r_i(A\cup\{i\})-r_i(A)=\sum_{j\in A}L_{ij}.
\]

Taking the product-law expectation yields

\[
H_i(q)=\sum_{j\ne i}L_{ij}q_j.
\tag{28}
\]

At an exact root, changing to pure Continue cannot gain, so

\[
q_iH_i(q)\ge0
\qquad(i\in I).
\tag{29}
\]

Every unordered off-diagonal pair of (7) sums to \(-1\).  Therefore

\[
\sum_iq_iH_i(q)
=q^{\mathsf T}Lq
=-\sum_{i<j}q_iq_j.
\tag{30}
\]

If at least two coordinates of \(q\) are positive, (30) contradicts (29).
If exactly \(q_j>0\), column \(j\) of \(L\) has an off-diagonal positive entry
\(L_{ij}=1\).  The pure-Continue player \(i\) then has

\[
H_i(q)=q_j>0
\]

and strictly gains by Quit.  Thus \(q=0\).  At \(q=0\), every endpoint
difference is zero, so all Continue is exact and unique.

The forced APS roots contain at most one possible quitter, so their Bellman
payoffs use only the singleton rows.  They remain the same exact Bellman path
under Completion B.  Equations (21) and (27), together with the unrestricted
summable-tail theorem named above, give terminal suffix payoff tending to zero
and unrestricted gain tending to

\[
\max_i\max\{0,r_i(\{i\})\}=1.
\]

## Boundary tests

1. At \(x=0\), every selected mass is zero and the common face \(s\) is a
   literal false APS fixed point.
2. At \(x=1/2\), all denominators in (12)--(20) are positive and the stated
   carrier bounds hold; no endpoint of a carrier interval is omitted.
3. From every \(x>0\), every mass is positive but their total is finite.  This
   separates positive-at-every-date from divergent absorption.
4. The raw and normalized homogeneous systems are both checked; excluding
   only one would not prove the claimed route no-go.
5. Completion A gives an exact unrestricted behavioral equilibrium and is not
   a counterexample game.
6. Completion B has unique all Continue only at the displayed cap.  No claim
   is made about roots at other caps or about nonexistence of a uniform payoff.
7. Completion B's APS roots are exact Bellman rows but are not asserted to be
   Nash rows.  Late unrestricted exploitability is positive rather than
   silently discarded at Never.

## Adapter and consumer

This is an exact impossibility theorem for an APS-only direct route, so its
adapter is the explicit rational reward/carrier construction (1), (5), (8),
and (9).  The calculations above verify every field of the relevant
carrier-restricted greatest APS object.

Its consumer is negative and exact: any proposed theorem which derives either
a terminal APS point, divergent executable singleton absorption, a nonzero
homogeneous singleton balance, or an absorbing common-face root from only the
displayed compact-convex greatest-family APS data is false.  A repaired direct
route must expose collision insertion toggles or the full endpoint polynomial.

There is deliberately no arbitrary-game positive producer in this packet.
The packet does not feed the paid-port consumer, produce terminal approximate
Nash profiles for Completion B, or decide the Fin4 conjecture.

## Lean handoff

A narrow formalization can use `Fin 4` and split into three files.

1. Define the singleton table and four interval fibers.  Prove the exact
   Flesch graph, carrier subinvariance by (12)--(17), greatest-family equality,
   terminal-freeness, and forced recurrence (18).
2. Prove the geometric mass bound, positive survival, both homogeneous
   exclusions, and instantiate
   `quittingValuePath_eq_terminalValue_add_survivalLimit_mul`.  Instantiate
   `QuittingSummableExactValueTail.suffixGain_tendsto_max_solo` for the
   unrestricted suffix statement.
3. Define the two completions.  Completion A is a direct behavioral-profile
   calculation.  For Completion B, prove (28) from
   `quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle`, then prove
   (30) and root uniqueness.

Useful finite tests are the six unordered identities
\(L_{ij}+L_{ji}=-1\), the presence of a positive entry in every column, the
three interval endpoint inequalities, and exact evaluation of \(T(1/2)=1/9\).
No desired conclusion should be added as a structure field.

## Scope and nonclaims

This packet proves an expressiveness boundary, not Fin4 uniform-equilibrium
existence or nonexistence.  In particular, it does not claim:

* that either complete game is a counterexample;
* that the Completion B APS path is Nash--Bellman or terminally approximate
  Nash;
* that every greatest APS family contains this third mode;
* that pair insertion toggles alone suffice to consume the third mode;
* that a non-all-Continue root exists at any cap in Completion B;
* that the common-face residual has an actual source chronology; or
* that collision/root data have already been connected to a stationary,
  terminal, or paid-port consumer.

The exact conclusion is only that the summable common-face mode is real and
cannot be decided from singleton essential-APS data.
