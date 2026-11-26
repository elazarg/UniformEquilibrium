# Actual minima with controllable late windows saturate the pivot Never bound

## Exact statement

Let I={0,...,n-1}, n>=2. A native quitting table assigns a finite real
reward Z_i(S) to every owner i and nonempty coalition S subset I, with
Z_i({i})=0. AllNever pays zero. Owners independently choose complete laws
on the natural dates and Never. Write U_i for expected terminal payoff,
B_i for the supremum over every unilateral replacement law, e_i for the
payoff of the pure Never response, N_i for the original marginal Never
probability, d_i=B_i-U_i, and nu=product_i N_i.

Fix a pivot p and r>0. Define the hollow matrices

    Gamma_ij=Z_i({j}),     J_ij=Z_i({i,j})       (i!=j).

Assume Gamma and J are invertible and

    v=Gamma^-1 e_p>0, S=sum_i v_i,
    A=I-J^-1 Gamma, b=J^-1 e_p.

Here e_p in matrix expressions is the p-th coordinate vector, not the
Never payoff. Let L be a fixed positive integer, and let T be a subset of
{0,...,L-1} such that

    R_T=[A^(L-1-k)b : k in T] has row rank n.              (1)

Let P be an ACTUAL independent complete-law profile satisfying:

1. N_i(P)>0 for every i, B_i(P)=e_i(P) for every i, and d_i(P)=0
   for every observer i!=p.
2. P minimizes J_r=d_p+r nu over all actual observer-optimal profiles,
   or over a larger feasible carrier containing all such profiles.
3. Every finite pure pivot deadline has payoff strictly less than B_p(P).
4. For arbitrarily large start dates a, every hazard q_i(a+k) is strictly
   positive for all i and all k=0,...,L-1.

Then

    N_p(P)=1/(1+rS).                                    (2)

For n=4 there is an open dense set of native reward tables on which J is
invertible and (1) holds with L=4 and T={0,1,2,3} for EVERY pivot.
Consequently, on that open dense set, for any actual minimum satisfying
item1 and item2 at a strict inverse-column pivot, at least one of the
following holds:

- a finite pivot deadline attains B_p;
- the equality (2) holds;
- there is a cutoff beyond which no four consecutive dates have all four
  hazards strictly positive at every date.

In particular this excludes the conjunction of strict mass
N_p<1/(1+rS), no finite pivot cap contact, and arbitrarily late such windows.
The theorem does not assume that conditional tails are global minima.

The same equality holds for the guarded sparse support patterns defined
below whenever their explicit constraint matrix has full row rank. In four players,
this generically includes exactly the 18 four-date pair patterns in which
the pivot is always active, all three observer labels occur, and the
repeated observer occurs at nonadjacent dates. Under strict mass and no
finite pivot cap contact, each such guarded pattern is eventually absent.
These patterns have no date of full support.

## Conjecture-facing change and strategic inputs

The live obligation is to contradict a positive selected minimum of
d_p+r nu on the observer-optimal carrier. One source case is realized by
an actual complete law; another is a nonrealized compact limit. This theorem
strictly restricts the actual case. It upgrades the upper pivot-Never bound
to equality in a specified support/contact mode, without a quadratic energy
certificate. Its raw rank hypothesis is generically available for all
pivots simultaneously, including a finite classified collection of sparse
patterns.

The required strategic input is the actual minimum in items1--2. The theorem
does not produce it from an arbitrary reward table. Items3--4 are explicit
cases in its contact and support geometry, not conclusions of a compactness
or genericity theorem. The proof produces all comparison profiles from this
one law by changing finitely many of its hazards. It assumes neither a
repair strategy nor a separately supplied improving direction.

The independent mathematical content is this necessary alternative for
actual minima. It removes the whole conjunction stated above, including raw
data where the earlier positive quadratic-energy test cannot hold. It does
not remove every actual minimum, exhibit a positive-gap game, or establish
UE for a new reward-table class. The saturation equality is endogenous and
cannot be discarded by a generic perturbation of rewards.

## Probability, information and exact recursions

Before absorption there is one public live history at each date. Private
randomization can be sampled in advance, so a unilateral behavioral response
is a mixture of deterministic quitting dates and Never. Its expected payoff
cannot exceed their supremum. Conversely every such response is legal.
Thus B prices all behavioral deviations, not only stationary or bounded
responses. No public lottery or correlated recommendation is introduced.

For a product root q in [0,1)^I, put

    H_i(q)=product_(j!=i)(1-q_j), c(q)=product_j(1-q_j),
    pi_i(S;q)=product_(j in S)q_j product_(j notin S, j!=i)(1-q_j),
    Q_i(q)=sum_(S subset I\{i}) pi_i(S;q) Z_i(S union{i}),
    P_i(q)=sum_(nonempty S subset I\{i}) pi_i(S;q) Z_i(S).

Q is the forced-Quit offer; P is the passive absorbing contribution.
With literal continuation coordinates (u,B,e,N), the exact recursions are

    e'_i=P_i+H_i e_i,
    u'_i=q_i Q_i+(1-q_i)P_i+c u_i,
    B'_i=max(Q_i,P_i+H_i B_i),
    N'_i=(1-q_i)N_i.                                  (3)

These follow by conditioning on the first root and exhaust every deadline
and Never. In particular B>=e and B>=u.

Every conditional tail of P is ALL-END: if a tail response exceeded its
Never offer, continuing to that cut and using the response would improve
the original Never payoff, since opponent head survival is positive.
Every observer's conditional prescribed law is also optimal: replacing it
after that cut would improve the original prescribed payoff by the positive
joint head-survival factor. Consequently, whenever q_i>0 for an observer,
its current forced-Quit offer equals its current END cap. Positive original
Never mass ensures q_i<1 at every date.

## A square finite constraint system

Fix one length-L window. Its continuation after the window is kept literally
unchanged. Number window dates 0,...,L-1. For arbitrary nearby hazards,
compute e_i,k and u_p,k backwards by (3), with the fixed continuation as
terminal data. Put

    G_i,k=Q_i(q_k)-e_i,k.

Choose exactly n dates C subset T whose columns in (1) are independent.
Impose the following exact constraints on the nL window hazards:

- G_i,k=0 for every observer and every window date;
- G_p,k equals its ORIGINAL value for every k outside C;
- e_i,0 equals its ORIGINAL value for every observer;
- e_p,0 equals its ORIGINAL value plus lambda.

The number of scalar equations is

    (n-1)L+(L-n)+n=nL.

The original window satisfies them at lambda=0. The pivot gaps at unused
dates are frozen at their original negative values, not replaced by zero.

Linearize at zero hazards and zero continuation values. For signed hazard
variations a_k, put f_k=sum_(m>=k)a_m, so f_L=0 and a_k=f_k-f_(k+1).
Native own-singleton zero gives

    de_i,k=(Gamma f_k)_i, dQ_i,k=(J a_k)_i.

The constraints are therefore

    Gamma f_k-J a_k=g_k e_p,
    Gamma f_0=lambda e_p, f_L=0, g_k=0 outside C.         (4)

The sign of g is minus the pivot-gap variation. Equivalently,

    f_0=lambda v, f_(k+1)=A f_k+b g_k,
    A^L v lambda+R_C g=0.                               (5)

For lambda=0, the invertibility of R_C forces g=0, then f=0 and a=0.
Thus the square constraint Jacobian has zero kernel and is invertible.
For general lambda its unique solution has f_0=lambda v.

The constraint maps are polynomial in hazards and continuation payoffs.
By the ordinary inverse function theorem, near zero data there is an exact
smooth window family through each original window, parametrized by lambda.
The fixed invertible Jacobian persists nearby, and the inverse derivatives
depend continuously on the original window and its continuation. In
particular, writing a dot for the derivative at lambda=0,

    dot e_p,0=1, dot u_p,0 ->1, dot c ->-S                (6)

as the window and continuation data tend to zero. Indeed the zero-data
first derivatives of prescribed pivot payoff and joint window survival
are (Gamma f_0)_p and -sum_i f_0,i respectively. Here c is the product of
all the window's nL survival factors.

This is a fixed finite-dimensional statement. Its neighborhood may depend
on L and C; no uniform assertion for growing windows is used.

## Feasibility against every complete deviation

The assumed strictness of every finite pivot deadline implies G_p,k<0 at
each original conditional window date. To see this, compare the whole
deadline at that date with whole Never; their difference is positive
opponent head survival times Q_p(q_k)-e_p,k. Every original window hazard
lies strictly between zero and one. Hence a sufficiently small TWO-SIDED
lambda interval retains all hazards in (0,1) and all pivot gaps negative.
Its radius may depend on the window and may tend to zero along late cuts.

Starting at the unchanged continuation, backward induction in (3) shows
that every window full cap equals its Never offer. Observer contact
equalities make their prescribed actions optimal, and their unchanged
continuation is already optimal. Thus their entrance payoff and cap equal
the old e_i,0 exactly. The pivot entrance full cap is its new e_p,0.

Splice this altered finite window into the original profile. Earlier
observer prescribed payoffs and full caps are unchanged. Deadlines before
the window retain their values, and every response entering the window is
bounded by its unchanged entrance cap. The literal head is unchanged and
the entrance prescribed payoff agrees with its old value. Therefore every
observer remains exactly optimal.
Every earlier pivot deadline is unchanged. There are finitely many such
deadlines, and all are strictly below the old global END value. Decreasing
the lambda interval if necessary keeps them below the new END value.
All responses inside and after the window are already covered by (3).
Consequently the whole altered pivot cap is still its Never offer.

This step explains why a finite earlier pivot cap contact is excluded.
Such a contact can block negative lambda even when all window contacts
have the desired strictness. No uniform separation over infinitely many
later queries is needed; their entire full cap is transported by (3).

The result is an actual independent profile. Its original Never masses
remain positive because only finitely many proper hazards changed. It is
therefore a legal competitor in the minimum problem in item2.

## Objective derivative and the actual-law limit

Let s_a be joint survival of the unchanged head before the window,
h_p,a its opponent survival, and nu_tail the joint Never probability of
the fixed continuation after the window. The source pivot cap changes by
h_p,a lambda. Its prescribed payoff changes by s_a times the entrance
payoff change. Its original joint Never mass is s_a c nu_tail. Thus the
exact derivative of the whole objective at lambda=0 is

    h_p,a-s_a dot u_p,0+r s_a nu_tail dot c.              (7)

Both signs of lambda are feasible. Minimality forces (7) to vanish.
Divide by s_a>0. The quotient h_p,a/s_a is the reciprocal of the pivot's
head survival.

For an actual law with N_i>0, its conditional finite mass after a tends to
zero: it is Pr(a<=T_i<Never)/Pr(T_i>=a). Therefore every late hazard tends
to zero, joint conditional Never tends to one, and all conditional native
prescribed and Never payoffs tend to zero. The latter follows from the
bounded-reward union bound on any finite quitting event. Pivot head
survival tends to its ORIGINAL N_p.

Take arbitrarily late qualifying windows in (7), using (6). This gives

    0=1/N_p-1-rS,

which proves (2). Each derivative was taken in one finite window; only
continuous finite-map derivatives were subsequently passed to the limit.
No escaped finite mass is relabeled Never.

## Guarded sparse support patterns

The finite constraint argument admits the following stronger form; it does
not require J invertible. Fix a word W=(S_0,...,S_(L-1)) of subsets of I.
Variables are indexed by (k,j) with j in S_k. Define F(W) by:

- n entrance rows, whose entry in row i and column (t,j) is Gamma_ij;
- a contact row (k,i) for every active observer i in S_k minus{p}.

An active-contact row (k,i) has column (t,j) entry

    J_ij 1_(t=k)-Gamma_ij 1_(t>=k).                      (11)

Assume F(W) has full row rank. Replace
item4 of the exact statement by arbitrarily late windows with EXACT support
W, at which every inactive observer has a strict inequality Q_i<e_i.
Retain items1--3, invertible Gamma, and v>0. Then (2) still follows.

Here is the complete modification of the proof. Choose a square invertible
column minor of F(W). Vary those active hazards and keep every other
hazard at its original value, including all zero hazards. Preserve active
observer contacts G_i,k=0 and all observer entrance Never offers, and
move the pivot entrance offer by lambda. The square Jacobian at zero
data is precisely the chosen minor. Its inverse produces the exact smooth
curve. Entrance rows again give
Gamma f_0=lambda e_p, so all three derivative limits in (6) are unchanged.

For a sufficiently small two-sided parameter, active hazards remain
strictly positive and below one. Inactive observer comparisons remain
strict. All finite pivot comparisons remain strict, including dates
at which the pivot is inactive. Backward induction in (3) proves ALL-END and observer
optimality at every cut of the altered window. The preceding full-head
splice, objective identity (7), and actual conditional finite-mass limit
apply verbatim. This proves (2). No inactive observer inequality is
mistaken for a contact equation, and its strict guard is not inferred from
raw matrix rank.

The original full-support theorem is a special case. Its square Jacobian
adds frozen pivot-gap rows to the rows of F, and its invertibility proves
that the rows of F are independent. More generally, if K={k:p in S_k}
and C subset K has n dates, append to F the pivot-gap rows (11) for
k in K minus C. The resulting square matrix M(W,C) has
sum_k |S_k| rows and columns. Its invertibility is a sufficient finite
certificate for full row rank of F; an arbitrary choice of C need not work.

### Exact generic classification for four-date pair patterns

Let n=L=4 and S_k={p,i_k}, with each i_k an observer. There are eight
hazard variables, four active observer contacts, and four entrance rows,
so F is square. Assume Gamma invertible and
J_ip-Gamma_ip!=0 for each observer. Generically F is invertible exactly
when all three observer labels occur and the repeated label is nonadjacent.

To prove this without enumerating numerical ranks, write a_k for a hazard
variation, f_k=sum_(t>=k)a_t, and u_k=a_(i_k),k. The observer contact at
date k is

    Gamma_i f_k-J_ip a_pk=0,   i=i_k.

Since a_k=e_p a_pk+e_i u_k, this is equivalent to

    f_k=T_i f_(k+1)+e_i u_k,
    T_i=I+e_p Gamma_i/(J_ip-Gamma_ip),   f_4=0.          (12)

Thus the four free observer variations parametrize all contact tangents.
Their entrance columns are c_k=T_i0 ... T_i(k-1) e_i(k). Each has the
form e_i(k)+z_k e_p. If any observer is absent, their projections span
at most two observer coordinates, so rank is at most3. If the repeated
label is adjacent, its two columns coincide because T_i e_i=e_i. Rank
is again at most3. In either case the square entrance/contact Jacobian is
singular.

Conversely suppose all three labels occur and label j repeats nonadjacently.
Its two columns differ by a multiple of e_p, generically nonzero. To verify
nonidentity, specialize every J_ip to a common large parameter H. In the
intervening product of T matrices, the e_p coefficient to first order in
H^-1 is the sum of Gamma_i,j over intervening labels different from j.
There is at least one such label. These off-diagonal coordinates are
independent, so this polynomial is not zero. The preceding product scales
e_p by a nonzero rational function generically; explicitly
T_i e_p=J_ip/(J_ip-Gamma_ip)e_p. Hence the column difference is nonzero
on a nonempty Zariski-open set. The other three projected directions are
the three distinct observer unit vectors. The entrance map therefore has
rank4. Since (12) parametrizes its entire contact kernel, F is invertible.

There are 18 such words: choose the repeated observer in three ways,
its two nonadjacent positions in three ways, and the order of the remaining
observers in two ways. The 18 all-three-label words with an adjacent repeat
are singular; words missing a label are also singular. This classifies
the raw four-date pair pattern test, not all sparse words or their strategic
realizability.

Each successful word has a nonzero determinant polynomial in the independent
Gamma/J entries. There are only finitely many words and pivots. Intersecting
their nonzero loci with (8), the invertible Gamma locus, and the needed
nonzero denominators gives an open dense raw set. On it, a contact-free
actual minimum with N_p!=1/(1+rS) eventually has neither a full-support
four-date window nor ANY of these 18 guarded pair patterns. The finitely
many individual cutoffs have a common maximum. No countable genericity or
growing-window uniformity is used.

## Generic four-date rank and gap-preserving perturbation

For hollow four-by-four matrices, define

    F_p(Gamma,J)=(det J)^10 det[b_p,A b_p,A^2 b_p,A^3 b_p],
    b_p=J^-1 e_p, A=I-J^-1 Gamma.

This is a polynomial in the 24 off-diagonal coordinates. If
K=(det J)I-adj(J)Gamma, column k, numbered0 through3, has numerator
K^k adj(J)e_p and denominator (det J)^(k+1). The determinant denominator
is (det J)^10. The exact example below has all four F_p nonzero. Hence

    det J !=0 and F_p!=0 for every p                       (8)

is open dense. The 24 entries are independent reward coordinates: singleton
rewards to other recipients and participant pair rewards are disjoint.
Thus (8) is open dense in the full 56-dimensional native own-zero table
space, with arbitrary passive-pair and higher-coalition rewards.

For completeness, let g(Z) be the infimum of sum_i(B_i-U_i) over all
absorbing independent profiles, where absorbing means nu=0. If two tables
differ by at most eta in reward sup norm, every prescribed payoff and every
replacement payoff differs by at most eta. Taking a supremum preserves
that bound for B. Each debt changes by at most 2eta, so

    |g(Z)-g(Z')|<=8eta.                                  (9)

The absorbing-profile set is the same for both tables. A positive absorbing
gap therefore survives sufficiently small generic perturbations satisfying
(8), as well as any other finite collection of open dense raw conditions.
After perturbation, any pivot and minimum used by the source analysis must
be selected afresh. Neither an old strategy nor an old minimum is claimed
to persist. Genericity supplies (8); it does not supply items1--4.

## Exact algebra and separation from a quadratic test

Take

    Gamma=[0,3,-1,-1; 3,0,-1,-1; -1,-1,0,3; -1,-1,3,0],
    D=diag(1/5,1/4,1/3,2/5), J=Gamma D.

Direct multiplication gives det Gamma=45, det J=3/10, and

    Gamma^-1=(1/15)[2,7,3,3; 7,2,3,3; 3,3,2,7; 3,3,7,2].

Every inverse column v is strictly positive, with S=1 and v_p=2/15.
Moreover A=I-D^-1=diag(-4,-3,-2,-3/2) and b_p=D^-1 v. The control
determinant is the product of the four b coordinates and the Vandermonde
determinant of these four distinct diagonal entries. It is exactly7/5
for every pivot, for either displayed four-column order. For p=0,
b=(2/3,28/15,3/5,1/2). This verifies (8) simultaneously for all pivots.

A different sufficient method for fixed entrance caps requires a symmetric
matrix W satisfying Wv=e_p and

    Q(W)=[W Gamma^-1 J+J^T Gamma^-T W-W]/2>0.              (10)

No such W exists here. For EVERY symmetric W with Wv=e_p,

    v^T Q(W)v=(D_pp-1/2)v_p,

which is respectively -1/25,-1/30,-1/45,-1/75. This rules out the whole
existential selection of W, independently of passive-pair or higher rewards.
More generally the same directional value equals
(Gamma^-1 Jv)_p-v_p/2. Continuity shows that the failure of (10), positive
inverse columns, and all four control ranks persist on an open neighborhood.

This is exact separation of two raw sufficient tests. It is not an example
of a positive-gap game or of a minimizing profile with items1--4. It makes
no claim that the displayed table is outside every available UE theorem.

## Actual-law recurrent guarded-word example

This example simultaneously realizes raw rank, an arbitrarily late recurrent
controlling word, all finite strict pivot comparisons, positive caps, positive
Never masses, and full observer optimality. It does not claim a minimum of
any objective or an unrestricted positive-gap game.

Take pivot 0, rho=1/3, and

    Gamma=[[0,1,1,1],[2,0,-1,-1],[2,-1,0,-1],[2,-1,-1,0]],
    J=[[0,-1,-1,-1],[6,0,0,0],[15/2,-5,0,-3],[13/2,-3,0,0]].

Then det Gamma=-6 and Gamma^-1 e_0=(1/3,1/3,1/3,1/3).
Set all remaining rewards to zero, for definiteness. Use support word
W=(01,02,03,01) and leading hazards

    a_0=(2,1,0,0), a_1=(1,0,1,0),
    a_2=(1,0,0,1), a_3=(1,1,0,0).

Let E=(6,12,21/2,21/2). The exact identities are

    Gamma sum_k a_k = (4,8,7,7) = (1-rho) E,
    det F(W) = -1728.

With terminal offer rho E=(2,4,7/2,7/2), the four leading entrance offers
(backwards through the block, displayed chronologically) are

    (6,12,21/2,21/2), (5,8,15/2,15/2),
    (4,7,11/2,13/2), (3,6,9/2,9/2).

The corresponding leading quit-minus-END gaps are

    (-7,0,-1/2,-1/2), (-6,-2,0,-1),
    (-5,-1,-1,0), (-4,0,-2,-1).

For each sufficiently small t, solve the finite block equations that preserve
its four active observer contacts and prescribe entrance offer tE and terminal
offer rho tE. At t=0 all hazards and boundary data are zero. The derivative
with respect to the eight active hazards is the invertible F(W). IFT gives
one smooth solution q(t), with

    q_k(t)=t a_k+O(t^2).

Thus all eight active hazards are positive for small t>0; every inactive
observer gap and every pivot gap is strict by the displayed linear terms.
The four internal offer vectors are positive for sufficiently small t.

Fix a sufficiently small h>0 and concatenate the actual blocks

    q(h), q(rho h), q(rho^2 h), ... .

Assigned boundary offers agree exactly between adjacent blocks. Every active
hazard is O(h rho^n) in block n, so each player's sum of hazards is finite;
all original marginal Never masses are strictly positive. The assigned offer
vectors tend to zero. Iterating the exact Never-payoff recursion through any
finite number of blocks leaves a bounded-survival factor times the assigned
terminal offer. That term tends to zero; hence the actual infinite-law Never
payoffs equal the assigned offers.

At every active observer date its immediate quit offer equals its assigned
Never offer; at every inactive observer date it is strictly smaller. Bellman
recursion or the complete deadline characterization therefore gives B_i=e_i
for all observers. Their prescribed strategies mix only between optimal
current quitting and optimal continuation; iteration with the vanishing
terminal offers gives U_i=e_i. Every pivot finite comparison is strict,
so B_p=e_p and no finite pivot deadline attains B_p. Thus the profile is
ALL-END, observer-Nash, and has positive entrance caps and positive original
Never masses. The guarded controlling word recurs in every block.

This proves the strategic recurrence hypothesis is compatible with the native
model and the other stated local source features. The global minimum property
is deliberately absent; the saturation theorem remains a necessary condition
on actual minima, not a contradiction from these source features alone.
Since N_p<1, any choice 0<r<(1/N_p-1)/S also gives the strict mass inequality.
Thus all geometric and strategic conditions in the excluded strict-mass
mode can coexist; global minimality is the missing premise in this example.

## Boundary tests and limits of the argument

Fewer than n independent control dates cannot give the square inverse in
(5). A rank claim based only on counting variables is insufficient.
When J=c Gamma for nonzero c, A is scalar and the control matrix has rank
at most1: this shows that rank is not automatic merely from v>0.

If a window hazard is zero, its cube face need not contain the two-sided
implicit curve. If a finite pivot deadline ties the cap, the negative
parameter can lose ALL-END before the window. Neither boundary can be
ignored. The theorem retains them as alternatives, rather than assigning
them artificial strict margins.

AllNever is not contradicted: it has no positive window hazards, and its
finite native pivot deadlines attain the same zero cap. Exact Nash laws
with pivot finite atoms likewise cannot satisfy item3, since an atom in
an optimal law must be supported on a cap-attaining response.

The equality (2) is a necessary condition, not a contradiction. Sparse
supports, finite cap contacts, and nonrealized compact minima remain open.
No calendar-density percentage is an intrinsic measure of reward-table
coverage. No uniform estimate for windows of increasing length is proved.

## Source correspondence and residual consumer

The actual-law objects are `quittingStoppingLawExpectedPayoff` and
`quittingStoppingLawReplacementPayoffCap` in
[StoppingLawOperationalDistance.lean](../../UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean).
The declarations
`quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`
and
`quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
identify them with payoff and unrestricted cap for arbitrary behavior.
Conversely `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`
and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
give those identities for the independent conditional-hazard implementation.

The literal prefix identity is
`quittingTerminalSemanticPair_rootThenContinuation` in
[TerminalSemanticPair.lean](../../UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean).
The full-cap recursion is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
[TerminalDebtPrefix.lean](../../UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean).
These existing declarations supply the operational meanings of (3).
The new mathematical steps are the square chart allowing entrance pivot
cap motion, its two-sided finite splice, and the resulting mass equality.

The established declaration
`not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
in [PositiveMinimumSemanticDebt.lean](../../UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean)
concerns positive minimum total debt on a compact semantic carrier. It
does not assert actual attainment, the observer-constrained J_r minimum,
or the support/contact hypotheses here. None is inferred from that theorem.

The residual consumer is exact: once an actual selected minimum satisfies
items1--2 and a strict inverse-column pivot is fixed, compute (8). If a
finite pivot cap attainer is absent and the strict mass inequality holds,
the support condition in item4 is impossible. Equivalently the generic
actual source must obey the three-way alternative in the exact statement.
The same argument also gives an eventual cutoff for the finite collection
of 18 guarded pair patterns. Their strict inactive-observer guards are
conditions on the observed word, not additional raw genericity conclusions.
If a source reduction also has a nonrealized arm, that arm is unchanged.
This is a conditional reduction of an actual source mode, not a complete
source-to-UE construction.

## Lean handoff

Use the existing complete stopping-law and literal root-prefix definitions.
Introduce a finite polynomial map for the observer contacts, the frozen
pivot gaps, and the entrance Never coordinates. Prove its zero-data
Jacobian invertible from (5), then apply a finite-dimensional inverse
function theorem. State the local chart with its derivative dependence
on the terminal values; do not assume a desired improving curve as a field.
For sparse supports, use the active-contact and entrance map F and select
an invertible column minor, leaving other hazards fixed. Prove the finite
pair-pattern classification through the explicit recurrence (12).

Prove the finite full-cap splice using (3) and the finitely many strict
earlier pivot gaps. Differentiate its explicit objective, then use the
actual conditional finite-mass limit to obtain (2). Separate the generic
four-by-four polynomial calculation and the reward-gap bound (9) from
the strategic theorem. No theorem should manufacture full-support windows
or actual realization from the rank condition.

This packet is ordinary mathematics awaiting formalization. It claims no
new Lean check, no equilibrium existence theorem, and no solution of Fin4.
