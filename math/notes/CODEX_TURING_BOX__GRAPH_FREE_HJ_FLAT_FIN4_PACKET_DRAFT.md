# Graph-free H/J and proper-flat uniform equilibrium for four players

This is an ordinary mathematical finite-reward class theorem. Its raw
adapter is not implemented in Lean. The named checked declarations supply
the actual semantic carrier, unrestricted-deviation calculus and uniform
consumer; the finite escape and raw-class argument below are ordinary math.

## 1. Exact statement and strategic scope

Let I have exactly four players. For each nonempty S subset I choose an
arbitrary finite real reward vector r(S). At the first quitting date, the
nonempty set S of simultaneous quitters fixes the absorbing reward r(S).
Live play and perpetual nontermination pay0. Strategies use independent
private randomization; a deviation replaces ONE player's ENTIRE behavioral
law, including every finite stopping date, literal Never and private mixture.
No public randomization, correlation device or restricted controller is used.

Put s_i=r_i({i})>=0. Suppose there are weights a_i>=0, not all0, such that
EVERY nonempty proper S satisfies

    H(S):=sum_i a_i[r_i(S)-s_i]>=0,
    J(S):=sum_(i notin S) a_i[r_i(S union{i})-r_i(S)]<=0.       (1)

Suppose also that EVERY nonempty proper A has a participant i in A with

    r_i(S)<=s_i for EVERY nonempty S subset A containing i.   (2)

THEOREM. The original game has a uniform-equilibrium payoff against all
unrestricted behavioral deviations. ONE target v is selected before
accuracy: every delta>0 has an actual independent private profile and a
horizon threshold delivering payoffs within delta of v and capping complete
unilateral deviations by v_i+delta at ALL later finite horizons.

There is NO insertion-graph assumption, NO strict H assumption and NO
strategic input. The rewards and weights are the only inputs; (1),(2) are
finite comparisons. Own singletons may be0, weights may vanish, and no
universal bound or normalization is required. This is not arbitrary Fin4 UE.

The proof produces an actual seed for a strict nearby table, its compact
constrained carrier, an escaping full root or explicit paid prefix, a
diagonal and actual approximating profiles. Reward closure then selects
one target for the original table. No safe child, supplied cap selector,
response-attaining optimizer, chronological spine or error sequence is input.

## 2. Actual carrier and arbitrary-root identities

Before absorption the only active public history is repeated all Continue.
Behavioral profiles therefore correspond to independent private deadline
laws on natural dates plus Never. Unrestricted one-player replacements
correspond to arbitrary such laws. Terminal payoff is affine in that law,
so its supremum equals the supremum over ALL finite pure deadlines and
Never; no attaining replacement or calendar truncation is needed.

For an actual profile let U_i be its terminal payoff and B_i its FULL
unrestricted response supremum. Let K be the closure of ALL actual pairs
(U,B), not of a chosen strategy family. A finite bound M on all rewards
and0 bounds every coordinate by[-M,M]. Hence K is nonempty and compact
and retains B>=U; it need not be convex and its points need not be actual.
Write

    d_i=B_i-U_i,       E=max_i d_i,
    L(B)=sum_i a_i(B_i-s_i).

Fix any product root q in[0,1]^I. For player i let A be its opponent
quitter set, and define

    c=product_i(1-q_i),       alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A union{i})],
    b_i=E[r_i(A) 1_(A nonempty)],
    C_i=b_i+alpha_i B_i,      g_i=Q_i-C_i,
    Delta_i=q_i(-g_i)_+ +(1-q_i)(g_i)_+.

Complete prefix semantics gives

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max(Q_i,C_i).                                      (3)

The cap split permits Quit now or Continue and then ANY old replacement.
It is exact even when the old supremum is not attained. For fixed q this
map is continuous and preserves K: it prefixes actual profiles, then
preserves their closure by continuity. A root may be chosen after the
point is fixed; no continuous root selector over K is required.

Subtracting coordinates gives the EXACT arbitrary-root account

    B_i'=q_i Q_i+(1-q_i)C_i+Delta_i,
    d_i'=c d_i+Delta_i,
    E'<=cE+Delta_max,       Delta_max=max_i Delta_i.          (4)

If q has proper support, every nonempty root coalition is proper and
weighted summation gives

    L(B')=cL(B)+sum_(S nonempty)p_q(S)H(S)
                         +sum_i a_i Delta_i.                (5)

A FULL cap-Nash root is a mixed Nash equilibrium of the finite Boolean
game with all-Continue vector B and absorbing rewards r(S). Its Nash
inequalities, including ALL inactive players, are equivalent to Delta=0.
Then d'=c d and E'=cE. Equations(3)--(5) do NOT assume Nash and retain
every early, simultaneous, intervening, late and Never response.

## 3. Strict-seed chamber and preservation under full Nash roots

Temporarily assume H({j})>0 for some j. Let j Quit0 surely and everyone
else Never. Its ACTUAL full pair is

    U_i=r_i({j}),       B_j=s_j,
    B_i=max(r_i({j}),r_i({i,j})) for i!=j.                    (6)

The owner gets s_j by any finite deadline and0 by Never, using s_j>=0.
Every other player chooses between joining at0 and the passive singleton
reward. Thus L(B)>=H({j})>0 and B_j=s_j. If E=0 a diagonal is already
produced. Otherwise fix lambda=L(B)/E>0 and the nonempty compact chamber

    C={(U,B) in K: min_i(B_i-s_i)<=0, L(B)>=lambda E}.        (7)

The objective is maximum debt E on C, not total debt or unconstrained E.
At a positive-E point in C, EVERY full cap-Nash root either yields a
diagonal or preserves C with E'=cE. A sure rate makes c=0 and (4) gives
a diagonal. Otherwise full support would have all rates interior. Put
z_i=q_i/(1-q_i)>0 and z_A=product_(j in A)z_j. Active indifference gives

    B_i-s_i=sum_(empty!=A subset I\{i})z_A
                     [r_i(A union{i})-r_i(A)],
    L(B)=sum_(empty!=S proper)z_S J(S)<=0,                  (8)

contrary to L(B)>=lambda E>0. Hence every remaining root has proper
support D. For nonempty D, (2) supplies i in D with Q_i<=s_i, because
every forced-Quit coalition is a subset of D containing i. Supported
Nash optimality gives B_i'=Q_i, retaining the low face. Equations(4),(5)
give E'=cE and L(B')>=cL(B)>=lambda E'. All Continue fixes the input.

## 4. Nonzero full roots from sinks and universal recipients

For distinct i,j put h_ij=r_i({i,j})-r_i({j}); draw j->i iff h_ij>0.
Suppose B>=s and T={i:B_i=s_i} is nonempty.

LEMMA. If the induced graph on T has a sink or a universal recipient,
the original finite game has a nonzero FULL cap-Nash root. A sink has
no outgoing positive arrow within T. A universal recipient receives a
strict positive arrow from every other vertex, without an outgoing rule.

For a sink i let only i quit with probability p>0. It is indifferent.
For each j!=i,

    Continue_j-Quit_j
      =(1-p)(B_j-s_j)+p[r_j({i})-r_j({i,j})].               (9)

This is nonnegative on T by the sink property and outside T for all
sufficiently small p>0 by the strict margins B_j>s_j. Finiteness retains
all inactive inequalities simultaneously, so this is a FULL root.

For a universal recipient i, suppose all Continue is the ONLY original
full Nash root. Add epsilon>0 to i's Quit action payoff in the finite
game and choose any perturbed Nash root. Compactness and the closed
Nash inequalities imply q^epsilon->0: every subsequential limit is
original Nash. Each outsider has g_j(0)=s_j-B_j<0, so its rate is0 for
all small epsilon. On tied coordinates finite expansion gives

    g_i(q)=sum_(j in T\{i})h_ij q_j+O(t^2),
    t=sum_(j in T\{i})q_j.

Positive linear coefficients dominate the bounded quadratic remainder
near0. If T={i}, g_i=0 exactly. Thus g_i+epsilon>0 near0 in every
case, forcing q_i^epsilon=1 and contradicting q^epsilon->0. The
ORIGINAL game therefore has a nonzero full root; no nonzero perturbed
limit or continuous selector is asserted.

Sets of size at most2 have a sink or universal recipient. On three
vertices, no sink means outdegree>=1 everywhere; no universal recipient
means indegree<=1 everywhere. Exactly three arrows occur and all degrees
are1, hence the graph is EXACTLY a bare directed triangle. Conversely
a bare triangle has neither special vertex. Zero differences are absent
arrows, not strict edges.

## 5. Bare triangles with positive forward product

Suppose the tied set T is a bare proper triple. Label its directed
cycle0->1->2->0 and write

    h=[[0,-n_0,p_0],[p_1,0,-n_1],[-n_2,p_2,0]],
    p_0=h_02>0, p_1=h_10>0, p_2=h_21>0,
    n_0=-h_01>=0, n_1=-h_12>=0, n_2=-h_20>=0,
    P=p_0p_1p_2>0,       N=n_0n_1n_2>=0.

These products are invariant under changing the cycle's starting vertex.
LEMMA. If P>N, there is a nonzero FULL original cap-Nash root, without
any H/J or flatness assumption.

Choose eta>0 with product_i(n_i+eta)<P, then sigma>1 with
sigma^2 product_i(n_i+eta)<P. Set

    w_0=1,       w_2=sigma(n_0+eta)/p_2,
    w_1=sigma(n_2+eta)w_2/p_1.

Then w>0 and w-transpose*h is positive in EVERY column, including
when reverse coefficients vanish. Suppose all Continue is the only
original full root. Add epsilon to EVERY tied player's Quit action.
As in Section4, any perturbed Nash root tends to0 and its outsider
rate is0 for small epsilon. Write t=sum_(i in T)q_i. Finite expansion
g=hq+O(t^2) gives mu>0,K<infinity with

    sum_(i in T)w_i g_i>=mu*t-K*t^2>=0

near0. The perturbed weighted gap exceeds this by epsilon sum_i w_i>0.
Some tied player strictly prefers Quit and has rate1, a contradiction.
Thus the original correspondence already contains a distant nonzero
full root. Finite mixed Nash existence is used only in finite games.

## 6. Reverse product: a paid non-Nash prefix with an exact low face

LEMMA. Let (U,B) be a positive-E point of C, with B>=s, tied bare
triple T, N>=P and H({j})>0 for some j in T. Under (1),(2), a FIXED
independent root supported on T stays in C and strictly reduces E.

Choose a flat participant of T by (2), and cyclically relabel it0.
Since N>=P>0, ALL n_i>0. Set

    z_1=1,       z_2=n_0/p_0,
    p_2/n_2<=z_0<=n_1n_0/(p_1p_0).                         (10)

The interval is nonempty exactly when N>=P and has positive endpoints.
Thus z>0, hz<=0 and (hz)_0=0. Product equality is included. Let k be
the fourth player. With q_k=0 the EXACT flat-row gap is

    g_0=-n_0q_1+p_0q_2+kappa q_1q_2,
    kappa=r_0(T)-r_0({1,2})+n_0-p_0.

For sufficiently small tau>0 take

    q_0=tau z_0,       q_1=tau z_1,
    q_2=n_0q_1/(p_0+kappa q_1),       q_k=0.                (11)

The denominator is positive near0, all tied rates lie in(0,1), and
q_i=tau z_i+O(tau^2). Direct substitution gives g_0=0 EXACTLY.
Every forced-Quit coalition for0 is a subset of T containing0, so

    B_0'=Q_0=C_0<=s_0.                                    (12)

No strict pair deficit or second-order low-face sign is assumed.
For every tied player, g_i=tau(hz)_i+O(tau^2). Hence its positive
part is O(tau^2), negative part O(tau), and Delta_i=O(tau^2).
The outsider has g_k(0)=s_k-B_k<0, so g_k<0 near0. Since q_k=0,
Delta_k=0 EXACTLY and its ENTIRE debt contracts as d_k'=c d_k.
Its full future response cap remains in C_k, not a selected deadline.

Put Z=sum_(i in T)z_i>0. For finite K and small tau>0,

    Delta_max<=K tau^2,       1-c>=(Z/2)tau,
    p_q({j})>=(z_j/2)tau.

Equations(4),(5), H>=0 and a>=0 give, for smaller positive tau,

    E'<=E-(EZ/2)tau+K tau^2<E,
    L(B')-lambda E'
      >=c[L(B)-lambda E]+p_q({j})H({j})-lambda Delta_max
      >=(z_j H({j})/2)tau-lambda K tau^2>=0.                (13)

The strict singleton H surplus pays the ENTIRE quadratic full-cap
defect. Together(12),(13) preserve C with the SAME lambda. Fixed-prefix
continuity preserves K even at a nonactual closure point. No Nash root,
safe child, altered continuation or pointwise outsider dominance is input.

## 7. Compact constrained minimum and removal of strictness

First suppose there is a strict singleton H seed and EVERY bare proper
triple either has P>N or meets a strict singleton H. The actual seed
and C are produced by Section3. Suppose the attained minimum of E on C
is positive, at(U*,B*). If some B_i*<s_i, all Continue is not Nash;
finite Nash existence supplies a nonzero full root, and Section3 gives
a diagonal or a smaller-E point in C. Both are contradictions.

Otherwise B*>=s. Its tied set is nonempty by the low face and proper
because L(B*)>0, so has at most three vertices. A sink or universal
recipient gives a nonzero full root by Section4 and the same contraction
contradiction. The only remaining graph is a bare triple. If P>N use
Section5; if N>=P use Section6 and its supplied strict singleton H.
All cases are exhausted, including zero reverse coefficients and P=N.
Thus min_C E=0. The minimizing pair is a diagonal(v,v) in K. Actual
profiles have BOTH terminal payoffs and full caps tending to the SAME
v. The checked diagonal consumer gives the fixed uniform target v.

In particular the intermediate hypotheses hold whenever TWO singleton
H values are strict: every triple meets their two-element set.

Now use ONLY the final raw assumptions (1),(2). Write A_*=sum_i a_i>0.
For every epsilon>0 define the literal passive-singleton raise

    r_i^epsilon(S)=r_i(S)+epsilon if S={j} with j!=i,
    r_i^epsilon(S)=r_i(S) otherwise.                        (14)

Own singletons are unchanged. Direct summation gives

    H^epsilon({j})=H({j})+epsilon(A_*-a_j),
    J^epsilon({j})=J({j})-epsilon(A_*-a_j).

For |S|>=2 BOTH H and J are unchanged. Every participant-flat comparison
is literally unchanged, because i in S excludes a changed passive entry.
At most one j has A_*-a_j=0: that equality means all other weights vanish,
and two such equalities would force A_*=0. Hence at least THREE singleton
H^epsilon values are strict. Every nearby table satisfies the intermediate
theorem, regardless of its graph. There is no need to preserve the graph
or put epsilon below its positive insertion gains.

Every nearby game has a uniform-equilibrium payoff and
|r_i^epsilon(S)-r_i(S)|<=epsilon. Checked reward-closedness gives UE
for r, permitting the nearby targets and profiles to vary. Equivalently,
for ANY fixed strategy laws, prescribed terminal payoff changes by at most
epsilon, EVERY deviating payoff by at most epsilon, and the full cap by
at most epsilon. Original maximum regret is within2epsilon of nearby
regret. Given delta>0, choose epsilon=delta/4 and a nearby actual terminal
profile of regret<=delta/2 from its diagonal carrier. Reuse the SAME laws
at r to obtain regret<=delta. The checked terminal-all-errors compiler
then selects ONE original uniform target; matching nearby targets is not
assumed. This proves the theorem even if EVERY original singleton H is0.

No weight is divided by. Nonnegative own singletons are used in the
exact seed cap only. All divisions are by positive p_i, by n_i>0 where
N>=P>0, and by the denominator in(11), positive near0. Constants may
depend on the table and minimizing pair. No universal convergence rate,
convexification, chronological selector or exact terminal Nash is asserted.

## 8. Boundary tests

The zero-H table r_i(S)=1 for every nonempty S and every i, with unit
weights, has H=J=0 and flatness by equality. It has no strict original
seed. Perturbation(14) gives H^epsilon({j})=3epsilon and
J^epsilon({j})=-3epsilon, leaving the other guards unchanged. This tests
the precise strictness removal; the original table has obvious equilibria.

Flatness alone does NOT give nonzero finite Nash escape for a bare
triangle. Consider a three-player Boolean game with all Continue and
own singleton rewards0. At sole j, recipient j+1 gets-2 and j-1 gets0,
modulo3. In each pair every participant gets-1 and the passive player0;
in the grand coalition everyone gets-1. Its exact gaps are

    g_i=q_(i-1)-q_(i+1)-q_(i-1)q_(i+1).

All participants are flat, P=N=1, and all Continue is its UNIQUE Nash
root. One positive rate makes its inactive successor want to Quit;
two give one supported player a negative gap; with three, the sum of
gaps is minus the positive sum of pair products, inconsistent with
supported Nash. This is a finite-root boundary, not a UE counterexample
or a claim that the raw H/J class has a positive minimum.

The next section supplies a literal admitted Fin4 table with P=2,N=12
on its bare triangle, exercising the paid-prefix orientation without
a graph guard. The proofs above separately cover P>N, zero reverse
coefficients, product equality, zero weights and zero own singletons.

## 9. Exact nonredundancy witness

Use unit weights, own singletons1, and the following complete table.
Vectors are in player order0,1,2,3; Never remains0.

| S | r(S) |
| --- | --- |
| 0 | (1,0,4,0) |
| 1 | (0,1,0,4) |
| 2 | (4,0,1,0) |
| 3 | (0,4,0,1) |
| 01 | (-1,2,3/2,3/2) |
| 02 | (5,2,0,2) |
| 03 | (2,3/2,3/2,-1) |
| 12 | (3/2,-3,1,9/2) |
| 13 | (2,0,2,0) |
| 23 | (3/2,3/2,-1,2) |
| 012 | (-1,-1,-1,10) |
| 013 | (-1,-1,10,-1) |
| 023 | (-1,10,-1,-1) |
| 123 | (10,-1,-1,-1) |
| 0123 | (9,9,9,9) |

Its singleton H values are all1 and singleton J=(-3,-4,0,-3).
H(02)=5, all other pair H=0, and in pair order01,02,03,12,13,23,
J=(-5,-6,-5,-8,-6,-5). Every triple has H=3,J=-1. Flat participants
for triples012,013,023,123 are2,3,2,1 respectively; every participant
subrow for the indicated player is<=1. Each pair has a flat member.
The insertion graph is EXACTLY

    0->1->2->0,       2->3->0.

Thus the theorem admits the table. Its bare012 fails both proper
acyclicity and the proper sink-or-universal-recipient graph guard,
independently of weights and relabeling. All six triangle insertion
differences have strict signs, so this failure persists nearby. It is
not a relabeling of the literal passive-triple template with own1,
adjacent participant rewards(-1,2) and opposite participant rewards0:
its pair participant reward5 is not among those allowed values. Section9.7
also excludes positive recipient-affine transport and its reward closure;
literal table inequality alone would not establish that stronger comparison.

### 9.1 Singleton and complete actual response-quotient selections

The singleton comparison matrix is

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    det Gamma=45,
    Gamma^-1=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2].

It is R0: every principal block of size>=2 is invertible, and a
singleton homogeneous complementary support fails an external negative
neighbor entry. Its nonnegative inverse and positive determinant give
degree1 by `r0Degree_eq_sign_det_of_nonnegative_inverse`. Every deleted
triple has determinant6 and a negative inverse diagonal, defeating ALL
literal raw nonnegative-inverse triple choices. The positive singleton
graph is an opposite matching, not a positive three- or four-cycle.

Actual response invariance requires equality of the full residual

    F_i(q)=(1-alpha_i)Q_i-b_i

on the block-constant unit cube. The necessary Gamma block-row-sum test
rejects eight of the fifteen set partitions. Every nondiscrete survivor
fails at the exact point below; only the discrete quotient survives.

| blocks | q | unequal original residuals |
| --- | --- | --- |
| 0123 | (1/2,1/2,1/2,1/2) | F0=-61/64, F1=-55/32 |
| 01\|23 | (0,0,1/2,1/2) | F0=-1/16, F1=-31/16 |
| 02\|13 | (0,1/2,0,1/2) | F0=-5/16, F2=-1/2 |
| 02\|1\|3 | (0,0,0,1/2) | F0=3/4, F2=0 |
| 03\|12 | (0,1/2,1/2,0) | F0=-5/8, F3=-7/4 |
| 0\|13\|2 | (0,0,1/2,0) | F1=-1/2, F3=3/4 |
| 0\|1\|2\|3 | arbitrary | Gamma, determinant45, degree1 |

This exhausts surjective block maps up to block renaming; a representative
section forces surjectivity. The discrete quotient's positive determinant
and degree1 defeat both the negative-determinant/nonnegative-inverse exit
and the degree-not-one exit. No quotient based only on selected reward
rows is substituted for actual response invariance.

These obstructions persist in a reward neighborhood. There are only
fifteen partitions: each rejected partition has a nonzero block-row or
displayed residual difference, and the discrete determinant remains
positive. The R0 and degree assertions are also stable here. Indeed, all
principal blocks of size at least2 remain invertible, and each singleton
support retains an external negative entry. Thus a nearby homogeneous
complementary vector would have no possible support. The whole matrix
retains its strictly positive inverse and positive determinant; each
deleted triple retains a negative inverse diagonal. Finite relabelings
or varying partitions cannot evade this census in a convergent sequence.

### 9.2 All protected, weighted and boxed choices fail

Every player has participant reward-1 in a proper triple, below own1.
Thus the maximal protected set is empty. Grand9 makes the full set a
premium trap, while proper flatness excludes all proper traps. No common
protected leaver or support-specific protected set exists, even with weak
leave comparisons or their passive reward-closure producer.

For ANY nonnegative global-floor weight w, the inserted-premium floor
at{1} requires -2w_0-w_3>=0, hence w_0=w_3=0. The floor at{3} requires
w_0-w_1-2w_2>=0, hence all weights vanish. Thus the ENTIRE nonzero
weight selection in `HasWeightedQuittingTrapLeavers` fails. The global
weighted upper-average alternative fails at grand, with surplus
8 sum_i w_i>0 for every nonzero w>=0.

For reward closure, normalize sum_i w_i=1. Adding the two necessary
global-floor rows gives -w_0-w_1-2w_2-w_3>=0, whose left side is at
most-1. Uniform reward perturbations change it by a uniformly vanishing
amount on this compact weight simplex. Thus weights tending to its
boundary, or unnormalized weights tending to infinity, cannot repair
the floor. The participant deficits and full-trap premiums are strict,
so the protected and weighted strict/weak reward-closure entrances also
fail nearby.

For ALL `QuittingTrapChargeCoefficients` on the full trap, singleton{2}
would require a strictly negative inserted-premium sum. Its actual sum
is(5-1)+(-3-1)+(2-1)=1>0. Consequently NO coefficient selection or
boxed threshold can work. Its leave sum J({2})=0 separately violates
the required strict singleton leave gap.

The inserted-premium obstruction1>0 is OPEN, unlike the zero leave sum,
so it also excludes reward closure of this boxed raw class. It defeats
any full-trap mixed upper-average-or-boxed selection, since both of its
alternatives have failed for EVERY coefficient choice. At the all-Quit
product root every active Quit endpoint is9>1; hence the all-root
`HasProductLowQuittingPremium` alternative fails as well, robustly.
No supplied support-local condition with a different quantifier is
identified with that all-root predicate.

### 9.3 All sure-owner induced roots and actual punishment floors fail

Every passive reward is nonnegative, so Never guarantees>=0. Every
actual cap and sound punishment lower value is therefore nonnegative.
Fix a sure owner; the other players' finite game is continuation-free.
The following exhausts its ENTIRE induced Nash correspondence.

- Owner0: opposite2's four joining gaps are(-4,-5/2,-5/2,-1), so2
  Continues. Then predecessor3's two gaps are(-1,-5/2), so3 Continues
  and successor1 surely Quits. The owner has Q_0=-1,b_0=0,alpha_0=0.
- Owner1: opposite3's four gaps are(-4,-5/2,-11/2,-1), so3 Continues.
  Then predecessor0's gaps are(-1,-5/2), so0 Continues and successor2
  surely Quits. The owner has Q_1=-3,b_1=0,alpha_1=0.
- Owner2: predecessor1's four gaps are(-3,-3,-5/2,-1), so1 Continues.
  For x=q_0,y=q_3 the remaining gaps are1-(7/2)y and2-5x. Their ENTIRE
  Nash set is(1,0),(0,1),(2/5,2/7). Owner(Q_2,b_2) is respectively
  (0,4),(-1,0),(1/7,46/35); at the mixed root alpha_2=3/7. Every
  case has Q_2<b_2+alpha_2 B_2 for ALL B_2>=0.
- Owner3: opposite1's four gaps are(-4,-5/2,-5/2,-1), so1 Continues.
  Then predecessor2 Continues and successor0 surely Quits. The owner
  has Q_3=-1,b_3=0,alpha_3=0.

Thus no full cap-Nash root with a sure label exists at any nonnegative
continuation. In particular the ENTIRE actual sure-owner/punishment-floor
selection fails, including boundary mixtures and bases with multiple sure
labels. Arbitrary negative unrealized continuations are not excluded.

### 9.4 Every child and all five raw withdrawal kinds fail

For each proper nonempty child C except012, choose a sole owner j with
all its positive outgoing arrows outside C. For pairs01,02,03,12,13,23
choose1,0,0,2,1,3; for triples013,023,123 choose1,0,3; singletons use
their member. Sole-j-Quit0 and the other child players Never is exact
unrestricted child Nash: every child joining reward is at most its
passive singleton reward, and the owner can get only1 or Never0.
Joint-Never mass is0. An omitted outgoing recipient joins profitably.
Thus ANY universal outside-debt bound by nonnegative weighted child
debts plus finite joint-Never slack fails for that child, at ALL weights.

For child012/outside3, direct raw F/J rows exclude ALL remaining
certificate choices. Put A={2} and use nonnegative advance weights
lambda. The future row, after discarding nonpositive withdrawal, requires

    1<=-3lambda_0+lambda_1.

The joining row, with the same advance weights, requires

    2<=lambda_0-3lambda_1.

Their sum gives3<=-2lambda_0-2lambda_1<=0, a contradiction. To justify
the discarded terms for EVERY `WithdrawalFutureJoinKind`: nonmembers
have withdrawal gain0; member2's singleton gain is its restart floor
minus own1. Patient floor<=max(1,0)=1; deadline floor<=0; evaluated
security floor<=0; terminal security floor<=1 by the security-value
singleton bound; cancellation uses the deadline floor. Future withdrawal
weight is either its nonnegative weight or0. Thus BOTH discarded terms
are nonpositive for every kind, irrespective of security optimization.

This excludes all five kinds, all advance/withdrawal weights and every
Never residual, without assuming an exact child012 Nash. Capped-clock
certificates are excluded by the same two rows. Additive F/J allowances
would have to satisfy futureError+joinError>=3 and cannot tend to0 on
this fixed table. For the other children the actual zero-debt, zero-Never
tests apply directly to the concluded full behavioral debt inequalities.

The whole-selection failure persists nearby. For the thirteen tested
children, every internal joining gap is strict, the owner's singleton
stays positive and some omitted joining gap stays positive. Their same
sole-owner laws therefore remain zero-debt, zero-Never falsifiers. For
child012 the summed coefficients of lambda_0,lambda_1 stay strictly
negative, while the already-present member2's advance coefficient is
identically0. Its withdrawal gain remains nonpositive: the applicable
restart floor is bounded by its positive own singleton. The summed
left side stays positive. Arbitrary finite withdrawal weights and Never
slack still cannot help. This excludes reward closure of these five raw
universal-certificate classes, not a conditional consumer supplied with
some favorable actual child equilibrium and a different comparison.

### 9.5 No exact stationary product Nash, over every support

Never gives nonnegative payoff, so an exact stationary value v is>=0.
Sure rates are excluded by Section9.3 at continuation v. All-Never fails
because own singletons are1. Remaining positive rates lie in(0,1).

Full support is impossible: positive singleton terminal probabilities,
H(singleton)=1, all proper H>=0 and grand H=32 give L(v)>0. The exact
full-support Nash odds identity(8) instead gives L(v)<=0.

One-player support fails at its positive-arrow successor. Adjacent
supports01,12,23,30 fail because the successor's Never is0 but Quit
payoff is respectively1+q_0,1,1+q_2,1+q_3>0. Opposite supports02,13
fail because player2,player1 respectively get4 by Never and at most1
by Quit. This exhausts supports of size at most2.

On three-player support, active indifference gives v_i=Q_i and
v_i=b_i/(1-alpha_i), hence Q_i>=b_i. For support013 put
(a,b,c)=(q_0,q_1,q_3). Flat player3 gives
1-2a-5b+(7/2)ab>=0. Endpoint checking first gives a<1/2, then
b<=(1-2a)/(5-(7/2)a)<=1/5. Player0 has Q_0=1+c-2b-bc>=3/5
but Never payoff2bc/(b+c-bc)<=2/5, contradiction. For support023 put
(a,b,c)=(q_3,q_0,q_2); flat2 has the SAME inequality and player3
has the SAME incompatible bounds. For support123 put
(a,b,c)=(q_2,q_3,q_1). Flat1 gives1-4a-5b+(11/2)ab>=0, forcing
a<1/4 then b<=1/5. Player2 has Q_2=1-2b>=3/5 and Never<=2/5.

For bare support012 put(a,b,c)=(q_0,q_1,q_2). Exact endpoints are

    Q_0=1-2b+4c-4bc,       b_0=4c-(5/2)bc,
    Q_1=1+a-4c+ac,         b_1=2ac,
    Q_2=1-a-ab,            b_2=4a-(5/2)ab.

From Q_0>=b_0 get b<=1/2, and from Q_2>=b_2 get
a<=[5-(3/2)b]^-1<=2/7. Active1 gives
0<=Q_1=2ac/(a+c-ac)<=2a, hence5/26<=c<=9/26<3/8.
But active0's exact stationary residual must vanish and equals

    F_0=b(1-2b)-c[3-(7/2)b+2b^2]+4c^2(1-b)^2.

For0<=b<=1/2,c<=3/8, the coefficient
3-(7/2)b+2b^2-4c(1-b)^2 is at least
3/2-b/2+b^2/2>=11/8, while b(1-2b)<=1/8. Thus
F_0<=1/8-(11/8)c<=-29/208<0, contradiction. EVERY support is
exhausted. No sound producer concluding an EXACT stationary product
Nash can cover this table, whatever its hazards or support.

For this specific exact-stationary comparison, reward closure fails too.
Suppose tables r^n converge uniformly to r and have exact stationary Nash
roots q^n. Compactness supplies a root limit q. If q is nonzero, root
absorption has a positive limiting probability. The actual stationary
terminal formula, its pure-Quit and pure-Continue endpoints and its
Never floor are continuous there. Nash inequalities pass to the limit,
giving the impossible exact stationary Nash of r.

If q=0, put t_n=sum_i q_i^n>0 and take a subsequence of
p^n=q^n/t_n converging to p in the probability simplex. The stationary
terminal mass of singleton{i} is

    q_i^n product_(j!=i)(1-q_j^n) /
                              [1-product_j(1-q_j^n)].

Its limit is p_i, since the denominator is t_n+O(t_n^2). The combined
terminal mass of coalitions of size at least2 is O(t_n). Consequently
the actual stationary value tends to 1+Gamma p, coordinatewise. Date-zero
Quit is an available unrestricted replacement and its endpoint tends
to own1, so Gamma p>=0. Whenever p_i>0, the rate q_i^n is positive
and strictly below1 for all large n, so active indifference gives
v_i^n=Q_i^n and (Gamma p)_i=0. Thus p is a NONZERO homogeneous
complementary vector of Gamma, contradicting the R0 proof in Section9.1.
This excludes closure of exact-stationary producers without an assumed
lower bound on their total hazard.

### 9.6 Nonstationary paired/matching and four-singleton selections

Stationary nonexistence does not exclude nonstationary producers. The
following separate literal guards and complete positive owner-field
calculation supply the relevant bounded nonstationary comparisons.

In `PairedCycle.RawRegion`, a recipient can have at most ONE quitter
whose singleton payoff is below that recipient's own singleton: it must
be its unique scheduled partner. Here every row has TWO such quitters.
Thus EVERY schedule fails. Positive recipient-affine transformations
and relabelings preserve these strict singleton-difference signs, so
they cannot restore membership. The strict sign obstruction persists
under sufficiently small reward perturbations.

For all strict, weak, inverse crossed-matching sources, their scheduled
pair joining-cap sources and the below-singleton joint-phase family,
the off-schedule participant pairs must be capped at the recipient's
own singleton, or strictly below it for the last family. Player0 has
TWO distinct participant pair rewards above own1:

    r_0({0,2})=5,       r_0({0,3})=2.

A pair partition puts at most one of2,3 with0. The other is off-schedule
and violates the necessary cap. This rejects EVERY pair partition and
proper hazard choice for `RawSource`, `WeakRawSource`, `InverseRawSource`,
`ScheduledPairCapSource` and `PairedCycle.BelowSingleton.RawFamily`.
Both surplus signs are strict, invariant under positive recipient-affine
table transport, and stable nearby; their weak/reward-closure versions
therefore also fail.

A four-phase paired passive-reward ray with a scheduled pair whose BOTH
participant premiums are positive cannot apply: EVERY pair in this table
has a participant strictly below its own singleton. In particular this
rejects the family with mate-pair participants A,A, own1 and
(5+sqrt(5))/2<A<4, under all relabelings, positive recipient-affine
images and reward limits. This is a necessary-premium comparison, not
a comparison of a selected solution's constants.

Next consider an exact periodic four-SINGLETON word: every player owns
exactly one phase, every owner hazard q_l lies in(0,1), and all other
players Continue at that phase. Put u_l=1-q_l. With any player's law
removed there remain three proper positive hazards, so opponent
absorption is almost sure. All prescribed phase values and every
deviating deadline endpoint are therefore the actual terminal ones.
At its own phase, positive proper mixing forces owner indifference;
the owner's prescribed value and its next-phase continuation coordinate
both equal its own singleton1.

If favorites0 and2 are adjacent in the cyclic order, inspect player0
at owner2's phase. If2 follows0, Continue has value1 by owner0's
indifference, while Quit yields1+4q_2. If2 precedes0, Continue has
value4q_2+(1-q_2)*1=1+3q_2, while Quit again yields1+4q_2. Each
case is a strict profitable deviation. This rejects every ordering in
which the favorites are adjacent; by rotation the other mutual favorite
pair gives the same conclusion when needed.

If favorites are not adjacent, the order is0123 or0321 up to rotation.
For either orientation, singleton-path recursion and owner indifference
give the COMPLETE field, with indices taken modulo4:

    E_l=u_l[4-4u_(l+1)+u_(l+1)u_(l+2)]-1=0.              (15)

For completeness, an owner's next-phase coordinate is1. The next
owner gives it singleton0, the opposite owner two phases later gives4,
and the preceding owner gives0 before returning to its own value1.
Substitution of these three scalar affine recursions gives(15).
Set a=u_0-u_2 and b=u_1-u_3. Subtraction gives

    E_0-E_2=4(1-u_1)a-u_2(4-u_0)b,
    E_1-E_3=u_3(4-u_1)a+4(1-u_2)b.

The coefficient determinant is
16(1-u_1)(1-u_2)+u_2u_3(4-u_0)(4-u_1)>0, so a=b=0.
Writing u_0=u_2=x,u_1=u_3=y, the remaining difference is
(4+xy)(x-y)=0. All four Continue probabilities coincide. Their common
equation factors as(u-1)(u^2-3u+1)=0, and the UNIQUE proper solution is

    u=(3-sqrt(5))/2.

At owner2's phase, player0's actual Continue value is1/u: its preceding
phase, owner1 or owner3, has value1 and passive reward0. Its literal
edited Quit endpoint is5-4u. Their difference is

    5-4u-1/u=2-3u=(3sqrt(5)-5)/2>0.                    (16)

Thus the MODIFIED pair rows exclude the ENTIRE positive four-singleton
word, not merely a symmetric guess or an unmodified table calculation.
The balanced-singleton mesh certificate has a distinct soloFloor field,
requiring EVERY phase value to be at least own1. It too fails on these
four-positive-singleton words: if mutual favorites are adjacent, choose
the one whose favorite follows it. Its value at that phase is1, so
the coordinate immediately afterwards is(1-4q_favorite)/(1-q_favorite)<1.
In the nonadjacent case the unique solution above has value u<1 at
the phase immediately preceding its own. This tests the actual field,
without treating a finite collision deviation as a mesh deviation.

The raw signed-four-cycle singleton producer, in BOTH spectral branches,
already fails its strictly positive predecessor four-cycle: Gamma's
positive graph is only an opposite matching. The cyclic-child joint-phase
raw table similarly requires a positive directed child three-cycle,
absent here. These sign comparisons are invariant under positive
recipient-affine table transport and strict in a reward neighborhood.

Finally, the two-pair group-exclusion reward entrance bounds BOTH
designated pair-average surpluses by a nonpositive value at every other
coalition. The grand coalition instead has surplus8 for EVERY pair,
so no relabeling works. The cross-mass reward entrance allows a positive
surplus only at a designated PAIR. Every designated recipient here has
a favorable SINGLETON surplus3, at which its bound is nonpositive.
Thus every label choice fails that entrance too.

### 9.7 Passive-triple transport and exact comparison scope

Consider the passive-triple family whose singleton rows are own1,
favorite4 and two neighbors0, whose adjacent participant pair rewards
are-1,2 and opposite participant pair rewards are0. Its passive pair
rewards are1; its triple/grand parameters may vary arbitrarily within
that family's inequalities. Suppose a relabeling and positive recipient-
affine transformation sends such a table to the present table. In each
recipient row the two low singleton coordinates force shift=0 and the
own singleton forces scale+shift=1. Hence scale=1. Its favorite is
forced by the unique positive singleton difference. This reasoning is
independent for EVERY recipient and covers all allowable relabelings.
The transformed participant pair coordinates therefore still belong
to{-1,0,2}, whereas the present table has5. Membership is impossible.

The same excludes positive scaling and reward closure of these images.
For a convergent sequence, finite relabelings permit a fixed subsequence;
the low and own singleton coordinates force each scale and shift to
converge to1 and0. The fixed participant pair discrepancy persists.
Even unbounded variable triple/grand parameters cannot change that
prescribed pair coordinate. No claim that arbitrary payoff translations
preserve the literal Never payoff0 is needed: this is a table-membership
comparison, not an unlicensed strategic transport theorem.

The witness therefore lies outside the named complete raw selections
and accepted finite families compared above, while satisfying the
new theorem. The arguments above are self-contained. Their scope is
bounded: they do NOT
assert a positive stationary or unrestricted regret gap, exclude
all-errors approximate stationary families, rule out longer/repeated-
owner or mixed solo/joint calendars, or classify every supplied-object
verifier or unknown distant implicit neighborhood. In particular a
universal quiet certificate and a favorable selected child equilibrium
are different objects. None of those unproved stronger assertions is
used in the existence theorem or the named producer comparisons.

## 10. Exact source correspondence

The semantic definitions and checked services are:

- `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix` and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`:
  the closure of actual payoff/full-cap pairs, compactness and fixed-prefix
  invariance used in Sections2,3,7.
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`:
  FULL finite root Nash existence at arbitrary continuation vectors.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect`
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`
  and `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`
  in `UniformEquilibrium/Quitting/Root/NashDefect.lean`:
  the exact ARBITRARY-root identity(4) and its displayed defect. No
  prescribed-payoff Nash block-action identity is substituted for them.
- `abs_quittingRootEndpointDifference_sub_solo_sub_tail_sub_collisionFlow_le`
  in `UniformEquilibrium/Quitting/Root/FirstOrderProductFlow.lean`:
  at tied coordinates the finite expansion has quadratic remainder
  bounded by4M times squared total rate. Sections4--6 also derive the
  needed expansions directly. The Nash specializations are
  `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`.
- `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
  in `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`:
  Section7's diagonal yields the SAME fixed target against unrestricted
  behavioral deviations, without sign, graph or stationarity assumptions.
- `abs_quittingContinuationBestResponseValue_sub_le_of_reward_close`,
  `abs_quittingTerminalExploitability_sub_le_of_reward_close` and
  `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
  The last delegates to
  `quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards`
  in `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean`.
  These give the one-epsilon cap bound, two-epsilon regret bound and
  fixed-target reward closure, permitting varying nearby targets.
  The alternative terminal compiler is
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The complete-selector comparisons use these exact raw definitions:

- `childMatrix` and
  `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`;
  `r0Degree_eq_sign_det_of_nonnegative_inverse` in
  `MathUE/LinearProgramming/NonnegativeInverseDegree.lean`.
- `QuittingResponseInvariantOnUnitCube` and
  `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
  `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
  in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.
- `IsCommonQuittingPremiumLeaver` in
  `UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`;
  `HasProtectedParticipantPremiums` and `HasSupportSpecificQuittingLeavers`
  in `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`;
  `exists_uniformEquilibriumPayoff_of_supportSpecific_weakLeave` in
  `UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversRewardClosure.lean`.
- `HasGlobalQuittingWeightedFloor`, `quittingWeightedInsertedPremium`
  and `HasWeightedQuittingTrapLeavers` in
  `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`;
  `QuittingTrapChargeCoefficients` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
  and `HasBoxedQuittingNashCharges` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`.
  The distinct all-root predicate `HasProductLowQuittingPremium` is in
  `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.
- The sure-owner semantics in
  `UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean` and
  `singletonBase_inducedNash_floorExcess_semantics` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`.
- `WithdrawalFutureJoinKind` and `WithdrawalFutureJoinRewardCertificate`
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`;
  their literal gain/floor definitions in `PatientWithdrawalRaw.lean`,
  `DeadlineWithdrawalRaw.lean`, `DeadlineWithdrawalRestartPointwiseCore.lean`
  and `DeadlineWithdrawalSecurityLP.lean` in that SAME directory,
  including `deadlineWithdrawalSecurityValue_le_singleton`.
  Their full behavioral-debt consumer is
  `quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
  in `WithdrawalFutureJoinFixedTarget.lean`. The capped-clock definitions
  are in `CappedClockPointwiseDomination.lean`; its actual full consumer is
  `quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack`
  in `CappedClockChildDeletionAdapter.lean`, in that SAME directory.
- `PairedCycle.RawRegion` and
  `PairedCycle.RawRegion.eq_partner_of_singleton_lt` in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`;
  `PairedCycle.CrossedMatching.RawSource`, `WeakRawSource`, `InverseRawSource`
  and `ScheduledPairCapSource` in
  `UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`;
  `PairedCycle.BelowSingleton.RawFamily` in
  `UniformEquilibrium/Quitting/Cycles/BelowSingletonJointPhaseSource.lean`.
  Their literal singleton and off-schedule collision fields are the
  necessary conditions separately rejected in Section9.6.
- `SignedFourCycleSingletonData` in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`
  and `SignedFourCycleSingletonData.LargerTests` in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleLargerRewardAdapter.lean`;
  `BalancedSingletonCycleCertificate` and
  `BalancedSingletonCycleCertificateWithBounds` in
  `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
  The last certificates have actual arc, active and soloFloor fields;
  finite-root collision optimality is not substituted for soloFloor.
- `CyclicChildJointPhase.RawTable` in
  `UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`;
  `hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds`
  in `UniformEquilibrium/Quitting/Paths/TwoPairGroupExclusion.lean` and
  `hasQuittingActualWeakSubsetExclusion_zero_one_of_crossMassBounds` in
  `UniformEquilibrium/Quitting/Paths/TwoPairCrossMassRewardExclusion.lean`.
  These entries impose the literal singleton-cycle or reward-bound
  hypotheses rejected in Section9.6; their broader conditional consumers
  are not claimed to have been excluded.

The new adapter needs only finite raw predicates(1),(2), the seed(6),
the compact chamber(7), the finite-root alternatives and the explicit
paid root(11), followed by the existing diagonal and reward-closure
consumers. It must not put the desired strategies, caps, favorable
roots or limit targets into an assumed structure field. The exact
ordinary calculations above are the mathematical obligations not
already asserted by the named generic Lean declarations.
