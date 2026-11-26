# Uniform equilibrium from a monotone-passive cap chamber

This is an ordinary-mathematical raw four-player existence theorem. The
generic terminal-semantic services and uniform-payoff consumer are existing
checked Lean; the reward-family adapter and chamber proof below are new
ordinary mathematics to be formalized.

## 1. Exact raw class and requested conclusion

Let the players be I=Z/4Z. Payoffs before the first quit and on perpetual
nontermination are zero. At the first finite quitting date, a nonempty
coalition S fixes the absorbing reward vector r(S). All numbers below are
finite real numbers. Choose independently:

* P_i>=4, for each recipient i;
* W_i(S)>=1, for every pair S and every outsider i not in S;
* K_i>=0 and G_i<=K_i, for each recipient i.

Define the ORIGINAL rewards by

    singleton {j}: j gets 1, j+2 gets P_(j+2), neighbors get 0;
    adjacent pair {j,j+1}: j gets -1, j+1 gets 2,
                          outsider i gets W_i({j,j+1});
    opposite pair: both members get 0, outsider i gets W_i(S);
    triple I\{i}: all three members get -1, outsider i gets K_i;
    grand coalition I: recipient i gets G_i.                     (1)

There are four free P coordinates, twelve free W coordinates, four K
coordinates, and four G coordinates. There is no upper bound on P,W,K,
no lower bound on G, and no aggregate grand-row condition.

**Theorem.** For every raw table (1), there is ONE fixed vector v and a
sequence of actual independent private behavioral profiles whose prescribed
terminal payoffs and FULL unilateral response suprema both converge to v.
Consequently v is a uniform-equilibrium payoff for the original quitting
game, against every complete unilateral behavioral replacement.

Explicitly, if gamma_n is expected average payoff over the first n
stages, then for every epsilon>0 there are one behavioral profile sigma
and an integer N such that for every n>=N and every player i,

    |gamma_n(sigma)_i-v_i|<=epsilon,
    gamma_n(tau_i,sigma_-i)_i<=v_i+epsilon
                  for EVERY complete behavioral replacement tau_i.

The same sigma works at all n>=N. The vector v is fixed before epsilon;
sigma and N may depend on epsilon. All conclusions are in expectation.

Before absorption, behavioral profiles are equivalently independent private
clock laws on Nat union {Never}. One player may replace its entire law;
the response supremum includes every finite pure deadline, Never, and
arbitrary private mixtures. No public correlation or supplied strategy is
assumed. The target is selected before accuracy. Neither an exact terminal
Nash profile nor a convergence rate is asserted.

## Conjecture-facing change

This is an actual-data uniform-equilibrium producer for a twenty-four-
parameter unbounded reward family, not a verifier for supplied strategies.
The raw family independently permits larger passive opposite-singleton
and pair rewards, permits passive triple rewards down to zero, and permits
grand/triple equality. The proof constructs an actual seed and constrains
the closed actual payoff/full-cap carrier by a low-cap condition and one
fixed cap-surplus/debt ratio. Cap-Nash roots then either give a diagonal
immediately or preserve that chamber with strictly contracting debt.

Its distinguishing calculation is nonnegative ROOT charge despite negative
raw triple charge: active indifference confines three-coordinate roots
to an explicit rectangle, and a bilinear corner argument controls their
charge. The exact witness in Section 8 compares this producer with the
applicable implemented criteria and previously admitted finite raw families.
Arbitrary four-player quitting-game existence remains open.

## Strategic inputs

Only P,W,K,G and their finite inequalities in (1) are inputs. Every
strategic object is produced:

* Section 3 specifies two actual private clocks, computes every pure
  response value, obtains their FULL caps, and fixes a positive chamber
  ratio from that actual seed.
* Section 2 uses the compact closure of ALL actual payoff/full-cap pairs,
  with the exact continuous prefix map and finite mixed Nash existence.
* Sections 4--6 prove the support and charge restrictions directly from
  the actual raw rewards; no favorable Nash-root selector is assumed.
* Section 7 attains the constrained minimum and constructs a nonzero
  full root explicitly in its tied boundary case, producing a diagonal.
* Actual carrier membership and the named semantic consumer provide actual
  profiles and one fixed original-game uniform target.

There is no strategic input, maximizing response, punishment law, safe
child, chronological spine, prescribed cap vector, continuation selector,
or vanishing-error sequence. No recursive producer is assumed.

## 2. Definitions and assumptions

For an actual profile let U_i be prescribed terminal payoff and B_i its
supremum over ALL complete unilateral replacements. Let S be the closure
of all actual pairs (U,B). Finite reward bounds make S nonempty and compact.
Every point has B_i>=U_i. Moreover B_i>=0: the literal Never response
encounters only nonnegative passive rewards 0,P_i,W_i(A),K_i, or Never 0.
Write

    d_i=B_i-U_i>=0,       D=max_i d_i.

For a product root q, let A be its independent opponent quitter set and put

    c=product_j(1-q_j),       alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A union {i})],
    b_i=E[r_i(A) 1_(A nonempty)].

Exact complete-response prefix semantics is

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max(Q_i,b_i+alpha_i B_i).                            (2)

For fixed q this continuous map preserves S. If q is a mixed Nash root
of the finite Boolean game with continuation B at all Continue, then

    B_i'=q_i Q_i+(1-q_i)(b_i+alpha_i B_i),
    d_i'=c d_i,                 D'=cD.                       (3)

An exact cap-Nash root exists by finite mixed Nash existence. Its inactive
inequalities are retained throughout; none of the support calculations
below substitutes for their existence.

If ANY q_i=1, then c=0 and (3) gives a diagonal member (U',B') of S
immediately. That already proves the theorem. This exit does not require
the prefixed point to satisfy a chamber inequality. Hence all further
arguments may handle only roots with every q_i<1. This is why equality
G_i=K_i causes no difficulty.

## Proof

### 3. An actual full-cap seed for unbounded passive pair rewards

Let

    Wmax=max(W_0({1,3}),W_2({1,3})),
    t=1/[2(2+Wmax)].                                         (4)

Then 0<t<=1/6. Players 0,2 Never. Independently, players 1,3 Quit at
date 0 with probability t and otherwise Never. The exact prescribed
values are

    U_i=W_i({1,3}) t^2                   for i=0,2,
    U_i=(1+P_i)t(1-t)                    for i=1,3.           (5)

For i=0,2, the payoffs of pure responses Quit 0, any positive finite
deadline, and Never are respectively

    1-t-t^2,     1-2t+(1+W_i({1,3}))t^2,     W_i({1,3})t^2.

The first minus the second is
t[1-(2+W_i({1,3}))t]>=t/2>0; the second exceeds the third by (1-t)^2.
For i=1,3 the same three responses pay respectively

    1-t,         1+(P_i-1)t,                  P_i t.

The middle value is largest: its excesses are P_i t and 1-t. A complete
behavioral response is a mixture of pure clock responses. Thus the FULL
caps are exactly

    B_0=B_2=1-t-t^2,
    B_i=1+(P_i-1)t                          for i=1,3.       (6)

In particular min B<1 and

    sum_i B_i-4=(P_1+P_3-4)t-2t^2>=4t-2t^2>0.             (7)

For either active seed player,
d_i=1-2t+(1+P_i)t^2>0, so the seed has D>0. Define the positive constant

    lambda=(sum_i B_i-4)/D

using this actual seed, and the nonempty compact chamber

    C={(U,B) in S: min_i B_i<=1,
                      sum_i B_i-4>=lambda D}.              (8)

The seed avoids every grand coalition and every passive triple reward,
so it is valid uniformly in K,G. It uses only two of the twelve W values;
arbitrarily large values shrink t rather than invalidate the seed.

### 4. Full support is impossible at positive chamber debt

Suppose (U,B) is in C with D>0 and a cap-Nash root has 0<q_i<1 for
every i. Put z_i=q_i/(1-q_i)>0 and z_A=product_(j in A)z_j. Dividing
active indifference by alpha_i gives

    B_i=1+sum_(empty!=A subset I\{i})
                    z_A [r_i(A union {i})-r_i(A)].          (9)

After summing, the coefficient of z_j is exactly 1-P_(j+2)<=-3:
the three joining participant rewards at singleton j sum 2-1+0=1.
For a pair A, its coefficient is

    sum_(i notin A)[-1-W_i(A)]<=-4.

For the triple I\{i}, its coefficient is G_i-K_i<=0. Therefore

    sum_i B_i<=4-3 sum_i z_i-4 sum_(|A|=2)z_A<4,            (10)

contrary to sum B>=4+lambda D>4. Every surviving root with all rates
below one has support at most three. This argument uses the ACTUAL
enlarged rewards and does not suppress any passive coordinate.

### 5. Proper supported roots keep a low cap and satisfy exact bounds

All bounds here are necessary consequences of active indifference and
B>=0. Increasing P or W only increases the relevant Continue-stop term;
the proper-support forced-Quit endpoint Q is unchanged because participant
rewards in (1) are fixed.

Singleton support owned by i has B_i'=Q_i=1.

For adjacent support rotate to q=(a,b,0,0), a,b>0. Then

    Q_0=1-2b,       b_0=0,
    (1-b)B_0=1-2b.

Thus b<=1/2 and B_0'=Q_0<1.

For opposite support q=(a,0,e,0),

    Q_0=1-e,       b_0=P_0 e,
    (1-e)B_0=1-(P_0+1)e.

Hence e<=1/(P_0+1)<=1/5, and similarly a<=1/5. Again B_0'=1-e<1.

For support three rotate the missing label to 3 and write
q=(a,b,e,0), with a,b,e>0. The forced-Quit values are

    Q_0=1-2b-e+be,
    Q_2=1-a+b-2ab,

whereas the enlarged passive rewards give

    b_0=P_0 e(1-b)+W_0({1,2})be >=(4-3b)e,
    b_2=P_2 a(1-b)+W_2({0,1})ab >=(4-3b)a.

Since Q_i=b_i+alpha_i B_i>=b_i for active i,

    1-2b-5e+4be>=0,
    1-5a+b+ab>=0.

Consequently

    0<=b<=1/2,
    0<=a<=A(b):=(1+b)/(5-b),
    0<=e<=F(b):=(1-2b)/(5-4b),                            (11)

and B_0'=Q_0<1. Thus every nonempty proper supported root keeps a low
cap. The all-Continue root preserves the original low cap.

### 6. Nonnegative charge with K as low as zero

Let T(S)=sum_i r_i(S) and let p_q(S) be the product-root probability
of coalition S. For cap-Nash roots, (3) yields

    sum B'-4=c(sum B-4)+H(q),
    H(q)=sum_(S nonempty)p_q(S)[T(S)-4].                  (12)

For every proper S, its actual total reward dominates the base values

    singleton 5, adjacent pair 3, opposite pair 2, triple -3.

The triple bound uses ONLY K_i>=0. Write H0 for the root charge using
these base totals. Then H(q)>=H0(q) whenever q has proper support.
The grand row never occurs in this comparison.

For singleton support H0=q_i>=0. For adjacent support (a,b,0,0),

    H0=a+b-3ab>=0                                      (13)

because b<=1/2: if b<=1/3 its a coefficient is nonnegative; otherwise
its minimum over a in [0,1] is 1-2b>=0. For opposite support,

    H0=a+e-4ae>=a/5+e>=0,                              (14)

using e<=1/5.

For three-support q=(a,b,e,0), direct expansion, INCLUDING the negative
triple charge -7abe, gives the cancellation

    H0=a+b+e-3ab-4ae-3be
       =b+(1-3b)(a+e)-4ae.                            (15)

For fixed b this is bilinear in (a,e), so on the rectangle (11) its
minimum occurs at a corner. Its four corner values are

    (0,0):     b;
    (A,0):     (1-b)(1+4b)/(5-b);
    (0,F):     (1+2b^2)/(5-4b);
    (A,F):     [10b^3+11b^2-11b+6]/[(5-b)(5-4b)].        (16)

Every denominator is positive on [0,1/2]. In the last numerator,

    10b^3+11b^2-11b+6
          =10b^3+11(b-1/2)^2+13/4>0.

Thus H0>=0 for every admissible three-support root, even though its
raw triple charge is negative. Equations (12)--(16) prove H(q)>=0
for every proper root allowed by Section 5.

Combining Sections 4--6, every cap-Nash prefix from a positive-debt
point of C either has a sure rate and already yields a semantic diagonal,
or remains in C with D'=cD. The latter claim also covers all Continue.

### 7. A nonzero root at a positive chamber minimizer

Let (U*,B*) minimize D on C, and suppose D*>0. If min B*<1, all
Continue is not Nash because a player can Quit for its singleton value 1.
Finite mixed Nash existence then gives a nonzero full cap-Nash root.

Otherwise every B_i*>=1, at least one equals 1, and sum B*>4 ensures
some cap exceeds 1. Walking round the directed four-cycle gives an edge
i to i+1 with B_i*=1 and B_(i+1)*>1. Let only i Quit with probability

    0<p<min(1,(B_(i+1)*-1)/(B_(i+1)*+1)).

The owner is indifferent. Its successor's Continue value is
(1-p)B_(i+1)*>1+p, its Quit endpoint. Its predecessor's Continue value
is at least 1-p>=1-2p, its Quit endpoint. Its opposite's Continue value
is P_(i+2)p+(1-p)B_(i+2)*>=1+3p>=1-p, its Quit endpoint. This is a
nonzero FULL exact Nash root, including all inactive players.

If that root has a sure rate, Section 2 already yields a diagonal of S.
Otherwise 0<c<1 and its prefix is in C with D'=cD*<D*, a contradiction.
Hence S has a diagonal. Actual carrier membership supplies actual profiles
whose U and full B converge to the SAME fixed v; the named unrestricted
uniform consumer gives the theorem.

The root is chosen at the limiting carrier point. Its fixed prefix map
is continuous, so it preserves S even if that root is not Nash at nearby
actual approximants. No continuous selector or exact-root spine is used.

## 8. Exact nonredundancy witness

### 8.1. Literal table, raw guards, and the former chamber families

Take P_i=4, K_i=6, G_i=5 for every i, with all W=1 except
W_0({1,3})=2. Its complete table is:

| S | r(S) |
| --- | --- |
| 0 | (1,0,4,0) |
| 1 | (0,1,0,4) |
| 2 | (4,0,1,0) |
| 3 | (0,4,0,1) |
| 01 | (-1,2,1,1) |
| 02 | (0,1,0,1) |
| 03 | (2,1,1,-1) |
| 12 | (1,-1,2,1) |
| 13 | (2,0,1,0) |
| 23 | (1,1,-1,2) |
| 012 | (-1,-1,-1,6) |
| 013 | (-1,-1,6,-1) |
| 023 | (-1,6,-1,-1) |
| 123 | (6,-1,-1,-1) |
| 0123 | (5,5,5,5) |

This belongs to the raw class (1). Its only premium trap is all four:
each participant reward 2 closes the directed predecessor cycle, whereas
every proper triple has a flat participant. The own singleton vector is 1.

The actual seed in (4)--(6) has t=1/8 and exact pair

    U=(2,35,1,35)/64,       B=(55,88,55,88)/64,
    D=54/64=27/32,         sum B-4=15/32,
    lambda=5/9.                                             (17)

Neither the triple nor grand rows are encountered by these seed clocks
or their unilateral response tests, so these values remain exact here.

The earlier literal passive-triple family has fixed W=1 and K_i>=7.
No relabeling or positive recipient-affine image of that family yields this
table. In every recipient row the three participant pair values form
{-1,0,2}. A positive affine map carrying this finite set to itself has
scale 1 and shift 0, even after a partner relabeling. The outsider pair
value 2 then cannot come from the old value 1; also K=6 cannot come from
K>=7. The same argument excludes reward limits of these images: a fixed
subsequence of the finitely many relabelings and the pair extrema force
scales to 1 and shifts to 0.

For every nonzero nonnegative weight a, writing A=sum a,

    H_a(I\{j})=7a_j-2A,       sum_j H_a(I\{j})=-A<0.

Consequently no weighted graph-free H/J-flat, sink-or-receiver, or older
two-ledger raw entrance can cover the table. This excludes ALL weights,
positive recipient-affine images of those guards, and their reward closure.
Normalize A=1 for the closure assertion; the summed margin remains -1.

### 8.2. Exact stationary Nash is excluded on every support

First no finite full Nash root has a sure player, at ANY continuation.
If i is sure, opposite i+2 has joining gaps -4, -1-W<=-2, and 5-6=-1,
so Continues. Predecessor i-1 then has gaps -1 and -1-W<0, so Continues.
Successor i+1 strictly joins, earning 2 instead of 0. The owner i then
receives -1 instead of the 0 available by withdrawing. This contradiction
exhausts all partly-sure and multi-sure roots.

All Never fails because own singletons are 1. A single proper active
player fails at its positive-arrow successor. For adjacent support, its
active successor receives 0 by Never but has positive Quit endpoint.
For opposite support, either active player gets 4 by Never and at most
1 by Quit.

Here an interior active stationary player must have actual value
v_i=Q_i=b_i+alpha_i v_i: root indifference and stationary recursion
give v_i=Q_i, and hence v_i=b_i/(1-alpha_i) when alpha_i<1. For the
adjacent active successor that value is 0, while Q_i>0; for opposite
support it is 4, while Q_i<=1. These exact equalities justify the two
support exclusions without treating comparison with Never alone as
sufficient for every stationary mixing claim.

For a three-player support rotate to q=(a,b,e,0). The forced-Quit values
of the first and middle players, and their opponent-stop terms, satisfy

    Q_0=1-2b-e+be,       b_0>=(4-3b)e,
    Q_1=1+a-2e-ae,      b_1=w ae,       1<=w<=2.

Stationary active indifference is Q_i=b_i/(1-alpha_i), not merely Q_i>=b_i.
Thus Q_0>0, b<1/2 and b_0>(5/2)e. Also Q_0<1-2b, and

    (1+e)-2(1-2b)(b+e-be)
                   =(1-e)(1-2b+4b^2)+4be>=0.

It follows that b_0=Q_0(b+e-be)<(1+e)/2 and e<1/4. Therefore
Q_1>1/2, whereas b_1/(a+e-ae)<=w e<=2e<1/2, contradiction.
The one exceptional w=2 occurs when player 0 is the middle player of
support {3,0,1}, i.e. triple013; it is INCLUDED in this argument.

For full proper support put z_i=q_i/(1-q_i)>0. For each i abbreviate

    x_i=z_(i-1), y_i=z_(i+2), w_i=z_(i+1),
    T_i=x_i y_i+x_i w_i+y_i w_i,
    V_i=x_i y_i w_i, A_i=x_i+y_i+w_i+T_i+V_i,
    P_i=1+2x_i-w_i-T_i+5V_i,
    N_i=4y_i+T_i+6V_i+1_(i=0)z_1 z_3.

Stationary indifference requires F_i=N_i(1+A_i)-P_i A_i=0.
Direct expansion gives

    sum_i F_i=sum_i z_i+Q(z)+z_1 z_3(1+A_0)
      +sum_i[5V_i+3T_i(2y_i+w_i)+(2T_i^2-x_i V_i)
                     +V_i(5y_i+2w_i)+3T_i V_i+V_i^2],
    Q(z)=2sum_i z_i^2+(z_0-z_2)^2+(z_1-z_3)^2
                                      +7sum_i z_i z_(i+1).

All displayed terms are nonnegative, and sum z_i>0. The polynomial
2(xy+xw+yw)^2-x(xyw) has its six monomial coefficients 2,2,2,3,4,4.
Thus every exact stationary support is exhausted.

This excludes EVERY sound producer concluding an exact stationary Nash,
whatever its input thresholds, root choice, or matrix selection. It includes
the positive-inverse coalition jackpots, signed single-column jackpot,
guarded stationary criteria, and endpoint-three-passive-poles conclusions.
It also excludes reward closure of exact-stationary producers. For a
convergent table/root sequence, a nonzero root limit has positive joint
absorption probability, so the actual stationary value formula and finite
Quit/Continue endpoints pass continuously to the limit. Bellman recursion
and the finite root Nash inequalities hold there. For a player with
alpha_i<1, opponents absorb almost surely; iterating the endpoint bounds
and letting bounded opponent-survival remainders vanish controls EVERY
behavioral replacement, including Never. If alpha_i=1, this is the sole
positive-rate player; its prescribed value is its own singleton 1 and
Never pays 0. Thus the limit is full terminal Nash, already excluded.
No continuity of Never payoffs or of full caps is asserted.
If q^n->0, put t_n=sum q_i^n and pass to q^n/t_n->p in the simplex.
The stationary terminal mass of singleton {i} is

    q_i^n product_(j!=i)(1-q_j^n) /
                              [1-product_j(1-q_j^n)].

The denominator is t_n+O(t_n^2), so singleton masses tend to p; the
combined mass of coalitions of size at least two is O(t_n) and tends
to zero.
Hence stationary values tend to 1+Gamma p. Quit-now inequalities give
Gamma p>=0; positive p_i gives active equality (Gamma p)_i=0.
The R0 calculation below excludes this nonzero complementary vector.
No stationary regret-gap claim follows from this closure argument.

### 8.3. Complete matrix, quotient, protected, and charge selections

The singleton comparison matrix and inverse are

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    det Gamma=45,
    Gamma^-1=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2].

Every size-two principal determinant is -1 or -9, each triple determinant
is 6, and a singleton homogeneous complementary support fails at a negative
neighbor. Thus Gamma is R0, with positive inverse and degree 1. Every
deleted-triple inverse has a negative diagonal entry. This rejects all four
choices of `childMatrix` in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`).

The necessary singleton block-row-sum test leaves seven of the fifteen
partitions. For the six nondiscrete survivors the ACTUAL residual
F_i(q)=(1-alpha_i)Q_i-b_i is unequal as follows:

| blocks | q | unequal residuals |
| --- | --- | --- |
| 0123 | (1/2,1/2,1/2,1/2) | F0=-21/16, F1=-19/16 |
| 01\|23 | (0,0,1/2,1/2) | F0=-7/8, F1=-23/16 |
| 03\|12 | (0,1/2,1/2,0) | F0=-23/16, F3=-7/8 |
| 02\|13 | (0,1/2,0,1/2) | F0=-5/16, F2=-1/16 |
| 02\|1\|3 | (0,0,0,1/2) | F0=3/4, F2=0 |
| 0\|13\|2 | (0,0,1/2,0) | F1=0, F3=3/4 |

Only the discrete quotient remains, with degree 1 and positive determinant.
The exact definitions are `QuittingResponseInvariantOnUnitCube`
and `quittingSingletonBlockRowSum_eq_of_responseInvariant`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`).
Positive row scales do not rescue another partition: rejected partitions
have opposite signs in a required singleton block sum; on each surviving
block, a nonzero common block sum forces equal scales within that block.
Then the displayed residual mismatches persist. Finite partitions and strict
margins also exclude the relevant reward-closure entrances.

Explicitly, the eight rejected partitions are the four triple/singleton
splits and the four adjacent-pair/two-singleton splits. In a triple block,
one internal block sum has opposite sign from another; for an adjacent
pair block, an external singleton produces required sums of opposite
sign. The other seven partitions are precisely the six printed above
and the discrete partition. Nonzero common within-block sums force equal
positive scales inside every surviving block, so none of the displayed
residual discrepancies can be hidden by those scales.

Every player has participant triple reward -1<1, so no protected player
exists. This defeats `IsCommonQuittingPremiumLeaver`,
`HasProtectedParticipantPremiums`, and
`HasSupportSpecificQuittingLeavers` in their correspondingly named files
under `UniformEquilibrium/Quitting/Classification/`, including weak leaves.
For the global weighted floor, coalition02 has inserted-premium vector
(-1,-2,-1,-2), strictly negative in EVERY coordinate. Thus no nonzero
nonnegative global-floor weight can work. Grand5 makes every upper-average
or participant-only supportwise certificate fail at the full trap; all-Quit
also refutes `HasProductLowQuittingPremium` directly. These sign obstructions
are invariant under positive row-affine reward transport and stable nearby.

For clarity, supportwise balance would require on active support I one
nonnegative weight vector normalized to sum 1 whose participant premium
sum is nonpositive on EVERY nonempty contained coalition. Its grand-row
test here is exactly 4, impossible. The global upper-average test at
grand is 4 sum_i w_i>0 for every nonzero nonnegative w. At the all-Quit
product root every forced-Quit endpoint is 5>1, directly violating the
all-root product-low requirement of a low active endpoint.

For boxed charges define the actual OUTSIDER sums

    P(S)=sum_(i notin S)[r_i(S union{i})-1],
    L(S)=sum_(i notin S)[r_i(S union{i})-r_i(S)].

For every singleton S these are P=-2,L=-3; for every triple S they
are P=4,L=-1. Necessary coefficient tests are P<=-delta,L<=-gap on
singletons and P<=tau,L<=-loss on triples, with all four coefficients
positive. In cardinality four the exact threshold is

    threshold=4 sqrt(delta/tau)[gap+loss*delta/tau],

and the actual criterion requires 4+4M<threshold for a uniform absolute
reward bound M.

For all boxed coefficients delta,tau,gap,loss in the original table,

    delta<=2, tau>=4, gap<=3, loss<=1,
    threshold<=7sqrt(2)<28=4+4*6.

This compares the WHOLE coefficient selection with the best allowed reward
bound M>=6. In fact it excludes arbitrary positive row-affine images whose
own rewards remain nonnegative. Write row scales u_i>0, T=sum u_i,
m=max u_i, n=min u_i. Summing the four singleton conditions and using the
four penultimate conditions gives

    delta<=T/2, tau>=4m, gap<=3T/4, loss<=n,
    delta/tau<=1/2, threshold<=7sqrt(2)m.

Every transformed row has reward range 7u_i, so any absolute reward bound
is at least 7m/2. The required threshold exceeds sum of own rewards plus
4M>=14m, impossible. This also defeats the only trap's mixed upper-or-charge
and mixed-premium-trap alternatives. The source predicates are
`QuittingTrapChargeCoefficients`
(`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`)
and `HasBoxedQuittingNashCharges`
(`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`).

### 8.4. Whole induced-base, universal quiet-child, and finite raw calendars

Every passive reward is nonnegative, and a sure successor singleton holds
any player's full cap to zero. Thus actual punishment values are exactly
zero. The no-sure proof in Section 8.2 excludes every full induced-base row
retaining all omitted-player joins and all owner withdrawals, not merely
stationary repetition. In particular an owner's negative row payoff cannot
be repaired by a punishment floor below zero. The finite base/free game
is `quittingPersistentBaseNashSet`
(`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`).

For EVERY nonempty proper child C choose j in C with j+1 outside C.
The child profile sole j Quit0, all other child players Never, is exact
terminal Nash: the other possible child joins pay -1 instead of 0, or 0
instead of 4. Its joint-Never mass is zero. In the full quiet lift the
omitted successor j+1 can Quit0 for 2 instead of 0. This falsifies every
universal bound by weighted child debts plus finite Never residual, for
all children and all nonnegative weights. It directly contradicts the
conclusions of
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`)
and `quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockChildDeletionAdapter.lean`)
if their raw certificates were supplied. This covers all five withdrawal
kinds, not an arbitrarily selected child equilibrium. It does not exclude
a different theorem restricted to a favorable selected child equilibrium.

`PairedCycle.RawRegion.eq_partner_of_singleton_lt`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`) permits at
most one below-own singleton source per recipient; here there are two.
Every pair partition leaves an incoming participant reward 2 outside a
scheduled pair, defeating the off-schedule own cap in all strict, weak,
inverse and scheduled-pair-cap crossed-matching sources, and the
below-singleton joint-phase source. The relevant raw definitions are in
`CrossedMatchingPhaseSource.lean` and `BelowSingletonJointPhaseSource.lean`
in that same directory. Every pair has a participant at or below 0, so the
positive-joint paired templates and their specified small neighborhoods
also fail. Singleton positive comparison edges form only the opposite
matching, rejecting signed-four-cycle and positive-child-three-cycle raw
entrances. These are strict finite sign exclusions, preserved by row-affine
changes and reward limits of the named sign-guarded entrances.

The signed-inverse-column raw criterion also fails every pair partition:
its necessary signed inverse condition is Gamma^-1 diag(sigma)>0
entrywise for sigma_i in{-1,1}, and sigma_i Pi_i>=0 for every scheduled
participant premium Pi_i=r_i({i,mate(i)})-1. The strictly positive inverse
forces every sigma_i=+1, requiring every scheduled premium nonnegative.
Every pair has a strictly negative participant premium. The strict
inverse and premium signs persist nearby and under positive recipient
scales; arbitrary recipient shifts cancel from the comparisons.

The opposite-sign matching construction has a different necessary raw
form. It uses distinct commuting matching involutions f,a, with o=f
composed with a; f is the favorite matching and a is the scheduled
matching. For some b_i>0 and common H>2 its singleton equations are

    r_i({i})=s_i,
    r_i({f(i)})=s_i+H b_i,
    r_i({a(i)})=r_i({o(i)})=s_i-b_i.

Here they force s_i=1, b_i=1, H=3 and f=(02)(13). Since a is distinct
from f, every scheduled pair is adjacent. The construction requires a
common participant coefficient Pi on each scheduled pair, meaning
r_i(pair)=s_i+Pi b_i for both members. Our normalized coefficients are
-2 and +1, contradicting that equality. Divide by the strict own-minus-
low singleton difference for positive recipient-affine images; the same
gap 3 remains. Finite relabelings and nonvanishing singleton denominators
preserve it in reward limits. This exclusion retains the construction's
summed off-schedule caps; no individual-cap assumption replaces them.

The scalar singular-circuit construction requires selected roles 0,2
with opposite reciprocal singleton signs,

    s_0-r_0({2})>0,       r_2({0})-s_2>0.

Every distinct pair of labels in the witness has reciprocal differences
of the SAME strict sign: positive for opposite labels and negative for
neighbors. Thus no role selection can meet these inequalities. Positive
recipient scales and small reward perturbations preserve the obstruction.

The four-phase passive-reward ray and four-joint/rectangle constructions
require a scheduled pair with BOTH participant premiums positive. There
is none. The specified local four-joint families retain that necessary
premium condition, so their strict finite neighborhoods fail as well.
The triple-singleton collision-box construction instead requires all six
joining gaps r_i({i,j})-r_i({j})>0 in some three-player child. Every pair
here has a negative such gap: -1 for the donor of an adjacent pair, or
-4 for either member of an opposite pair. No child choice meets all six.

### 8.5. Every proper four-owner singleton calendar fails

Consider ANY cyclic word in which each player owns exactly one phase,
the owner uses one fixed proper positive hazard q_i in(0,1), every other
player Continues, and the four phases repeat. Against one deviator the
other three positive hazards ensure opponent absorption almost surely,
so all phase values are actual terminal values. Exact Nash would force
the owner's actual value and its next-phase continuation coordinate to
equal its own singleton 1, by proper mixing at its own phase.

Every cyclic ordering of four distinct owners has a pair of chronologically
adjacent labels that are neighbors modulo 4: otherwise every consecutive
pair would be opposite, but an opposite matching cannot form a four-cycle.
Write these neighboring labels as j=i-1. Their literal rewards satisfy

    r_i({j})=0,       r_i({i,j})=2,       s_i=1.

If j's phase immediately precedes i's phase, player i's Continue value
at j is (1-q_j)*1, whereas Quit yields 1+q_j, a gain 2q_j>0. If i's
phase immediately precedes j's phase, the owner's preceding indifference
gives player i's actual Continue value 1 at j; Quit there yields 1+q_j,
a gain q_j>0. Either way a unilateral action change is profitable.

Thus EVERY cyclic order and EVERY proper positive hazard choice fails,
not merely a symmetric guess. From any initial phase, reaching that
profitable phase without prior absorption has positive probability, so a
replacement that waits to exploit it also yields a strict terminal gain.
No repeated-owner, longer, or mixed calendar is excluded by this argument.

Greatest-core size two or three criteria fail because the greatest premium
core here is I, including the joining-attractive and mixed-sign triple-core
criteria. The two-pair group-exclusion raw reward entrance fails because
grand5 has pair-average surplus 4 for EVERY designated pair, whereas its
non-designated-coalition bound is nonpositive. The cross-mass reward entrance
allows a positive surplus only at its designated pair; every recipient here
instead has favorite-singleton surplus 3. The exact declarations are
`hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds`
(`UniformEquilibrium/Quitting/Paths/TwoPairGroupExclusion.lean`) and
`hasQuittingActualWeakSubsetExclusion_zero_one_of_crossMassBounds`
(`UniformEquilibrium/Quitting/Paths/TwoPairCrossMassRewardExclusion.lean`).

### 8.6. Exact coverage scope

The witness is admitted by the complete raw producer (1) and excluded
by the named whole raw selections and finite families above. A producer
that concludes exact stationary Nash is excluded by Section 8.2,
independently of every numerical threshold and strategic selection. The
nonstationary raw comparisons use their own literal necessary guards and
the four-owner word argument; they are not inferred from stationary
nonexistence. Universal quiet certificates are distinguished from a
different theorem that might select a favorable child equilibrium.

No claim is made of a positive stationary regret infimum, an unrestricted
terminal exploitability gap, noncoverage by every supplied-object
verifier, repeated-owner or arbitrary mixed calendars, all-errors
approximate stationary profiles, or an unknown distant implicit-function
neighborhood. None of those stronger assertions is used by the existence
proof or the bounded producer comparisons. Arbitrary row translations
are not asserted strategic symmetries, since literal Never still pays 0;
affine statements above concern raw predicate membership under explicitly
preserved signs/equalities.

## 9. Boundary tests and an exact failed relaxation

Nonnegativity W_i(S)>=0 of passive pair rewards does not suffice for
cap-Nash optimality to preserve the same surplus chamber. The implication
is false even with a deterministic actual clock origin and a two-coordinate
root, as the following exact counterexample shows.

Keep P_i=4, all W_i(S)=0, K_i=0, G_i=-1, and every participant reward
from (1). Use actual clocks

    T_1=0,       T_3=1,       T_0=T_2=Never.

The exact actual pair is

    U=(0,1,0,4),       B=(0,4,2,4),       D=3,
    sum B-4=6.                                             (18)

For player 0, Quit 0 pays -1 and every positive deadline/Never pays 0.
For player 1, Quit 0 pays 1, Quit 1 pays 0, and every later deadline/Never
pays 4. For player 2, Quit 0 pays 2 and every positive deadline/Never pays
0. For player 3, Quit 0 pays 0 and every positive deadline/Never pays 4.
These exhaustive pure responses verify the FULL caps in (18), rather
than an arbitrary supplied vector. Its chamber ratio is lambda=2.

Take the root q=(3/5,1/2,0,0). Its exact Quit and Continue endpoints
against B are

| player | Q_i | b_i+alpha_i B_i |
| --- | --- | --- |
| 0 | 0 | 0 |
| 1 | 8/5 | 8/5 |
| 2 | 3/10 | 8/5 |
| 3 | -2/5 | 8/5 |

Thus this is a FULL exact cap-Nash root; both inactive-player inequalities
hold strictly. Its Continue mass is c=1/5, and the exact prefixed pair is

    U'=(0,1,6/5,8/5),       B'=(0,8/5,8/5,8/5),
    D'=3/5=cD.

Nevertheless

    sum B'-4=4/5 < 6/5=lambda D'.                         (19)

Equivalently H=-2/5: singleton-root probability is 1/2, adjacent-pair
probability is 3/10, their reward totals are 5 and 1, and
H=(1/2)-3(3/10)=-2/5. So this cap-Nash prefix exits the literal
surplus chamber despite exact debt contraction and an ACTUAL origin.

The root support is minimal for this failed ledger implication: with
the same singleton totals, every singleton-supported root has H=q_i>=0;
all Continue has H=0. No minimality in the number of game players is
claimed.

This counterexample refutes all-root chamber preservation from passive
nonnegativity. It does not refute a favorable-root selection theorem, a
different chamber, or existence of a uniform payoff for this exact table.
The raw theorem proved in Sections 1--7 retains W>=1 and K>=0.

Other exact boundaries of the positive theorem are:

* K_i=0 is allowed. Its triple total is -3 and its charge relative to
  the baseline 4 is -7; the proof retains that negative charge explicitly
  in (15), rather than discarding it.
* Arbitrarily large finite P,W,K are allowed. The literal seed rate t
  decreases with the two W coordinates it uses. Compactness and all
  numerical bounds are table-by-table; no uniform rate over the unbounded
  raw class is claimed.
* G_i may be arbitrarily negative. The full response cap stays nonnegative
  by Never, though the compact reward box depends on the table.
* G_i=K_i is allowed. In particular, if equality holds for all i, all
  players Quit 0 is exact terminal Nash: withdrawing leaves precisely
  the same outsider triple reward K_i. The proof also handles mixed
  equality/strict cases via the sure-root diagonal exit.
* The raw constraints are sufficient, not necessary for uniform payoff
  existence. The negative-chamber example (18)--(19) is a failure of this
  preservation argument, not a positive terminal exploitability gap.

## 10. Source correspondence

The main proof uses the following existing checked semantic services.
Their hypotheses are finite player type, finite real reward data, and
the explicit membership/Nash premises indicated; no missing strategy-
production theorem is hidden in these citations.

* `quittingTerminalSemanticPair`, `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` provide the
  closure of actual prescribed-payoff/unrestricted-response pairs,
  compactness, actual approximants, and the continuous fixed-root action.
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies a FULL
  finite mixed Nash root for every real continuation vector B.
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean` give the
  exact cap and debt identities (3), including inactive players and sure
  hazards. The zero-Continue-mass diagonal exit is a direct consequence.
* `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` in
  `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`
  converts the constructed diagonal to one original fixed target against
  unrestricted unilateral behavioral replacements at all sufficiently
  long finite horizons.

The new raw-family mathematics is the literal seed (4)--(7), support
inequalities (9)--(11), nonnegative charge despite negative raw triple
charge (12)--(16), and the constrained-minimum argument supplying the
consumer's diagonal premise. These are not claimed implemented by the
generic semantic declarations. No published theorem is invoked for this
new raw argument beyond finite mixed Nash existence as provided above.

The bounded coverage comparisons use these precise tracked interfaces:

* `r0Degree_eq_sign_det_of_nonnegative_inverse` in
  `MathUE/LinearProgramming/NonnegativeInverseDegree.lean` and
  `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`;
  `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
* `QuittingResponseInvariantOnUnitCube` and
  `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`,
  and `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
  in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.
  These use the FULL residual, not a quotient inferred only from Gamma.
* `IsCommonQuittingPremiumLeaver` in
  `UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`;
  `HasProtectedParticipantPremiums` and `HasSupportSpecificQuittingLeavers`
  in `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`;
  and the weak consumer `exists_uniformEquilibriumPayoff_of_supportSpecific_weakLeave`
  in `UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversRewardClosure.lean`.
* `HasGlobalQuittingWeightedFloor` and `HasWeightedQuittingTrapLeavers` in
  `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`;
  `IsSupportwiseQuittingPremiumWeightCertificate` in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`;
  `IsSupportwiseBalancedQuittingPremiumTable` in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`;
  `exists_uniformEquilibriumPayoff_of_supportwiseBalance` in
  `UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`;
  and `HasProductLowQuittingPremium` in
  `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.
* `QuittingTrapChargeCoefficients` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`,
  `QuittingTrapChargeCoefficients.threshold_of_cardinality_four` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean`,
  and `HasBoxedQuittingNashCharges` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`.
* `quittingPersistentBaseNashSet` in
  `UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`;
  `WithdrawalFutureJoinRewardCertificate` and `WithdrawalFutureJoinKind`
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`;
  the full consumer in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`;
  and the capped-clock consumer in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockChildDeletionAdapter.lean`.
  The universal child-profile quantifier and literal joint-Never factor
  are essential to the zero-debt child falsifiers in Section 8.4.
* `PairedCycle.RawRegion` and
  `PairedCycle.RawRegion.eq_partner_of_singleton_lt` in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`;
  `PairedCycle.CrossedMatching.RawSource`, `WeakRawSource`, `InverseRawSource`
  and `ScheduledPairCapSource` in
  `UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`;
  `PairedCycle.BelowSingleton.RawFamily` in
  `UniformEquilibrium/Quitting/Cycles/BelowSingletonJointPhaseSource.lean`.
* `SignedFourCycleSingletonData` in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`
  and its `LargerTests` in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleLargerRewardAdapter.lean`;
  `CyclicChildJointPhase.RawTable` in
  `UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`.
* `exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign`
  in `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean`;
  `exists_uniformEquilibriumPayoff_of_weakJoiningAttractive_core` in
  `UniformEquilibrium/Quitting/Classification/Existence/JoiningAttractiveCoreRewardClosure.lean`;
  `exists_uniformEquilibriumPayoff_of_weakMixedSignTriple_core` in
  `UniformEquilibrium/Quitting/Classification/Existence/MixedSignTripleCoreRewardClosure.lean`.
  Their exact smaller-core hypotheses fail at greatest core I.

The additional finite-family comparisons in Section 8 state their
necessary mathematical raw guards explicitly. They need no temporary
notebook, external checker output, or other conference document as a
proof input. They deliberately do not classify broader conditional
consumers lacking those necessary raw hypotheses.

## Adapter and consumer

The actual-data adapter takes only P,W,K,G satisfying (1), defines the
sixty-coordinate reward function, constructs the literal independent
seed, and proves existence of a diagonal in that table's full terminal
semantic carrier. All caps are unrestricted response suprema. In
particular, it does not take any clock, cap vector, root, continuation,
invariant region, Nash selector, approximate equilibrium or target as an
assumed input.

The named diagonal consumer then outputs the original game's uniform-
equilibrium payoff. Actual approximating profiles belong to the original
game and deliver the same target as their full response caps approach.
No public correlation, reward-table limit, alternate game, or bounded
controller completeness assertion is used by this adapter.

## Lean handoff

Define the literal Fin4 reward family and a raw predicate consisting only
of P_i>=4, W_i(S)>=1, K_i>=0 and G_i<=K_i. A likely theorem shape is

    exists target,
      (quittingGame (monotonePassiveReward P W K G))
        .IsUniformEquilibriumPayoff none target.

The predicate must not assume a strategy, cap vector, invariant chamber,
favorable root, semantic diagonal or vanishing-error sequence. A narrow
proof can formalize these table-specific lemmas in order:

1. Nonnegative full caps from Never and the actual seed's exact U,B.
2. The full-support cap-sum odds inequality (10).
3. Proper-support low-cap witnesses and the explicit rectangular bounds
   (11), using the inequalities on the ACTUAL enlarged passive rewards.
4. The total-cap ledger (12), its bilinear charge (15), and all four
   positive corner expressions (16).
5. A nonzero full root at every positive chamber minimum, with a direct
   diagonal exit when a root has a sure hazard; otherwise same-chamber
   strict debt contraction.
6. The existing diagonal-to-uniform-payoff consumer.

Literal Fin4 support enumeration suffices. No new LCP theorem, continuous
Nash selector, recursive certificate hierarchy or speculative repository
refactor is required. Useful exact tests are the K=6 witness in Section 8,
K=0 and grand/triple equality boundaries, and the actual-origin failed
W>=0 relaxation in Section 9.

First check a new source with `lake env lean path/to/File.lean`, then its
named target with `LEAN_NUM_THREADS=1 lake --quiet --iofail build Module.Name`.
Apply the repository's trust, import-graph, axiom-audit and documentation
checks to the changed modules. These are handoff suggestions, not claims
that this raw adapter has been compiled or integrated.

## Scope and nonclaims

The result supplies one fixed uniform-equilibrium target for every table
in the full raw class (1), with all complete unilateral behavioral
replacements allowed. It does not settle arbitrary Fin4, arbitrary finite
quitting games, or the general finite stochastic-game proposition.

It does not produce an explicit numerical target, a convergence rate,
an exact terminal Nash profile for every input, or stationary/periodic
strategy-class completeness. The witness comparisons in Section 8 have
the bounded quantifiers stated there and make no all-behavior nonexistence
claim. The failed relaxation in Section 9 is an exact counterexample to
one chamber-invariance implication, not to uniform-equilibrium existence.

