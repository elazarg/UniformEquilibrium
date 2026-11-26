# Every positive global partial-Nash minimum has an incoming collision root

Owner: CODEX_OBSERVER_PATH.

Status: the incoming extraction is a complete ordinary mathematical proof
draft, awaiting independent review. Section 6 is an exact countercontrol;
the root coordinator independently checked the source and prefix invariant
in Sections 6.1--6.2 in the current research session. CODEX_PIVOT_REVIEW
independently checked the full-law path in Section 6.3. Sections 7--8 give
exact deletion identities and an all-END, positive-Never countercontrol;
Sections 6.3 and 7--8 passed the independent
[CODEX_PIVOT_REVIEW audit](../feedback/CODEX_OBSERVER_PATH__GLOBAL_MINIMUM_INCOMING_COLLISION__BY_CODEX_PIVOT_REVIEW.md).
Section 9 records the current strict-tail comparison and remaining gap.
None is a Fin4 closure. No Lean build or export is claimed.

Curation removed historical comparisons and a redundant review link.
The mathematical claims and the review scopes above are unchanged.

## 1. Question and result

Use the native four-player independent complete-clock model: own singleton,
live, and Never rewards are zero; all coalition rewards have absolute value
at most M, where M>=1. Let K be the compact closure of payoff/full-cap pairs
of actual absorbing profiles, and write d_i=B_i-U_i>=0. For a fixed pivot
p let

    C_p={X in K:d_i(X)=0 for i!=p},
    m=min_(X in C_p) d_p(X)>0.

Suppose X belongs to C_p, attains m, and satisfies

    B_i=U_i>0 for every observer i!=p,
    B_p>m, so U_p=B_p-m>0.                              (1)

These are exactly the remaining generic global sources in
[CODEX_EXPENSIVE_EXIT__ABSORBING_PARTIAL_NASH_MINIMUM.md](CODEX_EXPENSIVE_EXIT__ABSORBING_PARTIAL_NASH_MINIMUM.md).

**Incoming-root theorem.** There exist Y in K and a product root q such that

    X=prefix_q(Y),
    q is observer-Nash at the full cap B(Y),
    q has at least two active owners.                   (2)

The root has a quantitative activity lower bound. Put

    mu=min_(i!=p) B_i(X),       h=B_p(X)-m,
    delta=min(1/8,mu/(64M),h/(64M)).

One can require sum_i q_i>=delta. Every active observer i satisfies
Q_i(q)=B_i(X)>0. In particular, an actual collision payoff is needed in
the first nonvanishing layer of any realizing sequence.

If c(q)=product_i(1-q_i)>0, then Y belongs to C_p and

    d_p(Y)>=m,
    m=R_p(q;B(Y))+c(q)d_p(Y),
    R_p(q;B(Y))<=m(1-c(q)).                              (3)

If c(q)=0, one still has Y in K and observer Nash at B(Y), but no zero
observer-debt assertion is made about Y. Its pivot root regret is m.

The theorem does NOT say that Y is another minimum, that its caps are
nonnegative, or that q is a full Nash root. The incoming bound in (3) is
the reverse of the outgoing minimum bound. This distinction is essential.

## 2. Exact decomposition and a uniform conditional-tail bound

For a root let H_i=product_(j!=i)(1-q_j), c=product_i(1-q_i), and let
Q_i and P_i be its forced-Quit and passive nonempty-opponent payoffs.
For any actual continuation pair, or its compact limit,

    U'_i=q_i Q_i+(1-q_i)P_i+c U_i,
    B'_i=max(Q_i,P_i+H_i B_i),
    d'_i=R_i+c d_i,
    R_i=max(Q_i,C_i)-q_i Q_i-(1-q_i)C_i>=0,
    C_i=P_i+H_i B_i.                                    (4)

These full-cap recursions include every finite deadline and Never.

Choose actual absorbing independent laws with pairs X_n tending to X.
We may assume every finite conditional hazard is strictly below one.
Indeed, mix each private law with an arbitrarily small amount of one fixed
proper geometric law having positive mass at every finite date. This
changes each law by vanishing total variation, hence changes all prescribed
and response payoffs uniformly by a vanishing amount. Absorption remains:
an absorbing independent finite-player profile has at least one proper
private law, and mixing that law with a proper law preserves properness.
Every finite all-Continue history now has positive probability, and its
conditional tail is again an actual absorbing independent profile.

Let epsilon_n=sum_(i!=p)d_i(X_n), so epsilon_n tends to zero. Compactness
and the definition of m supply a function omega(t) tending to zero as
t decreases to zero such that

    Y in K and max_(i!=p)d_i(Y)<=t
        imply d_p(Y)>=m-omega(t).                       (5)

For example take the positive part of m minus the infimum over this compact
slice. If the asserted convergence failed, a compact subsequence would
give a point of C_p with pivot debt below m.

Iterating (4), a conditional tail reached with joint survival at least
3/4 has each observer debt at most 4 epsilon_n/3. Therefore every such
tail has pivot debt at least

    m-omega(4 epsilon_n/3).                             (6)

Estimate (6) uses the actual global C_p minimum and compactness. No positive
joint Never mass is assumed here.

## 3. Small roots cannot accumulate before the collision root

Write ell(q)=sum_i q_i. Consider any initial finite segment of a realizing
profile whose individual roots obey ell<delta and whose cumulative ell is
at most 2delta. Let s_k be joint survival before its kth root and s the
survival after the segment. Then

    s_k>=s>=1-2delta>=3/4.                              (7)

For all sufficiently large n, every output cap along this segment stays
close to B(X), and at every root the Continue endpoint is the cap. Here
is the direct bootstrap, which does not assume continuity of a best reply.
The zero own singleton gives |Q_i|<=M ell. Whenever the current output cap
exceeds Q_i, equation (4) forces it to equal C_i. The conditional tail cap
then differs from that output cap by at most 2M ell, since

    |P_i+H_i B_i-B_i|<=2M ell.

The total cap movement is at most 4M delta. Initial convergence to B(X)
and the definition of delta keep observer output caps above mu/2 and
pivot output caps above m+h/2, with enough strict slack to subtract every
|Q_i|<=M delta. Consequently, at each root,

    R_i=q_i(C_i-Q_i)>= (mu/2)q_i       for i!=p,
    R_p=q_p(C_p-Q_p)>= (m+h/2)q_p.                      (8)

For clarity, taking initial cap errors at most min(mu,h)/8 suffices:
4M delta<=min(mu,h)/16 and M delta<=min(mu,h)/64 leave
more than the stated mu/2 and h/2 margins.

Let A be the sum of all observer hazards in the segment. The observer
debt identity and (7)--(8) give the uniform estimate

    A<=8 epsilon_n/(3mu).                               (9)

Write P=sum_k s_k q_(k,p). Since 1-c(q_k)<=ell(q_k),

    P>=1-s-A.

Using (6) for the terminal conditional tail and iterating the pivot debt
identity now yields

    d_p(X_n)>= (m+h/2)P+s[m-omega(4 epsilon_n/3)]
             >= m+(h/2)(1-s)
                -(m+h/2)A-omega(4 epsilon_n/3).          (10)

The right-hand errors tend to zero uniformly over EVERY segment of the
specified type. Hence s tends uniformly to one. Because

    s=product_k product_i(1-q_(k,i))
      <=exp(-sum_k ell(q_k)),

their cumulative hazard sums tend uniformly to zero as well.

## 4. A macroscopic first root is forced and has output X

For each sufficiently large n, there must be a root with ell>=delta,
and its preceding cumulative hazard is less than delta. Otherwise, before
any such root the cumulative hazard first crosses delta through roots of
size below delta. That finite segment has cumulative hazard in
[delta,2delta), contradicting Section 3. If it never crosses delta and
there is never a large root, its joint survival remains positive, contrary
to absorption. More explicitly, roots of size below delta and a bounded
total hazard have a positive infinite product survival.

Let k_n be the first root with ell>=delta. The segment strictly before it
has cumulative hazard below delta. Section 3 therefore says that this
preceding cumulative hazard tends to zero. The payoff difference across
that segment is at most 2M times its total hazard; the cap difference has
the same bound by the Continue bootstrap. Thus the conditional pair
immediately BEFORE the root tends to X.

Take a compact subsequence on which q_(k_n) tends to q and its actual
absorbing conditional tail pair tends to Y in K. Continuity of (4) gives
X=prefix_q(Y), and ell(q)>=delta. For each observer the debt identity is

    0=R_i(q;B(Y))+c(q)d_i(Y).

Both terms are nonnegative. Hence q is observer-Nash. If c(q)>0, the
tail observer debts vanish and Y belongs to C_p. Its minimum property
then gives (3). When c(q)=0, (4) gives R_p=m directly.

It remains to exclude singleton support. A sole active observer has its
own Quit value zero. Observer Nash with positive Quit probability forces
its output cap to be zero, contradicting (1). If p alone is active with
probability one, its output payoff is zero, also contradicting (1). If p
alone is active with probability t in (0,1), the tail belongs to C_p and
its pivot cap equals B_p(X)>m. Therefore

    d_p(X)=t B_p(X)+(1-t)d_p(Y)
          >=t B_p(X)+(1-t)m>m,

a contradiction. At least two owners are active. Finally every active
observer's zero root regret implies its Quit endpoint equals its output
cap, whether it mixes or quits surely. This proves the remaining claim.

## 5. What this sharpens and what remains

The all-positive minimum cannot be realized merely by indefinitely
spreading all early hazards into smaller atoms. Its strict pivot margin
and positive observer values force a nonvanishing collision layer, whose
conditional output is the selected global minimum itself. This is a
producer from arbitrary realizing sequences, rather than an assumed
incoming-root interface or a fixed-calendar statement.

The produced tail can have larger pivot debt, and a sure limiting root
can erase observer debt in that tail. Neither case contradicts the minimum.
The concrete remaining question is whether these produced collision roots,
including the sure case, permit a full replacement preserving the three
observer best replies while lowering pivot debt. Local prefix contraction
alone does not establish that replacement.

The literal semantic formulas were checked against
`quittingTerminalSemanticPrefix` and
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`. The extraction,
compact conditional-tail estimate, and minimum argument above are ordinary
mathematics, not newly checked Lean results.

## 6. Exact control: every observer-Nash prefix remains trapped

This control shows that a positive one-pivot source, a macroscopic incoming
collision, root inertia, and all outgoing observer-Nash prefix-budget
inequalities do not replace GLOBAL minimizing provenance. The control is
solved by an actual absorbing equilibrium. It is not a positive-gap table.

Label the pivot 0 and the other players 1,2,3. For EVERY nonempty coalition
S, define the complete reward table by

    Z_0(S)=2 if 1 belongs to S and 0 does not,
           1 if both 0 and 1 belong to S,
           0 if 1 does not belong to S;

    Z_1(S)=1 if 0 belongs to S and 1 does not,
           2 if both 0 and 1 belong to S,
           0 if 0 does not belong to S;

    Z_j(S)=0 if j belongs to S,
           1 if j does not belong to S,      for j=2,3.

The presence of players 2 or 3 has no further effect on the first two
rows. In particular all four own singleton rewards are zero. Live and
Never rewards are zero. These rules specify all 60 coalition rewards,
including every higher coalition.

### 6.1 Actual positive source and its full caps

Let player 1 quit surely at date zero, let player 0 use the proper geometric
clock with conditional hazard 1/2 at every date, and let players 2,3 Never.
The profile absorbs at date zero and has

    U=(3/2,1,1,1),       B=(2,1,1,1),
    d=(1/2,0,0,0).                                    (11)

For player 0, waiting beyond date zero yields 2 and quitting immediately
yields 1, so its full cap is 2. For player 1, a pure deadline k>=0 gives

    Pr(T_0<k)+2 Pr(T_0=k)
      =1-2^(-k)+2*2^(-(k+1))=1.

Never also gives 1 because the pivot clock is proper. Every complete
response is a mixture of these deadlines and Never, so its full cap is 1.
Players 2 and 3 obtain 1 by Never and can never exceed 1. Thus (11) prices
the full response menus, including off-path future pivot hazards.

For q=(1/2,1,0,0), direct substitution into (4) gives

    prefix_q(X)=X.

The pivot root endpoints are Q_0=1 and C_0=2. Player 1 has equal root
endpoints Q_1=C_1=1, and players 2,3 strictly Continue. Thus q is an
incoming two-owner observer-Nash root, and its survival c is zero.

AllContinue is the unique full Nash root at continuation U. Players 2,3
strictly Continue there. If player 1 has hazard s, the pivot endpoints are

    Q_0=s,       C_0=2s+(1-s)(3/2)>s.

The pivot therefore Continues. Player 1 then also strictly Continues
because its own singleton is zero and its continuation is 1.

### 6.2 An invariant under every observer-Nash prefix

Consider the following subset of the actual absorbing closure:

    B_0=2,             U_0<=3/2,
    B_1=U_1=b>=1,
    B_j=U_j=1           for j=2,3.                     (12)

It contains X. Every observer-Nash root preserves (12). To verify this,
players 2,3 have Quit value zero and Continue value exactly 1, so their
hazards are zero. Let t=q_0 and s=q_1. The player-1 gap is

    Q_1-C_1=2t-[t+(1-t)b]=t-(1-t)b.

Its threshold is t_*=b/(b+1)>=1/2. Hence observer Nash requires s=0
when t<t_*, s=1 when t>t_*, and allows any s when t=t_*.

The pivot cap remains 2, since its endpoints are

    Q_0=s,       C_0=2s+(1-s)2=2.

Its payoff is

    U'_0=(1-s)(1-t)U_0+s(2-t).                         (13)

When s=0, this is at most 3/2. When s=1, observer Nash implies t>=1/2,
so it is again at most 3/2. At the mixing threshold, (13) is a convex
combination of these same two bounded values. Player 1's equal payoff
and cap is t+(1-t)b>=1 in its Continue case, and 2t>=1 whenever its
Quit probability is positive. Players 2,3 retain equal value 1.
This proves invariance.

Consequently EVERY finite word of observer-Nash prefixes attached to X
has pivot debt at least 1/2. Every compact limit of such words has the
same lower bound. In particular X satisfies all outgoing one-root minimum
inequalities R_0>= (1/2)(1-c), and no such prefix word or its limit can
lower its remaining debt. The obstruction includes sure roots, arbitrary
finite word lengths, and the complete response caps.

### 6.3 Full law changes escape the invariant

The game nevertheless has an absorbing exact equilibrium: let player 0
Never, player 1 quit surely at date zero, and players 2,3 Never. Its payoff
and full-cap vector is (2,0,1,1). Thus the actual global minimum over C_0
is zero. Source X is a prefix minimum, not a global minimum.

There is also a direct continuous full-law escape while the pivot clock
is fixed. Retain its geometric hazard 1/2. Let player 1 quit at date zero
with probability beta and Never with probability 1-beta; keep players
2,3 at Never. Every response of player 1 still has payoff 1 by the deadline
calculation above, so all observer debts remain zero. The profile absorbs
because the pivot clock is proper. Its pivot payoff and cap are

    U_0=(3/2)beta,       B_0=2beta,
    d_0=beta/2.                                        (14)

For the cap, waiting beyond date zero yields 2beta, quitting immediately
yields beta, and on the branch where player 1 Never no pivot action can
obtain a nonzero reward. Thus (14) controls the entire response menu.
Decreasing beta from one to zero gives strictly smaller pivot debt within
C_0, reaching another actual absorbing equilibrium.

The full-law path deletes part of an observer's existing atom; prefixing
cannot perform that deletion. This is the precise missing freedom in the
prefix-only approach. A successful argument at a genuine global minimum
must exploit its full-law minimizing property or additional source data;
the incoming collision and local prefix budgets alone are insufficient.

## 7. Exact full-law deletion criteria and the three-observer constraint

This section concerns ACTUAL independent complete laws. It does not apply
a law operation to a compactified tuple without specifying common realizing
laws and the additional response data. Fix a partial-Nash profile sigma
with d_i=0 for every observer, and replace observer k's law by

    sigma_k^lambda=(1-lambda)sigma_k+lambda Never,
    0<=lambda<=1.

If a different owner is proper, all these profiles remain absorbing. If k
is the only proper owner, any positive lambda can destroy absorption. The
identities below still hold on the full all-profile carrier, but membership
in the absorbing carrier must be checked separately.

For an unaffected observer i and a pure complete response a, let V_i(a)
be its old response payoff and V_i^k(a) its response payoff when k Never.
Let U_i^k be its prescribed payoff in that latter profile. Put

    g_i(a)=B_i-V_i(a)>=0,
    h_i(a)=V_i^k(a)-U_i^k.

Independence and linearity in k's law give the EXACT debt formula

    d_i(lambda)=sup_a[-(1-lambda)g_i(a)+lambda h_i(a)].  (15)

Thus this observer remains exact precisely when

    lambda h_i(a)<=(1-lambda)g_i(a) for EVERY response a. (16)

This is the full finite/Never response menu. The moved observer k has
unchanged opponents and unchanged cap, so

    d_k(lambda)=lambda[B_k-V_k(Never)].                (17)

In particular a positive deletion can preserve k only if Never was already
its best reply.

The right derivative of (15) at zero is

    d_i'(0+)=max_(a in BR_i) h_i(a).                   (18)

Here BR_i is the complete old best-response set. To justify the maximum
and derivative, pure responses are finite deadlines and Never. Their
payoffs converge to the Never payoff as the deadline tends to infinity:
the finite opposing quitting mass after the deadline tends to zero,
and quitting alone against opponents who all Never gives the own singleton
zero. The same holds after deleting k. Thus g_i and h_i are continuous on
the one-point compactification of the natural dates, and the elementary
compact maximum derivative applies. The prescribed old law is supported
on BR_i and has average h_i zero, so the maximum in (18) is nonnegative.

Zero derivative does not imply a feasible interval in (16). Ratios
h_i(a)/g_i(a) for almost-optimal responses can be unbounded. More directly,
a feasible positive lambda exists precisely when h_i<=0 on g_i=0 and
the positive ratios h_i/g_i on g_i>0 have finite supremum; the corresponding
upper bound is lambda<=1/(1+sup h_i^+/g_i). This criterion is also to be
combined with (17) and absorption preservation.

For the pivot, write d=d_p and BR_p for its old best responses. Its debt
is convex in lambda, with exact right derivative

    d_p'(0+)=max_(a in BR_p)[V_p^k(a)-U_p^k-d].          (19)

If the objective is J=d_p+r nu and every original Never mass is positive,
the additional derivative is

    (r nu)'=r nu(1-N_k)/N_k.

These formulas identify actual feasible directions; they do not assert
that any nonzero one exists at a global constrained minimum.

### 7.1 Positive original Never makes the END constraints explicit

Suppose all three observers have positive original Never mass and zero
debt, so their caps equal their literal Never values e_i. Simultaneously
thin their complete laws by parameters x_i:

    sigma_i(x_i)=(1-x_i)sigma_i+x_i Never.

Positive original Never permits both signs of small x_i whenever the law
also has positive finite mass. Write e_i(x)-U_i(x) for observer i's END
rent. With the pivot law fixed, it has the exact form

    e_i(x)-U_i(x)
      =(1-x_i)[A_ij x_j+A_ik x_k+C_i x_j x_k],          (20)

where {i,j,k} are the observers and

    A_ij=e_i(sigma^(j Never))-U_i(sigma^(j Never)),

while C_i is the usual two-variable inclusion-exclusion coefficient for
the same END rent with i's original law retained. Equation (20) follows
because moving i itself toward Never multiplies its END rent by 1-x_i,
and the remaining two law coordinates enter multilinearly.

As long as each thinned observer retains positive Never mass, exactness
requires these three END rents to vanish, as well as all full-response
inequalities. If the zero-diagonal matrix A is invertible, the implicit
function theorem makes x=0 locally isolated among these END-equality
solutions. Even a nonzero kernel is insufficient: the next control has
a common-thinning kernel, but its quadratic terms prevent EVERY nonzero
thinning in the entire cube.

## 8. Positive Never and all ENDs do not supply any thinning move

This is a second control on the FULL all-profile carrier, designed for
the Never-penalized source rather than the absorbing source of Section 6.
It is an actual native table and profile. It is not asserted to be a
global constrained minimum, and its unrestricted absorbing gap is zero.

Index observers 1,2,3 cyclically, and put

    G = [ 0 -1  2 ]
        [ 2  0 -1 ]
        [-1  2  0 ].

Thus G_i,next(i)=-1 and G_i,prev(i)=2. Specify every nonempty coalition
as follows:

    Z_0(S)=2 if 0 is absent and some observer is present,
           1 if 0 is present with some observer,
           0 if S={0};

    for observer i absent from S:
      Z_i(S)=G_ij if exactly one other observer j belongs to S;
      Z_i(S)=2 if both other observers belong to S;
      Z_i({0})=-1;

    for observer i belonging to S:
      Z_i(S)=5 if S={0,1,2,3};
      Z_i(S)=0 otherwise.

The first two passive rules do not depend on whether the pivot belongs
to S. These cases are disjoint and exhaustive. All own singletons are
zero. The full singleton matrix and the relevant inverse data are

    Gamma = [ 0  2  2  2 ]
            [-1  0 -1  2 ]
            [-1  2  0 -1 ]
            [-1 -1  2  0 ],

    G^(-1)=(1/7)[2 4 1; 1 2 4; 4 1 2] >>0,
    Gamma^(-1)e_0=(1/6,1/6,1/6,1/6) >>0.              (21)

Every singleton column has a negative entry. Gamma is invertible: G is
invertible, G times the all-ones vector is the all-ones vector, and the
Schur complement of G is 6. Thus this control also satisfies the positive
inverse pivot-column condition; it does not merely exploit a nonnegative
pivot singleton column.

Let EVERY player independently use (Quit at date zero + Never)/2. Then

    N_i=1/2 for every i,       nu=1/16,
    U_0=21/16,                B_0=e_0=7/4,
    U_i=B_i=e_i=5/8 for i=1,2,3,
    d_0=7/16,                 d_observers=0.           (22)

Indeed the pivot's Never payoff is twice the probability 7/8 that some
observer quits at zero. Quitting at zero gives half that value. For
observer i, the two singleton-observer events each have probability 1/4
and contribute (-1+2)/4. Both other observers quit with probability 1/4
and contribute 2/4. Only the pivot quits with probability 1/8 and
contributes -1/8. Their sum is 5/8. Its Quit-at-zero payoff is also 5/8,
because it earns five precisely when all three opponents quit. Every
strictly later deadline has exactly the Never payoff: all opposing finite
mass is at zero, and its own singleton is zero. Thus all FULL caps in
(22) are literal END values.

AllContinue is the unique full root at U-r nu e_0 whenever 0<r<21.
Its pivot continuation is positive. With A the probability that some
observer quits in a candidate root, the pivot Quit endpoint is A and its
Continue endpoint is 2A+(1-A)(21-r)/16>A. The pivot therefore Continues.
The grand coalition now cannot occur, so every observer Quit payoff is
zero. There is no remaining nonzero observer root, as the following exact
check shows. If observer j quits surely, its cyclic successor i has Continue
value 2 regardless of the third observer's action, so i Continues. Then
j's Continue value is a convex combination of its positive continuation
and its positive singleton entry 2, contradicting j's sure Quit. Thus all
observer hazards are below one. One active observer faces its positive
continuation, and two active observers include one with a positive
singleton entry against its active opponent; neither support is possible.
For full support, use odds z_i=q_i/(1-q_i)>0. Every active Continue value,
after dividing by H_i, is

    w_i+(Gz)_i+2 z_next(i) z_prev(i).

Nash would require all three to be nonpositive, hence Gz<<0. The strictly
positive inverse in (21) would force z<<0. This final contradiction proves
inertia, including every sure-root case.

Now fix the pivot law and apply arbitrary independent deletions to the
three observer laws. Their date-zero masses a_i can range over the ENTIRE
cube [0,1/2]^3, with the rest of each law at Never. Every observer still
has positive Never mass. Its Quit-at-zero minus Never gap is

    F_i(a_next,a_prev)
      =2a_next a_prev+a_next/2-5a_prev/2+1/2.           (23)

All later deadlines equal Never, so this is the full-response comparison.
If a_i>0, exactness requires F_i=0; if a_i=0 it requires F_i<=0.

If a_i>0, its indifference equation forces a_prev>0: setting a_prev=0
makes F_i=(a_next+1)/2>0. A single positive atom therefore forces all
three atoms to be positive. Their indifference equations then give

    a_prev=f(a_next),       f(a)=(a+1)/(5-4a),
    f(a)-a=(2a-1)^2/(5-4a)>=0,

with equality only at a=1/2. Cycling the three inequalities forces all
atoms to equal 1/2. If all atoms are zero instead, every F_i is 1/2>0,
so Never is not optimal. Consequently

    the original a=(1/2,1/2,1/2) is the ONLY observer-Nash
    profile in its entire independent thinning cube.   (24)

This excludes simultaneous complete deletion as well as every arbitrarily
small thinning direction. It is stronger than merely a positive derivative
on individual coordinate rays.

For comparison with (20), use a_i=(1-x_i)/2. The END rents are

    e_i-U_i=(1-x_i)[3(x_next-x_prev)/8
                              -x_next x_prev/4].      (25)

The linear END matrix has rank two and kernel spanned by the all-ones
vector. Thus common thinning cancels EVERY first-order observer END rent.
Nevertheless, when x_1=x_2=x_3=x>0 the exact Quit-minus-Never gap is x^2/2,
and the observer debts are

    d_i=x^2(1+x)/4>0.                                 (26)

First-order cap cancellation does not lift to a feasible curve. In fact
the rational-cycle argument above also excludes sufficiently small
bidirectional reweightings: f(a)-a remains nonnegative on a neighborhood
of 1/2 with denominator positive, with equality only at 1/2.

The game nevertheless has an explicit absorbing exact equilibrium. Let
the pivot Never. At chronological dates 0,1,2,3,... the sole eligible
quitter is observer 3,1,2,3,1,2,..., with hazard 1/2 on its own turns;
the other observers Continue. Joint survival after n dates is 2^(-n),
so absorption is sure. The observer continuation-payoff vectors cycle
e_1,e_2,e_3,e_1,... in chronological order. At the e_1 state, for example,
owner 3 moves with probability 1/2 and the next continuation is e_2.
The Continue values are

    (1/2)e_2+(1/2)G_column3=e_1.

The mover's value is zero; every observer's Quit value is zero because
the pivot Never. Hence every root is Nash, and all continuation values
are nonnegative. An observer deviation leaves the other two observers'
hazards intact, so its uniform survival bound after n dates is at most
2^(-floor(2n/3)). Iterating the full-cap recursion with this vanishing
tail bound proves the displayed values are the complete caps.
The pivot receives two at absorption, while joining any observer yields
only one and quitting alone yields zero. Its full cap and payoff are two.
Thus the initial payoff/cap vector is (2,1,0,0), all debts are zero, and
nu=0. The global value of d_0+r nu is therefore zero for every r>0.

The control proves no obstruction to a genuine GLOBAL comparison on C.
It shows precisely why all-END activity, positive original Never, root
inertia, and three observer variables do not by themselves supply a
deletion or infinitesimal reweighting consumer. The full global minimum
provenance must enter elsewhere.

## 9. The strict incoming tail and the exact substitution objective

The [sure-root and proper-limit realization note](CODEX_PIVOT_REVIEW__SURE_ROOT_AND_PROPER_LIMIT_REALIZATION.md)
now proves a stronger global reduction. Starting at any nonrealized
positive global C_p minimum, it reaches a nonrealized minimum X_* such
that EVERY nonzero incoming factorization X_*=prefix_q(Y) has

    c(q)>0,       Y in C_p,       d_p(Y)>=m+kappa

for one fixed kappa>0. The root's activity is automatically bounded
away from zero. Its probability of continuation is also bounded away
from zero, because a sure root would actually realize X_*. Infinite
minimum-to-minimum incoming chains have already been excluded by an
actual realization argument. Merely requesting another incoming minimum
therefore does not advance this remaining case.

There is an exact comparison at each of these tails. Fix q and set

    C(Y)={Z in C_p:B_i(Z)=B_i(Y) for every i!=p}.

For every Z in C(Y), the same root remains observer-Nash and its
prefixed observer payoffs and caps equal those of X_*. Global minimality
therefore implies

    max(Q_p,P_p+H_p B_p(Z))-c U_p(Z)
      >= max(Q_p,P_p+H_p B_p(Y))-c U_p(Y).             (27)

The omitted prescribed head payoff is independent of Z. Thus Y is a
GLOBAL minimum of this explicit piecewise affine pivot objective on its
fixed-observer-cap slice, even though its pivot debt is strictly above m.
This is obtained directly from prefix closure of K and the complete-cap
recursion; it does not treat the incoming tail as a global C_p minimum.

For example, let Z be any global C_p minimum with these same observer
caps. It cannot satisfy both

    B_p(Z)<=B_p(Y),       U_p(Z)>=U_p(Y).              (28)

Indeed, (28) makes the prefixed pivot cap no larger and its payoff no
smaller. The new pivot debt is at most m; global minimality makes it
exactly m. Since both changes have the helpful sign, equality of the
debt forces both the prefixed cap and payoff to be unchanged. All other
coordinates were already unchanged, giving the forbidden nonzero
factorization X_*=prefix_q(Z) with minimum tail Z. This also covers the
case in which the pivot Quit cap hides a strict decrease in the tail
cap: the output is then unchanged, which still contradicts terminality.

This comparison identifies the unresolved operation; it is not a new
consumer. A full-law replacement has to move the observer-cap vector,
or supply a point contradicting the fixed-cap slice minimum (27).
Replacing Y by an unrelated lower-debt profile changes the three
observer continuation endpoints and need not preserve a single one of
their zero debts. The deletion controls in Sections 6--8 show why local
thinning or first-order cancellation alone cannot fill that gap. No
complete strict-tail surgery has been obtained here.
