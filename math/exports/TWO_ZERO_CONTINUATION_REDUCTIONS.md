# Two-zero continuations: a uniform incoming rule and a cap-preserving global return

## Exact statement and conjecture-facing change

Four players independently choose complete stopping laws on the natural dates
and Never. The first nonempty quitting coalition S pays a finite vector Z(S);
AllNever and live play pay zero. Native own singleton rewards are Z_i({i})=0.
Every unilateral behavioral replacement is allowed. Set M=max(1,max|Z_l(S)|).
Write U for prescribed payoff, B for the full response supremum, e for the
pure-Never response, and N
for the ORIGINAL marginal Never probabilities. Let H be the compact closure
of these actual augmented tuples. Fix a pivot p and put

    d=B-U, nu=product_l N_l, C={X in H:d_l(X)=0 for l!=p},
    J_r=d_p+r nu, A=inf{sum_l d_l(P):P actual, nu(P)=0}.

ALL-END means B=e. Define Gamma_ab=Z_a({b}) and J_ab=Z_a({a,b}) for a!=b,
with zero matrix diagonals. The scalar objective J_r and pair reward J_ab
are distinguished by their subscripts.

Assume the raw source conditions

    A>0, Gamma invertible, Gamma^(-1) e_p>0 coordinatewise.       (S)

Here e_p in the matrix expression is a coordinate unit vector. For EVERY
0<r<A, a minimum Y of J_r on C exists, has positive original Never and is
ALL-END. If Y is nonrealized, it admits a representation Y=Phi_P(Q) by an
ACTUAL positive-Never head P and an endpoint Q in C with positive original
Never, B(Q)=e(Q)>=0, at least one zero observer cap, and at least one positive
cap. The representation is the limit of finite-prefix maps; it never plays
Q after an infinite calendar. It can be selected with the following further
restrictions on its two-zero cases.

1. If B_p(Q)=B_i(Q)=0 and the other two caps are positive, then at least one
   of the raw inequalities

       min(0,Gamma_ip)<=J_ip<=max(0,Gamma_ip),
       min(0,Gamma_pi)<=J_pi<=max(0,Gamma_pi)                    (M)

   fails. The proof produces an exact incoming word with at most TEN roots
   whenever the two other observer caps are bounded below. Its positive
   activity bound is uniform with no restriction on the signs of B_p,B_i.

2. If two OBSERVERS i,j have zero caps and the pivot p and remaining observer
   k have positive caps, the finite negative-pair return test in Section 7
   cannot produce B_p'<=B_p and U_p'>=U_p. The test consists of raw
   sign inequalities, one rationally selected parameter, one entry-positivity
   test, and eight bilinear-corner comparisons. It returns all three observer caps
   EXACTLY and strictly reduces original Never. Such a comparison improves
   the global objective through EVERY positive-survival head, independently
   of its cap constraints or pivot obstacle. The more general obstacle test
   in Section 8 supplies a further sufficient exclusion.

The second exclusion is nonempty on a relatively open region of the admissible
raw table and two-zero annotation data. Its comparison is a compact limit of
increasingly long finite product prefixes, not a finite incoming word.
Its exact rational example has no nonzero finite
incoming word and has an actual head that pins the positive observer cap.
A nonlinear cap return succeeds even though every sufficiently small
nonzero move along the same curve changes that pinned cap. Its example game
has an absorbing equilibrium; it is not a positive-gap game.

These are reductions of the selected global source, not a new raw-table UE
class or a solution of all two-zero cases. Actual minima, other zero-face
configurations, and endpoints failing the nonzero cap return tests remain open.
The inherited endpoint is never assumed to minimize J_r by itself.

All strategic objects needed for the reductions are produced below. The
source is selected from (S); incoming roots come from actual approximants;
the competing reset is given by explicit independent product roots. The
reset recurrence is elementary two-player clock algebra; the contribution
is its exact return to a pinned cap, full-deviation verification, and global
consumer. No separately supplied repair direction or favorable controller
is assumed. All results here are ordinary mathematics, not new Lean checks.

## 1. Behavioral semantics, root maps, and compact comparison operations

Before absorption there is one live public history at each date. Sampling
private randomization in advance expresses a behavioral replacement as a
mixture of deterministic deadlines and Never. Thus B prices every unilateral
behavioral deviation. No public lottery or correlation device is used.

For a product root q, put H_l(q)=product_(a!=l)(1-q_a), c(q)=product_a(1-q_a).
Let Q_l(q) be forced-Quit payoff and P_l(q) the passive absorbing contribution
when l Continues. For an actual tail, and hence on H by continuity,

    U'_l=q_l Q_l+(1-q_l)P_l+c U_l,
    B'_l=max(Q_l,P_l+H_l B_l),
    e'_l=P_l+H_l e_l, N'_l=(1-q_l)N_l.                         (1)

The nonnegative root regret R_l satisfies d'_l=R_l+c d_l. Also
B'_l-e'_l>=H_l(B_l-e_l)>=0. Consequently positive-survival prefixes pass
zero observer debts and ALL-END to every descendant.

Changing independent complete laws on a coupling event of probability eta
changes every prescribed payoff, Never offer, and every pure response payoff
by at most 2M eta. Taking suprema gives the same full-cap bound. Finite-tail
censoring therefore approximates actual laws in all augmented coordinates.
The carrier H is a closed bounded subset of a finite-dimensional Euclidean
space, hence compact. The set C is closed; it contains AllNever.

For X,T in H, the retained-query graft is also in H and obeys

    U_l(new)=U_l(X)+nu(X)U_l(T),
    B_l(new)=max(B_l(X),e_l(X)+h_l(X)B_l(T)),
    e_l(new)=e_l(X)+h_l(X)e_l(T),
    N_l(new)=N_l(X)N_l(T), h_l(X)=product_(a!=l)N_a(X).         (2)

To prove this, first truncate an actual old law, censoring only its vanishing
finite tail to its own Never mass. Append an empty boundary query and an
actual tail at later natural dates. Every old query is retained; the empty
query equals old e_l<=B_l. Every new response has old e_l plus h_l times its
tail response. This proves(2), including the full maximum. Coupling and a
diagonal approximation extend it to arbitrary X,T in H. This construction
uses only finite concatenations and limits, not post-infinite play.

## 2. Production of the subcritical ALL-END source

Move a smallest original Never mass to one finite date. The resulting actual
profile absorbs surely. The moved owner's payoff changes by at most 2M N_l
and its cap is unchanged; each other payoff and cap changes by at most
2M N_l. Since min N_l<=nu^(1/4), on actual laws and by continuity on H,

    A <= sum_l d_l+14M nu^(1/4).                              (3)

For r>=0 put f(r)=min_C J_r. Compactness gives each minimum. For fixed r>0 write mu=f(r). AllNever gives mu<=r.
If 0<r<A, a zero minimum would have both d_p=0 and nu=0, contradicting(3).
Thus 0<mu<=r<A, and every minimum has

    nu >= ((A-r)/(14M))^4 > 0.                              (4)

In particular all original marginal Never coordinates are positive.

At a minimizer Y, any finite Nash root for continuation B(Y)-a e_p, a>=0,
is observer-Nash also at B(Y). Its pivot root regret at B(Y) is at most
a q_p H_p: increasing that one Continue endpoint by a H_p can increase the
pivot regret by at most the pivot Quit weight times this amount. Formula(1)
and global minimality give

    mu(1-c(q)) <= a q_p H_p.                                (5)

Finite-game mixed Nash existence supplies such a product root. If a<mu,
then 1-c(q)>=q_p H_p makes(5) possible only for q=0. AllContinue being Nash
at that continuation forces B_l(Y)>=0 for observers and B_p(Y)>=a. Letting
a increase to mu yields B_p(Y)>=mu>0. No stronger pivot margin is needed.

For an actual law, d_l>=N_l(B_l-e_l), by separating the owner's Never draw
from its finite draws. This inequality passes to H. Hence every observer
at Y is END-optimal. To establish pivot END-optimality use(S).
Put v=Gamma^(-1)e_p, S=sum_l v_l and k=S-v_p>0. Independent discrete clocks with hazards
1-exp(-v_l Delta), for floor(T/Delta) dates, have a compact limit Q_T with

    U_l(Q_T)=B_l(Q_T)=e_l(Q_T)=0   (l!=p),
    U_p(Q_T)=(1-exp(-ST))/S=:u(T)>0,
    B_p(Q_T)=e_p(Q_T)=(1-exp(-kT))/k=:b(T),
    N_l(Q_T)=exp(-v_l T).                                     (6)

Here T>0 and the final small interval can be adjusted to give total length T.
To check the complete cap, a finite response at time y tends uniformly to
(Gamma v)_l integral_0^y exp(-(S-v_l)t)dt. Collision error over the entire
profile and the collision error of any forced query are O(Delta), uniformly
in its chosen date. Arbitrary bounded nonsingleton rewards therefore vanish
from the limit. Prescribed payoffs use the analogous integral with rate S.
Since Gamma v=e_p, (6) follows; Never is the endpoint y=T. These are limits
of actual discrete profiles, not a new strategy space.

Graft Q_T onto Y using(2). The observers' caps and payoffs are unchanged.
If B_p(Y)>e_p(Y), small T leaves the pivot cap unchanged, but increases
U_p by nu(Y)u(T)>0 and decreases r nu by
r nu(Y)(1-exp(-ST))>0. This contradicts minimality. Thus Y is ALL-END.
Every strategic feature of the selected minimum used below is now produced.

A fact needed later is strict increase below A: if 0<=a<b and f(b)<A,
any minimizer Z_b at b has nu(Z_b)>0 by(3), and

    f(a)<=f(b)-(b-a)nu(Z_b)<f(b).                            (7)

## 3. Two elementary incoming rules

These rules concern arbitrary points X in C that are ALL-END with positive
original Never; they do not assume X minimizes anything.

If some B_l(X)=-z<0, extract the first root q and a tail T from actual
approximants. Formula(1) gives X=Phi_q(T), and
B_l(X)>=Q_l(q)>=-M sum_a q_a forces sum_a q_a>=z/M. Positive original Never
makes the root nonsure. The debt and END-gap recursions pass C and ALL-END
to T. This is the negative-cap rule.

If every observer cap is positive, set b=min_observer B_l(X)>0 and

delta=min(1/8,b/(64M)). Any positive observer cap supplies the crossing:
B_l<=M Pr(some opponent has a finite draw)<=M times total root activity.
Thus actual approximants have activity at least b/(2M). Take the first
activity crossing described in Section 4 below. In its small preliminary head all observer Continue comparisons
have gap at least b/4, so their total head hazard tends to zero by the
nonnegative debt recursion. Delete all their head activity by the coupling
bound. Only p acts in the resulting head, with finite mass f<2delta.

If that head is nonempty, compress it to the one solo-pivot root f e_p.
This preserves U,e,N. Each positive observer cap is its through-head offer;
the compressed Quit offer is bounded by Mf<2M delta<b/2, so its cap is
preserved too. The pivot cap in both heads is exactly max(0,B_p(tail)),
since every head pivot deadline pays its own singleton zero. Thus its cap
is preserved even when the limiting f is zero: retain that zero root as
an actual finite query. If the original head was empty, omit this root.
Take a subsequence distinguishing these cases; do not silently pad words.

A cumulative crossing has f>=delta/2 in the limit. An early macroscopic
crossing retains its extra root with activity at least delta. Extracting
this optional root and its tail gives an exact word of at most two roots
and total activity at least delta/2. Formula(1) passes C, ALL-END and all
positive original Never coordinates to its descendants. This is the
all-positive-observer rule.

## 4. Uniform incoming words with two protected observer caps

Use the model of Section 1. Fix pivot p and observer i;
let j,k be the other two observers. Let H be the compact closure of actual
independent stopping-law tuples (U,B,e,N), where B is the full unilateral
behavioral cap and N records original marginal Never masses. Let C impose
B_l=U_l for l != p. Assume the RAW pair inequalities

    J_ip lies between 0 and Gamma_ip,
    J_pi lies between 0 and Gamma_pi.                    (M)

where Gamma_ab=Z_a({b}) and J_ab=Z_a({a,b}). Set M0=max(1,max|Z_l(D)|).
For every X in C with B=e, all N_l>0 and

    B_j(X), B_k(X) >= b > 0,

there is an exact incoming word of at most TEN literal product roots,
followed by a point T in C, preserving all augmented coordinates, with

    total root activity >= delta/2,
    delta=min(1/8,b/(64M0)).                             (1)

Every root is nonsure, every intermediate point is ALL-END and has positive
original Never. There is NO sign or smallness requirement on B_p or B_i.
In particular (1) is uniform near B_p=B_i=0 from either side.

### 4.1. First activity crossing and deletion

Take actual tuples X_n -> X with positive original marginal Never. Their
conditional hazards exist and are all <1. For large n, B_j(X_n)>=7b/8.
A native forced deadline pays zero unless some opponent has a finite draw,
so B_j<=M0 Pr(some opponent has a finite draw). Thus the total root activity
is at least b/(2M0), and there is a finite crossing of delta.

Stop at the first date whose own activity is >=delta or whose cumulative
activity reaches delta. If that root is macroscopic, retain it separately
and let H_n be its prior head, of activity <delta. Otherwise include the
crossing date in H_n; its total activity is in [delta,2delta) and every
root in H_n has activity <delta.

On H_n the j,k caps remain above b/2, and Continue is their cap branch.
At each head root the forced-Quit offer has absolute value <=M0 delta.
While Continue is the cap branch, the next conditional cap differs by at
most 2M0 times the current root activity. The cumulative drift is less
than 4M0 delta<=b/16, so a first-failure argument closes this bootstrap.
The Quit-to-Continue gap is at least b/4 throughout the head. Joint survival
is at least 1-2delta>=3/4. The nonnegative root-debt decomposition gives

    sum_(t in H_n)(q_tj+q_tk)
       <= 8(d_j(X_n)+d_k(X_n))/b -> 0.                 (2)

Delete the j,k hazards on H_n, leaving the calendar and every tail law
unchanged. Coupling all independent draws changes every prescribed and
pure response payoff by at most 2M0 times the sum in (2), uniformly over
responses, hence changes full caps by the same bound. U,e,N are controlled
too. The modified actual tuples still tend to X. Their head now has only
p and i active, with total marginal finite mass f+g<=2delta.

### 4.2. Exact finite compression preserving both unprotected caps

Consider any nonempty finite two-owner head on dates 1,...,m, followed by
any fixed actual tail. Write its ABSOLUTE finite atom probabilities as
alpha_t for p and beta_t for i. Set

    f=sum alpha_t, g=sum beta_t,
    A_t=sum_(u<t) alpha_u,
    L=sum beta_t A_t, c=sum alpha_t beta_t.             (3)

Its first-coalition probabilities are

    first={p}: (1-g)f+L,
    first={i}: g-L-c,
    first={p,i}: c,
    no head quit: (1-f)(1-g).                          (4)

The head Never contribution for row i is Gamma_ip f, and for row p it is
Gamma_pi g. For either outside row it is its expected first-coalition
reward from (4). Consequently preserving f,g,L,c preserves all head
prescribed payoffs, Never contributions and original marginal survivals.

A pure deadline of i at head date t has payoff

    V_i(t)=Gamma_ip A_t+J_ip alpha_t.                  (5)

Condition (M) makes this deadline sequence monotone, with direction
controlled by the sign of Gamma_ip:

    V_i(t+1)-V_i(t)
      =(Gamma_ip-J_ip)alpha_t+J_ip alpha_(t+1).          (6)

Both coefficients are nonnegative when Gamma_ip>=0 and nonpositive when
Gamma_ip<=0. Likewise p's deadline sequence is monotone. Hence its maximum
is attained at one of the OLD FIRST AND LAST head dates, 1 and m. This also
covers a constant sequence and zero atom probabilities at either end. The
four endpoint offers are

    V_i(1)=J_ip alpha_1,
    V_i(m)=Gamma_ip(f-alpha_m)+J_ip alpha_m,
    V_p(1)=J_pi beta_1,
    V_p(m)=Gamma_pi(g-beta_m)+J_pi beta_m.               (7)

Each full cap is the maximum of these two head offers and its through-head
conditional tail cap. This holds for arbitrary signed tail caps.

If m=1 leave the head unchanged. Otherwise keep dates 1 and m and their i
atoms beta_1,beta_m fixed. If g-beta_1-beta_m>0, apply the ordinary plane
Caratheodory theorem to the weighted mean of (A_t,alpha_t), 1<t<m, with
weights beta_t/(g-beta_1-beta_m). Replace i's interior atoms by atoms on at
most THREE of those OLD dates, preserving their total mass and their two
moments. If the interior mass is zero no selected interior dates are needed.
Thus g,L,c,beta_1,beta_m are preserved. Leave p's law unchanged for this step.

There are at most FIVE retained special dates: the selected interior i dates
and the mandatory old first and last dates. Between successive special dates
are at most FOUR blocks, each containing only p atoms. Coalesce each nonempty
block into its LAST old p-support date, preserving its total absolute p mass.
Keep exactly these block dates and all special dates, delete every other date,
and reindex consecutively. The old first and last dates are retained even if
they have zero hazards. There are no blocks before or after these endpoints.

This has at most NINE head dates. At every retained i date, its p cumulative
mass A_t and same-date atom alpha_t are unchanged. Hence L,c remain unchanged.
The old endpoint dates remain first and last, and all four endpoint atoms
alpha_1,beta_1,alpha_m,beta_m are unchanged. Therefore (7) is unchanged.
The new deadline sequences are monotone by (M), so BOTH p/i full caps remain
exactly unchanged. Neither cap need be positive, and the original head need
not be END-optimal.

The outside rows j,k have full caps equal to their through-head tail options
whenever their caps exceed M0(f+g): every head deadline is bounded by that
quantity, because it pays zero when no opponent makes a finite head draw.
Those tail options are preserved by (4) and the marginal survivals. In the
application, outside caps are b-o(1), whereas M0(f+g)<=2M0 delta<=b/32.
Therefore all four caps, all U,e,N coordinates are preserved EXACTLY by
this compression for all sufficiently large n.

The head may originally have dates where both p/i atoms vanish. Retaining
both old endpoint query dates is necessary: they record the genuine endpoint
offers in (7), not newly inserted queries. An originally empty head is omitted
entirely. No padding with arbitrary zero roots is used.

### 4.3. Exact extraction and activity bound

Apply Section 4.2 to each modified head. Pass to a subsequence with a fixed
number of retained dates, and a fixed crossing case. Compactness extracts
the at most nine root hazards and their conditional augmented tails. In the
macroscopic case also extract the retained extra root and its actual tail.
The compressed actual tuples tend to X, so continuity of literal root maps
gives the exact full augmented incoming identity. The word has at most ten
roots.

In a cumulative crossing, the surviving p/i hazard sum is >=delta-o(1).
Every original head marginal survival is >=1-2delta, so

    f+g >= (1-2delta)(sum_head q_tp+q_ti)
         >=3delta/4-o(1).

Any head realizing these exact marginal finite masses has total hazard at
least f+g. Thus the limiting compressed word has activity >=3delta/4.
In a macroscopic crossing the extra root alone has activity >=delta. This
proves (1), with margin.

The exact identities N_l(X)=product_a(1-q_al)N_l(T)>0 make every root
nonsure and every intermediate Never mass positive. For each root,

    d_l(before)=R_l+c(q)d_l(after), R_l>=0,
    (B_l-e_l)(before)>=H_l(q)(B_l-e_l)(after)>=0.

These identities/inequalities pass to H by continuity. Since c,H_l>0,
zero observer debts and ALL-END pass to all descendants.

## 5. Selecting one actual head and a restricted endpoint

Let Y be a nonrealized minimum supplied by Section 2. At every current point
use an eligible rule from Sections 3--4 with the largest of its finitely many
canonical positive activity bounds. For the all-positive-observer rule use
b=min_observer B_l; for a negative cap use z=-B_l; for each pair satisfying
(M), use b=min(B_j,B_k). Stop if no rule applies.

Every word is finite and literal. Positive original Never makes every root
nonsure; C and ALL-END pass to every descendant. At a finite stop use that
endpoint Q and the finite head P followed by Never. Otherwise flatten all
words into ONE natural sequence q_t with conditional tuples X_t, X_0=Y.
Every finite prefix has survival at least nu(Y), since its tail's Never
coordinates are at most one. Thus

    sum_t sum_l q_(t,l)<infinity,
    product_t product_l(1-q_(t,l))>=nu(Y)>0.              (8)

The actual head P uses this natural sequence and leaves its residual masses
at literal Never. Nothing is inserted after a limit time. Adjacent U and e
coordinates differ by at most 2M sum_l q_(t,l); since B=e the same bound
controls caps. Original tail Never coordinates increase and stay bounded.
Consequently the full augmented tuples converge to Q in C, ALL-END, with
positive original Never. The root inequality
B_l(X_t)>=Q_l(q_t)>=-M sum_a q_(t,a) implies B_l(Q)>=0.

Every observer cap cannot stay positive at Q: the all-positive rule would
then give a uniform positive lower bound on every sufficiently late word,
contradicting (8). If B_p(Q)=B_i(Q)=0, B_j(Q),B_k(Q)>0 and (M) holds, the
new rule gives that same contradiction. Its bound is uniform as BOTH other
caps approach zero from either sign. At a finite stop those configurations
are excluded directly by eligibility. Therefore the endpoint has a zero
observer cap and satisfies the first claimed two-zero restriction.

Write n_l=N_l(P), h_l=product_(a!=l)n_a and s=product n_l. Unrolling gives

    U_l(Y)=U_l(P)+s U_l(Q),
    B_l(Y)=max(B_l(P),e_l(P)+h_l B_l(Q)),
    e_l(Y)=e_l(P)+h_l e_l(Q),
    N_l(Y)=n_l N_l(Q).                                  (9)

For finite prefixes these are the exact stopped-law identities. Payoff and
Never series converge absolutely by (8). Finite head queries increase
through the actual response menu, and the remaining tail converges to Q.
Its nonnegative caps ensure that the through-head cap dominates the head's
own Never query. This proves the limiting maximum in (9). Equivalently,
finite prefix maps are nonexpansive in the supplied payoff/cap coordinates,
so applying them to X_t or Q has the same limit. This is the retained-query
semantic map Phi_P(Q), not an execution after infinitely many dates.

The argument also permits any additional finite family of exact incoming
rules that preserves C, ALL-END and original Never, with assigned activity
bounds bounded away from zero near each limit configuration they exclude.
Include their bounds in the same maximum. Summability and the uniform-limit
contradiction are unchanged. Thus the new restriction is compatible with
other exclusions obtained by such incoming rules.

## 6. The selected endpoint cannot have all caps zero

Suppose B(Q)=0. Since Q is ALL-END, also e(Q)=0; observer optimality gives
U_l(Q)=0 for every observer. Put R=d_p(Q)+r nu(Q)>0. Grafting Q after ANY
Z in C using Section 1, formula (2), retains all caps and observer payoffs and gives exactly

    J_r(Z graft Q)=d_p(Z)+R nu(Z)=J_R(Z).

Hence f(R)>=f(r)=mu. On the other hand(9) shows that the ACTUAL head P
has the same observer caps and payoffs as Y, and so P belongs to C. The
same identities give J_R(P)=J_r(Y)=mu, yielding f(R)=mu<A. Strict increase
below A in Section 2, formula (7) forces R=r. Thus d_p(Q)=r(1-nu(Q)).

If nu(Q)<1, repeat retained-query grafts of Q after Y. The resulting points
remain in C, have the same full caps, and satisfy

    nu(Y_n)=nu(Y)nu(Q)^n,
    d_p(Y_n)=mu-r nu(Y)nu(Q)^n.

A compact limit has nu=0 and SUM debt mu<A, contradicting(3). If nu(Q)=1,
all marginal Never coordinates are one. On actual laws, own-zero rewards
give |U_l|<=M(1-nu), |e_l|<=M(1-h_l), and |B_l|<=M(1-h_l); these bounds
pass to H. Thus Q is exactly AllNever. Formula(9) would make Y the actual
tuple of P, contrary to its nonrealized status.

Therefore Q has at least one strictly positive cap. Together with
Section 5 this proves the mixed endpoint assertion in the present theorem. The proof
never minimizes at Q, reassigns original Never mass, or changes the selected
source table or penalty during the incoming construction.

## 7. A negative-pair reset that returns the pinned positive cap

### 7.1. Raw tests and produced comparison

There are four players p,i,j,k. Native own singletons and AllNever pay zero.
Let H be the compact closure of actual independent complete stopping-law
(U,B,e,N) tuples, and C impose zero observer debt B_l-U_l for l!=p.
B prices every deterministic finite deadline and Never, hence all behavioral
replacements. Let Q in C satisfy

    B(Q)=e(Q), N_l(Q)>0,
    b_i=b_j=0, b_p>0, b_k>0.

Put u=U_p(Q), nu=product N_l(Q), z=b_p-u+r nu for fixed r>0.
Raw signs are

    Gamma_ij=-a<0, Gamma_ji=-b<0,
    Pi=Z_i({i,j})>0, Pj=Z_j({i,j})>0,
    A=Gamma_ip>0, B=Gamma_jp>0.                  (1)

Define literal constants

    c_i=B/b, c_j=A/a, C=c_i+c_j, W=1+C, D=1+Pi/a+Pj/b,
    g_l=Gamma_lp+c_i Gamma_li+c_j Gamma_lj,
    E_l=Z_l({i,j})+Gamma_li Pj/b+Gamma_lj Pi/a,
    K_l=c_i c_j E_l/D,                            (2)

for l=p,k; Gamma_pp=0. For a scalar 0<t<1 put

    S=1/[(1+c_i t)(1+c_j t)],
    L_p=S[b_p+t g_p+t^2 K_p],
    L_k=S[b_k+t(g_k-b_k)+t^2 K_k],
    J=S[(1-t)z+t b_p].                           (3)

The test below constructs a point R_t in C, with ALL-END, positive original
Never, B_i=B_j=0, B_p=L_p, B_k=L_k, and J_r(R_t)=J. The test uses only
literal arithmetic and finitely many inequalities, including all full caps.

Require the diffuse solo-p entry cap to be nonnegative:

    E_k^entry=(1-t)b_k+t Gamma_kp>=0.             (4)

There is NO participant-premium comparison on any of the three pivot pairs.
The entry uses vanishing atoms and all queried participant rewards may be
arbitrary finite numbers. The eight reset guards below remain in force.

Put x0=tA, y0=tB, A0=Pi+a, B0=Pj+b. For each l=p,k, define the bilinear
polynomial G_l(x,y) by

    G_l(x,y)=L_l(A0+x)(B0+y)
      +(L_l-Gamma_lj)(Pi/a) x(B0+y)
      +(L_l-Gamma_li)(Pj/b) y(A0+x)
      +(L_l-E_l/D)(Pi Pj/(ab))xy
      -Z_l({l,i}) A0 y-Z_l({l,j}) B0 x-Z_l({l,i,j})xy.   (5)

Require G_l>=0 at the four corners of [0,x0] times [0,y0], for each l=p,k.
These EIGHT finite inequalities certify every quiet deadline in an unbounded
reverse-geometric prefix. They also imply L_p,L_k>=0 by the zero corner.
Strict positive L_p,L_k may be imposed to remain on the same two-zero face.
No continuity in unspecified strategic witnesses is an input.

### 7.2. Exact negative-pair projection, including full caps

Produce the entry tuple T by a diffuse solo-p block. Its desired i,j caps,
payoffs and Never offers are x0=tA,y0=tB. Its pivot cap and Never offer
are b_p, pivot payoff is (1-t)u, and the quiet observer k has cap/payoff/
Never offer E_k^entry. Original Never N_p is multiplied by1-t; the other
three original Never coordinates are unchanged. These claims follow from
full cap calculations, without participant-premium restrictions.

For m>=1 prepend m solo-p roots, each of hazard
h_m=1-(1-t)^(1/m), then take the full augmented limit. For l!=p, its pure
head deadline at date d, 0<=d<m, pays

    V_l,d=Gamma_lp[1-(1-h_m)^d]
                         +(1-h_m)^d h_m Z_l({l,p}).       (4a)

The sequence is monotone: its increment is
h_m(1-h_m)^d[Gamma_lp-h_m Z_l({l,p})], with a fixed sign. Thus all head
queries are controlled by the first and last. Their limits are0 and
Gamma_lp t. The exact through-tail cap is
bhat_l=Gamma_lp t+(1-t)b_l. Consequently the limiting FULL cap is

    max(0,Gamma_lp t,bhat_l).                    (4b)

For i,j, b_l=0 and Gamma_lp>0, so the cap equals bhat_l=t Gamma_lp. For k,
bhat_k-Gamma_kp t=(1-t)b_k>0, so the entry guard bhat_k>=0 makes its cap
bhat_k. Prescribed payoff and Never offer are also bhat_l for every observer.
At every finite stage the pivot cap is b_p; its payoff after the block is
(1-t)u, and its original Never factor is1-t. The other Never coordinates
are unchanged. Hence all augmented coordinates converge to the required
ALL-END T in C. Each finite block maps H into H; closure gives T in H.
No time is assigned after an infinite block: later finite constructions
below use actual approximants to T and a diagonal finite-profile sequence.

Repeatedly PREPEND joint i,j roots. From tail caps (x_(n-1),y_(n-1)), use

    q_j,n=x_(n-1)/(Pi+a+x_(n-1)),
    q_i,n=y_(n-1)/(Pj+b+y_(n-1)),
    x_n=Pi q_j,n, y_n=Pj q_i,n.                    (6)

Every such root is proper. The exact active comparisons are

    -a q_j,n+(1-q_j,n)x_(n-1)=Pi q_j,n=x_n,
    -b q_i,n+(1-q_i,n)y_(n-1)=Pj q_i,n=y_n.

Thus both observers remain optimal and ALL-END at every root. The other
two players always Continue in this prefix. Both recurrences contract:

    0<x_n<=x0 [Pi/(Pi+a)]^n,
    0<y_n<=y0 [Pj/(Pj+b)]^n.

Their original Never factors telescope because

    1-q_j,n=(a+x_n)/(a+x_(n-1)),
    1-q_i,n=(b+y_n)/(b+y_(n-1)).                   (7)

The n-root chronological word is q_n,...,q_1 followed by T. It is a finite
prefix of a point in H, hence in H. For fixed n, approximate T by actual
finite profiles and prepend this FINITE word. A diagonal sequence realizes
the augmented limit. No root follows an infinite calendar.

For a passive recipient l=p,k, let v_l,n denote its full Never offer after
n roots. Direct substitution in the passive root recursion gives

    v_l,n=L_l+(L_l-Gamma_lj)x_n/a
                   +(L_l-Gamma_li)y_n/b
                   +(L_l-E_l/D)x_n y_n/(ab).     (8)

At n=0 this agrees with T by (2)-(3). The coefficient identity making (8)
invariant is D=1+Pi/a+Pj/b. Alternatively it follows by the first-coalition
mass calculation below. Since the roots' denominators are positive,

    (Pi+a+x)(Pj+b+y)[v_l,n-Q_l(q_n)]=G_l(x,y),    (9)

where x=x_(n-1), y=y_(n-1). All these pairs lie in the tested rectangle.
A bilinear polynomial attains its minimum on a rectangle at a corner.
The eight guards therefore prove Continue weakly dominates Quit at EVERY
root. Starting from T's full cap equal to its Never offer, induction gives
B_l,n=e_l,n=v_l,n. This checks unrestricted behavioral caps: a behavioral
replacement is a mixture of finite deadlines and Never; the root max-cap
recursion is exact, not merely a one-step-deviation assertion.

For n tending to infinity, (8) converges to L_l, while x_n,y_n tend to0.
The limiting original Never coordinates are

    N_p(R_t)=(1-t)N_p(Q), N_k(R_t)=N_k(Q),
    N_i(R_t)=N_i(Q)/(1+c_i t),
    N_j(R_t)=N_j(Q)/(1+c_j t).                    (10)

All are positive. Every augmented coordinate converges, so compact closure
puts the limit R_t in H. All observer debts are zero throughout and hence
at the limit. ALL-END is also preserved.

For completeness, the pair prefix's limiting first-coalition masses are

    survival=S,
    chi_ij=x0 y0/[(a+x0)(b+y0)D]=S t^2 c_i c_j/D,
    alpha_j=(Pi chi_ij+S x0)/a,
    alpha_i=(Pj chi_ij+S y0)/b.                  (11)

These follow from (7), the two active zero-payoff identities
-a alpha_j+Pi chi+S x0=0 and -b alpha_i+Pj chi+S y0=0, and total probability.
Thus they are nonnegative and sum with S to1. For l=p,k their absorbing
contribution is Gamma_li alpha_i+Gamma_lj alpha_j+Z_l(ij)chi.
Equations (3), (8) follow. In particular

    U_p(R_t)=S[(1-t)u+t g_p+t^2 K_p],
    nu(R_t)=S(1-t)nu,
    d_p(R_t)=S[b_p-(1-t)u].                      (12)

This proves J_r(R_t)=J exactly, including original Never coordinates.

### 7.3. Returning to the one positive observer cap

The changed positive observer cap satisfies the exact identity

    L_k-b_k=S t [g_k-W b_k+t(K_k-c_i c_j b_k)].    (13)

If H_k:=K_k-c_i c_j b_k is nonzero, the UNIQUE nonzero algebraic return
has produced parameter

    t_star=(W b_k-g_k)/H_k.                       (14)

Test 0<t_star<1, (4), and the eight corners (5). If they pass, this single
explicitly produced R_t has exactly the SAME THREE OBSERVER CAPS as Q,
even if the first derivative g_k-W b_k is nonzero. This is a nonzero cap return,
not a tangent with first-order cap errors. If H_k=0 and g_k=W b_k, every
admissible t returns the cap; if H_k=0 but g_k!=W b_k, no t>0 returns it.

## 8. Global consumption without losing the head's cap constraints

Apply Section 7 to the two-zero-observer endpoint Q from Sections 2--6.
Every observer cap is returned exactly; since Q and R_t belong to C, their
observer payoffs are equal too. Both are ALL-END. For the actual head P,
Section 5, formula (9), also valid for R_t by finite approximation, preserves EVERY
observer payoff and cap. Hence Phi_P(R_t) belongs to C.

A particularly useful test is

    L_p<=b_p, U_p(R_t)>=u.                              (D)

It uses the explicitly produced quantities (3),(12), not an assumed
improving strategy. The pivot cap of Phi_P(R_t) weakly decreases by
Section 5, formula (9),
and its prescribed payoff weakly increases by s[U_p(R_t)-u]. Its original
Never decreases by the STRICT factor S(1-t)<1. Since r>0 and s,nu(Q)>0,

    J_r(Phi_P(R_t)) < J_r(Phi_P(Q)).

This contradicts global minimality. The argument handles every inherited
cap pin and every pivot obstacle, including equality at the obstacle. With
strict payoff increase it also works at r=0. Therefore every selected
two-zero-observer endpoint must fail at least one raw premise, candidate
selection, full-cap guard, or inequality (D). All compared objects are
produced. The change gives a fixed positive gain: actual approximants to
Phi_P(R_t) have observer debts tending to zero and source objective below
the old minimum by at least half that gain eventually.

Here is a stronger head-dependent test that retains the obstacle explicitly.
Set n=N_p(P)>0 and alpha=[B_p(P)-e_p(P)]/h_p>=0. The inequality alpha>=0
holds because actual finite pivot deadlines tend to the head's Never offer.
ALL-END at Y implies b_p>=alpha. Section 5, formula (9), gives the exact difference

    [J_r(Phi_P(R_t))-J_r(Y)]/s
      = max(alpha,L_p)/n-U_p(R_t)+r nu(R_t)
         -b_p/n+u-r nu(Q).                             (O)

Whenever this is negative, the same contradiction follows. Equality of
observer caps makes the comparison valid without a separate assumption
about the head's active owners. No minimum property of Q itself is used.
Writing z=b_p-u+r nu(Q), (O)<0 is the finite arithmetic test

    J+max(alpha,L_p)/n-L_p < z+(1/n-1)b_p,              (O1)

where J is from (3). If L_p>=alpha, put theta=1/n-1 and c=c_i c_j.
The exact difference becomes

    S t [L+t R],
    L=b_p-W z+theta(g_p-C b_p),
    R=theta K_p-c(z+theta b_p).                         (O2)

The max in (O) must be used when the returned cap crosses the obstacle.

A head-independent version between (D) and (O) puts V=u-r nu(Q)=b_p-z
and requires

    L_p<=b_p, U_p(R_t)-r nu(R_t)>V.                     (D1)

For the produced t these are exactly

    (W V-g_p)/t+c_i c_j V < K_p
                   <=(C b_p-g_p)/t+c_i c_j b_p.         (D2)

The interval length is [(W+c_i c_j t)z-b_p]/t. This test allows a pivot
payoff decrease when reduced Never more than compensates it. Condition (D)
is sufficient for (D1) because r>0 and Never strictly decreases. These
inequalities classify the displayed comparison, not all possible repairs.

## 9. Exact nonvacuity at a no-incoming endpoint with a genuinely pinned cap

Use roles p=0,k=1,i=2,j=3 and singleton matrix

    Gamma=[ 0, 5,-1,-1;
           -2, 0, 1, 1;
            2,-1, 0,-1;
            2,-1,-1, 0].                         (E1)

For every nonsingleton S, set Z_l(S)=1 if l belongs to S and l is 2 or3.
Set all other nonsingleton entries to0, except

    Z_0({2,3})=400, Z_1({2,3})=-100, Z_1({0,1})=1.  (E2)

This specifies the full native table. The following tuple belongs to C,
is ALL-END, and has positive original Never:

    U=(2802569/32000000,40951/250000,0,0),
    B=e=(3683/16000,40951/250000,0,0),
    N=(9/20,1/2,81/200,81/200).                  (E3)

Here d_p=4563431/32000000 and nu=59049/1600000. To verify (E3) without a
strategic existence hypothesis, for each m execute two finite m-stage blocks,
then AllNever. In the first block use rates (1,0,2,2), duration -log(9/10);
in the second use rates (1,1,1,1), duration log2. A block with rates lambda
and duration T uses the proper independent hazards
q_l=1-exp(-lambda_l T/m) at each of its m dates.

The full-cap limit is checked as follows. For one repeated proper root put
H_l=product_(a!=l)(1-q_a), c=product_a(1-q_a), let P_l be passive absorption,
Q_l its forced-Quit offer, and E_l its prescribed absorption. Set
A_l=P_l/(1-H_l), D_l=E_l/(1-c). With an arbitrary tail (u,b,e,N), exact
unrolling gives

    e_l'=A_l(1-H_l^m)+H_l^m e_l,
    U_l'=D_l(1-c^m)+c^m u_l,
    B_l'=max{Q_l,
             A_l(1-H_l^(m-1))+H_l^(m-1)Q_l,
             A_l(1-H_l^m)+H_l^m b_l}.            (21)

The head deadline values form a monotone geometric sequence, so the first
two displayed endpoints cover ALL head queries. The last covers all old
tail queries and Never. In a fixed-rate diffuse limit, A_l tends to
(Gamma lambda)_l/(sum lambda-lambda_l), D_l tends to
(Gamma lambda)_l/sum lambda, and Q_l tends to0. Thus (21) gives full-cap
convergence, not only payoff convergence. The second block's limit is

    U=(45/64,0,0,0), B=e=(7/8,0,0,0), N=(1/2,1/2,1/2,1/2).

For the first block put x=9/10. Its singleton drift is (-4,2,0,0), total
rate5. Substitution into (21) gives

    U_0=-4/5+(481/320)x^5,
    B_0=e_0=-1+(15/8)x^4,
    U_1=B_1=e_1=(2/5)(1-x^5),
    U_2=B_2=e_2=U_3=B_3=e_3=0,
    N=(x/2,1/2,x^2/2,x^2/2),

which is (E3). Every higher reward is finite, so its simultaneous-event
contribution vanishes in this fixed-rate diffuse limit; the large entries
(E2) therefore cause no gap in this calculation.

At this tuple every literal initial root is zero: for l=2,3, all its
participant nonsingletons equal1, so Q_l(q)=1-product_(a!=l)(1-q_a).
B_2=B_3=0 forces every q_a=0, independently of the tail. A zero queried
root would force the after-tuple to remain (E3), because B=e>=0. Hence
there is no positive finite incoming word. The new comparison is genuinely
outside the finite-incoming construction that fails here.

For (E1)-(E3), a=b=Pi=Pj=1, A=B=2, c_i=c_j=2, W=5, D=3,
g_p=-4,g_k=2,K_p=1592/3,K_k=-392/3. Formula (14) gives

    t_star=885735/98491412 in (0,1).

The entry guard (4) is strict. All eight corners (5) are strictly positive.
The produced point has L_k=b_k, L_p<b_p, U_p(R_t)>u, and nu(R_t)<nu.
The exact changes include

    L_p-b_p=-10938555223243947/8042116405556739200<0,
    U_p(R_t)-u=57793451446575/20105291013891848>0,
    nu(R_t)/nu=2403330236736481/2513161376736481<1.

The exact rational checks below reproduce these assertions. The first
positive-observer cap derivative is

    g_k-W b_k=59049/50000>0.

Thus no sufficiently small nonzero move along this same excursion/reset
curve preserves the pinned k cap. Its nonzero cap return succeeds nonetheless.

There is an ACTUAL head that pins this cap: take one root

    q_p=b_k/(b_k+3), q_k=1/100, q_i=q_j=0.

Observer k's forced-Quit offer is q_p, while its through-Q continuation is
-2q_p+(1-q_p)b_k=q_p. It is therefore properly active and pins a_k=b_k.
The two zero observers are quiet with strict gaps q_p-1/50>0. The pivot's
Quit offer is0 and its through cap is positive, so a_p=0. All source caps
are positive. This is a genuine head-box example, not an invented equality
constraint. The strict domination above works even if other heads impose
more severe pivot obstacles.

The completion (E2) already has a pure absorbing Nash profile: players
1,2,3 quit together and player0 Continues. The participants receive (0,1,1);
leaving gives respectively -100,0,0, and player0 is indifferent at0. Thus
A=0. The example establishes nonvacuity and separation from finite incoming
and infinitesimal pinned-cap tests; it is NOT a positive-gap example or a
claim that a no-UE table is known. The selected positive-gap source used in the theorem is counterfactual;
this example does not assert that such a source exists.

### Exact witness certificate

Python3 with SymPy; all comparisons are exact. The decimals printed for corner
values are convenience only.

```python
"""Exact source-mechanism check; literal game has absorbing Nash, not A>0."""
import sympy as s
R=s.Rational
G=s.Matrix([[0,5,-1,-1],[-2,0,1,1],[2,-1,0,-1],[2,-1,-1,0]])
Z={}
for mask in range(1,16):
    if mask & (mask-1)==0:
        Z[mask]=list(G[:,mask.bit_length()-1])
    else:
        Z[mask]=[s.Integer(int(i in (2,3) and bool(mask>>i&1))) for i in range(4)]
Z[12][0]=s.Integer(400); Z[12][1]=s.Integer(-100); Z[3][1]=s.Integer(1)
U=[R(2802569,32000000),R(40951,250000),0,0]
B=[R(3683,16000),R(40951,250000),0,0]
N=[R(9,20),R(1,2),R(81,200),R(81,200)]
bp,bk=B[:2]; up=U[0]; d=bp-up; nu=s.prod(N)
assert d==R(4563431,32000000) and nu==R(59049,1600000)
# Exact two-block diffuse limit; higher-coalition rewards disappear in the limit.
x=R(9,10)
assert up==-R(4,5)+R(481,320)*x**5
assert bp==R(15,8)*x**4-1 and bk==R(2,5)*(1-x**5)
assert N==[x/2,R(1,2),x*x/2,x*x/2]
def root(q,ut,bt,nt):
    P=[]; Q=[]; H=[]
    for i in range(4):
        ps=qs=s.Integer(0)
        others=[j for j in range(4) if j!=i]
        for mask in range(16):
            if mask>>i&1: continue
            prob=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in others)
            if mask: ps+=prob*Z[mask][i]
            qs+=prob*Z[mask|1<<i][i]
        P.append(ps);Q.append(qs);H.append(s.prod(1-q[j] for j in others))
    c=s.prod(1-v for v in q)
    uu=[s.factor(q[i]*Q[i]+(1-q[i])*P[i]+c*ut[i]) for i in range(4)]
    ee=[s.factor(P[i]+H[i]*bt[i]) for i in range(4)]
    bb=[max(Q[i],ee[i]) for i in range(4)]
    nn=[(1-q[i])*nt[i] for i in range(4)]
    return uu,bb,ee,nn,Q
# A genuine finite head pins observer1's positive endpoint cap.
q=[bk/(bk+3),R(1,100),0,0]
yu,yb,ye,yn,yq=root(q,U,B,N)
assert yb==ye and all(yu[i]==yb[i] for i in (1,2,3))
assert yq[1]==yb[1] and all(yq[i]<yb[i] for i in (2,3))
pu,pb,pe,pn,pq=root(q,[0]*4,[0]*4,[1]*4)
a=[s.factor((pb[i]-pe[i])/s.prod(pn[j] for j in range(4) if j!=i)) for i in range(4)]
assert a==[0,bk,0,0]
# Produced finite excursion and nonlinear return.
t=s.factor((5*bk-2)/(-R(392,3)-4*bk)); S=1/(1+2*t)**2
lp=s.factor(S*(bp-4*t+R(1592,3)*t*t))
lk=s.factor(S*(bk+(2-bk)*t-R(392,3)*t*t))
unew=s.factor(S*((1-t)*up-4*t+R(1592,3)*t*t))
nunew=s.factor(S*(1-t)*nu)
assert 0<t<1 and lk==bk and 0<lp<bp and unew>up and 0<nunew<nu
assert (1-t)*bk-2*t>0 # Diffuse entry needs no participant-pair guard.
xx,yy=s.symbols('x y')
for l,cap,E in [(0,lp,398),(1,lk,-98)]:
    poly=cap*(2+xx)*(2+yy)+(cap-G[l,3])*xx*(2+yy)+(cap-G[l,2])*yy*(2+xx)+(cap-R(E,3))*xx*yy
    corners=[s.factor(poly.subs({xx:xc,yy:yc})) for xc in (0,2*t) for yc in (0,2*t)]
    assert min(corners)>0
    print('strict corners row',l,':',[float(c) for c in corners])
assert 2-5*bk==R(59049,50000) # First-order pinning condition fails.
print('t =',t)
print('Bp change =',s.factor(lp-bp))
print('Up change =',s.factor(unew-up))
print('Never ratio =',s.factor(nunew/nu))
print('actual head =',q,'; obstacle vector =',a)
# Explicit absorbing Nash: players1,2,3 quit surely.
au,ab,ae,an,aq=root([0,1,1,1],[0]*4,[0]*4,[1]*4)
assert au==ab and s.prod(an)==0
print('PASS: complete finite tests, actual pinned head, strict dominance; A=0 literal game.')
```

## 10. Monotone-pair boundary tests and scope

The two directed signs in (M) may differ. When Gamma>0 and J=0, head
queries are nondecreasing cumulative singleton rewards; when J=Gamma they
are the cumulative rewards including the queried atom. Negative Gamma
reverses both monotonicities. If Gamma=0, (M) requires J=0 and every such
head offer is zero. The proof retains BOTH old endpoint queries, including
zero-hazard queried dates, so these equalities are covered without limits.
For a one-date head the two retained endpoints coincide.

The interval hypothesis is real: with Gamma=1,J=2 and absolute opposing
atoms (1/100,1/5,1/100), the three queried offers are 1/50,41/100,23/100.
The middle query dominates both endpoints. Endpoint retention alone would
not preserve this cap outside (M). This is a boundary of the compression
argument, not a claim that no different incoming word is possible.

The raw pair condition intersects a strict singleton residual. For example

    Gamma=[0,3,-1,-1;3,0,-1,-1;-1,-1,0,3;-1,-1,3,0]

has determinant45 and inverse

    [2,7,3,3;7,2,3,3;3,3,2,7;3,3,7,2]/15>0.

Every column has negative entries, mutually negative pairs exist, and each
principal triple has determinant6 and a negative inverse diagonal. Thus no
principal triple has nonnegative inverse. The strict interval
0<J_01,J_10<3 is nonempty here. This is an exact matrix-level boundary test,
not a claim of a positive-gap completion or a new raw UE class.

The return test requires nonzero H_k=K_k-c_i c_j b_k in its one-candidate
form. If H_k=0=g_k-W b_k, every admissible t returns the cap, and the same
proof applies to any explicitly chosen t passing the finite guards. If only
H_k is zero there is no positive return on this curve. Neither case is
silently included in the nondegenerate rational selector. Corner positivity
is sufficient, not necessary, for the countable full-cap comparisons.

## 11. Source correspondence and formalization handoff

The literal root maximum is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; the exact payoff
and cap action is `quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`. Finite-game
mixed Nash existence is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`. The model above uses
the same independent behavioral strategies and unrestricted deviations.
The compact augmented carrier, source selection, compression and reset
comparisons are the ordinary mathematics proved here, not assertions about
new checked Lean declarations.

Formalization can separate: full-cap continuity and augmented prefix maps;
first/last-query moment compression for signed monotone pairs; uniform
finite incoming extraction; chronological actual-head selection; the two
contracting scalar recurrences and their bilinear passive invariant; the
eight finite guards; and the exact cap return and head substitution. Keep
original N distinct from escaped finite mass throughout. None of these
interfaces should assume an incoming word or improving strategy as a field.

The source theorem takes the raw obstruction A>0 and the strict inverse
column as inputs. It produces the minimum, its positive Never/ALL-END
properties, and the head/endpoint alternative used by both new reductions.
It does not prove that arbitrary tables have A>0 or that every selected
minimum is actual. The excluded configurations are the signed-monotone
pivot/observer zero face and the two-zero-observer return region certified
above. Other two-zero endpoints and the other global source branches remain
open. No unrestricted Fin4 solution or positive-gap example is asserted.
