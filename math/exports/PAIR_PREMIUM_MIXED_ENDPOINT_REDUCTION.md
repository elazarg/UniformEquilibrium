# A uniform incoming reduction outside the strict positive pair-premium face

## Exact statement and conjecture-facing change

There are four players I={0,1,2,3}, a pivot p, and three observers I minus{p}.
A native quitting table assigns finite real rewards Z_l(S) to nonempty
coalitions, with Z_l({l})=0 and live/AllNever reward zero. Players independently
use complete stopping laws on the natural dates and a separate Never point.
A unilateral behavioral replacement is unrestricted. Let U be prescribed
payoff, B the full behavioral response cap, e the pure-Never offer, and N the
ORIGINAL marginal Never probabilities. Put d=B-U, nu=product_l N_l and
M=max(1,max|Z_l(S)|). Let H be the compact closure of actual (U,B,e,N) tuples,
and C={X in H:d_l(X)=0 for every observer l}. ALL-END means B=e.

Two conclusions are proved.

**Uniform incoming theorem.** Fix an observer i, writing j,k for the other
two. Suppose X in C is ALL-END, every N_l(X)>0, and

    B_p(X),B_j(X),B_k(X)>=b>0,
    J_ip:=Z_i({p,i}) <= max(0,Gamma_ip), Gamma_ip:=Z_i({p}).       (U)

There is NO sign assumption on B_i(X). With

delta=min(1/8,b/(64M)), X is exactly a finite prefix of a point T in C by at
most EIGHT literal product roots, whose total hazard is at least delta/2.
All augmented coordinates are retained. Every root is nonsure, and every
intermediate/tail point is ALL-END with positive original Never coordinates.
The same lower bound applies throughout the three-positive-cap collar,
including negative, zero, and positive values of B_i. No limiting calendar,
rate, or root word is an input.

**Global source reduction.** Define the native absorbing SUM-debt infimum

    A=inf{sum_l d_l(P): P actual, nu(P)=0}.

Suppose A>0 and the raw singleton matrix Gamma is invertible with

    v=Gamma^(-1)e_p>0 coordinatewise.                           (S)

The symbol e_p in(S) is a coordinate unit vector, not a Never offer.
For EVERY 0<r<A, minimize J_r=d_p+r nu on C and let mu be its minimum.
Every minimizer Y has positive original Never, is ALL-END, has nonnegative
observer caps and B_p(Y)>=mu>0. If Y is nonrealized as a full augmented
actual tuple, it has a representation

    Y=Phi_P(Q), Q in C, nu(P)>0, nu(Q)>0, B(Q)=e(Q)>=0,           (R)

where P is an ACTUAL independent head. The map Phi_P is the limit of its
finite-prefix maps; it does not execute Q after an infinite calendar.
The endpoint Q has a zero observer cap, a strictly positive cap, and either

1. at least TWO zero caps among all four coordinates; or
2. exactly one zero cap, at observer i, and

       J_ip > max(0,Gamma_ip).                                 (F)

The head and endpoint are produced from the global source. In particular a
unique-zero-observer endpoint with positive pivot cap must have both a
strictly positive pair reward and a strictly positive pair premium relative
to that observer's pivot singleton reward.

In the ratio chamber J_ip/Gamma_ip>1, Gamma_ip!=0, conclusion(F) forces the
unique-zero observer to have Gamma_ip>0. The negative-singleton observer
cannot be the only zero-cap observer at a positive-pivot endpoint.

The raw hypotheses A>0 and(S) are explicit counterfactual source conditions.
This theorem does not produce an unrestricted positive-gap example, prove
that every table has such a source, or solve Fin4. It strictly narrows the
nonrealized source alternative while leaving actual minima, the strict
positive-premium faces(F), and higher-zero faces open. The endpoint is not
treated as a global minimum. The uniform collar, rather than an incoming
word merely at the exact zero face, is what permits the global conclusion.

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

For fixed r>0, compactness produces mu=f(r)=min_C J_r. AllNever gives mu<=r.
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
Put S=sum_l v_l and k=S-v_p>0. Independent discrete clocks with hazards
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
activity crossing described in Section4. In its small preliminary head all observer Continue comparisons
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

## Uniform incoming theorem: hypotheses for Sections4--6

Fix i,j,k and X satisfying(U). Put G=Gamma_ip, J=J_ip, and

delta=min(1/8,b/(64M)). The following proof constructs the word claimed
in the first theorem. In particular B_i may have either sign.

## 4. First activity crossing and deletion of the two positive observers

Take actual tuples X_n tending to X. Every original Never coordinate is
eventually positive; all conditional hazards q_(n,t,l) therefore exist and
are strictly less than one. Let epsilon_n=d_j(X_n)+d_k(X_n)->0.

The total root activity of each realizer is at least b/(2M), for large n:
native own-zero gives B_p<=M Pr(some opponent has a finite draw), which is
at most M times total root activity. In particular an activity crossing of
delta exists at a finite date.

Stop at the first date for which either its own activity ell(q)>=delta or
the cumulative activity reaches delta. If that date has ell(q)>=delta,
call the preceding head H_n and retain this one extra macroscopic root.
Its head activity is <delta. Otherwise H_n includes the crossing date;
every root in H_n has activity <delta and its total activity is in
[delta,2delta). There is no extra root in this second case.

On H_n, the j and k caps stay at least b/2, and Continue gives their caps.
Indeed a head root Quit offer has absolute value at most M delta. While
Continue gives a cap, moving to the next cap changes it by at most 2M ell.
Starting with caps at least 7b/8, cumulative movement below 4M delta<=b/16
keeps the cap separated from every root Quit offer by at least b/4. The
usual first-failure argument closes this bootstrap. The head joint survival
is at least 1-2delta>=3/4. Nonnegative root debts therefore give

    sum_(t in H_n)(q_(n,t,j)+q_(n,t,k))
        <= 8 epsilon_n/b -> 0.                              (H1)

Delete j and k activity from H_n, leaving every conditional tail law
unchanged. An independent-law coupling changes the full laws only on an event
of probability at most the left side of(H1). It controls U,e,N and EVERY
unilateral response payoff, hence full B, by O(M) times that quantity.
The resulting actual tuples still tend to X. Their head has only p and i
active. Its total marginal finite mass f_n+g_n is at most 2delta.

Let T_n be the unchanged actual tail immediately after H_n. In the
macroscopic-root case T_n itself begins with the retained root of activity
at least delta. That root and its further tail will be extracted separately.

## 5. Exact finite compression of a two-owner head

This is a finite-head lemma; it uses no limiting or actual-attainment claim.
For the p/i head write its ABSOLUTE finite atom probabilities as alpha_t
and beta_t. Put

    f=sum_t alpha_t, g=sum_t beta_t, A_t=sum_(u<t) alpha_u,
    L=sum_t beta_t A_t, c=sum_t alpha_t beta_t.

Its first-coalition probabilities are exactly

    Pr(first={p})=(1-g)f+L,
    Pr(first={i})=g-L-c,
    Pr(first={p,i})=c,
    Pr(no head quit)=(1-f)(1-g).                              (H2)

For g>0, apply finite-dimensional Caratheodory to the mean of the two-vectors
(A_t,alpha_t) with weights beta_t/g. Replace i's head distribution by one
on at most THREE of its OLD positive support dates, preserving g,L,c. For
g=0 use no such dates. Keep p's head and all conditional tail laws fixed.
This preserves(H2), every U output, e output and N output. Player i's cap is
unchanged because its opponents are unchanged.

The other three caps are also unchanged once their output caps exceed
M(f+g). Every head deadline of any such player has absolute payoff at most
M(f+g): unless an opponent has a finite head draw, the deviator quits alone
at native payoff zero. Its cap is therefore its through-head tail option,
which is unchanged by(H2), the original marginal survivals and the tail cap.
For the sequences in Section4 these three caps are at least b-o(1), while
M(f+g)<=2M delta<=b/32. Thus this protection holds for all sufficiently
large n, both before and after the remaining compression.

Keep the at most three selected i dates, including any p atom at those
dates. Between them there are at most FOUR blocks containing p atoms but
no i atoms. If J<=0, move all p mass of each nonempty block to its FIRST p
date. Otherwise (U) gives J<=G; move the mass to its LAST p date instead.
Keep precisely those at most seven occupied dates and delete
ALL other head dates, then append the unchanged tail immediately. Thus no
new empty query is inserted after a coalesced p atom. Retained dates are
reindexed consecutively on the natural calendar.

Both p prefix mass A_t and p same-date mass alpha_t at every retained i
date remain exactly as before. Hence L,c and every quantity in(H2) remain
unchanged. In the FIRST-date construction, at a coalesced p-only date the i
deadline value, measured from the head entrance, changes from

    G A_t + J alpha_t

to G A_t+J a, where a>=alpha_t is the full p mass of that block. In the
FIRST-date construction it cannot increase because J<=0. In the LAST-date
construction write A for p mass strictly before the block, a for its total
p mass, and alpha for its old last atom. The old query is
G(A+a-alpha)+J alpha and the new query is G A+J a. Their difference is
(J-G)(a-alpha)<=0. At every retained i date its deadline value is unchanged.
These are ALL finite head queries in the compressed calendar.
Tail query values are unchanged because their prefix contribution Gf and
opponent survival 1-f are unchanged. Consequently

    e_i(old)=e_i(new) <= B_i(new) <= B_i(old).                  (H3)

The earlier three protected caps stay equal to their unchanged through-head
tail options. Every U,e,N output remains EXACTLY unchanged. Equation(H3)
is the only possible cap change. At the source approximants its size is at
most B_i(old)-e_i(old), which tends to zero because X is ALL-END.

Deleting the unretained queries is essential. Retaining a new empty query
after a coalesced p atom could raise the i offer when G>0; that operation
is not used. The new head is an ordinary finite independent stopping-law
profile, not a product of formal maps with an altered query inventory.

## 6. Extraction and quantitative activity

Apply Section5 to each two-owner head. There are at most seven occupied
head dates. Pass to a subsequence with a fixed number of retained dates and
a fixed choice of the two crossing cases. Do NOT pad the words with zero
roots. Extract each hazard and its actual conditional tail by compactness.
The full tuples of the compressed profiles still tend to X by(H3), so the
continuous exact root maps give the asserted augmented equality. In the
macroscopic case extract that extra root too; this gives at most eight roots.

In the cumulative-crossing case, let a_p,a_i be the sums of original head
hazards of p and i. Deletion gives a_p+a_i>=delta-o(1). Each original
head marginal survival is at least 1-2delta, so

    f_n+g_n >= (1-2delta)(a_p+a_i) >= 3delta/4-o(1).

Any head realizing these exact finite marginal masses has total hazard at
least f_n+g_n. Thus the limiting compressed word has activity at least
3delta/4, in particular delta/2. In the other case its retained extra
root has activity at least delta. Either case makes the limiting word
nonempty and proves the required activity bound.

Original Never coordinates satisfy

    N_l(X)=product_a(1-q_(a,l)) N_l(T)>0.

Every root is therefore nonsure and every intermediate/tail original Never
coordinate is positive. For a literal root the exact debt recursion is

    d_l(before)=R_l(q;B(after))+c(q)d_l(after), R_l>=0.

Since c(q)>0, zero observer debt passes to all descendants and every
observer root has zero regret. Similarly

    (B_l-e_l)(before)>=H_l(q)(B_l-e_l)(after)>=0

passes ALL-END to every descendant. These inequalities hold on H by
continuity. No global minimality of any descendant is inferred.

## 7. A single chronological incoming chain selects the smaller boundary

Let Y be any nonrealized selected minimum from Section2. At each current
point apply any eligible incoming rule from Sections3--6, choosing one with
the largest of its finitely many stated activity lower bounds. For the
all-positive-observer rule use b=min_observer B_l. For each eligible i in
(U) use b=min_(l!=i)B_l. For a negative cap use z=-B_l. These are canonical
positive bounds, not arbitrarily small choices. Stop if no rule applies.

Every extracted word is a literal finite word at the current point. Its
positive original Never makes all roots nonsure; C and ALL-END propagate.
If the process stops finitely, let Q be that endpoint and let P be the finite
head, followed by Never. Otherwise flatten its finite words into ONE natural
sequence q_t with conditional tuples X_t, starting at Y. Every finite prefix
has joint survival at least nu(Y), since the conditional Never coordinates
are at most one. Therefore

    sum_t sum_l q_(t,l)<infinity,
    product_t product_l(1-q_(t,l))>=nu(Y)>0.                  (8)

No root is inserted after a limit time. The actual head P uses this one
sequence on the natural dates and leaves its residual masses at literal Never.

The differences of adjacent U and e coordinates are bounded by
2M sum_l q_(t,l). Because B=e, cap coordinates have the same bound. Original
Never coordinates increase and stay bounded. Thus the full augmented X_t
converges to a point Q in C, ALL-END, with positive original Never. At every
root B_l(X_t)>=Q_l(q_t)>=-M sum_a q_(t,a). Equation(8) implies B_l(Q)>=0.

The limit cannot have every observer cap positive: the all-positive rule
would eventually supply a fixed positive activity lower bound, contradicting
(8). If Q has exactly one zero observer cap i, its pivot cap is positive,
and J_ip<=max(0,Gamma_ip), its other three cap coordinates are eventually
bounded below by one fixed b>0. The uniform theorem then gives the SAME
positive delta/2 lower bound at every sufficiently late word, regardless of
whether B_i(X_t) approaches zero from above or below. This again contradicts
(8). The maximal-bound choice prevents another applicable rule from evading
this bound. The same conclusions hold at a finite stop by eligibility.

The finite-prefix identities unroll to Y=Phi_P(Q) with all coordinates
retained. Explicitly, with n_l=N_l(P), h_l=product_(a!=l)n_a and s=product n_l,

    U_l(Y)=U_l(P)+s U_l(Q),
    B_l(Y)=max(B_l(P),e_l(P)+h_l B_l(Q)),
    e_l(Y)=e_l(P)+h_l e_l(Q),
    N_l(Y)=n_l N_l(Q).                                      (9)

For finite prefixes these are their exact stopped-law identities. Payoff
and Never series converge absolutely by(8); finite head queries increase
through the whole actual response menu. The remaining tail has the fixed
limit Q. Its nonnegative cap ensures that its through-head cap dominates
the head's own Never query, so the limiting maximum is exactly(9).
Equivalently, finite-prefix maps are nonexpansive in their supplied payoff
and cap coordinates, and finite heads applied to X_t converge to the same
limit as those applied to Q. Original Never products give the last identity.
This is a representation by a semantic limit, not execution after infinity.

## 8. The selected endpoint cannot have all caps zero

Suppose B(Q)=0. Since Q is ALL-END, also e(Q)=0; observer optimality gives
U_l(Q)=0 for every observer. Put R=d_p(Q)+r nu(Q)>0. Grafting Q after ANY
Z in C using(2) retains all caps and observer payoffs and gives exactly

    J_r(Z graft Q)=d_p(Z)+R nu(Z)=J_R(Z).

Hence f(R)>=f(r)=mu. On the other hand(9) shows that the ACTUAL head P
has the same observer caps and payoffs as Y, and so P belongs to C. The
same identities give J_R(P)=J_r(Y)=mu, yielding f(R)=mu<A. Strict increase
below A in(7) forces R=r. Thus d_p(Q)=r(1-nu(Q)).

If nu(Q)<1, repeat retained-query grafts of Q after Y. The resulting points
remain in C, have the same full caps, and satisfy

    nu(Y_n)=nu(Y)nu(Q)^n,
    d_p(Y_n)=mu-r nu(Y)nu(Q)^n.

A compact limit has nu=0 and SUM debt mu<A, contradicting(3). If nu(Q)=1,
all marginal Never coordinates are one. On actual laws, own-zero rewards
give |U_l|<=M(1-nu), |e_l|<=M(1-h_l), and |B_l|<=M(1-h_l); these bounds
pass to H. Thus Q is exactly AllNever. Formula(9) would make Y the actual
tuple of P, contrary to its nonrealized status.

Therefore Q has at least one strictly positive cap. Combining this with
Section7 gives precisely alternatives1--2 in the global theorem. The proof
never minimizes at Q, reassigns original Never mass, or changes the selected
source table or penalty during the incoming construction.

## 9. Exact boundary tests

The sign alternatives in(U) control different queries. For a p-only block
of total absolute mass a and first atom alpha, first-date coalescence changes
the i query by J(a-alpha). For old last atom beta, last-date coalescence
changes it by (J-G)(a-beta). These are nonpositive under their respective
hypotheses. Retained i dates keep both their p prefix mass and p simultaneous
mass exactly, so every reward row has the same first-coalition moments.

Deleting newly empty dates is necessary. Take G=1,J=-1, two p atoms of mass
1/10, and then a tail whose i cap and Never offer are -1/4. Such a tail is
actual: a third player quits surely, and both its solo reward to i and its
joint reward with i are -1/4. The two head i query values are -1/10 and0;
the through-tail value is 1/5+(4/5)(-1/4)=0. Coalescing p to mass1/5 at the
first head date gives query -1/5 and unchanged through-tail value0. If the
second now-empty date were retained before the tail, its i query would be
1/5 and would destroy the cap. The proof retains only the occupied compressed
head dates, with the tail immediately afterward.

The collar really includes negative B_i. Let p=0,i=1, f,g in(0,1). Set
Gamma_ip=-1,J_ip=-2,Gamma_pi=1,J_pi=0. For j,k, give reward1 on every
nonempty coalition contained in{p,i}, and reward0 on every coalition containing
that observer; complete other entries arbitrarily with own singleton zero.
Let p have atoms f*2^(-t-1) at every natural t and Never mass1-f; let i
have its only finite atom g at date0. Players j,k Never. Then

    B=e=(g,-f,f+g-fg,f+g-fg),
    U_i=-f, U_j=B_j, U_k=B_k,
    U_p=g(1-f/2), d_p=gf/2.

Every finite i deadline equals -f, because
-Pr(T_p<t)-2Pr(T_p=t)=-f. Pivot Never and every positive-date pivot deadline
equal g; its date0 offer is zero. The passive observers obtain the full
absorption probability at Never, while quitting cannot increase it. All
original Never coordinates are positive. This actual source control has the
negative cap allowed by(U); no global minimization or positive gap is claimed.

At the J=0 boundary take only i's atom g, passive rewards1 to p,j,k, and
participant rewards0 for those players. Then B=e=(g,0,g,g), with zero
observer debts. At the other boundary J=G>0, let both p and i have one atom
of masses f,g at date0, use Gamma_pi=1,J_pi=0, and the same passive rewards
for j,k. Then B=e=(g,Gf,f+g-fg,f+g-fg), and every observer is optimal.
Thus neither closed equality in(U) is removed.

The remaining strict positive-premium sector has a real finite-compression
obstruction. If G>0,J>G and only p acts in a head with total finite mass
f>0 and tail i cap AND Never offer zero, any finite-support head has a last
p atom alpha>0.
Its last i query is Gf+(J-G)alpha>Gf, whereas the Never offer is Gf.
The infinite diluted geometric p law of rate G/J has EVERY finite i query
and its Never offer equal to Gf. Thus finite moment preservation cannot
simply remove the remaining strict-premium hypothesis. This is an obstruction
to that compression step, not a claim that all incoming words or equilibria
are absent in the remaining sector.

## Source correspondence, handoff, and scope

The existing exact operational declarations are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, and
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
Their root maximum and payoff equations match(1) for literal independent
prefixes. The compact augmented carrier, finite moment compression, uniform
incoming producer, and strengthened global endpoint selection are ordinary
mathematics to be formalized, not asserted to be checked Lean here.

A handoff should separate: the three-positive-cap finite-head buffer; the
three-support moment replacement; first/last p-block compression with its
retained query inventory; the uniform eight-root extraction; and the single
chronological incoming selection. None should assume an incoming word or
endpoint classification as a structure field. Original marginal Never must
remain a coordinate throughout the carrier and all limit arguments.

The raw source hypothesis A>0 is a fixed absorbing SUM-debt obstruction
against every actual independent profile, not a displayed positive regret
for a bounded strategy class. The inverse column in(S) is raw matrix data.
The theorem constructs its minimizers, ALL-END property, roots, head and
endpoint from those assumptions; it does not assert actual attainment of the
selected minimum. It also makes no claim that native AllNever is a uniform
solution of the original unnormalized game. Fin4 remains open.
