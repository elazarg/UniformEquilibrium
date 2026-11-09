# Signed two-zero continuations: one monotone row and a finite three-player return

## Exact statement and conjecture-facing change

In the native four-player quitting model of Section1, assume a positive
absorbing SUM-debt gap and a strictly positive inverse pivot column (S1).
For every penalty 0<r<A the compact observer-feasible problem has an ALL-END
minimum Y with positive original Never. If Y is nonrealized, a single actual
positive-Never head P and a mixed endpoint Q are produced below. The endpoint
has nonnegative caps, a zero observer cap, and a positive cap; it is not
assumed to minimize the objective itself.

Three restrictions strengthen this source reduction.

1. When the pivot and one observer have zero caps and the other two caps are
   positive, their directed pair rewards must satisfy (HIGH) or (BOTH-LOW).
   Only ONE directed row needs to lie between zero and its singleton reward
   for the uniform incoming rule to apply; the other may extend below both.
2. When two observers have zero caps and the remaining observer has a
   positive cap, the pivot cap may be ANY nonnegative value. The asymmetric
   nonpositive-pair structure in Section5
   admits a completely finite test. A produced diffuse pivot entry followed
   by ONE product root restores both zero caps exactly. A polynomial of
   degree at most two selects returns to the remaining observer cap. If it
   vanishes identically, finite polynomial sign cells supply the candidates.
   The full pivot cap is priced as a maximum, including ties and changes of
   its maximizing response. A successful componentwise or actual-head
   obstacle comparison excludes the source.
3. Section6 removes that matching-ratio condition for a further family with
   independently variable negative pair rewards and pivot-pair rewards.
   Two explicit roots perform the reset. Their contact equation is a conic;
   rational parametrization reduces every return and full-cap test to
   finitely many one-variable polynomial sign tests, including exceptional
   rays. Four zero cross/triple entries remain required.

The second construction permits unequal nonpositive pair rewards under one
explicit normalization equality and four specified zero entries. All other
rewards are arbitrary finite inputs. These hypotheses are restrictions, not
a classification of arbitrary games. The exact example in Section7 has unequal
pair participant rewards -1/2 and -4/5 and passes strict comparisons at a
negative pivot payoff. It witnesses feasible continuation geometry; its literal game
already has an absorbing Nash profile.

These results narrow selected global sources. They do not assert a new raw
UE reward-table class, settle actual minima, or close all two-zero endpoints.
Every strategic object used by the reduction is produced: the minimum and
head from (S1), incoming words from actual approximants, and the comparison
from the finite reward and endpoint tests. A>0 is the native residual premise,
not an assumed favorable strategy. All proofs here are ordinary mathematics,
not new Lean checks.

## 1. Model and the source produced from the absorbing gap

There are four players. A finite vector Z(S) is specified for every nonempty
quitting coalition S; live play and AllNever pay zero, and Z_l({l})=0.
Put M=max(1,max|Z_l(S)|), Gamma_ab=Z_a({b}) for a!=b, Gamma_aa=0,
and J_ab=Z_a({a,b}). Every player uses private independent randomization.
Before absorption there is exactly one live public history at each natural
date. Sampling all private randomization in advance therefore identifies an
actual profile with four independent complete stopping laws on the natural
dates and Never. Every unilateral behavioral replacement is a mixture of
deterministic finite deadlines and Never.

For an actual profile let U be its prescribed payoff, B the supremum of all
these response payoffs, e its pure-Never response vector, and N its ORIGINAL
marginal Never probabilities. Let H be the closure of all such (U,B,e,N) in
finite-dimensional Euclidean space. It is compact because the coordinates
are bounded. For a fixed pivot p write

    d=B-U, nu=product_l N_l, C={X in H:d_l(X)=0 for l!=p},
    J_r(X)=d_p(X)+r nu(X),
    A=inf{sum_l d_l(P): P actual and nu(P)=0}.

The scalar J_r is distinguished from the directed pair rewards J_ab.
ALL-END means B=e. The set C is compact and contains AllNever.

Assume

    A>0, Gamma invertible, Gamma^(-1)e_p>0 coordinatewise,       (S1)

where e_p in (S1) denotes a coordinate unit vector. For every 0<r<A, J_r
has a positive minimum mu on C. Every minimizer Y has positive original
Never and is ALL-END. If Y is not the tuple of an actual profile, the proof
below produces an actual positive-Never head P and an endpoint Q in C such
that Y=Phi_P(Q), with

    N_l(Q)>0, B(Q)=e(Q)>=0,
    some observer cap zero, some cap strictly positive.        (S2)

The representation is a limit of finite-prefix operations, not a move after
an infinite calendar. The endpoint Q need not minimize J_r.

There is a further restriction on a pivot-plus-observer zero face. If
B_p(Q)=B_i(Q)=0 and the other two caps are positive, then necessarily

    J_ip>max(0,Gamma_ip) OR J_pi>max(0,Gamma_pi),                 (HIGH)

or

    J_ip<min(0,Gamma_ip) AND J_pi<min(0,Gamma_pi).                (BOTH-LOW)

Thus one row above its interval, or both rows below their intervals, are the
only remaining directed pair patterns on this face. This does not close all
two-zero faces or establish a new reward-table UE class.

## 2. Literal roots, retained queries, and the ALL-END minimum

For a product root q let Q_l(q) be the payoff of forced Quit, P_l(q) the
passive absorbing contribution when l Continues, H_l(q)=product_(a!=l)(1-q_a),
and c(q)=product_a(1-q_a). Literal finite prefixing gives

    U'_l=q_l Q_l+(1-q_l)P_l+c U_l,
    B'_l=max(Q_l,P_l+H_l B_l),
    e'_l=P_l+H_l e_l, N'_l=(1-q_l)N_l.                         (S3)

These identities hold on H by continuity. With C_l=P_l+H_l B_l,

    d'_l=R_l+c d_l,
    R_l=max(Q_l,C_l)-q_l Q_l-(1-q_l)C_l>=0,
    B'_l-e'_l>=H_l(B_l-e_l)>=0.                               (S4)

In particular zero observer debts and ALL-END pass to descendants through
every positive-survival root. Changing complete laws on a coupling event
of probability eta changes every prescribed or pure response payoff by at
most 2M eta. Taking suprema gives the same bound on full caps. This also
justifies finite-tail censoring in all augmented coordinates.

For X,T in H a retained-query graft is in H and has

    U_l(new)=U_l(X)+nu(X)U_l(T),
    B_l(new)=max(B_l(X),e_l(X)+h_l(X)B_l(T)),
    e_l(new)=e_l(X)+h_l(X)e_l(T),
    N_l(new)=N_l(X)N_l(T), h_l(X)=product_(a!=l)N_a(X).          (S5)

To construct it, first censor an actual old law's vanishing finite tail to
its own Never mass. Keep all old queried dates, insert one empty boundary
query, and then append an actual tail. The boundary query offers the old e_l
and is bounded by its old cap. All subsequent responses have old passive
contribution e_l plus h_l times a tail response. This proves (S5) for the
finite construction. Coupling and diagonal approximation prove it on H.

Moving a smallest original Never mass of an actual profile to one finite
date forces absorption. The moved owner's cap is unchanged and its payoff
changes by at most 2M N_l. Each other payoff and cap changes by at most
2M N_l. Since min_l N_l<=nu^(1/4), passage to H gives

    A<=sum_l d_l+14M nu^(1/4).                                (S6)

Put f(s)=min_C J_s for s>=0. AllNever gives f(s)<=s. If 0<r<A, compactness
and (S6) give 0<mu=f(r)<=r<A and, at every minimizer,

    nu>=((A-r)/(14M))^4>0.                                    (S7)

For any a>=0 take a finite-game mixed Nash root at continuation B(Y)-a e_p.
Such a root exists by finite mixed Nash existence. It is observer-Nash also
at B(Y), and raising the pivot Continue value by a H_p increases its root
regret by at most a q_p H_p. Equations (S3)-(S4) and minimality imply

    mu(1-c(q))<=a q_p H_p.                                    (S8)

If a<mu, the inequality 1-c(q)>=q_p H_p forces c(q)=1 and hence q=0.
AllContinue being Nash at that continuation implies B_l(Y)>=0 for observers
and B_p(Y)>=a. Letting a increase to mu gives B_p(Y)>=mu>0.

For actual laws, separation of the owner's Never draw gives
d_l>=N_l(B_l-e_l); continuity extends this to H. Thus the observers of Y
are END-optimal. To treat the pivot, set v=Gamma^(-1)e_p, S=sum_l v_l,
and k=S-v_p>0. For fixed T>0 use independent hazards 1-exp(-v_l Delta)
over a mesh of [0,T], followed by AllNever. As the mesh tends to zero their
augmented tuples converge to a point D_T in H satisfying

    U_l(D_T)=B_l(D_T)=e_l(D_T)=0                       (l!=p),
    U_p(D_T)=(1-exp(-ST))/S,
    B_p(D_T)=e_p(D_T)=(1-exp(-kT))/k,
    N_l(D_T)=exp(-v_l T).                                    (S9)

Indeed the probability of a collision over the whole mesh is O(Delta).
Uniformly in a chosen response date y, the forced-query collision error is
also O(Delta), and its payoff tends to
(Gamma v)_l integral_0^y exp(-(S-v_l)t)dt. Prescribed payoffs use rate S.
Since Gamma v=e_p, these limits prove the FULL-cap assertion (S9), including
Never and every finite deadline. Only actual finite profiles are used.

If B_p(Y)>e_p(Y), grafting D_T after Y for small T leaves every cap unchanged
and every observer payoff unchanged. It strictly raises the pivot payoff
by nu(Y)U_p(D_T) and strictly lowers r nu. This contradicts minimality.
Therefore Y is ALL-END. Also, if 0<=a<b and f(b)<A, every minimizer Z_b
has nu(Z_b)>0 by (S6), so

    f(a)<=f(b)-(b-a)nu(Z_b)<f(b).                              (S10)

## 3. Uniform incoming extraction with protected observers

All incoming rules here apply to arbitrary X in C which is ALL-END and has
positive original Never; they do not require X to minimize anything.
If B_l(X)=-z<0, extract the first root q and its conditional tail from actual
approximants. Compactness and (S3) give X=Phi_q(T), with
B_l(X)>=Q_l(q)>=-M sum_a q_a. Thus sum_a q_a>=z/M. Positive original Never
makes q nonsure, and (S4) passes C and ALL-END to T.

For a positive observer cap bounded below by b>0, put

    delta=min(1/8,b/(64M)).                                   (S11)

Take actual approximants X_n to X, with positive original Never. A native
deadline pays zero if no opponent has a finite draw, so its cap is at most
M times total root activity. For large n a cap at least 7b/8 supplies a
finite activity crossing of delta. Stop at the first date whose own activity
is at least delta or whose cumulative activity reaches delta. If the root
is macroscopic, retain it separately: the preliminary head has activity
less than delta. Otherwise include the crossing root: the head activity is
in [delta,2delta), with each individual root below delta.

Suppose a set E of observer caps is bounded below by b. On the preliminary
head, each l in E has a Continue gap at least b/4. Here is the bootstrap:
the current Quit offer has absolute value at most M delta; while Continue
is the cap branch its conditional cap changes by at most 2M times the root
activity. The total drift is less than 4M delta<=b/16, so starting above
7b/8 the cap cannot reach b/2 or lose this branch. Head joint survival is
at least 1-2delta>=3/4. The nonnegative debt decomposition (S4) therefore
gives

    sum_(t in head,l in E)q_tl <= 8 sum_(l in E)d_l(X_n)/b ->0. (S12)

Delete these E hazards on the head, preserving the old queried calendar and
the tail. The coupling bound changes U,B,e,N by o(1), uniformly over all
responses. Hence the modified tuples still converge to X.

When E is all three observers, the surviving head is pivot-only, with finite
mass f<=2delta. If the old head is nonempty, compress it to one root f e_p.
This preserves U,e,N and the pivot cap max(0,B_p(tail)). Its observer caps
are unchanged through-tail offers, since their head Quit offers are at most
Mf<=2M delta<b/2. Retain this root even if f tends to zero: it records an old
query. An originally empty head is omitted. Extracting also the optional
macroscopic root gives at most two roots. In a cumulative crossing the
surviving marginal mass is at least (1-2delta)delta-o(1); a macroscopic root
has activity at least delta. The extracted word has activity at least
delta/2. This proves the all-positive-observer incoming rule.

Now protect only observers j,k, and let i be the other observer. Assume

    J_ip<=max(0,Gamma_ip), J_pi<=max(0,Gamma_pi),
    J_ip>=min(0,Gamma_ip) OR J_pi>=min(0,Gamma_pi).              (S13)

Thus at least one directed row lies in its closed singleton-to-zero segment;
the other may extend below its segment. The surviving head has only p and i
active. The following compression gives at most nine head dates and hence
at most TEN roots including the optional macroscopic crossing root. The
activity bound is again delta/2, with no restriction on B_p or B_i.

For a nonempty finite head on old dates 1,...,m, write its absolute p and i
atoms as alpha_t,beta_t, and put

    f=sum alpha, g=sum beta, A_t=sum_(u<t)alpha_u,
    L=sum beta_t A_t, c=sum alpha_t beta_t.

The probabilities of first coalitions {p},{i},{p,i}, and no head quit are
respectively (1-g)f+L, g-L-c, c, and (1-f)(1-g). Thus f,g,L,c determine
all prescribed head payoffs, all head Never contributions, and all marginal
survivals. The p/i head deadline menus are

    V_i(t)=Gamma_ip A_t+J_ip alpha_t,
    V_p(t)=Gamma_pi sum_(u<t)beta_u+J_pi beta_t.                (S14)

Assume first that row p is in its segment. Its successive differences are
(Gamma_pi-J_pi)beta_t+J_pi beta_(t+1), all of one sign. Its maximum occurs
at an OLD first or last query. Keep dates 1,m and beta_1,beta_m fixed; if
m=1 do nothing. Apply plane Caratheodory to the interior i atoms with
moment points (A_t,alpha_t), retaining at most three interior old dates and
preserving their mass and both moments. This preserves g,L,c. Player p's
monotone menu has the same endpoint offers and the same through-tail offer,
so its full cap is unchanged. Player i's response menu is unchanged because
its own law does not enter its response payoffs.

There are at most five special dates, including the two old endpoints, and
at most four intervening p-only blocks. In each nonempty block coalesce all
p mass to its FIRST old support date if J_ip<=0, and to its LAST old support
date otherwise. The latter case of (S13) implies 0<J_ip<=Gamma_ip. Retain
the special and coalesced dates; delete every other date, without inserting
queries. Both old endpoint dates are kept even if their hazards vanish.

At special dates, A_t and alpha_t are unchanged, hence so are L,c and the
i query. In a FIRST block the retained i query changes by J_ip(a-alpha)<=0,
where a is block mass and alpha the old atom there. In a LAST block it
changes by (J_ip-Gamma_ip)(a-alpha)<=0. These are all remaining head queries.
The through-tail offer is unchanged. Changing p's own law does not affect
p's cap. Consequently U,e,N and the p cap are exact, while

    e_i(old)=e_i(new)<=B_i(new)<=B_i(old).                      (S15)

Each protected outside cap is exact as well: every head deadline is at most
M(f+g), whereas its cap b-o(1) exceeds M(f+g)<=2M delta. Its through-tail
offer, preserved by f,g,L,c, is therefore the cap. If row i is the monotone
row, exchange p and i in this compression only; the globally designated
pivot is unchanged. The other unprotected cap then obeys (S15).

The old modified tuples converge to ALL-END X, so (S15) squeezes any decreased
cap back to the required limit. Extract a subsequence of fixed word length,
without padding. In a cumulative crossing the surviving two-owner hazard
sum is at least delta-o(1), and each marginal head survival is at least
1-2delta. Thus f+g>=3delta/4-o(1). Every compressed head with these marginal
masses has hazard sum at least f+g. In the macroscopic case the retained
extra root alone has activity at least delta. Continuity gives the exact
incoming identity, at most ten roots, and activity at least delta/2.
The identity N_l(X)=product_a(1-q_al)N_l(T)>0 makes every extracted root
nonsure. Equations (S4) pass C, ALL-END and positive original Never to every
intermediate point. This completes the uniform rule under (S13).

## 4. One actual head, its mixed endpoint, and the global consumer

Start with a nonrealized minimizer Y from Section 2. At each current point
choose among the preceding eligible rules one with largest assigned activity
bound: z/M for a negative cap, delta/2 for all positive observer caps, and
delta/2 for each eligible pair in (S13), using the minimum of its protected
caps for b. Stop when none applies. Each extracted word is finite and literal.
If the procedure stops finitely, use its endpoint Q and its finite head P
followed by Never. Otherwise flatten all words into one natural sequence q_t
with conditional tuples X_t, starting at X_0=Y.

Every prefix survival is at least nu(Y)>0, because all tail Never coordinates
are at most one. Taking logarithms of the product gives

    sum_t sum_l q_tl<infinity,
    product_t product_l(1-q_tl)>=nu(Y)>0.                       (S16)

The actual head P uses these roots and leaves the remaining masses at literal
Never. Adjacent U,e coordinates differ by at most 2M sum_l q_tl; ALL-END
gives the same bound for B. Tail Never coordinates increase and stay bounded.
Thus X_t converges to Q in C, ALL-END, with positive original Never.
Since B_l(X_t)>=Q_l(q_t)>=-M sum_a q_ta, its caps are nonnegative. At a finite
stop this follows from ineligibility of the negative-cap rule.

If all observer caps at Q were positive, the all-positive rule would supply
one positive activity bound on all sufficiently late words, contradicting
(S16). The same argument applies if B_p(Q)=B_i(Q)=0<B_j(Q),B_k(Q) and
(S13) holds: its bound is uniform as both unprotected caps approach zero
from either sign. At a finite stop, eligibility directly excludes these
configurations. Negating (S13) is exactly (HIGH) or (BOTH-LOW).

Let n_l=N_l(P), h_l=product_(a!=l)n_a and s=product_l n_l>0. Unrolling (S3)
gives the retained-query head map

    U_l(Y)=U_l(P)+s U_l(Q),
    B_l(Y)=max(B_l(P),e_l(P)+h_l B_l(Q)),
    e_l(Y)=e_l(P)+h_l e_l(Q), N_l(Y)=n_l N_l(Q).                (S17)

The payoff and Never series converge absolutely by (S16). Finite head
queries exhaust the actual head menu; the nonnegative cap B_l(Q) makes the
through-head option dominate the head's own Never query. This proves the
cap identity. Equivalently, finite prefix maps are nonexpansive in the tail
payoff and cap coordinates, so replacing X_t by its limit Q has vanishing
effect. Formula (S17) identifies Y=Phi_P(Q); it does not execute Q after an
infinite calendar. By (S5), Phi_P(R) is a point of H for every R in H.

It remains to exclude B(Q)=0. Then e(Q)=0 and U_l(Q)=0 for observers. Put
R=d_p(Q)+r nu(Q)>0. Grafting Q after any Z in C preserves all its caps and
observer payoffs, and gives J_r(Z graft Q)=J_R(Z). Hence f(R)>=f(r)=mu.
Formula (S17) also shows that the ACTUAL head P belongs to C and satisfies
J_R(P)=mu. Thus f(R)=f(r)=mu<A, and (S10) forces R=r.

If nu(Q)<1, repeated retained-query grafts of Q after Y remain in C, preserve
all caps, and satisfy nu(Y_n)=nu(Y)nu(Q)^n and
d_p(Y_n)=mu-r nu(Y)nu(Q)^n. A compact limit has nu=0 and total debt mu<A,
contradicting (S6). If nu(Q)=1, every marginal Never coordinate is one.
On actual laws, |U_l|<=M(1-nu), |e_l|<=M(1-h_l), and
|B_l|<=M(1-h_l); these inequalities pass to H. Hence Q is exactly AllNever,
and (S17) makes Y the actual tuple of P, again a contradiction. Therefore
some cap at Q is positive, proving (S2).

The construction permits any additional finite family of exact incoming
rules preserving C, ALL-END and original Never, whose assigned activity
bounds stay positive near the configurations they exclude. Include their
bounds in the same maximum. The same summability argument retains every
previous exclusion. No minimizing property of Q is used.

For subsequent comparisons, (S17) shows directly that a replacement R in C
with exactly the same observer payoffs and caps, B_p(R)<=B_p(Q),
U_p(R)>=U_p(Q), and nu(R)<nu(Q), contradicts global minimality after the
same positive-survival head P. Its output observer debts stay zero, its pivot
cap cannot increase, its pivot payoff cannot decrease, and its penalty
strictly decreases. This remains valid at a binding pivot cap obstacle.

The literal root maximum corresponds to
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; the prescribed
payoff/cap splice corresponds to
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
These interfaces price unrestricted behavioral deviations. The augmented
Never coordinates, compact selection, uniform compression, and source
reductions proved here are ordinary mathematics beyond those root identities.

## 5. A finite return for asymmetric nonpositive pair rewards

### 5.1. Native data and the input endpoint

The four distinct roles are p,i,j,k. Native own-singleton and AllNever
rewards are zero. All rewards Z_l(S) are finite. Write Gamma_ab=Z_a({b}).
Players use independent complete stopping laws on the natural dates and
Never; a unilateral behavioral replacement is unrestricted. Let H be the
compact closure of their full augmented tuples (U,B,e,N), where B is the
supremum over finite deadlines and Never and N is ORIGINAL marginal Never.
Let C impose B_l=U_l for the three observers l!=p.

Consider an endpoint Q in C with

    B(Q)=e(Q), N_l(Q)>0,
    B_i(Q)=B_j(Q)=0, B_p(Q)=b_p>=0, B_k(Q)=b_k>0,
    U_p(Q)=u, nu=product_l N_l(Q)>0.                 (1)

The raw conditions concern only the two zero observer rows:

    A=Gamma_ip>0, B=Gamma_jp>0,
    a=-Gamma_ij>0, b=-Gamma_ji>0,
    m_i=Z_i({p,i})>0, m_j=Z_j({p,j})>0.             (2)

Compute theta=-A Z_i({i,j})/(a m_i). Require

    0<=theta<1,
    Z_j({i,j})=-theta b m_j/B,
    Z_i({p,j})=Z_j({p,i})=0,
    Z_i({p,i,j})=Z_j({p,i,j})=0.                    (3)

Thus both pair participant rewards are NONPOSITIVE, possibly zero, and
need not be equal. The normalization equality in (3) is a real restriction;
no generic perturbation or arbitrary signed-pair closure is claimed.
All other singleton and higher rewards are arbitrary finite inputs.

Put

    alpha=theta/(1-theta)>=0,
    beta=B/[b(1-theta)]>0, gamma=A/[a(1-theta)]>0,
    d1=alpha+beta+gamma,
    d2=alpha beta+alpha gamma+beta gamma,
    d3=alpha beta gamma.                            (4)

Every coefficient below is a literal arithmetic expression in the raw table
and the source's b_p,b_k,u,nu. No controller, root, rate, or favorable return
point is supplied.

### 5.2. Finite parameter selection

Define the raw k coefficients

    h1=(1+alpha)Gamma_kp+beta Gamma_ki+gamma Gamma_kj-b_k,
    h2=alpha beta Z_k({p,i})+alpha gamma Z_k({p,j})
                                      +beta gamma Z_k({i,j}),
    h3=alpha beta gamma Z_k({p,i,j}),
    R(t)=(h1-d1 b_k)+(h2-d2 b_k)t+(h3-d3 b_k)t^2.   (5)

If R is not identically zero, enumerate its at most two real roots by the
linear/quadratic formula, retaining those in (0,1). If R is identically zero,
the finite polynomial-sign procedure in Section5.6 produces all needed test
representatives. For each produced t set

    D_p=(1+beta t)(1+gamma t),
    D=(1+alpha t)D_p,
    v_k=(1-t)b_k+t Gamma_kp,
    E_p=b_p+t[beta Gamma_pi+gamma Gamma_pj]
                                      +t^2 beta gamma Z_p({i,j}),
    Q_p=t[beta Z_p({p,i})+gamma Z_p({p,j})]
                                      +t^2 beta gamma Z_p({p,i,j}),
    U_p^num=(1-t)u+t[beta Gamma_pi+gamma Gamma_pj]
                       +t^2 beta gamma Z_p({i,j})+alpha t Q_p,
    Q_k=t[alpha Z_k({k,p})+beta Z_k({k,i})+gamma Z_k({k,j})]
        +t^2[alpha beta Z_k({k,p,i})+alpha gamma Z_k({k,p,j})
                                      +beta gamma Z_k({k,i,j})]
        +t^3 alpha beta gamma Z_k({p,i,j,k}).         (6)

The superscript num identifies a numerator, and Q_p,Q_k in (6) are also
numerators, not the input tuple Q. Test ONLY these two entry/observer guards:

    v_k>=0, Q_k<=b_k D.                             (7)

If they pass, the construction below produces Q_t in C with

    B_i(Q_t)=B_j(Q_t)=0, B_k(Q_t)=b_k,
    B_p(Q_t)=max(E_p,Q_p)/D_p=:b_p',
    U_p(Q_t)=U_p^num/D=:u',
    nu(Q_t)=(1-t)nu/D=:nu', N_l(Q_t)>0.              (8)

The output need not be pivot-END-optimal. Its FULL cap is the displayed
maximum; no pivot quiet guard is needed. If E_p>=Q_p it is ALL-END, but
that extra inequality is not required for the source comparison.

A sufficient head-independent rejection test is

    b_p'<=b_p, u'>=u.                               (9)

Because 0<nu'<nu, any passing candidate strictly improves the global
objective through EVERY compatible actual incoming head and every r>0.
The explicit general obstacle test in Section5.5 can reject more sources.

### 5.3. Construction and exact contacts

First produce a diffuse solo-p entry T with total pivot quitting probability
t. Use m solo-p roots of common hazard h_m=1-(1-t)^(1/m), followed by an
actual approximant to Q, and take a diagonal full augmented limit. It gives

    U_i(T)=B_i(T)=e_i(T)=A t,
    U_j(T)=B_j(T)=e_j(T)=B t,
    U_k(T)=B_k(T)=e_k(T)=v_k,
    B_p(T)=e_p(T)=b_p, U_p(T)=(1-t)u.                (10)

Original N_p is multiplied by1-t; other original Never coordinates are
unchanged. The first inequality in (7) makes (10) valid for the FULL caps.
Indeed l!=p's head deadline at date d, 0<=d<m, pays

    Gamma_lp[1-(1-h_m)^d]
                       +(1-h_m)^d h_m Z_l({l,p}).   (11)

Its successive increments all have the sign of
Gamma_lp-h_m Z_l({l,p}), so the sequence is monotone. The endpoint limits
are0 and t Gamma_lp. The through-tail cap is
(1-t)B_l(Q)+t Gamma_lp. For i,j it equals the positive endpoint A t or B t.
For k it exceeds t Gamma_kp by (1-t)b_k>0 and is nonnegative by (7).
Therefore it dominates all limiting head deadlines. The pivot's cap stays
b_p at every finite stage. This also proves that every participant reward
queried during entry is arbitrary finite data; no joining inequality is
silently imposed.

Now prepend ONE product root. Give p,i,j odds

    z=alpha t, y_i=beta t, y_j=gamma t,
    q_p=z/(1+z), q_i=y_i/(1+y_i), q_j=y_j/(1+y_j), q_k=0.    (12)

All hazards are proper; q_i,q_j are strictly positive. If theta=0, q_p=0,
so the construction becomes one joint i,j root. After division by the
positive opponent survival, i's forced-Quit offer is

    m_i z+Z_i({i,j})y_j+Z_i({p,i,j})z y_j=0,

by (3)-(4). Its Continue offer divided by the same survival is

    A t+A z-a y_j+Z_i({p,j})z y_j=0,

because 1+alpha=1/(1-theta) and gamma=A/[a(1-theta)]. The same identities
hold for j. Both observers' forced endpoints are exactly zero. Their
prescribed payoffs, Never offers and full caps are therefore zero, including
all inherited tail queries. These are exact product-root identities, not
first-order approximations or tests of only selected deviations.

### 5.4. The remaining full caps and the nonzero return polynomial

For the pivot, opponent survival is1/D_p. The root Continue cap is E_p/D_p,
and its forced-Quit offer is Q_p/D_p. Hence its full cap is their maximum,
and its Never offer is E_p/D_p. The prescribed payoff is

    [alpha t Q_p+t(beta Gamma_pi+gamma Gamma_pj)
             +t^2 beta gamma Z_p({i,j})+(1-t)u]/D,

which is (8). This formula includes the pivot's prescribed quitting mass;
no pivot indifference or END optimality is assumed.

For k, opponent survival is1/D. Its Continue cap and prescribed payoff
both have numerator

    E_k=b_k+h1 t+h2 t^2+h3 t^3.                    (13)

Its forced-Quit offer is Q_k/D. Exact return to the old k cap is

    E_k-b_k D=t R(t)=0.                            (14)

The selected nonzero root of (5) gives E_k=b_k D, and the second inequality
in (7) makes Continue optimal. Thus U_k=B_k=e_k=b_k. Every tail deviation
is covered by the full cap of T, and the sole new root deviation by (7).
Behavioral replacements are mixtures of deterministic deadlines and Never,
so these calculations price the unrestricted unilateral class.

The original Never coordinates are exactly

    N_p(Q_t)=(1-t)N_p(Q)/(1+alpha t),
    N_i(Q_t)=N_i(Q)/(1+beta t),
    N_j(Q_t)=N_j(Q)/(1+gamma t), N_k(Q_t)=N_k(Q).      (15)

They stay positive and their product is strictly smaller than nu. The finite
root map is continuous on H, so applying it to the diffuse entry T produces
Q_t in H. Concretely approximate T by finite entry blocks and actual tails,
then prepend the single root (12). No root is played after an infinite
calendar. All original Never coordinates are retained in the limit.

This proves (8) and observer feasibility from the raw finite tests.

### 5.5. Consumption by the actual global source

Let Y=Phi_P(Q) be a global minimum of J_r=d_p+r nu on C, with an ACTUAL
positive-Never head P and r>0. The retained-query head map satisfies

    U_l(Phi_P R)=U_l(P)+s U_l(R),
    B_l(Phi_P R)=max(B_l(P),e_l(P)+h_l B_l(R)),
    nu(Phi_P R)=s nu(R),
    s=product N_l(P)>0, h_l=product_(a!=l)N_a(P)>0.   (16)

Truncate P, retain a boundary query, append actual finite approximants to R,
and pass to the coupled limit to prove (16). It does not execute R after
infinitely many dates.

Q and Q_t have identical observer payoffs AND caps. Thus Phi_P(Q_t) has the
same observer payoffs and caps as Y, hence belongs to C. If (9) passes,
its pivot cap weakly decreases, its payoff weakly increases, and its Never
product strictly decreases. Its J_r therefore strictly decreases, contrary
to global minimality. One fixed passing t gives a fixed positive gain; it
is not a vanishing-gain comparison disguised as an error limit.

For a sharper head-dependent test put n=N_p(P)>0 and

    a_p=[B_p(P)-e_p(P)]/h_p>=0.

The exact endpoint obstacle objective, up to a positive factor and constant,
is

    F_P(R)=max(a_p,B_p(R))/n-U_p(R)+r nu(R).

Consequently ANY passing candidate (7)-(8) is excluded if

    max(a_p,b_p')/n-u'+r nu'
                         <max(a_p,b_p)/n-u+r nu.     (17)

No sign or END condition is imposed on the new pivot cap. Formula (17)
keeps the obstacle when it is crossed. A further head-independent sufficient
criterion is b_p'<=b_p and u'-r nu'>u-r nu.

Thus the selected source with zero observer caps i,j cannot satisfy (2)-(3)
and have a candidate passing (7) and either (9) or (17). All candidates and
all strategic objects in this comparison are produced by (4)-(15).

### 5.6. Complete selection in the identity-return case and scope

A nonzero polynomial (5) produces at most two candidates. If it is a
nonzero constant there is no candidate. If R is identically zero, every
parameter in (0,1) returns k's cap; there is still a COMPLETE finite selector
for the stated guards and descent tests.

For the intrinsic test (7),(9), use the five polynomial inequalities

    v_k>=0, b_k D-Q_k>=0,
    b_p D_p-E_p>=0, b_p D_p-Q_p>=0,
    U_p^num-u D>=0.                                (18)

Every degree is at most3 and the denominators cleared are positive. List
0,1 and all real roots in (0,1) of the NONZERO polynomials on the left.
Test every listed interior root and one midpoint in each intervening open
interval. Identically zero polynomials contribute no breakpoint and retain
their zero value in the tests. On each open interval every nonzero polynomial
has a fixed sign, so either every point passes (18) or none does. Testing
the boundary roots also covers isolated admissible points. Thus one of these
finitely many representatives passes exactly when any t in (0,1) passes.
Choose the first passing representative in increasing order. This completes
the strategy producer even in the identity-return branch.

If the actual head is supplied, the sharper obstacle test (17) has the same
finite treatment. Put F_old=max(a_p,b_p)/n-u+r nu and

    W(t)=n[U_p^num-r(1-t)nu+F_old D].

Replace the last three weak inequalities in (18) by the three STRICT
polynomial inequalities

    W(t)-a_p D>0,
    W(t)-(1+alpha t)E_p>0,
    W(t)-(1+alpha t)Q_p>0.                          (19)

The two entry/observer guards remain. Indeed the maximum in (17) is below
the right side exactly when each of a_p,E_p/D_p,Q_p/D_p is below it.
Positive denominators give exactly (19), all of degree at most3. The same
root/cell procedure handles strict signs, including an identically zero
strict polynomial, which correctly prevents any candidate from passing.
One may run the intrinsic and obstacle procedures separately and retain
either successful candidate. No unspecified feasible parameter remains.

The construction covers both zero pair premiums (theta=0) and an entire
nonpositive normalized-premium interval 0<theta<1. It requires the raw
alignment and zero cross/triple entries in (3). Other negative-pair tables
remain open. Neither repeated positive-pair reset algebra nor a positive
pair-premium theorem supplies this root: both participant pair rewards here
are nonpositive, while the positive pivot-pair rewards fund the exact
zero active contacts in (12).

The finite source test has no large-price assumption. No additional raw UE
class is inferred from it. Section6 removes the normalization equality on a
further strict negative-premium region while retaining the four specified
zero entries. Neither result closes all signed-pair continuations.


## 6. Removing pair alignment with a second root

### 6.1. Data, scope, and the actual comparison

Use the native model and augmented carrier H=(U,B,e,N), zero-observer-debt
set C, and input endpoint Q of Section5: B=e, all N>0,
B_i=B_j=0, B_p=b_p>=0, B_k=b_k>0, U_p=u. All behavioral deviations are allowed.
Let

    Gamma_ip=A>0, Gamma_jp=B>0,
    Gamma_ij=-a<0, Gamma_ji=-b<0,
    Z_i({p,i})=m_i A, Z_j({p,j})=m_j B, m_i,m_j>1,
    Z_i({i,j})=-a c_i, Z_j({i,j})=-b c_j,
    0<c_i,c_j<1,                                  (1)
    Z_i({p,j})=Z_j({p,i})=0,
    Z_i({p,i,j})=Z_j({p,i,j})=0.

Every other raw reward is arbitrary finite data. In particular the two
negative pair premiums vary independently through an OPEN rectangle.
Their old normalized alignment equality is absent; m_i and m_j are also
independent. The four zero cross/triple entries remain real restrictions.

The construction below provides a finite algebraic test producing a diffuse
entry and TWO literal roots. A passing test returns all three observer caps
exactly and gives B_p'<=b_p, U_p'>=u, and 0<nu'<nu. It therefore rules out Q
as the endpoint of EVERY actual-head global minimum of d_p+r nu, r>0.
Failure of this test does not assert that the source exists or cannot be
improved by another strategy.

### 6.2. An exact relay and an automatic contact-existence subclass

For 0<t<1 produce the diffuse solo-p entry T with observer values/caps
At,Bt,b_k^entry=(1-t)b_k+t Gamma_kp, pivot cap b_p and payoff (1-t)u.
Require b_k^entry>=0. The finite equal-hazard blocks and full-cap endpoint formula
used in Section5 justify this entry with no participant guard.

Set

    kappa_i=A(m_i-c_i)/c_i, kappa_j=B(m_j-c_j)/c_j,
    ell=max(c_i/(m_i-c_i),c_j/(m_j-c_j)),
    h=min(1/(m_i-1),1/(m_j-1)), ell t<z<h t,
    delta_i=t-(m_i-1)z, delta_j=t-(m_j-1)z.        (2)

If ell>=h this strictly positive relay chart is empty and its test fails.

The first root has odds

    w_p=z, w_i=(B/b)delta_j/(1-c_j),
    w_j=(A/a)delta_i/(1-c_i), w_k=0.               (3)

Both zero observers are exactly indifferent: after division by opponent
survival, i's difference between Quit and Continue is
(m_i-1)A z+a(1-c_i)w_j-At=0, and similarly for j. Their common current
payoff/cap/Never offers are strictly positive:

    X_i=A[(m_i-c_i)z-c_i t]/[(1+z)L_i],
    X_j=B[(m_j-c_j)z-c_j t]/[(1+z)L_j],
    L_i=1-c_i+(A/a)delta_i, L_j=1-c_j+(B/b)delta_j. (4)

To admit the final zero-contact root require X_i/kappa_i=X_j/kappa_j.
After positive denominators are cleared this is the conic

    H(t,z)=c_i(m_j-c_j)[(m_i-c_i)z-c_i t]L_j
            -c_j(m_i-c_i)[(m_j-c_j)z-c_j t]L_i=0. (5)

H has degree at most2 and no constant term. The main finite test below
handles every nonzero H, without assuming the contact conic is feasible.
There is also a useful COMPLETE automatic-contact subclass: if m_i=m_j=m
and c_i!=c_j, a root exists strictly inside (2) for EVERY t>0. Indeed assume
c_i>c_j. At z=ell t, X_i=0<X_j, so H<0. At z=h t both first-root observer
odds vanish and X_i/A=X_j/B=mz/(1+z); the normalized cap difference has the
positive sign of c_i/(m-c_i)-c_j/(m-c_j). Thus H>0. Continuity gives an
interior root. The reverse inequality c_j>c_i reverses the two signs.
This proves contact existence on the whole independent-premium rectangle
within that common-m subclass; it is not a claim that the quiet-cap return
or global improvement automatically passes.

At a root of (5), put z2=X_i/kappa_i=X_j/kappa_j>0. The second root odds are

    v_p=z2, v_i=m_j B z2/(b c_j),
    v_j=m_i A z2/(a c_i), v_k=0.                  (6)

Observer i's forced-Quit numerator is m_i A z2-a c_i v_j=0; its Continue
numerator is X_i+A z2-a v_j=0. The same holds for j. Thus their FINAL full
caps, payoffs and Never offers are exactly zero. All hazards in (3),(6) are
proper and both reset observers are active.

### 6.3. Explicit finite remaining tests, including every full cap

There is no unspecified continuation in the algorithm. For any nonnegative
odds vector w define D_l(w)=product_(a!=l)(1+w_a), D(w)=product_a(1+w_a), and

    P_l(w)=sum_(nonempty S subset I minus{l}) Z_l(S) product_(a in S)w_a,
    Q_l(w)=sum_(S subset I minus{l}) Z_l(S union{l}) product_(a in S)w_a.

The EXACT literal root map, applied to a tail (U,B,e,N), is

    U_l'=[w_l Q_l(w)+P_l(w)+U_l]/D(w),
    B_l'=max(Q_l(w),P_l(w)+B_l)/D_l(w),
    e_l'=[P_l(w)+e_l]/D_l(w), N_l'=N_l/(1+w_l).     (7)

Compute R1=Phi_w(T), R2=Phi_v(R1), using (3)-(7). Require

    b_k^entry>=0,
    Q_k(w)<=P_k(w)+B_k(T),
    Q_k(v)<=P_k(v)+e_k(R1),
    e_k(R2)=b_k,
    B_p(R2)<=b_p, U_p(R2)>=u.                    (8)

The relay k guard implies B_k(R1)=e_k(R1)=U_k(R1), and the final guard and
return imply B_k(R2)=e_k(R2)=U_k(R2)=b_k. The two other observers have already
been checked exactly. Pivot caps are the FULL maxima in (7); pivot END
optimality is not assumed at either root. Hence every passing pair (t,z)
produces R2 in C with unchanged observer payoffs and caps. Formula (7)
prices all tail queries and every new root query, so (8) covers unrestricted
behavioral replacements, not just prescribed active actions.

Every original Never coordinate remains positive, and

    nu(R2)=(1-t)nu(Q)/[D(w)D(v)]<nu(Q).            (9)

Both literal roots precede finite approximants to the diffuse entry. The
continuous finite root maps and a diagonal limit put R2 in H; no date is
placed after an infinite block. The actual-head formulas then give the
strict global improvement exactly as in Section5. Alternatively
replace the last two inequalities of (8) by the exact inherited obstacle
objective inequality; its maximum is priced, not dropped.

### 6.4. Complete UNIVARIATE parameter production, including degeneracies

The test is finite and produces (t,z); it does not assume a favorable relay.
Write z=lambda t in (5). Since H has no constant term,

    H(t,lambda t)=t[L(lambda)+t Q(lambda)],        (10)

where L has degree at most1 and Q has degree at most2. When H is nonzero,
L,Q are not both identically zero. The complete parameter selection for this
chart then has two branches.

For Q(lambda)!=0 set t=-L(lambda)/Q(lambda), z=lambda t. Every quantity in
(2)-(8), including the quiet return, is now rational in ONE variable lambda.
Impose ell<lambda<h, 0<t<1 and (8). The pivot maxima can be evaluated by their
finitely many branches. Concretely the two root caps expand into three
rational candidates for the final pivot cap; include their pairwise
comparison numerators when forming the sign tests.

For each COMMON real zero lambda0 of L and Q in (ell,h), fix z=lambda0 t.
There are only finitely many such zeros because L,Q are not both zero.
Every t then satisfies the contact conic. All remaining conditions become
rational sign/equality tests in the single variable t in (0,1).

In either branch, replace a rational inequality N/D>=0 by N D>=0 with
D!=0, and likewise for strict signs; an equality becomes N=0 with D!=0.
Include all pole locations, and list all real roots of the resulting nonzero
polynomials. Test every admissible boundary root and one point in each open
interval between consecutive roots. On each such interval all polynomial
signs are fixed. An equality that is not identically zero only needs its
roots tested; identically zero equalities impose no condition. Thus this
finite root/cell procedure finds a passing parameter EXACTLY when one exists
within (2)-(8), including common components and isolated boundary solutions.
It uses no generic-resultant or uniqueness assumption. If neither branch
passes, this particular produced two-root comparison is rejected.

Finally handle H identically zero without pretending that (10) has a
nonzero denominator. Its coefficient of z is
(m_i-c_i)(m_j-c_j)(c_i-c_j), so H=0 identically first forces c_i=c_j=c.
The coefficient of t is then c^2(1-c)(m_i-m_j), forcing m_i=m_j=m.
These raw data have the aligned parameter theta=c/m, and Section5
supplies the designated finite fallback. No completeness for ALL
two-root controllers on this degenerate conic is claimed. When the fallback
also fails, the combined source test simply rejects this input.
Endpoint values c_i=0 or1, or c_j=0 or1, are not silently covered by the
strict relay rectangle.

## 7. Exact negative-value boundary examples

This is a complete carrier example and strict global comparison, not a
positive-gap game or a new UE class. All payoffs are native, own singletons
and AllNever are zero, and deviations may use any finite deadline or Never.
Roles are p=0,k=1,i=2,j=3. Use singleton matrix

    Gamma=[0,5,-1,-1; -2,0,1,1; 2,-1,0,-1; 2,-1,-1,0].

Every nonsingleton reward is zero except

    Z_2(02)=Z_3(03)=8, Z_2(23)=-1/2, Z_3(23)=-4/5,
    Z_0(23)=1000, Z_1(23)=-1000,
    Z_0(01)=-256, Z_1(01)=1,
    Z_2(12)=Z_3(13)=-8.                              (1)

This specifies all sixty native absorbing entries. The negative pair
magnitudes are unequal, and every reward other than the two passive pair
prices is bounded in absolute value by256. In particular the normalized
one-root alignment fails: its two theta values are1/8 and1/5.

### 7.1. Producing the input and its full caps

There is a compact actual-law tuple Q0 with

    U0=(2802569/32000000,40951/250000,0,0),
    B0=e0=(3683/16000,40951/250000,0,0),
    N0=(9/20,1/2,81/200,81/200).                       (2)

To produce it, concatenate m equal roots with rates (1,0,2,2) and total
duration -log(9/10), then m equal roots with rates (1,1,1,1) and duration
log2, then AllNever. A rate lambda over duration T means hazard
1-exp(-lambda T/m). Every approximant is an actual finite calendar.

Here is the full-cap calculation. For n repetitions of a proper root, write
F_l for its forced-Quit payoff, P_l for its passive absorption, H_l for
opponent survival, c for joint survival and E_l for prescribed absorption.
Over tail (u,b,e,N), put A_l=P_l/(1-H_l), D_l=E_l/(1-c). The exact output is

    U_l'=D_l(1-c^n)+c^n u_l,
    e_l'=A_l(1-H_l^n)+H_l^n e_l,
    B_l'=max(F_l,A_l(1-H_l^(n-1))+H_l^(n-1)F_l,
                        A_l(1-H_l^n)+H_l^n b_l).        (3)

The head deadline offers form a monotone geometric sequence; the first two
terms give both endpoints, and the last includes all tail responses. In each
block all denominators are nonzero. As m increases, A_l tends to
(Gamma lambda)_l/(sum lambda-lambda_l), D_l to
(Gamma lambda)_l/sum lambda, and F_l to zero. Thus (3) proves FULL cap
convergence, not just payoff convergence. The second block gives
U=(45/64,0,0,0), B=e=(7/8,0,0,0), N=(1/2,1/2,1/2,1/2).
For x=9/10 the first block then gives

    U_0=-4/5+(481/320)x^5, B_0=e_0=-1+(15/8)x^4,
    U_1=B_1=e_1=(2/5)(1-x^5), U_2=B_2=e_2=U_3=B_3=e_3=0,
    N=(x/2,1/2,x^2/2,x^2/2),

which proves (2). Every higher reward in (1) is finite, so collision terms
vanish in these fixed-rate limits.

Now prefix Q0 by one root with

    f=q_p=40951/790951=B0_k/(B0_k+3),
    g=q_k=40951/415951=2f/(1+f), q_i=q_j=0.

For each zero observer, Continue pays `2f-g-fg=0` and Quit pays
`8(f-g)<0`. For k, both offers are f: `-2f+(1-f)B0_k=f`.
For p, Quit pays -256g and Continue pays `5g+(1-g)B0_p>0`.
The exact max-cap root formula therefore produces a tuple Q with

    U=(-4017756840871/5263949750416,40951/790951,0,0),
    B=e=(4657205/6655216,40951/790951,0,0),
    N=(337500/790951,187500/415951,81/200,81/200).       (4)

It is observer-optimal, ALL-END and has positive original Never. Write
u=U_p,b_p=B_p,b_k=B_k,nu=product N. The elementary rational bounds

    69/100<b_p<71/100, -77/100<u<-3/4,
    1/20<b_k<3/50

show in particular that u<-2b_k. This negative-value region is therefore
feasible in the actual compact carrier; it is not limited to singleton-only
diffuse continuations.

### 7.2. Unequal pair rewards, two contacts, and an exact return

For t in (0,1), first produce a diffuse solo-p entry of total mass t over Q.
Its annotations are

    U^T=((1-t)u,(1-t)b_k-2t,2t,2t),
    B^T=e^T=(b_p,(1-t)b_k-2t,2t,2t),
    N^T=((1-t)N_p,N_k,N_i,N_j).                         (5)

The same endpoint-query calculation as (3), or the exact query formula
`Gamma_lp[1-(1-h)^d]+(1-h)^d h Z_l(lp)`, proves (5) in full caps whenever
the k entry is nonnegative. No participant bound survives the vanishing atoms.

For a parameter v>0 define

    z=v(2+3v)/[2(1-2v)], t=7v(1+v)/[2(1-2v)],
    w=v/(2-2v+3v^2).                                   (6)

These satisfy v=2t-6z. Prepend to (5) an INNER root with odds
`(z,0,5v,2v)` in the order p,k,i,j. Its i row's forced-Quit and Continue
numerators are `8z-v` and `2t+2z-2v`; the j row's are `8z-4v` and
`2t+2z-5v`. The identity v=2t-6z makes both contacts exact. Dividing by
the opponent odds denominators gives the two caps

    X_i=(8z-v)/[(1+z)(1+2v)]=14w,
    X_j=(8z-4v)/[(1+z)(1+5v)]=8w.                      (7)

Next prepend the OUTER root with odds `(w,0,10w,16w)`. For i its
forced-Quit and Continue numerators are `8w-(1/2)16w=0` and
`14w+2w-16w=0`. For j they are `8w-(4/5)10w=0` and `8w+2w-10w=0`.
Thus both final observer caps, values and Never offers are exactly zero.
The chronological order is outer root, inner root, finite approximants to
the diffuse entry, then finite approximants to Q.

Put D1=(1+z)(1+5v)(1+2v), D2=(1+w)(1+10w)(1+16w), and
E=(1-t)b_k-2t. The other through-cap and value coordinates are

    b1=[b_p-7v+10000v^2]/[(1+5v)(1+2v)],
    u1=[(1-t)u-7v+10000v^2]/D1,
    k1=[E-2z+7v-10000v^2]/D1,
    b2=[b1-26w+160000w^2]/[(1+10w)(1+16w)],
    u2=[u1-26w+160000w^2]/D2,
    k2=[k1+24w-160000w^2]/D2.                          (8)

The pivot's forced-Quit offer is zero at both roots. The k forced-Quit
offers are z/D1 and w/D2. Hence positivity of b1,b2 and of
k1-z/D1,k2-w/D2 verifies their FULL caps, including all inherited queries.
Original Never is multiplied in product by `(1-t)/(D1 D2)`.

Exact return to b_k is the following literal rational identity:

    k2-b_k=v P(v)/H(v),
    H(v)=790951(1+2v)(1+5v)(3v^2-v+2)
                         (3v^2+8v+2)(3v^2+14v+2),
    P(v)=-11056770v^7+286365677031v^6-4320206716803v^5
          +571366811308v^4-1645508206366v^3-1265376442516v^2
          -316159728872v+55085880.                    (9)

Let I=[17411/10^8,17412/10^8]. Direct rational substitution gives
P(left)>900 and P(right)<-2200. On I, P'<-3*10^11: the constant
derivative term is below -3.16*10^11 and the sum of its positive terms
is less than20, using v<1/5000. Thus there is a unique root v* in I.
All factors of H are positive there, so it is an exact nonzero cap return.

For completeness the full strict comparisons have these rational bounds
throughout I. The symbols are the literal rational functions (6)-(8).

| Expression | Strict lower bound | Strict upper bound |
| --- | --- | --- |
| t | 6/10000 | 7/10000 |
| E | 5/100 | 51/1000 |
| b1 | 697/1000 | 699/1000 |
| k1-z/D1 | 5/100 | 52/1000 |
| b2 | 694/1000 | 697/1000 |
| b_p-b2 | 43/10000 | 45/10000 |
| u2-u | 13/10000 | 14/10000 |
| k2-w/D2 | 5/100 | 53/1000 |

These bounds can be checked by elementary rational interval arithmetic,
without numerical root approximations: insert the two endpoints of I in
(6), then (8), using the minimum and maximum of the four endpoint products
for multiplication and reciprocal endpoints for positive division. Preserve
the displayed factorization; all denominator intervals are positive. The
resulting intervals lie strictly inside every displayed bound. This is also
an explicit finite certificate of every strict inequality used here.

Consequently at v*, Q' is observer-optimal and ALL-END, returns all three
observer caps, strictly lowers the pivot cap, raises its payoff, and lowers
original Never, since `0<(1-t)/(D1 D2)<1`.

Through any actual positive-survival head, equal observer U/B coordinates
remain equal, while the pivot cap weakly falls and payoff strictly rises.
Therefore this replacement strictly improves d_p+r nu for every r>0, with
one fixed gain for the fixed table. It excludes Q as an endpoint of such a
globally minimizing representation.

The table (1) itself is ALREADY SOLVED: coalition {1,2,3} quitting surely
pays all four players zero. Player1 loses1000 by leaving; the other players
are indifferent. Thus it is absorbing Nash and A=0. This example establishes
feasibility and a strict global comparison. It does not establish additional raw UE
coverage or exhibit a positive-gap source. The unequal pair entries do
certify that this return is outside the normalized one-root alignment.

### 7.3. A nonempty aligned return test

If the two pair participant entries in this same table are instead both -1,
the construction of Q is unchanged: its diffuse blocks ignore finite
collision rewards, and its final p/k head has no i/j collision. Section5
then has theta=1/4, alpha=1/3 and beta=gamma=8/3. Put z=t/3,y=8t/3 and
D=(1+z)(1+y)^2. The one-root values are

    b_p'=[b_p-2y+1000y^2]/(1+y)^2,
    u'=[(1-t)u-2y+1000y^2]/D,
    b_k'=[(1-t)b_k-2t-2z+2y-1000y^2]/D.

The two quiet forced-Quit offers are0 and z/D. Return is equivalent to
2620864t^2+151872420240t-49577292=0. This polynomial is strictly increasing
for t>=0 and has its unique positive root in (3/10000,1/2500). Throughout
that interval the entry k value is positive, b_p'>0 and

    (1+y)^2(b_p'-b_p)=y[-2(1+b_p)+(1000-b_p)y]<0,
    D(u'-u)/t=-16/3-(20/3)u+t(64000/9-80u/9)-(64/27)u t^2>9/5.

Use the rational bounds on b_p,u,b_k established in Section7.1. At return,
b_k>1/20>z/D; both quiet guards hold. Thus Section5's one-root test is also
nonempty, and passes strict comparisons with nonpositive pair rewards.
The same absorbing-Nash caveat applies to this completion.

## 8. Boundary tests, source correspondence, and formalization handoff

The incoming rule includes every closed segment endpoint and permits a
strictly low second row. For example Gamma_ip=2, J_ip=-1,
Gamma_pi=-1, J_pi=-1/2 satisfies (S13), while J_ip lies below its whole
singleton-to-zero segment. In contrast, two strict low rows or any strict
high row fail (S13); no compression in that region is asserted.

Both finite return constructions include b_p=0: the diffuse entry retains
the pivot cap max(0,b_p)=b_p, and every subsequent pivot maximum is priced
explicitly. Thus successful tests also exclude three-zero endpoints with
only observer k having a positive cap. Strict pivot positivity is unnecessary.

For the finite return, theta=0 is included: the pivot hazard at the final
root is zero, and both observer pair rewards are zero. At theta=1 the
odds formulas are undefined and the theorem does not apply. A nonzero
constant return polynomial supplies no candidate. Identity return is handled
by sign cells, including isolated admissible boundary roots. If either
entry or quiet-observer guard fails, the claimed observer-feasible output
does not follow. The pivot guard is never discarded: its full maximum is
retained explicitly. Passing a single root test without the actual-head
comparison is not a global exclusion.

The source correspondence is the literal maximum and semantic-pair splice
named at the end of Section4. Those existing declarations provide finite
prefix identities under the project's behavioral deviation semantics.
No existing declaration is being asserted to prove the augmented compact
source, the one-monotone compression, or the finite signed return. There
is no appeal to a public correlation device, a continuous-time strategy,
or execution after an infinite calendar. Diffuse entries and retained-query
grafts are limits of finite profiles in the original native model.

A formalization can separate the following statements: the compact
augmented carrier and continuous literal root maps; the absorbing-gap
lower bound and ALL-END minimizer; the one-monotone finite compression
and chronological head selection; the asymmetric zero-contact identities;
the quadratic return and identity-case sign selector; the two-root contact
conic, its exceptional rays and full-cap selector; and the composition
comparison through the selected actual head. The last theorem should take
(S1) and finite reward predicates, construct its minimum/head and candidate
roots, and conclude the stated source exclusions. It must not place a
favorable controller, cap return, or desired inequality in a structure
field that claims to produce it.

The scalar and quadratic identities can be checked independently of source
selection. The full-cap proof must retain all old queried dates and the
through-tail option; verifying only current deviations is insufficient.
Original marginal Never masses are separate coordinates throughout.
Actual minima, strict HIGH and BOTH-LOW endpoint patterns, negative-pair
data outside the stated structural tests, failed finite return comparisons,
and higher-zero faces not excluded by these tests remain open under this
packet's argument.
