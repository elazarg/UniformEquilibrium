# Actual minima and inherited mixed endpoints

Owner: CODEX_ROOT.

## Current mathematical boundary

The subcritical selection in Section9 of
[the zero-observer boundary reduction](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md)
leaves two source cases: an actual positive-Never ALL-END minimum of
J_r=d_p+r nu, or a nonrealized minimum represented by an actual
positive-Never head and an inherited mixed endpoint. The endpoint has
nonnegative caps, at least one zero observer cap, and at least one positive
cap. It is not itself a global minimum. Neither source case is closed here.

The [uniform pair-premium reduction](../exports/PAIR_PREMIUM_MIXED_ENDPOINT_REDUCTION.md)
sharpens the second alternative. The incoming head and endpoint can be selected
so that the endpoint has either at least two zero caps, or exactly one zero
observer cap i with J_ip>max(0,Gamma_ip). Here Gamma_ip=Z_i({p}) and
J_ip=Z_i({p,i}); the strict condition requires both a positive participant
reward and a positive joining increment. The new incoming word has at most
eight roots and a positive activity bound uniform as B_i approaches zero from
either sign. Its source proof produces ALL-END and positive original Never
from the native absorbing gap and a strict inverse column. No endpoint
minimality or continuation after an infinite calendar is assumed. In Ratio,
this removes the negative-G observer as the unique-zero positive-pivot
endpoint. Actual minima, the positive-premium single-zero faces, and the
higher-zero faces remain unresolved.

The [incoming boundary controls](CODEX_ROOT__INCOMING_BOUNDARY_CONTROLS.md)
show why the remaining cases need more than a bare carrier lemma. The
positive-premium case can require arbitrarily long words across all incoming
representations, while an open two-zero region contains nonrealized tuples
with no positive finite incoming word at all. Both explicit games are solved;
these are limits of the method, not positive-gap or minimizing examples.

The supporting results preserve original Never coordinates, give an exact
incoming root on a positive-pair subface, and identify the actual head's
precise constraints on every replacement endpoint. An observer active in
the head pins its endpoint cap; an inactive observer imposes a lower bound.
The inherited endpoint is a global minimum of an explicit obstacle objective
on this cap box. This supplies a valid fixed-gain comparison criterion, but
does not produce a compatible improvement for every endpoint. No new UE
reward-table class is asserted. All results are ordinary mathematics, not
new Lean checks.

The added internal geometry results expose the remaining gap more precisely.
Pinned observer caps can freeze all outcome moments of an entire two-owner
head. Actual recurrent pivot contacts persist on an open raw set, so generic
rank alone cannot produce the missing pivot guard. A separate arbitrary-length
curvature/rank argument at a degree1 no-child matrix imposes a conditional
quiet-contact density bound. None supplies a new reward-table UE class or a
completed reward-dependent overlap certificate.

The next concrete question is whether the full selected source admits a
cap-compatible replacement with one fixed positive improvement in J_r.
Vanishing observer errors are acceptable; a gain tending to zero with those
errors is not sufficient.

## Model and inspected interfaces

Use four owners with independent complete stopping laws on the natural
dates and Never. The first nonempty quitting coalition S pays Z(S), with
native Z_i({i})=0 and AllNever0. Write X=(U,B,e,N), where U is prescribed
payoff, B the supremum over all finite deadlines and Never, e the pure
Never response, and N the ORIGINAL marginal Never probabilities. Let H
be the compact closure of these actual tuples. Put d=B-U and nu=product N.
ALL-END means B=e. One unilateral behavioral deviation is a mixture of
deadlines and Never along the unique live history, so B is unrestricted.

The named operational declarations inspected were
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` and
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
Their max-cap and payoff recursions justify literal independent prefixing.
They do not prove the new augmented representation or incoming lemma.

For a root q, let Q_i be the forced-Quit payoff, P_i the passive absorbing
contribution, H_i=product_(j!=i)(1-q_j), and c=product_j(1-q_j). Then

    U'_i=q_i Q_i+(1-q_i)P_i+c U_i,
    B'_i=max(Q_i,P_i+H_i B_i),
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i.                 (1)

The debt recursion is d'_i=R_i+c d_i, where
R_i=max(Q_i,C_i)-q_i Q_i-(1-q_i)C_i>=0 and C_i=P_i+H_i B_i.

## The one-zero head representation preserves the augmented tuple

Let the endpoint Y have B_i(Y)=0 for exactly one observer i, pivot p,
and positive caps at the other observers. Section5 of the canonical
boundary note replaces any inherited infinite head by a finite prefix
followed by at most two diluted geometric clocks of p and i, leaving Y
fixed. Its proof needs the actual positive-survival head and observer
optimality at its cuts, not minimizing status of Y. It therefore applies
to the subcritical source once those data are supplied.

Here is the additional argument for e and N. In the late two-owner head,
let f,g be the finite masses of p,i and a,b,c the probabilities that its
first coalition is {p},{i},{p,i}. Every other head owner uses Never.
Write G=Z_i({p}), J=Z_i({p,i}), A=Z_p({i}), C=Z_p({p,i}). Then

    e_p(head)=A g, e_i(head)=G f,
    e_j(head)=Z_j({p})a+Z_j({i})b+Z_j({p,i})c  (j outside{p,i}).

The canonical moment replacements preserve f,g,a,b,c, and hence this
entire e vector and every original head Never mass. For a fixed tail Y,
the full composition formulas are

    U_l(out)=U_l(head)+s U_l(Y),
    B_l(out)=max(B_l(head),e_l(head)+h_l B_l(Y)),
    e_l(out)=e_l(head)+h_l e_l(Y),
    N_l(out)=N_l(head)N_l(Y),                         (2)

where s=product N_l(head) and h_l=product_(m!=l)N_m(head). The existing
representation proof already preserves U and the full B output; the
displayed equalities prove preservation of e and N as well. The head B
need not be separately preserved when the tail cap dominates. Finite
prefix composition retains all equalities. No finite mass is renamed Never.

ALL-END propagates to every cut of the incoming representation. If
B_p(Y)=0, the late pivot cap is exactly A g, so the strict finite-pivot-cap
subcase of the older representation cannot occur. If B_p(Y)>0, a finite
prefix followed by a single solo-pivot clock suffices. If B_p(Y)=0, use
the persistent-Never two-clock representation, including its degenerate
subcases. Intermediate caps can be negative; endpoint nonnegativity does
not make all earlier conditional caps nonnegative.

For explicit finite calculations, write the two diluted clocks as

    Pr(T_p=t)=f theta(1-theta)^t, Pr(T_i=t)=g u(1-u)^t,
    0<=f,g<1, 0<theta,u<=1, D=theta+u-theta u,
    s=(1-f)(1-g), c=f g theta u/D,
    a=f-c/theta, b=(1-f)g+(1/theta-1)c.

Put b_p=B_p(Y), d=d_p(Y), and nu_Y=product N_l(Y). The exact active-owner
caps and Never offers are

    B_i(out)=f max(G,J theta), e_i(out)=G f,
    B_p(out)=A g+max((1-g)b_p,g(C u-A)),
    e_p(out)=A g+(1-g)b_p.

For example i's deadline t pays G f+(J theta-G)f(1-theta)^t, so its
supremum is the displayed maximum. For f>0, ALL-END requires J theta<=G;
observer i's zero debt requires equality when also g>0. Pivot ALL-END
requires g(C u-A)<=(1-g)b_p. The absent-clock cases drop their vacuous
constraints.

If M>=1 bounds rewards and endpoint caps, the sufficient quiet-observer
buffer 3M(f+g)<min_(j outside{p,i}) B_j(Y) makes every quiet head deadline
smaller than its tail offer. Indeed these deadlines are at most M(f+g),
while the tail offer is at least B_j(Y)-2M(f+g). A late cut of a summable
head provides this buffer. Under these conditions,

    J_r(out)=s(d+r nu_Y)+f(1-g)b_p+f g theta(A-C u)/D.    (3)

For each preceding ALL-END root the exact observer conditions and objective
recursion are

    C_l>=Q_l for all l, q_l(C_l-Q_l)=0 for l!=p,
    J_r(before)=c J_r(after)+q_p(C_p-Q_p).              (4)

Thus a supplied finite prefix and its final clocks admit finite rational
constraints. Endpoint membership in H and a uniform prefix-length bound
are not supplied. Equations(3)--(4) do not license minimizing at Y or
deleting a costly inherited head.

## Exact incoming root on the positive-pair zero face

Let X in H have zero observer debts, B=e, nu(X)>0,
B_p(X)=B_i(X)=0, and B_j(X),B_k(X)>=b>0. Assume

    a=min(Z_p({i}),Z_i({p}),Z_p({p,i}),Z_i({p,i}))>0.

Take M>=1 bounding all rewards and delta=min(1/8,b/(64M)). Then there
are a literal product root q and T in H with

    X=Phi_q(T) in all augmented coordinates,
    sum_l q_l>=delta, q_l<=1-N_l(X)<1, c(q)>=nu(X)>0,
    d_l(T)=0 (l!=p), B(T)=e(T), nu(T)>0,
    q_j+q_k>=a delta/(a+4M).                           (5)

The root is observer-Nash against B(T), and Continue attains every cap.
T need not have nonnegative caps or minimizing status.

Choose actual tuples X_n converging to X. Eventually the j/k caps exceed
7b/8, their prescribed payoffs exceed b/2, and all original Never masses
are positive. Some finite quitting event has probability at least b/(2M),
so cumulative root activity exceeds delta. Let t_n be its first delta
crossing. The prior head has activity h_n<delta. Let E_n be the sum of
j/k hazards on that head.

Throughout this head, j/k caps remain above b/2. Indeed their forced-Quit
offers have absolute value at most M delta; their selected Continue cap
can move by at most 2M times current activity. A first-failure argument
and 2M delta<=b/32 prove the bound. Quit is therefore worse by at least
b/4. Joint head survival is at least1-delta, so the nonnegative debt
recursion gives

    E_n<=8(d_j(X_n)+d_k(X_n))/b ->0.                   (6)

Let f_p,n and f_i,n be p/i finite quitting masses on the prior head. If
that head is nonempty, price i's deadline at its last date. Removing j/k
changes this response by at most2M E_n. Against p alone, every earlier
p atom pays Z_i({p})>=a and the simultaneous last atom pays
Z_i({p,i})>=a. If p has not quit, the payoff is native own-Quit0. Thus

    a f_p,n<=B_i(X_n)+2M E_n,
    a f_i,n<=B_p(X_n)+2M E_n.                         (7)

Both masses tend to zero. All prior marginal survivals are at least
1-delta, giving h_n<=E_n+(f_p,n+f_i,n)/(1-delta)->0. Hence the crossing
root alone has limiting activity at least delta. Positivity of BOTH
singleton and participant-pair coefficients removes the last-atom error.

Let W_n be the actual tuple immediately before that root. Deleting the
vanishing prior head changes U,e,N by o(1). To control zero caps as well,
let h_l,n be prior opponent survival and z_l,n its Never contribution.
Then e_l(X_n)=z_l,n+h_l,n e_l(W_n) and
B_l(X_n)>=z_l,n+h_l,n B_l(W_n), so

    0<=h_l,n(B_l(W_n)-e_l(W_n))<=B_l(X_n)-e_l(X_n)->0.

Since h_l,n->1, all B coordinates also converge, and W_n->X as full
augmented tuples. Take a convergent crossing root q_n->q and a compact
subsequence of its actual tails T_n->T. Continuity of (1) gives X=Phi_q(T).
Original Never gives N_l(X)<=(1-q_l), so c(q)>=nu(X)>0. The debt and
END-gap recursions imply observer feasibility and ALL-END for T, observer
Nash for q, and positive original Never in T.

Finally put z=q_j+q_k. If z<=1/2, positivity of the participant pair
reward gives Q_p(q)>=a q_i(1-z)-M z. But Q_p(q)<=B_p(X)=0, hence
q_i<=2M z/a. Likewise q_p<=2M z/a. Therefore
delta<=sum q<=z(1+4M/a), proving the final bound in (5). If z>1/2 that
bound holds immediately. Some positive-cap observer is necessarily active.

## Why the global composition step remains open

Suppose the selected source is Phi_P(X) with an ACTUAL infinite head P
and X as in (5). The identity Phi_P(Phi_q(T)) is valid semantically.
It does not provide an actual head obtained by playing q after P: that
would place a date after infinitely many dates. Finite truncations of P
followed by q have original Never tending to N(P)(1-q), while their
ordinary early-clock limit can retain original Never N(P). Actual-head
realization is therefore not preserved by the bare composition identity.

Allowing arbitrary compact limits of prefix operators loses the same
information. Every augmented carrier point is already a limit of finite
prefixes applied to AllNever. Maximizing a tail Never coordinate over
that larger factorization class can terminate at AllNever while all
nonrealization remains in the head. That does not contradict the actual-
head source theorem. A valid new selection must preserve its realization
requirement or supply a separate global improvement consumer.

The cap-box result below identifies exactly which endpoint replacements
compose to observer-feasible carrier points and retain a fixed improvement.
Producing such a replacement, or changing the head to release its pinned
caps, remains open.

## Exact global endpoint optimization induced by an actual head

### Source and notation

Use native own-singleton and AllNever rewards zero, bounded in absolute
value by M>=1. Independent complete stopping laws and all behavioral
replacements have the payoff/cap meanings stated in
quittingStoppingLawExpectedPayoff and quittingStoppingLawReplacementPayoffCap
(UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean).
The literal prefix and complete max-cap recursions inspected were
quittingTerminalSemanticPair_rootThenContinuation
(UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean) and
quittingContinuationBestResponseValue_rootThenContinuation_eq_max
(UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean).

Let H be the compact augmented actual-law carrier (U,B,e,N), C its zero
observer-debt subset, and nu=product N. Fix r>0 and a global minimum
Y in C of J_r=d_p+r nu, with value mu>0. Suppose the given source supplies

 Y=Phi_P(Q), Q in C, N_i(P)>0, N_i(Q)>0, B(Q)=e(Q)>=0,
 B(Y)=e(Y), delta=B_p(Y)-mu>0,

where P is an ACTUAL complete-law head. Phi_P is the retained-query head
map, not execution of Q after an infinite time. Write

 n_i=N_i(P), h_i=product_(j!=i)n_j, s=product_i n_i,
 a_i=[B_i(P)-e_i(P)]/h_i, A={i!=p:n_i<1}.

Every a_i>=0: finite deadlines against an actual native head tend to its
Never payoff, so B_i(P)>=e_i(P).

### Exact preimage of observer feasibility

For every R in H the head map has

 U_i(Phi_P R)=U_i(P)+s U_i(R),
 B_i(Phi_P R)=max(B_i(P),e_i(P)+h_i B_i(R)),
 N_i(Phi_P R)=n_i N_i(R).                                  (H1)

These maps send H into H. To construct approximants, truncate P at a large
finite date, insert an empty query date, and append actual approximants to R.
The remaining finite head mass tends to zero; the uniform replacement-payoff
coupling bound controls full caps. The resulting augmented tuples tend to
(H1), preserving ORIGINAL Never coordinates n_i N_i(R). This comparison
construction does not assert an actual infinite-head concatenation.

For an observer i in A, some finite P_i atom has positive mass. Writing
alpha_t for its finite head atoms and V_t for their deadline values gives

 U_i(Y)=sum_t alpha_t V_t+n_i[e_i(P)+h_i U_i(Q)].

Every term is bounded by B_i(Y), including the bracket, because Q is
observer-optimal. Equality forces every positive-weight head deadline and
the bracket to attain B_i(Y). This remains valid when Y is nonrealized.
Each finite head deadline value is independent of Q.
Thus B_i(P)=B_i(Y)=e_i(P)+h_i B_i(Q), so

 a_i=B_i(Q),  U_i(P)=e_i(P)+(1-n_i)h_i a_i.                 (H2)

For i notin A, U_i(P)=e_i(P), and source ALL-END gives a_i<=B_i(Q).
Using (H1)--(H2), with b_i=B_i(R) and d_i=d_i(R), gives the exact debts

 d_i(Phi_P R)/h_i
   =max(a_i,b_i)-(1-n_i)a_i-n_i b_i+n_i d_i  (i in A),
   =max(a_i,b_i)-b_i+d_i                    (i notin A).    (H3)

In the first row, the cap term is (1-n_i)(b_i-a_i) if b_i>=a_i,
and n_i(a_i-b_i) if b_i<=a_i. All terms are nonnegative, and n_i>0.
Therefore

 Phi_P(R) in C iff R in C and
 B_i(R)=a_i for i in A,
 B_i(R)>=a_i for i notin A, i!=p.                         (H4)

This is an exact equivalence over the whole carrier, not a sufficient
component-preserving condition. An observer who ever quits in the head
FREEZES its endpoint cap. An observer who always waits imposes only a lower
bound, which may be strict at Q.

### The endpoint is a genuine minimum of an explicit obstacle objective

Define the compact cap box C_P by the right side of (H4), and put

 F_P(R)=max(a_p,B_p(R))/n_p-U_p(R)+r nu(R).                 (H5)

The full source objective is exactly

 J_r(Phi_P R)=e_p(P)-U_p(P)+s F_P(R).                      (H6)

Consequently Q is a GLOBAL minimum of F_P on C_P. All data in C_P and F_P
are produced by the actual head P. Since source Y is ALL-END, B_p(Q)>=a_p.
The pivot cap is amplified by 1/n_p; even below a finite head cap it is
replaced by the fixed obstacle a_p. Neither modification can be dropped.

### A global head-activity collar

Put f=1-n_p, H_p=product_(i!=p)n_i, epsilon=1-H_p. For f>0 let W be the
pivot's expected head reward conditional on its finite head draw. If all
observers draw head Never, its outcome is its own singleton and pays zero.
Independence therefore gives |W|<=M epsilon. The conditional head-Never
branch followed by Q has pivot payoff B_p(Y)-H_p d_p(Q). Hence

 mu=f[B_p(Y)-W]+n_p H_p J_r(Q).                           (H7)

Since Q in C, global minimality gives J_r(Q)>=mu. Rearranging (H7) yields

 f delta <= epsilon [f M+n_p mu],
 epsilon >= f delta/[f M+n_p mu]  when f>0.               (H8)

In particular, a nonempty head containing ONLY pivot activity is impossible
at this global source. This uses the strict GLOBAL margin delta, so it is
not contradicted by actual-head/nonrealizable-composite controls that fail
minimization. For f=0 the assertion is vacuous. The bound does not remove
finite observer activity in an otherwise infinite pivot head.

### Exact whole-source consumer for a one-zero solo prefix

Assume Q has exactly one zero-cap observer i and B_p(Q)>0; the other two
observer caps are positive. Set b_j=B_j(Q), z=J_r(Q)>=mu>0 and L=Gamma_pi.
For sufficiently small t>0, prefix Q by the literal solo-i root of hazard t.
Call the result Q_t. Observer i is indifferent at zero, and every other
owner strictly prefers Continue for small t. Thus Q_t lies in C and is
ALL-END, with

 B_i(Q_t)=0,
 B_j(Q_t)=b_j+t(Gamma_ji-b_j) for j!=i,
 U_p(Q_t)=U_p(Q)+t(L-U_p(Q)), nu(Q_t)=(1-t)nu(Q).

It belongs to the head box C_P for all sufficiently small t>0 EXACTLY when

 Gamma_ji=b_j for every positive-cap observer j in A;
 Gamma_ji>=b_j for every positive-cap observer j notin A with b_j=a_j.
                                                               (H9)

Strict lower-bound coordinates impose no condition for sufficiently small t.
The zero observer coordinate remains zero automatically. This failure is
quantitative, not removable by taking actual approximants: for a positive-cap
observer j put Delta_j=Gamma_ji-b_j. Its exact whole-source debt is

 h_j t [(1-n_j)(Delta_j)^+ + n_j(-Delta_j)^+]    if j in A,
 h_j t (-Delta_j)^+                            if j notin A, b_j=a_j,
 0                                            if j notin A, b_j>a_j,
                                                               (H9a)

for all sufficiently small t. Therefore, if (H9) fails, some fixed c>0
satisfies max_observer d_j(Phi_P(Q_t))>=c t. Any such solo-prefix sequence
with observer errors tending to zero must have t tending to zero, and its
whole-source objective improvement also tends to zero by continuity.
It cannot meet the fixed-positive-gain source requirement. This is an exact
obstruction at the genuine minimizing source, not a nonglobal control.

Let Delta=L-b_p.
The exact small-t change in (H5) is t D, where

 D=(1/n_p-1)Delta-z                    if b_p>a_p,
 D=max(0,Delta)/n_p-Delta-z             if b_p=a_p.         (H10)

Thus (H9) and D<0 contradict global minimality. Choose any fixed admissible
small t. Equations (H4)--(H6) give a carrier point with J_r=mu+s t D<mu;
its actual approximants have observer debts tending to zero and objective
gain tending to -s t D>0. In particular, all sufficiently late approximants
have gain at least -s t D/2. This meets the fixed-gain source requirement.
There is no post-omega execution or vanishing-gain substitution.

For example, b_p>a_p and L<=b_p imply D<=-z<0. At the obstacle b_p=a_p,
the interval b_p-z<L<=b_p still gives D<0. In general the exact condition
is (H10). A local decrease J_r(Q_t)=(1-t)z alone does not suffice: the head
may freeze a changing observer cap or amplify the changed pivot cap.

With an empty head, n_p=1, a=0, A empty, and positive b_p, (H9) is automatic
and D=-z. Hence a GLOBAL selected minimum itself cannot have exactly one
zero observer cap. An inherited one-zero endpoint remains possible only
because a genuine head imposes the additional box/obstacle restrictions.

### Remaining gap

The theorem does not produce a direction satisfying (H9)--(H10) for every
inherited endpoint, nor a replacement of the head that changes these rigid
cap constraints. If a positive-cap observer quits in the head, (H9) can
fail outright, even though the endpoint solo prefix is a strict descent.
The useful new datum is the exact constrained global extremality (H5), not
an assertion that the endpoint minimizes its old J_r.

## Uniform obstruction to small repairs with a fully pinned head

Use native own-zero rewards bounded by M>=1, pivot p, and the compact
augmented actual-law carrier. Let Q be observer-optimal, ALL-END, with all
caps b_i>=0 and positive original Never. Let an actual head P satisfy
Y=Phi_P(Q), with Y observer-optimal, N_p(P)>0, and 0<N_i(P)<1 for observers.
Thus all three observer endpoint caps are pinned by the old head. Write
Z={i!=p:b_i=0}, K={p} union Z, and A_ik=Gamma_ik-b_i for i!=p,k in K.
Assume ker(A) intersects the nonnegative orthant only at0.

There are beta0,C>0 such that every actual independent head R with marginal
finite masses f_i=1-N_i(R), beta=sum_i f_i<=beta0, satisfies

 beta <= C epsilon,  epsilon=max_(i!=p) d_i(Phi_P(Phi_R(Q))).       (S1)

The heads may have arbitrary countable supports, atoms or coincidences.
Phi_R is the retained-query semantic head map; no post-infinite play is
asserted. For every fixed r>=0 the absolute change of the whole-source
objective d_p+r nu is at most (4M+r) beta. Consequently such small heads
cannot yield a fixed positive gain while their observer errors tend to0.

Proof. Set W=Phi_R(Q), n_i=N_i(P), h_i=product_(j!=i)n_j. The exact old-head
debt identity, obtained by subtracting its prescribed payoff from its
max-cap formula, is

 d_i(Phi_P W)/h_i=(1-n_i)(B_i(W)-b_i)^+
                    +n_i(b_i-B_i(W))^+ +n_i d_i(W).

Every term is nonnegative. Since 0<n_i<1, this bounds both
|B_i(W)-b_i| and d_i(W) by C0 epsilon for every observer.
Let T_i=e_i(R)+H_i(R)b_i be the through-head response value. A finite head
deadline has absolute payoff at most M beta: absent another finite head
draw it produces the owner's singleton0. Also |T_i-b_i|<=2M beta.
Decomposing the prescribed law into finite draws and its Never draw gives

 d_i(W)>=(1-f_i)(B_i(W)-T_i),
 d_i(W)>=f_i(T_i-M beta).

For every positive-cap observer, beta sufficiently small makes
T_i-M beta>=b_i/2, hence f_i<=C1 epsilon. The first inequality, beta<=1/2,
and the cap bound give |T_i-b_i|<=C2 epsilon for all observers.

Uniformly over the whole head calendar, independence gives
e_i(R)=sum_(j!=i)Gamma_ij f_j+O(M beta^2) and
H_i(R)=1-sum_(j!=i)f_j+O(beta^2): all discrepancies require at least two
opponents to have finite head draws. Therefore
T_i-b_i=sum_(j!=i)(Gamma_ij-b_i)f_j+O(M beta^2).
Discarding the O(epsilon) masses of positive-cap observers yields
|A f_K|<=C3(epsilon+beta^2). Compactness of the nonnegative unit simplex
and the kernel assumption give |A x|>=c|x| for x>=0. Thus
beta<=C4(epsilon+beta^2), and decreasing beta0 absorbs the quadratic term,
proving(S1). These estimates also pass to limits retaining the original f.

Finally |U(W)-U(Q)|,|B(W)-B(Q)|<=2M beta and |nu(W)-nu(Q)|<=beta;
nonnegative b prevents the retained head cap from introducing a fixed jump.
The old head map is nonexpansive in each payoff/cap coordinate and multiplies
nu by at most1, proving the objective bound. No global minimizing property
was used. For |Z|<=2, full column rank of A is a sufficient open condition;
this lemma does not assert that every inherited endpoint satisfies it.

## Conservative exceptional cycles can have positive curvature on every closed tangent loop

Internal mechanism boundary only. Its positive-pivot singleton chamber is
already degree zero and excluded by the existing source screen. No actual
global minimum, absorbing gap, or Fin4 counterexample is asserted. This explains why the [global rigidity theorem](../revisit/ACTUAL_MINIMUM_GLOBAL_PAIR_STAR_RIGIDITY.md)'s
generic exception should not be silently erased by a second-variation claim.

Take p=0, G=(-1,1,1), and

 c=[0,3/2,1/2; 5/2,0,3; 3/4,5/4,0],
 h=(1,1/3,7), lambda=(1/8,1/3,1/2), rho_i=1/(1-lambda_i).

Set Gamma_ip=G_i, Gamma_pi=h_i, Gamma_ij=-G_i c_ij, and
J_ip=rho_i G_i. Choose pivot participant pairs

 J_p=(-124909/1827,-91201/3654,-164954/1827).

Then all Raw conditions hold. Since c^-1 1=(22,50,8)/79>0, the inverse pivot
column is strictly positive. At penalty r=0 the three coefficients are

 A=(-15581/261,-90592/5481,-152165/3654)<0.

For the periodic observer word123123..., compute its periodic pivot memories
pi^i and v^i=sum_j pi_j^i c_j as defined in that theorem. The resulting price
matrix S is exactly symmetric. Its diagonal memory values are

 R=(v_1^1,v_2^2,v_3^3)=(58/47,267/188,103/47)>0.

Write k_i=-A_i>0 and z=x_p-v^i dot y before a phase-i date. Exactly

 z_next=lambda_i z+lambda_i R_i u_i.

The full quadratic supply at that date is (S y)_i u_i+k_i z u_i.
Because S is symmetric, a closed observer path has

 sum (S y)_i u_i=(1/2)sum S_ii u_i^2
                         =(1/2)sum k_i R_i u_i^2.

Thus each residual contribution becomes the scalar difference of squares

 k_i z u_i+(k_i R_i/2)u_i^2
       =[k_i/(2R_i)](z_next^2/lambda_i^2-z^2).

For a complete closed state loop, z starts and ends at zero. Therefore

 Q_0=(1/2)sum_t b_(phase t) z_t^2,
 b_i=k_(i-1)/(R_(i-1)lambda_(i-1)^2)-k_i/R_i,

where predecessor labels are cyclic. Here the exact three coefficients are

 b_1=301610233/10914498>0,
 b_2=130899543584/42439383>0,
 b_3=2871940781/33496218>0.

Consequently EVERY nonzero finite closed contact tangent loop along this
periodic word has strictly positive Q_0. Indeed equality forces all z_t=0,
then the scalar recurrence forces every u_i=0 and every pivot tangent0.
This concerns the full multilabel fibre, not only a fixed short window.

The other reward entries may be set arbitrarily for this algebraic boundary:
zero-penalty curvature uses only the displayed singleton and participant
pair data. Their choices may create absorbing exits or prevent actual quiet
feasibility; none of those strategic questions is resolved by this example.
Generic reward perturbation remains available in the positive-gap argument,
so this obstruction does not weaken the generic theorem.

Exact reproducer:

```python
import sympy as s
c=s.Matrix([[0,s.Rational(3,2),s.Rational(1,2)],
 [s.Rational(5,2),0,3],[s.Rational(3,4),s.Rational(5,4),0]])
h=s.Matrix([1,s.Rational(1,3),7]);la=[s.Rational(1,8),s.Rational(1,3),s.Rational(1,2)]
A=s.Matrix([-s.Rational(15581,261),-s.Rational(90592,5481),-s.Rational(152165,3654)])
p=s.Matrix(s.symbols('p0:3'));pn=p
for i in range(3):pn=la[i]*pn+(1-la[i])*s.eye(3)[:,i]
pn=p.subs(s.solve(list(pn-p),list(p),dict=True)[0]);S=s.zeros(3);R=[]
for i in range(3):
 v=pn.T*c;R.append(v[i])
 for j in range(3):S[i,j]=A[i]*(c[i,j]-v[j])+h[j]*c[j,i]
 pn=la[i]*pn+(1-la[i])*s.eye(3)[:,i]
assert S==S.T
assert c.inv()*s.ones(3,1)==s.Matrix([22,50,8])/79
energy=[-A[i]/R[i] for i in range(3)]
b=[s.factor(energy[(i-1)%3]/la[(i-1)%3]**2-energy[i]) for i in range(3)]
assert b==[s.Rational(301610233,10914498),s.Rational(130899543584,42439383),s.Rational(2871940781,33496218)]
assert all(z>0 for z in b)
Jp=[s.factor((A[i]-h[i]*la[i])/(1-la[i])) for i in range(3)]
assert Jp==[-s.Rational(124909,1827),-s.Rational(91201,3654),-s.Rational(164954,1827)]
print('PASS: conservative Raw price and strictly positive all-loop square coefficients.')
```

## Three pinned observer caps can freeze every late two-owner head outcome

Internal exact obstruction to a head-variation route. It does not close the
nonrealized branch and is not proposed for export. Unlike the small-new-head
bound, this concerns arbitrary replacements of the existing late head.

Let Y=Phi_F(Phi_H(Q)) be an ALL-END global minimum source, where F is a
finite actual prefix with positive survival, H is an actual positive-Never
head using only pivot p and observer i, and Q has positive original Never,
zero observer debts, ALL-END, and endpoint cap b_i=0. The remaining observers
are j,k. Assume all three observers have some activity in F. Then the exact
head-box theorem pins all three observer caps at the exit of F, equivalently
at the entrance to H. Explicitly, each observer has a used finite F deadline
whose value depends only on the fixed F laws. Observer optimality pins its
global cap to that fixed deadline value. The original ALL-END identity
B_l(global)=e_l(F)+H_l(F)B_l(after F), with H_l(F)>0, then pins the
after-F cap. The exact head-box equality gives the same conclusion for every
observer-feasible replacement, even if its pivot ceases to be END-optimal.

Fix F and Q. Consider ANY alternative actual head H' using only p,i, with
both marginal Never masses positive, such that Phi_F(Phi_H'(Q)) has zero
observer debts. The heads may have countable supports and arbitrary ties.
The head maps are limits of actual finite truncations with the original
Never coordinates retained; no play after an infinite date is asserted.

Write G=Gamma_ip!=0, rho=J_ip/G. Let f,g be the finite marginal masses of
p,i in H'; let a,b,c be its first-coalition probabilities for {p},{i},{p,i}.
Then a+b+c=f+g-fg. Set X=Phi_H'(Q).

Zero observer debt passes through F to X. Positive marginal Never at X
implies every observer is END-optimal, including at semantic carrier points
by d_l>=N_l(B_l-e_l). Observer i's Never payoff is G f,
while its prescribed payoff is G a+J_ip c, since U_i(Q)=b_i=0. Therefore

 B_i(X)=G f,  a=f-rho c,
 b=(1-f)g+(rho-1)c.                                      (1)

For l in {j,k}, put

 K_l=Z_l({p,i})-rho Gamma_lp+(rho-1)Gamma_li,
 a_l=Gamma_li-b_l.

The actual first-coalition expansion gives the exact observer caps

 B_l(X)=b_l+f(Gamma_lp-b_l)+(1-f)g a_l+c K_l.              (2)

These identities use only original finite masses and actual first-coalition
probabilities. They do not assume geometric clocks or positive intermediate
caps. In particular they apply to the canonical at-most-two-clock head.

### Exact rigidity

If

 D=a_j K_k-a_k K_j !=0,                                  (3)

every such observer-feasible replacement has exactly the same f,g,c as H.
Indeed the pinned i cap first fixes f by (1). With t=(1-f)g, the two remaining
pinned caps give the invertible linear system

 [a_j K_j; a_k K_k] [t;c]
   =[B_j(X)-b_j-f(Gamma_jp-b_j);
     B_k(X)-b_k-f(Gamma_kp-b_k)].                         (4)

Its right side is fixed by F and Q. Thus t,c, and hence g, are fixed.
Equations(1) also fix a,b. The prescribed pivot payoff and its Never offer are

 U_p(X)=Gamma_pi b+Z_p({p,i})c+(1-f)(1-g)U_p(Q),
 e_p(X)=Gamma_pi g+(1-g)b_p.                              (5)

They are fixed, as are every original Never coordinate and all observer
payoffs/caps. The old X was pivot-END, so every replacement satisfies
B_p(X)>=e_p(X)=B_p(X_old). The prefix map's pivot cap is monotone in that
endpoint cap, while its prescribed payoff and Never mass are unchanged.
Consequently

 J_r(Phi_F(X))>=J_r(Y) for EVERY r>=0.                    (6)

This is an exact global obstruction, not merely a first-order stationarity
condition. Head changes can vary timing, support size, ties, geometric
rates, and finite masses in their proposal; observer feasibility forces all
payoff-relevant moments back to their original values.

### One-clock specialization and limitation

When b_p>0, the canonical late head may use only the pivot. Then g=c=0 and
B_l(X)=b_l+f(Gamma_lp-b_l). Its clock rate does not affect the retained tuple.
Any pinned observer cap with Gamma_lp!=b_l fixes f. If i is pinned, G!=0
already supplies that condition.

The assumption that F contains all three observers is substantive. It holds
whenever all three occur in the whole actual head and the cut is chosen
later than one occurrence of each. It is not supplied for every source.
Condition(3) depends on the inherited endpoint caps b_j,b_k; no claim that a
generic reward perturbation forces it for every endpoint is made.

The useful conclusion is that, in this nondegenerate fully pinned case,
replacing the entire late two-owner head while fixing F and Q cannot improve
the objective at all. A successful global comparison must change the earlier
finite prefix, change Q, leave the two-owner support, or reach a different
cap stratum. The finite-prefix variation problem remains open.

### Simultaneous endpoint solo-prefix does not bypass these pins

Let Q_t be the literal solo-i prefix of Q with hazard t, assuming it is
observer-feasible (in particular this holds for small t when b_p>0 and
the other two observer caps are positive). Replace H simultaneously by an
arbitrary observer-feasible two-owner H' before Q_t, keeping F fixed.
Write f,g,c for H'. The retained composition has the same first-coalition
accounting as a two-owner head before Q with effective masses

 f_eff=f,  g_eff=g+(1-g)t,  c_eff=c.                       (7)

Indeed an i exit from the added root occurs only after both head owners
chose Never, increasing the solo-i first-coalition probability by
(1-f)(1-g)t. Observer i still has endpoint payoff/cap0, so(1)--(5) apply
with g_eff in place of g. No actual realization of the composed infinite
head is needed for these semantic identities; finite truncation comparisons
supply the retained tuple. Under(3), pinned caps fix f_eff,g_eff,c_eff.
Hence the pivot objective again cannot decrease.

If the old late head is pivot-only, its effective g is0. For any t>0,
g_eff=g+(1-g)t>0 for every admissible g>=0, so no such simultaneous
replacement is observer-feasible through F at all. Thus the tempting
endpoint solo-zero descent cannot be rescued merely by readjusting the
canonical late head. The preceding finite prefix itself must change.

## Actual recurrent pivot contact survives local genericity

This is an internal boundary for a proposed pivot-guard producer, not a
Fin4 exclusion or counterexample. It uses a degree-one singleton matrix
with strictly positive inverse, negative passive-deletion rows, and no
singleton stationary absorbing equilibrium. Other stationary supports and
all implemented full-table UE consumers have not been excluded. No positive
absorbing gap or global source minimum is asserted.

The conclusion is stronger than a tangent example: there is an actual
positive-Never, ALL-END Nash tail with cyclic pair supports 01,02,03, every
pivot comparison tied, and every inactive observer comparison strict.
The construction persists in an open neighborhood of its24 raw rewards.
All fixed finite values of the other32 rewards are allowed, with a smaller
tail parameter when needed.

### Explicit raw data and bounded source screens

Use native own-singleton zero and

    Gamma=[0,5,-1,-1; -2,0,1,1; 2,-1,0,-1; 2,-1,-1,0],
    J=[0,-12,-15/4,-13/4; -6,0,2,5/2;
       15/2,1,0,-11/10; 13/2,1,-1/2,0].

Here Gamma_ij is the reward to i when only j quits, and J_ij is the
reward to i when exactly i,j quit. Gamma has determinant6 and a strictly
positive inverse. Every principal of size at least two is nonsingular,
every column has a negative entry, and the sole complementary root at
offset minus the all-ones vector has full support and positive index.
Thus Gamma is R0 of degree one. Every omitted-player row multiplied by
the corresponding triple inverse is strictly negative; hence the simple
passive-triple inheritance test does not apply.

A singleton stationary absorber j with hazard q requires
Gamma_ij>=J_ij q for every i!=j and0<q<=1. All four owners fail: owner0
would need q>=1/3 and q<=4/15; owner1 faces Gamma_21<0<J_21; owner2
would need q>=2; owner3 needs q>=10/11 and q<=2/5. These tests are strict
and therefore survive small raw perturbation. They are bounded screens,
not a claim that this complete table has no known UE.

For comparison with the signed-pivot timing calculation, put
lambda_i=1-Gamma_i0/J_i0. They are2/3,11/15,9/13, and

    C_i=Gamma_0i lambda_i+J_0i(1-lambda_i)
       =(-2/3,-26/15,-22/13).

Thus all three timing coefficients are negative. Recurrent pivot ties
are compatible even with that strict sign choice.

### Exact analytic contact dynamics

Let E be a supplied four-dimensional Never-cap vector at one date whose
support is{0,i}. Impose both active contacts by setting

    q_0=E_i/J_i0,  q_i=E_0/J_0i,  q_j=0 otherwise.             (1)

The two active Quit offers are exactly E_0,E_i. Let A_j(q) be the immediate
absorbing payoff to a continuing player j, and
H_j(q)=product_(k!=j)(1-q_k). Define the rational map

    Phi_i(E)_j=[E_j-A_j(q)]/H_j(q).                          (2)

This is analytic near0 for every fixed finite completion of the table.
Its derivative is

    T_i=I-Gamma[:,0] e_i^T/J_i0-Gamma[:,i] e_0^T/J_0i.       (3)

The three-date map F=Phi_3 Phi_2 Phi_1 has derivative T=T_3T_2T_1 with

    det(zI-T)=(z-1)^2(65z-22)(260z-187)/16900.

Set rho=187/260 and

    v=(-1,-1360/5913,7561/5913,6337/5913).

Then Tv=rho v. At the three successive linear phases, the supported hazard
pairs (pivot,observer) are

    (680/17739,1/12),
    (18241/106434,17/45),
    (1185019/6918210,187/585).

Every supported hazard is positive. At phases1,2,3, respectively, the two
quiet gaps E_j-(Jq)_j, with observers ordered increasingly, are

    (21473/23652, 52451/70956),
    (10591/88695, 40783/266085),
    (278443/6918210, 12716/1330425).

All are strictly positive, so these inequalities hold on a cone around the ray.

The pivot scalar recurrence on any tied pair date is particularly simple:

    E_0^next=E_0(1-Gamma_0i/J_0i)/(1-E_0/J_0i).             (4)

Here its three linear factors are17/12,11/15,9/13, with product rho<1.
Hence a blanket expansion argument cannot forbid the tied calendar.

### Actual realization, including the convergence argument

There is a real analytic curve E(t)=tv+O(t^2), defined for sufficiently
small |t|, satisfying

    F(E(t))=E(rho t).                                      (5)

For completeness this follows without assuming an actual tail. Write
F(x)=Tx+N(x), N=O(|x|^2), and E(t)=tv+h(t), with h having no constant or
linear term. Its equation is

    h(rho t)-T h(t)=N(tv+h(t)).                             (6)

For every integer n>=2 the matrix rho^n I-T is invertible. Its possible
eigenvalues are1,rho,22/65: the first two are immediate exclusions, and
rho^n cannot equal22/65 because its reduced numerator has a prime17
factor while22/65 does not. Moreover the inverse norms are uniformly
bounded in n, since rho^n tends to0 and T is invertible. On the Banach
space of absolutely convergent vector power series on a sufficiently
small disk, with zero constant and linear terms, the coefficientwise
inverse of the left side of(6) is therefore bounded. The right side has
Lipschitz constant O(disk radius) on the ball |h|=O(radius^2). The
contraction theorem proves(5), including convergent coefficients. Real
coefficients give a real curve. The same proof works in a small raw
neighborhood: rho remains a simple positive eigenvalue, the finitely many
potential resonances stay separated, and the remaining powers approach0
uniformly. The strict hazard and quiet-gap signs also persist.

Start a tail at E(t), t>0 small. Apply(1),(2) successively for labels1,2,3,
then repeat from E(rho t), E(rho^2 t), and so on. All supported hazards are
positive and less than1, all quiet hazards are zero, and the total sum of
hazards is finite, since every cycle has size O(rho^n t). Thus the hazard
sequence defines independent complete laws with positive original Never
mass for every player. The supplied E vectors tend to0. Iterating(2) and
using bounded convergence therefore identifies them with the actual
conditional Never payoffs of these laws.

At every date both active players are tied and every inactive player has
Quit offer strictly below its supplied Never value. Iterating the exact
Continue recursion bounds every deterministic finite deadline by E; the
actual Never reply attains E. Private randomized deviations are mixtures
of such deadlines and Never, so the unrestricted cap is exactly E.
The prescribed laws use only tied finite dates and Never, hence each
prescribed payoff also equals E. This proves ALL-END and Nash optimality
for all four players, not just observer optimality. In particular the
pivot debt is zero throughout this tail.

This actual construction is a boundary for a generic contact-rank claim.
It does not make the resulting profile a minimum of d_0+r nu, nor show
that an actual positive-gap source can possess this particular tail.


## Arbitrary-length curvature and regularity at a no-child point

Independently reviewed internal theorem. It concerns finite variations of
a supplied actual minimum, not an arbitrary-game producer. Completion-dependent
overlap has not been certified; this result is not an accepted export.
The degree-zero chamber is not used. Double quiet contacts and pivot contacts
remain outside the regularity conclusion.

Use pivot0 and

    Gamma=[[0,1,2,-1],[-1,0,-1,2],[1,-1,0,1],[1,1,-1,0]],
    rho=(3,15/4,13/4), J_i0=rho_i Gamma_i0, J_0i=-1.

This matrix has determinant11, inverse column0=(1,4,5,3)/11, degree1,
and no inverse-positive principal triple. These singleton screens alone
do not certify failure of completion-dependent equilibrium producers. Quiet-participant rewards J_ji (i,j observers,
i!=j) do not enter the active-contact dynamics or the zero-penalty Hessian.

### Exact periodic transfer symbol

At date k with label i, let x_k be the remaining signed atom vector and u_k
the observer atom tangent. Fixed entrance/final caps give x_0=x_N=0. The
active observer contact and state update are

    a_k=Gamma_i x_k/(rho_i Gamma_i0),
    x_(k+1)=A_i x_k-u_k e_i,
    A_i=I-e_0 Gamma_i/(rho_i Gamma_i0).

For a cyclic123 period, T=A_3 A_2 A_1 has observer block identity and

    T_00=a=22/65, T_0,obs=(-8/65,9/65,2/13).

Let X_n be the three observer state coordinates at period entrance, with
u_(i,n)=X_(i,n)-X_(i,n+1). A harmonic z^n input gives

    p(z)=sum_i [T_0i+B_i0(1-z)] X_i(z)/(z-a),
    B_1=-A_3 A_2 e_1, B_2=-A_3 e_2, B_3=-e_3.

All subsequent within-period states follow the displayed updates. On a
closed loop the zero-penalty pivot-debt quadratic is exactly

    D=sum_k a_k[Gamma_0 x_k-J_0i u_k].

Form its Hermitian symbol S(z) by substituting the harmonic states and
symmetrizing the real quadratic. Put P(z)=|z-a|^2 S(z). It is a Hermitian
Laurent polynomial of degree at most2. Direct expansion of the displayed
rational transfer formulas gives

    P_11=116(2-z-z^-1)/4225,
    P_22=87(2-z-z^-1)/845,
    P_33=29(2-z-z^-1)/195,

    det P=(z-1)^4(22z-65)^2(65z-22)^2
             *(24336z^2-55465z+24336)/(12217860281250 z^5).

For |z|=1,z!=1, the determinant is strictly negative: its nontrivial last
factor is 24336(z+z^-1)-55465<=48672-55465<0, while the other factors have
positive real product after the displayed powers of z are removed. A positive
diagonal entry rules out three negative eigenvalues. Hence S has EXACTLY
one negative and two positive eigenvalues at every nonzero frequency.

The signature persists in one raw neighborhood, uniformly in frequency.
For real coefficient data, P(1)=0; diagonal entries are even in frequency
and therefore divisible by 2-z-z^-1. The real even determinant is O(theta^3)
and hence O(theta^4), so is divisible by (2-z-z^-1)^2. The normalized diagonal
and determinant functions extend continuously across z=1. Their strict
signs at the reference point and compactness of the circle supply a single
parameter neighborhood retaining the signature. This avoids length-by-length
continuity and does not extrapolate finite LDL tests.

### A finite-loop index bound with an absolute boundary loss

Choose a real three-vector sequence Y supported on periods1,...,L. Set
X=(shift-a)Y. The numerator formula for p then makes p finitely supported
too. Both x and p vanish at periods-1 and L+1, so these sequences embed
injectively into closed active-contact loops on m=L+2 periods.

Their quadratic is the L-block Toeplitz form of P. Compare it with the
L-block circulant of the same degree2 Laurent polynomial. The difference
is supported on the first and last two block coordinates, so has rank<=12.
The circulant has one negative direction at each nontrivial Fourier mode
and none at mode1: its negative index is L-1. Real Fourier conjugate pairs
have their usual doubled real dimension. Thus the closed-loop debt form on
N=3m dates has negative index at least

    L-1-12=m-15.

The constant is a boundary allowance, not a new finite-window optimization.
The same argument gives the asymptotic lower density1/3 for all lengths.
Cyclic changes of phase give unitarily congruent harmonic forms and the
same conclusion, or may be handled by removing at most two boundary dates.

For a fixed finite assignment of the other rewards, the fixed-penalty
augmented Hessian has the same construction for all sufficiently small r.
Indeed, in absolute atoms it is D+r sum_i w_i P_i^(2), where
w^T=1^T Gamma^-1 and P_i^(2) is the quadratic Never payoff. Explicitly

    P_i^(2)=sum_k sum_(j<l; j,l!=i)
      [-Gamma_il v_jk x_lk-Gamma_ij v_lk x_jk+Z_i({j,l})v_jk v_lk].

There is at most one pivot factor per term, so clearing z-a still gives
Laurent degree<=2. At z=1 observer atoms vanish and the pivot atoms sum to
zero over the period; thus this symbol also vanishes at1. The same normalized
continuity proof gives one table-dependent r0>0 and one raw neighborhood,
independent of m. Joint Never has zero quadratic coefficient on closed
absolute-atom loops. Its cap-multiplier correction is exactly the displayed
r-weighted Never term. No uniform bound on other rewards is asserted.

### Produced rank for all single-quiet masks below density1/3

Take N=3m, m>=2, in any phase. Let S be ANY quiet-contact slot set with
at most one slot at each date and |S|<=m-1. The complete rows consisting of
four entrance caps, N active observer contacts, and the |S| quiet contacts
are generically independent in the six quiet-participant coordinates.

Proof: set all six quiet-participant J_ji=T and let T tend to infinity.
After dividing a quiet row by T its leading row is precisely u_k. It
suffices to prove the endpoint map has rank4 after all these u_k are pinned.
Each of the three phases has m occurrences; fewer than m are removed in
total, so at least one free occurrence remains in each phase, and some phase
has two free occurrences. For a control of owner i with ell full periods
remaining, its endpoint observer component is-e_i and its pivot component is

    -T_0i/(1-a)+a^ell C_i,  C_i=B_i0+T_0i/(1-a).

For phase123 the constants are

    C=(-176/2795,-55/559,10/43).

For phases231 and312 they are respectively

    (-16/129,-110/1677,20/129),
    (-176/1935,-55/387,44/387).

All are nonzero. Two free controls of the same phase have distinct pivot
components because 0<a<1. Their difference gives a nonzero pivot-only
endpoint vector. One control of each observer then supplies the other
three independent directions. This proves endpoint rank4, hence the full
augmented rank. The relevant leading determinant is nonzero, so a polynomial
minor in the quiet rewards is nonzero, rather than an assumed rank oracle.

These C_i inequalities persist in one neighborhood of the active data,
uniformly in m. For every such active table, every finite single-quiet mask
therefore has a nonzero minor polynomial in the quiet rewards. By the Baire
theorem, a dense intersection of their open nonzero loci supplies simultaneous
full rank for ALL lengths and all these masks, in any prescribed quiet-reward
open box. There is no finite uniform condition-number claim.

### Conditional actual-law consequence and remaining obstruction

At such generic raw data, an ACTUAL positive-Never ALL-END observer-optimal
global minimum with an eventual cyclic123 pair tail and eventual pivot
strictness cannot have arbitrarily late N=3m windows with at most m-16 quiet
contacts and at most one quiet contact per date. The negative-index bound
survives restriction by fewer than m-15 independent quiet rows. Full row rank
gives an exact finite IFT fibre preserving all those contacts and all entrance
caps. Strict omitted gaps and positive supported hazards persist locally.
For each fixed finite N the actual tail tends to the zero-data reference;
the augmented-objective cancellation transfers its negative Hessian to the
actual cap-preserving fibre, contradicting minimality.

Thus, if every sufficiently late date has at most one quiet contact, the
lower asymptotic quiet-contact density is at least1/3 per date. This uses one
single raw/penalty neighborhood and a produced countably generic rank set,
not a different neighborhood for each length. Arbitrary double-quiet slots,
late pivot ties, other support words, source realization, and production of
this singleton/raw chamber from arbitrary games remain unresolved. No
unrestricted Fin4 closure or new reward-table UE theorem is claimed.
