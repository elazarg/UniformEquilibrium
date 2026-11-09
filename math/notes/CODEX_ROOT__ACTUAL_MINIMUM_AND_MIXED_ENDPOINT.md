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

The supporting results preserve original Never coordinates, give an exact
incoming root on a positive-pair subface, and identify the actual head's
precise constraints on every replacement endpoint. An observer active in
the head pins its endpoint cap; an inactive observer imposes a lower bound.
The inherited endpoint is a global minimum of an explicit obstacle objective
on this cap box. This supplies a valid fixed-gain comparison criterion, but
does not produce a compatible improvement for every endpoint. No new UE
reward-table class is asserted. All results are ordinary mathematics, not
new Lean checks.

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

Internal mechanism boundary only. No actual global minimum, absorbing gap,
or Fin4 counterexample is asserted. This explains why the [global rigidity theorem](../exports/ACTUAL_MINIMUM_GLOBAL_PAIR_STAR_RIGIDITY.md)'s
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
