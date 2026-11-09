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

The supporting results below concern exactly one zero-cap observer. They
extend the existing head representation to its original Never coordinates
and give an exact incoming root on a positive-pair subface. The latter does
not yet pass through an infinite actual head. No new UE reward-table class
is asserted. All results are ordinary mathematics, not new Lean checks.

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

The useful conclusions retained here are augmented head preservation and
the exact positive-pair incoming root. The uniform-gain composition or
realization step is still missing.
