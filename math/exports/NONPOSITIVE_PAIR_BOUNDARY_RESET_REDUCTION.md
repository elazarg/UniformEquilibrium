# Nonpositive-pair continuation resets with arbitrary cross rewards

## Exact statement and conjecture-facing change

Consider a native four-player quitting game: every own singleton reward,
live reward and AllNever reward is zero, all absorbing rewards are finite,
and all players randomize privately and independently. Deviations range over
all behavioral strategies. Section1 defines the full-response compact
carrier, the absorbing sum-debt gap Delta, and the objective J_r.

Under Delta>0 and a strictly positive inverse singleton column for pivot p,
Sections1--4 produce an ALL-END global minimum with positive original Never.
It is either actual, or has an actual positive-survival head and an inherited
endpoint Q with nonnegative caps, at least one zero observer cap, and some
positive cap. No minimizing property of Q is assumed.

On the endpoint face

    B_i(Q)=B_j(Q)=0, B_p(Q)=b_p>=0, B_k(Q)=b_k>0,

the following contact producer is total. Assume

    Gamma_ip=A>0, Gamma_jp=B>0, Gamma_ij=-a<0, Gamma_ji=-b<0,
    Z_i({p,i})=M_i>A, Z_j({p,j})=M_j>B,
    Z_i({i,j})=-c_i<=0, Z_j({i,j})=-c_j<=0.                (T)

Every other reward is arbitrary finite data. In particular neither pair
depth is bounded, no equality between normalized depths is required, and
the four observer cross/triple rewards need not vanish. For every sufficiently
small positive parameter, an explicit rational case split produces a diffuse
pivot entry followed by at most two literal product roots. The resulting
point R lies in the observer-optimal carrier, returns both zero observer caps
exactly to zero, has B_k(R)>0 and positive original Never, and converges to Q
as the parameter decreases to zero. The remaining observer's full-cap guards
hold automatically near zero. The pivot's full maximum is always retained,
including when b_p=0.

A complete finite real-polynomial sign selector then finds a parameter with
exact k-cap return and pivot improvement whenever one exists in this
designated family. Every passing parameter contradicts global minimality
through the actual inherited head. Thus a selected source satisfying (T)
must fail every stated return/improvement test. All strategic objects tested
by this necessary condition are produced from the raw table and selected
source coordinates; no favorable controller or feasible parameter is assumed.

The change is a complete contact mechanism on the full nonpositive-pair
region under M_i>A and M_j>B, plus finite global source exclusions beyond
shallow-pair and zero-cross restrictions. The exact finite example in
Section7 has deep negative pairs, all four cross entries nonzero, and passes
every comparison. Its literal game is already solved. This is a residual
source reduction, not a new reward-table UE existence class. Exact k return
and pivot improvement are not proved to succeed universally. Actual minima,
other endpoint faces and arbitrary Fin4 remain open.

## Strategic inputs and source correspondence

The only source premises are the native table, its positive absorbing gap,
the strict inverse column, and 0<r<Delta. The proof produces the minimum and,
in the nonactual case, its actual head and endpoint. The contact theorem
applies when that endpoint meets (T) and the stated face. It also applies
directly to any ALL-END observer-optimal carrier point with those coordinates.
The finite selector returns a concrete improvement or reports that none of
its finitely many sign cells passes; it does not infer success from contact
production alone.

The literal unrestricted-response maximum is represented by
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; the payoff/cap
splice by `quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
The augmentation by original Never, compact source selection and total
boundary construction below are ordinary mathematics beyond those literal
root identities. No new Lean theorem or integration is asserted.
## 1. Model and the source produced from the absorbing gap

There are four players. A finite vector Z(S) is specified for every nonempty
quitting coalition S; live play and AllNever pay zero, and Z_l({l})=0.
Put M=max(1,max|Z_l(S)|), Gamma_ab=Z_a({b}) for a!=b, Gamma_aa=0.
Every player uses private independent randomization.
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
    Delta=inf{sum_l d_l(P): P actual and nu(P)=0}.

ALL-END means B=e. The set C is compact and contains AllNever.

Assume

    Delta>0, Gamma invertible, Gamma^(-1)e_p>0 coordinatewise,       (S1)

where e_p in (S1) denotes a coordinate unit vector. For every 0<r<Delta, J_r
has a positive minimum mu on C. Every minimizer Y has positive original
Never and is ALL-END. If Y is not the tuple of an actual profile, the proof
below produces an actual positive-Never head P and an endpoint Q in C such
that Y=Phi_P(Q), with

    N_l(Q)>0, B(Q)=e(Q)>=0,
    some observer cap zero, some cap strictly positive.        (S2)

The representation is a limit of finite-prefix operations, not a move after
an infinite calendar. The endpoint Q need not minimize J_r.

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

    Delta<=sum_l d_l+14M nu^(1/4).                                (S6)

Put f(s)=min_C J_s for s>=0. AllNever gives f(s)<=s. If 0<r<Delta, compactness
and (S6) give 0<mu=f(r)<=r<Delta and, at every minimizer,

    nu>=((Delta-r)/(14M))^4>0.                                    (S7)

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
and k=S-v_p>0. For fixed T>0 use independent hazards 1-exp(-v_l epsilon)
over a mesh of [0,T], followed by AllNever. As the mesh tends to zero their
augmented tuples converge to a point D_T in H satisfying

    U_l(D_T)=B_l(D_T)=e_l(D_T)=0                       (l!=p),
    U_p(D_T)=(1-exp(-ST))/S,
    B_p(D_T)=e_p(D_T)=(1-exp(-kT))/k,
    N_l(D_T)=exp(-v_l T).                                    (S9)

Indeed the probability of a collision over the whole mesh is O(epsilon).
Uniformly in a chosen response date y, the forced-query collision error is
also O(epsilon), and its payoff tends to
(Gamma v)_l integral_0^y exp(-(S-v_l)t)dt. Prescribed payoffs use rate S.
Since Gamma v=e_p, these limits prove the FULL-cap assertion (S9), including
Never and every finite deadline. Only actual finite profiles are used.

If B_p(Y)>e_p(Y), grafting D_T after Y for small T leaves every cap unchanged
and every observer payoff unchanged. It strictly raises the pivot payoff
by nu(Y)U_p(D_T) and strictly lowers r nu. This contradicts minimality.
Therefore Y is ALL-END. Also, if 0<=a<b and f(b)<Delta, every minimizer Z_b
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

## 4. One actual head, its mixed endpoint, and the global consumer

Start with a nonrealized minimizer Y from Section 2. At each current point
choose among the preceding eligible rules one with largest assigned activity
bound: z/M for a negative cap and delta/2 for all positive observer caps,
using the minimum of those caps for b. Stop when none applies. Each extracted word is finite and literal.
If the procedure stops finitely, use its endpoint Q and its finite head P
followed by Never. Otherwise flatten all words into one natural sequence q_t
with conditional tuples X_t, starting at X_0=Y.

Every prefix survival is at least nu(Y)>0, because all tail Never coordinates
are at most one. Taking logarithms of the product gives

    sum_t sum_l q_tl<infinity,
    product_t product_l(1-q_tl)>=nu(Y)>0.                       (S13)

The actual head P uses these roots and leaves the remaining masses at literal
Never. Adjacent U,e coordinates differ by at most 2M sum_l q_tl; ALL-END
gives the same bound for B. Tail Never coordinates increase and stay bounded.
Thus X_t converges to Q in C, ALL-END, with positive original Never.
Since B_l(X_t)>=Q_l(q_t)>=-M sum_a q_ta, its caps are nonnegative. At a finite
stop this follows from ineligibility of the negative-cap rule.

If all observer caps at Q were positive, the all-positive rule would supply
one positive activity bound on all sufficiently late words, contradicting
(S13). At a finite stop, eligibility directly excludes all-positive observer caps.

Let n_l=N_l(P), h_l=product_(a!=l)n_a and s=product_l n_l>0. Unrolling (S3)
gives the retained-query head map

    U_l(Y)=U_l(P)+s U_l(Q),
    B_l(Y)=max(B_l(P),e_l(P)+h_l B_l(Q)),
    e_l(Y)=e_l(P)+h_l e_l(Q), N_l(Y)=n_l N_l(Q).                (S14)

The payoff and Never series converge absolutely by (S13). Finite head
queries exhaust the actual head menu; the nonnegative cap B_l(Q) makes the
through-head option dominate the head's own Never query. This proves the
cap identity. Equivalently, finite prefix maps are nonexpansive in the tail
payoff and cap coordinates, so replacing X_t by its limit Q has vanishing
effect. Formula (S14) identifies Y=Phi_P(Q); it does not execute Q after an
infinite calendar. By (S5), Phi_P(R) is a point of H for every R in H.

It remains to exclude B(Q)=0. Then e(Q)=0 and U_l(Q)=0 for observers. Put
R=d_p(Q)+r nu(Q)>0. Grafting Q after any Z in C preserves all its caps and
observer payoffs, and gives J_r(Z graft Q)=J_R(Z). Hence f(R)>=f(r)=mu.
Formula (S14) also shows that the ACTUAL head P belongs to C and satisfies
J_R(P)=mu. Thus f(R)=f(r)=mu<Delta, and (S10) forces R=r.

If nu(Q)<1, repeated retained-query grafts of Q after Y remain in C, preserve
all caps, and satisfy nu(Y_n)=nu(Y)nu(Q)^n and
d_p(Y_n)=mu-r nu(Y)nu(Q)^n. A compact limit has nu=0 and total debt mu<Delta,
contradicting (S6). If nu(Q)=1, every marginal Never coordinate is one.
On actual laws, |U_l|<=M(1-nu), |e_l|<=M(1-h_l), and
|B_l|<=M(1-h_l); these inequalities pass to H. Hence Q is exactly AllNever,
and (S14) makes Y the actual tuple of P, again a contradiction. Therefore
some cap at Q is positive, proving (S2).

The construction permits any additional finite family of exact incoming
rules preserving C, ALL-END and original Never, whose assigned activity
bounds stay positive near the configurations they exclude. Include their
bounds in the same maximum. The same summability argument retains every
previous exclusion. No minimizing property of Q is used.

For subsequent comparisons, (S14) shows directly that a replacement R in C
with exactly the same observer payoffs and caps, B_p(R)<=B_p(Q),
U_p(R)>=U_p(Q), and nu(R)<nu(Q), contradicts global minimality after the
same positive-survival head P. Its output observer debts stay zero, its pivot
cap cannot increase, its pivot payoff cannot decrease, and its penalty
strictly decreases. This remains valid at a binding pivot cap obstacle.
## 5. Total contact production on the nonpositive-pair region

### 5.1. Data and produced diffuse entry

Fix roles p,i,j,k and an endpoint Q in C with B=e, all N_l>0, and

    B_i=B_j=0, B_p=b_p>=0, B_k=b_k>0, U_p=u.

Use (T), and write

    m_i=M_i/A>1, m_j=M_j/B>1,
    d_i=Z_i({p,j}), d_j=Z_j({p,i}),
    s_i=Z_i({p,i,j}), s_j=Z_j({p,i,j}).

The letters A and B here are singleton rewards; Delta remains the absorbing
gap, and B_l denotes a full response cap. All four d/s entries are arbitrary.

For 0<t<1 first produce a diffuse solo-p entry with total pivot quitting
mass t. Prefix actual approximants of Q by m solo-p roots of common hazard
h_m=1-(1-t)^(1/m) and take a diagonal augmented limit. For l!=p, a head
deadline d with 0<=d<m pays

    Gamma_lp[1-(1-h_m)^d]+(1-h_m)^d h_m Z_l({l,p}).       (E1)

Successive increments have the sign of Gamma_lp-h_m Z_l({l,p}); thus the
deadline sequence is monotone, with endpoint limits 0 and t Gamma_lp.
Its through-tail cap is (1-t)B_l(Q)+t Gamma_lp. If

    E=(1-t)b_k+t Gamma_kp>=0,                            (E2)

this dominates every limiting head deadline, for i,j and k. The pivot cap
stays max(0,b_p)=b_p. Hence the full augmented entry is

    U_p=(1-t)u, B_p=e_p=b_p,
    U_i=B_i=e_i=At, U_j=B_j=e_j=Bt,
    U_k=B_k=e_k=E,
    N_p=(1-t)N_p(Q), N_l=N_l(Q) for l!=p.                (E3)

This proves entry from actual finite profiles and prices all deadline
responses. It imposes no condition on participant rewards queried during
entry. Condition (E2) holds strictly for all sufficiently small t.
### 5.2. A scalar exact boundary primitive

Suppose a tail has i payoff/cap/Never offer 0 and j payoff/cap/Never offer
X>=0. A root with only i active, at odds v=X/b, returns both to zero.
The i offers are both 0. The j Continue numerator is X-bv=0 and its Quit
numerator is -c_j v<=0. This prices all inherited queries by the literal
root maximum. If X=0 omit the root. The cross/triple entries never occur.

### 5.3. Complete contact production when both pair magnitudes are positive

Fix sufficiently small pivot odds z>0 so that all four quantities

    c_i-s_i z, c_j-s_j z, a-d_i z, b-d_j z

are positive. Define the rational functions

    t0_i=(m_i-1)z, t0_j=(m_j-1)z,
    T_i=-z+(a-d_i z) M_i z/[A(c_i-s_i z)],
    T_j=-z+(b-d_j z) M_j z/[B(c_j-s_j z)],
    L_i=a-c_i+(s_i-d_i)z, L_j=b-c_j+(s_j-d_j)z.

Use the following finite partition. The chosen t is the mass of a diffuse
solo-p entry, whose two observer caps are At and Bt.

1. If T_i<=t0_j, set t=t0_j and use inner odds

       w_p=z, w_i=0, w_j=A(t+z)/(a-d_i z), w_k=0.

   Observer j is exactly indifferent because Bt=(M_j-B)z. Observer i
   Continues at value 0. Its Quit numerator is

       M_i z-(c_i-s_i z) A(t+z)/(a-d_i z)<=0,

   exactly by T_i<=t. Thus i is quiet and optimal at zero; j has full
   cap X=M_j z/(1+z)>0. Apply Section5.2.

2. Otherwise, if T_j<=t0_i, use the symmetric switch and then solo j.

3. Otherwise T_i>t0_j and T_j>t0_i. Choose the smaller T; suppose
   T_i<=T_j. Set t=T_i and inner odds

       w_p=z, w_j=M_i z/(c_i-s_i z),
       w_i=B(T_i-t0_j)/L_j, w_k=0.

   The identity

       T_j-t0_j=M_j z L_j/[B(c_j-s_j z)]

   and T_j>=T_i>t0_j show L_j>0. Consequently w_i>0, and

       0<w_i<=M_j z/(c_j-s_j z).

   Both i offers are exactly zero. Observer j is exactly indifferent by
   the definition of w_i, and its full common cap is

       X=[M_j z-(c_j-s_j z)w_i]/[(1+z)(1+w_i)]>=0.

   Apply Section5.2. If T_j<T_i use the symmetric construction.

This proves total production, including every comparison equality. There is
no division by a possibly zero L in a chosen branch: the third branch proves
its selected L strictly positive. The switches do not use L at all.

Every selected t is positive and O(z). Every inner/outer odds coordinate is
O(z): in the third branch both observer odds are bounded by their displayed
zero-Quit thresholds; the switch has a denominator bounded away from zero.
Thus t<1 and all roots are proper for sufficiently small z. This is a
direct algebraic partition, not an implicit-function or genericity argument.

### 5.4. Zero pair magnitudes

If c_i=0<c_j, retain T_j and t0_i. If T_j<=t0_i, use the j-quiet switch.
Otherwise put t=T_j and use the j-zero main root

    w_i=M_j z/(c_j-s_j z),
    w_j=A(T_j-t0_i)/[a+(s_i-d_i)z].

The denominator is positive for small z, and both observer odds are O(z).
The i common cap numerator is M_i z+s_i z w_j>0 for sufficiently small z.
The solo-j boundary primitive returns it to zero; its forced-Quit numerator
is now exactly zero because c_i=0. The opposite case is symmetric.

If c_i=c_j=0, for any sufficiently small t>0 use the single root

    w_p=w_k=0, w_i=Bt/b, w_j=At/a.

Both observer Quit and Continue numerators vanish. All four cross/triple
terms vanish because the pivot does not quit at this root.

Therefore all c_i,c_j>=0 admit the reset, with arbitrary finite d/s entries.

## 6. Exact remaining-observer return and complete finite selection

For the chosen t use the diffuse solo-p entry proved in Section5.1. Its
exact annotations are

    U_p=(1-t)u, B_p=e_p=b_p,
    U_i=B_i=e_i=At, U_j=B_j=e_j=Bt,
    U_k=B_k=e_k=E=(1-t)b_k+t Gamma_kp,
    N_p=(1-t)N_p(Q), N_l=N_l(Q) for l!=p.

Require E>=0. For nonnegative odds w let D_l=product_(h!=l)(1+w_h),
D=product_h(1+w_h), and define the passive and forced-Quit odds numerators by

    P_l=sum_(nonempty S subset players\{l}) Z_l(S) product_(a in S)w_a,
    Q_l=sum_(S subset players\{l}) Z_l(S union {l}) product_(a in S)w_a.

The exact full root map is

    U_l'=[w_l Q_l+P_l+U_l]/D,
    B_l'=max(Q_l,P_l+B_l)/D_l,
    e_l'=[P_l+e_l]/D_l, N_l'=N_l/(1+w_l).

Apply it to the inner root and then the scalar boundary root. Require the
two quiet-k guards Q_k<=P_k+e_k, exact final e_k=b_k, final B_p<=b_p,
and final U_p>=u. Observer i,j contacts were proved above; these tests return
the full cap and payoff of k. Every inherited pivot maximum is retained.
When X=0, omit the outer root as a separate branch and use the identity map
on every coordinate. Do not replace omission by an all-zero literal root:
that root would add a fresh zero query and could change a negative cap.
In this branch there is no second k guard and D(outer)=1.
Every non-maximum expression is rational in the one chosen parameter z (or
t when both c's vanish). The pivot cap is the maximum of finitely many
rational candidates; split into their finitely many comparison branches.
The literal finite return equation has a polynomial numerator.

For each of the finitely many branches, collect the denominators, branch
comparison polynomials, return numerator and full-cap/comparison polynomials.
The domain tests explicitly include z>0, 0<t<1, every displayed strict
denominator sign for the selected branch, every produced odds coordinate
nonnegative, and X>=0. In the one-zero-pair main branch X>=0 is retained as
an exact finite test; the preceding small-z proof shows that its domain is
nonempty. When both pair magnitudes vanish the parameter is t in (0,1).
If the return numerator is nonzero, enumerate all its real roots and retain
exactly those satisfying every test. If it is identically zero, list all
roots of the other nonzero polynomials and one point from each complementary
sign interval, retaining admissible points. Denominator zeros are rejected.
This finite selector is complete for the designated branch construction;
it does not claim completeness for all possible two-root controllers.

A selected output R belongs to H by prefixing the literal roots before finite
approximants to the diffuse entry and Q. Its original Never product is

    nu(R)=(1-t)nu(Q)/[D(inner)D(outer)]<nu(Q).

The observer U/B coordinates return exactly. Therefore through EVERY actual
positive-survival head P, pivot cap cannot rise, pivot payoff cannot fall,
and r nu strictly falls. This includes a binding pivot obstacle; Q itself
need not be a minimum. Alternatively use the exact inherited-head obstacle
inequality, with all maxima kept, as specified below.
### 6.1. Automatic observer feasibility near zero

The contact partition proves that t and all inner/outer odds are O(z), or
O(t) in the both-zero case. This remains true when a selected L denominator
vanishes at zero: the displayed threshold bound controls its quotient.
The intermediate nonzero cap X is O(z), so the boundary odds are O(z) too.

At the diffuse entry E tends to b_k>0. At each of the at most two subsequent
roots, the k forced-Quit offer tends to its own singleton reward zero, whereas
its Continue value tends to b_k. Thus every k guard holds strictly for all
sufficiently small parameters. The resulting R lies in C, has B_k(R)>0,
and all original Never coordinates remain positive. Its full augmented tuple
tends to Q: the root maps are continuous, and their zero-odds limits send
B_l to max(0,B_l)=B_l because all input caps are nonnegative. When X=0
the omitted root is the identity. No strict pivot cap buffer is required.

This produces observer-feasible contacts without a successful k-return
test. The head graft need not remain observer-optimal until k returns: an
observer active in the actual head can pin its endpoint cap exactly.
Convergence to Q alone does not remove that constraint or supply a fixed
positive global improvement.

### 6.2. The exact inherited obstacle comparison

The actual head can permit a weaker k condition than exact return. For any
observer l put n_l=N_l(P), h_l=product_(a!=l)N_a(P),
a_l=[B_l(P)-e_l(P)]/h_l, and d_l^P=B_l(P)-U_l(P). If a replacement is
observer-optimal with common l payoff/cap x, its head debt divided by h_l is

    d_l^P/h_l+max(0,x-a_l)-n_l x.                       (H1)

The actual head inequality d_l^P>=n_l[B_l(P)-e_l(P)] gives
d_l^P/h_l>=n_l a_l. If n_l<1, (H1) is zero only when
d_l^P/h_l=n_l a_l and x=a_l. If n_l=1, l never quits in the head, so
U_l(P)=e_l(P); then (H1)=0 exactly when x>=a_l. Since the old graft is
observer-optimal, it already satisfies these conditions at x=B_l(Q).
The new construction returns i,j exactly. Therefore its complete remaining
head-feasibility test is

    B_k(R)=b_k                 if N_k(P)<1,
    B_k(R)>=a_k                if N_k(P)=1.             (H2)

The second branch includes automatic feasibility near zero when b_k>a_k.
At b_k=a_k it retains the displayed one-sided inequality. The finite selector
can replace the exact return equation by this inequality in that branch;
all nonzero guard roots and complementary sign intervals suffice. No return
parameter is assumed in either branch.

For an actual head P set n=N_p(P)>0, h_p=product_(l!=p)N_l(P)>0, and

    a_p=[B_p(P)-e_p(P)]/h_p>=0.

Under (H2), the head graft is observer-optimal. Its pivot objective, up to
a positive factor and additive constant, is

    F_P(R)=max(a_p,B_p(R))/n-U_p(R)+r nu(R).              (F)

This follows directly from (S14), since its joint survival is n h_p.
Consequently the complete selector may use F_P(R)<F_P(Q) instead of the
sufficient B_p(R)<=b_p and U_p(R)>=u tests. Split every maximum into its
finite rational branches and apply the same polynomial sign partition.
This retains obstacle crossings and ties. One passing fixed parameter
gives a fixed positive decrease at the actual global minimum. No vanishing
gain is passed off as an improvement after taking approximation limits.
## 7. An exact deep-pair example with arbitrary cross entries

### 7.1. Complete reward table and actual source production

Use roles p=0,k=1,i=2,j=3, with all vectors in player order 0,1,2,3.
Specify the singleton matrix

    Gamma=[0,5,-1,-1; -2,0,1,1; 2,-1,0,-1; 2,-1,-1,0].

All nonsingleton entries are zero except the following complete list:

    Z_2(02)=Z_3(03)=8,
    Z_2(23)=-8, Z_3(23)=-10,
    Z_0(23)=1000, Z_1(23)=-1000,
    Z_0(01)=-512, Z_1(01)=1,
    Z_2(12)=Z_3(13)=-8,
    Z_1(03)=-1000,
    Z_2(03)=100, Z_2(023)=200,
    Z_3(02)=-300, Z_3(023)=400.                  (7.1)

Thus A=B=2,a=b=1,M_i=M_j=8 and m_i=m_j=4. The pair depths are c_i=8,c_j=10,
so BOTH are beyond m_l. All four formerly zero observer cross/triple entries
are nonzero, of mixed signs, and far from zero.

Produce Q0 with two finite-block limits. First use m equal roots with rates
(1,0,2,2), duration -log(9/10); then m equal roots with rates (1,1,1,1), duration
log 2; then AllNever. A rate lambda over duration T means hazard
1-exp(-lambda T/m). Every approximant is an actual finite calendar.

For full-cap verification, a proper root has forced-Quit payoff F_l, passive
absorption P_l, opponent survival H_l, joint survival c, and prescribed
absorption E_l. Over n repetitions and tail (u,b,e,N), set
A_l=P_l/(1-H_l), D_l=E_l/(1-c). The exact formulas are

    U_l'=D_l(1-c^n)+c^n u_l,
    e_l'=A_l(1-H_l^n)+H_l^n e_l,
    B_l'=max(F_l,A_l(1-H_l^(n-1))+H_l^(n-1)F_l,
                        A_l(1-H_l^n)+H_l^n b_l).            (7.2)

The head deadline offers form a monotone geometric sequence; (7.2) retains
both endpoints and all tail responses. In these blocks all denominators are
nonzero. As m tends to infinity, A_l tends to (Gamma lambda)_l/(sum lambda-
lambda_l), D_l to (Gamma lambda)_l/sum lambda, and F_l to zero. Every higher
reward in (7.1) is finite, so all collision terms vanish in these fixed-rate
limits. This proves convergence of FULL caps as well as payoffs.

The second block gives U=(45/64,0,0,0), B=e=(7/8,0,0,0), N=(1/2,1/2,1/2,1/2).
For x=9/10, the first block then gives

    U_p=-4/5+(481/320)x^5, B_p=e_p=-1+(15/8)x^4,
    U_k=B_k=e_k=(2/5)(1-x^5),
    U_i=B_i=e_i=U_j=B_j=e_j=0,
    N=(x/2,1/2,x^2/2,x^2/2).

Consequently

    U(Q0)=(2802569/32000000,40951/250000,0,0),
    B(Q0)=e(Q0)=(3683/16000,40951/250000,0,0),
    N(Q0)=(9/20,1/2,81/200,81/200).               (7.3)

Prefix Q0 by a root with hazards

    f=q_p=40951/790951, g=q_k=40951/415951=2f/(1+f),
    q_i=q_j=0.

Each zero observer's Continue value is 2f-g-fg=0 and Quit value is 8(f-g)<0.
The k offers are both f, since -2f+(1-f)B_k(Q0)=f. The pivot Quit offer is
-512g and its Continue offer is 5g+(1-g)B_p(Q0)>0. Therefore the literal
FULL maximum gives an exact Q in H with

    b_p=4657205/6655216, b_k=40951/790951,
    u=-10886684947367/5263949750416,
    N=(337500/790951,187500/415951,81/200,81/200),             (7.4)

and B=e=(b_p,b_k,0,0), U=(u,b_k,0,0). In particular

    699/1000<b_p<7/10, 1/20<b_k<3/50, u<-1.       (7.5)

The exact pivot payoff is also
5(1-f)g-512fg+(1-f)(1-g)2802569/32000000. This source production does not
postulate cap annotations; it prices every finite deadline and Never.

### 7.2. A rational return with complete cap checks

Choose the exact parameter

    t=(15b_k-6)/(-1984+282b_k)=4131441/1557698602,
    z=t/3, y=8t/(3-100t), v=8t/(3+t).            (7.6)

A diffuse solo-p entry of mass t over Q has pivot payoff (1-t)u and cap b_p,
observer i/j caps and payoffs 2t, and quiet-k cap/payoff/Never offer

    E=(1-t)b_k-2t.

Its original N_p is multiplied by 1-t and other Never coordinates stay
fixed. Full caps follow from the finite equal-hazard endpoint calculation
(7.2): all entry deadline limits lie below the through-tail offer provided
E>=0, verified below.

Prefix an INNER root with odds (z,0,0,y) in role order p,k,i,j. The i Continue
numerator is 2t+2z-y+100zy=0, whereas its forced-Quit numerator is

    8z-8y+200zy=2t(-84+400t)/[3(3-100t)]<0.       (7.7)

Thus i is quiet and optimal at exactly zero. Player j is exactly indifferent:
its Continue numerator 2t+2z equals its Quit numerator 8z. Its full cap is

    X_j=8z/(1+z)=8t/(3+t)=v.

Prefix an OUTER root with only i active, at odds v. The i offers are both
zero. The j Continue numerator is X_j-v=0 and its Quit numerator is -10v<0.
Thus BOTH final observer caps, payoffs and Never offers are exactly zero.
The other two large cross/triple entries in (7.1) are fully present but cannot
contribute: i is quiet at the inner root, p is quiet at the outer root.

For k define D=(1+z)(1+y) and K=E-2z+y-1000zy. Its inner Continue offer is
k1=K/D, its inner Quit offer is z/D, and its outer Quit offer is zero.
The outer Continue value is k2=(k1+v)/(1+v). The exact return identity is

    k2-b_k=4t[6-15b_k+t(-1984+282b_k)]/
                              [3(1+3t)(3-92t)]=0.          (7.8)

This is an exact rational nonzero return. Its denominator is positive at t.

The following elementary rational bounds hold by integer cross-multiplication:

    265/100000<t<266/100000,
    y<1/125, v<1/140,
    699/1000<b_p<7/10, 1/20<b_k<3/50, u<-1.       (7.9)

They give E>0. Equation (7.8) gives k1=b_k-(1-b_k)v>b_k-v>3/70>z/D, so
both quiet guards hold strictly and k really returns with its FULL cap.

The pivot forced-Quit offers are zero at both roots. Its Continue caps and
prescribed payoffs are

    b1=(b_p-y)/(1+y), b2=(b1-v)/(1+v),
    u1=((1-t)u-y)/D, u2=(u1-v)/(1+v).             (7.10)

The bounds (7.9) give b1>691/1008 and b2>3419/5076>2/3, while b2<b_p;
thus these are the literal full pivot
caps, not merely Continue branches. Since (1+z)(1+v)=1+3t, exact subtraction
in (7.10) gives

    (1+y)(1+3t)(u2-u)
      =-u(4t+y+3ty)-y-(8/3)t(1+y)
      >(4/3)t+(1/3)ty>0.                         (7.11)

Original Never is multiplied in product by

    0<(1-t)/[D(1+v)]<1,

and every marginal stays positive. Prefix both roots before finite entry
and Q approximants and take a diagonal limit to obtain the output R in H.
Nothing is played after an infinite calendar.

Exact Python `fractions.Fraction` substitution independently checked (7.8),
(7.7), E>0, both quiet guards, both pivot cap branches, strict payoff and cap
improvement, and (7.9). For cross-checking only, the cap drop is approximately
0.0249219 and payoff gain approximately 0.0228680. The proof uses exact
fractions and inequalities, not numerical root approximations. No Lean check.
### 7.3. What the example separates

The produced output has identical observer payoffs and full caps, a strictly
smaller pivot cap, a strictly larger pivot payoff, and strictly smaller
original Never. Section4 therefore excludes this endpoint through every
compatible actual positive-survival head and every r>0.

Both pair depths exceed their pivot multipliers. These depths already obstruct
the earlier simultaneous-contact architecture in the zero-cross specialization;
the displayed table additionally violates its four-zero hypotheses. Indeed,
with zero cross entries,
a row with Gamma_ip=A>0, Gamma_ij=-a<0, M_i=A m_i>A and c_i/a>=m_i
obeys, at any proper contact root with positive input cap x_i,

    (a-c_i)D_i X_i=(a M_i-c_i A)z-c_i x_i,
    D_i=(1+z)(1+w_j)>0.                                (B1)

Here X_i is the current common cap. Both a-c_i and the right side are
strictly negative, so X_i>0. Every finite word retaining i contact keeps
this positivity. A final root with both i offers zero would need input cap
(a M_i/c_i-A)z<=0, which cannot occur. Equation (B1) follows by eliminating
w_j from x_i=(M_i-A)z+(a-c_i)w_j and D_i X_i=M_i z-c_i w_j.
The new construction instead allows i to be quiet at its first zero and
then active alone at the boundary root. This explains why unrestricted
pair depths do not obstruct the contact producer.

All four d/s entries in the displayed table are nonzero. Nevertheless this
table has absorbing Nash coalition {1,2,3}: its payoff vector is zero;
player1 leaving receives -1000, and every other unilateral change is
indifferent. Hence Delta=0. The example certifies a larger finite
source-exclusion test, not a positive-gap source or new raw UE class.

## 8. Lean handoff and remaining boundary

The main declarations to formalize are:

1. Compact augmented source selection and its actual-head factorization,
   including original Never and the absorbing sum-debt estimate (S6).
2. The scalar boundary-root identity and the exhaustive rational contact
   partition, with explicit one-zero and both-zero cases.
3. The O(z) bounds, automatic local k-feasibility, and exact full-cap root
   recurrence, including the omitted-root identity branch.
4. The finite polynomial sign selector and its completeness for this
   designated family, followed by the strict actual-head consumer (F).

Use the named literal root identities to price complete deviations. Neither
a structure field asserting a successful return nor an assumed endpoint
minimum may replace these producers and comparisons. Finite selection here
means a mathematical selector over exact real coefficients; effective
machine execution requires an appropriate representation of those reals.

The total contact theorem allows arbitrary finite rewards outside (T) and
includes b_p=0. Its k-return and pivot-improvement tests can still fail.
It does not cover M_i<=A or M_j<=B in general, and does not replace valid
constructions on those other reward regions. Other sign patterns, endpoint
faces, the general actual-minimum alternative, and Fin4 remain open.
