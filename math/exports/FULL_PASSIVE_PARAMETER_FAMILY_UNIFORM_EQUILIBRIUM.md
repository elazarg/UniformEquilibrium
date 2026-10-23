# Absorbing equilibrium approximation throughout the formula17 family

## 1. Exact theorem and game semantics

Let I={0,1,2,3}. There is one live state. At each live date every player
privately and independently chooses Continue or Quit. A nonempty quitting
coalition selects the absorbing state. That live selecting date pays zero;
every later absorbed date pays the coalition reward. The path on which
nobody quits pays zero forever. A unilateral deviation can replace the
player's entire behavioral strategy, with arbitrary time dependence.

For arbitrary finite M,N,T>=0, define the native own-zero reward table Z:

| Coalition | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
| 0 | 0 | 3 | -1 | -1 |
| 1 | 3 | 0 | -1 | -1 |
| 2 | -1 | -1 | 0 | 3 |
| 3 | -1 | -1 | 3 | 0 |
| 01 | -1 | -1 | -1 | -1 |
| 02 | -2 | -1 | -1/10 | -1 |
| 03 | -1/10 | -1 | -1 | -2 |
| 12 | -1 | -1/10 | -2 | -1 |
| 13 | -1 | -2 | -1 | -1/10 |
| 23 | M | N | 4 | 1 |
| 012 | -6 | -41/10 | -11/10 | -1 |
| 013 | -41/10 | -6 | -1 | -11/10 |
| 023 | -11/10 | -1 | 9/10 | -4 |
| 123 | -1 | -11/10 | -1 | -21/10 |
| 0123 | -M-T-61/10 | -N-61/10 | -1/10 | -31/10 |

**Theorem.** For every such M,N,T, the infimum A_Z of total full terminal
Nash debt over almost-surely absorbing independent profiles equals zero.
Consequently, for every lambda_i>0 and s_i>=0, the original table

    R_i(A)=lambda_i Z_i(A)+s_i

has one uniform-equilibrium payoff. For that fixed game there is one vector
v such that, for every epsilon>0, some behavioral profile and integer H have
prescribed average payoff within epsilon of v in every coordinate and cap
every unilateral behavioral gain by epsilon at every horizon h>=H. The
profile and H may depend on epsilon; the payoff target v does not.

The theorem treats all three displayed passive/grand parameters with no
upper bound. Native AllNever has zero debt but does not establish A_Z=0;
the absorbing approximation conclusion is the assertion proved here.
The nonnegative offset restriction is part of the global original-game
statement. Separate exact constructions below permit signed offsets where
opponent-deleted absorption is proved. No such signed-offset conclusion is
inferred from the general absorbing source argument.

This is ordinary mathematics with complete exact certificates and an
explicit adapter to the existing Lean semantic interfaces. It is not a new
checked Lean theorem and does not settle arbitrary four-player tables.

## 2. Parameter cover and the proof mechanism

The proof supplies five regions, always including every finite T>=0:

| Region | Exact hypothesis | Native conclusion |
|---|---|---|
| Base square | 0<=M,N<=4 | A_Z=0 by actual-source exclusion |
| Middle source rectangle | 0<=M<=43/5, 2<=N<=25/2 | A_Z=0 by actual-source exclusion |
| Two-period construction | M>=K_star, N>=0 | exact absorbing terminal Nash |
| Four-period construction | 4<=M<=9, 0<=N<=2 | exact absorbing terminal Nash |
| Stationary construction | M>=0, N>=25/2 | exact absorbing terminal Nash |

Here

    K_star=(71-sqrt(65)+2sqrt(809))/14.

One has K_star<43/5<9: sqrt(65)>8 and sqrt(809)<57/2 give
K_star<60/7<43/5. Thus first use the two-period construction when
M>=K_star and the stationary construction when N>=25/2. The remaining
case has M<K_star<43/5 and N<25/2. If N>=2, the middle source rectangle
applies. If N<=2 and M<=4, the base square applies. If N<=2 and M>=4,
the four-period construction applies. All boundary values are included.
No equality or compatibility of profiles on overlapping regions is needed.

The source proofs work in the compact closure of actual independent-law
payoffs, complete caps and original Never masses. Positive absorbing debt
would give a positive minimum Never product on a marked zero-debt set.
An actual first date and its genuine tail then yield a legal prefix with a
smaller original Never product. The decisive incoming023 case sometimes
replaces that first date by TWO rows at the same actual tail. Other source
supports and the nonnegative boundary are also fully exhausted below.
Tails are never assigned minimum status, and virtual continuations are
removed by nonexpansive complete-cap comparison.

The quantitative exits use exact proper periodic or stationary hazards and
prove absorption after deleting any player. Their active equalities and all
outside caps imply complete terminal Nash inequalities for unrestricted
behavioral deviations. Every construction and every polynomial certificate
used in this cover is provided below.

Section C gives an exact new-scope calibration at M=N=5,T=0 with own
levels1. It excludes the earlier raw-class admissions by complete finite
role and root censuses, including the stationary and specified short-phase
architectures. Its comparison with the earlier source neighborhood uses
the documented radius restriction epsilon<=1/100; no maximal-radius claim
is inferred from that qualitative theorem.

## 3. Actual laws, exact prefix maps, and absorbing repair

A behavioral strategy on the unique live history is equivalent to a law on
finite dates and Never. Independent private randomness gives independent
complete laws. A unilateral behavioral deviation is another complete law;
its payoff is affine in that law. Hence its supremum equals the supremum
over all deterministic finite deadlines and the literal Never response.
This argument allows arbitrary time dependence and private randomization.
There is no public lottery or additional observation.

For a fixed native table W with W_i({i})=0, write U(P), B(P), N(P) for the
prescribed payoff, full unilateral cap, and four original Never masses of an
actual independent profile P. Set d_i=B_i-U_i>=0 and D=sum_i d_i. If B_reward>=1
bounds all rewards in absolute value, these coordinates belong to
[-B_reward,B_reward]^8 times[0,1]^4. Define their finite-dimensional compact closure

    H=closure{(U(P),B(P),N(P)):P actual},
    E={X in H:B(X)=U(X)},
    E_C={X in E:min_(i in C) U_i(X)<=0},
    C={0,1},  nu(X)=product_i N_i(X).

A point of H need not be attained by one actual law. Every finite prefix
extends to H by continuity of the maps now defined.

Define zero-diagonal matrices Gamma,J,L by

    Gamma_ij=W_i({j}), J_ij=W_i({i,j}) for i!=j,
    Gamma_ii=J_ii=0, L=J-Gamma.

For a hazard q in[0,1]^4 let a(q)=product_i(1-q_i). Let A be the random
opponent quitting set under independent first-date actions, and put

    Q_i(q)=E[W_i(A union{i})],
    P_i(q)=E[1_(A nonempty) W_i(A)],
    H_i(q)=Pr(A empty)=product_(j!=i)(1-q_j),
    E_i(q)=q_i Q_i(q)+(1-q_i)P_i(q).

For an arbitrary real payoff/cap pair (u,b), exact prefixing means

    u'_i=E_i(q)+a(q)u_i,
    b'_i=max(Q_i(q),P_i(q)+H_i(q)b_i),
    N'_i=(1-q_i)N_i.                                  (Prefix)

The cap formula follows by splitting any complete deviation according to
its first action. Suprema need not be attained: approximate best responses
in the Continue branch establish the reverse inequality. The maps preserve
b>=u. They are coordinatewise 1-Lipschitz in the suffix annotations, and the
same is true for every fixed finite word, independently of its length.
Indeed a payoff difference is multiplied by joint survival and a cap
difference is multiplied by opponent survival before taking a maximum.

A root q is Nash against u when its prescribed mix optimizes each player's
two endpoints Q_i and P_i+H_i u_i. Equivalently the gap

    g_i(q,u)=Q_i(q)-P_i(q)-H_i(q)u_i

is nonpositive if q_i=0, zero if 0<q_i<1, and nonnegative if q_i=1.
Nash roots have a closed graph on the compact hazard cube and exist for every
u. At b=u an exact Nash root preserves b'=u'. More generally every prefix
satisfies

    d'_i>=a(q)d_i.                                      (Debt)

To verify (Debt), subtract the policy mixture from the cap and use that the
cap is at least each of Q_i and P_i+H_i b_i. Exact Nash against b makes
(Debt) an equality. A nonzero root strictly reduces original joint Never
unless it was already zero; a sure root reduces it to zero.

Define A_W as the infimum of total full debt over actual profiles whose
joint Never product is zero, equivalently which absorb almost surely.
For any actual profile choose an owner with least Never mass m and move
that entire mass to one fixed finite date. That owner now quits surely at
a finite time, so the changed profile absorbs almost surely. Under the
natural coupling, each prescribed payoff changes by at most 2 B_reward m.
The changed owner's cap is unchanged because its opponents did not change;
each of the other three full caps changes by at most 2 B_reward m, uniformly
over all deviations. Therefore

    A_W <= D+14 B_reward min_i N_i
        <= D+14 B_reward nu^(1/4).                    (Repair)

This continuous bound passes to H. Native AllNever has U=B=0, so E_C is
nonempty. If A_W>0, every zero-debt point has positive nu, and compactness
gives a minimum of nu on E_C, necessarily positive. Every nonzero Nash
prefix whose output is still marked contradicts that minimum: it preserves
zero debt and lowers nu, including the sure-root boundary.

## 4. First-date envelope and genuine conditional tails

Set

    ell_i=min(0,min_(nonempty A not containing i) W_i(A)).

Every actual profile with literal first-date hazards q satisfies

    B_i>=Q_i(q),
    B_i>=P_i(q)+H_i(q)ell_i,
    q_i(B_i-Q_i(q))<=d_i.                            (1)

The second deviation Continues on this date and then Never quits; conditional
on no opponent quitting now, it receives either zero or a passive reward at
least ell_i. For the third, let C_i be the payoff from Continue now followed
by the prescribed conditional strategy. Since C_i<=B_i and
U_i=q_i Q_i+(1-q_i)C_i, both terms in

    d_i=q_i(B_i-Q_i)+(1-q_i)(B_i-C_i)

are nonnegative. The formulas remain valid at zero and unit hazards.
Witness compactness extends (1) to the whole closed actual carrier. Thus
every zero-debt point admits q such that

    U_i>=Q_i(q),
    U_i>=P_i(q)+H_i(q)ell_i,
    q_i(U_i-Q_i(q))=0.                              (2)

A stronger incoming decomposition exists when nu(X)>0. Choose actual
profiles tending to X and let q^n be their literal first-date hazards.
Their survival masses a_n satisfy a_n>=nu_n, so eventually a_n is bounded
below by a positive constant. Their conditional all-Continue tails are
well-defined actual independent profiles. Extract convergent subsequences
of hazards and bounded tail annotations, obtaining q and Y in H. Then

    a(q)>=nu(X)>0, X=prefix_q Y, nu(Y)=nu(X)/a(q)>0.

By (Debt), if X has zero debt then Y has zero debt. The exact cap formula
then proves q is Nash against the genuine tail payoff v=U(Y). Every positive
hazard is paid, so U_i(X)=Q_i(q) whenever q_i>0. If any coordinate of U(X)
is negative, q cannot be AllContinue because (2) would give U>=0. No
minimum assertion about Y is used.

At positive Never, actual zero debt also gives passive upper bounds. For an
actual independent law P, let V_i(Never;P_-i) be the payoff from literal
Never. Affinity in player i's complete stopping law and optimality of its
full cap imply

    d_i(P)>=N_i(P)[B_i(P)-V_i(Never;P_-i)].

The bracket is nonnegative. Write
R_i^pass=max(0,max_(nonempty A not containing i) W_i(A)). Literal Never
always pays at most R_i^pass. Passing the displayed inequality to actual
approximants at any closed zero-debt point with N_i>0 gives U_i<=R_i^pass.
For the displayed table this yields

    -1<=U_0<=max(M,3), -1<=U_1<=max(N,3),
    -1<=U_2<=3,        -1<=U_3<=3.

These bounds hold at every genuine positive-Never zero-debt tail. They do
not presume that the tail attains the minimum used to select its parent.

## 5. A local marked escape from small-root invariance

Here the player set may be any finite nonempty I. Use the same prefix maps
and zero-diagonal singleton matrix Gamma as in Section 3, with products
and sums over this I. Let W be any bounded native table, let C be any fixed nonempty marked set, and write
K_C={u:min_(i in C)u_i<=0}. Assume that for some delta0 in(0,1),

    u in K_C, q Nash against u, max_i q_i<=delta0
                      imply a(q)u+E(q) in K_C.          (SNI)

This quantifies over every real virtual continuation, but only small roots.
Let v>=0 with min_C v=0, suppose its ENTIRE Nash correspondence consists of
AllContinue, and put S={i:v_i=0}.

**Local lemma.** For every d>0 and eta>0 there are c>0 and finite independent
prefix words W_k supported on S, with each hazard at most d, whose full
annotations from(v,v) and joint survivals h_k satisfy

    1-eta<=h_k<=1-c,
    sum_i(B_i(W_k)-U_i(W_k))->0,
    limsup_k min_C U(W_k)<=0.                          (L)

Every coordinate outside S retains a positive buffer. No actual realization
of a virtual seed is an assumption.

Proof. The induction retains precisely where (SNI) is used.
Decrease eta to lie below1 and preserve every positive coordinate of v.
Choose M>=1 bounding the rewards, v and all nearby seeds. Every word with
survival p from seed z satisfies

    ||U-v||_infinity<=||z-v||_infinity+2M(1-p).          (B)

All annotations stay in the bounded reward/seed cube, since both the policy
and the full-cap update take convex combinations or maxima of such values.

Induct on |S| in the SAME ambient game and with the SAME C and delta0.
If Gamma_SS x=0 for nonzero x>=0, normalize sum x=1 and repeat hazards
epsilon*x on S for floor(t/epsilon) dates, where1-eta<exp(-t)<1. Core
passive and prescribed absorption contributions are O(epsilon^2), whereas
forced-Quit contributions are O(epsilon). More explicitly, for each core
coordinate there is a fixed K such that after k dates,
|u_i(k)|<=K k epsilon^2 and b_i(k)<=K epsilon+K k epsilon^2.
Induction in (Prefix) proves these bounds for every k up to floor(t/epsilon).
Therefore core payoffs and full cap debts tend to zero over this word. The cap bound uses a nonnegative
upper estimate O(epsilon+floor(t/epsilon)*epsilon^2), so multiplying by a
Continue probability never reverses the estimate. Positive outsiders have
forced-Quit values O(epsilon), retain positive Continue values by(B), and
have zero debt. Survival tends to exp(-t), and S meets C, proving(L).
This includes |S|=1, since its singleton matrix is zero.

Otherwise separation of the compact column hull from zero gives a nonzero
signed row w on S with w Gamma_SS>>0. Uniform singleton expansion then
gives gamma>0 and, for all sufficiently small hazards supported on S,

    w E_S(q)>=gamma sum_i q_i.                       (W)

The quadratic remainder is bounded by a constant times max q times sum q,
so this includes arbitrarily unequal or zero hazard coordinates.

There are seeds z tending to v, with z_out=v_out, w z_S>0 and
min_(C intersect S)z<0. If C intersect S contains two owners, failure of
such seeds would force w to be supported on each of their distinct axes,
and hence zero. If it contains only i, failure would force w to be a
nonnegative multiple of e_i; then(w Gamma_SS)_i=0, a contradiction.

Choose delta<=min(d,delta0), strictly below eta/(4|I|), so(W) and the
positive outsiders' local Continue buffers hold. Compactness and closedness
of the ENTIRE Nash graph, together with uniqueness at v, give epsilon0>0
such that every root at ||u-v||<epsilon0 has max q<delta and is supported
on S. Fix c0=min(eta/4,epsilon0/(8M),1/4), then choose the seeds within
epsilon0/4 of v.

For a fixed seed z, let K_z be the compact closure of all outputs(u,b,p)
of finite S-supported words with individual hazards<=delta and survival
p>=1-eta. It includes the empty word. It is stable under a fixed allowed
finite prefix whenever the resulting survival has strict slack above
1-eta, by prefixing defining approximants before taking their limit.
Minimize p on its nonempty closed subset

    b=u,   min_C u<=0,   w u_S>=p w z_S.              (F)

Suppose a minimum Y=(u,u,p) has p>1-c0. Bound(B) places it in the root
neighborhood of v. Every Nash root there is small and supported on S.
If one is nonzero, its prefix preserves equality of payoff and full cap;
(SNI) preserves the marked cone because its maximum hazard is<=delta0;
and(W) preserves the ORIGINAL inequality in(F). Also

    a(q)p>1-|I|delta-c0>1-eta/2.

It therefore lowers p inside the same(F), a contradiction. Finite Nash
existence now implies that the ENTIRE root correspondence at u is exactly
AllContinue. Thus u>=0. Its core is nonzero by the weighted inequality,
while min_C u<=0 gives a zero set T which is nonempty, properly contained
in S, and meets C. All coordinates outside T are positive.

Apply the induction hypothesis at u, retaining the SAME C and delta0.
(SNI) remains true because it is a property of the fixed game and C, and
does not depend on v. Request hazards<=delta and a total budget eta'>0
so p(1-eta')>1-eta. The resulting words have survival h<=1-c' for some
c'>0, zero-debt limits and nonpositive marked minimum. Their endpoints
from Y lie in the original K_z by strict-slack stability. Moreover every
one of their hazards is supported on T subset S and at most delta, so(W)
gives the ORIGINAL inequality

    w U_S>=h w u_S>=ph w z_S.

This does not require their intermediate roots to be Nash at the original
seed annotation. A compact endpoint limit is in the same(F) and has
survival at most p(1-c')<p, a contradiction. Hence every seed has minimum
survival at most1-c0; the inner c' need not be uniform in the seed.

Approximate these minima by defining finite words with debt tending to zero,
survival<=1-c0/2 and marked minimum limsup<=0. Apply the identical words
to(v,v). Coordinatewise payoff and full-cap nonexpansiveness changes total
debt by at most2 sum_i|z_i-v_i| and the marked minimum by at most||z-v||.
Survival is unchanged. This gives(L), with c=c0/2, and closes induction.
There was no invocation of invariance for a hazard above delta0.


## 6. Local premises and the base-table consumer

For the table of Section 1 let C={0,1}, D={2,3}, and K=max(M,N).
Every marked participant reward is nonpositive. If a Nash root has an active
marked owner, that owner's output is its forced-Quit value and is
nonpositive. If neither marked owner is active, then

    E_i(q)=-q2-q3+(K_i+2)q2q3,  (K_0,K_1)=(M,N).

For max q<=delta0=1/[2(K+2)], the bound
2q2q3<=delta0(q2+q3) gives E_i(q)<=-3(q2+q3)/4<=0.
A nonpositive marked input remains nonpositive. Thus (SNI) holds for all
M,N,T>=0, at every real continuation in K_C.

At any v>=0 with min_C v=0, every nonzero Nash root also has output in K_C,
including sure roots. Active marked owners prove this directly. Otherwise
q0=q1=0 and owner3's gap is

    -2q2-(1-q2)v3.

If q2>0 this is strictly negative and forces q3=0. Thus a nonzero root
supported on D is a singleton root; its output at any zero marked coordinate
is strictly negative. At an actual positive-Never minimum of E_C with
nonnegative payoff, all nonzero roots therefore contradict minimum status.
The whole Nash correspondence there is AllContinue. Applying (L) and
attaching its words to the actual carrier point gives, by compactness and
continuous prefixing, a zero-debt marked endpoint with strictly smaller
original Never product. That too is impossible.

It remains to exclude negative-payoff minima. The source classifications
below supply that exclusion on the stated parameter regions. Once every
negative minimum is excluded, the nonnegative consumer above and (Repair)
give A_Z=0.


## B. Negative-source classification for the base square

Use the normalized reward table in Section1.

Throughout this section assume 0<=M,N<=4 and T>=0. All parameters are
finite. The native own singleton rewards, live rewards and payoff on the path
where nobody quits are zero. The strategy and deviation class consists of
complete independent behavioral stopping laws, including Never.

For a hazard vector q, write

    H_i(q)=product_(j!=i)(1-q_j),
    P_i(q)=sum_(empty!=A subset I\{i})
               Z_i(A) product_(j in A)q_j product_(j notin A, j!=i)(1-q_j),
    Q_i(q)=sum_(A subset I\{i})
               Z_i(A union{i}) product_(j in A)q_j product_(j notin A, j!=i)(1-q_j).

P_i is the nonempty opponent contribution, Q_i is the immediate-Quit
endpoint, and P_i+H_i v_i is the Continue endpoint at continuation v.
A Nash root chooses Quit with positive probability only when its Quit
endpoint is at least its Continue endpoint, and chooses Continue with
positive probability only when the reverse inequality holds.

Let H be the compact closed carrier of the actual payoff, complete
unilateral-cap and individual Never-mass annotations. Thus its points are
limits of annotations of actual independent stopping profiles. Let E be its
zero-full-debt set, C={0,1}, E_C={X in E:min(U0(X),U1(X))<=0}, and
nu(X) the product of its four individual Never masses. The common carrier
argument gives the following facts used here:

* Prefixing a zero-debt point by a Nash root preserves zero full debt and
  multiplies nu by product_i(1-q_i). A nonzero root strictly lowers positive
  nu; a sure hazard gives nu=0.
* Every zero-debt point satisfies U_i>=-1 and has a first-date witness q
  satisfying

      U_i>=Q_i(q), U_i>=P_i(q)-H_i(q),
      q_i(U_i-Q_i(q))=0.                         (B0)

* At positive nu, the actual first-date extraction has a proper hazard
  vector q and a genuine positive-Never zero-debt conditional tail Y. Its
  exact payoff and full-cap prefix equations hold. If any coordinate of
  U is negative then this q is nonzero.

These facts concern the actual closed carrier. They are not hypotheses
asserted for an arbitrary virtual payoff vector. The extraction used below
is restated in detail to keep its actual-tail scope explicit.

**Base-square negative-source theorem.** A point X minimizing nu on E_C,
with nu(X)>0, has no negative payoff coordinate.

The proof is an exhaustive classification of its outgoing and incoming
Nash roots. A genuine tail used during the classification need not minimize
anything.

### B1. A bad outgoing root fixes the unmarked sign pattern

Assume some coordinate of `u=U(X)` is negative. AllContinue is then not a
Nash root against `u`, since an owner with negative continuation can Quit
alone for zero. Finite normal-form Nash existence supplies a nonzero root.
Any root with an active marked owner has a nonpositive output in that
owner's coordinate, since its entire participant row is nonpositive. Such
a root would prefix `X` to another point of `E_C` with a strictly smaller
Never product. Consequently every root at this hypothetical minimum has
`q0=q1=0` and strictly positive outputs for both marked owners.

For these D-only roots the Quit-minus-Continue gaps of owners 2 and 3 are

    g2=q3-(1-q3)u2,       g3=-2q2-(1-q2)u3.          (B1)

A nonzero singleton root gives, at any nonpositive marked input, the output
`(1-q)u_i-q<0`, and so also contradicts minimum status. Both D owners must
therefore be active. Neither can have unit hazard: `q3=1` forces `q2=1`
by `g2=1`, whereas `q2=1` forces `q3=0` by `g3=-2`. They are both proper,
and indifference gives the necessary input pattern and unique D root

    u2=x>0, u3=-y<0,
    q2=y/(2+y), q3=x/(1+x).                         (B2)

Its marked output divided by its positive joint survival is

    u_i+K_i xy/2-x-y/2>0,      K0=M, K1=N.         (B3)

Since some marked `u_i<=0`, and `M,N<=4`, this implies

    F(x,y):=2xy-x-y/2>0.

Every actual zero-debt point has `u3>=-1` by its literal Never deviation.
Thus

    1/2<y<=1,       x>y/[2(2y-1)]>=1/2.           (B4)

These strict implications include `M=0` or `N=0`; no division by a passive
parameter is used.

### B2. Extracting an actual incoming root

The genuine incoming-root construction applies to this `X` without any
restriction on the marked signs. In detail, take actual profiles tending to
`X` and their literal first-date hazards `q^n`. Their root survival masses
`a_n` satisfy `a_n>=nu_n`, so a convergent subsequence has a proper limit
`q` with `a(q)>=nu(X)>0`. The conditional all-Continue tails have bounded
payoffs, full caps and Never coordinates; pass to a limit `Y` in `H`.

The coordinate debt inequality `d_i(prefix_q Y)>=a(q)d_i(Y)` proves that
`Y` has zero debt. Payoff and full-cap prefix maps are continuous, so
`X=prefix_q Y` and `q` is cap-Nash on the genuine tail payoff `v=U(Y)`.
Also `nu(Y)=nu(X)/a(q)>0`. Finally `q` is nonzero because `U3=-y<0`
and the immediate-Quit cap at AllContinue is zero.

In particular paid owners satisfy `U_i=Q_i(q)`, all owners satisfy the
first-date envelope (B0), and the tail satisfies every actual cap restriction
again. Write

    q=(r,t,p,z)=(q0,q1,q2,q3).

At least one marked hazard is positive: if `r=t=0`, then `Q3=p>=0`,
contradicting `U3=-y`. The next cases exhaust all incoming supports.

### B3. A genuine forced-123 tradeoff

The following actual-carrier inequality will be used on both the original
point and its genuine tail:

    U0>0, U2>0, U3<-1/10
      imply U3 >= (31/47)U2-323/235.               (B5)

It uses only the first-date envelope (B0), so it does not require positive
Never mass. Its witness has `r=0`, since every owner0 participant payoff is
nonpositive. The negative `U3` forces `t>0`. If `p=0`, then
`Q3=-t/10>=-1/10`, a contradiction. Hence `p>0`. If `z=0`, the paid
owner2 output would be `Q2=-2t<0`, another contradiction. Thus the witness
has exactly the active set 123 and

    U1=pz-p/10-2z,
    U2=z(4-3t)-2t,
    U3=p(1-3t)-t/10.                              (B6)

The same formulas hold whenever an incoming root has support 123, even if
`U0` is not positive. The actual floor `U1>=-1` gives

    z <= (1-p/10)/(2-p) <=9/10.

If `U3<-1/10`, then `t>1/3`; otherwise its formula in (B6) is at least
`-1/30`. Consequently

    U2<=18/5-(47/10)t,
    U3>=1-(31/10)t.

Eliminating `t` proves (B5). No inequality here is claimed for an arbitrary
virtual continuation or a correlated calendar point.

### B4. Both marked owners cannot be paid

Suppose `r,t>0`. Set `H=5-p-z+pz`. The exact paid identities and passive
floor envelope give

    0<=Q0-P0+H0
      =1-2p-z/10-Ht-Mpz-Ttpz,
    0<=Q1-P1+H1
      =1-p/10-2z-Hr-Npz.

Here `H0,H1` denote opponent survival, whereas `H` is the displayed
positive polynomial. Since `M,N,T>=0`, it follows that

    0<=p<=1/2,     t<=9/40,
    r <= R(p):=(1-p/10)/(5-p).                    (B7)

For the middle bound use the exact identity

    9H-40(1-2p-z/10)=5(1-z)+p(71+9z)>=0.

For the last bound, the difference between `R(p)` and
`(1-p/10-2z)/H`, multiplied by `(5-p)H`, is
`z(9-9p/10-p^2/10)>=0`.

The complete owner3 forced-Quit polynomial is

    -Q3=2r+t/10-rt-p(1-3r-3t+3rt).

It increases with `r` in the rectangle (B7) and is affine in `t`. At its
two relevant endpoints, direct substitution yields

    1/2-(-Q3)|_(r=R(p),t=0)
       =(5+17p-7p^2)/[10(5-p)]>0,
    1/2-(-Q3)|_(r=R(p),t=9/40)
       =(245-400p-37p^2)/[400(5-p)]>0.

The numerator polynomials are positive on `0<=p<=1/2`. Therefore
`U3>=Q3>-1/2`, contradicting (B4). This eliminates all supports containing
both 0 and 1, including full support, without any sign premise on `U0,U1`.

### B5. Only marked owner1 cannot be paid

Suppose `r=0,t>0`. The same reasoning as in Section B3 forces `p,z>0`,
so (B6) holds. Now `y>1/2` implies `t>1/3`, and `x>0` implies
`z>2t/(4-3t)>2/9`. Hence

    u1=pz-p/10-2z<=-z<-2/9.

The forced-123 tradeoff bounds `x` above by
`(47/31)(323/235-y)`. Since `2y-1>0`,

    F(x,y) <= -(94/31)y^2+(1607/310)y-323/155
            <=153489/1165600 <2/9.

Thus `u1+Nxy/2-x-y/2<=u1+F(x,y)<0`, contradicting the second strict
inequality (B3). No original sign of the other marked coordinate is needed.

### B6. Only marked owner0: sole0 or incoming03

It remains to consider `r>0,t=0`. If `z=0,p>0`, then paid owner2 would
have payoff `Q2=-r/10<0`, impossible. If `z=p=0`, the root is sole0 and
`u0=v0=0`. Increase `r` slightly with the actual tail fixed. Owner0 remains
indifferent. Owner2's inactive gap equals `-r/10-x<0`. The other gaps are

    g1=-4r-(1-r)v1,      g3=-r-(1-r)v3.

Any strict gap stays strict. At a binding gap of the form
`g=kr-(1-r)v=0`, with `k=-4` or `-1`, the derivative holding `v` fixed is
`k+v=k/(1-r)<0`. Thus the increased root remains cap-Nash, keeps marked
output0 equal to zero, and strictly reduces Never. This rules out sole0 for every sign of `u1`.

Next suppose `p=0,z>0`, so the incoming support is 03. Put `a=z/10`.
The paid identities and the inactive owner2 cap give

    u0=-a,    y=2r,    x>=z(4-3r)-r/10.

The first bad-output inequality (B3), with `M<=4`, implies

    x(4r-1)>r+z/10.

Thus `r>1/4`, `r<=1/2` by the actual floor, and
`x>r/(4r-1)>=1/2`.

There is an explicit outgoing root candidate with active support 02:

    q0'=x/(x+9/10),    q2'=a/(1+a),    q1'=q3'=0. (B8)

Its active owners are exactly indifferent and owner0's output is negative.
After multiplication by the positive denominator `(x+9/10)(1+a)`, the
inactive gaps are

    G1=-4x-(31/10)ax+(81/100)a-(9/10)u1<0,
    G3=(9/10)y-x(1+3a)-(9/5)a.

For `G1<0`, use `u1>=-1`, `x>1/2`, `0<a<1/10`. If `G3<=0`, (B8)
is a good root contradicting minimum status. Otherwise `x<(9/5)r`,
which together with the lower bound on `x` implies `r>7/18`.

The genuine zero-debt tail of the incoming03 root has

    v0=(9/10)z/(1-z)>0,
    v3=-r/(1-r)<-1/10,
    v2=[x+r-3z(1-r)]/[(1-r)(1-z)]>0.

The last numerator is at least `z+(9/10)r` by the incoming owner2 cap.
Apply (B5) to this actual tail. It gives the lower bound

    z >= (713r+155x-323)/(142+93r),

whereas the incoming owner2 cap gives the upper bound

    z <= (x+r/10)/(4-3r).                          (B9)

These bounds are inconsistent. Their lower-minus-upper difference equals

    [21483r^2+5580rx-38068r-4780x+12920]
      /[10(3r-4)(93r+142)].

The denominator is negative. The numerator decreases in `x` on
`7/18<=r<=1/2`. At `x=r/(4r-1)` it equals `P(r)/(4r-1)`, where

    P=85932r^3-168175r^2+84968r-12920.

Its degree-three Bernstein coefficients on `[7/18,1/2]` are

    -9245/36, -496111/972, -112699/108, -6953/4.

They are all negative. The difference in (B9) is therefore positive, a
contradiction. Every incoming03 case has now been eliminated.

### B7. Incoming023: positivity of a genuine marked tail

The only remaining incoming support is 023. Write its hazards `(r,0,b,c)`,
all three strictly between zero and one. The exact paid outputs are

    x=c(4-3r)-r/10,
    y=2r+b(3r-1),
    a=-u0=2b+c/10-bc>0.                            (B10)

The exact actual tail has

    v2=[(9/10)r+c]/[(1-r)(1-c)]>0,
    v3=-(r+2b)/[(1-r)(1-b)],
    v0=[-b+(9/10)c-(M+1)bc]/[(1-b)(1-c)].         (B11)

Its actual floor `v3>=-1` implies

    2r+3b-rb<=1.                                  (B12)

The bad D-only output0 and `M<=4` give

    D:=4xy-y-2x-2a>0.                             (B13)

In particular `y>1/2`, so `r>1/4`: for `r<=1/4`, (B10) would give
`y<=2r<=1/2`. Equation (B12) gives `r<=1/2`. Also `b<9/50`. To see the
last bound, substitute the maximum possible `r=(1-3b)/(2-b)` into the
increasing function `y(r,b)`. Its difference from `1/2` is

    (16b^2+9b-2)/[2(b-2)].

Thus `y>1/2` forces `16b^2+9b-2<0`. This polynomial is increasing for
`b>=0` and is positive at `9/50`, proving the claim.

We next prove `v0>0`, so that (B5) applies to this tail. If `v0<=0`, then
`M<=4` and `b<9/50` imply

    c<=b/(9/10-5b).

Write `D=d0+dc*c`, where direct substitution in (B10) gives

    d0=-(6br^2+13br+15b+4r^2+9r)/5<0,
    dc=-(180br^2-300br+70b+120r^2-190r+41)/5.

As `D>0`, necessarily `dc>0`. At the asserted upper bound on `c`,

    D <= S/[5(50b-9)],
    S=1500b^2r^2-3650b^2r-50b^2+1054br^2-2233br
         +545b+36r^2+81r.                          (B14)

The denominator is negative, and `S>0` on the required floor domain. Here
is a finite exact certificate. Substitute `r=t(1-3b)/(2-b)`, with
`0<=t<=1`, and multiply `S` by `(2-b)^2`. The resulting polynomial has
degree four in `b` and two in `t`. Its tensor Bernstein coefficients on the
following rectangles have the listed minimum:

| b interval | t interval | minimum coefficient |
|---|---|---:|
| `[0,9/100]` | `[0,1]` | `0` |
| `[9/100,27/200]` | `[0,1]` | `113404437/16000000` |
| `[27/200,9/50]` | `[0,1]` | `1416969/2000000` |

On the first rectangle its only zero coefficient is the constant corner;
all other coefficients are strictly positive. Thus the polynomial is positive
whenever `t>0`, as here. These exact coefficients, reconstructed by the
checker below, prove `S>0`. Equation (B14) contradicts `D>0`. Therefore
`v0>0`. Moreover `r>1/4` implies `v3<-1/3<-1/10`.

### B8. Incoming023: the forced-123 tail is inconsistent with bad funding

All hypotheses of (B5) now hold for the genuine tail (B11). Multiply that
inequality by `470(1-r)(1-b)(1-c)>0`. The result is

    f0+fc*c>=0,
    f0=646-1395r-1586b+925br,
    fc=-646br+1896b+1116r-956.                     (B15)

On the entire rectangle `1/4<=r<=1/2`, `0<=b<=9/50`, the bilinear
polynomial `fc` is strictly negative, as its four corner values show. Hence
`c<=f0/(-fc)`. Recall that `dc>0` follows from `D>0`. We obtain

    D<=d0+dc*f0/(-fc).

The numerator of the right side, multiplied by five, is

    G=-170376b^2r^3+565958b^2r^2-525592b^2r+139460b^2
        +144212br^3-158168br^2-26439br+5466b
        +171864r^3-336350r^2+171331r-26486.         (B16)

This polynomial is strictly negative on that rectangle. Its tensor Bernstein
degrees are three in `r` and two in `b`. With `b` in `[0,9/50]`, the
following three subdivisions have the listed largest coefficient:

| r interval | largest coefficient |
|---|---:|
| `[1/4,3/10]` | `-89734/125` |
| `[3/10,2/5]` | `-140297/750` |
| `[2/5,1/2]` | `-96288/125` |

All coefficients are strictly negative, proving `G<0`. Since `-fc>0`,
we have `D<0`, contradicting (B13). This eliminates incoming023 and closes
the exhaustive incoming-support classification.


The cases are exhaustive: a negative-payoff marked minimum forces a bad
outgoing root23; its proper actual incoming support contains a marked owner;
the alternatives are both marked, only marked1, sole0, 03, and 023. Each is
excluded. Thus every such minimum has nonnegative payoff. Combining this
with the common nonnegative-minimum exclusion and absorbing-repair argument
proves that the native absorbing debt infimum is zero on the entire box.

### B9. Complete exact polynomial checker

The following complete Python3 program uses SymPy and has no input file,
random sample, numerical optimization, or dependence on another checker.
It reconstructs all60 reward coordinates and verifies every algebraic
identity and sign certificate used in this classification. The genuine-tail
and minimality arguments are the mathematical proof above.

For clarity, the exact tensor Bernstein identity used by the program is as
follows. After an affine substitution to [0,1]^d, let p have power
coefficients a_k and coordinate degrees n. Its Bernstein coefficients are

    beta_i=sum_(k<=i) a_k product_j binom(i_j,k_j)/binom(n_j,k_j).

The basis polynomials are nonnegative and sum to one. Hence uniform strict
coefficient signs prove the corresponding polynomial sign throughout the
closed box. In the one certificate with a single zero corner coefficient,
every point away from that corner has a positive weight on another,
strictly positive coefficient. In particular the asserted positivity at
t>0 follows, including the other boundary faces.

Save this block as a Python file and run it with Python3 and SymPy installed.

```python
from itertools import product
from math import comb
import sympy as s

R = s.Rational
M, N, T = s.symbols('M N T', nonnegative=True)
r, t, p, z, b, c, x, y, a = s.symbols('r t p z b c x y a')
Z = {
    (0,): (0, 3, -1, -1), (1,): (3, 0, -1, -1),
    (2,): (-1, -1, 0, 3), (3,): (-1, -1, 3, 0),
    (0, 1): (-1, -1, -1, -1),
    (0, 2): (-2, -1, -R(1, 10), -1),
    (0, 3): (-R(1, 10), -1, -1, -2),
    (1, 2): (-1, -R(1, 10), -2, -1),
    (1, 3): (-1, -2, -1, -R(1, 10)),
    (2, 3): (M, N, 4, 1),
    (0, 1, 2): (-6, -R(41, 10), -R(11, 10), -1),
    (0, 1, 3): (-R(41, 10), -6, -1, -R(11, 10)),
    (0, 2, 3): (-R(11, 10), -1, R(9, 10), -4),
    (1, 2, 3): (-1, -R(11, 10), -1, -R(21, 10)),
    (0, 1, 2, 3): (-M-T-R(61, 10), -N-R(61, 10), -R(1, 10), -R(31, 10)),
}
assert len(Z) * 4 == 60


def zero(expr):
    assert s.cancel(expr) == 0, s.factor(expr)


def endpoints(q):
    P, Q, H = [], [], []
    for i in range(4):
        opp = [j for j in range(4) if j != i]
        pi = qi = 0
        for bits in product((0, 1), repeat=3):
            A = tuple(j for j, bit in zip(opp, bits) if bit)
            mass = s.prod(q[j] if bit else 1-q[j] for j, bit in zip(opp, bits))
            pi += mass * (Z[A][i] if A else 0)
            qi += mass * Z[tuple(sorted(A+(i,)))][i]
        P.append(s.expand(pi))
        Q.append(s.expand(qi))
        H.append(s.prod(1-q[j] for j in opp))
    return P, Q, H


def bernstein(poly, variables, bounds):
    """Full tensor Bernstein coefficients, with exact affine substitutions."""
    tt = s.symbols('tau:'+str(len(variables)))
    repl = {v: lo+(hi-lo)*u for v, u, (lo, hi) in zip(variables, tt, bounds)}
    pp = s.Poly(s.expand(poly.subs(repl)), *tt)
    deg = pp.degree_list()
    out = {}
    for idx in product(*(range(n+1) for n in deg)):
        out[idx] = sum(coef*s.prod(R(comb(i, k), comb(n, k))
                                  for i, k, n in zip(idx, mon, deg))
                       for mon, coef in pp.terms()
                       if all(k <= i for i, k in zip(idx, mon)))
    return out


P, Q, H = endpoints((r, t, p, z))
L = s.Matrix([[0, -4, -1, R(9, 10)], [-4, 0, R(9, 10), -1],
              [R(9, 10), -1, 0, 1], [-1, R(9, 10), -2, 0]])
for i in range(4):
    correction = ((M+1)*p*z+T*t*p*z if i == 0 else
                  (N+1)*p*z if i == 1 else 0)
    zero(Q[i]-P[i]-(L*s.Matrix([r, t, p, z]))[i]+correction)
    assert all(s.sympify(Z[A][i]+1).is_nonnegative for A in Z if i not in A)
for i in (0, 1):
    assert all(s.sympify(-R(1, 10)-Z[A][i]).is_nonnegative
               for A in Z if i in A and len(A) >= 2)
zero(Q[2]-(3*r*t*z+r*t-3*r*z-r/10-3*t*z-2*t+4*z))
zero(Q[3]-(3*p*r*t-3*p*r-3*p*t+p+r*t-2*r-t/10))

# Exact D-only root and its marked output numerators.
PD, QD, HD = endpoints((0, 0, y/(2+y), x/(1+x)))
zero(QD[2]-PD[2]-HD[2]*x)
zero(QD[3]-PD[3]+HD[3]*y)
for i, K in ((0, M), (1, N)):
    zero(PD[i]/HD[i]-(K*x*y/2-x-y/2))

# Both anchors paid: exact Never-floor bounds and the Q3 lower bound.
h = 5-p-z+p*z
zero(Q[0]-P[0]+H[0]-(1-2*p-z/10-h*t-M*p*z-T*t*p*z))
zero(Q[1]-P[1]+H[1]-(1-p/10-2*z-h*r-N*p*z))
zero(9*h-40*(1-2*p-z/10)-(5*(1-z)+p*(71+9*z)))
rp = (1-p/10)/(5-p)
zero((rp-(1-p/10-2*z)/h)*(5-p)*h-z*(9-R(9, 10)*p-p*p/10))
minus_q3 = -Q[3]
assert min(bernstein(s.diff(minus_q3, r), (p, t), ((0, R(1, 2)), (0, R(9, 40)))).values()) > 0
zero((R(1, 2)-minus_q3.subs({r: rp, t: 0}))-(5+17*p-7*p*p)/(10*(5-p)))
zero((R(1, 2)-minus_q3.subs({r: rp, t: R(9, 40)}))
     -(245-400*p-37*p*p)/(400*(5-p)))
assert min(bernstein(5+17*p-7*p*p, (p,), ((0, R(1, 2)),)).values()) > 0
assert min(bernstein(245-400*p-37*p*p, (p,), ((0, R(1, 2)),)).values()) > 0

# Forced123 output identities and the maximum possible D-funding surplus.
for i, expr in ((1, p*z-p/10-2*z), (2, z*(4-3*t)-2*t),
                (3, p*(1-3*t)-t/10)):
    zero(Q[i].subs(r, 0)-expr)
zero(R(9, 10)-(1-p/10)/(2-p)-R(4, 5)*(1-p)/(2-p))
F = 2*x*y-x-y/2
fy = s.expand(F.subs(x, R(47, 31)*(R(323, 235)-y)))
zero(fy-(-R(94, 31)*y*y+R(1607, 310)*y-R(323, 155)))
ymax = R(1607, 1880)
zero(fy.subs(y, ymax)-R(153489, 1165600))
assert R(153489, 1165600) < R(2, 9)

# Sole0 root: all binding inactive gaps decrease as its hazard increases.
for coefficient in (-4, -1):
    v = s.symbols('v')
    gap = coefficient*r-(1-r)*v
    zero(s.diff(gap, r).subs(v, -coefficient*r/(r-1))-coefficient/(1-r))

# Incoming03 and its explicit outgoing02 alternative.
P03, Q03, H03 = endpoints((r, 0, 0, z))
zero(Q03[0]+z/10)
zero(Q03[3]+2*r)
zero(Q03[2]-(z*(4-3*r)-r/10))
v03 = [R(9, 10)*z/(1-z), None,
       (x+r-3*z*(1-r))/((1-r)*(1-z)), -r/(1-r)]
zero(Q03[0]-P03[0]-H03[0]*v03[0])
zero(Q03[3]-P03[3]-H03[3]*v03[3])
zero(P03[2]+H03[2]*v03[2]-x)
P02, Q02, H02 = endpoints((x/(x+R(9, 10)), 0, a/(1+a), 0))
u1 = s.symbols('u1')
u = [-a, u1, x, -y]
g02 = [s.cancel(Q02[i]-P02[i]-H02[i]*u[i]) for i in range(4)]
zero(g02[0]); zero(g02[2])
zero(g02[1]*(x+R(9, 10))*(1+a)-(-4*x-R(31, 10)*a*x+R(81, 100)*a-R(9, 10)*u1))
zero(g02[3]*(x+R(9, 10))*(1+a)-(R(9, 10)*y-x*(1+3*a)-R(9, 5)*a))
trade03 = s.cancel((v03[3]-R(31, 47)*v03[2]+R(323, 235))*235*(1-r)*(1-z))
zero(trade03-(323-713*r-155*x+(142+93*r)*z))
lo = (713*r+155*x-323)/(142+93*r)
hi = (x+r/10)/(4-3*r)
n03 = 21483*r*r+5580*r*x-38068*r-4780*x+12920
zero(lo-hi-n03/(10*(3*r-4)*(93*r+142)))
poly03 = 85932*r**3-168175*r*r+84968*r-12920
zero(n03.subs(x, r/(4*r-1))-poly03/(4*r-1))
bc03 = list(bernstein(poly03, (r,), ((R(7, 18), R(1, 2)),)).values())
assert bc03 == [-R(9245, 36), -R(496111, 972), -R(112699, 108), -R(6953, 4)]

# Incoming023: paid outputs, true suffix, and its passive floor.
P23, Q23, H23 = endpoints((r, 0, b, c))
xx = c*(4-3*r)-r/10
yy = 2*r+b*(3*r-1)
aa = 2*b+c/10-b*c
zero(Q23[0]+aa); zero(Q23[2]-xx); zero(Q23[3]+yy)
v23 = [(-b+R(9, 10)*c-(M+1)*b*c)/((1-b)*(1-c)), None,
       (R(9, 10)*r+c)/((1-r)*(1-c)), -(r+2*b)/((1-r)*(1-b))]
for i in (0, 2, 3):
    zero(Q23[i]-P23[i]-H23[i]*v23[i])
zero((v23[3]+1)*(1-r)*(1-b)-(1-2*r-3*b+r*b))
zero((yy-R(1, 2)).subs(r, (1-3*b)/(2-b))-(16*b*b+9*b-2)/(2*(b-2)))
assert (16*b*b+9*b-2).subs(b, R(9, 50)) > 0
D = s.expand(4*xx*yy-yy-2*xx-2*aa)
d0 = -(6*b*r*r+13*b*r+15*b+4*r*r+9*r)/5
dc = -(180*b*r*r-300*b*r+70*b+120*r*r-190*r+41)/5
zero(D-d0-dc*c)
S = (1500*b*b*r*r-3650*b*b*r-50*b*b+1054*b*r*r-2233*b*r
     +545*b+36*r*r+81*r)
zero(D.subs(c, b/(R(9, 10)-5*b))-S/(5*(50*b-9)))
ss = s.cancel(S.subs(r, t*(1-3*b)/(2-b))*(2-b)**2)
mins = []
for blo, bhi in ((0, R(9, 100)), (R(9, 100), R(27, 200)), (R(27, 200), R(9, 50))):
    coeffs = bernstein(ss, (b, t), ((blo, bhi), (0, 1)))
    mins.append(min(coeffs.values()))
    if blo == 0:
        assert coeffs[(0, 0)] == 0
        assert all(v > 0 for idx, v in coeffs.items() if idx != (0, 0))
    else:
        assert min(coeffs.values()) > 0
assert mins == [0, R(113404437, 16000000), R(1416969, 2000000)]

# The actual suffix's forced123 tradeoff contradicts D>0.
f0 = 646-1395*r-1586*b+925*b*r
fc = -646*b*r+1896*b+1116*r-956
zero((v23[3]-R(31, 47)*v23[2]+R(323, 235))*470*(1-r)*(1-b)*(1-c)-f0-fc*c)
assert max(bernstein(fc, (r, b), ((R(1, 4), R(1, 2)), (0, R(9, 50)))).values()) < 0
G = (-170376*b*b*r**3+565958*b*b*r*r-525592*b*b*r+139460*b*b
     +144212*b*r**3-158168*b*r*r-26439*b*r+5466*b
     +171864*r**3-336350*r*r+171331*r-26486)
zero(G-5*(d0*(-fc)+dc*f0))
maxs = []
for rlo, rhi in ((R(1, 4), R(3, 10)), (R(3, 10), R(2, 5)), (R(2, 5), R(1, 2))):
    coeffs = bernstein(G, (r, b), ((rlo, rhi), (0, R(9, 50))))
    maxs.append(max(coeffs.values()))
    assert max(coeffs.values()) < 0
assert maxs == [-R(89734, 125), -R(140297, 750), -R(96288, 125)]

print('PASS: full60 symbolic family, all first-date polynomials and passive floors.')
print('PASS: both-anchor, sole1/123, sole0 and incoming03 exact reductions.')
print('PASS: genuine023 suffix, positive marked tail and strict Bernstein contradiction.')
print('PASS: all bounds are uniform for 0<=M,N<=4 and every T>=0.')
```

## R. Complete incoming023 exclusion on the extended parameter range

### R1. Exact source conclusion

Assume0<=M<=9,N>=2,T>=0. Let Y be a positive-Never marked zero-debt
minimum as constructed in Sections3--4, and suppose its payoff has a negative
coordinate. If its genuine proper incoming root has support023, every
nonzero outgoing Nash root at Y must be the bad proper pair23 with both
marked outputs positive. Indeed an active marked owner is paid a nonpositive
participant reward; a singleton2 or3 sends any nonpositive marked input to a
strictly negative output; and a D-only two-owner root cannot have a unit
hazard. Its active equations force U2>0,U3<0. We now exclude this entire
incoming023 case. All passive bounds used below were proved in Section4.
Only the ORIGINAL point Y minimizes Never; no such property is assigned to
its genuine conditional tail.

### R2. Exact incoming equations and necessary funding

Write incoming hazards as (r,0,b,c), all r,b,c in (0,1), its output as
U=(-m,u_1,x,-d), and its actual tail as V=(z,v_1,X,-D). The only bad outgoing
pair23 gives x,d>0. Literal endpoint evaluation yields

```
x = c(4-3r)-r/10,
d = 2r+b(3r-1),
m = 2b+c/10-bc > 0,
X = ((9/10)r+c)/((1-r)(1-c)) > 0,
D = (r+2b)/((1-r)(1-b)) > 0,
z = (-b+(9/10)c-(M+1)bc)/((1-b)(1-c)).
```

Its bad marked output0 requires

```
F = Mxd-d-2x-2m > 0.                                (1)
```

The actual tail bounds D<=1 and X<=3 respectively give

```
1-2r-3b+rb >= 0,
3-(39/10)r-c(4-3r) >= 0.                            (2)
```

Thus r<=1/2, b<=1/3, c<=3/4. The actual current floor also gives d<=1.
Inequality (1) implies Md>2, so M>2. If r<=1/3, then d<=2r, hence Mr>1
and r>1/9 since M<=9. If r>1/3, then r>1/9 directly. The assertion Mr>1
is used below only in the small-r case, where it has just been proved.

### R3. Positive tail coordinate0

First suppose z>0. If D<=1/10, then D<1/5. Otherwise the actual tail's own
incoming row must have support123: positive coordinate0 excludes owner0;
negative coordinate3 forces owner1; D>1/10 forces owner2; and positive
coordinate2 forces owner3.

A genuine proper123 row with hazards (0,a,b,c), actual input coordinate1 at
least -1, and positive paid coordinate2 has

```
c <= (1-b/10)/(2+Nb) <= (1-b/10)/(2+2b),
a < (40-4b)/(70+37b),
-V_3 = a(1/10+3b)-b
     < (40+496b-490b^2)/(700+370b) < 1/5.
```

The first inequality is the input1 equation; the second follows from
V_2=c(4-3a)-2a>0. The last follows from
490b^2-422b+100>0, whose discriminant is -17916. Therefore D<1/5 in either
case. Its explicit formula implies r<1/6, hence

```
d = 2r+b(3r-1) < 1/3.
```

Now (1) and M<=9 give (9d-2)x>d+2m and consequently x>1/3. At the current
payoff choose the outgoing02 row q_0=x/(x+9/10), q_2=m/(1+m). The active
owners are indifferent and its owner0 output is negative. Its inactive gap
numerators are

```
G_1 = -4x-(31/10)mx+(81/100)m-(9/10)u_1,
G_3 = (9/10)d-x(1+3m)-(9/5)m.
```

The floor u_1>=-1 and x>1/3 give G_1<0; d<1/3 and x>1/3 give G_3<0.
This full root contradicts minimum status. Hence it remains to consider z<=0.

### R4. Tail02 is a full Nash row when z<=0

Set a=-z>=0. At the genuine tail choose

```
p_0=X/(X+9/10), p_2=a/(1+a), p_1=p_3=0.
```

The two active equations hold. This includes a=0, when owner2 uses Continue
and is tied. Its inactive1 gap is bounded above using v_1>=-1 by

```
T_1 = 9/10-4X+a(81/100-(31/10)X).                  (3)
```

We prove X>81/310. If r>=1/3, then X>(9/10)r/(1-r)>=9/20. If r<=1/3,
then d<=2r and (1) imply x>r/(9r-1). Also

```
X > ((37/40)r+x/4)/(1-r).
```

Subtracting81/310 after this lower bound gives

```
9(1471r^2-453r+36)/(1240(1-r)(9r-1)) > 0,
```

because the quadratic's discriminant is -6615. Both coefficients in (3)
are therefore strictly negative, so the inactive1 cap is strict.

The inactive3 gap numerator is

```
T_3 = (9/10)D-X(1+3a)-(9/5)a.
```

A literal substitution gives

```
-100(1-r)(1-b)(1-c)^2 T_3 = c L,
L = Mb(180cr+120c+90r+180)
  + b(180cr+40c+360r+560)-252cr-208c+9r-62.
```

The condition z<=0 gives b>=b_0=(9/10)c/(1+(M+1)c). Since L is increasing
in b,

```
L >= L(b_0)
   = (1-c)[90Mcr+100Mc+90cr+172c+9r-62]/[1+(M+1)c].
```

It is enough to prove

```
c > c_star = (62-9r)/[M(90r+100)+90r+172].           (4)
```

For r<=1/3, (1) and d<=2r give

```
c > r(Mr+9)/[10(Mr-1)(4-3r)].
```

The difference between this lower bound and c_star has positive denominator
10(4-3r)(Mr-1)(45Mr+50M+45r+86), and numerator

```
P = 45M^2r^3+50M^2r^2-90Mr^3+1601Mr^2-790Mr
  +540r^2-336r+1240.
```

In tensor Bernstein order (M index first, then r index), its degree(2,3)
coefficients on [0,9] x [1/9,1/3] are

```
3628/3, 3580/3, 10676/9, 1188,
16249/18, 40007/54, 12677/18, 1577/2,
5860/9, 11342/27, 1552/3, 974.
```

All are positive. For r>=1/3, use d<=1 in (1) to obtain x>1/(M-2), hence

```
c > [1/(M-2)+r/10]/(4-3r).
```

Its difference from c_star has positive denominator
10(M-2)(4-3r)(45Mr+50M+45r+86), and numerator

```
Q = 45M^2r^2+50M^2r-180Mr^2+1546Mr-740M
  +180r^2-1942r+3340.
```

The degree(2,2) Bernstein coefficients on [0,9] x [1/3,1/2] are

```
8138/3, 15365/6, 2414,
4835/3, 23935/12, 2360,
6797/3, 11170/3, 20969/4.
```

Again all are positive. This proves (4), so L>0 and T_3<0. Tail02 is a full
Nash row for every surviving source, including z=0.

### R5. One more Nash row supplies a quantified survival reduction

Let W be the output of that tail02 prefix. Owner2 is paid, or tied at a=0,
so

```
W_2 = -h, where h=X/(10X+9)>0.
```

Choose ANY finite Nash root q at W, whose existence is finite-game Nash
existence. Let S=product_i(1-q_i) be its survival. If q_2=1 then S=0.
Otherwise Continue is supported for owner2. The complete literal owner2 gap
is

```
g_2 = (9/10)q_0-q_1+q_3+h(1-q_0)(1-q_1)(1-q_3) <= 0.
```

Consequently q_1>=h(1-q_0)(1-q_1)(1-q_3)>=hS. Since 1-S>=q_1, one has

```
S <= 1/(1+h).
```

This root's output has a nonpositive marked coordinate. If either marked
owner is active, that owner is paid a nonpositive participant reward. If both
are inactive, the displayed gap is strictly positive unless q_2=1. In that
case owner3's gap is -2, so q_3=0; sole sure2 pays both marked owners -1.
This argument includes unit hazards and does not assume a selected support.

Prefix the actual tail first by tail02, then prefix its output by this Nash
row. Both prefix operations preserve zero complete debt. The final point
belongs to E_C. Its survival relative to the SAME genuine tail is at most

```
[9/((10X+9)(1+a))] * [(10X+9)/(11X+9)]
  = 9/[(11X+9)(1-z)].                               (5)
```

The original incoming row has survival (1-r)(1-b)(1-c). The exact certificate
in Section R6 proves (5) is strictly smaller. The new point therefore has
strictly smaller Never product than the original minimum. This contradiction
excludes the entire z<=0 branch.

### R6. Exact survival comparison

Clearing positive denominators, the required strict survival comparison is

```
H = (9+(9/10)r+2c+9rc)
      *(1-(19/10)c+(M+2)bc)-9(1-c) > 0.              (6)
```

It holds on the larger semialgebraic domain

```
0<=M<=9, 1/9<=r<=1/2, 0<=b<=1/3, 0<=c<=3/4,
F=Mxd-d-2x-2m>0,
b-(9/10)c+(M+1)bc>=0,
1-2r-3b+rb>=0,
3-(39/10)r-c(4-3r)>=0,
```

where x,d,m are exactly those of Section R2. An exact rational tensor Bernstein
subdivision certificate establishes (6), with complete code in Section R7.

For each polynomial, substitute affine coordinates for the displayed box.
For a power polynomial with coefficients c_k and multidegree n, its tensor
Bernstein coefficients are

```
beta_i = sum_(k<=i) c_k product_j binom(i_j,k_j)/binom(n_j,k_j).
```

The Bernstein basis is nonnegative and sums to one, so its coefficients bound
the polynomial on the box. The checker covers the initial box by a finite
binary tree of exact midpoint subdivisions. At each box it either establishes
strictly positive target coefficients, excludes F>0 using nonpositive funding
coefficients, excludes a required weak constraint using strictly negative
coefficients, or exactly subdivides using rational de Casteljau recursion.
It succeeds only when every leaf is certified or excluded. The subdivision
heuristic uses rational variation; its choice affects proof size but not any
leaf inference. There are no numerical sign tests or sampled inferences.

The H certificate has2861 total nodes, maximum depth23, and leaf counts
646 positive,187 funding excluded,525 sign-z excluded,30 floor excluded,
and43 upper-bound excluded. Its1431 leaves satisfy2861=2*1431-1. The same
program independently verifies L>0 with1039 nodes and520 leaves; Section R4
already provides the smaller explicit certificate for that conclusion.
All node arithmetic is rational, including every box boundary. Thus the
finite tree proves the universal strict inequality on the stated domain.


### R7. Complete exact programs

Save each block separately and run it with Python3 and SymPy. The first
reconstructs all literal endpoints and both cap certificates on0<=M<=9.
The second independently reconstructs all literal endpoints and verifies
both universal subdivision certificates. Each complete block runs without
another project file; all sign arithmetic is exact rational arithmetic.

```python
"""Exact caps and arbitrary-second-root bound for the incoming023 tail02 word.

Scope: 0<=M<=9,N>=2,T>=0, and the source assumptions stated above.
This checker does not include the separate strict two-step survival budget.
Save and run this standalone block with Python3 and SymPy.
"""
from itertools import product
from math import comb
import sympy as s

R = s.Rational
r, t, p, z, M, N, T = s.symbols('r t p z M N T')
Z = {
    (0,): (0, 3, -1, -1), (1,): (3, 0, -1, -1),
    (2,): (-1, -1, 0, 3), (3,): (-1, -1, 3, 0),
    (0, 1): (-1, -1, -1, -1),
    (0, 2): (-2, -1, -R(1, 10), -1),
    (0, 3): (-R(1, 10), -1, -1, -2),
    (1, 2): (-1, -R(1, 10), -2, -1),
    (1, 3): (-1, -2, -1, -R(1, 10)),
    (2, 3): (M, N, 4, 1),
    (0, 1, 2): (-6, -R(41, 10), -R(11, 10), -1),
    (0, 1, 3): (-R(41, 10), -6, -1, -R(11, 10)),
    (0, 2, 3): (-R(11, 10), -1, R(9, 10), -4),
    (1, 2, 3): (-1, -R(11, 10), -1, -R(21, 10)),
    (0, 1, 2, 3): (-M-T-R(61, 10), -N-R(61, 10),
                    -R(1, 10), -R(31, 10)),
}


def zero(e):
    assert s.cancel(e) == 0, s.factor(e)


def endpoints(q):
    P, Q, H = [], [], []
    for i in range(4):
        opp = [j for j in range(4) if j != i]
        pp = qq = 0
        for bits in product((0, 1), repeat=3):
            A = tuple(j for j, bit in zip(opp, bits) if bit)
            mass = s.prod(q[j] if bit else 1-q[j]
                          for j, bit in zip(opp, bits))
            pp += mass * (Z[A][i] if A else 0)
            qq += mass * Z[tuple(sorted(A+(i,)))][i]
        P.append(s.expand(pp))
        Q.append(s.expand(qq))
        H.append(s.prod(1-q[j] for j in opp))
    return P, Q, H


def bernstein(poly, variables, bounds):
    tt = s.symbols('tau:'+str(len(variables)))
    repl = {v: lo+(hi-lo)*u for v, u, (lo, hi)
            in zip(variables, tt, bounds)}
    pp = s.Poly(s.expand(poly.subs(repl)), *tt)
    deg = pp.degree_list()
    out = []
    for idx in product(*(range(n+1) for n in deg)):
        out.append(sum(coef*s.prod(R(comb(i, k), comb(n, k))
                                  for i, k, n in zip(idx, mon, deg))
                       for mon, coef in pp.terms()
                       if all(k <= i for i, k in zip(idx, mon))))
    return out


b, c, a, X, D, v1 = s.symbols('b c a X D v1')
P, Q, H = endpoints((r, t, p, z))
Pi, Qi, Hi = endpoints((r, 0, b, c))
x = c*(4-3*r)-r/10
d = 2*r+b*(3*r-1)
m = 2*b+c/10-b*c
xt = (R(9, 10)*r+c)/((1-r)*(1-c))
dt = (r+2*b)/((1-r)*(1-b))
at = (b-R(9, 10)*c+(M+1)*b*c)/((1-b)*(1-c))
zero(Qi[0]+m); zero(Qi[2]-x); zero(Qi[3]+d)
zero((Qi[0]-Pi[0])/Hi[0]+at)
zero((Qi[2]-Pi[2])/Hi[2]-xt)
zero((Qi[3]-Pi[3])/Hi[3]+dt)

# Literal tail02 active equations and all four output coordinates needed below.
qq = (X/(X+R(9, 10)), 0, a/(1+a), 0)
Po, Qo, Ho = endpoints(qq)
v = [-a, v1, X, -D]
g = [s.cancel(Qo[i]-Po[i]-Ho[i]*v[i]) for i in range(4)]
zero(g[0]); zero(g[2])
T1 = R(9, 10)-4*X+a*(R(81, 100)-R(31, 10)*X)
T3 = R(9, 10)*D-X*(1+3*a)-R(9, 5)*a
scale = (X+R(9, 10))*(1+a)
zero(g[1]*scale-(T1-R(9, 10)*(v1+1)))
zero(g[3]*scale-T3)
zero(Qo[0]+2*a/(1+a))
zero(Qo[2]+X/(10*X+9))
zero(Po[2]+Ho[2]*X+X/(10*X+9))

# Cap1: X>81/310, without any additional restriction on a>=0.
small_x_lower = r/(9*r-1)
small_X_lower = (R(37, 40)*r+small_x_lower/4)/(1-r)
zero(small_X_lower-R(81, 310)
     -9*(1471*r*r-453*r+36)/(1240*(1-r)*(9*r-1)))
assert 453**2-4*1471*36 == -6615
assert R(9, 20) > R(81, 310)
assert R(9, 10)-4*R(81, 310) < 0
zero(R(81, 100)-R(31, 10)*R(81, 310))

# Cap3: isolate the exact threshold supplied by v0<=0.
L = (M*b*(180*c*r+120*c+90*r+180)
     +b*(180*c*r+40*c+360*r+560)-252*c*r-208*c+9*r-62)
zero(-T3.subs({X: xt, D: dt, a: at})
     *100*(1-r)*(1-b)*(1-c)**2-c*L)
bmin = R(9, 10)*c/(1+(M+1)*c)
J = 90*M*c*r+100*M*c+90*c*r+172*c+9*r-62
zero(L.subs(b, bmin)-(1-c)*J/(1+(M+1)*c))
cthresh = (62-9*r)/(M*(90*r+100)+90*r+172)
zero(J-(M*(90*r+100)+90*r+172)*(c-cthresh))
low_small = r*(M*r+9)/(10*(M*r-1)*(4-3*r))
Pcert = (45*M*M*r**3+50*M*M*r*r-90*M*r**3+1601*M*r*r
         -790*M*r+540*r*r-336*r+1240)
common = 45*M*r+50*M+45*r+86
zero(low_small-cthresh-Pcert/(10*(4-3*r)*(M*r-1)*common))
pbc = bernstein(Pcert, (M, r), ((0, 9), (R(1, 9), R(1, 3))))
assert pbc == [R(3628, 3), R(3580, 3), R(10676, 9), 1188,
               R(16249, 18), R(40007, 54), R(12677, 18), R(1577, 2),
               R(5860, 9), R(11342, 27), R(1552, 3), 974]
assert min(pbc) == R(11342, 27) > 0
low_large = (1/(M-2)+r/10)/(4-3*r)
Qcert = (45*M*M*r*r+50*M*M*r-180*M*r*r+1546*M*r
         -740*M+180*r*r-1942*r+3340)
zero(low_large-cthresh-Qcert/(10*(M-2)*(4-3*r)*common))
qbc = bernstein(Qcert, (M, r), ((0, 9), (R(1, 3), R(1, 2))))
assert qbc == [R(8138, 3), R(15365, 6), 2414,
               R(4835, 3), R(23935, 12), 2360,
               R(6797, 3), R(11170, 3), R(20969, 4)]
assert min(qbc) == R(4835, 3) > 0

# Every subsequent Nash root has the claimed survival bound, including
# inactive-player2 and all sure-hazard boundaries.
h = s.symbols('h')
zero(Q[2]-P[2]+H[2]*h-(R(9, 10)*r-t+z+H[2]*h))
zero((Q[3]-P[3]).subs({r: 0, t: 0, p: 1})+2)
first_survival = s.prod(1-u for u in qq)
second_survival_bound = 1/(1+X/(10*X+9))
zero(first_survival*second_survival_bound-9/((11*X+9)*(1+a)))
print('PASS: tail02 full caps and arbitrary-second-Nash survival/marked-output coverage')
```

```python
"""Exact formula17 tail02 cap3 and two-step replacement survival budget.

All polynomial signs use rational tensor Bernstein coefficients and exact
midpoint subdivision. Branch choices are rational; numerical optimization is
not used. The source scope and finite subdivision proof are stated above.
"""
from fractions import Fraction
from itertools import product
from math import comb
import sympy as s

R = s.Rational
M, N, T, r, b, c = s.symbols('M N T r b c')
Z = {
    (0,): (0, 3, -1, -1), (1,): (3, 0, -1, -1),
    (2,): (-1, -1, 0, 3), (3,): (-1, -1, 3, 0),
    (0, 1): (-1, -1, -1, -1),
    (0, 2): (-2, -1, -R(1, 10), -1),
    (0, 3): (-R(1, 10), -1, -1, -2),
    (1, 2): (-1, -R(1, 10), -2, -1),
    (1, 3): (-1, -2, -1, -R(1, 10)),
    (2, 3): (M, N, 4, 1),
    (0, 1, 2): (-6, -R(41, 10), -R(11, 10), -1),
    (0, 1, 3): (-R(41, 10), -6, -1, -R(11, 10)),
    (0, 2, 3): (-R(11, 10), -1, R(9, 10), -4),
    (1, 2, 3): (-1, -R(11, 10), -1, -R(21, 10)),
    (0, 1, 2, 3): (-M-T-R(61, 10), -N-R(61, 10),
                    -R(1, 10), -R(31, 10)),
}


def zero(expr):
    assert s.cancel(expr) == 0, s.factor(expr)


def endpoints(q):
    pp, qq, hh = [], [], []
    for i in range(4):
        opp = [j for j in range(4) if j != i]
        p = z = 0
        for bits in product((0, 1), repeat=3):
            coal = tuple(j for j, bit in zip(opp, bits) if bit)
            mass = s.prod(q[j] if bit else 1-q[j]
                          for j, bit in zip(opp, bits))
            p += mass*(Z[coal][i] if coal else 0)
            z += mass*Z[tuple(sorted(coal+(i,)))][i]
        pp.append(s.expand(p))
        qq.append(s.expand(z))
        hh.append(s.prod(1-q[j] for j in opp))
    return pp, qq, hh


x = c*(4-3*r)-r/10
d = 2*r+b*(3*r-1)
m = 2*b+c/10-b*c
w0 = (-b+R(9, 10)*c-(M+1)*b*c)/((1-b)*(1-c))
X = (R(9, 10)*r+c)/((1-r)*(1-c))
D = (r+2*b)/((1-r)*(1-b))
P, Q, H = endpoints((r, 0, b, c))
for i, val in [(0, -m), (2, x), (3, -d)]:
    zero(Q[i]-val)
for i, val in [(0, w0), (2, X), (3, -D)]:
    zero(Q[i]-P[i]-H[i]*val)

fund = M*x*d-d-2*x-2*m
V = b-R(9, 10)*c+(M+1)*b*c
floor3 = 1-2*r-3*b+r*b
upper2 = 3-R(39, 10)*r-c*(4-3*r)
zero(V+w0*(1-b)*(1-c))
zero(floor3-(1-D)*(1-r)*(1-b))
zero(upper2-(3-X)*(1-r)*(1-c))

budget = ((9+R(9, 10)*r+2*c+9*r*c)
          *(1-R(19, 10)*c+(M+2)*b*c)-9*(1-c))
cap3 = (M*b*(180*c*r+120*c+90*r+180)
        + b*(180*c*r+40*c+360*r+560)
        - 252*c*r-208*c+9*r-62)
old_survival = (1-r)*(1-b)*(1-c)
zero(((9+11*X)*(1-w0)-9/old_survival)
     *(1-r)*(1-b)*(1-c)**2-budget)
g3 = D-R(10, 9)*X+2*w0+R(10, 3)*X*w0
zero(-g3*90*(1-r)*(1-b)*(1-c)**2-c*cap3)

# Reconstruct the tail02 row and its exact negative owner2 output.
aa, xx, vv = s.symbols('aa xx vv', nonnegative=True)
a02 = R(10, 9)*xx
q02 = (a02/(1+a02), 0, aa/(1+aa), 0)
P02, Q02, H02 = endpoints(q02)
zero(Q02[0]-P02[0]+aa*H02[0])
zero(Q02[2]-P02[2]-xx*H02[2])
zero(Q02[2]+xx/(9+10*xx))
zero(s.prod(1-q for q in q02)/(1+xx/(9+10*xx))
     -9/((9+11*xx)*(1+aa)))

# Exact cleared owner2 field for an arbitrary subsequent proper root.
a, t, p, z = s.symbols('a t p z', nonnegative=True)
PP, QQ, HH = endpoints((a/(1+a), t/(1+t), p/(1+p), z/(1+z)))
f2 = (R(9, 10)*a-t+z-R(1, 10)*a*t
      +R(19, 10)*a*z+R(9, 10)*a*t*z)
zero((QQ[2]-PP[2])/HH[2]-f2)
zero(f2+t*(1+a/10)-(R(9, 10)*a+z+R(19, 10)*a*z+R(9, 10)*a*t*z))
zero((1+a)*(1+t)-1-t*(1+a/10)-(a+R(9, 10)*a*t))

# Rational Bernstein proof on the closed box. Only funding is strict.
variables = (M, r, b, c)
bounds = ((0, 9), (R(1, 9), R(1, 2)), (0, R(1, 3)), (0, R(3, 4)))
necessary = (fund, V, floor3, upper2)
tau = s.symbols('tau:4')


def initial(poly):
    repl = {v: lo+(hi-lo)*u
            for v, (lo, hi), u in zip(variables, bounds, tau)}
    pp = s.Poly(s.expand(poly.subs(repl)), *tau)
    degree = pp.degree_list()
    out = []
    for index in product(*(range(n+1) for n in degree)):
        value = sum(coef*s.prod(R(comb(i, k), comb(n, k))
                               for i, k, n in zip(index, mon, degree))
                    for mon, coef in pp.terms()
                    if all(k <= i for k, i in zip(mon, index)))
        out.append(Fraction(int(s.numer(value)), int(s.denom(value))))
    return degree, tuple(out)


def split(poly, axis):
    degree, coeff = poly
    n = degree[axis]
    if n == 0:
        return poly, poly
    shape = [range(d+1) for d in degree]
    indices = list(product(*shape))
    lookup = {index: k for k, index in enumerate(indices)}
    left, right = list(coeff), list(coeff)
    others = [i for i in range(4) if i != axis]
    for vals in product(*(shape[i] for i in others)):
        base = dict(zip(others, vals))
        loc = [lookup[tuple(j if i == axis else base[i] for i in range(4))]
               for j in range(n+1)]
        line = [coeff[j] for j in loc]
        ll, rr = [line[0]], [line[-1]]
        for _ in range(n):
            line = [(v+w)/2 for v, w in zip(line, line[1:])]
            ll.append(line[0])
            rr.append(line[-1])
        for k, j in enumerate(loc):
            left[j], right[j] = ll[k], rr[n-k]
    return (degree, tuple(left)), (degree, tuple(right))


def choose_axis(polys):
    # This heuristic affects only proof size; all arithmetic remains rational.
    scores = []
    for axis in range(4):
        score = Fraction(0)
        for degree, coeff in polys[:3]:
            if degree[axis] == 0:
                continue
            indices = list(product(*(range(n+1) for n in degree)))
            table = dict(zip(indices, coeff))
            spread = max(abs(table[index]-table[tuple(
                0 if k == axis else index[k] for k in range(4))])
                         for index in indices)
            score += spread/(1+abs(max(coeff))+abs(min(coeff)))
        scores.append(score)
    return max(range(4), key=lambda j: scores[j])


def certify(target):
    stack = [([initial(p) for p in (target,)+necessary], 0)]
    count, depth_max = 0, 0
    leaves = [0]*5
    while stack:
        polys, depth = stack.pop()
        count += 1
        depth_max = max(depth_max, depth)
        assert count < 1000000 and depth < 80
        if min(polys[0][1]) > 0:
            leaves[0] += 1
            continue
        excluded = False
        for j in range(1, len(polys)):
            upper = max(polys[j][1])
            if upper < 0 or (j == 1 and upper == 0):
                leaves[j] += 1
                excluded = True
                break
        if excluded:
            continue
        axis = choose_axis(polys)
        halves = [split(poly, axis) for poly in polys]
        stack.append(([pair[1] for pair in halves], depth+1))
        stack.append(([pair[0] for pair in halves], depth+1))
    assert sum(leaves)*2-1 == count
    return count, depth_max, tuple(leaves)


for name, polynomial in [('survival_budget', budget), ('tail_owner3_cap', cap3)]:
    print('PASS', name, certify(polynomial))
print('PASS exact full-table identities and two-step owner2 survival bound')
```

## M. Middle-region negative-source classification

Use the native table of the theorem, and suppose
`0<=M<=43/5, 2<=N<=25/2, T>=0`. All parameters are finite. Let E be the
closed actual independent-law zero-full-debt carrier, and let X minimize
the ORIGINAL joint Never product nu on
`E_C={Y in E:min(U0(Y),U1(Y))<=0}`, where C={0,1}. Suppose nu(X)>0.
The actual-carrier construction and extraction proved earlier give these
facts, at X and at every genuine positive-Never conditional tail:

- Every payoff coordinate is at least-1, and coordinates2,3 are at most3.
- A negative-coordinate point admits a nonzero proper incoming Nash root
  q and a genuine zero-debt conditional tail W. Writing Q_i for the Quit
  endpoint, P_i for the nonempty opponent payoff and H_i for opponent
  survival, `U_i>=Q_i`, `q_i>0` implies `U_i=Q_i`, and
  `U_i=P_i+H_i W_i`. The last equality holds because Continue is supported.
- Prefixing any zero-debt carrier point by a full Nash root keeps it in E.
  A finite prefix multiplies its original Never product by its common
  survival. The tail W is not assumed to minimize anything.

We prove that X has no negative payoff coordinate. Assume the contrary.
AllContinue is not a Nash root at U(X), since a player with negative
continuation could Quit alone for zero. Finite normal-form Nash existence
therefore supplies a nonzero root. If either marked player is active, that
player's output is nonpositive: every marked participant reward in the
literal table is nonpositive. This would contradict the minimum after
prefixing X. Thus all such roots have q0=q1=0.

A singleton2 or singleton3 root maps a nonpositive marked input u_i to
`(1-q)u_i-q<0`, again a contradiction. Both unmarked owners must be active.
Their gaps are `q3-(1-q3)u2` and `-2q2-(1-q2)u3`. If q3=1 the first
forces q2=1, while q2=1 makes the second force q3=0; no sure boundary is
possible. Hence the root is the proper pair23, and its active equations
give

    U(X)=(u0,u1,x,-d), x,d>0,
    q2=d/(2+d), q3=x/(1+x),
    beta0=u0+Mxd/2-x-d/2>0,
    beta1=u1+Nxd/2-x-d/2>0.                      (S)

Both strict output signs follow from original minimum status. Also d<=1.
Extract a genuine incoming root `q=(r,t,p,z)` of X. It is proper and
nonzero. If r=t=0, its owner3 Quit endpoint is p>=0, contradicting U3<0.
We now exhaust every remaining support, without changing the source.

### M1. A paid123 improvement for every sufficiently negative output


For formula17, let a proper legal incoming root have support123 and inputs
w1,w3>=-1. Write its hazards a=q1,b=q2,c=q3 and its output
U=(z,-m,x,-d). Assume z>=-1,x>0,d>=1/10. Then there is a proper full123
Nash root at U with active owner1 odds greater than21/100. This new root
has owner0 input threshold less than-1, so its outside-owner0 cap is legal.
Its owner1 output is strictly negative.

The incoming active equations and floors give
c <= cmax=(1-b/10)/(2+Nb),
b <= (1-a/10)/(3-a),
m=b/10+2c-bc,
x=c(4-3a)-2a,
d=a/10+b(3a-1).
Since x>0 and cmax<=1/2, a<4/7. Thus b<2/5. Since d>=1/10,
a>=a0=(1/10+b)/(1/10+3b), implying b>3/50. The constraints x>0 and
c<=cmax additionally imply
a<(4-2b/5)/(7+(2N-3/10)b).
Comparison with a0 gives
200Nb^2+20Nb+90b^2-499b+30<0.
If N>=6 this polynomial is at least1290b^2-379b+30>0, whose leading
coefficient is positive and discriminant is-11159. Thus0<=N<6.

For the next123 root write odds A,B,C and put K=N+11/10. Its active
relations are B=(9A/10+d)/(2+11A/10), C=A+x, and
f(A)=9B/10-C-KBC=-m.
The hazard bounds give
`d<(4/7)(1/10+3b)-b<12/35`. Thus
B'(A)=(9/5-11d/10)/(2+11A/10)^2 is positive and at most9/20.
Consequently f'(A)<81/200-1<0, and f(A) tends to minus infinity.
Its lower endpoint A=0 has B=d/2,C=x. To prove existence and A>21/100, it suffices
to show f(21/100)>-m. Let A*=21/100, D=2+11A*/10,
bn=9A*/10+d, C*=A*+x. The desired expression times D is
S=(m-C*)D+9bn/10-K C* bn.
It is affine in incoming c. The allowed interval is
cmin=2a/(4-3a) <= c <= cmax.
At cmin multiply S by4-3a; at cmax multiply S by2+Nb. Substitute
a=a0+t(4/7-a0),0<=t<=1, then multiply each polynomial by
49(30b+1)^2. On b in[3/50,2/5],N in[0,6],t in[0,1], all tensor
Bernstein coefficients are positive. The lower-end polynomial has24
coefficients, minimum527584421/390625; the upper-end polynomial has45,
minimum49535031/500000. The complete exact coefficient calculation is included in Program1 below.

Hence A>A*. Also d<12/35 from the preceding hazard bounds, so
B(A) is increasing in A. The owner0 threshold is
F0=-4A-B+9C/10-5AB-31AC/10-(M+11/10)BC-(M+T+51/10)ABC.
At fixed x>=0,d>=1/10 it decreases as A increases, since C=A+x,
B increases, and the only positive linear C term combines with-4A to
-31A/10+9x/10. It decreases as d, M or T increases. Therefore its largest
possible value occurs at A=A*,d=1/10,M=T=0. There B=289/2231; its slope
in x is-719/22310<0. At x=0 its value is
-2481589/2231000<-1. Thus F0<-1<=z, proving the full owner0 cap.


### M2. Both marked incoming owners, with player2 active


**Proposition.** Under the source facts and(S), r,t,p>0 is impossible for
`0<=M<=9,N>=2,T>=0`. This includes every full-support incoming root. It
also excludes support012 directly, without a limiting-positive-hazard
assumption. No upper bound on N is used.

First, z=0 would give the paid owner2 output

    x=Q2=-r/10-(2-r)t<0.

Hence z>0, so all four owners are paid. Put h=5-p-z+pz. The actual tail
floors in the marked equations give

    0<=1-2p-z/10-h*t-M*p*z-T*t*p*z,
    0<=1-p/10-2z-h*r-N*p*z.                     (3)

These imply

    0<=p,z<=1/2,  0<=t<=9/40,
    0<=r<=(1-p/10)/(5-p)<=9/40.                (4)

For completeness, p<=1/2 and z<=1/2 follow directly from(3).
The t bound follows from
`9h-40(1-2p-z/10)=5(1-z)+p(71+9z)>=0`.
The difference between (1-p/10)/(5-p) and
(1-p/10-2z)/h has numerator z(9-9p/10-p^2/10)>=0.

The paid unmarked coordinates are

    x=z(4-3r-3t+3rt)+rt-r/10-2t,
    d=2r+t/10-rt-p(1-3r-3t+3rt).              (5)

At fixed hazards beta0 is affine in M. Its value at M=0 is negative,
because Q0<=0,x>0,d>0. Its coefficient of T is -ptz. It therefore suffices
to exclude positive beta0 at M=9,T=0. Denote that polynomial by B.

An exact tensor Bernstein conversion on the box(4) gives

    partial B/partial p <= -159/160 <0.         (6)

Program2 reconstructs the coefficient calculation from the complete reward table. Thus
`B(r,t,p,z)<=C(r,t,z):=B(r,t,0,z)`.
The x in(5) is independent of p. At p=0 the new d is
`d0=2r+t/10-rt`. If r<=1/9, then d0<=2/9: the bilinear expression has
maximum2/9 at the corners of [0,1/9] x [0,9/40]. Hence

    C=Q0|_(p=0)+(9d0/2-1)*x-d0/2<=0.

Here Q0|_(p=0)<=0,d0>=0,x>0. A positive B would therefore require
r>1/9. On the corresponding box, another exact Bernstein conversion gives

    partial C/partial t <= -137/144 <0.        (7)

It follows that

    B<=C<=C0:=z*A(r)-9r(r+1)/10,
    A(r)=-27r^2+39r-41/10.                    (8)

If A(r)<=0 this is already strictly negative. Suppose A(r)>0. Since N>=2,
the second inequality(3) implies

    0<=1-5r-z(2-r)+p*E,
    E=r-1/10-z(r+2).                           (9)

If E<=0, then r<=1/5 and z<=(1-5r)/(2-r). By(8),

    C0 <= [1359r^3-2229r^2+577r-41]/[10(2-r)]<0.       (10)

The strict polynomial sign holds on the entire interval[1/9,1/5]. In
order, its four tensor-free Bernstein coefficient lists on the intervals
[1/9,7/50], [7/50,3/20], [3/20,4/25], [4/25,1/5] are

    (-206/81,-2576/2025,-8354/16875,-22413/125000),
    (-22413/125000,-10501/150000,-959/60000,-127/8000),
    (-127/8000,-473/30000,-2609/37500,-2749/15625),
    (-2749/15625,-5638/9375,-3502/1875,-486/125).

If E>0, then z<(r-1/10)/(r+2). Substituting this bound in(8), and
multiplying by10(r+2), gives the numerator

    -279r^3+390r^2-98r+41/10.

Its Bernstein coefficients on[1/9,9/40] are

    (-1909/810,-10301/3240,-117407/43200,-88591/64000),

all strictly negative. Both cases contradict B>0. This proves the
proposition, including every relevant endpoint of the auxiliary boxes.


### M3. Both marked incoming owners, with player2 inactive

#### Weighted actual123 bound


Consider any actual positive-Never zero-debt source V with V2=X>0 and
V3=-D<-1/10. If its genuine incoming owner0 hazard vanishes, its support
is precisely123. Indeed owner3's negative Quit cap forces owner1 active;
D>1/10 forces owner2 active; positive V2 then forces owner3 active.
Write its hazards(alpha,p,c), and put V1=-B.

The actual incoming tail's coordinate1 is at least-1. Therefore

    c<=(1-p/10)/(2+N*p)<=(1-p/10)/(2+2p)=:cmax.

The paid equations give

    B=c(2-p)+p/10,
    X=c(4-3alpha)-2alpha>0,
    D=alpha(1/10+3p)-p.

For fixed p, both B and the upper bound on D increase with c; moreover
`alpha<4c/(2+3c)`. Hence

    B<=Bmax=(3p^2-10p+20)/(20(1+p)),
    D<Dmax=(-245p^2+248p+20)/(5(37p+70)).

The exact identity

    39/70-Dmax-Bmax/2
      =p(12943p^2+6724p+1404)/[280(1+p)(37p+70)]>=0

proves the strict necessary inequality

    B+2D<39/35.                                 (3)

No sign assumption on B was needed. This argument uses an actual
conditional-tail floor, not merely the prescribed payoff floor.

#### Actual incoming-owner0 barrier

Consider an actual positive-Never zero-debt source
`V=(-A,-B,X,-D)`, with D>1/10 and with owner0 active in a genuine incoming
root. Then A>=0, and

    B+2D<=1+20*A*D.                              (4)

The conclusion does not require a sign of B or X. If A>=1/10 it follows
immediately from B<=1 and D>0. Assume A<1/10, and write the incoming
hazards(r,t,p,z). The literal paid owner0 endpoint is

    A=-Q0=t+p+z/10+p(1-z)+pt(3-2z)+3tz+(M+T)ptz
      >=t+p+z/10.

Thus t,p<1/10. Since V3>=Q3 and D>1/10, one has -Q3>1/10. Its formula

    -Q3=2r+t/10-rt-p(1-3r-3t+3rt)

then forces r>1/25: for r<=1/25 the p coefficient in parentheses is
positive and the remaining upper bound is at most9/100.

The actual next tail's owner1 floor gives `V1>=P1-H1`. Since 2-20A>0,

    1+V1+(2-20A)V3
       >= L:=1+P1-H1+(2-20A)Q3.                (5)

This L is nonnegative. To see this directly from the table, let Lbase be
its polynomial at M=T=0,N=2. The exact identity is

    L=Lbase+(N-2)pz(1-r)-20(M+T)ptz*Q3.

The added terms are nonnegative, because Q3<0. All36 tensor Bernstein
coefficients of Lbase on

    r in[1/25,1], t,p in[0,1/10], z in[0,1]

are nonnegative; exactly four vanish. The full table, polynomial
reconstruction and rational coefficient conversion are included in Program3. This establishes (5)>=0, which is exactly(4).

Combining(3)--(4): for any actual positive-Never zero-debt source with
V2=X>0 and V3=-D<-1/10, write V1=-B and A=max(-V0,0). Then

    B+2D<=max(39/35,1+20*A*D).                  (6)

More precisely, failure of(3) forces incoming owner0 active, V0<=0 and
inequality(4). Every support alternative has been included.

#### The first outgoing02 test

Return to the incoming root q=(r,t,0,z) of the hypothetical marked minimum,
where r,t>0 and z>=0. Both marked owners are paid, so write
U=(-a,-b,x,-d), with a,b>0.
The paid marked endpoints and owner3 cap give

    a=t+z/10+3tz>0,
    b=r+2z+3rz>0,
    d<=d0:=2r+t/10-rt.                          (7)

The actual marked tail floors imply

    0<=1-z/10-(5-z)t,
    0<=1-2z-(5-z)r.

In particular r<=1/5,t<=9/40,z<=1/2 and d<=2/5. Also b<=1, by the
actual source floor. Since M<=43/5, beta0>0 in(S) gives

    (43d/10-1)x>a+d/2,
    d>10/43, x>(25a+5)/18>5/18.                (8)

The lower x bound uses that `(a+d/2)/(43d/10-1)` decreases with d and
that d<=2/5.

Consider the proper outgoing02 root at U with hazards

    q0=x/(x+9/10), q2=a/(1+a), q1=q3=0.

The two active equations hold exactly. Multiplying each inactive gap by
the positive denominator `(x+9/10)(1+a)` gives

    G1=-4x-(31/10)ax+(81/100)a+(9/10)b,
    G3=(9/10)d-x(1+3a)-(9/5)a.                 (9)

Using b<=1,x>5/18,a>=0 gives `G1<-19/90<0`. If G3<=0, this is a full
proper Nash root with negative owner0 output. Prefixing it to the marked
minimum strictly decreases its Never product and preserves a nonpositive
marked payoff, a contradiction.

Assume henceforth G3>0. Combining the preceding funding and outgoing-cap bounds yields

    F(a,d):=3a^2-4a/5+(231/25)ad+7d/5-(387/100)d^2<0.  (10)

Since d>10/43, the coefficient of a in this expression is positive.
Consequently d>140/387. Also a<21/1000. For the latter, F increases with
a, while F(21/1000,d) is concave in d on[10/43,2/5] and its endpoint
values are respectively6274889/43000000 and2939/1000000, both positive.
Thus

    d>140/387, 0<t<=a<21/1000, r>17/100.        (11)

The last inequality follows from d<=2r+t/10.

#### The actual continuation violates the barrier

The genuine continuation W has coordinates W0=-A,W1=-B,W2=X,W3=-D,
where the exact incoming identities give

    A=(4t-9z/10)/[(1-t)(1-z)],
    B=(4r+z)/[(1-r)(1-z)],
    D=(d-r-t+rt)/[(1-r)(1-t)].                 (12)

These formulas hold whether z vanishes or is positive. The incoming
owner2 cap gives

    X>=(9r/10-t+z)/H2>0,

using(11). Also
`d-r-t+rt>140/387-1/5-21/1000>1/10`, so D>1/10. Finally

    B+2D >= 2(d+r-t-rt)/[(1-r)(1-t)]
           >980188/803025>39/35.               (13)

The rational lower bound follows directly from(11), r<=1/5 and
`(1-r)(1-t)<83/100`.

The strict123 inequality(3) is therefore impossible for this actual W.
Its incoming owner0 is active, so A>=0 and the barrier(4) applies:

    B+(2-20A)D-1<=0.                            (14)

For fixed r,t,d, B in(12) increases with z, A decreases with z because
4t<9/10, and D is independent of z. Thus the left side of(14) is at
least its value at z=0. Clearing the positive denominator
`(1-r)(1-t)^2`, we obtain

    L0:=(5r-1)(1-t)^2
         +2(1-41t)(d-r-t+rt)<=0.               (15)

The coefficient of r in L0 is `(1-t)(3+77t)>0`. Set

    rmin=(d-t/10)/(2-t)<=r.

Replacing r by rmin preserves(15). At `d=(2-t)rmin+t/10`, that
inequality is equivalent to

    rmin<=rbar(t):=(5-t-364t^2)/[5(7-92t+5t^2)],
    d<=dbar(t):=(733t^3-1546t^2-7t+20)/[10(5t^2-92t+7)].    (16)

The denominators are positive on[0,21/1000]. One also has dbar<=2/5 there:
the numerator of2/5-dbar has strictly positive Bernstein coefficients

    (8,5473/1000,1588101/500000,1102817687/1000000000)

on that interval. On `d>=140/387,a<=21/1000`, F decreases in d and
increases in a. Hence(10),(16) and a>=t imply

    0>F(a,d)>=F(t,d)>=F(t,dbar(t)).             (17)

The final quantity is strictly positive. Its denominator is
`10000(5t^2-92t+7)^2`, and its numerator is

    -173316243t^6+159907892t^5+598454822t^4
    -13496588t^3+4123557t^2-1634640t+41200.

Its seven Bernstein coefficients on[0,21/1000] are

    41200,
    886969/25,
    149393762879/5000000,
    121968640661633/5000000000,
    47562990701638897/2500000000000,
    6891267342337699091/500000000000000,
    8683083043089138688597/1000000000000000000.

All are positive, contradicting(17). This proves the claimed exclusion of
every incoming01 and013 root, with neither a positive lower bound on z nor
an assumption that owner3 is paid when z=0.

Thus every incoming support containing both marked owners is excluded.


### M4. Exactly one marked incoming owner

If r=0,t>0, owner1 is paid and u1<=0. From beta1>0 in(S) we get
Nd>2. Since N<=25/2, this implies d>4/25>1/10. If p=0, the owner3
Quit endpoint is -t/10>=-1/10, contrary to U3=-d. Thus p>0. If z=0,
paid owner2 would have payoff -2t<0, contrary to x>0. Hence z>0 and
the incoming support is123. The paid123 improvement just proved applies
using the genuine tail floors. It gives a full proper root with negative
owner1 output, contradicting the original marked minimum. This argument
does not require u0<=0; it also covers the entire u0>0 alternative.

Now suppose r>0,t=0. If z=0,p>0, paid owner2 has Q2=-r/10<0,
impossible. If z=p=0 the root is sole0 and u0=W0=0. Increase r slightly
with its genuine tail held fixed. Owner0 stays indifferent and its output
stays zero. Owner2's inactive gap is -r/10-x<0. The other two gaps are
`-4r-(1-r)W1` and `-r-(1-r)W3`. At a binding gap
`kr-(1-r)W_i=0`, k=-4 or -1, its derivative is
`k+W_i=k/(1-r)<0`. Strict gaps remain strict under a sufficiently small
increase. Thus the perturbed root is full Nash and proper, preserves the
zero marked output, and has less survival than the incoming root. Prefixing
the SAME genuine tail contradicts the original minimum.

For p=0,z>0 the incoming support is03. Write its hazards r,c. Its paid
coordinates are u0=-a=-c/10, U3=-2r, and U2=x>0. Then beta0>0 gives

    M r x-r-x-a>0.                              (R)

Since M<=9, r>1/9. The genuine tail has

    W0=(9/10)c/(1-c)>0,
    W2=[x+r-3c(1-r)]/[(1-r)(1-c)]>0,
    W3=-r/(1-r)<-1/8.

The W2 numerator is at least c+9r/10 by the incoming owner2 cap.
Any genuine incoming root to this tail must have owner0 inactive because
W0>0 and all its participant rewards are nonpositive. W3<-1/10 forces
owner1 and owner2 active: without1 the owner3 cap is nonnegative; without2
it is at least-1/10. Positive paid owner2 then forces owner3 active.
It is therefore a proper123 root.

For any such123 root, write hazards alpha,b,c. The actual input1 floor
gives c<=(1-b/10)/(2+Nb)<=(1-b/10)/(2+2b). Positive paid2 gives
alpha<(40-4b)/(70+37b). Consequently

    -W3 < (40+496b-490b^2)/(700+370b) < 1/5.

The last inequality is equivalent to490b^2-422b+100>0, with positive
leading coefficient and discriminant-17916. Hence r<1/6. From(R),
x>r/(9r-1)>1/3. Choose the outgoing02 root at U with
q0=x/(x+9/10), q2=a/(1+a), and other hazards zero.
Both active equations hold. Its owner0 output is negative. Its inactive
owner1 gap, after multiplying by (x+9/10)(1+a), is
`-4x-(31/10)ax+(81/100)a-(9/10)u1<0`, because u1>=-1 and x>1/3.
If its owner3 cap failed, the other gap would imply x<(9/5)r. But(R)
would then give M>1/x+1/r+a/(rx)>14/(9r)>28/3>9, impossible.
Thus this full legal marked prefix also contradicts minimum status.

The only remaining case is r,p,z>0 and t=0, exactly incoming023.
The complete incoming023 theorem proved in its own section applies:
it requires precisely the genuine positive-Never tail, full paid/cap
identities, actual floors and ceiling, and beta0>0 already obtained here.
Its parameter range contains the present middle region. It either gives a
legal marked root at U or a two-row marked prefix of the SAME genuine tail
whose survival is less than the original incoming row. Both contradict
the original minimum. That section includes W0=0 and all sure-hazard
boundaries of its second root; no additional tail minimum is used.

These cases exhaust all fifteen nonempty incoming supports: neither
marked owner, both marked owners, only1, and only0. Positive Never already
excludes unit hazards for the incoming root; zero hazards have been handled
explicitly. Every hypothetical negative-coordinate marked minimum is
therefore impossible throughout the middle region.

### M5. Exact arithmetic programs for this classification

Each program below is complete and uses Python with SymPy. The polynomial
coefficient conversions are rational: a polynomial on a rectangle lies
between its least and greatest tensor Bernstein coefficients, since the
Bernstein basis is nonnegative and sums to one. No numerical sampling is
used to prove a universal sign.

#### Program1

```python
"""Exact inequalities for a paid123 output with U2>0 and U3<=-1/10.

This checks the scalar bridge to a next legal123 root, not a global selector.
No numerical root approximations or bounded orbit census are used.
Run from the repository root with Python and SymPy installed.
"""

from itertools import product
from math import comb

import sympy as s

R = s.Rational
a, b, c, N, t = s.symbols("a b c N t")
m = b / 10 + 2 * c - b * c
x = c * (4 - 3 * a) - 2 * a
d = a / 10 + b * (3 * a - 1)
cmin = 2 * a / (4 - 3 * a)
cmax = (1 - b / 10) / (2 + N * b)
a0 = (R(1, 10) + b) / (R(1, 10) + 3 * b)
amax = (4 - 2 * b / 5) / (7 + (2 * N - R(3, 10)) * b)

# Necessary geometry from the actual incoming active equations.
assert s.factor((amax - a0) * (30 * b + 1) * (20 * N * b - 3 * b + 70)) == (
    -200 * N * b**2 - 20 * N * b - 90 * b**2 + 499 * b - 30
)
assert 379**2 - 4 * 1290 * 30 == -11159
assert s.factor(a0.subs(b, R(3, 50)) - R(4, 7)) == 0
assert (1 - R(4, 7) / 10) / (3 - R(4, 7)) == R(33, 85) < R(2, 5)
assert R(4, 7) / 10 + R(2, 5) * (3 * R(4, 7) - 1) == R(12, 35)


def bernstein_coefficients(poly):
    """All exact tensor coefficients on b:[3/50,2/5],t:[0,1],N:[0,6]."""
    z, w = s.symbols("z w")
    p = s.Poly(s.expand(poly.subs({b: R(3, 50) + R(17, 50) * z, N: 6 * w})), z, t, w)
    degrees = [p.degree(variable) for variable in (z, t, w)]
    answer = []
    for orders in product(*[range(degree + 1) for degree in degrees]):
        value = 0
        for exponents, coefficient in p.terms():
            if all(exponent <= order for exponent, order in zip(exponents, orders)):
                value += coefficient * s.prod(
                    R(comb(order, exponent), comb(degree, exponent))
                    for exponent, order, degree in zip(exponents, orders, degrees)
                )
        answer.append(value)
    return answer


# At A*=21/100, S>0 is exactly f(A*)>-m. It is affine in incoming c.
astar = R(21, 100)
den = 2 + R(11, 10) * astar
bn = R(9, 10) * astar + d
cstar = astar + x
expression = s.factor((m - cstar) * den + R(9, 10) * bn - (N + R(11, 10)) * cstar * bn)
assert s.Poly(expression, c).degree() == 1
expected = [(24, R(527584421, 390625)), (45, R(49535031, 500000))]
for (endpoint, multiplier), (count, minimum) in zip(
    [(cmin, 4 - 3 * a), (cmax, 2 + N * b)], expected
):
    polynomial = s.factor(expression.subs(c, endpoint) * multiplier)
    polynomial = s.factor(
        polynomial.subs(a, a0 + t * (R(4, 7) - a0)) * 49 * (30 * b + 1) ** 2
    )
    coefficients = bernstein_coefficients(polynomial)
    assert len(coefficients) == count
    assert min(coefficients) == minimum > 0

# Literal inactive-owner0 threshold at its worst endpoint A*,d=1/10,M=0.
bs = (R(9, 10) * astar + R(1, 10)) / (2 + R(11, 10) * astar)
assert bs == R(289, 2231)
slope = R(9, 10) - R(31, 10) * astar - (R(11, 10) + R(51, 10) * astar) * bs
threshold = (
    -R(31, 10) * astar - bs - 5 * astar * bs - R(31, 10) * astar**2
    - R(11, 10) * bs * astar - R(51, 10) * astar**2 * bs
)
assert slope == -R(719, 22310) < 0
assert threshold == -R(2481589, 2231000) < -1

print('PASS: paid123 large-negative improvement and complete outside cap')
```

#### Program2

```python
from itertools import product
from math import comb
import sympy as s

R = s.Rational
r, t, p, z, M, N, T = s.symbols('r t p z M N T')
Z = {
    (0,): (0, 3, -1, -1), (1,): (3, 0, -1, -1),
    (2,): (-1, -1, 0, 3), (3,): (-1, -1, 3, 0),
    (0, 1): (-1, -1, -1, -1),
    (0, 2): (-2, -1, -R(1, 10), -1),
    (0, 3): (-R(1, 10), -1, -1, -2),
    (1, 2): (-1, -R(1, 10), -2, -1),
    (1, 3): (-1, -2, -1, -R(1, 10)),
    (2, 3): (M, N, 4, 1),
    (0, 1, 2): (-6, -R(41, 10), -R(11, 10), -1),
    (0, 1, 3): (-R(41, 10), -6, -1, -R(11, 10)),
    (0, 2, 3): (-R(11, 10), -1, R(9, 10), -4),
    (1, 2, 3): (-1, -R(11, 10), -1, -R(21, 10)),
    (0, 1, 2, 3): (-M-T-R(61, 10), -N-R(61, 10),
                    -R(1, 10), -R(31, 10)),
}


def zero(e):
    assert s.cancel(e) == 0, s.factor(e)


def endpoints(q):
    P, Q, H = [], [], []
    for i in range(4):
        opp = [j for j in range(4) if j != i]
        pp = qq = 0
        for bits in product((0, 1), repeat=3):
            A = tuple(j for j, bit in zip(opp, bits) if bit)
            mass = s.prod(q[j] if bit else 1-q[j]
                          for j, bit in zip(opp, bits))
            pp += mass * (Z[A][i] if A else 0)
            qq += mass * Z[tuple(sorted(A+(i,)))][i]
        P.append(s.expand(pp))
        Q.append(s.expand(qq))
        H.append(s.prod(1-q[j] for j in opp))
    return P, Q, H


def bernstein(poly, variables, bounds):
    tt = s.symbols('tau:'+str(len(variables)))
    repl = {v: lo+(hi-lo)*u for v, u, (lo, hi)
            in zip(variables, tt, bounds)}
    pp = s.Poly(s.expand(poly.subs(repl)), *tt)
    deg = pp.degree_list()
    out = []
    for idx in product(*(range(n+1) for n in deg)):
        out.append(sum(coef*s.prod(R(comb(i, k), comb(n, k))
                                  for i, k, n in zip(idx, mon, deg))
                       for mon, coef in pp.terms()
                       if all(k <= i for i, k in zip(idx, mon))))
    return out


P, Q, H = endpoints((r, t, p, z))
h = 5-p-z+p*z
zero(Q[0]-P[0]+H[0]-(1-2*p-z/10-h*t-M*p*z-T*t*p*z))
zero(Q[1]-P[1]+H[1]-(1-p/10-2*z-h*r-N*p*z))
zero(Q[2].subs(z, 0)-(-r/10-(2-r)*t))
zero(Q[2]-(z*(4-3*r-3*t+3*r*t)+r*t-r/10-2*t))
zero(-Q[3]-(2*r+t/10-r*t-p*(1-3*r-3*t+3*r*t)))
x, d = Q[2], -Q[3]
beta = s.expand(Q[0]+M*x*d/2-x-d/2)
assert s.Poly(beta, M).degree() == 1
zero(s.diff(beta, T)+p*t*z)
beta9 = s.factor(beta.subs({M: 9, T: 0}))
dp = bernstein(s.diff(beta9, p), (r, t, z),
               ((0, R(9, 40)), (0, R(9, 40)), (0, R(1, 2))))
assert max(dp) == -R(159, 160)
C = s.factor(beta9.subs(p, 0))
dt = bernstein(s.diff(C, t), (r, t, z),
               ((R(1, 9), R(9, 40)), (0, R(9, 40)), (0, R(1, 2))))
assert max(dt) == -R(137, 144)
C00 = z*(-27*r*r+39*r-R(41, 10))-R(9, 10)*r*(r+1)
zero(C.subs(t, 0)-C00)
E = r-R(1, 10)-z*(r+2)
zero((Q[1]-P[1]+H[1]).subs(N, 2)
     -(1-5*r-z*(2-r)+p*E))
cubic = 1359*r**3-2229*r*r+577*r-41
zero(C00.subs(z, (1-5*r)/(2-r))-cubic/(10*(2-r)))
expected = [
    [-R(206, 81), -R(2576, 2025), -R(8354, 16875), -R(22413, 125000)],
    [-R(22413, 125000), -R(10501, 150000), -R(959, 60000), -R(127, 8000)],
    [-R(127, 8000), -R(473, 30000), -R(2609, 37500), -R(2749, 15625)],
    [-R(2749, 15625), -R(5638, 9375), -R(3502, 1875), -R(486, 125)],
]
intervals = [(R(1, 9), R(7, 50)), (R(7, 50), R(3, 20)),
             (R(3, 20), R(4, 25)), (R(4, 25), R(1, 5))]
for bounds, target in zip(intervals, expected):
    bc = bernstein(cubic, (r,), (bounds,))
    assert bc == target and max(bc) < 0
numer = -279*r**3+390*r*r-98*r+R(41, 10)
zero(10*(r+2)*C00.subs(z, (r-R(1, 10))/(r+2))-numer)
bc = bernstein(numer, (r,), ((R(1, 9), R(9, 40)),))
assert bc == [-R(1909, 810), -R(10301, 3240),
              -R(117407, 43200), -R(88591, 64000)]
assert max(bc) < 0

print('PASS: complete active-player2 both-anchor exclusion')
```

#### Program3

```python
from itertools import product
from math import comb
import sympy as s

R = s.Rational
r, t, p, z, M, N, T = s.symbols('r t p z M N T')
Z = {
    (0,): (0, 3, -1, -1), (1,): (3, 0, -1, -1),
    (2,): (-1, -1, 0, 3), (3,): (-1, -1, 3, 0),
    (0, 1): (-1, -1, -1, -1),
    (0, 2): (-2, -1, -R(1, 10), -1),
    (0, 3): (-R(1, 10), -1, -1, -2),
    (1, 2): (-1, -R(1, 10), -2, -1),
    (1, 3): (-1, -2, -1, -R(1, 10)),
    (2, 3): (M, N, 4, 1),
    (0, 1, 2): (-6, -R(41, 10), -R(11, 10), -1),
    (0, 1, 3): (-R(41, 10), -6, -1, -R(11, 10)),
    (0, 2, 3): (-R(11, 10), -1, R(9, 10), -4),
    (1, 2, 3): (-1, -R(11, 10), -1, -R(21, 10)),
    (0, 1, 2, 3): (-M-T-R(61, 10), -N-R(61, 10),
                    -R(1, 10), -R(31, 10)),
}


def zero(e):
    assert s.cancel(e) == 0, s.factor(e)


def endpoints(q):
    P, Q, H = [], [], []
    for i in range(4):
        opp = [j for j in range(4) if j != i]
        pp = qq = 0
        for bits in product((0, 1), repeat=3):
            A = tuple(j for j, bit in zip(opp, bits) if bit)
            mass = s.prod(q[j] if bit else 1-q[j]
                          for j, bit in zip(opp, bits))
            pp += mass * (Z[A][i] if A else 0)
            qq += mass * Z[tuple(sorted(A+(i,)))][i]
        P.append(s.expand(pp))
        Q.append(s.expand(qq))
        H.append(s.prod(1-q[j] for j in opp))
    return P, Q, H


def bernstein(poly, variables, bounds):
    tt = s.symbols('tau:'+str(len(variables)))
    repl = {v: lo+(hi-lo)*u for v, u, (lo, hi)
            in zip(variables, tt, bounds)}
    pp = s.Poly(s.expand(poly.subs(repl)), *tt)
    deg = pp.degree_list()
    out = []
    for idx in product(*(range(n+1) for n in deg)):
        out.append(sum(coef*s.prod(R(comb(i, k), comb(n, k))
                                  for i, k, n in zip(idx, mon, deg))
                       for mon, coef in pp.terms()
                       if all(k <= i for i, k in zip(idx, mon))))
    return out


P, Q, H = endpoints((r, t, p, z))
aa, dd, xx, bb = s.symbols('aa dd xx bb')

# Sharp weighted actual123 bound, using the real input1 floor.
cmax = (1-bb/10)/(2+2*bb)
mmax = s.factor(cmax*(2-bb)+bb/10)
dmax = s.factor(4*cmax/(2+3*cmax)*(R(1, 10)+3*bb)-bb)
zero(mmax-(3*bb**2-10*bb+20)/(20*(1+bb)))
zero(dmax-(-245*bb**2+248*bb+20)/(5*(37*bb+70)))
zero(R(39, 70)-dmax-mmax/2
     -bb*(12943*bb**2+6724*bb+1404)/(280*(1+bb)*(37*bb+70)))

# Actual owner0-paid barrier m+2d <= 1+20ad when d>1/10.
a0 = -Q[0]
zero(a0-(t+p+z/10+p*(1-z)+p*t*(3-2*z)+3*t*z+(M+T)*p*t*z))
L = s.expand(1+P[1]-H[1]+(2-20*a0)*Q[3])
Lbase = s.expand(L.subs({M: 0, N: 2, T: 0}))
zero(L-Lbase-(N-2)*p*z*(1-r)+20*(M+T)*p*t*z*Q[3])
barrier_bc = bernstein(Lbase, (r, t, p, z),
                       ((R(1, 25), 1), (0, R(1, 10)),
                        (0, R(1, 10)), (0, 1)))
assert len(barrier_bc) == 36 and min(barrier_bc) == 0
assert sum(c == 0 for c in barrier_bc) == 4
assert all(c >= 0 for c in barrier_bc)
# If a<1/10 and r<=1/25, -Q3<=9/100<1/10.
assert 1-3*R(1, 25)-3*R(1, 10) > 0
assert 2*R(1, 25)+R(1, 100) < R(1, 10)

# Outer both-anchor p=0 source, including z=0 and its unpaid owner3.
Pi, Qi, Hi = [[s.factor(e.subs(p, 0)) for e in vec] for vec in (P, Q, H)]
a = t+z/10+3*t*z
b = r+2*z+3*r*z
d0 = 2*r+t/10-r*t
zero(Qi[0]+a); zero(Qi[1]+b); zero(Qi[3]+d0)
zero(Qi[0]-Pi[0]+Hi[0]-(1-z/10-(5-z)*t))
zero(Qi[1]-Pi[1]+Hi[1]-(1-2*z-(5-z)*r))
A = (4*t-R(9, 10)*z)/((1-t)*(1-z))
B = (4*r+z)/((1-r)*(1-z))
D = (dd-r-t+r*t)/((1-r)*(1-t))
X = (xx-Pi[2])/Hi[2]
zero((Qi[0]-Pi[0])/Hi[0]+A)
zero((Qi[1]-Pi[1])/Hi[1]+B)
zero((-dd-Pi[3])/Hi[3]+D)
zero(Qi[2]-Pi[2]-(R(9, 10)*r-t+z))

# The outgoing02 root and both inactive caps are derived from the table.
Pout, Qout, Hout = endpoints((xx/(xx+R(9, 10)), 0, aa/(1+aa), 0))
u = [-aa, -bb, xx, -dd]
gaps = [s.cancel(Qout[i]-Pout[i]-Hout[i]*u[i]) for i in range(4)]
zero(gaps[0]); zero(gaps[2])
g1 = -4*xx-R(31, 10)*aa*xx+R(81, 100)*aa+R(9, 10)*bb
g3 = R(9, 10)*dd-xx*(1+3*aa)-R(9, 5)*aa
zero(gaps[1]*(xx+R(9, 10))*(1+aa)-g1)
zero(gaps[3]*(xx+R(9, 10))*(1+aa)-g3)
assert R(9, 10)-4*R(5, 18) == -R(19, 90)
assert R(81, 100)-R(31, 10)*R(5, 18) < 0

# Contradiction region forced by failure of the owner3 cap.
F = 3*aa**2-R(4, 5)*aa+R(231, 25)*aa*dd+R(7, 5)*dd-R(387, 100)*dd**2
zero(F-((aa+dd/2)*(1+3*aa)
        -(R(43, 10)*dd-1)*(R(9, 10)*dd-R(9, 5)*aa)))
assert F.subs({aa: R(21, 1000), dd: R(2, 5)}) == R(2939, 1000000)
assert F.subs({aa: R(21, 1000), dd: R(10, 43)}) == R(6274889, 43000000)
assert R(231, 25)*R(10, 43)-R(4, 5) > 0
assert R(231, 25)*R(21, 1000)+R(7, 5)-R(387, 50)*R(140, 387) < 0
assert 2*R(17, 100)+R(21, 10000) < R(140, 387)
assert R(9, 10)*R(17, 100)-R(21, 1000) > 0
assert R(140, 387)-R(1, 5)-R(21, 1000) > R(1, 10)
coarse = 2*(R(140, 387)+R(17, 100)-R(21, 1000)
            -R(1, 5)*R(21, 1000))/R(83, 100)
assert coarse == R(980188, 803025) > R(39, 35)
zero(s.diff(A, z)-(4*t-R(9, 10))/((1-t)*(1-z)**2))
zero(s.diff(B, z)-(1+4*r)/((1-r)*(1-z)**2))

# The final barrier reduction to one variable.
Lnum = (5*r-1)*(1-t)**2+2*(1-41*t)*(dd-r-t+r*t)
zero((B+(2-20*A)*D-1).subs(z, 0)*(1-r)*(1-t)**2-Lnum)
zero(s.diff(Lnum, r)-(1-t)*(3+77*t))
rb = (5-t-364*t**2)/(5*(7-92*t+5*t**2))
db = (733*t**3-1546*t**2-7*t+20)/(10*(5*t**2-92*t+7))
zero(Lnum.subs(dd, d0)-(7-92*t+5*t**2)*(r-rb))
zero(db-(2-t)*rb-t/10)
db_numer = -733*t**3+1566*t**2-361*t+8
zero(R(2, 5)-db-db_numer/(10*(5*t**2-92*t+7)))
assert bernstein(db_numer, (t,), ((0, R(21, 1000)),)) == [
    8, R(5473, 1000), R(1588101, 500000), R(1102817687, 1000000000)]
fnum = (-173316243*t**6+159907892*t**5+598454822*t**4
        -13496588*t**3+4123557*t**2-1634640*t+41200)
zero(F.subs({aa: t, dd: db})-fnum/(10000*(5*t**2-92*t+7)**2))
final_bc = bernstein(fnum, (t,), ((0, R(21, 1000)),))
assert final_bc == [41200, R(886969, 25), R(149393762879, 5000000),
                    R(121968640661633, 5000000000),
                    R(47562990701638897, 2500000000000),
                    R(6891267342337699091, 500000000000000),
                    R(8683083043089138688597, 1000000000000000000)]
assert min(final_bc) > 0
print('PASS: actual-tail barrier and complete inactive-player2 both-anchor exclusion')
```

#### Program4

```python
from fractions import Fraction as F
import sympy as s
b,r,c,x,a,u1=s.symbols('b r c x a u1')
cmax=(1-b/10)/(2+2*b)
alpha=4*cmax/(2+3*cmax)
dmax=s.factor(alpha*(F(1,10)+3*b)-b)
assert s.cancel(dmax-(40+496*b-490*b*b)/(700+370*b))==0
assert 422**2-4*490*100==-17916
assert F(9,10)-4*F(1,3)<0
assert F(81,100)-F(31,10)*F(1,3)<0
assert F(28,3)>9
assert F(2,1)/F(25,2)==F(4,25)>F(1,10)
assert s.cancel(c*(4-3*r)-r/10+r-3*c*(1-r)-(c+F(9,10)*r))==0
assert s.cancel(F(9,10)*r-(x+r)-(-r/10-x))==0
print('PASS: incoming03 paid123 bound and sole-marked1 threshold')
```

## P. Exact quantitative producers for the complementary regions

### P1. Complete reward table and exact conclusions

Let the players be I={0,1,2,3}. At each live date they independently choose
Continue or Quit. The first nonempty coalition A of quitters selects an
absorbing state with reward Z(A). The selecting live date pays zero; every
subsequent absorbed date pays Z(A). If nobody ever quits, every payoff is zero.
All parameters M,N,T are finite nonnegative real numbers. The complete native
reward table, with coordinates ordered by recipient0,1,2,3, is

| A | Z0(A) | Z1(A) | Z2(A) | Z3(A) |
|---|---:|---:|---:|---:|
| 0 | 0 | 3 | -1 | -1 |
| 1 | 3 | 0 | -1 | -1 |
| 2 | -1 | -1 | 0 | 3 |
| 3 | -1 | -1 | 3 | 0 |
| 01 | -1 | -1 | -1 | -1 |
| 02 | -2 | -1 | -1/10 | -1 |
| 03 | -1/10 | -1 | -1 | -2 |
| 12 | -1 | -1/10 | -2 | -1 |
| 13 | -1 | -2 | -1 | -1/10 |
| 23 | M | N | 4 | 1 |
| 012 | -6 | -41/10 | -11/10 | -1 |
| 013 | -41/10 | -6 | -1 | -11/10 |
| 023 | -11/10 | -1 | 9/10 | -4 |
| 123 | -1 | -11/10 | -1 | -21/10 |
| 0123 | -M-T-61/10 | -N-61/10 | -1/10 | -31/10 |

The equivalent formula used by the symbolic checks is as follows. Set

    Gamma=[0,3,-1,-1; 3,0,-1,-1; -1,-1,0,3; -1,-1,3,0],
    L=[0,-4,-1,9/10; -4,0,9/10,-1;
       9/10,-1,0,1; -1,9/10,-2,0].

For B subset I minus{i}, put F_i(empty)=0, F_i({j})=Gamma_ij, and
F_i(B)=-1 for |B|>=2, except F_0({2,3})=M and F_1({2,3})=N. Then

    Z_i(A)=F_i(A minus{i})+1_(i in A)*[
      sum_(j in A minus{i}) L_ij
      -(M+1)1_(i=0 and {2,3} subset A minus{i})
      -(N+1)1_(i=1 and {2,3} subset A minus{i})]
      -T*1_(i=0 and A=I).

Define

    K*=(71-sqrt65+2sqrt809)/14.

The following three conclusions will be proved with no assumed strategic
witness, selected root, or continuation value:

1. If M>=K*, every N,T>=0 admits an absorbing exact period-two terminal Nash
   profile.
2. If 4<=M<=9 and 0<=N<=2, every T>=0 admits an absorbing exact period-four
   terminal Nash profile.
3. If N>=25/2, every M,T>=0 admits an absorbing exact stationary terminal Nash
   profile with player0 Never.

Terminal Nash here caps every replacement of one player's entire behavioral
strategy, including Never. Each construction has geometric absorption even
after any such replacement. Consequently each remains an exact terminal Nash
profile after any transformation

    r_i(A)=lambda_i Z_i(A)+s_i,  lambda_i>0, s_i arbitrary real,

and has one fixed uniform-equilibrium payoff. In particular it supplies the
native absorbing debt infimum A_Z=0: the infimum, over almost-surely
absorbing profiles, of their total full terminal debt is zero. These conclusions are
stronger than native nonabsorbing equilibrium by AllNever.

The signed-offset assertion in this note uses the opponent absorption proved
for these three constructions. It does not assert signed-offset invariance for
any other approximate absorbing construction used elsewhere in a family proof.

### P2. Complete periodic behavioral and fixed-target consumer

This section supplies the full semantic argument shared by the three
constructions. Fix a period length ell>=1. At phase k, player i quits with
probability q_i^k, independently of the other players, and the next live phase
is k+1 modulo ell. Define opponent survival and the two literal action endpoints
against a supplied next-phase value V^{k+1} by

    H_i^k = product_(j!=i)(1-q_j^k),
    Q_i^k = sum_(B subset I minus{i}) p_i^k(B) Z_i(B union{i}),
    C_i^k = sum_(nonempty B subset I minus{i}) p_i^k(B) Z_i(B)
             + H_i^k V_i^{k+1},

where p_i^k(B)=product_(j in B)q_j^k product_(j notin B,j!=i)(1-q_j^k).
The terminal payoff convention assigns the absorbed reward immediately when
computing these endpoints; the actual stage-payoff timing is handled below.

Suppose finite phase values V satisfy the policy equations

    V_i^k=q_i^k Q_i^k+(1-q_i^k)C_i^k,

both action bounds Q_i^k<=V_i^k and C_i^k<=V_i^k, and, for each player i,

    rho_i=product_(k=0,...,ell-1) H_i^k < 1.             (C1)

For a proper active probability 0<q_i^k<1, it suffices to prove the policy
equation and Q_i^k=V_i^k: then C_i^k=V_i^k follows by division by 1-q_i^k.
For an inactive player q_i^k=0, the policy equation gives C_i^k=V_i^k, and
the remaining obligation is the literal Quit cap.

For any unilateral behavioral replacement, condition on each finite live
history. Whatever that player's conditional mixed action is, its one-step
reward plus surviving continuation is at most V_i^k, because this is a convex
combination of the two action bounds. Iterating gives the same bound after
any finite number of dates, with the surviving remainder V at the next phase.
The probability of survival through n dates is at most

    rho_i^floor(n/ell).

Indeed a whole cycle contains all prescribed opponent phases once; the
deviator can only decrease survival relative to those opponent clocks. This
argument also covers a deviator using private randomization, arbitrary history
dependence, and Never. All live action histories of the opponents before
absorption consist of Continue, so their stipulated phase probabilities are
unchanged by the replacement.

The bounded remainder tends to zero by (C1). Hence the expected terminal
reward of every replacement is at most V_i^0. Under the prescribed profile,
each step uses the policy equality; the same limit gives terminal payoff
exactly V^0. This proves exact terminal Nash and also almost-sure absorption
under every replacement.

For clarity, this supplies a direct uniform finite-horizon bound. Set
rho=max_i rho_i<1. Let tau>=1 be the date of the first nonempty quitting
coalition, with initial live date numbered1. For every unilateral replacement,

    E[tau]=sum_(n>=0) Pr(tau>n) <= ell/(1-rho).         (C2)

The same bound holds for prescribed play. For a fixed reward table r, let
B=max_(i,A)|r_i(A)|. Its H-date average reward, on a path absorbed at tau,
is (H-tau)_+ r_i(A)/H. Thus its expected distance from terminal reward is at
most

    B E[tau]/H <= B ell/((1-rho)H),                   (C3)

uniformly over every unilateral replacement. In particular, the prescribed
H-date payoff tends to V^0, and every deviating H-date payoff exceeds the
prescribed payoff by at most 2B ell/((1-rho)H). Given epsilon>0, all integers
H>=max(1,ceil(2B ell/((1-rho)epsilon))) satisfy the fixed-target uniform
equilibrium requirements. The target V^0 and the profile are chosen before
epsilon, and the same profile works for every sufficiently long H.

Every prescribed and deviating terminal law absorbs. Therefore replacing Z_i
by lambda_i Z_i+s_i changes every terminal expectation to lambda_i times the
old expectation plus s_i. Exact terminal comparisons are preserved for every
real s_i and lambda_i>0. The absorption bound is unchanged, while (C3) uses
the finite bound for the transformed table. The fixed target becomes
lambda_i V_i^0+s_i, coordinatewise.

### P3. Period two for every M>=K*

#### P3.1. A complete branch producer and exact funding threshold

Write y for player3's odds and z for player2's odds in a joint phase, and let
u be player0's solo hazard. Require

    y^2+(5u-3)y+u=0,
    -2z^2+(2u-3)z+u=0.                               (P2.1)

For 0<u<=9/25, define

    y_-(u)=(3-5u-sqrt((1-u)(9-25u)))/2,
    z(u)=(sqrt((3-2u)^2+8u)-(3-2u))/4.

Both are strictly positive: the y polynomial has positive product u and
positive root sum 3-5u, and the z polynomial has exactly one positive root.
On 7/20<=u<=9/25 also use

    y_+(u)=(3-5u+sqrt((1-u)(9-25u)))/2.

The two y branches meet at u=9/25, where y=3/5. Travel continuously from
u=7/20 along the larger branch to this meeting point and then along the smaller
branch toward u=0. On this connected curve set

    K(u,y)=1/y+1/z(u).

It is continuous, and K tends to infinity at the open u=0 end because z(u)
tends to zero. At the starting endpoint

    y_+=(25+sqrt65)/40, z=(sqrt809-23)/40,
    K(7/20,y_+)=K*.

Thus every finite M>=K* is attained somewhere on this curve: for M>K*,
choose a sufficiently small positive endpoint with K>M and apply the
intermediate value theorem on the intervening compact path; equality uses
the starting point. No monotonicity of K or global minimum claim is needed.

Every attained point has 0<u<=9/25 and 0<z<u/2. For the latter assertion,
the z polynomial is positive at zero, equals u(u-1)/2<0 at z=u/2, and has
exactly one positive root. On the smaller branch, evaluating the y polynomial
at 5u/3 gives 4u(25u-9)/9<=0, so y_-<=5u/3. On the larger branch before
the meeting point,

    y_+'(u)=-(5y_++1)/sqrt((1-u)(9-25u))<0.

Continuity at the meeting point then gives

    y_+<=y_+(7/20)<7/8=(5/2)(7/20)<=(5/2)u.

Consequently 3u-y-z>0 on both branches: on the smaller branch use
y+z<(5/3+1/2)u<3u, and on the larger branch use z<u/2 and y<(5/2)u.
For any N>=0 the numbers

    B=(3u-y-z+Nyz)/(u+y+z+yz),
    A=3u+(1-u)B                                      (P2.2)

are therefore strictly positive. All divisions above have positive
denominators.

#### P3.2. Every cyclic equation and every outside cap

Use the chronological repeating schedule

    phase A: (q0,q1,q2,q3)=(u,0,0,0),
    phase B: (q0,q1,q2,q3)=(0,0,z/(1+z),y/(1+y)).

Player1 is Never. The candidate phase values are

    V^A=(0,A,y,-2z),
    V^B=(0,B,4y/(1+y),z/(1+z)).                       (P2.3)

At phase A the Continue endpoints equal V^A. For player0 this is zero;
for player1 it is 3u+(1-u)B=A. The remaining equalities

    -u+(1-u)4y/(1+y)=y,
    -u+(1-u)z/(1+z)=-2z

are exactly (P2.1). The Quit endpoint vector is

    Q^A=(0,-u,-u/10,-2u).

Thus player0 is indifferent, players1 and2 have strictly positive values
above their negative Quit endpoints, and player3 has
-2z>-u>-2u. All four caps at phase A hold.

At phase B, the Continue endpoint of player0 is

    (-z-y+Myz)/((1+y)(1+z))=0,

because M=1/y+1/z. Player1's Continue endpoint equals B: after multiplying
by (1+y)(1+z) this is precisely

    B(1+y)(1+z)=-z-y+Nyz+A,

which follows from (P2.2). For player2 the Continue endpoint is
4y/(1+y), since its continuation value from phase A is y; its Quit endpoint
is the same value. For player3 the Continue and Quit endpoints both equal
z/(1+z), since its continuation value from phase A is -2z. The other two
Quit endpoints are

    Q^B_0=-(20z+y+11yz)/(10(1+y)(1+z))<0,
    Q^B_1=-(z+20y+11yz)/(10(1+y)(1+z))<0.

They are strictly below the values0 and B>0. This checks every action of
every player in both phases and verifies the policy equations as well.

All three active hazards are proper. Writing q2=z/(1+z),q3=y/(1+y), the
four deleted-opponent cycle survivals, for deleted players0,1,2,3, are

    (1-q2)(1-q3), (1-u)(1-q2)(1-q3),
    (1-u)(1-q3), (1-u)(1-q2),

respectively. Every one is strictly below1. Section P2 therefore proves the
complete behavioral terminal equilibrium, arbitrary signed row-offset and
positive-scale invariance, and the fixed uniform payoff with initial target
V^A. No on-path coalition has more than two players; a unilateral replacement
can add at most one player. Hence the grand coalition is unreachable even
under a replacement, and T has no effect on this construction.

### P4. Period four on 4<=M<=9, 0<=N<=2

#### P4.1. A unique cubic root and proper hazards

Set t=1/(M+2), so 1/11<=t<=1/6. Let z be the unique root in
(2/5,11/20) of

    G(N,t,z)=4(N-7)z^3+[41-3N+8(N-7)t]z^2
               +[-13+(77-5N)t]z-21t=0.              (P4.1)

This root exists throughout the closed parameter rectangle. At z=2/5 and
z=11/20 the signs are negative and positive, respectively. Since each
endpoint expression is separately affine in N and t, the four exact corner
signs suffice. The complete tensor Bernstein coefficients of G_z after
rescaling N,t,z to their unit intervals are all at least809/100, as checked
by the exact program in Section P6. Therefore G_z>0 throughout the box, and
the intermediate value theorem gives existence and uniqueness.

Define

    p=[Nz(4z-3)-28z^2+45z-12]/[21-16z+4Nz],
    alpha=2p/(1-p), beta=p/(1+p), c=(4z-p)/(1+p),
    gamma=[(z/(1-z)+alpha)/(1-alpha)-c]/(3-c),
    P0=-p-z+pz/t, P1=-p-z+(N+2)pz, h=(1-p)(1-z).   (P4.2)

The exact finite interval certificate in Section P6 establishes, over the
entire rectangle and its unique roots, that every displayed denominator is
nonzero and that

    p>0, 1-3p>0, z>0, 1-z>0, gamma>0, 1-gamma>0,
    c>0,
    4alpha-(1-alpha)gamma>0,
    c(1-gamma)-gamma>0,
    pz-t(-p+(9/10)z+pz)>0.                         (P4.3)

In particular 0<p<1/3 implies 0<alpha<1 and 0<beta<1. Thus every
scheduled hazard is proper. The certificate is a finite exact continuum
cover, not a grid or floating-point search. Its details are given below.

#### P4.2. Literal cyclic equations and all sixteen action caps

The chronological period and candidate values are

    A: solo0(alpha),       U_A=(0,3alpha-(1-alpha)gamma,z/(1-z),-alpha),
    B: solo3(gamma),       U_B=(0,-gamma,3gamma+(1-gamma)c,0),
    C: solo1(beta),        U_C=(gamma/(1-gamma),0,c,0),
    D: joint23(p,z),       U_D=(P0,0,4z,p).          (P4.4)

In a solo phase all other hazards are zero; in the joint phase only players2
and3 have the indicated independent Quit probabilities. Unlike Section P3,
p and z here are probabilities, not odds.

The unconditional stopping-reward vectors and full-profile survival factors
computed directly from the complete table are

    E_A=(0,3alpha,-alpha,-alpha),       S_A=1-alpha,
    E_B=(-gamma,-gamma,3gamma,0),       S_B=1-gamma,
    E_C=(3beta,0,-beta,-beta),          S_C=1-beta,
    E_D=(P0,P1,3z+pz,3p-2pz),         S_D=(1-p)(1-z).

All sixteen policy equations are U_k=E_k+S_k U_(k+1). The two remaining
funding identities, after substituting (P4.2), are

    P1+h[3alpha-(1-alpha)gamma]=0,
    P0=[gamma(1+4p)-3p]/(1-gamma).                   (P4.5)

Their numerators have zero polynomial remainder on division by G in the
variable z. The definition of gamma is precisely player2's cyclic equation;
player3's equations reduce to alpha=2p/(1-p), beta=p/(1+p). The exact program
independently verifies all sixteen recursions modulo G, as well as all five
active Quit equalities.

The literal Quit endpoint vectors are

    Q_A=(0,-alpha,-alpha/10,-2alpha),
    Q_B=(-gamma/10,-2gamma,4gamma,0),
    Q_C=(-beta,0,-2beta,-beta/10),
    Q_D=(-2p-z/10+pz,-p/10-2z+pz,4z,p).             (P4.6)

The complete inactive Quit gaps U_ki-Q_ki are as follows:

| phase | inactive player | gap |
|---|---:|---|
| A | 1 | 4alpha-(1-alpha)gamma |
| A | 2 | z/(1-z)+alpha/10 |
| A | 3 | alpha |
| B | 0 | gamma/10 |
| B | 1 | gamma |
| B | 2 | c(1-gamma)-gamma |
| C | 0 | gamma/(1-gamma)+beta |
| C | 2 | c+2beta |
| C | 3 | beta/10 |
| D | 0 | [pz-t(-p+(9/10)z+pz)]/t |
| D | 1 | p/10+z(2-p) |

Every entry is strictly positive by (P4.3). The five active Quit gaps are
zero. The policy equations and properness then supply the Continue bounds
by Section P2. Thus all action comparisons, including those for the negative
player3 value in phase A, are accounted for.

#### P4.3. Why the finite exact certificate covers the continuum

The checker uses rational interval addition, subtraction, multiplication and
division, with division permitted only when its denominator interval excludes
zero. These operations contain every value of the corresponding operation
on their input intervals. The tensor Bernstein basis on a unit box consists
of nonnegative functions summing to1. Therefore the computed minimum
coefficient809/100 is a valid lower bound for G_z on the whole original box.

For a parameter subrectangle in N,t, the program computes the four corner
roots using24 exact rational bisections of [2/5,11/20]. Let L be the smallest
lower bracket endpoint and R the largest upper endpoint. At L every corner
polynomial is nonpositive, and at R every corner polynomial is nonnegative.
Separate affinity makes G at an interior parameter a convex combination of
these four corner values. Strict monotonicity in z consequently encloses
every interior root in [L,R]. This uses no monotonicity of the root in either
parameter.

The rational interval evaluations over that subrectangle and [L,R] then
verify (P4.3), including exclusion of zero in every division. If a box is not
yet certified, the program bisects a parameter side and checks both children;
their closed union is their parent. Starting from the full closed rectangle,
the completed computation accepts265 leaves with maximum depth14 and no
uncovered box. This proves every listed strict inequality at every parameter,
including all boundary values. The full finite algorithm and all its input
constants appear verbatim below.

Every player has a positive hazard in the period. After deleting any one
player, another player's proper positive hazard still occurs each period;
hence all four deleted-opponent survival products are strictly below1.
Section P2 proves exact Nash against unrestricted behavioral deviations, signed
offset and positive-scale invariance, and the fixed uniform target U_A.
The grand coalition remains unreachable under one replacement, since the
largest prescribed support is the pair23. Thus every finite T>=0 is covered.

### P5. Stationary123 for every N>=25/2

#### P5.1. The complete continuous branch

For 0<x<=7/20 let y(x),z(x) be the unique roots in (0,x/2) of

    F3(x,y)=(-30x^2+40x-10)y^2
                 +(29x^2-39x+30)y+x^2-10x=0,
    F2(x,z)=(-3x^2+7x-4)z^2
                 +(x^2-5x+3)z+2x^2-x=0.            (SN.1)

Here x,y,z will be the Quit probabilities of players1,2,3 respectively.
Both constant coefficients are strictly negative. The quadratic coefficient
of F2 is -(x-1)(3x-4)<0. Its derivative in z on [0,x/2] is therefore
minimized at x/2, with value

    D2(x)=-3x^3+8x^2-9x+3.

The derivative D2' has negative leading coefficient and discriminant-68,
so D2 strictly decreases and is at least D2(7/20)=5611/8000>0.
The quadratic coefficient of F3 changes sign at1/3, but is at least-10
throughout the required interval. Consequently, for 0<=y<=x/2,

    partial_y F3>=-20y+29x^2-39x+30>=30-49x>=257/20>0.

At the right endpoints,

    F3(x,x/2)=x(10-42x+49x^2-15x^3)/2,
    F2(x,x/2)=x(2-6x+9x^2-3x^3)/4.

The first bracket strictly decreases on [0,7/20], since its derivative is
at most -42+98(7/20)<0, and ends at211/320>0. The second bracket has
increasing derivative on that interval, with final derivative-321/400<0;
it too decreases and ends at6991/8000>0. Thus each polynomial changes
sign on its interval and is strictly increasing there. The intermediate
value theorem gives the asserted unique roots. Their nonzero derivatives
give continuous dependence on x, including x=7/20.

The ratios y/x,z/x lie in (0,1/2). Substituting y=xu,z=xv and dividing
(SN.1) by x yields limiting equations 30u-10=0 and 3v-1=0. Every
accumulation limit of either bounded ratio is therefore1/3, so

    y(x)/x ->1/3, z(x)/x ->1/3 as x decreases to zero. (SN.2)

#### P5.2. The funding map covers the entire requested ray

Set

    Q1=-y/10-2z+yz,
    N(x)=[(9/10)y-z-(1-y)(1-z)Q1]/(yz)-1.            (SN.3)

This is continuous on 0<x<=7/20. Equation (SN.2) gives xN(x)->6,
so N(x) tends to positive infinity as x decreases to zero. At x=7/20
the equations become

    130y^2+7961y-1351=0,
    -767z^2+549z-42=0.

Exact endpoint substitution, together with the established derivative
signs, gives

    yl=16923461/10^8 < y < yh=16923462/10^8,
    zl=8710211/10^8 < z < zh=8710212/10^8.

Expanding (SN.3) gives

    N=-yz+11y/10-y/(10z)+3z-41/10+1/z-2z/y+1/y.

Each term has the following outward bound on the preceding positive
intervals:

    N(7/20)<-yl*zl+11yh/10-yl/(10zh)+3zh-41/10
                +1/zl-2zl/yh+1/yl
             <12499/1000<25/2.                     (SN.4)

The final two inequalities are exact rational comparisons verified by the
full checker below. For any finite requested N>=25/2, choose a positive
x0 small enough that N(x0)>N. Continuity on [x0,7/20] and (SN.4) supplies
x with N(x)=N. Monotonicity or uniqueness of this funding parameter is not
assumed. The endpoint N=25/2 is included with strict funding slack, and all
chosen hazards remain strictly positive.

#### P5.3. Full stationary equations and the outside-player cap

Use stationary hazards q=(0,x,y,z). For the three active players, the
literal Quit endpoints and Quit-minus-passive contributions are

    Q1=-y/10-2z+yz, Q2=-2x+4z-3xz, Q3=-x/10+y-3xy,
    Delta1=(9/10)y-z-(N+1)yz,
    Delta2=-x+z, Delta3=(9/10)x-2y.

Here Delta_i=Q_i-P_i, where P_i is the expected immediate reward from
nonempty opponent quitting coalitions when i Continues. Put

    H1=(1-y)(1-z), H2=(1-x)(1-z), H3=(1-x)(1-y).

The equations (SN.1) and N(x)=N are exactly H_i Q_i=Delta_i for i=1,2,3.
In fact H2 Q2-Delta2=F2 and 10(H3 Q3-Delta3)=F3; the player1
identity is (SN.3). Taking V_i=Q_i for these players makes their Continue
endpoints P_i+H_i V_i equal Q_i. Thus both action endpoints and all active
policy equations coincide.

Player0's nonsingleton participant rewards, in order01,02,03,012,013,023,0123,
are

    -1,-2,-1/10,-6,-41/10,-11/10,-M-T-61/10.

They are all strictly negative. At least one opponent quits with positive
probability, so player0's immediate Quit endpoint Q0 is strictly negative.
Its passive contribution P0 is strictly positive. The singleton1 event
contributes3x(1-y)(1-z). Every other nonempty opponent event contains2 or3,
has reward at least-1, and these events have total probability at most y+z.
Therefore

    P0>=3x(1-y)(1-z)-y-z
       >x[3(1-x/2)^2-1]>=1667x/1600>0.              (SN.5)

Let a=(1-x)(1-y)(1-z)<1 and V0=P0/(1-a)>0. Player0 is inactive, and its
Continue endpoint P0+aV0 equals V0, strictly exceeding Q0. All four policy
equations and all action caps are now established. This specifies the fixed
native terminal value V=(V0,Q1,Q2,Q3) without an external continuation input.

After deleting any one player, at least two of the three positive active
hazards remain. All four deleted-opponent survival factors are strictly below1.
Section P2 therefore applies with ell=1: unrestricted behavioral Nash, almost
sure absorption under every replacement, arbitrary signed row-offset and
positive-scale invariance, and the fixed uniform payoff all follow. Here an
owner0 replacement can reach the grand coalition; its cap used the specified
negative grand entry and the assumptions M,T>=0. No uniform lower hazard or
geometric rate over the unbounded parameter ray is needed or asserted.

### P6. Complete standalone exact checking programs

Each following Python3 program is complete. Save a block to a file and run it
with Python3 and SymPy installed. All strategic production and behavioral
arguments are proved above; the programs verify their exact algebra and, for
the four-phase case, the complete finite rational interval cover. No private
module, generated data file, floating-point decision, or external notebook is
needed by any block.

#### P6.1. Period-two algebra, branch bounds and radical threshold

```python
"""Exact two-branch endpoint identities for the positive-passive family.

This supports the ordinary IVT argument above;
no finite sample of profiles is used to infer an all-parameter theorem.
"""
import sympy as s
from itertools import product
R=s.Rational
u,y,z,N,M,T=s.symbols('u y z N M T')
G=s.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]])
L=s.Matrix([[0,-4,-1,R(9,10)],[-4,0,R(9,10),-1],
            [R(9,10),-1,0,1],[-1,R(9,10),-2,0]])
def reward(i,A):
 B=tuple(j for j in A if j!=i)
 F=0 if not B else G[i,B[0]] if len(B)==1 else (M if i==0 else N) if B==(2,3) and i in (0,1) else -1
 if i not in A:return F
 return F+sum(L[i,j] for j in B)-(M+1 if i==0 else N+1 if i==1 else 0)*int(2 in B and 3 in B)-T*int(i==0 and len(B)==3)
def endpoints(q,v):
 ans=[]
 for i in range(4):
  O=[j for j in range(4) if j!=i];P=Q=0;H=s.prod(1-q[j] for j in O)
  for bb in product((0,1),repeat=3):
   A=tuple(j for j,b in zip(O,bb) if b)
   p=s.prod(q[j] if b else 1-q[j] for j,b in zip(O,bb))
   Q+=p*reward(i,tuple(sorted(A+(i,))))
   if A:P+=p*reward(i,A)
  ans.append((s.factor(Q),s.factor(P+H*v[i])))
 return ans
fy=y*y+(5*u-3)*y+u
fz=-2*z*z+(2*u-3)*z+u
basis=s.groebner([fy,fz],y,z,u,N)
def zero(expr):
 num=s.cancel(expr).as_numer_denom()[0]
 assert basis.reduce(s.expand(num))[1]==0, s.factor(num)
B=(3*u-y-z+N*y*z)/(u+y+z+y*z)
A=3*u+(1-u)*B
VA=[0,A,y,-2*z];VB=[0,B,4*y/(1+y),z/(1+z)]
a=endpoints([u,0,0,0],VB)
b=endpoints([0,0,z/(1+z),y/(1+y)],VA)
b=[tuple(s.factor(v.subs(M,1/y+1/z)) for v in pair) for pair in b]
for i in range(4):
 zero(a[i][1]-VA[i]);zero(b[i][1]-VB[i])
assert a[0][0]==0 and a[1][0]==-u and a[2][0]==-u/10 and a[3][0]==-2*u
zero(b[0][1]);zero(b[2][0]-VB[2]);zero(b[3][0]-VB[3])
assert s.cancel(b[0][0]+(11*y*z+y+20*z)/(10*(y+1)*(z+1)))==0
assert s.cancel(b[1][0]+(11*y*z+20*y+z)/(10*(y+1)*(z+1)))==0
# Exact branch bounding polynomial evaluations.
assert s.factor(fy.subs(y,R(5,3)*u))==4*u*(25*u-9)/9
assert s.factor(fz.subs(z,u/2))==u*(u-1)/2
uf=R(9,25);u0=R(7,20)
y0=(25+s.sqrt(65))/40;z0=(s.sqrt(809)-23)/40
assert s.simplify(fy.subs({u:u0,y:y0}))==0
assert s.simplify(fz.subs({u:u0,z:z0}))==0
K0=(71-s.sqrt(65)+2*s.sqrt(809))/14
assert s.simplify(1/y0+1/z0-K0)==0
assert 65<100 and y0<R(7,8)
assert R(5,2)*u0==R(7,8)
# Both y branches meet at the fold; the z branch is unchanged.
yf=R(3,5);zf=(3*s.sqrt(561)-57)/100
assert s.simplify(fy.subs({u:uf,y:yf}))==0
assert s.simplify(fz.subs({u:uf,z:zf}))==0
assert s.simplify(1/yf+1/zf-(s.sqrt(561)+29)/6)==0
print('PASS: all16 endpoint identities, exact branch bounds, fold and threshold')
print('Threshold:',K0)
```

#### P6.2. Period-four algebra and exact continuum cover

```python
"""Exact four-phase producer on 4<=M<=9, 0<=N<=2.

This checks the rational policy identities and a finite rational interval
cover of the complete parameter rectangle. It is ordinary computer-assisted
mathematics, not a Lean theorem or an unrestricted Fin4 closure.
"""
from fractions import Fraction as F
from itertools import product
import sympy as s
class I:
 def __init__(self,a,b=None):self.a=F(a);self.b=F(a if b is None else b)
 def __add__(x,y):
  if not isinstance(y,I):y=I(y)
  return I(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return I(-x.b,-x.a)
 def __sub__(x,y):return x+-asI(y)
 def __rsub__(x,y):return asI(y)+-x
 def __mul__(x,y):
  y=asI(y);a=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b];return I(min(a),max(a))
 __rmul__=__mul__
 def __truediv__(x,y):
  y=asI(y);assert y.a*y.b>0
  return x*I(1/y.b,1/y.a)
 def __repr__(x):return f'[{float(x.a):.8g},{float(x.b):.8g}]'
def asI(x):return x if isinstance(x,I) else I(x)
def G(n,t,z):return 4*(n-7)*z*z*z+(41-3*n+8*(n-7)*t)*z*z+(-13+(77-5*n)*t)*z-21*t
def bracket(n,t):
 lo,hi=F(2,5),F(11,20)
 assert G(n,t,lo)<0<G(n,t,hi)
 for _ in range(24):
  mid=(lo+hi)/2
  if G(n,t,mid)<0:lo=mid
  else:hi=mid
 return lo,hi
def cert(n0,n1,t0,t1):
 corners=[bracket(n,t) for n,t in product([n0,n1],[t0,t1])]
 z=I(min(x[0] for x in corners),max(x[1] for x in corners));n=I(n0,n1);t=I(t0,t1)
 try:
  p=(n*z*(4*z-3)-28*z*z+45*z-12)/(21-16*z+4*n*z)
  a=2*p/(1-p);b=p/(1+p)
  c=(4*z-p)/(1+p)
  gam=((z/(1-z)+a)/(1-a)-c)/(3-c)
  vals=[p,1-3*p,z,1-z,gam,1-gam,4*a-(1-a)*gam,c, c*(1-gam)-gam, p*z-t*(-p+F(9,10)*z+p*z)]
  return all(v.a>0 for v in vals), (p,z,a,b,gam),vals
 except AssertionError:return False,None,None
# Exact Bernstein derivative check on the entire rectangle.
n,t,z=s.symbols('n t z');D=s.Poly(s.diff(G(n,t,z),z),n,t,z)
def bernstein(poly,variables,bounds):
 x=s.symbols('x:'+str(len(variables)));P=s.Poly(s.expand(poly.as_expr().subs({v:l+(h-l)*u for v,u,(l,h) in zip(variables,x,bounds)})),*x)
 deg=P.degree_list();out=[]
 for k in product(*[range(d+1) for d in deg]):
  out.append(sum(c*s.prod(s.binomial(ki,ji)/s.binomial(di,ji) for ki,ji,di in zip(k,j,deg)) for j,c in P.terms() if all(ji<=ki for ji,ki in zip(j,k))))
 return out
coef=bernstein(D,(n,t,z),[(0,2),(s.Rational(1,11),s.Rational(1,6)),(s.Rational(2,5),s.Rational(11,20))]);assert min(coef)>0
print('monotone cubic derivative minimum Bernstein',min(coef),flush=True)
# Verify identities after imposing the funding formula for p and the cubic G=0.
p=(n*z*(4*z-3)-28*z*z+45*z-12)/(21-16*z+4*n*z)
a=2*p/(1-p);b=p/(1+p);c=(4*z-p)/(1+p)
g=((z/(1-z)+a)/(1-a)-c)/(3-c)
P0=-p-z+p*z/t;P1=-p-z+(n+2)*p*z;h=(1-p)*(1-z)
for expr in [P1+h*(3*a-(1-a)*g), P0-(g*(1+4*p)-3*p)/(1-g)]:
 num=s.fraction(s.factor(expr))[0]
 assert s.rem(num,s.fraction(s.factor(G(n,t,z)))[0],z)==0
# Independent literal endpoint table for the four prescribed support patterns.
P0=-p-z+p*z/t
U=[s.Matrix([0,3*a-(1-a)*g,z/(1-z),-a]),
   s.Matrix([0,-g,3*g+(1-g)*c,0]),
   s.Matrix([g/(1-g),0,c,0]),s.Matrix([P0,0,4*z,p])]
Q=[s.Matrix([0,-a,-a/10,-2*a]),s.Matrix([-g/10,-2*g,4*g,0]),
   s.Matrix([-b,0,-2*b,-b/10]),s.Matrix([-2*p-z/10+p*z,-p/10-2*z+p*z,4*z,p])]
E=[s.Matrix([0,3*a,-a,-a]),s.Matrix([-g,-g,3*g,0]),
   s.Matrix([3*b,0,-b,-b]),
   s.Matrix([P0,P1,3*z+p*z,3*p-2*p*z])]
S=[1-a,1-g,1-b,(1-p)*(1-z)]
active=[(0,),(3,),(1,),(2,3)]
GP=s.Poly(G(n,t,z),z)
def zero_on_root(expr):
 num=s.fraction(s.factor(expr))[0]
 return s.rem(num,GP.as_expr(),z)==0
for k in range(4):
 for i in range(4):
  assert zero_on_root(U[k][i]-E[k][i]-S[k]*U[(k+1)%4][i])
 for i in active[k]:assert zero_on_root(U[k][i]-Q[k][i])
# The only three nontrivial inactive inequalities are exactly the intervals
# checked below; all other differences are positive from p,z,a,b,g>0.
assert zero_on_root(U[0][1]-Q[0][1]-(4*a-(1-a)*g))
assert zero_on_root(U[1][2]-Q[1][2]-(c*(1-g)-g))
assert zero_on_root(t*(U[3][0]-Q[3][0])-(p*z-t*(-p+s.Rational(9,10)*z+p*z)))
print('exact cyclic policy identities and literal endpoint table PASS',flush=True)
stack=[(F(0),F(2),F(1,11),F(1,6),0)];leaves=0;maxdepth=0;maxstack=0
while stack:
 n0,n1,t0,t1,depth=stack.pop();ok,pars,vals=cert(n0,n1,t0,t1)
 if ok:leaves+=1;maxdepth=max(depth,maxdepth);continue
 if depth>=24:
  print('FAILED',n0,n1,t0,t1,pars,vals);raise SystemExit(1)
 # Normalize side lengths to the original parameter rectangle.
 if (n1-n0)/2>=(t1-t0)/(F(1,6)-F(1,11)):
  mid=(n0+n1)/2;stack.extend([(n0,mid,t0,t1,depth+1),(mid,n1,t0,t1,depth+1)])
 else:
  mid=(t0+t1)/2;stack.extend([(n0,n1,t0,mid,depth+1),(n0,n1,mid,t1,depth+1)])
 if leaves and leaves%1000==0:print('progress',leaves,len(stack),flush=True)
print('PASS exact closed rectangle 4<=M<=9,0<=N<=2; leaves',leaves,'depth',maxdepth)
```

#### P6.3. Stationary123 algebra and complete funding ray

```python
"""Exact branch-extension certificate for formula17 stationary123, N >= 25/2.

All input data are literal rational reward formulas. This is ordinary symbolic
verification, not Lean and not a numerical parameter scan.
"""
from itertools import combinations
import sympy as s

R = s.Rational
x, y, z, M, N, T = s.symbols('x y z M N T')
G = s.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
              [-1, -1, 0, 3], [-1, -1, 3, 0]])
L = s.Matrix([[0, -4, -1, R(9, 10)], [-4, 0, R(9, 10), -1],
              [R(9, 10), -1, 0, 1], [-1, R(9, 10), -2, 0]])
I = tuple(range(4))


def subsets(items):
    return [frozenset(a) for k in range(len(items)+1)
            for a in combinations(items, k)]


def passive(i, B):
    if not B:
        return s.S.Zero
    if len(B) == 1:
        return G[i, next(iter(B))]
    if B == frozenset((2, 3)) and i in (0, 1):
        return (M, N)[i]
    return s.S.NegativeOne


def reward(i, A):
    B = A - {i}
    value = passive(i, B)
    if i in A:
        value += sum(L[i, j] for j in B)
        if {2, 3} <= B and i in (0, 1):
            value -= (M, N)[i] + 1
    if i == 0 and A == frozenset(I):
        value -= T
    return value


W = {(i, A): reward(i, A) for A in subsets(I) if A for i in I}
assert len(W) == 60
q = (0, x, y, z)
Q, P, H = [], [], []
for i in I:
    opponents = tuple(j for j in I if j != i)
    qi = pi = 0
    for B in subsets(opponents):
        mass = s.prod(q[j] if j in B else 1-q[j] for j in opponents)
        qi += mass * W[i, B | {i}]
        if B:
            pi += mass * W[i, B]
    Q.append(s.expand(qi))
    P.append(s.expand(pi))
    H.append(s.prod(1-q[j] for j in opponents))

F3 = (-30*x*x+40*x-10)*y*y+(29*x*x-39*x+30)*y+x*x-10*x
F2 = (-3*x*x+7*x-4)*z*z+(x*x-5*x+3)*z+2*x*x-x
Q1 = -y/10-2*z+y*z
funding = (R(9, 10)*y-z-(1-y)*(1-z)*Q1)/(y*z)-1
assert s.expand(H[2]*Q[2]-(Q[2]-P[2])-F2) == 0
assert s.expand(10*(H[3]*Q[3]-(Q[3]-P[3]))-F3) == 0
assert s.cancel((H[1]*Q[1]-(Q[1]-P[1])).subs(N, funding)) == 0

# Complete root interval 0 < x <= 7/20, 0 <= y,z <= x/2.
xmax = R(7, 20)
a2 = -3*x*x+7*x-4
assert s.expand(a2+(x-1)*(3*x-4)) == 0
d2 = s.expand(s.diff(F2, z).subs(z, x/2))
assert d2 == -3*x**3+8*x*x-9*x+3
assert s.discriminant(s.diff(d2, x), x) == -68
assert d2.subs(x, xmax) == R(5611, 8000) > 0
# The F3 quadratic coefficient changes sign, so do not retain the old sign premise.
a3 = -30*x*x+40*x-10
assert s.expand(a3+10+10*x*(3*x-4)) == 0
assert s.expand(s.diff(F3, y)-2*a3*y) == 29*x*x-39*x+30
assert 30-49*xmax == R(257, 20) > 0
b2 = 2-6*x+9*x*x-3*x**3
b3 = 10-42*x+49*x*x-15*x**3
assert s.expand(F2.subs(z, x/2)-x*b2/4) == 0
assert s.expand(F3.subs(y, x/2)-x*b3/2) == 0
assert s.expand(s.diff(b2, x, 2)-(18-18*x)) == 0
assert s.diff(b2, x).subs(x, xmax) == -R(321, 400) < 0
assert b2.subs(x, xmax) == R(6991, 8000) > 0
assert -42+98*xmax == -R(77, 10) < 0
assert b3.subs(x, xmax) == R(211, 320) > 0

# The original small-x funding limit remains 6/x.
u, v = s.symbols('u v')
assert s.limit(F3.subs(y, x*u)/x, x, 0) == 30*u-10
assert s.limit(F2.subs(z, x*v)/x, x, 0) == 3*v-1
assert s.limit(x*funding.subs({y: x/3, z: x/3}), x, 0) == 6

# Exact endpoint root enclosures and an outward rational funding bound.
ylo, yhi = R(16923461, 10**8), R(16923462, 10**8)
zlo, zhi = R(8710211, 10**8), R(8710212, 10**8)
assert s.expand(400*F3.subs(x, xmax)) == 130*y*y+7961*y-1351
assert s.expand(400*F2.subs(x, xmax)) == -767*z*z+549*z-42
for polynomial, variable, lo, hi in ((F3, y, ylo, yhi), (F2, z, zlo, zhi)):
    assert 0 < lo < hi < xmax/2
    assert polynomial.subs({x: xmax, variable: lo}) < 0
    assert polynomial.subs({x: xmax, variable: hi}) > 0
expanded = -y*z+R(11, 10)*y-y/(10*z)+3*z-R(41, 10)+1/z-2*z/y+1/y
assert s.cancel(funding-expanded) == 0
upper = (-ylo*zlo+R(11, 10)*yhi-ylo/(10*zhi)+3*zhi-R(41, 10)
         +1/zlo-2*zlo/yhi+1/ylo)
assert upper < R(12499, 1000) < R(25, 2)

# Complete outside-owner0 cap: every participant reward is negative, passive >= -1.
assert [W[0, A] for A in subsets(I) if 0 in A and len(A)>1] == [
    -1, -2, -R(1, 10), -6, -R(41, 10), -R(11, 10), -M-T-R(61, 10)]
for B in subsets((1, 2, 3)):
    if B and B != frozenset((1,)):
        assert passive(0, B) in (s.S.NegativeOne, M)
assert 3*(1-xmax/2)**2-1 == R(1667, 1600) > 0

print('PASS: exact full table, complete stationary active equations and all branch bounds.')
print('PASS: N(7/20) < 12499/1000 < 25/2, with a continuous ray to infinity.')
print('PASS: full inactive-owner0 cap for every M,T >= 0, all deleted clocks geometric.')
```

## 7. Completion of the family and the original-game adapter

The base-square classification in Section B excludes every negative-payoff
minimum for0<=M,N<=4. The classification in Section M, including the complete
incoming023 theorem in Section R, does the same for
0<=M<=43/5,2<=N<=25/2. In either region, Section6 excludes every nonnegative
minimum. If A_Z were positive, Sections3--4 would have constructed precisely
such a positive-Never minimum. This contradiction proves A_Z=0 in both
source regions. The three constructions in Section P give exact absorbing
terminal Nash profiles on their stated regions, and therefore A_Z=0 there
as well. The exhaustive cover in Section2 now proves A_Z=0 for every finite
M,N,T>=0, including every parameter boundary.

Fix one such game, positive recipient factors lambda_i, and nonnegative own
levels s_i. Given eta>0, A_Z=0 supplies an actual almost-surely absorbing
independent profile with total native debt below eta/max_i lambda_i.
Positive recipient scaling multiplies coordinate i's debt by lambda_i.
Adding s_i to every absorbing reward adds exactly s_i to its prescribed
payoff, since prescribed absorption is almost sure. A unilateral behavioral
deviation gains only s_i times its absorption probability, at most s_i.
Its deviation gain therefore does not increase under this offset. We obtain
terminal eta-Nash profiles for the ORIGINAL table R at every eta>0, against
all complete unilateral behavioral replacements. Live and all-Never-path
rewards remain zero throughout this argument.

These terminal profiles have payoffs in the compact finite-dimensional cube
determined by the fixed game's finite reward bound. Along accuracies tending
to zero, select a convergent subsequence of their terminal payoff vectors,
with limit v. The terminal-to-uniform consumer supplies, at each desired
positive accuracy, a profile from a sufficiently late part of this same
family and a horizon threshold. Its prescribed Cesaro payoff is close to v
and every sufficiently long horizon caps all behavioral deviations. The
existing exact semantic equivalence named in Section8 provides this step
with the required strict-error budget. Thus v is fixed BEFORE the requested
accuracy. No single target is required to work for different parameter games.

The signed-offset argument for the explicit Section P profiles is stronger
because those profiles absorb even after deleting any player: every
unilateral deviation then gains the same offset. The actual-source proof
uses only prescribed absorption. Consequently the global source-based
conclusion retains s_i>=0, exactly as stated in the theorem.

## 8. Exact semantic sources and Lean handoff

The action and reward timing are defined by `quittingGame` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`:
the live state pays zero and transitions to the selected absorbing coalition;
only later absorbed dates pay that coalition's reward.

The goal declaration is `quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean`. It defines the arbitrary
finite-quitting existence proposition; it is not a proof of that proposition.

The precise existing interfaces used here are:

* `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
  `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
  in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`
  identify complete independent-law payoffs and full law-replacement caps
  with the behavioral model, including literal Never.
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies mixed
  one-stage Nash existence at every real continuation. All faces, including
  sure actions, are allowed. It supplies the arbitrary second root in the
  incoming023 replacement; that root's support is not an extra witness.
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean` gives exact
  coordinate debt scaling by common Continue mass when a prefix is Nash
  against the complete cap. In particular it preserves equal payoff/cap
  annotations, as used in the one-row and two-row minimum contradictions.
* `quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart` in
  `UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean` bounds
  full-cap discrepancies after a fixed finite word by opponent-deleted
  survival times the positive initial discrepancy. Applying it in both
  directions gives the nonexpansiveness used to remove virtual seeds from
  the local finite-face argument. Intermediate rows need not be Nash at the
  original seed.
* `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  states the exact equivalence between terminal approximate Nash profiles
  at every positive accuracy and existence of ONE uniform-equilibrium
  payoff. Section7 supplies its right-hand hypothesis for the original game.

The reward-coordinate conventions are also those of `rawChild_future_delta`,
`rawChild_future_base`, `rawChild_joining_delta`, and `rawChild_joining_base`
in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`.
All polynomial programs independently reconstruct their needed endpoints
from the printed raw table or its explicitly proved equivalent finite formula.

These are existing source declarations under their stated imports. No new
Lean file, build, or formalization seal is claimed for this manuscript.
The new ordinary mathematics comprises the actual compact-source argument,
finite-face local escape, exhaustive source support exclusions, exact
same-tail replacement, and complete parameter cover. Each strategically
necessary profile, tail, root, or finite word is produced by those arguments.
None is left as an assumed source structure field. No unproved paper claim
is used as an intermediate theorem.

A direct formalization can first encode the actual annotation closure,
(Prefix), (Debt), (Repair), and genuine-tail extraction. The local lemma uses
induction on the finite zero set. The source cases then reduce to the printed
rational identities and exact Bernstein certificates. The final consumer is
the existing terminal semantic equivalence above. Formalizing only a
supplied-object verifier would not establish the source theorem.

## C. Exact new-scope calibration and complete prior-class comparison

### C1. Exact calibration and conclusion

Let R_i(A)=1+Z_i(A) for every nonempty A subset{0,1,2,3}, where

| A | Z(A), recipients0,1,2,3 |
| --- | --- |
| 0 | (0,3,-1,-1) |
| 1 | (3,0,-1,-1) |
| 2 | (-1,-1,0,3) |
| 3 | (-1,-1,3,0) |
| 01 | (-1,-1,-1,-1) |
| 02 | (-2,-1,-1/10,-1) |
| 03 | (-1/10,-1,-1,-2) |
| 12 | (-1,-1/10,-2,-1) |
| 13 | (-1,-2,-1,-1/10) |
| 23 | (5,5,4,1) |
| 012 | (-6,-41/10,-11/10,-1) |
| 013 | (-41/10,-6,-1,-11/10) |
| 023 | (-11/10,-1,9/10,-4) |
| 123 | (-1,-11/10,-1,-21/10) |
| 0123 | (-111/10,-111/10,-1/10,-31/10) |

Live dates, including the selecting date, and the path where nobody quits
pay zero. After
selection the original reward R is repeated. Randomization is private and
independent, and deviations may replace complete behavioral strategies.
This is exactly formula17 with M=N=5,T=0 and all four original own levels1.
The comparisons below also hold after decreasing only Z0(0123) by any T>=0.

The complete prior-class inventory and exact exclusions are given below.
The parameter-dependent calculations are performed at5: they include every
stationary support, every joint/solo/solo role, every root of the specified
period-four recipe, and all stated transformed-neighborhood selections.
Thus the calibration records new coverage beyond the prior raw classes;
failure of a sufficient numerical threshold alone is never its proof of
nonadmission. The already covered calibration M=N=7/2 is not used for this
purpose.

For the prior qualitative source neighborhood, the scope statement is
deliberately precise: every radius produced by its proof after imposing
epsilon<=1/100 excludes this calibration, even after all relabelings,
signed offsets and positive row scales. Its existential theorem provides
no numerical admission at5. This audit does not assert that every possible
larger valid UE neighborhood is disjoint from5; Section C6 explains the
distinction. No unrestricted periodic-profile nonexistence is claimed.

### C2. Parameter-independent exclusions and complete finite selections

Put Gamma_ij=Z_i(j), J_ij=Z_i(ij), with zero diagonals, and L=J-Gamma.
Here

    L=[0,-4,-1,9/10; -4,0,9/10,-1;
       9/10,-1,0,1; -1,9/10,-2,0],
    det Gamma=45,
    Gamma^-1=(1/15)[2,7,3,3;7,2,3,3;3,3,2,7;3,3,7,2].

The native joining fields at continuation zero are

    g0=L0*q-6q2q3-Tq1q2q3,
    g1=L1*q-6q2q3, g2=L2*q, g3=L3*q.                 (1)

The companion checker reconstructs(1) from all sixty rewards and repeats
the following complete finite-selector arguments at M=N=5.

**Quiet children.** For a child S and outsider o, necessary singleton
future and joining rows for nonnegative weights lambda_i are

    sum_(i in S) lambda_i*(-Gamma_ij)>=-Gamma_oj,
    sum_(i in S) lambda_i*L_ij>=L_oj  (j in S).

For thirteen children a joining row has nonpositive left coefficients and
a positive right side. For S=123,o=0, add future rows2,3 and twice joining
row3: the coefficients are(0,-1,-3) and the right side19/5. Thus all14
nonnegative weight systems fail, even without the Never row. A recursive
quiet construction also fails at its outermost proper child.

**Every sure-owner/punishment selection.** The complete complementary Nash
fibers with the indicated owner forced sure are

| Sure owner | Complete fiber | Owner Quit-minus-Continue gap |
| --- | --- | --- |
| 0 | (1,0,1,0) | -1 |
| 1 | (0,1,t,1), 0<=t<=9/20 | -1-(51/10)t |
| 2 | (0,1,1,0) | -1 |
| 3 | (0,0,1,1) | -2 |

For example, at q0=1, row1 is strictly negative on its entire opponent
cube, so q1=0; row3 is then strictly negative, giving q3=0; row2 is
positive, giving q2=1. At q1=1, row0 forces q0=0. Row2=q3-1 forces
q3=1, and row3 gives the displayed interval. The remaining two fibers
follow successively from rows0,3,1 and rows1,2,0. All boundary faces are
included. Every profile has another sure quitter, making the designated
owner's punishment-continuation coefficient zero. Thus no punishment law
repairs these negative gaps. Larger persistent bases would give a complete
root with a sure owner and fail the same census.

**Blocks, funding, traps and weights.** All149 ordered marked-subset/block
choices fail: a marked set meeting23 has a positive participant sum in
its first block meeting23; a marked set contained in01 sees the strictly
positive disjoint passive row5 at23. The two-unmarked funding rules can
only mark01 and orient the unmarked pair2,3. The exact separate and
calendar thresholds are7/3 and32/11, both below5. All36 funding roles
are included. The calendar value32/11 is the true optimum: for all150
deterministic calendars,

    20u2-41u3<=63+62(u2-m2)-3(u3-m3), m3>=-1,

and the mixture of time vectors(0,0,0,0),(1,0,0,1),(1,1,1,0), with
weights1/4,9/40,21/40, attains diagonal observation(11/10,-1,11/10,-1).

The sole premium trap and greatest core is23. Its joining product is-2;
both inserted participant values4,1 are positive. Every recipient has a
negative participant value. At singleton0 the trap's inserted values are
-1/10,-2, defeating every positive trap-floor weight. Pure23 falsifies
ProductLow. The vector Z(01) is strictly negative, the sum of inserted
singleton tests0,1 is(-1,-1,-21/10,-21/10), and the sum of the four
singleton columns is(1,1,1,1). These defeat every nonzero nonnegative
lower ledger, inserted floor and upper ledger, respectively.

**Role and singleton geometry.** Each of the three pair partitions has a
negative scheduled joining and participant coordinate. Every triple has a
negative joining coordinate and a strictly negative active singleton row.
No negative-singleton pair has both participant coordinates below its
singleton value-1. The favorite pairs have participant entries(-1,-1,4,1).
Rows0,1 have no positive participant pair entry. All reciprocal singleton
products are positive; four pairs are mutually negative. There is no
positive directed triple or Hamiltonian cycle, nor an opposite-sign
singleton edge. These statements exhaust all partitions and all circular
roles, are unchanged by positive row scaling, and are checked literally.

Gamma is R0: the singleton, pair and triple support tests above rule out
nonzero homogeneous complementarity on proper supports; invertibility
rules out full support. Its strictly positive inverse and determinant45
give degree+1, so neither the degree-not-one nor negative-determinant
inverse producer applies. A negative reciprocal principal pair has neither
the Q property nor a nonzero homogeneous complementary vector, defeating
the projective Q-bar alternative.

### C3. Complete stationary exclusion at N=5

Adding the original own offset1 preserves all stationary comparisons when
at least two hazards are positive, because every unilateral replacement
then faces geometric opponent absorption. Original AllNever is not an
equilibrium: quitting alone pays1. The sure-owner fibers in Section C2
exclude every profile with a sure hazard. At a singleton support j, choose
i with Gamma_ij=-1,J_ij=-1/10. Its prescribed native value is-1, while
immediate Quit pays-q_j/10>-1. For each proper pair, active stationarity
requires q_j=Gamma_ij/J_ij. Pair01 has ratio-3, each cross pair a ratio10,
and pair23 a ratio3; thus all proper pairs fail.

**Support023.** Put x=q0,y=q2,z=q3. Its third active equation is

    (-3x^2+4x-1)y^2+(x^2-2x+3)y+2x^2-x=0.

For x>=1/2 all terms are nonnegative and the y term is positive. For
x<1/2 its left side increases on0<=y<=1, and at y=1/20 equals
(817x^2-436x+59)/400>0, whose discriminant is-2716. Thus y<1/20.
The owner0 equation gives

    M=(1-2y)/z+(11/10-y-1/(10y))z+3y-41/10+1/y.

This decreases in z>0 on the necessary range, so z<1 forces
M>9/(10y)-2>16, contradicting M=5.

**Support123.** Put x=q1,y=q2,z=q3. The complete active equations are

    F1=(1-y)(1-z)(-y-20z+10yz)-9y+10z+60yz=0,
    F2=(-3x^2+7x-4)z^2+(x^2-5x+3)z+2x^2-x=0,
    F3=(-30x^2+40x-10)y^2+(29x^2-39x+30)y+x^2-10x=0.

The lexicographic Groebner basis in z,y,x has three members: a linear
z equation, a linear y equation, both with nonzero constant leading
coefficient, and x times a degree14 polynomial P. In descending order
P has coefficients

    33968510242650,-307665408098943,1225548294133932,
    -2842110213322922,4331571368629306,-4752836982039919,
    4157727919496144,-3186077022771016,2162524139653648,
    -1202620786598080,501186595819200,-146131186224000,
    27831680800000,-3096084000000,152208000000.

It has exactly three roots in(0,1), isolated in

    (7477/27207,1708/6215),
    (3749/13287,2152/7627),
    (14104/16815,17007/20276).

The first two linear equations uniquely reconstruct z=Z(x), y=Y(x).
Every Bernstein coefficient of Y-1 on the first two intervals exceeds,
respectively,7871/500 and91/5; every coefficient of -Z on the third
exceeds23/8. Hence all candidates violate properness. The checker derives
the equations from literal Quit and joining endpoints, computes the basis,
counts every real root and verifies these exact rational signs. Both
quadratic branches are retained; no small-hazard branch restriction is used.

#### C3U1. Parameter-uniform stationary equations

Use the native family table in Section1 for arbitrary finite M,N,T>=0.

We prove that no exact stationary terminal Nash profile has proper support
012,013 or0123, for every M,N,T>=0. Proper support S means 0<q_i<1 for
i in S and q_i=0 outside S. These exclusions therefore apply at the
calibration. They remain valid after arbitrary signed recipient offsets and
positive recipient scales: with at least three positive hazards, deleting
any one player leaves positive stationary opponent absorption. Every unilateral
replacement absorbs geometrically, so a terminal-row offset adds the same
constant to the prescribed and deviating payoffs, and a positive scale
preserves their comparison. The original own offset1 is included.

For any product root q, write

    H_i=product_(j!=i)(1-q_j),
    Q_i=sum_(B subset I minus{i}) Pr_q(B) Z_i(B union{i}),
    P_i=sum_(nonempty B subset I minus{i}) Pr_q(B) Z_i(B),
    Delta_i=Q_i-P_i.

Here Pr_q(B)=product_(j in B)q_j product_(j notin B,j!=i)(1-q_j).
If a proper active player i has stationary terminal value U_i, both first
actions are used and must attain that value at a terminal Nash profile.
Consequently

    U_i=Q_i=P_i+H_i U_i,
    H_i Q_i-Delta_i=0.                              (1)

It suffices to rule out these necessary equations; no claim of their
sufficiency is used. The exact programs below derive their coefficients
directly from the raw rewards.

#### C3U2. Proper supports012 and013 are impossible

For support012 put x=q0,y=q1,z=q2. The vectors of active Quit values and
joining differences, in player order0,1,2, are

    Q=(-3yz-y-2z, -(30xz+10x+z)/10, (10xy-x-20y)/10),
    Delta=(-4y-z, -(40x-9z)/10, (9x-10y)/10).

For support013 put x=q0,y=q1,z=q3. In player order0,1,3 they are

    Q=(-(30yz+10y+z)/10, -3xz-x-2z, (10xy-20x-y)/10),
    Delta=(-(40y-9z)/10, -4x-z, -(10x-9y)/10).

In either case the survival factors in the same coordinate order are

    H=((1-y)(1-z),(1-x)(1-z),(1-x)(1-y)).

These give the complete three polynomial equations (1), after clearing
their constant rational denominators. No M,N,T occurs: every queried
coalition is a subset of the active triple, and neither triple contains23
or the grand coalition. Thus their equations are identical for every
parameter choice, including M=N=5. The checker below uses the representative
M=N=4 in its reward routine solely for coordinates that these active
equations never query.

For each triple, compute the lexicographic Groebner basis with variable
order z,y,x. The basis has exactly three members. The first is linear in
z and the second linear in y, each with a nonzero constant leading
coefficient; hence they reconstruct z=Z(x), y=Y(x) as polynomials. The
last member is a degree16 polynomial P(x). Its exact closed-unit-interval
root count is2; x=0 is one root and x=1 is not a root. There is exactly
one remaining proper candidate, simple and isolated as follows:

| support | interval containing the sole root in (0,1) | positive polynomial on that interval | lower bound on every Bernstein coefficient |
|---|---|---|---|
| 012 | (1436/6341,4397/19416) | -Y(x) | 2927/10000 |
| 013 | (7231/7265,13824/13889) | Y(x)-1 | 133/1250 |

The lower bounds in the last column are strict. The complete deterministic
program in Section C3U4.1 reconstructs the three input equations, computes the
basis over the rationals, verifies its linear reconstruction structure,
counts every real root in [0,1], isolates the sole proper candidate, and
computes every Bernstein coefficient of the indicated test polynomial.
It uses exact symbolic and rational arithmetic throughout.

To spell out the last sign implication, on an interval [l,h] substitute
x=l+(h-l)s. For a polynomial sum_j a_j s^j of degree d its Bernstein
coefficient at k is

    b_k=sum_(j<=k) a_j binom(k,j)/binom(d,j).

The polynomial equals sum_k b_k binom(d,k)s^k(1-s)^(d-k). These basis
functions are nonnegative on [0,1] and sum to1, so strictly positive
coefficients imply strict positivity on the whole interval. Hence the
support012 candidate has y<0, and the support013 candidate has y>1.
Both contradict properness. Every proper solution of the original equations
must satisfy the computed basis and its unique linear reconstructions,
so no branch or alternative reconstruction is omitted.

#### C3U3. Proper full support is impossible

Write q=(r,t,p,z). All passive rewards of each recipient are at least-1.
Literal Never therefore earns at least-1 against stationary opponents, and
Nash implies U_i>=-1. By (1), Delta_i=H_i U_i, so

    Delta_i+H_i>=0.                                (2)

Set K=5-p-z+pz. Direct expansion of the complete table gives

    Delta_0+H_0=1-2p-z/10-Kt-Mpz-Ttpz,
    Delta_1+H_1=1-p/10-2z-Kr-Npz.                  (3)

Because M,N,T>=0 and K>0 on the unit cube, (2)--(3) imply

    Kt<=1-2p-z/10, Kr<=1-p/10-2z.

In particular p,z<=1/2. The identities

    9K-40(1-2p-z/10)=5(1-z)+p(71+9z)>=0,
    9K-40(1-p/10-2z)=5(1-p)+z(71+9p)>=0

then imply the closed necessary box

    0<=r,t<=9/40, 0<=p,z<=1/2.                      (4)

This argument uses no positive lower hazard bound and is uniform in the
unbounded nonnegative parameters.

Let S(M,N,T;q)=sum_i(H_i Q_i-Delta_i). Exact expansion gives

    S(M,N,T;q)=S(0,0,0;q)
      +Mpz(1-tH_0)+Npz(1-rH_1)+Ttpz(1-H_0).        (5)

All added terms are nonnegative on the unit cube. Define

    R(q)=S(0,0,0;q)-(r+t+p+z)/100.

This polynomial has coordinatewise degree at most(2,2,2,2). The following
six closed rectangles cover (4), with disjoint interiors. For each rectangle
the last column is the exact minimum of its81 tensor Bernstein coefficients
of degree(2,2,2,2).

| r | t | p | z | minimum coefficient |
|---|---|---|---|---:|
| [9/80,9/40] | [0,9/40] | [0,1/2] | [0,1/2] | 2497/128000 |
| [0,9/80] | [9/80,9/40] | [0,1/2] | [0,1/2] | 3899/64000 |
| [0,9/80] | [0,9/80] | [1/4,1/2] | [0,1/2] | 253/800 |
| [0,9/80] | [0,9/80] | [0,1/4] | [0,1/4] | 0 |
| [9/160,9/80] | [0,9/80] | [0,1/4] | [1/4,1/2] | 349/51200 |
| [0,9/160] | [0,9/80] | [0,1/4] | [1/4,1/2] | 3553/512000 |

For a box with endpoints l_j,h_j substitute q_j=l_j+(h_j-l_j)s_j.
If the resulting power coefficients are a_k, the tensor Bernstein
coefficient at i in{0,1,2}^4 is

    sum_(k<=i) a_k product_j binom(i_j,k_j)/binom(2,k_j).

The tensor basis functions are nonnegative and sum to1. The nonnegative
minima therefore prove R(q)>=0 throughout (4). Section C3U4.2 contains the
complete standard-library rational checker: it reconstructs all60 rewards,
the endpoint polynomials, every parameter contribution, both bound
identities, and all486 coefficients. There is no external coefficient file
or numerical search.

Combining this certificate with (5), every nonzero q in (4) satisfies

    S(M,N,T;q)>=(r+t+p+z)/100>0.

Full-support stationary Nash would require all four summands to vanish by
(1). This contradiction proves the full-support exclusion, in particular
for M=N=5 and every finite T>=0. As explained in Section C3U1, signed offsets
and positive recipient scales preserve this exclusion. No conclusion about
nonstationary equilibria follows.

#### C3U4. Complete standalone programs

Save either Python block to a file and run with Python3. The first requires
SymPy; the second uses only the Python standard library. Both compute their
complete exact certificates from literal input data.

##### C3U4.1. Anchor triples012 and013

```python
"""Exact exclusion of proper stationary012 and013; all family parameters.

Ordinary algebraic proof, not a full stationary census or Lean theorem.
"""
import sympy as s
from itertools import product
x,y,z,t=s.symbols('x y z t')
G=s.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]])
L=s.Matrix([[0,-4,-1,s.Rational(9,10)],[-4,0,s.Rational(9,10),-1],[s.Rational(9,10),-1,0,1],[-1,s.Rational(9,10),-2,0]])
def reward(i,A):
 B=set(A)-{i}; p=0 if not B else G[i,next(iter(B))] if len(B)==1 else 4 if B=={2,3} and i<2 else -1
 return p+(sum(L[i,j] for j in B)-(5 if i<2 and {2,3}<=B else 0) if i in A else 0)
def bernstein(poly,l,h):
 pp=s.Poly(s.expand(poly.subs(x,l+(h-l)*t)),t);d=pp.degree()
 return [sum(pp.nth(j)*s.binomial(k,j)/s.binomial(d,j) for j in range(k+1)) for k in range(d+1)]
for S in [(0,1,2),(0,1,3)]:
 q={i:a for i,a in zip(S,[x,y,z])};F=[]
 for i in S:
  opp=[j for j in S if j!=i];Qi=0;Pi=0;Hi=s.prod(1-q[j] for j in opp)
  for b in product([0,1],repeat=2):
   A={j for j,v in zip(opp,b) if v};mass=s.prod(q[j] if v else 1-q[j] for j,v in zip(opp,b))
   Qi+=mass*reward(i,A|{i});Pi+=mass*reward(i,A)
  F.append(s.together(Hi*Qi-(Qi-Pi)).as_numer_denom()[0])
 gb=s.groebner(F,z,y,x);assert len(gb.polys)==3
 P=s.Poly(gb.polys[-1].as_expr(),x);Y=s.solve(gb.polys[1].as_expr(),y)[0];Z=s.solve(gb.polys[0].as_expr(),z)[0]
 assert Y.free_symbols<={x} and Z.free_symbols<={x}
 for k,var in [(0,z),(1,y)]:
  pp=s.Poly(gb.polys[k].as_expr(),var);assert pp.degree()==1 and not pp.coeff_monomial(var).free_symbols
 assert P.count_roots(0,1)==2 and P.eval(0)==0 and P.eval(1)!=0
 intervals=[(I,m) for I,m in P.intervals(eps=s.Rational(1,10**8)) if 0<I[0]<I[1]<1]
 assert len(intervals)==1 and intervals[0][1]==1
 (l,h),m=intervals[0];test=-Y if S==(0,1,2) else Y-1
 b=bernstein(test,l,h);assert min(b)>0
 print(S,'interval',l,h,'fails', 'y>0' if S==(0,1,2) else 'y<1','margin>',s.floor(min(b)*10000)/10000)
print('PASS: proper stationary012 and013 impossible for every M,N,T; ordinary exact proof.')
```

##### C3U4.2. Full support

```python
"""Exact six-box certificate excluding proper full-support stationary Nash.

Run with Python 3. Standard-library rational algebra only.
The mathematical claim and stationary-to-box adapter are proved above.
This is ordinary mathematical evidence, not a Lean check.
"""
from fractions import Fraction as F
from itertools import product
from math import comb

ZERO = (0, 0, 0, 0)
ONE = {ZERO: F(1)}


def clean(poly):
    return {k: v for k, v in poly.items() if v}


def add(*polys):
    out = {}
    for poly in polys:
        for k, v in poly.items():
            out[k] = out.get(k, F(0)) + v
    return clean(out)


def scale(poly, factor):
    return clean({k: v * F(factor) for k, v in poly.items()})


def mul(*polys):
    out = ONE
    for poly in polys:
        nxt = {}
        for k, v in out.items():
            for ell, w in poly.items():
                idx = tuple(a + b for a, b in zip(k, ell))
                nxt[idx] = nxt.get(idx, F(0)) + v * w
        out = clean(nxt)
    return out


def sub(a, b):
    return add(a, scale(b, -1))


q = [{tuple(int(i == j) for j in range(4)): F(1)} for i in range(4)]
r, t, p, z = q
survive = [sub(ONE, qi) for qi in q]
H = [mul(*(survive[j] for j in range(4) if j != i)) for i in range(4)]


def table(M, N, T):
    return {
        1: (0, 3, -1, -1), 2: (3, 0, -1, -1),
        4: (-1, -1, 0, 3), 8: (-1, -1, 3, 0),
        3: (-1, -1, -1, -1), 5: (-2, -1, F(-1, 10), -1),
        9: (F(-1, 10), -1, -1, -2), 6: (-1, F(-1, 10), -2, -1),
        10: (-1, -2, -1, F(-1, 10)), 12: (M, N, 4, 1),
        7: (-6, F(-41, 10), F(-11, 10), -1),
        11: (F(-41, 10), -6, -1, F(-11, 10)),
        13: (F(-11, 10), -1, F(9, 10), -4),
        14: (-1, F(-11, 10), -1, F(-21, 10)),
        15: (-M-T-F(61, 10), -N-F(61, 10), F(-1, 10), F(-31, 10)),
    }


def endpoints(M, N, T):
    reward = table(M, N, T)
    Q, P = [], []
    for i in range(4):
        opp = [j for j in range(4) if j != i]
        qi, pi = {}, {}
        for bits in product((0, 1), repeat=3):
            coalition = sum(1 << j for j, bit in zip(opp, bits) if bit)
            mass = mul(*(q[j] if bit else survive[j] for j, bit in zip(opp, bits)))
            qi = add(qi, scale(mass, reward[coalition | (1 << i)][i]))
            if coalition:
                pi = add(pi, scale(mass, reward[coalition][i]))
        Q.append(qi)
        P.append(pi)
    delta = [sub(Q[i], P[i]) for i in range(4)]
    residual = [sub(mul(H[i], Q[i]), delta[i]) for i in range(4)]
    return Q, P, delta, residual


Q, P, delta, residual = endpoints(0, 0, 0)
K = add(scale(ONE, 5), scale(p, -1), scale(z, -1), mul(p, z))
bound0 = add(ONE, scale(p, -2), scale(z, F(-1, 10)), scale(mul(K, t), -1))
bound1 = add(ONE, scale(p, F(-1, 10)), scale(z, -2), scale(mul(K, r), -1))
assert add(delta[0], H[0]) == bound0
assert add(delta[1], H[1]) == bound1
for idx, params in enumerate(((1, 0, 0), (0, 1, 0), (0, 0, 1))):
    _, _, changed_delta, changed_residual = endpoints(*params)
    dc = [sub(changed_delta[i], delta[i]) for i in range(4)]
    fc = [sub(changed_residual[i], residual[i]) for i in range(4)]
    expected_dc = [{}, {}, {}, {}]
    expected_fc = [{}, {}, {}, {}]
    if idx == 0:
        expected_dc[0] = scale(mul(p, z), -1)
        expected_fc[0] = mul(p, z, sub(ONE, mul(t, H[0])))
    elif idx == 1:
        expected_dc[1] = scale(mul(p, z), -1)
        expected_fc[1] = mul(p, z, sub(ONE, mul(r, H[1])))
    else:
        expected_dc[0] = scale(mul(t, p, z), -1)
        expected_fc[0] = mul(t, p, z, sub(ONE, H[0]))
    assert dc == expected_dc and fc == expected_fc
assert sub(scale(K, 9), scale(add(ONE, scale(p, -2), scale(z, F(-1, 10))), 40)) == add(scale(sub(ONE, z), 5), mul(p, add(scale(ONE, 71), scale(z, 9))))
assert sub(scale(K, 9), scale(add(ONE, scale(p, F(-1, 10)), scale(z, -2)), 40)) == add(scale(sub(ONE, p), 5), mul(z, add(scale(ONE, 71), scale(p, 9))))
R = sub(add(*residual), scale(add(*q), F(1, 100)))


def bernstein(poly, box):
    """Tensor degree (2,2,2,2), under q_i=l_i+(h_i-l_i)*u_i."""
    power = {}
    for exponent, coefficient in poly.items():
        assert all(d <= 2 for d in exponent)
        for index in product(*(range(d + 1) for d in exponent)):
            value = coefficient
            for d, k, (lo, hi) in zip(exponent, index, box):
                value *= comb(d, k) * lo ** (d - k) * (hi - lo) ** k
            power[index] = power.get(index, F(0)) + value
    coefficients = []
    for index in product(range(3), repeat=4):
        value = F(0)
        for exponent, coefficient in power.items():
            if all(e <= k for e, k in zip(exponent, index)):
                term = coefficient
                for e, k in zip(exponent, index):
                    term *= F(comb(k, e), comb(2, e))
                value += term
        coefficients.append(value)
    assert len(coefficients) == 81
    return coefficients


# These six boxes partition [0,9/40]^2 x [0,1/2]^2 along shared faces.
a, b, c = F(9, 40), F(9, 80), F(9, 160)
half, quarter = F(1, 2), F(1, 4)
boxes = [
    ((b, a), (0, a), (0, half), (0, half)),
    ((0, b), (b, a), (0, half), (0, half)),
    ((0, b), (0, b), (quarter, half), (0, half)),
    ((0, b), (0, b), (0, quarter), (0, quarter)),
    ((c, b), (0, b), (0, quarter), (quarter, half)),
    ((0, c), (0, b), (0, quarter), (quarter, half)),
]
minimum = [F(2497, 128000), F(3899, 64000), F(253, 800), F(0), F(349, 51200), F(3553, 512000)]
for i, (box, expected) in enumerate(zip(boxes, minimum), start=1):
    coefficients = bernstein(R, box)
    assert min(coefficients) == expected and expected >= 0
    print(f'box {i}: all 81 exact Bernstein coefficients >= {expected}')
print('PASS: raw-table identities, parameter monotonicity, floor bounds, six-box positivity.')
print('Proper full-support stationary exact terminal Nash is impossible for all M,N,T >= 0.')
```



This exhausts every stationary profile of R. It excludes every previously
implemented or accepted producer whose conclusion includes an exact
stationary terminal Nash profile, including every unspecified threshold,
pole role or stationary neighborhood. In particular the passive-pole guard
census retains its one passing role(1,3,0,2); the terminal stationary
obstruction excludes its producing region, rather than incorrectly claiming
that all preliminary guards fail.

**A positive stationary regret gap at each fixed table.**

For each fixed finite T>=0 there is a number delta_T>0 such that every
stationary product profile of the ORIGINAL own-one game has full terminal
exploitability max_i(B_i-U_i) at least delta_T. No uniform lower bound over T is asserted.
This strengthens the noncoverage comparison to producers of arbitrarily
accurate stationary profiles, without excluding any nonstationary strategy.

For original stationary hazards q let H_i be opponent survival, Q_i the
original immediate-Quit endpoint and P_i the original nonempty opponent
contribution. When H_i<1 put W_i=P_i/(1-H_i). A pure deadline k has value

    W_i+H_i^k*(Q_i-W_i),

and Never has value W_i. Thus the complete behavioral cap is exactly
`B_i(q)=max(Q_i,W_i)`. If H_i=1 all opponents Never, so the cap is1:
finite quitting pays the own singleton1 and Never pays0. These formulas
price every complete replacement; mixing deadlines does not increase the
supremum.

Suppose contrary to the claim that stationary q^n have exploitability
tending to zero. Pass to a subsequence converging to q*. At q*!=0 the
prescribed original terminal payoff is continuous, since its per-date
absorption probability stays positive. If at least two entries of q* are
positive, every H_i<1 and the displayed cap formula is continuous. If q*
has exactly one positive entry i, all other caps are continuous, while
`B_i(q*)=1=Q_i(q*)<=liminf B_i(q^n)`. Thus all caps are lower semicontinuous
at any nonzero q*. Vanishing debt would make q* exact stationary Nash,
contradicting the complete support census.

It remains q^n->0. Profiles q^n=0 have exploitability one and may be
discarded. Put a_n=sum_i q_i^n and pass to a subsequence with
`q^n/a_n->p`, where p>=0 and sum p_i=1. Boundedness of the fixed table
makes simultaneous-coalition contributions O(a_n^2), and per-date total
absorption is a_n+O(a_n^2). The native prescribed stationary payoff
therefore tends to Gamma*p. Native immediate Quit tends to zero. The
corresponding ORIGINAL quantities are one plus these native quantities,
because the prescribed profile absorbs. Vanishing debt implies

    Gamma*p>=0.                                        (6)

If p_i<1, then opponents' per-date absorption is
`a_n*(1-p_i)+o(a_n)`, and their native Never payoff tends to
`(Gamma*p)_i/(1-p_i)`. Since original Never also absorbs in this case,
its original payoff is one plus that value. The Never-minus-prescribed
gain and vanishing debt imply

    p_i*(Gamma*p)_i/(1-p_i)<=0.

Together with (6), this gives `p_i*(Gamma*p)_i=0`. If p_i=1 the same
equality follows from Gamma_ii=0 and all other p_j=0. Thus p is a nonzero
nonnegative homogeneous complementary vector. This is impossible directly:
if Gamma*p=0 then invertibility gives p=0; otherwise
`p=Gamma^-1*(Gamma*p)>0` because the inverse is strictly positive, and
complementarity would force Gamma*p=0. This final contradiction proves
delta_T>0.

The conclusion concerns stationary profiles at each fixed table. It supplies
neither a positive all-behavior gap nor a counterexample to UE; the new
actual-source theorem provides nonstationary approximate equilibria.

### C4. Complete short-phase selections

Every scheduled hazard in the proper architectures below lies strictly
between0 and1; an unscheduled owner has hazard zero.

**Solo/joint period two.** The mixed-positive-passive theorem forces the
joint pair2,3, in that orientation, and allows only anchor0 or1. With solo
hazard0<u<1 and owner odds Y2=q2/(1-q2),Y3=q3/(1-q3), its full proper
architecture requires

    Y3^2+(5u-3)Y3+u=0,
    -2Y2^2+(2u-3)Y2+u=0,
    5=1/Y2+1/Y3.

The first discriminant gives u<=9/25; the second gives
Y2<u/(3-2u)<=3/19. Hence the last right side exceeds19/3>5. This excludes
every positive branch and both anchors, not only the theorem's sufficient
large-passive threshold.

**Four singleton phases.** Necessary consecutive-owner tests
J_ij<=0,J_ji<=Gamma_ji leave only the order2,0,3,1 and rotations.
Writing u_i=1-q_i for Continue probabilities, its active equations are
u_i(4-4u_(i+1)+u_(i+1)u_(i+2))=1. Subtract opposite equations; the
determinant

    16(1-u1)(1-u2)+u2u3(4-u0)(4-u1)>0

forces opposite u's equal, and then all four equal. Their proper root is
(3-sqrt5)/2. Put p=(sqrt5-1)/2. At owner3's row, recipient2's prescribed
value is1+p but immediate Quit pays4p, a strict gain3p-1>0. This excludes
the whole exact proper architecture and its implicit-function neighborhoods.

**Two copies of one joint pair plus two solos.** The neighborhood theorem
retains every native singleton floor. Its two joint participant premiums
must be nonnegative, forcing pair23. Its second-joint rate is x/(x-2)
in orientation2,3, or y/(y-2) in orientation3,2. Both are negative for
proper first-joint hazards. All24 roles therefore fail its floors or
properness, independently of an unspecified local radius.

**Joint/solo/solo.** The full-dimensional cyclic-child theorem outputs
this exact three-row architecture. Consecutive solo comparisons leave six
distinct words among all24 ordered roles: four cross-joint words and the
joint23 words with solo orders0,1 and1,0. Set X=x/(1-x),Y=y/(1-y) for
the joint hazards. The two solo equations express their hazards as

    z=-B_d(1+X)(1+Y)/Gamma_dc,
    w=B_c/(B_c-Gamma_cd),
    B_i=[Gamma_ia X+Gamma_ib Y+Z_i(ab)XY]/[(1+X)(1+Y)].

The two joint equations equate their next-phase values to
(J_ab-Gamma_ab)Y and(J_ba-Gamma_ba)X. These give two rational equations
in X,Y. Denominators cleared are nonzero for every proper candidate.

For the four cross-joint words the equations do not depend on M,N,T.
Their eliminant is proportional to

    X(4X+1)[11465X^5-16931X^4-55694X^3
                           +58497X^2+62199X+10800],

with no positive root. For the joint23 words at5 the eliminant is

    X(2X-1)(2X+1)(3X+5)
       *(700X^4+1448X^3+115X^2-705X+75).              (2)

The other Groebner member reconstructs Y as a polynomial in X. There
are exactly three positive roots: one in(2188/19641,2617/23492), the
root1/2, and one in(5164/9823,10011/19043). At the latter two, Y<0.
At the first,1/10<X<1/8 and Y>1. Exact Bernstein signs certify each
statement. In solo order0,1, the owner0 joint-row gain is

    [-10X+9Y-61XY]/[10(1+X)(1+Y)]>0,

since its numerator is(9-61X)(Y-1)+(9-71X)>0. In solo order1,0,
recipient3's solo1-row gain is2X-z/10>1/10. Both remaining roles
therefore fail complete inactive caps. This excludes every possible
qualitative neighborhood whose produced profile has the stated architecture.

**The formula17 period-four construction.** The specified exact
producer uses chronological solo0,solo3,solo1,joint23. Merely observing
that its proved rectangle assumes N<=2 would not exclude a different
root selection. At M=N=5 its complete active cubic factors as

    G(z)=-56z^3+166z^2-39z-21
        =-(4z+1)(14z^2-45z+21).

There is exactly one root in(0,1), in(1/2,4/7). Its joint2 hazard must be
p=(-8z^2+30z-12)/(21+4z). Seven times the owner0 joint-row Continue-minus-
Quit cap is6pz+p-(9/10)z. Its positive denominator is40z+210, and
its numerator modulo14z^2-45z+21 equals

    (27669/49)z-2322/7<0.

Thus its entire proper root selection fails. Exact formula17 singleton
and participant data have no nonidentity joint relabeling, and singleton
spreads force every row scale1; the checker exhausts these selections too.
This statement does not exclude unrelated four-date support words.

### C5. Explicit accepted cubes and older implemented calibrations

The ten-phase cube has epsilon=1/1000000, with favorite singleton3 and
negative singleton-1. Under arbitrary signed offsets and positive row
scales, a transformed copy matching our singleton spread4 must satisfy

    4/(4+2epsilon)<=lambda_i<=4/(4-2epsilon).

Signs relative to own singletons identify the favorite pairs; the negative
participant favorite pair must be01. Its passive complementary pair
coordinate, relative to its own singleton, is therefore at most

    [4/(4-2epsilon)]*(4+2epsilon)<5.

This contradicts both marked passive coordinates of our table. It includes
every relabeling and the cube's arbitrary or one-sided grand coordinates.
The same nonadmission persists under independent radius1/1000 perturbations
of our56 non-grand coordinates: replace the scale upper bound by
(4+2/1000)/(4-2epsilon), and5 by5-2/1000.

The global asymmetric-pair cube and four-joint neighborhoods have positive
native participant entries at both favorite pairs, whereas our pair01
has two negative entries. Their stated perturbation margins preserve these
signs. The four-phase passive ray requires a common favorite participant
reward;(-1,-1,4,1) is incompatible after singleton spreads fix scales.

The implemented E1 period-three cylinder also needs an explicit comparison.
Its free coordinates are only recipient0/3 passive-triple or grand entries.
Every favorite participant pair entry, relative to its own singleton,
has magnitude at most2eta, eta=1/50000000. Its singleton spread fixes
lambda_i<=4/(4-2eta). Thus its transformed favorite participant magnitude
is less than1, contradicting our pair01 native magnitude1. This excludes
the entire affine cylinder and its smaller exact/cube classes.

The earlier deadlock integer period-three result is also excluded by the
complete joint/solo/solo architecture proof. Candidate-C nonsingleton
fibers have a zero normalized off-diagonal singleton coordinate, which our
table lacks. Integral-tournament singleton fibers have negative reciprocal
products, while ours are positive. The asymmetric paired-cycle interval
class has two positive native singleton entries in every recipient row;
ours has only one. Componentwise weighted-potential, robust-predecessor,
conditional-face and strict-blocker raw producers output stationary exact
profiles and fail the complete census in Section C3. Ordered-premium peeling
fails at trap23; same-sign pair-core fails its joining product-2; the
nonnegative social-weight chamber fails the upper-ledger singleton sum.
Three-player row-cone inheritance fails the inverse test on every triple.

### C6. The prior source-neighborhood radius: exact scope and limitation

The preceding actual-source neighborhood class proves existence of a positive
radius around the entire
base square0<=M,N<=4,T>=0. Its proof first imposes epsilon<=1/100 in
its quantitative construction and then obtains a sufficiently small radius within that
restriction. Use that produced witness, retaining the stated upper bound.

Consider every transformed copy of every normalized table in that proved
tube. The own singleton is exactly zero before the recipient offset.
Positive and negative singleton signs identify the favorite pairs. Their
native participant signs identify the marked pair as01, even after a
permutation, since the base marked values are-1 and the unmarked values
are4,1. Let0<epsilon<=1/100 be any candidate radius from this proof.
Again singleton spread4 forces

    lambda_i<=4/(4-2epsilon).

The marked passive complementary pair reward before scaling is at most
4+epsilon. Consequently every admitted transformed table has that native
coordinate at most

    [4/(4-2epsilon)]*(4+epsilon)
       <=[4/(4-2/100)]*(4+1/100)<5.                 (3)

Thus the table in Section C1 lies outside every transformed tube using the
proof's documented witness restriction. This is an exact quantitative
scope separation; it does not compare only the centers or assume that
positive distance from a center suffices.

The headline theorem does not specify a maximal possible radius. Since
the full conjecture predicts UE even much farther away, one cannot infer
from(3) that no larger valid neighborhood exists. The accurate conclusion
is that the previously established proof and its chosen radius do not
admit this calibration. No stronger maximal-radius claim is used for the
new-scope comparison.

### C7. Complete inventory and implementation correspondence

The inventory groups producers by a necessary raw test or produced
architecture, preserving all selection variables.

| Earlier class | Complete obstruction at the calibration |
| --- | --- |
| Nonnegative singleton quiet lifts, including recursive outer lifts | All14 child weight cones fail Section C2. |
| Singleton punishment and persistent-base producers | Complete four sure-owner fibers; every available punishment coefficient vanishes. |
| Common leaver, support-specific leavers, weighted floor, mixed traps, mixed-support upper/charge, boxed charges, premium core, joining-attractive and mixed-sign triple core | Sole trap23, joining product-2, positive trap participants, failed global floors, and core size2. |
| Ordered anchor blocks, passive bounds, calendar polytope | All149 block choices and36 funding roles; exact thresholds7/3 and32/11. |
| Graph-free H/J-flat, sink/receiver, two-ledger, nonnegative social-weight | Full lower/upper/floor weight-cone failures. |
| Two-pair join-cap, crossed matching, nonmatching-positive-passive, bounded inverse corners, signed inverse columns | All three pair partitions have negative required joining/participant entries; inverse signs force positive columns. |
| Zero-premium, negative-passive, below-singleton, opposite-sign matching, globally asymmetric, negative-pair-funded phases | No zero participant pair; negative pairs fail both-below tests; favorite participants(-1,-1,4,1) fail every admissible role. |
| Mixed-positive-passive solo/joint | All proper quadratic branches and both anchors fail Section C4. |
| Ordered and unordered rotating mixed pairs, scalar singular circuit | Rows0,1 lack a positive forward participant pair; only one positive participant pair exists. |
| Triple-singleton collision boxes | Every triple has a negative joining entry. |
| Cyclic child, negative-premium cyclic child, global two-joint child, diffuse solo, one/two outsider buffers | No required cyclic singleton triple; full-dimensional qualitative class additionally fails the complete joint/solo/solo architecture. |
| Attached negative pair, joint negative pair/two solo, arbitrary one/both joint premium | Required opposite-sign singleton edge absent. |
| Nonpositive reciprocal, no mutually negative pair, negative-chord Hamiltonian, either signed four-cycle eigenvalue branch | All reciprocal products positive, four mutually negative pairs, no directed required geometry. |
| Four singleton, two copies of one joint pair, four joint phases, four-joint rectangle, four-phase passive ray | Exact architecture, preserved participant signs, or forced singleton/favorite comparisons in Sections C4--C5. |
| Passive triple and monotone passive cap chambers | Positive forward participant premise fails in rows0,1. |
| Positive-inverse jackpots, signed single-column jackpots, signed passive-coalition, raw three-passive-pole, positive-passive stationary triple, stationary face/local/blocker producers | Complete stationary census and positive stationary regret gap in Section C3. |
| Ten-phase cube and E1 cube/cylinder | Every affine/relabelled copy excluded by Section C5. |
| Prior actual-source neighborhood | Every transformed tube under its proved witness epsilon<=1/100 excluded by(3); no maximal-radius assertion. |
| Formula17 period-four and high-passive producers | Complete cubic cap failure or complete stationary/solo-joint architecture exclusion. |

The relevant implemented criteria include
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`,
`SignedFourCycleSingletonData` and `StrictTests` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`, and
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`.
The last theorem requires negative determinant; here it is45.

Quiet-child tests use `rawChild_future_delta`, `rawChild_future_base`,
`rawChild_joining_delta`, `rawChild_joining_base` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`
and `nonempty_cappedClockParentRewardCertificate_iff` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExactLPAlternative.lean`.
These are source correspondences, not a new Lean check or declaration.

Generic consumers of supplied cycles, interval-face boxes, paths, perfect
sequences or root witnesses are not unconditional raw reward-class
producers. This coverage statement does not purport to show that no such
strategic certificate exists at the calibration. In particular the E1
general interval-face compiler remains available if new strategic box data
are produced; its finite cube/cylinder input class is what Section C5 excludes.


### C8. Complete exact calibration program

Save this block and the two uniform stationary blocks in Section C3 as
separate Python files and run each. This block requires SymPy, reconstructs
all sixty rewards and checks every finite selection, new polynomial root
census, and quantitative transformed-class inequality used above. The other
two blocks supply the parameter-independent stationary supports. Together
they constitute the full exact calibration certificate; no numerical
sampling is used to exclude a root or a strategy class.

```python
"""Exact old-selector coverage for the original-own-one middle table.

Save this standalone block and run it with Python3.
Requires SymPy. M=N=5; T>=0 decreases only the native recipient0 grand reward.
This is a coverage checker, not the ten-phase existence certificate and not
a complete stationary-equilibrium or arbitrary-controller census.
"""
from itertools import combinations, permutations, product
import sympy as s

I = tuple(range(4))
T = s.symbols('T', nonnegative=True)
q = s.symbols('q0:4', nonnegative=True)
R = s.Rational
K = s.Integer(5)
Z = {frozenset(A): tuple(map(s.sympify, row)) for A, row in {
    (0,): (0,3,-1,-1), (1,): (3,0,-1,-1),
    (2,): (-1,-1,0,3), (3,): (-1,-1,3,0),
    (0,1): (-1,-1,-1,-1), (0,2): (-2,-1,R(-1,10),-1),
    (0,3): (R(-1,10),-1,-1,-2),
    (1,2): (-1,R(-1,10),-2,-1), (1,3): (-1,-2,-1,R(-1,10)),
    (2,3): (K,K,4,1), (0,1,2): (-6,R(-41,10),R(-11,10),-1),
    (0,1,3): (R(-41,10),-6,-1,R(-11,10)),
    (0,2,3): (R(-11,10),-1,R(9,10),-4),
    (1,2,3): (-1,R(-11,10),-1,R(-21,10)),
    (0,1,2,3): (-K-R(61,10)-T,-K-R(61,10),-R(1,10),-R(31,10))
}.items()}
assert len(Z) == 15 and all(len(v) == 4 for v in Z.values())

def z(i, A):
    return Z[frozenset(A)][i] if A else s.Integer(0)

def original(i, A):
    return 1+z(i,A) if A else s.Integer(0)

def subsets(A):
    return [frozenset(B) for n in range(len(A)+1)
            for B in combinations(sorted(A),n)]

ALL = subsets(I)
G = s.Matrix([[z(i,{j}) for j in I] for i in I])
J = s.Matrix([[z(i,{i,j}) for j in I] for i in I])
L = J-G
assert all(original(i,{i}) == 1 for i in I)
assert G.det() == 45
assert G.inv() == s.Matrix([[2,7,3,3],[7,2,3,3],
                           [3,3,2,7],[3,3,7,2]])/15
assert L == s.Matrix([[0,-4,-1,R(9,10)],[-4,0,R(9,10),-1],
                      [R(9,10),-1,0,1],[-1,R(9,10),-2,0]])
assert all(L[i,j]+L[j,i] < 0 for i,j in combinations(I,2))
assert all(any(L[i,j] > 0 for i in I) for j in I)

def field(i):
    others=[j for j in I if j != i]
    return s.expand(sum(s.prod(q[j] if j in A else 1-q[j] for j in others)
                        *(z(i,A|{i})-z(i,A)) for A in subsets(others)))

g = [field(i) for i in I]
models = list(L*s.Matrix(q))
models[0] -= (K+1)*q[2]*q[3]+T*q[1]*q[2]*q[3]
models[1] -= (K+1)*q[2]*q[3]
assert all(s.expand(a-b) == 0 for a,b in zip(g,models))

# Complete sure-owner elimination is justified by strict signs on each cube
# and the surviving one-dimensional face, not by sampling equilibria.
def strict_negative_on_cube(expr, variables):
    # Affine in T with a nonpositive coefficient on the hazard cube.
    assert s.diff(expr,T,2) == 0
    for bits in product((0,1),repeat=len(variables)):
        v=s.expand(expr.subs(dict(zip(variables,bits))))
        assert v.subs(T,0) < 0 and s.diff(v,T) <= 0

strict_negative_on_cube(g[1].subs(q[0],1),[q[2],q[3]])
assert s.expand(g[3].subs({q[0]:1,q[1]:0})) == -1-2*q[2]
assert g[2].subs({q[0]:1,q[1]:0,q[3]:0}) == R(9,10)
strict_negative_on_cube(g[0].subs(q[1],1),[q[2],q[3]])
assert g[2].subs({q[0]:0,q[1]:1}) == q[3]-1
assert g[3].subs({q[0]:0,q[1]:1}) == R(9,10)-2*q[2]
strict_negative_on_cube(g[0].subs(q[2],1),[q[1],q[3]])
strict_negative_on_cube(g[3].subs({q[2]:1,q[0]:0}),[q[1]])
assert g[1].subs({q[2]:1,q[0]:0,q[3]:0}) == R(9,10)
strict_negative_on_cube(g[1].subs(q[3],1),[q[0],q[2]])
assert g[2].subs({q[3]:1,q[1]:0}) == 1+R(9,10)*q[0]
strict_negative_on_cube(g[0].subs({q[3]:1,q[1]:0,q[2]:1}),[])
t = s.symbols('t', nonnegative=True)
fibers=[(1,0,1,0),(0,1,t,1),(0,1,1,0),(0,0,1,1)]
owner_gaps=[s.expand(g[i].subs(dict(zip(q,p)))) for i,p in enumerate(fibers)]
assert owner_gaps == [-1,-1-(K+R(1,10))*t,-1,-2]
for i,p in enumerate(fibers):
    assert any(p[j] == 1 for j in I if j != i)
print('PASS: entire four forced-owner fibers; every actual punishment coefficient is zero')

# All14 quiet-child systems have an exact dual obstruction using singleton
# future/joining rows, independent of all grand entries.
for child in (A for A in ALL if 0 < len(A) < 4):
    if child == {1,2,3}:
        outside=0; terms=[('F',2,1),('F',3,1),('J',3,2)]
    else:
        j,outside=next((j,o) for j in child for o in I if o not in child
                       and L[o,j]>0 and max(L[i,j] for i in child)<=0)
        terms=[('J',j,1)]
    coeff=[sum(w*(-G[i,j] if kind=='F' else L[i,j]) for kind,j,w in terms)
           for i in child]
    rhs=sum(w*(-G[outside,j] if kind=='F' else L[outside,j])
            for kind,j,w in terms)
    assert max(coeff)<=0<rhs
print('PASS: all14 full quiet-child weight systems fail exact necessary rows')

# All149 ordered-subset/block choices fail the old unboxed criterion for
# every strictly positive weighting. The two box/polytope criteria force C01.
block_count=0
for marked in ALL[1:]:
    owners=sorted(marked)
    for n in range(1,len(marked)+1):
        for labels in product(range(n),repeat=len(marked)):
            if set(labels)!=set(range(n)): continue
            blocks=[{i for i,label in zip(owners,labels) if label==k} for k in range(n)]
            if marked & {2,3}:
                first=next(B for B in blocks if B & {2,3})
                assert all(z(i,{2,3})>0 for i in first & {2,3})
            else:
                assert marked <= {0,1}
                assert all(z(i,{2,3})>0 for i in marked)
            block_count+=1
assert block_count==149

# Exact calendar threshold at the sole viable unmarked orientation2,3.
def calendars(remaining):
    yield ()
    for A in subsets(remaining)[1:]:
        for tail in calendars(remaining-A): yield (A,)+tail

CALS=list(calendars(frozenset(I)))
assert len(CALS)==150
def value(calendar,i,never=False):
    for A in calendar:
        B=A-{i} if never else A
        if B: return z(i,B)
    return s.Integer(0)

for cal in CALS:
    u2,u3,m2,m3=value(cal,2),value(cal,3),value(cal,2,True),value(cal,3,True)
    assert 20*u2-41*u3 <= 63+62*(u2-m2)-3*(u3-m3)
    assert m3>=-1
def time_vector(times):
    cal=tuple(frozenset(i for i in I if times[i]==v) for v in sorted(set(times)))
    return s.Matrix([value(cal,2),value(cal,3),value(cal,2,True),value(cal,3,True)])
mix=sum((w*time_vector(times) for w,times in [
    (R(1,4),(0,0,0,0)),(R(9,40),(1,0,0,1)),(R(21,40),(1,1,1,0))]),s.zeros(4,1))
assert mix==s.Matrix([R(11,10),-1,R(11,10),-1])
assert 1/mix[0]+2/(-mix[1])==R(32,11)<K
passive_up=max([0]+[z(2,A) for A in ALL[1:] if 2 not in A])
passive_down=max([0]+[-z(3,A) for A in ALL[1:] if 3 not in A])
assert passive_up==3 and passive_down==1
assert 1/passive_up+2/passive_down==R(7,3)<K
print('PASS: all weighted-block roles; true calendar32/11 and passive-extrema7/3 both fail K5')

# Traps and weight cones: all assertions hold uniformly for T>=0.
traps=[A for A in ALL[1:] if all(any(i in B and z(i,B)>0
               for B in subsets(A)[1:]) for i in A)]
assert traps==[frozenset({2,3})]
assert all(any(z(i,A)<0 for A in ALL[1:] if i in A) for i in I)
assert all(z(i,{0,1})==-1 for i in I)
assert [J[i,0]+J[i,1] for i in I]==[-1,-1,-R(21,10),-R(21,10)]
assert [sum(G[i,j] for j in I) for i in I]==[1]*4
assert J[2,3]>0 and J[3,2]>0 # Pure23 falsifies ProductLow.
assert L[2,3]*L[3,2]==-2 # Weak mixed pair-trap product fails.
assert z(2,{0,2})<0 and z(3,{0,3})<0 # Trap global inserted floor fails.
print('PASS: sole trap23; all nonzero lower/upper/floor weights and pair-trap alternatives fail')

# All partitions fail nonnegative pair joining; all fail nonnegative pair
# participant premises, including the signed-column variant since G^-1>0.
PARTITIONS=[((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))]
for partition in PARTITIONS:
    pairs=[(i,j) for A in partition for i in A for j in A if i!=j]
    assert any(L[i,j]<0 for i,j in pairs)
    assert any(J[i,j]<0 for i,j in pairs)
assert not any(J[i,j]<G[i,j]<0 and J[j,i]<G[j,i]<0
               for i,j in combinations(I,2))
assert [J[i,j] for i,j in ((0,1),(1,0),(2,3),(3,2))]==[-1,-1,4,1]
assert all(G[i,j]*G[j,i]>0 for i,j in combinations(I,2))
assert sum(bool(G[i,j]<0 and G[j,i]<0) for i,j in combinations(I,2))==4
assert not any(all(G[p[k],p[(k+1)%3]]>0 for k in range(3))
               for p in permutations(I,3))
assert not any(all(G[p[k],p[(k+1)%4]]>0 for k in range(4))
               for p in permutations(I))
assert all(any(all(G[i,j]<0 for j in A if j!=i) for i in A)
           for A in combinations(I,3))

# Rotating class: each recipient must have a positive forward pair premium;
# rows0,1 have none. Check all circular role assignments literally as well.
assert all(all(J[i,j]<=0 for j in I) for i in (0,1))
assert not any(all(J[p[k],p[(k+1)%4]]>0 for k in range(4))
               for p in permutations(I))
# Scalar singular circuit needs TWO distinct positive pairs03 and13.
assert not any(J[p[3],p[0]]>0 and J[p[1],p[3]]>0 for p in permutations(I))

# Necessary endpoint inequalities for consecutive singleton owners.
orders=[p for p in permutations(I) if all(
    J[p[k],p[(k+1)%4]]<=0 and
    J[p[(k+1)%4],p[k]]<=G[p[(k+1)%4],p[k]] for k in range(4))]
assert len(orders)==4
assert set(orders)=={(2,0,3,1),(0,3,1,2),(3,1,2,0),(1,2,0,3)}
p=(s.sqrt(5)-1)/2
assert s.simplify(p*p+p-1)==0
assert 3*p-1>0 # Mate2's native forced Quit4p exceeds actual1+p.
print('PASS: all3 pair partitions, all24 rotating/scalar roles, all24 proper singleton orders')

# The mixed-positive pair theorem can use only2,3 in this orientation, with
# anchor0 or1. Its actual quadratic architecture forces K>19/3>5.
roles=[]
for a,o,i,j in permutations(I):
    if (G[a,i]<0 and G[a,j]<0 and G[i,a]<0 and G[j,a]<0
        and G[i,j]>0 and G[j,i]>0 and J[i,j]>G[i,j]
        and 0<J[j,i]<G[j,i]): roles.append((a,o,i,j))
assert roles==[(0,1,2,3),(1,0,2,3)]
u,y=s.symbols('u y',real=True)
assert s.expand((5*u-3)**2-4*u)==s.expand(25*(u-R(9,25))*(u-1))
assert R(9,25)/(3-2*R(9,25))==R(3,19)
assert R(19,3)>K

# Complete passive-pole guard census. Each expression is affine in T, so
# endpoint and slope signs certify the entire T>=0 ray.
def uniform_sign(expr):
    expr=s.cancel(expr)
    assert s.diff(expr,T,2)==0
    a,b=expr.subs(T,0),s.diff(expr,T)
    if a==0 and b==0:return 0
    if a>0 and b>=0:return 1
    if a<0 and b<=0:return -1
    raise AssertionError(('Nonconstant sign requires subdivision',expr))
def joining(i,A):return z(i,set(A)|{i})-z(i,A)
preliminary=[];passing=[]
for i,j,k,l in permutations(I):
    a,b=joining(i,{l}),joining(i,{k,l})
    if not (a>0>b):continue
    c=s.cancel(a/(a-b))
    guards=tuple(s.cancel(v) for v in (
        joining(k,{l}),joining(k,{i,l}),
        (1-c)*joining(j,{l})+c*joining(j,{k,l}),
        (1-c)*joining(j,{i,l})+c*joining(j,{i,k,l}),
        c*(c*z(l,{k,l})-z(l,{k})),
        (1-c)*joining(l,{i})+c*joining(l,{i,k})))
    signs=tuple(uniform_sign(v) for v in guards)
    preliminary.append(((i,j,k,l),c,guards))
    if signs==(-1,-1,-1,-1,1,-1):passing.append(((i,j,k,l),c,guards))
assert len(preliminary)==7 and len(passing)==1
role,c,guards=passing[0]
assert role==(1,3,0,2) and c==R(9,40)
assert guards==(-1,-5,-R(89,40),-R(53,40),R(3519,16000),-R(319,400))
assert (original(3,{0,1}),original(0,{2,3}),original(2,{1,3}))==(0,1+K,0)
print('PASS: all24 pole roles, exactly one passing endpoint role retained honestly')
print('PASS: complete literal original-own-one family and all listed finite selectors, T>=0')
print('This finite-selector program is composed with separate exact all-support stationary proofs.')

# The unordered rotating extension retains the same positive forward pair
# premise. Rows0,1 therefore exclude all its circular labelings as well.
assert not any(all(J[p[k],p[(k+1)%4]]>0 for k in range(4))
               for p in permutations(I))

# Exclude the ENTIRE signed-affine/relabelled ten-phase numerical cube.
# Singleton spread4 pins each positive scale, independent of its offset.
eps=R(1,1000000)
lamlo=4/(4+2*eps);lamhi=4/(4-2*eps)
assert lamlo*(1-2*eps)>0
# Negative favorite participant entries identify the marked pair under
# every allowed matching-preserving relabeling. Its passive23 entry would
# have to be at most lamhi*(4+2eps), impossible at K=5.
assert K > lamhi*(4+2*eps)
# This exclusion even holds on an independent56-coordinate neighborhood
# of radius1/1000, with ALL grand coordinates ignored.
eta=R(1,1000)
robust_lamlo=(4-2*eta)/(4+2*eps)
robust_lamhi=(4+2*eta)/(4-2*eps)
assert 1-2*eta>0 and 3-2*eta>0
assert -1+2*eta<0<robust_lamlo*(1-2*eps)
assert K-2*eta>robust_lamhi*(4+2*eps)
print('PASS: all24 unordered rotating roles and every affine/relabelled ten-phase cube')
print('PASS: ten-phase nonadmission remains true on the independent56-coordinate radius1/1000')

# The older two-joint/same-pair plus two solo construction retains all
# singleton floors. Its joint premiums must therefore both be nonnegative.
# Only pair23 survives. One repeated-joint hazard is then negative for
# EVERY proper first-joint hazard, in either orientation.
nonnegative_pairs=[(i,j) for i,j in permutations(I,2) if J[i,j]>=0 and J[j,i]>=0]
assert nonnegative_pairs==[(2,3),(3,2)]
x,y=s.symbols('x y',real=True)
for i,j in nonnegative_pairs:
    xi,eta,H,ell=J[i,j],J[j,i],-G[j,i],G[i,j]
    e=s.cancel(eta*x/(H+eta+eta*x))
    f=s.cancel(xi*y/(xi-ell+xi*y))
    if (i,j)==(2,3): assert e==x/(x-2)
    else: assert f==y/(y-2)
print('PASS: all24 two-joint/same-pair neighborhood roles fail its retained floors or properness')

# Every triple contains a negative reciprocal pair. Hence no triple has
# all six positive joining increments; triple/singleton collision-box
# selection and joining-attractive triple hypotheses cannot hold.
for A in combinations(I,3):
    assert any(L[i,j]<0 for i,j in permutations(A,2))

# Reciprocal products are strictly positive. Both signed four-cycle
# eigenvalue branches, directed cyclic children and alternating singleton
# floor certificates require an opposite-sign adjacent pair.
assert not any(G[i,j]<=0<=G[j,i] for i,j in permutations(I,2))
# The singleton matrix is R0: principal triples contain a strictly negative
# active row; positive pairs force positive active image; negative pairs
# force negative active image; full determinant is nonzero.
for A in combinations(I,3):
    assert any(all(G[i,j]<0 for j in A if j!=i) for i in A)
assert G.det()>0 and all(v>0 for v in G.inv())
# Existing nonnegative-inverse degree theorem gives degree sign(det G)=+1.
assert G*s.ones(4,1)==s.ones(4,1)
print('PASS: all triple selections, signed cycles, R0/degree and inverse-child geometry')

# The frozen actual-source proof chooses its witness radius <=1/100.
# This excludes every affine/relabelled copy of its PROVED thin tube.
# It does not assert that no unspecified larger valid UE ball can exist.
eps_source=R(1,100)
source_lamhi=4/(4-2*eps_source)
assert -1+eps_source<0<1-eps_source
assert K > source_lamhi*(4+eps_source)
print('PASS: every transformed source tube with its proved radius <=1/100 excludes K5')

# The implemented E1 affine cylinder fixes every singleton and pair within
# its tiny cube. Its favorite-pair native participant coordinates are near0.
eps_e1=R(1,50000000)
assert (4/(4-2*eps_e1))*(2*eps_e1)<1
# Formula17's exact singleton and participant data have no nonidentity
# joint relabeling; the singleton row spreads also force every scale to1.
symmetries=[p for p in permutations(I)
            if all(G[p[i],p[j]]==G[i,j] and J[p[i],p[j]]==J[i,j]
                   for i in I for j in I)]
assert symmetries==[(0,1,2,3)]
print('PASS: transformed E1 cylinder excluded; exact formula17 role matching is unique')

# Complete proper stationary123 active census at N=5.
x,y,z,t=s.symbols('x y z t')
F3=(-30*x*x+40*x-10)*y*y+(29*x*x-39*x+30)*y+x*x-10*x
F2=(-3*x*x+7*x-4)*z*z+(x*x-5*x+3)*z+2*x*x-x
F1=s.expand((1-y)*(1-z)*(-y-20*z+10*y*z)-9*y+10*z+60*y*z)
Q1=-y/R(10)-2*z+y*z
Q2=-2*x+4*z-3*x*z
Q3=-x/R(10)+y-3*x*y
assert s.expand(10*((1-y)*(1-z)*Q1-(R(9,10)*y-z-6*y*z)))==F1
assert s.expand((1-x)*(1-z)*Q2-(-x+z)-F2)==0
assert s.expand(10*((1-x)*(1-y)*Q3-(R(9,10)*x-2*y))-F3)==0
basis=s.groebner([F1,F2,F3],z,y,x)
assert len(basis.polys)==3
P=s.Poly(basis.polys[-1].as_expr(),x)
quoted=[33968510242650,-307665408098943,1225548294133932,
-2842110213322922,4331571368629306,-4752836982039919,
4157727919496144,-3186077022771016,2162524139653648,
-1202620786598080,501186595819200,-146131186224000,
27831680800000,-3096084000000,152208000000]
assert P.degree()==15 and P.eval(0)==0 and P.eval(1)!=0
assert s.Poly(P.as_expr()/x,x).monic()==s.Poly.from_list(quoted,x).monic()
assert P.count_roots(0,1)==4
reconstruction=[]
for eq,var in zip(basis.polys[:2],(z,y)):
    pp=s.Poly(eq.as_expr(),var)
    assert pp.degree()==1 and not pp.coeff_monomial(var).free_symbols
    root=s.solve(eq.as_expr(),var)
    assert len(root)==1 and root[0].free_symbols<={x}
    reconstruction.append(root[0])
ZZ,YY=reconstruction

def bernstein1(poly,var,interval):
    lo,hi=interval
    tt=s.Dummy('t')
    pp=s.Poly(s.expand(poly.subs(var,lo+(hi-lo)*tt)),tt)
    degree=max(0,pp.degree())
    return [sum(pp.nth(j)*s.binomial(k,j)/s.binomial(degree,j)
                for j in range(k+1)) for k in range(degree+1)]

stationary_intervals=[(R(7477,27207),R(1708,6215)),
                      (R(3749,13287),R(2152,7627)),
                      (R(14104,16815),R(17007,20276))]
for k,interval in enumerate(stationary_intervals):
    lo,hi=interval
    assert 0<lo<hi<1 and P.count_roots(lo,hi)==1
    if k: assert stationary_intervals[k-1][1]<lo
    test=YY-1 if k<2 else -ZZ
    margin=min(bernstein1(test,x,interval))
    assert margin>[R(7871,500),R(91,5),R(23,8)][k]
print('PASS: all three proper-x stationary123 roots at N5 violate hazard properness')

# Complete proper joint/solo/solo words, every24 owner-role assignment.
X,Y=s.symbols('X Y')
Gamma=s.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]])
J=s.Matrix([[0 if i==j else Z[frozenset((i,j))][i] for j in I] for i in I])
roles=[(a,b,c,d) for a,b,c,d in permutations(I)
       if a<b and J[c,d]<=0 and J[d,c]<=Gamma[d,c]]
assert len(roles)==6
assert {(c,d) for a,b,c,d in roles}=={(0,1),(1,0),(0,3),(1,2),(2,0),(3,1)}
systems={}
for a,b,c,d in roles:
    if {a,b}!={2,3} and J[a,b]!=R(-1,10):a,b=b,a
    name='positive' if (a,b)==(2,3) else 'cross'
    data=(Gamma[a,b],Gamma[a,c],Gamma[a,d],Gamma[b,c],Gamma[b,d],
          Gamma[c,d],Gamma[d,c],J[a,b],J[b,a],
          Z[frozenset((a,b))][c],Z[frozenset((a,b))][d])
    expected=((3,-1,-1,-1,-1,3,3,4,1,5,5) if name=='positive' else
              (-1,3,-1,-1,3,-1,-1,R(-1,10),-2,-1,-1))
    assert data==expected
    systems[name]=data
for name,data in systems.items():
    gab,gac,gad,gbc,gbd,gcd,gdc,pa,pb,kc,kd=data
    x,y=X/(1+X),Y/(1+Y)
    D=(1+X)*(1+Y)
    Bc=(gac*X+gbc*Y+kc*X*Y)/D
    Bd=(gad*X+gbd*Y+kd*X*Y)/D
    z=s.cancel(-Bd*D/gdc)
    w=s.cancel(Bc/(Bc-gcd))
    VaB=z*gac+(1-z)*(w*gad+(1-w)*pa*y)
    VbB=z*gbc+(1-z)*(w*gbd+(1-w)*pb*x)
    aa,bb=[s.fraction(s.cancel(e))[0] for e in
            (VaB-(pa-gab)*Y,VbB-(pb-gab)*X)]
    basis=s.groebner((aa,bb),Y,X)
    assert len(basis.polys)==2
    first,last=[p.as_expr() for p in basis.polys]
    pp=s.Poly(first,Y)
    assert pp.degree()==1 and not pp.coeff_monomial(Y).free_symbols
    YY=s.solve(first,Y)[0]
    assert YY.free_symbols<={X}
    P=s.Poly(last,X)
    if name=='cross':
        expected=X*(4*X+1)*(11465*X**5-16931*X**4-55694*X**3
                           +58497*X**2+62199*X+10800)
        assert P.monic()==s.Poly(expected,X).monic()
        assert P.count_roots(0,s.oo)==1 and P.eval(0)==0
    else:
        expected=X*(2*X-1)*(2*X+1)*(3*X+5)*(700*X**4+1448*X**3
                                          +115*X**2-705*X+75)
        assert P.monic()==s.Poly(expected,X).monic()
        assert P.count_roots(0,s.oo)==4 and P.eval(0)==0
        intervals=[(R(2188,19641),R(2617,23492)),(R(1,2),R(1,2)),
                   (R(5164,9823),R(10011,19043))]
        for lo,hi in intervals:assert P.count_roots(lo,hi)==1
        for interval in intervals[1:]:
            assert min(bernstein1(-YY,X,interval))>0
        lo,hi=intervals[0]
        assert R(1,10)<lo<hi<R(1,8)
        assert min(bernstein1(YY-1,X,intervals[0]))>0
        gap01=-2*x-y/10+x*y-Bc
        assert s.cancel(gap01-(-10*X+9*Y-61*X*Y)/(10*D))==0
        assert 9-61*R(1,8)>0 and 9-71*R(1,8)>0
        assert 2*R(1,10)-R(1,10)>0
        assert J[3,1]==R(-1,10) and pb-gab==-2
print('PASS: every proper joint/solo/solo word at K5 fails active equations or a complete cap')

# The formula17 period-four producer: check its entire cubic root selection,
# not merely the former sufficient parameter rectangle N<=2.
z=s.symbols('z')
four=-56*z**3+166*z**2-39*z-21
quad=14*z*z-45*z+21
assert s.expand(four+(4*z+1)*quad)==0
assert s.Poly(four,z).count_roots(0,1)==1
assert quad.subs(z,R(1,2))>0>quad.subs(z,R(4,7))
p=(-8*z*z+30*z-12)/(21+4*z)
scaled_cap=s.cancel(6*p*z+p-R(9,10)*z)
num,den=s.fraction(scaled_cap)
assert den==40*z+210
assert s.rem(num,quad,z)==R(27669,49)*z-R(2322,7)
assert R(27669,49)*R(4,7)-R(2322,7)<0
print('PASS: unique proper-z period-four candidate at M=N5 fails the owner0 joint-row cap')
print('PASS: complete new-calibration checks; compose with parameter-uniform012/013 and full-support proofs')
```

## 9. Scope of the conclusion

The theorem eliminates the entire displayed three-parameter native family,
and all of its positive recipient-scaled copies with nonnegative own levels,
from the surviving uniform-equilibrium counterexample class. It does not
assert that every four-player reward table has this form. The source
construction permits arbitrary time dependence and unrestricted behavioral
deviations; it does not promise a stationary equilibrium or any fixed finite
controller size. Every point in the compact carrier is used only through
actual approximants and continuous finite prefixes. A virtual continuation
is never declared to be actual, and no genuine tail inherits minimum status.

The positive boundary checks are included in the proof itself: the exact
certificates cover M=0, N=0 where their regions apply, N=2, M=4,
M=43/5, N=25/2, and T=0; the two-period construction is proper at its
radical endpoint. Arbitrarily large finite T is treated without a limiting
game, and s_i=0 is permitted by the offset adapter.

A simple negative control explains why the offset restriction cannot be
removed from that adapter. In the all-zero native table, the profile where
owner0 quits surely and the other owners Never is absorbing and exactly
Nash. Subtract1 from every absorbing reward. That same profile now pays
owner0 -1, while its unilateral Never deviation pays0. Thus an absorbing
native equilibrium alone does not imply signed-offset invariance. This
example tests the adapter's direction; it is not a uniform-equilibrium
counterexample and does not alter the stated family theorem.
