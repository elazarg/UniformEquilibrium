# A uniform open reward neighborhood from actual marked-source geometry

## 1. Exact statement

Let I={0,1,2,3}. A quitting game has one live state. At each date every
player privately and independently chooses Continue or Quit. The first
nonempty quitting coalition A selects the absorbing state. That live
action date pays zero; every later absorbed date pays r_i(A) to player i.
The reward is zero while the game is live, including on the path where
nobody ever quits. Every unilateral deviation may
replace the player's entire behavioral strategy.

For M,N,T>=0 define the normalized table Z(M,N,T) below, with its four own
singleton entries zero.

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


**Theorem.** There exists a real epsilon_*>0 with the following property,
uniformly in 0<=M,N<=4 and T>=0. If a finite table Zhat has zero own
singleton entries and

    max_(i,A nonempty) |Zhat_i(A)-Z_i(A;M,N,T)| < epsilon_*,

then the infimum of total full terminal Nash debt over almost-surely
absorbing independent profiles of Zhat is zero. Consequently, for every
vector s in[0,infinity)^4, the original table

    r_i(A)=Zhat_i(A)+s_i

has one uniform-equilibrium payoff. In particular the exact entire parameter
box 0<=M,N<=4,T>=0 is covered.

The conclusion fixes a payoff v before the accuracy: for every eta>0 there
is a behavioral profile and an integer H such that every horizon h>=H has
prescribed average payoff within eta of v in every coordinate and no complete
unilateral behavioral deviation gains more than eta. The profile and H may
depend on eta; v does not.

The radius is uniform in the unbounded parameter T. It need not be computed
numerically for this theorem. The allowed normalized tables form an open
subset of all 56 free normalized reward coordinates. With all s_i>0, their
original tables contain a nonempty open subset of the full 60-dimensional
reward space: the map r -> (r_i(A)-r_i({i}),r_i({i})) is an invertible linear
coordinate change. For example, around r=1+Z(7/2,7/2,0), every raw table
at sup distance less than min(1/2,epsilon_*/3) has positive own levels
and normalized distance less than epsilon_* from that center. This
statement is ordinary mathematics to be formalized; it is not a new checked
Lean theorem.

## 2. Conjecture-facing change and strategic inputs

The mechanism constructs absorbing approximate equilibria from raw reward
tables in an open family where the passive joint rewards can defeat global
marked-cone invariance. Its source restriction is exact independent-law
realizability with complete deviation caps. A conditional tail is used only
after it is extracted from actual approximants; no minimum property is
transferred to a tail.

The following strategic witnesses are produced in the proof:

* Actual compact zero-debt data exist because native AllNever has zero debt.
  A positive least original Never product follows from absorbing repair if
  the desired absorbing debt infimum were positive.
* A finite one-stage Nash root exists at every real continuation by finite
  mixed Nash existence. No selector is supplied or assumed.
* A genuine zero-debt conditional tail is extracted from the least source's
  actual approximants. Its positive Never mass comes from the literal
  first-date survival identity.
* Arbitrarily small finite prefix words at every stalled nonnegative source
  are constructed by a complete finite-face induction. The induction retains
  its marked set, its original signed inequality, and its survival budget.
* The resulting contradiction supplies absorbing profiles at every positive
  error through the definition of the debt infimum. The full terminal
  semantic endpoint then selects one fixed uniform-equilibrium payoff.

No strategic witness remains an input hypothesis. The only restrictions are
on the raw reward table and on the nonnegative original own singleton levels.
The full four-player quitting conjecture remains outside this theorem.
Section 9.3 gives a complete prior-class calibration at M=N=7/2,
including exact absence of every stationary terminal Nash profile for the
original-own-one table; the new existence proof therefore needs time-dependent
behavior. It also separates the entire transformed ten-phase reward cube.

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

It remains to exclude negative-payoff minima. Section 7 supplies the complete
classification for the exact box. It follows with (Repair) that A_Z=0 there.
Section 8 proves that the whole argument persists on one uniform open reward
neighborhood, including the unbounded T direction.

## 7. Complete negative-payoff minimum classification on the passive square

From here assume `0<=M,N<=4` and `T>=0`, with exactly the full table in
Section 1. Keep the actual closed carrier `H`, its zero-debt set `E`, marked
set `C={0,1}`, set `E_C` and Never product `nu` from Section 3.

**Negative-source exclusion.** A point `X` minimizing `nu` on `E_C`, with
`nu(X)>0`, has no negative payoff coordinate.

All statements in this section are about actual closed zero-debt data or
exact Nash roots attached to such data. The tail extracted below need not
minimize anything.

### 7.1 A bad outgoing root fixes the unmarked sign pattern

Assume some coordinate of `u=U(X)` is negative. AllContinue is then not a
Nash root against `u`, since an owner with negative continuation can Quit
alone for zero. Finite normal-form Nash existence supplies a nonzero root.
Any root with an active marked owner has a nonpositive output in that
owner's coordinate, since its entire participant row is nonpositive. Such
a root would prefix `X` to another point of `E_C` with a strictly smaller
Never product. Consequently every root at this hypothetical minimum has
`q0=q1=0` and strictly positive outputs for both marked owners.

For these D-only roots the Quit-minus-Continue gaps of owners 2 and 3 are

    g2=q3-(1-q3)u2,       g3=-2q2-(1-q2)u3.          (11)

A nonzero singleton root gives, at any nonpositive marked input, the output
`(1-q)u_i-q<0`, and so also contradicts minimum status. Both D owners must
therefore be active. Neither can have unit hazard: `q3=1` forces `q2=1`
by `g2=1`, whereas `q2=1` forces `q3=0` by `g3=-2`. They are both proper,
and indifference gives the necessary input pattern and unique D root

    u2=x>0, u3=-y<0,
    q2=y/(2+y), q3=x/(1+x).                         (12)

Its marked output divided by its positive joint survival is

    u_i+K_i xy/2-x-y/2>0,      K0=M, K1=N.         (13)

Since some marked `u_i<=0`, and `M,N<=4`, this implies

    F(x,y):=2xy-x-y/2>0.

Every actual zero-debt point has `u3>=-1` by its literal Never deviation.
Thus

    1/2<y<=1,       x>y/[2(2y-1)]>=1/2.           (14)

These strict implications include `M=0` or `N=0`; no division by a passive
parameter is used.

### 7.2 Extracting an actual incoming root

The incoming construction in Section 4 applies to this `X` without any
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
first-date envelope (2), and the tail satisfies every actual cap restriction
again. Write

    q=(r,t,p,z)=(q0,q1,q2,q3).

At least one marked hazard is positive: if `r=t=0`, then `Q3=p>=0`,
contradicting `U3=-y`. The next cases exhaust all incoming supports.

### 7.3 A genuine forced-123 tradeoff

The following actual-carrier inequality will be used on both the original
point and its genuine tail:

    U0>0, U2>0, U3<-1/10
      imply U3 >= (31/47)U2-323/235.               (15)

It uses only the first-date envelope (2), so it does not require positive
Never mass. Its witness has `r=0`, since every owner0 participant payoff is
nonpositive. The negative `U3` forces `t>0`. If `p=0`, then
`Q3=-t/10>=-1/10`, a contradiction. Hence `p>0`. If `z=0`, the paid
owner2 output would be `Q2=-2t<0`, another contradiction. Thus the witness
has exactly the active set 123 and

    U1=pz-p/10-2z,
    U2=z(4-3t)-2t,
    U3=p(1-3t)-t/10.                              (16)

The same formulas hold whenever an incoming root has support 123, even if
`U0` is not positive. The actual floor `U1>=-1` gives

    z <= (1-p/10)/(2-p) <=9/10.

If `U3<-1/10`, then `t>1/3`; otherwise its formula in (16) is at least
`-1/30`. Consequently

    U2<=18/5-(47/10)t,
    U3>=1-(31/10)t.

Eliminating `t` proves (15). No inequality here is claimed for an arbitrary
virtual continuation or a correlated calendar point.

### 7.4 Both marked owners cannot be paid

Suppose `r,t>0`. Set `H=5-p-z+pz`. The exact paid identities and passive
floor envelope give

    0<=Q0-P0+H0
      =1-2p-z/10-Ht-Mpz-Ttpz,
    0<=Q1-P1+H1
      =1-p/10-2z-Hr-Npz.

Here `H0,H1` denote opponent survival, whereas `H` is the displayed
positive polynomial. Since `M,N,T>=0`, it follows that

    0<=p<=1/2,     t<=9/40,
    r <= R(p):=(1-p/10)/(5-p).                    (17)

For the middle bound use the exact identity

    9H-40(1-2p-z/10)=5(1-z)+p(71+9z)>=0.

For the last bound, the difference between `R(p)` and
`(1-p/10-2z)/H`, multiplied by `(5-p)H`, is
`z(9-9p/10-p^2/10)>=0`.

The complete owner3 forced-Quit polynomial is

    -Q3=2r+t/10-rt-p(1-3r-3t+3rt).

It increases with `r` in the rectangle (17) and is affine in `t`. At its
two relevant endpoints, direct substitution yields

    1/2-(-Q3)|_(r=R(p),t=0)
       =(5+17p-7p^2)/[10(5-p)]>0,
    1/2-(-Q3)|_(r=R(p),t=9/40)
       =(245-400p-37p^2)/[400(5-p)]>0.

The numerator polynomials are positive on `0<=p<=1/2`. Therefore
`U3>=Q3>-1/2`, contradicting (14). This eliminates all supports containing
both 0 and 1, including full support, without any sign premise on `U0,U1`.

### 7.5 Only marked owner1 cannot be paid

Suppose `r=0,t>0`. The same reasoning as in Section 7.3 forces `p,z>0`,
so (16) holds. Now `y>1/2` implies `t>1/3`, and `x>0` implies
`z>2t/(4-3t)>2/9`. Hence

    u1=pz-p/10-2z<=-z<-2/9.

The forced-123 tradeoff bounds `x` above by
`(47/31)(323/235-y)`. Since `2y-1>0`,

    F(x,y) <= -(94/31)y^2+(1607/310)y-323/155
            <=153489/1165600 <2/9.

Thus `u1+Nxy/2-x-y/2<=u1+F(x,y)<0`, contradicting the second strict
inequality (13). No original sign of the other marked coordinate is needed.

### 7.6 Only marked owner0: sole0 or incoming03

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

The first bad-output inequality (13), with `M<=4`, implies

    x(4r-1)>r+z/10.

Thus `r>1/4`, `r<=1/2` by the actual floor, and
`x>r/(4r-1)>=1/2`.

There is an explicit outgoing root candidate with active support 02:

    q0'=x/(x+9/10),    q2'=a/(1+a),    q1'=q3'=0. (18)

Its active owners are exactly indifferent and owner0's output is negative.
After multiplication by the positive denominator `(x+9/10)(1+a)`, the
inactive gaps are

    G1=-4x-(31/10)ax+(81/100)a-(9/10)u1<0,
    G3=(9/10)y-x(1+3a)-(9/5)a.

For `G1<0`, use `u1>=-1`, `x>1/2`, `0<a<1/10`. If `G3<=0`, (18)
is a good root contradicting minimum status. Otherwise `x<(9/5)r`,
which together with the lower bound on `x` implies `r>7/18`.

The genuine zero-debt tail of the incoming03 root has

    v0=(9/10)z/(1-z)>0,
    v3=-r/(1-r)<-1/10,
    v2=[x+r-3z(1-r)]/[(1-r)(1-z)]>0.

The last numerator is at least `z+(9/10)r` by the incoming owner2 cap.
Apply (15) to this actual tail. It gives the lower bound

    z >= (713r+155x-323)/(142+93r),

whereas the incoming owner2 cap gives the upper bound

    z <= (x+r/10)/(4-3r).                          (19)

These bounds are inconsistent. Their lower-minus-upper difference equals

    [21483r^2+5580rx-38068r-4780x+12920]
      /[10(3r-4)(93r+142)].

The denominator is negative. The numerator decreases in `x` on
`7/18<=r<=1/2`. At `x=r/(4r-1)` it equals `P(r)/(4r-1)`, where

    P=85932r^3-168175r^2+84968r-12920.

Its degree-three Bernstein coefficients on `[7/18,1/2]` are

    -9245/36, -496111/972, -112699/108, -6953/4.

They are all negative. The difference in (19) is therefore positive, a
contradiction. Every incoming03 case has now been eliminated.

### 7.7 Incoming023: positivity of a genuine marked tail

The only remaining incoming support is 023. Write its hazards `(r,0,b,c)`,
all three strictly between zero and one. The exact paid outputs are

    x=c(4-3r)-r/10,
    y=2r+b(3r-1),
    a=-u0=2b+c/10-bc>0.                            (20)

The exact actual tail has

    v2=[(9/10)r+c]/[(1-r)(1-c)]>0,
    v3=-(r+2b)/[(1-r)(1-b)],
    v0=[-b+(9/10)c-(M+1)bc]/[(1-b)(1-c)].         (21)

Its actual floor `v3>=-1` implies

    2r+3b-rb<=1.                                  (22)

The bad D-only output0 and `M<=4` give

    D:=4xy-y-2x-2a>0.                             (23)

In particular `y>1/2`, so `r>1/4`: for `r<=1/4`, (20) would give
`y<=2r<=1/2`. Equation (22) gives `r<=1/2`. Also `b<9/50`. To see the
last bound, substitute the maximum possible `r=(1-3b)/(2-b)` into the
increasing function `y(r,b)`. Its difference from `1/2` is

    (16b^2+9b-2)/[2(b-2)].

Thus `y>1/2` forces `16b^2+9b-2<0`. This polynomial is increasing for
`b>=0` and is positive at `9/50`, proving the claim.

We next prove `v0>0`, so that (15) applies to this tail. If `v0<=0`, then
`M<=4` and `b<9/50` imply

    c<=b/(9/10-5b).

Write `D=d0+dc*c`, where direct substitution in (20) gives

    d0=-(6br^2+13br+15b+4r^2+9r)/5<0,
    dc=-(180br^2-300br+70b+120r^2-190r+41)/5.

As `D>0`, necessarily `dc>0`. At the asserted upper bound on `c`,

    D <= S/[5(50b-9)],
    S=1500b^2r^2-3650b^2r-50b^2+1054br^2-2233br
         +545b+36r^2+81r.                          (24)

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
checker below, prove `S>0`. Equation (24) contradicts `D>0`. Therefore
`v0>0`. Moreover `r>1/4` implies `v3<-1/3<-1/10`.

### 7.8 Incoming023: the forced-123 tail is inconsistent with bad funding

All hypotheses of (15) now hold for the genuine tail (21). Multiply that
inequality by `470(1-r)(1-b)(1-c)>0`. The result is

    f0+fc*c>=0,
    f0=646-1395r-1586b+925br,
    fc=-646br+1896b+1116r-956.                     (25)

On the entire rectangle `1/4<=r<=1/2`, `0<=b<=9/50`, the bilinear
polynomial `fc` is strictly negative, as its four corner values show. Hence
`c<=f0/(-fc)`. Recall that `dc>0` follows from `D>0`. We obtain

    D<=d0+dc*f0/(-fc).

The numerator of the right side, multiplied by five, is

    G=-170376b^2r^3+565958b^2r^2-525592b^2r+139460b^2
        +144212br^3-158168br^2-26439br+5466b
        +171864r^3-336350r^2+171331r-26486.         (26)

This polynomial is strictly negative on that rectangle. Its tensor Bernstein
degrees are three in `r` and two in `b`. With `b` in `[0,9/50]`, the
following three subdivisions have the listed largest coefficient:

| r interval | largest coefficient |
|---|---:|
| `[1/4,3/10]` | `-89734/125` |
| `[3/10,2/5]` | `-140297/750` |
| `[2/5,1/2]` | `-96288/125` |

All coefficients are strictly negative, proving `G<0`. Since `-fc>0`,
we have `D<0`, contradicting (23). This eliminates incoming023 and closes
the exhaustive incoming-support classification.


The cases are exhaustive: a negative-payoff marked minimum forces a bad
outgoing root23; its proper actual incoming support contains a marked owner;
the alternatives are both marked, only marked1, sole0, 03, and 023. Each is
excluded. Thus every such minimum has nonnegative payoff. Combining this
with Section 6 and (Repair) proves A_Z=0 for the exact entire box.

## 8. A uniform neighborhood of the entire unbounded family

### 8.1 Stable signs and the nonnegative stratum

For every table within `epsilon<=1/100` of a base table, all marked
nonsingleton participant rewards of owners `C={0,1}` are at most `-9/100`.
Their own singleton rewards remain exactly zero. Their four passive singleton
rewards on `D={2,3}` lie in `[-101/100,-99/100]`. The relevant joining
increments and pair participant rewards satisfy

    c2:=J23-Gamma23 in[98/100,102/100],
    c3:=J32-Gamma32 in[-202/100,-198/100],
    L03,L20 in[88/100,92/100], L02 in[-102/100,-98/100],
    L10 in[-402/100,-398/100],
    L30 in[-102/100,-98/100],
    J02<=-199/100, J20<=-9/100, J21<0, J30<0, J32>0.           (2)

There is uniform small-root invariance of the marked cone
`K_C={u:min(u0,u1)<=0}`. If a marked owner is active, its Nash output is
its nonpositive forced-Quit value. Otherwise only owners 2 and 3 act, and
the absorption contribution of marked owner `i` is

    E_i=Gamma_i2*q2+Gamma_i3*q3
          +(Zhat_i(23)-Gamma_i2-Gamma_i3)q2*q3.

The last coefficient is at most `603/100`. For `max q<=1/16`,
`q2*q3<=(q2+q3)/32`, so

    E_i<=-(99/100-603/3200)(q2+q3)<0

unless both hazards vanish. A nonpositive marked input therefore remains
nonpositive. This statement holds for every real input, however negative;
it does not rely on a bounded continuation box.

At every `u>=0` with `min(u0,u1)=0`, every nonzero Nash root has output
in `K_C`, including sure roots. A marked active owner proves this directly.
If no marked owner is active, the owner3 gap is
`c3*q2-(1-q2)u3`. When `q2>0` it is strictly negative, forcing `q3=0`.
Thus a nonzero D-only root is a singleton root, and at a zero marked
coordinate its output is a strictly negative passive singleton reward
times its positive hazard.

The local face theorem of Section 5 therefore rules out a
positive-Never marked minimum with nonnegative payoff for every sufficiently
close table. Arbitrarily negative continuations do not create a gap in this
step: small-root invariance is global in the continuation, while whole-root
uniqueness is invoked only at the actual nonnegative boundary point.

### 8.2 Uniform passive bounds without uniform Never

For a native table let

    ell_i=min(0,min_(A not containing i) Zhat_i(A)),
    R_i=max(0,max_(A not containing i) Zhat_i(A)).

Every actual cap is at least `ell_i`, by the literal Never response. Also
the own first-Quit/Never decomposition gives the continuous actual inequality

    d_i >= N_i*max(B_i-R_i,0).                     (3)

Indeed the prescribed law is a mixture of finite deadlines, each worth at
most `B_i`, and a Never atom of mass `N_i`, worth at most `R_i`. Subtracting
the prescribed payoff from `B_i`, using `d_i>=0`, proves (3). It passes to
the closed actual carrier.

Consequently every zero-debt carrier point with positive joint Never has

    ell_i<=U_i=B_i<=R_i.                          (4)

For tables at distance at most `epsilon` from the base family, these bounds lie in

    [-1-epsilon,4+epsilon] for owners0,1,
    [-1-epsilon,3+epsilon] for owners2,3.           (5)

They are independent of `T`: its only unbounded reward is a participant
reward, never a passive reward. The same bounds apply to every genuine
zero-debt incoming tail, since its Never product is positive. The positive
Never numbers may tend to zero along a sequence of tables; after using (3)
for each individual zero-debt point, the uniform bounds (5) remain.

### 8.3 A hypothetical sequence of bad minima

Suppose the uniform theorem fails. Choose tables with errors
`epsilon_n->0`, base parameters `M_n,N_n in[0,4]`, `T_n>=0`, and
`A_Zhat_n>0`. For each table, AllNever lies in its compact zero-debt marked
carrier. The absorbing-repair inequality makes the minimum joint Never
positive. Let `X_n` be such a minimum. Section 8.1 excludes the nonnegative
stratum, so `X_n` has a negative payoff coordinate.

Every nonzero root at `X_n` must leave the marked cone. Finite Nash existence
supplies such a root, since AllContinue is not Nash at a negative input.
A marked active owner or a D-only singleton root would be good, so its
active support is exactly 23. By the opposite signs of `c2,c3` in (2),
this root is proper and its input is

    U2=x_n>0, U3=-y_n<0,
    Y2=y_n/(-c3), Y3=x_n/c2                       (6)

where `Y2,Y3` are odds. The hazards are odds
divided by one plus odds. For both marked owners the output numerator is

    U_i+Gamma_i2*y_n/(-c3)+Gamma_i3*x_n/c2
            +Zhat_i(23)*x_n*y_n/[(-c3)c2]>0.       (7)

For at least one marked owner its input is nonpositive. Equation (7) then
forces `Zhat_i(23)>0` and gives the uniform lower bounds

    x_n > (99/100)(98/100)/(401/100)=4851/20050,
    y_n > (99/100)(198/100)/(401/100)=9801/20050.  (8)

Together with (5), these permit a subsequence with bounded payoffs converging
to `u`, `x_n->x`, `y_n->y`, `M_n->M`, `N_n->N`. The limit satisfies

    min(u0,u1)<=0,  0<x<=3,  0<y<=1,
    u_i+K_i xy/2-x-y/2>=0  (i=0,1).               (9)

In particular `F(x,y)=2xy-x-y/2>=0`. Since `x>0`, this forces

    6/11<=y<=1,              x>=1/2.              (10)

For the first bound, `F>=0` implies `x>1/4` and
`y>=2x/(4x-1)>=6/11`, using `x<=3`. Thus negative unmarked payoffs do
not disappear in this compactness limit.

For each `X_n`, extract its genuine proper incoming root and zero-debt tail
as in Section 4. The tail has positive Never, so its payoff `v_n`
also satisfies (5). Extract `q_n->q`, `v_n->v` and a fixed incoming active
support along a subsequence. The root can have sure or zero hazards in the
limit; we do not assert that the limit tail is an actual point of a limiting
game. Only the following continuous necessary identities and inequalities
are used.

All rows except the owner0 grand entry converge to the corresponding base
table. After adding `T_n` to that single entry, the entire bounded completion
converges to `Z(M,N,0)`. Thus all endpoint polynomials converge uniformly
on the hazard cube unless they use this one unbounded term. When both marked
owners are paid, that term has a favorable nonpositive sign and is discarded
before passing to the limit. In every other branch that uses owner0's paid
identity, `q1=0` makes the term exactly zero.

### 8.4 A stable actual forced-123 constraint

We will use the following sequential version of the fixed-table tradeoff.
Let `w_n` be any zero-debt actual-carrier points for these tables, bounded
as in (5), with

    w0_n>0,  w2_n>0,
    lim w2_n>0,  lim w3_n<-1/10.

Their first-date envelope witnesses eventually have active support exactly
123. Strict negativity of owner0's nonsingleton participant row forces
`q0=0`. Negative owner3 payoff forces `q1>0`, since with `q0=q1=0` its
Quit value is `J32*q2>=0`. If `q2=0`, the owner3 Quit value is
`J31*q1>=-1/10-o(1)`, contradicting the strict limiting bound. If `q3=0`,
the paid owner2 value is `J21*q1<0`, also impossible.

After extracting the three hazards, the paid rows1,2,3 and the passive floor
pass to exactly the identities (16) in Section 7.3. Hence their
limits satisfy

    lim w3_n >= (31/47)lim w2_n-323/235.           (11)

The limit of `w0_n` need not be positive: its strict positivity for each
actual point suffices to force the witnesses' owner0 hazards to be zero.
This is relevant when an incoming03 hazard tends to zero. No actual source
or source minimum is postulated for the limiting vector.

### 8.5 Every limiting incoming support is impossible

If both incoming marked hazards vanish for each `n`, the first-date cap
would give `U3_n>=J32*q2>=0`. Thus the fixed support has a marked owner.

#### 8.5.1 Both marked owners paid

The paid and Never-floor identities have errors tending uniformly to zero.
Discard the favorable `-T_n*q1*q2*q3` term from the owner0 equation.
The limits obey precisely the two inequalities of Section 7.4 of this proof, with `M,N>=0`. Thus `p<=1/2`, `t<=9/40`,
`r<=(1-p/10)/(5-p)`, and the same strictly positive Bernstein numerators
give `u3>=Q3>-1/2`. This contradicts `y>=6/11` in (10). Vanishing paid
hazards in the limit do not invalidate the identities: they were paid at
every `n` before the limit was taken.

#### 8.5.2 Only marked owner1 paid

The exact strict signs in (2), and the uniform negative output in (10), force
support 123 for all large `n`, by the argument in Section 8.4. The limiting
paid identities and the actual passive floor give the original tradeoff.
They imply `t>1/3`, `z>2/9` (because `x>=1/2>0`) and `u1<-2/9`.
The exact bound `F(x,y)<=153489/1165600<2/9` contradicts (9).

#### 8.5.3 Sole0 is excluded before any limit

Suppose only owner0 acts in the incoming root. Its active indifference forces
`v0=0`, so the marked output0 is zero. Hold this actual tail fixed and
increase the hazard slightly. The inactive owner2 gap is
`J20*q0-U2<0`. The other inactive gaps have the form
`L_i0*q0-(1-q0)v_i`. At equality their derivatives are
`L_i0/(1-q0)<0` for `i=1,3`, by (2); strict inequalities persist locally.
Owner0 remains indifferent. The resulting root keeps output0 zero and
strictly reduces Never. This contradicts minimum status for each individual
table; no uniform variation radius or limiting properness is required.

If the fixed support contains 0 and 2 but not 3, its paid owner2 value is
`J20*q0<0`, contradicting `U2>0`. The only remaining supports are 03 and
023, with owner1 inactive.

#### 8.5.4 Incoming03 and the alternative02 root

The limits of the paid and inactive cap identities give

    u0=-z/10, y=2r, x>=z(4-3r)-r/10,
    x(4r-1)>=r+z/10,
    r<=1/2, x>=r/(4r-1).

For each perturbed table, put `a_n=-U0_n>0`. The exact candidate outgoing
root02 has hazards

    q0'=x_n/(x_n+L20_n),
    q2'=a_n/(a_n-L02_n).

The denominators are positive, both hazards are proper, and both active
owners are indifferent. Owner0's paid output is `J02*q2'<0`. The inactive
owner1 gap has a strictly negative limit by the fixed-table formula, (5),
`x>=1/2` and `a=z/10<=1/10`. If the inactive owner3 gap were nonpositive,
this would be a good root, contradicting minimum status. Thus its limit is
nonnegative. The exact limiting gap formula yields

    x(1+3a)+(9/5)a<=(9/10)y=(9/5)r,

so `r>=7/18`.

The incoming actual tail satisfies
`v0_n=L03_n*z_n/(1-z_n)>0`. Since the tail is bounded, this identity keeps
`z_n` away from one. The analogous paid owner3 identity, and `r<=1/2`,
give `v3=-r/(1-r)<-1/10`. The owner2 inactive identity gives

    v2=[x+r-3z(1-r)]/[(1-r)(1-z)]>0,

since its numerator is at least `z+(9/10)r>0`. Apply Section 8.4 to these
genuine tails. It gives the same two incompatible bounds (19), now allowing
weak bad-output and failed-alternative inequalities. The strict Bernstein
certificate for `P(r)` remains negative on the closed interval
`[7/18,1/2]`. It therefore contradicts the limit as before. This branch
also covers `z_n->0`: each tail has positive `v0_n` and (11) still applies.

#### 8.5.5 Incoming023

The bounded actual tails and the active owner3 indifference give in the limit

    -(r+2b)=(1-r)(1-b)v3,   v3>=-1.

Thus `2r+3b-rb<=1`. In particular `r<=1/2`, `b<=1/3`, so those incoming
hazards cannot tend to one. The active owner2 identity similarly gives

    (9/10)r+c=(1-r)(1-c)v2,

which rules out `c=1` by boundedness of `v2`. All three rational tail
identities (21) therefore remain valid at the limit, including a possible
zero `b`.

The paid outputs are exactly (20), and (9) gives `D>=0`. The stronger
uniform bound `y>=6/11` ensures `r>1/4`; the floor then gives `r<=1/2`,
and the same increasing-polynomial argument gives `b<9/50`. Also
`d0<0`, so `D>=0` forces `dc>0`.

If the limiting `v0` were nonpositive, the Bernstein certificate (24)
would give `D<0`, a contradiction. This remains strict when `b=0`, since
the normalized floor coordinate `t` is positive. Therefore `v0>0`, and
`v2>0`, `v3<-1/10`. The actual tails have the same strict properties for
all large `n`; Section 8.4 applies and yields (25) in the limit. The final
strict certificate `G<0` again gives `D<0`, contradicting `D>=0`.

All fixed incoming supports have been excluded. The hypothetical sequence
of nearby positive-gap games cannot exist, proving a positive uniform radius.


## 9. Original-game adapter, exact controls, and coverage

### 9.1 Original-game and fixed-target adapter

For every table covered by Section 8 and every epsilon>0, A_Zhat=0 provides
an actual almost-surely absorbing independent profile with total native debt
below epsilon. Hence each player's complete native deviation gain is below
epsilon. For fixed s_i>=0, its prescribed payoff in the original game
r_i(A)=Zhat_i(A)+s_i gains exactly s_i, because absorption is almost sure.
The payoff under any unilateral deviation gains s_i times that deviation's
absorption probability, at most s_i. Its original debt consequently does not
increase. This establishes terminal approximate Nash profiles at every error
against all behavioral replacements. The fixed-target terminal-to-uniform
consumer stated in Section 11 yields the claimed single payoff target before
the accuracy. The live and Never payoffs remain zero throughout this adapter.
Signed offsets are not silently treated as affine invariance.

### 9.2 Positive and negative boundary controls

All exact corners M,N in{0,4}, T=0 are included, as is every T>=0 on each
corner. The proof never divides by M or N and never imposes an upper bound
on T. Its root limits allow every hazard to tend to zero or one; the genuine
tail bounds in Section 8 explicitly exclude only the singular faces whose
indifference identities make them impossible.

The theorem does not require global invariance of the marked cone. At
M=N=4,T=0, the virtual input (0,0,3,-6) and q=(0,0,3/4,3/4) give a Nash
root with output (15/8,15/8,3,3/4). Its two marked gaps are -231/80 and its
two unmarked gaps vanish. Thus both marked outputs are positive although
both marked inputs are zero. This hazard lies outside the small-root
threshold 1/12. The input also violates the actual floor U3>=-1, so it is
not an actual zero-debt source and creates no contradiction.

Another exact source control is the entire actual slice U0=U1=0:
its first-date envelope forces U3>=-1/2, for all M,N,T>=0. Indeed q0>0
forces all other hazards zero by marked participant negativity; then
0=U1>=4q0-1 and U3>=-2q0, proving the bound. If q0=0,q1>0 the same
negativity forces the sole1 support and U3>=-q1/10>=-1/10. If both marked
hazards vanish then U3>=q2>=0. This tests sure and zero hazard faces without
assuming positive Never or source minimality.

The preliminary perturbation radius 1/100 supplies only the sign margins in
Section 8.1. It is not asserted to be the final epsilon_*: the latter also
comes from the strict compactness exclusions. No numerical sampling is used
to infer an open neighborhood.

### 9.3 Complete prior-class calibration

Throughout this calibration set M=N=7/2, T>=0, and r_i(A)=1+Z_i(A).
The complete table is the one in Section 1.

Original own-singleton values are all one. Original AllNever therefore has
full response cap one in every coordinate and is not an equilibrium. Native
AllNever is exact; this difference is retained throughout. Every absorbing
stationary profile with at least two positive hazards has opponent absorption
under every deviation, so adding the own offsets preserves its stationary
Nash comparisons. Singleton and empty supports are checked directly below.

Write `Gamma_ij=Z_i(j)`, `J_ij=Z_i(ij)`, and `L=J-Gamma`, with zero
diagonals. Exact matrices are

    Gamma^-1=(1/15)[2,7,3,3;7,2,3,3;3,3,2,7;3,3,7,2],
    det Gamma=45,
    L=[0,-4,-1,9/10; -4,0,9/10,-1;
       9/10,-1,0,1; -1,9/10,-2,0].

The complete native joining fields at continuation zero are

    g0=L0*q-(9/2)q2*q3-T*q1*q2*q3,
    g1=L1*q-(9/2)q2*q3,  g2=L2*q,  g3=L3*q.       (1)

#### 9.3.1. Every quiet child and every sure-owner punishment selection

For a nonempty proper child S, outsider o, and nonnegative child weights,
the singleton future and joining rows necessarily include, for j in S,

    sum_(i in S) lambda_i*(-Gamma_ij)>=-Gamma_oj,
    sum_(i in S) lambda_i*L_ij>=L_oj.                 (2)

For the following `(S,o,j)`, the joining right side is strictly positive
while all left coefficients are nonpositive:

    (0,2,0),(1,3,1),(2,1,2),(3,0,3),
    (01,2,0),(02,1,2),(03,2,0),(12,3,1),(13,0,3),(23,1,2),
    (012,3,1),(013,2,0),(023,1,2).

For `S=123,o=0`, add future rows j=2,3 and twice joining row j=3.
The resulting left coefficients in order 1,2,3 are `(0,-1,-3)` and
the right side is `19/5`. Thus all fourteen systems fail over their
entire nonnegative weight cones, including versions omitting the Never row.
This excludes recursive quiet lifts at their outermost proper child too.

The entire complementary Nash correspondences with one owner forced sure
are obtained from (1):

| Sure owner | All complementary profiles |
|---|---|
| 0 | (1,0,1,0) |
| 1 | (0,1,t,1), 0<=t<=9/20 |
| 2 | (0,1,1,0) |
| 3 | (0,0,1,1) |

For owner0 sure, row1 is strictly negative, then row3 is strictly negative,
then row2 is positive. For owner1 sure, row0 is strictly negative. With
q0=0, row2 is q3-1; q3<1 would force q2=0 and then q3=1, a contradiction.
Thus q3=1, and row3 gives the displayed interval. For owner2 sure, rows
0,3,1 successively force q0=0,q3=0,q1=1. For owner3 sure, rows1,2,0
force q1=0,q2=1,q0=0. The term containing T strengthens a strict sign or
vanishes. This proves exhaustion on all boundary faces, not a sampled census.

The designated owners' Quit-minus-Continue gaps are

    -1,   -1-(18/5)t,   -1,   -2.                   (3)

Each profile has another sure quitter. The coefficient of every punishment
continuation in that owner's comparison is therefore zero. No punishment
law, including an optimal one, repairs (3). This excludes the complete
singleton-base punishment producer. A larger persistent base satisfying all
its induced Nash, leave and join tests would give a whole root with a sure
owner, also contradicted by the census.

#### 9.3.2. Every block, funding role, trap and weight

For any marked set meeting 23 and any ordered partition into positive-weight
blocks, the first block meeting 23 has strictly positive participant sum
at coalition23. For a marked set contained in01, its disjoint coalition23
has every marked payoff `7/2>0`. Thus all149 ordered-subset/block choices
fail the unboxed criterion, for every positive weighting.

The two-unmarked-player funding theorems can only mark01. Their three block
orders are `01`, `0|1`, and `1|0`; the opposite joining signs force ordered
unmarked pair `(2,3)`, with joining coefficients `1,-2` and both marked
singleton magnitudes one. The exact passive extrema are `3,-1`, giving
the separate threshold `7/3<7/2`.

The actual calendar threshold is exactly `32/11<7/2`, not just a convenient
lower estimate. Every deterministic calendar satisfies

    20u2-41u3<=63+62(u2-m2)-3(u3-m3),  m3>=-1.

On its diagonal this makes reciprocal funding at least32/11. The calendars
with time vectors `(0,0,0,0)`, `(1,0,0,1)`, `(1,1,1,0)`, with weights
`1/4,9/40,21/40`, have diagonal observation `(11/10,-1,11/10,-1)` and
attain32/11. The checker enumerates all150 calendars, including the empty
one. All36 discrete funding/block roles and all their positive weight choices
are exhausted by these forced marked and unmarked selections.

Only owners2,3 have positive participant entries, and23 is the sole premium
trap and greatest premium core. Its joining product is `1*(-2)=-2`, failing
even the weak mixed-pair-trap alternative. At23 every nonzero nonnegative
weight on the trap sees positive inserted values4,1, so the supportwise
upper alternative fails. The boxed-charge theorem requires trap size at
least three. The joining-attractive and mixed-sign triple-core theorems fail
their core-size premise. The core-at-most-two result additionally requires
global nonnegative participant premiums, violated in every row.

Every recipient has a negative participant entry; there is no protected
player. For trap23, testing the global inserted floor at singleton0 gives
strictly negative coefficients `Z2(02)=-1/10,Z3(03)=-2`, so every positive
trap weight fails. Pure23 gives both active Quit premiums positive, directly
falsifying ProductLow. These exclude the common-leaver, protected-support,
weighted-floor and product-low alternatives over their whole choice sets.

For any nonzero nonnegative global weight, coalition01 has native payoff
`(-1,-1,-1,-1)`, ruling out lower ledgers. The sum of inserted singleton
tests0 and1 has recipient coefficients `(-1,-1,-21/10,-21/10)`, ruling
out a global inserted floor. The sum of the four singleton columns is
`(1,1,1,1)`, ruling out an upper ledger. The graph-free H/J-flat,
sink-or-receiver and two-ledger classes require the failed lower ledger;
their proper-flat requirement also fails at trap23.

#### 9.3.3. Pair, triple, cycle and local-neighborhood producers

Every pair has a strictly negative L entry. All three partitions fail the
nonnegative scheduled joining premises of the general two-pair join-cap
and crossed-matching producers. Each partition also has a negative scheduled
participant entry, excluding the nonmatching-positive-passive and bounded-
inverse-corner criteria. Since `Gamma^-1>0`, every column sign in the signed
all-column two-pair theorem is forced positive; it fails the same participant
premise. Every triple contains a negative joining entry, so none satisfies
the six positive joining tests of the triple-singleton collision-box theorem.

The four negative-singleton pairs have participant pair entries `(-2,-1/10)`
or their reverse. Neither orientation has both below the singleton value-1;
the below-singleton and opposite-sign matching-phase classes therefore fail.
For positive-singleton matching01|23, the four participant entries are
`(-1,-1,4,1)`, excluding a common friendly-pair premium and the globally
asymmetric favorable joining inequalities. The negative-pair-funded boundary
requires both members of its positive-singleton pair above their singleton
comparison;01 fails twice and23 fails at owner3. Positive row scaling cannot
alter any of these signs or inequalities.

The solo/joint mixed-positive-passive producer can only use joint `(2,3)`
and anchor0 or1. In its entire proper period-two architecture, let u be the
solo hazard and Y2=q2/(1-q2), Y3=q3/(1-q3) the positive joint odds.
Its equations imply

    Y3^2+(5u-3)Y3+u=0,
    -2Y2^2+(2u-3)Y2+u=0,
    7/2=1/Y2+1/Y3,  0<u<1.

The first discriminant is `25(u-9/25)(u-1)`; hence u<=9/25.
The second equation gives `Y2<u/(3-2u)<=3/19`. The last right side
is greater than19/3, a contradiction. Both quadratic branches are retained.

Both rotating mixed-pair theorems, including the new unordered extension,
require each recipient's forward participant pair premium positive. Rows0,1
have no positive participant pair coordinate, excluding every circular role.
The scalar singular circuit requires two distinct positive participant pairs
sharing one owner;23 is the only positive participant pair, so all its roles
fail as well.

Every participant pair coordinate here is nonzero, excluding the zero-premium
joint-phase criterion, which requires both joint participant premiums to
vanish. The separate radius 1/1000000 reward cube of the global asymmetric
pair construction has positive native participant premiums at both favorite
pairs; the negative pair01 excludes its transformed copies as well.

For a proper positive once-per-owner four-singleton Nash word, consecutive
owners i,j must satisfy `J_ij<=0` and `J_ji<=Gamma_ji`: the earlier owner
has own value zero at the next date, and the later owner has own value zero
immediately after the earlier date. All24 permutations leave only
`2,0,3,1` and its rotations. Write u_i=1-q_i for the Continue probabilities
at those four rows; thus q_i is the Quit hazard. Its four owner equations, in cyclic order, are

    u_i(4-4u_(i+1)+u_(i+1)u_(i+2))-1=0.

Subtracting opposite equations gives a linear system for `u0-u2,u1-u3`
with determinant

    16(1-u1)(1-u2)+u2*u3*(4-u0)*(4-u1)>0.

Thus u0=u2,u1=u3, and the remaining difference makes all four equal.
Their proper root is `(3-sqrt5)/2`. Put `p=(sqrt5-1)/2`. At owner3's
date recipient2's prescribed native value is1+p, but Quit pays4p;
`3p-1>0`. This excludes the whole proper four-singleton producer, including
its implicit-function neighborhoods, without comparing their centers.

The older two-joint/same-pair plus two solo neighborhood also admits an
architecture-level exclusion. Its proof retains all phase singleton floors.
The joint pair's two native participant premiums xi,eta must therefore be
nonnegative, since its values at the first joint phase are xi*y,eta*x with
x,y>0. This forces the pair23. Write `H=-Gamma_ji,L=Gamma_ij` for its
ordered joint pair. Its exact second-joint rates are

    e=eta*x/(H+eta+eta*x),
    f=xi*y/(xi-L+xi*y).

For `(i,j)=(2,3)`, e=x/(x-2)<0. For `(i,j)=(3,2)`, f=y/(y-2)<0.
Thus all24 role choices fail floors or properness. No unspecified local
radius or assumption about all other two-joint strategies is used.

The four-joint fixed rectangle and radius-at-most1/2 neighborhood have
strictly positive participant premiums at both positive-singleton favorite
pairs, while our pair01 has both negative. Singleton-compatible relabeling,
signed row offsets and positive row scaling preserve this obstruction.
The four-phase passive ray requires a common favorite participant reward,
incompatible with `(-1,-1,4,1)` after the singleton comparisons fix scales.
The two passive cap chambers have positive native forward pair premiums
for every owner; rows0,1 again exclude them under every role assignment.

The positive singleton graph is two disjoint reciprocal pairs. Every
reciprocal product is positive, so neither signed four-cycle eigenvalue branch,
directed opposition cycle nor negative-chord Hamiltonian geometry can fit.
There is no directed positive triple or positive Hamiltonian cycle. The
cyclic-child classes with explicit singleton sign premises, the one-joint
diffuse-solo class, repeated solo buffer classes, and their arbitrary-joint-
premium variants require such a cyclic
child or an opposite-sign singleton edge; both are absent. Every proper
triple has a strictly negative active singleton row, precluding a positive
image or nonnegative inverse. Positive two-owner children have negative
outsider rows. Four mutually negative pairs defeat the no-mutually-negative
class. A negative reciprocal principal block has neither standard Q nor
a nonzero homogeneous complementary vector, defeating projective Q-bar.

The full matrix is nevertheless R0 and has degree+1. For singleton active
support, an inactive negative singleton row prevents complementarity. For
pairs, positive pairs have strictly positive active image and negative pairs
strictly negative active image. Every triple has its strictly negative active
row; full support is excluded by invertibility. Thus there is no nonzero
homogeneous complementary vector. The positive inverse and determinant45
give degree+1 by the nonnegative-inverse degree theorem. In particular the
degree-not-one and negative-determinant inverse exits do not apply.

##### 9.3.3.1. Every proper joint-pair/solo/solo exact architecture fails

The full-dimensional cyclic-child theorem produces a literal three-row
exact terminal Nash profile. The following argument excludes its entire
output architecture, independent of any unspecified neighborhood radius.
It also covers every signed row offset and positive row scaling: every opponent-deleted family absorbs geometrically
in a proper three-row word, preserving all such payoff comparisons.

Consider the repeated word A=joint{a,b}, B=solo c, C=solo d. Each of its
four scheduled Quit hazards is strictly between zero and one; all other
hazards at each row are zero. Cyclically rotating the word loses no case. Exact Nash at
the initial date implies Nash at every phase because every phase is reached
with positive probability. Consecutive solo owners require

    J_cd<=0,  J_dc<=Gamma_dc.

Indeed owner c's native value before and after its own date is zero, so its
Quit endpoint at d's date is `J_cd*q_d<=0`. Owner d has zero value at its
own date and immediately after it, so at c's date its policy value is
`Gamma_dc*q_c`, and its immediate Quit value is `J_dc*q_c`. Enumerating
all24 role permutations leaves just six support words, with solo orders

    (c,d)=(0,1),(1,0),(0,3),(1,2),(2,0),(3,1).       (4a)

The first two have joint pair23. The last four are equivalent at the active
equations: order their joint pair so `J_ab=-1/10,J_ba=-2`; c favors a and
d favors b, and all the other relevant singleton comparisons are-1.
The passive joint pair entries in recipients c,d are both-1. The checker
verifies this identification from the literal table, rather than assuming
a global symmetry of the higher rewards.

Let x,y be the joint hazards and z,w the solo hazards. Set

    X=x/(1-x),  Y=y/(1-y),  D=(1+X)(1+Y),
    B_i=[Gamma_ia*X+Gamma_ib*Y+Z_i(ab)*XY]/D
                                         for i=c,d.

The solo indifferences give `U_A,d=0,U_B,c=U_C,c=0`. The joint policy
equation in recipient d and the solo-d policy equation in recipient c
therefore force

    z=-B_d*D/Gamma_dc,  w=B_c/(B_c-Gamma_cd).          (4b)

The second denominator is nonzero in every proper solution since it equals
`-Gamma_cd/(1-w)`. Active joint indifference requires

    V_B,a=(J_ab-Gamma_ab)*Y,
    V_B,b=(J_ba-Gamma_ba)*X,                          (4c)

where for i=a,b the exact next-phase value is

    V_B,i=z*Gamma_ic+(1-z)[w*Gamma_id+(1-w)*Q_i],
    Q_a=J_ab*y,  Q_b=J_ba*x.

Thus all active equations are necessary equations in X,Y alone; no inactive
cap has yet been imposed and no candidate root has been selected.

For each of the four cross-joint roles, (4b) becomes

    z=-XY-X+3Y,  w=(-XY+3X-Y)/(4X+1).

After clearing denominators, (4c) gives

    A=3X^2Y^2-47X^2Y-50X^2-6XY^2+134XY-20X-9Y^2+30Y=0,
    B=5X^2Y^2-6X^2Y-15X^2-12XY^2+40XY-9X-9Y^2+6Y=0.

An exact lexicographic Groebner basis in Y,X has two members. Its first
member is linear in Y with nonzero constant leading coefficient. Its last
member, up to a nonzero constant, is

    X(4X+1)[11465X^5-16931X^4-55694X^3
                         +58497X^2+62199X+10800].     (4d)

The bracketed polynomial has no positive real root. The exact Sturm signs
at0 are `(+,+,-,-,-,-)`, and at positive infinity are
`(+,+,+,+,-,-)`, giving one variation at both endpoints. Equivalently,
the checker counts exactly one distinct root of (4d) in[0,infinity), namely
X=0. Hence no positive X,Y solution exists, without any bounded-hazard
restriction. This rules out all four cross-joint words even before caps.

For the two joint23 words take a=2,b=3. Both passive pair entries equal7/2,
the joint participant entries are4,1, and (4b) becomes

    z=(-7XY+2X+2Y)/6,
    w=(7XY-2X-2Y)/(XY-8X-8Y-6).

The two cleared equations are

    A=35X^2Y^2-3X^2Y-2X^2+26XY^2+18XY-4X-18Y^2+14Y=0,
    B=14X^2Y^2+8X^2Y+12X^2+3XY^2+30XY+14X-2Y^2-4Y=0.

The exact lexicographic basis again has a linear Y member with a nonzero
constant leading coefficient and last member proportional to

    X(9X^2+8X-10)[3836X^5+9716X^4+3955X^3
                              -4538X^2-1950X+300].    (4e)

There are exactly three positive roots, one in each of

    I1=(20658/167377,12211/98937),
    I2=(90066/147331,85291/139520),
    I3=(56043/80117,352826/504387).

Let Y=Y(X) be the polynomial reconstruction from the first basis member.
Exact Bernstein conversion gives `Y<0` throughout I2 and I3, and `Y>1`
throughout I1. Also `1/10<X<1/8` on I1. Every proper solution is therefore
confined to the last inequalities; it is unnecessary to decide whether it
really satisfies all the other active and properness conditions.

For solo order0,1, recipient0's joint-row Quit endpoint is
`Q0=-2x-y/10+xy`, while its policy value is B0. The gain is exactly

    Q0-B0=(-10X+9Y-46XY)/(10D).

Its numerator is `(9-46X)(Y-1)+(9-56X)>0` for X<1/8,Y>1.
For solo order1,0, recipient3's policy value at the solo1 row is-2X
by (4c), while immediate Quit pays-z/10. Its gain is
`2X-z/10>1/10`, using X>1/10 and proper z<1. Thus both remaining words
fail a strict inactive cap. This exhausts all24 role assignments.

The complete symbolic derivation, exact Groebner bases, root counts,
isolators and Bernstein signs are reproduced in Section 10.5.
No grand reward is queried by these prescribed phases or unilateral actions,
so the result holds for every T>=0. This proof excludes the full stated
architecture, including every possible qualitative neighborhood producing
it; it does not claim exclusion of every three-date word with other supports.

#### 9.3.4. Exclusion of the entire ten-phase reward cube

This comparison includes all24 player permutations, arbitrary signed row
offsets, and arbitrary positive row scales permitted by the ten-phase
theorem, including its free grand coordinates. Let epsilon=1/1000000.
In each recipient row the difference between its favorite and a negative
singleton entry is4. In the ten-phase perturbation it lies between
4-2epsilon and4+2epsilon. Consequently any matching positive row scale
lambda lies in

    4/(4+2epsilon)<=lambda<=4/(4-2epsilon).        (4)

The centered singleton signs force preservation of the two favorite pairs.
In the ten-phase center the marked favorite pair has negative participant
premiums and the unmarked favorite pair has positive premiums at least1.
The perturbation cannot reverse these signs. Our negative participant pair01
must therefore be the marked pair. Its passive payoff at the complementary
pair would then have to be at least

    [4/(4+2epsilon)]*(4-2epsilon)>7/2,

contradicting the actual table. This is a quantitative exclusion of the
whole admitted transformed class, not a comparison with one central table.

It persists under independent perturbations of all 56 non-grand coordinates
of our original table by eta=1/1000. The lower scale bound becomes
`(4-2eta)/(4+2epsilon)`; all necessary signs persist, and

    7/2+2eta < [(4-2eta)/(4+2epsilon)]*(4-2epsilon).

This last statement concerns nonadmission by the ten-phase class only;
it is not an assertion that the new actual-source UE theorem covers that
entire perturbation neighborhood.

#### 9.3.5. Complete stationary census at M=N=7/2

All sure hazards are already excluded by Section 9.3.1, independently of the
continuation. At singleton support j, choose the owner i with
`Gamma_ij=-1,J_ij=-1/10`. Its native prescribed eventual payoff is-1,
but immediate Quit pays `-q_j/10>-1`. Thus no singleton support is Nash.
For each pair, active stationary equations force `q_j=Gamma_ij/J_ij`.
Pair01 has ratio-3; pairs02,03,12,13 have a ratio10; pair23 has a ratio3.
No proper pair is possible.

For proper support023, write x=q0,y=q2,z=q3. The third active equation is

    (-3x^2+4x-1)y^2+(x^2-2x+3)y+2x^2-x=0.

At x>=1/2 all terms are nonnegative and the y term is positive. At x<1/2
the left side increases strictly for0<=y<=1; at y=1/20 it equals
`(817x^2-436x+59)/400>0`, whose discriminant is-2716. Hence y<1/20.
The owner0 equation gives

    M=(1-2y)/z+(11/10-y-1/(10y))*z+3y-41/10+1/y.

Its right side decreases strictly in z>0, so z<1 implies
`M>9/(10y)-2>16`, contradicting M=7/2.

For support123, put x=q1,y=q2,z=q3. The exact stationary equations are

    F1=(1-y)(1-z)(-y-20z+10yz)-9y+10z+45yz,
    F2=(-3x^2+7x-4)z^2+(x^2-5x+3)z+2x^2-x,
    F3=(-30x^2+40x-10)y^2+(29x^2-39x+30)y+x^2-10x.

The exact lexicographic Groebner basis in z,y,x has a linear polynomial
in z, one linear in y, each with nonzero constant leading coefficient,
and x times a degree14 polynomial. In descending order its coefficients are

    21875610794400,-208894142007378,898794148815507,
    -2317321487877947,4039564082194831,-5124193299946159,
    4986219266400074,-3850284715402636,2379776730698788,
    -1156909704350680,426710349445200,-113688686724000,
    20429862400000,-2200944000000,106848000000.

It has exactly three roots in(0,1), isolated respectively in

    (9787/36899,2289/8630),
    (10509/35300,2504/8411),
    (9789/12058,12274/15119).

Reconstruction gives polynomials y=Y(x),z=Z(x). Every Bernstein coefficient
of Y-1 on the first two intervals exceeds respectively6667/500 and26783/1000;
every coefficient of -Z on the third exceeds539/250. Thus all three candidates
violate properness. Exact root counting and Bernstein conversion are performed
by the complete checker, not inferred from decimal approximations.

For012 put x=q0,y=q1,z=q2. Its Quit and joining vectors are

    Q=(-3yz-y-2z, -(30xz+10x+z)/10, (10xy-x-20y)/10),
    Delta=(-4y-z, -(40x-9z)/10, (9x-10y)/10).

For013 use x=q0,y=q1,z=q3, obtaining

    Q=(-(30yz+10y+z)/10, -3xz-x-2z, (10xy-20x-y)/10),
    Delta=(-(40y-9z)/10, -4x-z, -(10x-9y)/10).

Form `H_i Q_i-Delta_i=0` in each case. Each lexicographic basis has linear
z and y polynomials with nonzero constant leading coefficients and a final
degree16 polynomial. Besides x=0 it has exactly one root in[0,1]. For012
the root is in `(1436/6341,4397/19416)` and every Bernstein coefficient
of -Y is greater than2927/10000. For013 the root lies in
`(7231/7265,13824/13889)` and every coefficient of Y-1 exceeds133/1250.
Thus y<0 or y>1. These equations are independent of M,N,T.

For full proper support, the following direct polynomial certificate applies. Nash and literal Never
give every native U_i>=-1. Active indifference gives U_i=Q_i and
`H_i Q_i=Delta_i`. With q=(r,t,p,z) and K=5-p-z+pz, the marked rows imply

    Kt<=1-2p-z/10,  Kr<=1-p/10-2z,
    p,z<=1/2,  r,t<=9/40.

Let S=sum_i(H_i Q_i-Delta_i). The raw-table identity is

    S(M,N,T)=S(0,0,0)
      +Mpz(1-tH0)+Npz(1-rH1)+Ttpz(1-H0).

The parameter terms are nonnegative. Six rational rectangles partition the
necessary box, and all 81 tensor Bernstein coefficients of
`S(0,0,0)-(r+t+p+z)/100` are nonnegative on each. Their respective minima
are `2497/128000,3899/64000,253/800,0,349/51200,3553/512000`.

| r interval | t interval | p interval | z interval | Minimum coefficient |
|---|---|---|---|---:|
| `[9/80,9/40]` | `[0,9/40]` | `[0,1/2]` | `[0,1/2]` | `2497/128000` |
| `[0,9/80]` | `[9/80,9/40]` | `[0,1/2]` | `[0,1/2]` | `3899/64000` |
| `[0,9/80]` | `[0,9/80]` | `[1/4,1/2]` | `[0,1/2]` | `253/800` |
| `[0,9/80]` | `[0,9/80]` | `[0,1/4]` | `[0,1/4]` | `0` |
| `[9/160,9/80]` | `[0,9/80]` | `[0,1/4]` | `[1/4,1/2]` | `349/51200` |
| `[0,9/160]` | `[0,9/80]` | `[0,1/4]` | `[1/4,1/2]` | `3553/512000` |

Thus S>0 at any proper full-support point, contradicting all four stationary
equations. The complete polynomial reconstruction and486 coefficient tests
are reproduced by the complete program in Section 10.4. The finite algebra
certificate includes the full table and all polynomial operations.

This exhausts every absorbing stationary support. Original empty support
fails the own-one deviation. Consequently the original finite table has no
stationary exact terminal Nash equilibrium for any T>=0.

In particular this excludes, table by table, every prior theorem whose
conclusion produces such a stationary profile, regardless of its unspecified
threshold or neighborhood radius. It includes the positive-inverse coalition
jackpot, signed single-column jackpot, signed passive-coalition and raw
three-passive-pole theorems; the positive-passive three-owner stationary
theorem; and implemented stationary face, pure exit, interval blocker,
participant-only, strict-blocker and local-branch producers. The passing
pole guard role is not silently discarded: among all24 roles exactly
`(1,3,0,2)` passes all eight preliminary guards, with c=9/40 and remaining
six guards

    (-1,-5,-89/40,-53/40,3519/16000,-319/400).

The stationary obstruction proves the calibration lies outside the theorem's
eventual producing region even for that role. Unlike the old family-level
ray comparison, this is exact finite-table noncoverage.

##### 9.3.5.1. A positive gap for every stationary profile of each fixed table

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

#### 9.3.6. Inventory and source audit

The comparisons above group all accepted raw existence families by their
actual necessary hypotheses or produced architecture. The group names below identify raw sufficient criteria or the architectures
constructed by them; the necessary conditions and exact exclusions are
spelled out above.

| Group | Accepted producers and exclusion |
|---|---|
| Quiet | Nonnegative singleton finite quiet lifts: all14 child weight systems fail. |
| Participant/trap | Common leaver with signed premiums; support-specific leavers; weighted floor return; mixed premium traps; mixed support upper or charge; boxed Nash charges; premium core at most two; joining-attractive triple core; mixed-sign triple premium core: Section 9.3.2's complete trap, floor and cone obstructions. |
| Marked | Ordered nonpositive anchor blocks; passive bounds; calendar polytope: all149 block choices and all36 funding roles in Section 9.3.2. |
| Ledgers | Graph-free H/J-flat Fin4; sink-or-receiver cap chamber; two-ledger proper-support chamber: failed lower ledger and trap23. |
| Pair phases | Two-pair join cap; crossed matching; nonmatching positive passive pair; bounded inverse corners; signed inverse column; zero-premium joint phase; negative-passive paired phase; below-singleton joint phase; opposite-sign matching phase; global asymmetric pair phase; negative-pair-funded boundary: Section 9.3.3, every partition and role. |
| Solo/joint | Mixed-pair positive-passive: both possible anchor roles fail the entire quadratic architecture. |
| Rotating | Rotating mixed-premium pairs and unordered rotating mixed pairs: rows0,1 have no positive forward participant pair. |
| Triple/singleton | Triple-singleton collision box: every triple has a negative joining entry. |
| Cyclic child | Cyclic child with one joint phase; negative-premium cyclic child; global two-joint cyclic child; one joint phase with diffuse solo exits; repeated solo exit with positive outsider buffer; two outsider buffers with a repeated solo exit: no cyclic singleton triple. The full-dimensional cyclic-child qualitative neighborhood is excluded by the complete three-row architecture proof in Section 9.3.3.1. |
| Attached pair | Attached negative pair complementary solo; joint negative pair two solo; arbitrary one joint premium; both joint premiums arbitrary: required opposite-sign singleton edge absent. |
| Singleton geometry | Nonpositive reciprocal singleton products; no mutually negative singleton pair; negative-chord Hamiltonian; larger-eigenvalue signed four-cycle: strict reciprocal products and four negative pairs exclude every relabeling. |
| Local phases | Four singleton phases; two joint phases full-table neighborhood; four joint phases; four-joint rectangle; four-phase passive reward ray; scalar singular circuit: architecture or literal sign exclusions in Section 9.3.3. |
| Cap chambers | Passive triple cap chamber and monotone passive cap chamber: positive forward participant pair missing in rows0,1. |
| Stationary | Positive-inverse coalition jackpots; signed single-column jackpot; signed passive-coalition rewards; raw endpoint three passive poles; three-owner joint positive-passive triple: complete census in Section 9.3.5. |
| Ten phases | Entire ten-phase middle reward cube, including all its allowed affine/relabelled copies and free grand rows: Section 9.3.4. |

The quiet rows are the exact rows in declarations `rawChild_future_delta`,
`rawChild_future_base`, `rawChild_joining_delta`, `rawChild_joining_base`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`
and `nonempty_cappedClockParentRewardCertificate_iff` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExactLPAlternative.lean`.
The punishment coefficient and full leave/join inputs are expressed by
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
and `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.

The actual singleton geometry and degree hypotheses are expressed by
`SignedFourCycleSingletonData` and `StrictTests` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`,
`targetValue_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleCertificate.lean`,
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`, and
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`.
The inverse theorem requires negative determinant; our determinant is positive.
No stationary completeness is inferred from the terminal semantic endpoint
in Section 11; the complete stationary exclusion was proved directly above.

Exact source correspondence and script checks do not constitute a new Lean
proof. Results which constrain actual positive-gap sources, or compile
already supplied periodic/return/root data, are not earlier unconditional
reward-class producers. This audit does not claim nonexistence of arbitrary
periodic profiles, all finite words, or unrestricted equilibria. The new UE
proof itself shows that those broader negative claims would be false.



## 10. Exact reproducible polynomial certificates

The following complete Python program uses SymPy for exact rational symbolic
arithmetic. Save it as a Python file and run it with Python 3 and SymPy
installed. It reconstructs all 60 rewards, proves the displayed identities,
checks every tensor Bernstein certificate, and checks the uniform sign and
limit margins. It has no input file or random search. The elementary
Bernstein identity is: after an affine substitution to[0,1]^d, a polynomial
sum_k a_k x^k of coordinate degrees n has tensor coefficient

    beta_i=sum_(k<=i) a_k product_j binom(i_j,k_j)/binom(n_j,k_j).

The tensor Bernstein basis is nonnegative and sums to one. Thus strict signs
of all coefficients prove the corresponding strict polynomial signs; a sole
zero corner coefficient gives positivity off that corner as used in (24).
The program checks finite algebraic certificates. The infinite-law,
compactness, and local-induction arguments are the mathematical proofs above.

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

R = s.Rational
e = R(1, 100)

# A convenient preliminary sign neighborhood; it is not the final radius.
assert -R(1, 10)+e == -R(9, 100) < 0
assert 1-2*e == R(98, 100) > 0
assert -2+2*e == -R(198, 100) < 0
for coefficient in (R(9, 10),):
    assert coefficient-2*e > 0
for coefficient in (-4, -1):
    assert coefficient+2*e < 0
assert -R(1, 10)+e < 0 and -2+e < 0 and 1-e > 0
small_margin = 1-e-(6+3*e)/32
assert small_margin == R(513, 640) > 0

# Passive row extrema are independent of unbounded T and uniform in M,N.
for i in range(4):
    passive = [v[i] for A, v in Z.items() if i not in A]
    assert all(T not in s.sympify(v).free_symbols for v in passive)
    extrema = [s.sympify(v).subs({M: m, N: n})
               for v in passive for m in (0, 4) for n in (0, 4)]
    assert min(extrema) == -1
    assert max(extrema) == (4 if i < 2 else 3)

assert (1-e)*(1-2*e)/(4+e) == R(4851, 20050) > 0
assert (1-e)*(2-2*e)/(4+e) == R(9801, 20050) > 0

# At the limit F>=0 and x<=3 force y>=6/11, strictly beyond1/2.
x = s.symbols('x')
assert s.cancel(2*x/(4*x-1)-R(6, 11)+2*(x-3)/(11*(4*x-1))) == 0
assert R(6, 11) > R(1, 2)

# The incoming03 alternative's inactive owner1 gap stays uniformly strict.
assert -4*R(1, 2)+R(81, 100)*R(1, 10)+R(9, 10) == -R(1019, 1000) < 0
assert R(153489, 1165600) < R(2, 9)
assert max(bc03) < 0
assert min(mins[1:]) > 0
assert max(maxs) < 0

# The unbounded T term vanishes identically when owner1 is inactive.
assert s.diff(Q[0], T) == -p*t*z
assert s.diff(P[0], T) == 0
assert s.diff(Q[0], T).subs(t, 0) == 0
for i in (1, 2, 3):
    assert s.diff(Q[i], T) == s.diff(P[i], T) == 0

print('PASS: uniform raw sign neighborhood and continuation-independent small-root invariance.')
print('PASS: bounded passive source/tail boxes, positive bad-funding limits and strict certificates.')
print('PASS: unbounded T is favorable in the both-marked case and absent in every other used branch.')


# Large-root failure of global marked invariance, at an unrealizable input.
qc = (0, 0, R(3, 4), R(3, 4))
pc, qc_pay, hc = endpoints(qc)
uc = (0, 0, 3, -6)
ac = s.prod(1-v for v in qc)
for i in range(4):
    gc = (qc_pay[i]-pc[i]-hc[i]*uc[i]).subs({M: 4, N: 4, T: 0})
    assert gc == (-R(231, 80) if i < 2 else 0)
    out = (qc[i]*qc_pay[i]+(1-qc[i])*pc[i]+ac*uc[i]).subs({M: 4, N: 4, T: 0})
    assert out == (R(15, 8), R(15, 8), 3, R(3, 4))[i]
print('PASS: exact large-root control; global marked invariance is not assumed.')

```


### 10.2 Complete finite-selector and transformed-class check

Run this independent complete Python program with SymPy. It reconstructs the
original-own-one calibration and enumerates every finite choice set claimed
in Section 9.3. Infinite weight choices are excluded by the exact dual rows
and sign arguments in that section.

```python
from itertools import combinations, permutations, product
import sympy as s

I = tuple(range(4))
T = s.symbols('T', nonnegative=True)
q = s.symbols('q0:4', nonnegative=True)
R = s.Rational
K = R(7,2)
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
print('PASS: all weighted-block roles; true calendar32/11 and passive-extrema7/3 both fail K7/2')

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
# anchor0 or1. Its actual quadratic architecture forces K>19/3>4.
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
# have to be at least lamlo*(4-2eps), impossible at K=7/2.
assert K < lamlo*(4-2*eps)
# This exclusion even holds on an independent56-coordinate neighborhood
# of radius1/1000, with ALL grand coordinates ignored.
eta=R(1,1000)
robust_lamlo=(4-2*eta)/(4+2*eps)
robust_lamhi=(4+2*eta)/(4-2*eps)
assert 1-2*eta>0 and 3-2*eta>0
assert -1+2*eta<0<robust_lamlo*(1-2*eps)
assert K+2*eta<robust_lamlo*(4-2*eps)
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

```

### 10.3 Complete proper triple stationary check

This independent program reconstructs all three-owner stationary equations
from the literal table. Groebner elimination retains every real branch;
exact root counts and rational Bernstein bounds exclude all proper roots.
The support023 argument additionally uses its displayed monotonicity proof.
No numerical root finder or floating-point sign is used.

```python
import sympy as s
from itertools import product
R=s.Rational
M,N,T=s.symbols('M N T', nonnegative=True)
x,y,z,t=s.symbols('x y z t')
reward={
 (0,):(0,3,-1,-1), (1,):(3,0,-1,-1), (2,):(-1,-1,0,3), (3,):(-1,-1,3,0),
 (0,1):(-1,-1,-1,-1), (0,2):(-2,-1,-R(1,10),-1),
 (0,3):(-R(1,10),-1,-1,-2), (1,2):(-1,-R(1,10),-2,-1),
 (1,3):(-1,-2,-1,-R(1,10)), (2,3):(M,N,4,1),
 (0,1,2):(-6,-R(41,10),-R(11,10),-1),
 (0,1,3):(-R(41,10),-6,-1,-R(11,10)),
 (0,2,3):(-R(11,10),-1,R(9,10),-4),
 (1,2,3):(-1,-R(11,10),-1,-R(21,10)),
 (0,1,2,3):(-M-T-R(61,10),-N-R(61,10),-R(1,10),-R(31,10))}
def residuals(S):
 q=dict(zip(S,(x,y,z)))
 out=[]
 for i in S:
  opp=[j for j in S if j!=i]
  Q=P=0
  for bits in product((0,1),repeat=2):
   A=tuple(j for j,bit in zip(opp,bits) if bit)
   mass=s.prod(q[j] if bit else 1-q[j] for j,bit in zip(opp,bits))
   Q+=mass*reward[tuple(sorted(A+(i,)))][i]
   P+=mass*(reward[A][i] if A else 0)
  H=s.prod(1-q[j] for j in opp)
  out.append(s.expand(H*Q-Q+P))
 return out
#023 exact third equation and M-threshold.
f023=residuals((0,2,3))
F=(-3*x*x+4*x-1)*y*y+(x*x-2*x+3)*y+2*x*x-x
assert s.expand(f023[2]-F)==0
assert s.expand(-3*x*x+4*x-1+(x-1)*(3*x-1))==0
assert s.expand(F.subs(y,R(1,20))-(817*x*x-436*x+59)/400)==0
assert s.discriminant(817*x*x-436*x+59,x)==-2716
assert s.expand(s.diff(F,y).subs(y,1)-(-5*x*x+6*x+1))==0
# For 0<x<1/2, derivative is positive: if its y coefficient is negative,
# its minimum is -5x^2+6x+1>=1; otherwise the y=0 value is (x-1)^2+2.
assert s.expand(s.diff(F,y).subs(y,0)-((x-1)**2+2))==0
mexpr=(1-2*y)/z+(R(11,10)-y-1/(10*y))*z+3*y-R(41,10)+1/y
assert s.cancel(f023[0].subs(M,mexpr))==0
assert s.cancel(mexpr.subs(z,1)-(R(9,10)/y-2))==0
assert R(9,10)/R(1,20)-2==16
print('PASS: support023 necessary equations force M>16.')

parameter_N=N
N=R(7,2)
x,y,z,t=s.symbols('x y z t')
F3=(-30*x*x+40*x-10)*y*y+(29*x*x-39*x+30)*y+x*x-10*x
F2=(-3*x*x+7*x-4)*z*z+(x*x-5*x+3)*z+2*x*x-x
F1=s.expand((1-y)*(1-z)*(-y-20*z+10*y*z)-9*y+10*z+10*(N+1)*y*z)
# Literal stationary endpoint derivation; own1 hazard=x, own2=y, own3=z.
Q1=-y/s.Integer(10)-2*z+y*z;Q2=-2*x+4*z-3*x*z;Q3=-x/s.Integer(10)+y-3*x*y
assert s.expand(10*((1-y)*(1-z)*Q1-(s.Rational(9,10)*y-z-(N+1)*y*z)))==F1
assert s.expand((1-x)*(1-z)*Q2-(-x+z)-F2)==0
assert s.expand(10*((1-x)*(1-y)*Q3-(s.Rational(9,10)*x-2*y))-F3)==0
literal=residuals((1,2,3))
for actual,claimed,factor in zip(literal,(F1,F2,F3),(10,1,10)):
 assert s.expand(factor*actual.subs(parameter_N,N)-claimed)==0
G=s.groebner([F1,F2,F3],z,y,x)
assert len(G.polys)==3
P=s.Poly(G.polys[-1].as_expr(),x)
assert P.degree()==15 and P.eval(0)==0 and P.eval(1)!=0
quoted=[21875610794400,-208894142007378,898794148815507,
 -2317321487877947,4039564082194831,-5124193299946159,4986219266400074,
 -3850284715402636,2379776730698788,-1156909704350680,426710349445200,
 -113688686724000,20429862400000,-2200944000000,106848000000]
assert s.Poly(P.as_expr()/x,x).monic()==s.Poly.from_list(quoted,x).monic()
assert P.count_roots(0,1)==4 # includes the endpoint root x=0
Z=s.solve(G.polys[0].as_expr(),z);Y=s.solve(G.polys[1].as_expr(),y)
assert len(Z)==len(Y)==1 and Z[0].free_symbols <= {x} and Y[0].free_symbols <= {x}
assert s.Poly(G.polys[0].as_expr(),z).degree()==1
assert s.Poly(G.polys[1].as_expr(),y).degree()==1
assert not s.Poly(G.polys[0].as_expr(),z).coeff_monomial(z).free_symbols
assert not s.Poly(G.polys[1].as_expr(),y).coeff_monomial(y).free_symbols

def bernstein(poly,l,h):
 pp=s.Poly(s.expand(poly.subs(x,l+(h-l)*t)),t);d=pp.degree()
 return [sum(pp.nth(j)*s.binomial(k,j)/s.binomial(d,j) for j in range(k+1)) for k in range(d+1)]
isolators=[(R(9787,36899),R(2289,8630)),(R(10509,35300),R(2504,8411)),
           (R(9789,12058),R(12274,15119))]
assert all(P.count_roots(l,h)==1 for l,h in isolators)
intervals=[(I,1) for I in isolators]
for k,((l,h),m) in enumerate(intervals):
 test=Y[0]-1 if k<2 else -Z[0]
 cs=bernstein(test,l,h);assert min(cs)>0
 print('proper-x interval',l,h,'fails', 'y<1' if k<2 else 'z>0','margin>',s.floor(min(cs)*1000)/1000)
print(f'PASS: all proper stationary123 active equations at N={N} excluded; arbitrary M,T irrelevant.')

def bernstein(poly,l,h):
 pp=s.Poly(s.expand(poly.subs(x,l+(h-l)*t)),t);d=pp.degree()
 return [sum(pp.nth(j)*s.binomial(k,j)/s.binomial(d,j) for j in range(k+1)) for k in range(d+1)]
for S in [(0,1,2),(0,1,3)]:
 F=[s.together(f).as_numer_denom()[0] for f in residuals(S)]
 gb=s.groebner(F,z,y,x);assert len(gb.polys)==3
 P=s.Poly(gb.polys[-1].as_expr(),x);Y=s.solve(gb.polys[1].as_expr(),y)[0];Z=s.solve(gb.polys[0].as_expr(),z)[0]
 assert Y.free_symbols<={x} and Z.free_symbols<={x}
 for k,var in [(0,z),(1,y)]:
  pp=s.Poly(gb.polys[k].as_expr(),var);assert pp.degree()==1 and not pp.coeff_monomial(var).free_symbols
 assert P.count_roots(0,1)==2 and P.eval(0)==0 and P.eval(1)!=0
 I=((R(1436,6341),R(4397,19416)) if S==(0,1,2)
    else (R(7231,7265),R(13824,13889)))
 assert P.count_roots(*I)==1
 intervals=[(I,1)]
 (l,h),m=intervals[0];test=-Y if S==(0,1,2) else Y-1
 b=bernstein(test,l,h);assert min(b)>0
 print(S,'interval',l,h,'fails', 'y>0' if S==(0,1,2) else 'y<1','margin>',s.floor(min(b)*10000)/10000)
print('PASS: proper stationary012 and013 impossible for every M,N,T; ordinary exact proof.')

```

### 10.4 Complete full-support stationary check

This independent program uses only Python's standard library. It rebuilds
the residual polynomial and every one of the 486 rational tensor Bernstein
coefficients in the six rectangles of Section 9.3.5.

```python
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


### 10.5 Complete proper joint-pair/solo/solo architecture check

This independent exact SymPy program enumerates all role assignments,
reconstructs the active equations, counts every positive elimination root,
and checks the strict inactive cap which defeats every surviving candidate.
All reward entries it uses are literal entries of the table in Section 1.

```python
from itertools import permutations
import sympy as s

R = s.Rational
I = tuple(range(4))
X, Y, t = s.symbols('X Y t')
Gamma = s.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
                  [-1, -1, 0, 3], [-1, -1, 3, 0]])
pair = {
    frozenset((0, 1)): (-1, -1, -1, -1),
    frozenset((0, 2)): (-2, -1, R(-1, 10), -1),
    frozenset((0, 3)): (R(-1, 10), -1, -1, -2),
    frozenset((1, 2)): (-1, R(-1, 10), -2, -1),
    frozenset((1, 3)): (-1, -2, -1, R(-1, 10)),
    frozenset((2, 3)): (R(7, 2), R(7, 2), 4, 1),
}
J = s.Matrix([[0 if i == j else pair[frozenset((i, j))][i]
               for j in I] for i in I])
roles = [(a, b, c, d) for a, b, c, d in permutations(I)
         if a < b and J[c, d] <= 0 and J[d, c] <= Gamma[d, c]]
assert len(roles) == 6
assert {(c, d) for a, b, c, d in roles} == {
    (0, 1), (1, 0), (0, 3), (1, 2), (2, 0), (3, 1)}

systems = {}
for a, b, c, d in roles:
    if {a, b} != {2, 3} and J[a, b] != R(-1, 10):
        a, b = b, a
    name = 'positive' if (a, b) == (2, 3) else 'cross'
    data = (Gamma[a, b], Gamma[a, c], Gamma[a, d],
            Gamma[b, c], Gamma[b, d], Gamma[c, d], Gamma[d, c],
            J[a, b], J[b, a], pair[frozenset((a, b))][c],
            pair[frozenset((a, b))][d])
    expected = ((3, -1, -1, -1, -1, 3, 3, 4, 1, R(7, 2), R(7, 2))
                if name == 'positive' else
                (-1, 3, -1, -1, 3, -1, -1, R(-1, 10), -2, -1, -1))
    assert data == expected
    systems[name] = data


def bernstein(poly, interval):
    lo, hi = interval
    pp = s.Poly(s.expand(poly.subs(X, lo + (hi - lo)*t)), t)
    degree = pp.degree()
    return [sum(pp.nth(j)*s.binomial(k, j)/s.binomial(degree, j)
                for j in range(k + 1)) for k in range(degree + 1)]


for name, data in systems.items():
    gab, gac, gad, gbc, gbd, gcd, gdc, pa, pb, kc, kd = data
    x, y = X/(1+X), Y/(1+Y)
    D = (1+X)*(1+Y)
    Bc = (gac*X+gbc*Y+kc*X*Y)/D
    Bd = (gad*X+gbd*Y+kd*X*Y)/D
    z = s.cancel(-Bd*D/gdc)
    w = s.cancel(Bc/(Bc-gcd))
    VaB = z*gac+(1-z)*(w*gad+(1-w)*pa*y)
    VbB = z*gbc+(1-z)*(w*gbd+(1-w)*pb*x)
    Ea = s.factor(VaB-(pa-gab)*Y)
    Eb = s.factor(VbB-(pb-gab)*X)
    F, G = [s.fraction(s.cancel(e))[0] for e in (Ea, Eb)]
    basis = s.groebner((F, G), Y, X)
    assert len(basis.polys) == 2
    first, last = [p.as_expr() for p in basis.polys]
    assert s.Poly(first, Y).degree() == 1
    assert not s.Poly(first, Y).coeff_monomial(Y).free_symbols
    YY = s.solve(first, Y)[0]
    assert YY.free_symbols <= {X}
    P = s.Poly(last, X)
    if name == 'cross':
        expected = X*(4*X+1)*(11465*X**5-16931*X**4-55694*X**3
                              +58497*X**2+62199*X+10800)
        assert P.monic() == s.Poly(expected, X).monic()
        assert P.eval(0) == 0 and s.diff(P.as_expr(), X).subs(X, 0) != 0
        assert P.count_roots(0, s.oo) == 1  # Exactly the endpoint X=0.
        print('PASS: all four cross-joint roles have no positive active root.')
    else:
        expected = X*(9*X**2+8*X-10)*(3836*X**5+9716*X**4
                         +3955*X**3-4538*X**2-1950*X+300)
        assert P.monic() == s.Poly(expected, X).monic()
        assert P.count_roots(0, s.oo) == 4  # Endpoint zero plus three positives.
        intervals = [(R(20658, 167377), R(12211, 98937)),
                     (R(90066, 147331), R(85291, 139520)),
                     (R(56043, 80117), R(352826, 504387))]
        assert all(P.count_roots(lo, hi) == 1 for lo, hi in intervals)
        assert all(0 < lo < hi for lo, hi in intervals)
        assert all(intervals[k][1] < intervals[k+1][0] for k in range(2))
        for interval in intervals[1:]:
            assert min(bernstein(-YY, interval)) > 0
        lo, hi = intervals[0]
        assert R(1, 10) < lo < hi < R(1, 8)
        assert min(bernstein(YY-1, intervals[0])) > 0
        # For solo order0,1, owner0's joint-row Quit minus policy gain is
        # [-10X+9Y-46XY]/[10(1+X)(1+Y)]. Its numerator is
        # (9-46X)(Y-1)+(9-56X)>0 at X<1/8,Y>1.
        Q0 = -2*x-y/10+x*y
        gap01 = s.factor(Q0-Bc)
        assert s.cancel(gap01-(-10*X+9*Y-46*X*Y)/(10*D)) == 0
        assert 9-46*R(1, 8) > 0 and 9-56*R(1, 8) > 0
        # For solo order1,0, owner3's solo1-row gain is2X-z/10>0,
        # using X>1/10 and proper z<1.
        assert 2*R(1, 10)-R(1, 10) > 0
        assert J[3, 1] == R(-1, 10) and pb-gab == -2
        print('PASS: all three positive roots counted; two have Y<0;')
        print('the remaining root fails an explicit cap for BOTH anchor orders.')

print('PASS: all24 proper joint-pair/solo/solo role assignments excluded; T never queried.')

```

## 11. Source correspondence and Lean handoff

The stage timing and Boolean action model are defined by `quittingGame` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`: a
live state pays zero and transitions to the selected absorbing coalition;
only later absorbed dates pay its reward.

The semantic target is `quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean`. It is a proposition
definition, not a proof of arbitrary-game existence.

The following existing declarations give the precise interfaces consumed:

* `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
  `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
  in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`
  identify an independent complete law profile's terminal payoff and full
  law-replacement cap with the behavioral model. They justify the probability
  and deviation semantics of Sections 3 and 4, including literal Never.
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies exact mixed
  one-stage Nash existence for every real continuation. Roots on all faces,
  including sure actions, are allowed.
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean` proves exact
  coordinate debt scaling by joint Continue mass when the prefix root is
  Nash against the complete cap. For equal payoff/cap annotations it
  preserves zero debt exactly, as used at every least source.
* `quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart` in
  `UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean` bounds
  the difference of two full caps after an arbitrary fixed finite word by
  player-deleted survival times the positive initial discrepancy. Applying
  it in both directions supplies the uniform nonexpansiveness needed to
  remove virtual seeds. It does not require intermediate Nash roots.
* `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  states exactly that terminal approximate Nash profiles at every positive
  error are equivalent to existence of one uniform-equilibrium payoff. The
  adapter in Section 9.1 supplies its right-hand hypothesis and imports no
  additional strategic certificate.

These are existing checked-source declarations under their stated imports;
no new Lean build or formalization of this packet is asserted. The new
mathematics consists of the marked small-root face induction, the exhaustive
actual source support elimination, and the uniform reward-neighborhood
compactness proof with its unbounded favorable parameter. No published
paper claim is used as an unproved intermediate lemma.

A direct formalization can define the actual finite-dimensional annotation
closure, prove (Prefix), (Debt), (Repair), and the positive-Never tail
extraction, and prove the local lemma by induction on finite zero sets.
The table has a finite coordinate definition. The support cases reduce to
explicit rational polynomial identities and Bernstein sign certificates.
For the neighborhood theorem, a contradiction sequence of normalized tables
and their bounded passive source/tail coordinates avoids compactifying T;
its single negative contribution is discarded before passage to the limit.
The final theorem should quantify a positive radius over raw table distance,
then derive absorbing debt infimum zero and the existing terminal semantic
consumer. No structure field should assume equilibrium existence, an actual
minimum selector, or the required prefix words.

## 12. Scope and nonclaims

The result covers the displayed open reward class with nonnegative original
own singleton levels. It does not settle arbitrary Fin4 or give a numerical
radius. The strategic construction is unrestricted in time and deviation
power; it does not assert existence within any fixed finite controller or
stationary architecture. The closed carrier is used only through actual
approximants and continuous finite prefixes. Virtual annotations are never
declared realizable, and limiting tails from changing games are used only
through the finite algebraic necessary conditions proved in Section 8.
