# Boundaries of finite incoming arguments

Owner: CODEX_ROOT. Independently reviewed ordinary mathematics; internal only.

These controls identify precise limits of the
[uniform incoming source reduction](../exports/PAIR_PREMIUM_MIXED_ENDPOINT_REDUCTION.md).
A positive pair premium can force arbitrarily long finite incoming words,
even for actual tuples. Two zero observer caps can forbid every nonzero finite
incoming word on an open raw region. These mechanisms coexist with the stated
singleton residual tests. Each displayed completion nevertheless has an
absorbing equilibrium, so neither is a global-minimum counterexample or a
new restriction on UE reward tables.

The [two-zero continuation reductions](../exports/TWO_ZERO_CONTINUATION_REDUCTIONS.md)
now supply such a global comparison on a nonempty part of the second geometry.
A nonlinear reset returns every observer cap exactly while improving the
pivot and reducing Never, so it remains valid through every inherited head.
Its explicit completion preserves the no-finite-incoming obstruction below;
the comparison itself is a compact limit of finite profiles. The remaining
two-zero continuations still require further work. The Ratio-specific
limitation of the first control is proved explicitly. A third control below covers the remaining BOTH-LOW pivot/observer face:
a general full-Nash criterion forbids every nonzero incoming root, with an
exact inverse-positive degree1 example. It confirms that global minimality
is essential for that face. Section and equation
numbers are local to each part. The [independent reviews](../feedback/CODEX_ROOT__INCOMING_BOUNDARY_CONTROLS__BY_INDEPENDENT_REVIEWS.md)
record the exact scope and the original reviewed proof hashes.

The [additional internal reviews](../feedback/CODEX_ROOT__RESET_AND_INCOMING_CONTROLS__BY_INDEPENDENT_REVIEWS.md)
cover the general BOTH-LOW obstruction and exact fixture in Part III.

## I. Sharp finite incoming-length obstruction at a positive pair premium


### What fails, and what does not

The uniform incoming theorem outside J_ip>max(0,Gamma_ip) cannot be extended
to that missing sign region using its other hypotheses alone. For ONE fixed
native four-player table, all integers n>=1, and arbitrarily small f>0,
there are ACTUAL independent-clock tuples X_(f,n) with zero observer debts,
ALL-END, positive original Never masses, B_i=f, and the other three caps
uniformly greater than1/8. Every finite incoming factorization of X_(f,n)
which contains any nonpivot activity has at least n+1 dates. A shorter
factorization has total activity at most -log(1-f).

Consequently no uniform positive activity bound and uniform finite length
bound work throughout this three-positive-cap collar. This is an exact
length obstruction on actual tuples, not only a nonrealized limiting point.
It allows arbitrary product roots and arbitrary tails in the full augmented
compact carrier, rather than retaining one chosen head word.

The example can satisfy R0, degree1, positive full determinant and a strict
positive inverse pivot column. It nevertheless has an explicit absorbing
Nash profile, so it does not refute an extension using ALL no-UE source
constraints. Its zero-observer row lies outside the Ratio chamber. A final
structural calculation explains why the analogous deadline construction
inside Ratio has negative determinant and cannot survive the source there.

### A single complete table

Players are p=0, i=1, j=2, k=3. Own singleton and AllNever rewards vanish.
The following rules specify every nonempty-coalition reward Z_l(S).

* For recipient0: if 0 belongs to S, pay0. Otherwise, if 1 belongs to S,
  pay2. On S={2},{3},{2,3}, pay respectively -7,6,8.
* For recipient1: on S={0},{0,1},{2},{3}, pay respectively1,2,1,-1;
  pay0 on every other coalition.
* For recipient2: pay -1 if 0 belongs to S; otherwise pay1 if 3 belongs
  to S; otherwise pay -4 if 1 belongs to S; otherwise pay0.
* For recipient3: pay -2 if 0 belongs to S; otherwise pay1 if 2 belongs
  to S; otherwise pay2 if 1 belongs to S; otherwise pay0.

Thus M=8 bounds every reward. The critical singleton and pair rewards are
G=Z1({0})=1 and J=Z1({0,1})=2>max(0,G). Notice that recipients2,3 have
rewards independent of their own membership in the quitting coalition:
for every root, Q2=P2 and Q3=P3 exactly.

The singleton matrix is

    Gamma=[0,2,-7,6; 1,0,1,-1; -1,-4,0,1; -2,2,1,0],
    det Gamma=32, Gamma^-1 e0=(3,1,4,7)/16>0.

All principal submatrices of order at least two are nonsingular; their
mask-ordered determinants are

    mask: 3,5,6,7,9,10,11,12,13,14,15,
    det: -2,-7,4,26,12,2,16,-1,8,6,32.

Every singleton column has a negative entry, so no nonzero homogeneous
complementary vector can have singleton support. Nonsingularity excludes
all larger homogeneous supports. Hence Gamma is R0. At offset -ones,
exhausting all fifteen supports gives the unique complementary vector

    x=(13/8,3/8,7/2,33/8), w=0.

It has full-support index sign(det Gamma)=1. Thus the R0 degree is1.
These are exact finite calculations reproduced below, not a no-UE claim.

### Explicit actual profiles

Fix t=1/4, 0<f<1/64, and n>=1. Put

    alpha_l=f*2^(-l-1), l=0,...,n-1,
    F=f(1-2^-n), v=f*2^-n/(1-F).

Player0 puts absolute first-Quit atoms alpha_l on dates0,...,n-1 and its
remaining mass1-F on Never. Player1 always uses Never. Players2 and3 have
only one possible finite date, namely date n, with respective probabilities
t+v and t. All laws are independent. The strict bound on f gives 0<t+v<1.

Call the one-date tail Q_v. Its actual native values/caps/Never offers are

    (b_v,v,t,t+v), b_v=5/16-(19/4)v>1/8.

Indeed recipient1's passive value is q2-q3=v and its Quit offer is0.
Recipients2,3 have Q=P and are indifferent. Recipient0's Quit offer is0,
while its passive expectation is
-7q2(1-q3)+6(1-q2)q3+8q2q3=b_v>0.
After this date all players Never; all full caps follow by the literal
maximum recursion, including later deadlines.

For player1, its deadline at any pivot-head date l has payoff

    sum_(h<l)alpha_h+2 alpha_l=f.

Its pure-Never payoff is

    F+(1-F)v=f.

Its deadline at the final joint date pays F<f; later deadlines pay f.
Thus it is optimal to use Never, and its full behavioral cap is f.
For players2,3, every pivot-head deadline has nonpositive value, whereas
the through-head values below are positive. Their later prescribed actions
are optimal by the Q_v calculation. Player0's early Quit offers are0 and
its cap is b_v, attained by Never. Therefore the complete augmented tuple is

    U=((1-F)b_v, f, -F+(1-F)t, -2F+(1-F)(t+v)),
    B=e=(b_v, f, -F+(1-F)t, -2F+(1-F)(t+v)),
    N=(1-F,1,1-t-v,1-t).                                 (1)

The three coordinates other than1 exceed1/8 uniformly. Observer debts are
zero, every original Never coordinate is positive, and the tuple is ALL-END.
All cap assertions concern every behavioral replacement: a fixed private
random seed determines a deadline or Never, and all those responses were
priced. No public randomization is used.

### Two saturated defects force chronological separation

For any actual tuple with N1=1, let f0=1-N0 and t_l=1-N_l. Against recipient2's
Never response, the payoff is -1 when player0 is first or tied with3,
and +1 when player3 is strictly before player0. Independence gives

    e2=-f0+N0*t3+2 Pr(T3<T0<infinity).

Similarly,

    e3=-2f0+N0*t2+3 Pr(T2<T0<infinity).

Consequently the coordinate defects

    D2=e2+f0-N0*t3 >=0,
    D3=e3+2f0-N0*t2 >=0                              (2)

are nonnegative on the augmented compact carrier whenever N1=1. To pass
from actual approximants with N1 tending to1, delete player1's vanishing
finite mass; a bounded-reward coupling controls the error. No realization
of the limiting tail is needed.

The tuple (1) has D2=D3=0. Under a literal root with q1=0, writing f0^+
for the continuation's finite pivot mass, direct root algebra gives

    D2(before)=(1-q0)(1-q3)D2(after)
                   +2(1-q0)q3 f0^+,
    D3(before)=(1-q0)(1-q2)D3(after)
                   +3(1-q0)q2 f0^+.                    (3)

All terms are nonnegative. These identities also hold on the compact carrier
by continuity.

### Exact n+1 lower bound for every incoming representation

Suppose (1) has a finite incoming factorization into product roots followed
by any compact-carrier tuple, preserving U,B,e,N exactly. Positive original
Never makes every root nonsure. N1=1 forces q1=0 at every root and N1=1 at
all descendants. The exact debt recursion passes zero observer debt to all
descendants; the positive-survival END-gap recursion passes ALL-END.

Before the first root with player2 or3 active, every root is pivot-only.
Let A be the absolute pivot mass already used by this prefix. Its survival
is1-A. The retained finite pivot mass and player1 cap are

    f0=(F-A)/(1-A), B1=e1=(f-A)/(1-A).                  (4)

At a pivot-only root with conditional hazard x, player1's Quit offer is2x.
Thus ALL-END requires 2x<=B1. Its absolute pivot atom alpha=(1-A)x obeys

    alpha<=(f-A)/2.

After L pivot-only roots, even allowing empty queries,

    A<=f(1-2^-L).                                      (5)

Now consider the first root with q2+q3>0, if one occurs. Equations (2)--(3)
force f0^+=0: there is no remaining finite pivot mass in its tail. Because
Q2=P2 and Q3=P3, an active observer's exact root contact forces its tail
cap to vanish. With players0,1 Never in that tail, B2=e2=1-N3 and
B3=e3=1-N2. Thus if either player2 or3 is active, the other must exhaust
its remaining finite mass at this same root; then both are active. Since
no earlier root used either player, their hazards here are exactly

    q2=t+v, q3=t,

and afterward N0=N1=N2=N3=1. Let x=q0 and s=(1-t-v)(1-t).
The player1 Never recursion at this root is

    e1=x*s+(1-x)*v.                                    (6)

By (4) and f0^+=0, its current finite pivot mass is x=(F-A)/(1-A), while

    e1=x+(1-x)*v,

because f-F=(1-F)v. Comparing with (6) gives x(1-s)=0. Since s<1, x=0.
Thus A=F: ALL finite pivot mass must have been used strictly before the
first nonpivot root. Equation (5) and F=f(1-2^-n) now imply L>=n.
The first nonpivot root is therefore date n or later; any incoming word
containing it has length at least n+1.

If an incoming word has length at most n, it can contain only pivot roots.
Its survival is at least N0(X)=1-F, because the remaining pivot Never
coordinate is at most1. Hence

    sum_a sum_l q_(a,l)=sum_a q_(a,0)
       <=-log product_a(1-q_(a,0))
       <=-log(1-F)<-log(1-f).                         (7)

This proves the stated obstruction, including tails that are not actual.
The bound n+1 is attained by the original profile itself.

For any proposed uniform length m and activity eta>0, choose
0<f<min(1/64,1-exp(-eta)) and n>=m. Equation (7) rules out every incoming
word of length at most m with activity at least eta. One may additionally
make f smaller than any prescribed cap-collar width. All other caps keep
the same positive lower bound1/8. Thus the failure is precisely uniformity
as the fourth cap approaches zero.

### The nonrealized limit and why the exact face does not repair the collar

As n tends to infinity at fixed f, (1) converges to

    U=((1-f)5/16, f, -f+(1-f)t, -2f+(1-f)t),
    B=e=(5/16, f, -f+(1-f)t, -2f+(1-f)t),
    N=(1-f,1,1-t,1-t).                                 (8)

This compact-carrier tuple is not actual. The same saturated-defect argument
shows that any first date using player2 or3 would have to follow exhaustion
of pivot finite mass f. But the player1 cap bound permits at most
f(1-2^-L)<f in L finite pivot dates. Since N2,N3<1, an actual representation
would have such a finite first date, a contradiction.

Every finite incoming factorization of (8) is pivot-only and has total
activity at most -log(1-f). At f=0 the tuple is the actual Q_0 and has a
macroscopic joint incoming root. Thus an exact-face incoming theorem can
coexist with the proved failure of every neighborhood-uniform finite rule.
No root is placed after an infinite calendar in this argument.

### Source-specific limitation and the Ratio determinant obstruction

The matrix calculation above confirms that this length obstruction is
compatible with R0, degree1, positive determinant and a strict inverse pivot
column. It is NOT a surviving no-UE example: the sole sure quitter1 already
forms an absorbing Nash profile. Players0,2,3 receive respectively2,-4,2;
joining pays respectively0,-4,2. Player1's own0 is optimal. The original table R=Z+1 also has this same
absorbing Nash profile; arbitrary negative shifts of the sure quitter
are not covered, because that player can choose Never and receive0.

The construction uses two protected players with positive reciprocal
singleton rewards Gamma_jk=Gamma_kj=1. If it is forced into Ratio, where
Gamma_ab=-G_a c_ab with c_ab>0 for distinct observers and G_i>0, this makes
G_j<0 and G_k<0. A strict positive inverse pivot column yields z=c^-1 1>0
and h dot z>0, where h is the pivot singleton row. Schur complementation gives

    det Gamma=-(G_i G_j G_k) det(c) (h dot z).           (9)

Here det(c)=c_ij c_jk c_ki+c_ik c_ji c_kj>0. With two negative G entries,
the right side is negative. Therefore THIS positive-premium length mechanism
cannot satisfy the established det Gamma>0 source requirement inside Ratio.
The obstruction is structural, not a failure to search enough constants.
The det-positive example above necessarily leaves Ratio; its row1 has mixed
observer singleton signs. A source-specific uniform or global reduction in
the remaining det-positive Ratio chamber is still open and is not refuted.

### Sources and exact check

The literal max-cap and semantic-prefix declarations inspected are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`).
The source distinction det Gamma>0 is used only as an existing required
filter, not derived from R0 degree1 alone. No Lean commands were run.

The payoff and defect identities above are direct finite-outcome formulas.
The complete matrix and support census is reproduced by this short Python3
program with SymPy; every comparison is exact.

```python
import sympy as s
G=s.Matrix([[0,2,-7,6],[1,0,1,-1],[-1,-4,0,1],[-2,2,1,0]])
assert G.det()==32
assert G.inv()[:,0]==s.Matrix([3,1,4,7])/16
assert all(min(G[i,j] for i in range(4) if i!=j)<0 for j in range(4))
dets={}; roots=[]
for mask in range(1,16):
    ids=[i for i in range(4) if mask>>i&1]
    if len(ids)==1:
        continue  # Zero diagonal cannot solve 0*x=1 at this offset.
    A=G.extract(ids,ids);dets[mask]=A.det();assert A.det()!=0
    z=A.inv()*s.ones(len(ids),1);x=s.zeros(4,1)
    for i,t in zip(ids,z):x[i]=t
    w=G*x-s.ones(4,1)
    if all(t>=0 for t in x) and all(t>=0 for t in w):
        assert all(x[i]*w[i]==0 for i in range(4))
        roots.append((mask,x))
assert list(dets.values())==[-2,-7,4,26,12,2,16,-1,8,6,32]
assert roots==[(15,s.Matrix([s.Rational(13,8),s.Rational(3,8),
                             s.Rational(7,2),s.Rational(33,8)]))]
print('PASS exact principal determinants, strict column and complete LCP census')
```

## II. Two zero observer caps can forbid every finite incoming word


### 1. Complete table and exact claim

The four native players have own singleton and AllNever rewards zero. Set

    Gamma=[ 0, 5,-1,-1;
           -2, 0, 1, 1;
            2,-1, 0,-1;
            2,-1,-1, 0].

For every nonsingleton coalition S, set Z_i(S)=1 when i belongs to
S and i is2 or3; set every other nonsingleton reward to0. This specifies
all rewards. The proof also works for ANY finite completion whose participant
entries in rows2 and3 are all strictly positive.

Let H be the closure of actual independent complete stopping-law tuples
(U,B,e,N). Here B is the cap over ALL unilateral behavioral replacements,
e the pure-Never response, and N the ORIGINAL individual Never masses.
Let C impose B_i=U_i for observers i=1,2,3, with pivot0. Then H contains

    U=(2802569/32000000, 40951/250000, 0, 0),
    B=e=(3683/16000, 40951/250000, 0, 0),
    N=(9/20, 1/2, 81/200, 81/200).                         (X)

This tuple is in C, is ALL-END, has positive original Never coordinates,
and has exactly two zero observer caps and positive other caps. Yet every
finite literal product-root factorization

    X=Phi_(q_1)...Phi_(q_m)(T), T in H,

has all q_a=0 and T=X. Thus it has NO positive-activity finite incoming word,
even with arbitrary continuation. The pivot-pair inequalities from the
one-zero theorem hold STRICTLY for both zero rows:

    J_20=J_30=1<2=Gamma_20=Gamma_30.

No local extension based just on these pair inequalities can suffice.

### 2. Exact repeated-root cap formula

For one proper product root, write P_i for the passive absorption contribution
when i Continues, Q_i for its forced-Quit offer, H_i for opponents' survival,
E_i for the prescribed absorption contribution, and c for joint survival.
Repeat that root n times over a supplied actual tail (u,b,e,N). Put

    A_i=P_i/(1-H_i), D_i=E_i/(1-c).

When 0<H_i,c<1, the exact output coordinates are

    e_i'=A_i(1-H_i^n)+H_i^n e_i,
    U_i'=D_i(1-c^n)+c^n u_i,
    B_i'=max{Q_i,
             A_i(1-H_i^(n-1))+H_i^(n-1)Q_i,
             A_i(1-H_i^n)+H_i^n b_i}.                    (1)

Indeed the n head deadline offers are A_i(1-H_i^t)+H_i^t Q_i for
0<=t<n, a monotone sequence, so only its endpoints matter. The third term
includes every tail deadline and Never, whether or not the tail cap is
attained. Behavioral replacements are mixtures of deadlines and Never.
Thus (1) preserves the full response class, not only root deviations.
Original Never masses multiply by the player's root survival to power n.

For fixed rates lambda and duration T, take q_(n,i)=1-exp(-lambda_i T/n).
Let Lambda=sum lambda and L_i=Lambda-lambda_i. Bounded rewards and native
own-zero imply, as n tends to infinity,

    A_i -> (sum_a Gamma_ia lambda_a)/L_i,
    D_i -> (sum_a Gamma_ia lambda_a)/Lambda,
    Q_i ->0,
    H_i^n=exp(-L_i T), c^n=exp(-Lambda T).                 (2)

All L_i below are positive. Equations (1)--(2) give convergence of FULL caps;
there is no unproved interchange of a supremum with the diffuse limit.

### 3. Two finite blocks and the rational limiting tuple

Each approximant is one actual 2n-stage profile: a first repeated-root block,
then a second repeated-root block, then AllNever. There is no stage after
an infinite calendar.

The SECOND block has all four rates equal to1 and duration log2. Since
Gamma*(1,1,1,1)=(3,0,0,0), equations (1)--(2) give its limiting tail tuple

    U^tail=(45/64,0,0,0),
    B^tail=e^tail=(7/8,0,0,0),
    N^tail=(1/2,1/2,1/2,1/2).                             (3)

For row0, A tends to1, D to3/4 and H^n=1/8; the other rows' ratios tend
to0. Thus (3) includes the full caps, not just the prescribed payoffs.

The FIRST block has rates lambda=(1,0,2,2) and exp(-T)=x=9/10. Here

    Gamma*lambda=(-4,2,0,0), Lambda=5,
    A ->(-1,2/5,0,0),
    (H_0^n,H_1^n,H_2^n,H_3^n)=(x^4,x^5,x^3,x^3).

Using (3) as the limiting tail in (1) yields

    U_0=-(4/5)(1-x^5)+(45/64)x^5
       =-4/5+(481/320)x^5,
    U_1=(2/5)(1-x^5), U_2=U_3=0,

    e_0=-(1-x^4)+(7/8)x^4=(15/8)x^4-1>0,
    e_1=(2/5)(1-x^5)>0, e_2=e_3=0.

Row0's two head-cap endpoint limits are0 and -(1-x^4)<0, while its
through-tail cap is e_0>0. Row1's last head deadline and through-tail cap
both tend to e_1>0; rows2 and3 have all three terms tending to0. Hence
B=e exactly in the limit. The original Never vector is exactly
(x/2,1/2,x^2/2,x^2/2) for EVERY approximant. Substitution gives (X).
Observer debts tend to0; the approximants themselves need not lie in C.

### 4. Every incoming root is zero; zero queries cannot evade this

For i=2,3 the literal table has

    Q_i(q)=1-product_(a!=i)(1-q_a)>=0.                    (4)

More generally strict positive participant entries give the same inequality
with a strictly positive multiplicative lower bound. The root full cap is
at least Q_i, independently of the continuation. Its value0 at X therefore
forces q_0=q_1=q_3=0 from row2 and q_0=q_1=q_2=0 from row3. Hence q=0.
This also excludes sure roots.

A zero root is a genuine queried date, with map

    U_before=U_after, e_before=e_after, N_before=N_after,
    B_before=max(0,B_after) coordinatewise.               (5)

It is NOT an identity on arbitrary tuples. But H always satisfies B>=e,
and X has B=e>=0. Thus (5) forces the whole after-tuple to equal X.
Induction proves that every finite incoming word is entirely zero.

The tuple is also nonrealized by actual complete stopping laws: an actual
first root would be zero and its actual tail would again equal X. Induction
would force every finite hazard zero, contradicting its original N vector.

### 5. An open raw criterion for the same obstruction

The two-block mechanism does not require the displayed singleton equalities.
Let p,i,j,k be the four distinct players. Assume Gamma is invertible and

    v=Gamma^-1 e_p>0,
    Gamma_ip,Gamma_jp>0, Gamma_ij,Gamma_ji<0.              (6)

Define the nonnegative first-block rate vector by

    w_p=1, w_i=-Gamma_jp/Gamma_ji,
    w_j=-Gamma_ip/Gamma_ij, w_k=0.

Then w_i,w_j>0 and (Gamma w)_i=(Gamma w)_j=0. Require only

    g_k=(Gamma w)_k>0,                                   (7)

with NO sign condition on g_p=(Gamma w)_p. Require every participant
nonsingleton reward of each of i,j to be strictly positive. All remaining
higher rewards are arbitrary finite. One may additionally impose

    0<J_ip<Gamma_ip, 0<J_jp<Gamma_jp.                     (8)

For every such table there exists a nonrealized ALL-END tuple in C with
positive original Never masses, exactly zero caps i,j, positive caps p,k,
and NO positive-activity finite incoming word, even with arbitrary tail.

Proof. Fix any second-block duration tau>0 and give its four owners rates v.
Put V=sum v and L=V-v_p>0. Since Gamma v=e_p, equations (1)--(2) give

    U_p^tail=u=(1-exp(-V tau))/V>0,
    B_p^tail=e_p^tail=b=(1-exp(-L tau))/L>0,

while every observer's U,B,e is0 and N_a^tail=exp(-v_a tau)>0.
Let the first block have rates w, duration t>0, total W=sum w, and
L_p=W-1>0. Its limiting output is

    U_p=(g_p/W)(1-exp(-W t))+exp(-W t)u,
    e_p=(g_p/L_p)(1-exp(-L_p t))+exp(-L_p t)b,
    U_k=e_k=(g_k/W)(1-exp(-W t))>0,
    U_i=e_i=U_j=e_j=0,
    N_a=exp(-w_a t-v_a tau)>0.                            (9)

Choose t sufficiently small that both U_p,e_p remain positive. The pivot's
first/last head-deadline limits are0 and
(g_p/L_p)(1-exp(-L_p t)). Its through-tail cap equals e_p and exceeds
the latter value by exp(-L_p t)b>0, so (1) gives B_p=e_p regardless of
the sign of g_p. For k, the last head deadline and through-tail cap both
equal e_k>0. For i,j all three cap terms tend to0. Therefore B=e and
observer debts vanish. Concatenating the two n-stage approximating blocks
proves that (9) belongs to H. Section4 applies verbatim to the positive
participant rows i,j, proving the incoming-word obstruction and
nonrealizability. This proves the criterion.

All hypotheses (6)--(8) and participant positivity are strict, continuous
conditions on the raw native rewards, so the criterion describes an open
region. It is nonempty: the literal table has p=0,i=2,j=3,k=1,
v=(1,1,1,1)/3, w=(1,0,2,2), and Gamma w=(-4,2,0,0).
Taking tau=3 log2 and t=-log(9/10) recovers (X). The same fixed durations
work in a neighborhood, since all needed positive quantities there are
strict. The full inverse positivity, positive determinant and listed
strict singleton-screen failures also persist in a sufficiently small
neighborhood of this matrix.

This is an open-region FAILURE of a finite-incoming carrier lemma. It is
not an open UE exclusion or a claimed positive-gap/global-minimum source.
No assertion A>0 is made for any completion in this region.

### 6. Exact scope and prior singleton screens

The existing signed-pivot fixture has det Gamma=6 and strictly positive

    Gamma^-1=[1/3,7/6,5/6,5/6;
              1/3,2/3,1/3,1/3;
              1/3,5/3,4/3,1/3;
              1/3,5/3,1/3,4/3].

Strict inverse positivity proves R0 and that the unique LCP root at offset
-1 is fully supported, with index+1; hence its R0 degree is1. Column0 of
the inverse is strictly positive. Every singleton column has a negative
entry, and pair23 is mutually negative. Only principal triples012 and013
have nonnegative inverse, but both outside inverse rows are negative. These
are existing matrix facts, not new strategy-class exclusions.

The literal completion is ALREADY SOLVED: pure simultaneous quitting by
players2 and3 gives native payoff (0,0,1,1). Each quitter strictly prefers
joining to Continue (the latter receives -1); players0,1 are indifferent to
joining, receiving0 either way. Thus this is an actual absorbing Nash
profile with all debts zero and nu=0. Its absorbing minimum A is0, and the
global minimum of d_0+r nu is0 for every r>0. The tuple (X), whose

    d_0=4563431/32000000>0, nu=59049/1600000>0,

cannot be such a global minimum. For source comparison R_i(S)=1+Z_i(S),
with original live/Never rewards0, the same pure profile is absorbing Nash
at payoff (1,1,2,2). There is no original-game counterexample here.

The result shows why the TWO-zero carrier case cannot be closed by a finite
incoming lemma that uses only cap signs, original Never positivity, good
pivot pair premiums, and these singleton residual screens. Any successful
extension must use an additional global-minimum property or a different
operation. It does not refute such a source-specific extension.

Sources inspected: the [uniform incoming reduction](../exports/PAIR_PREMIUM_MIXED_ENDPOINT_REDUCTION.md);
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
`CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md`; and
`CODEX_COORDINATOR__DIFFUSE_APPROXIMATION_ATOM_OBSTRUCTION.md`.
The last excludes diffuse approximate FULL equilibria on the residual;
the strictly positive pivot debt here prevents applying its adapter.


## III. Both-low pair data can forbid every nonzero incoming word

This is a carrier obstruction, not a positive-gap or minimizing example.
The complete game below has an absorbing Nash profile.

### Complete table and compact full-Nash point

Players are 0,1,2,3, with pivot0. Own singleton and AllNever rewards vanish.
The singleton matrix is

    Gamma=[ 0, 3,-1,-1;
            3, 0,-1,-1;
           -1,-1, 0, 3;
           -1,-1, 3, 0].                               (G)

For rows0 and1, set every nonsingleton reward equal to -1, except

    Z_0({0,1})=Z_1({0,1})=-3.

For l=2,3, set every nonsingleton participant reward to0, set the passive
reward Z_l({0,1})=100, and set every other nonsingleton passive reward to0.
Together with (G), these rules specify the complete native table.

Thus Gamma_01=Gamma_10=3 and J_01=J_10=-3<min(0,3): both rows lie strictly
outside the monotone segment on its LOW side. Every forced-Quit offer of
player2 or3 is nonpositive at every product root (in fact it is identically
zero, since all their participant rewards including own singleton are0).

Let H denote the full augmented actual-law closure (U,B,e,N), and let C impose
zero debts for observers1,2,3. The following point belongs to H:

    U=B=e=(0,0,62/147,32/21),
    N=(6/7,6/7,1/2,1).                                 (X)

It has zero debt for ALL FOUR players, positive original Never, and exactly
the zero pivot and observer1 caps. Every literal product-root factorization
X=Phi_q(T), T in H, has q=0 and T=X. Consequently every finite incoming word
is entirely zero. This includes arbitrary compact tails, not just tails in
the family used to produce (X).

### Finite actual approximants and exact full-cap convergence

Start with the one-date root q=(0,0,1/2,0), followed by AllNever. Its exact
full cap and payoff vector is (-1/2,-1/2,0,3/2); it is Nash. Rows0,1 receive
-1/2 from either forced Quit or prescribed Continue; player2 receives0 from
every response; player3 prefers Continue at3/2 to Quit at0.

Put x_0=1/6 and, for n>=1, define

    x_n=x_(n-1)/(2+x_(n-1))=1/(7*2^n-1).

Prefix the base, in chronological order, by pair roots with hazards
(x_n,x_n,0,0),...,(x_1,x_1,0,0). Against a tail whose two active caps equal
-3x_(m-1), each pair player's forced-Quit offer is -3x_m and its Continue
cap is

    3x_m-3(1-x_m)x_(m-1)=-3x_m.

Thus both active players are exactly indifferent and their output cap and
payoff are -3x_m. Their marginal survival through the n-root head is

    a_n=product_(m=1)^n(1-x_m)=6*2^n/(7*2^n-1)
       =(6/7)(1+x_n) ->6/7,
    S_n=a_n^2.

Let alpha_n be the probability that this head's first coalition is exactly
{0} (equally, {1}), and c_n the probability of first coalition{0,1}.
The pair payoff identity and total probability give

    alpha_n-c_n=S_n/6-x_n,
    2alpha_n+c_n=1-S_n,
    c_n=[1-(4/3)S_n+2x_n]/3.                            (1)

Consequently the exact outsiders' through-head Continue offers are

    E_2=100c_n-2alpha_n
       =(98+202x_n)/3-(1580/49)(1+x_n)^2,
    E_3=E_2+(3/2)S_n.                                  (2)

For n>=1, x_n lies in [0,1/13]. The quadratic E_2(x) in (2) is concave and
has endpoint values

    E_2(0)=62/147>0, E_2(1/13)=76/169>0.

Hence every such E_2, and therefore E_3, is strictly positive. At every
head root both outsiders have forced-Quit offer0. They therefore prefer
Continue, and (2) gives their exact full caps and prescribed payoffs.
Induction proves that every finite approximant is a full terminal Nash
profile against every complete behavioral deviation. The max-cap recursion
includes every later deadline and Never, not merely current deviations.

All original Never masses are positive. Thus full Nash implies B=e by
B-U>=N(B-e)>=0; the same equality also follows directly from the root maps.
Taking n->infinity in these exact formulas gives the complete tuple (X):
E_3 tends to62/147+(3/2)(36/49)=32/21. Original Never masses are
(a_n,a_n,1/2,1). No escaping finite mass is relabeled Never.

### A general no-incoming lemma on this face

The following sufficient criterion proves the obstruction beyond the literal
example. Let p,i,j,k be the four distinct players, and let X in H have

    d_l(X)=0 for ALL FOUR l, N_l(X)>0,
    B_p(X)=B_i(X)=0, B_j(X),B_k(X)>0.                  (L1)

Require the raw conditions

    Gamma_pi,Gamma_ip>0, J_pi,J_ip<0,
    Z_l(S)<=0 whenever l in S, for l=j,k,
    Gamma_lp,Gamma_li<=0 for l=j,k.                    (L2)

Then every incoming literal root factorization of X is the zero root with
the same tail X. Hence every finite incoming word is entirely zero and X is
not actual. FULL Nash in (L1), including d_p=0, is essential to this proof;
observer optimality alone does not justify the active-pivot argument below.

Proof. Full Nash and positive original Never give B=e by
B_l-U_l>=N_l(B_l-e_l)>=0. Any root factorization X=Phi_q(T) has proper roots
and positive tail Never coordinates. All four zero debts and ALL-END pass
to T. At the root every active player must attain its output cap.

The outside forced-Quit offers are nonpositive by (L2), so their strictly
positive caps force q_j=q_k=0. If both q_p,q_i are positive, the pivot's
forced-Quit offer J_pi q_i is negative while its output cap is zero, which
contradicts its active optimality. At most one pair owner acts.

Suppose q_p>0 and q_i=0. After any finite sequence of solo-p incoming roots,
let F be p's aggregate finite quitting mass in that prefix. The conditional
full-Nash, ALL-END tuple has exact caps and Never coordinates

    B_p=0, B_i=-Gamma_ip F/(1-F),
    B_l=[B_l(X)-Gamma_lp F]/(1-F)>0 for l=j,k,
    N_p=N_p(X)/(1-F), N_a=N_a(X) for a!=p.             (3)

The outside caps stay positive because Gamma_lp<=0. Original Never forces
F<=1-N_p(X)<1. After the hypothesized first root, F>=F_0=q_p>0.

Every point of H has a first-root representation, by extracting first roots
and actual conditional tails from actual approximants. Apply it at the
current tuple (3). The negative i cap rules out the zero root. Positive
outside caps again force q_j=q_k=0. The full-cap inequality B_i>=Q_i=J_ip q_p
forces

    q_p >= [Gamma_ip/(-J_ip)] F/(1-F)
        >= [Gamma_ip/(-J_ip)] F_0/(1-F_0)=epsilon>0.   (4)

Player p is therefore active and must attain its output cap0, so
J_pi q_i=0 and q_i=0. The next root is solo-p and (3) propagates. If epsilon
is at least1, properness already gives a contradiction. Otherwise repeated
extraction gives arbitrarily many solo-p roots of hazard at least epsilon.
Their product survival would tend to zero, while (3) forces it to stay at
least N_p(X)>0. This contradiction excludes the initial solo-p root.
The symmetric argument excludes a solo-i root.

Thus q=0. A zero queried root fixes U,e,N and sends B to max(0,B), so is
not an identity on arbitrary H points. Here B(X)=e(X)>=0 and every H point
has B>=e. These facts force its tail to equal X. Induction proves the
finite-word assertion. If X were actual, its first root and every subsequent
one would be zero with unchanged conditional tuple. This would force N=one,
inconsistent with B_j,B_k>0 in a native own-zero game. This proves the lemma.

The literal point (X) satisfies every hypothesis: both pair cross singletons
are3, both pair rewards are-3, all outsider participant rewards are zero,
and all four outsider singleton rewards on pair owners are-1. In (3), its
outside caps are (B_l(X)+F)/(1-F), so they in fact increase during the
contradictory solo-owner extraction. This proof covers arbitrary compact
tails, with no assumption about their particular calendars or reward support.

### Matrix screens and exact scope

The singleton matrix has

    det Gamma=45,
    Gamma^-1=(1/15)[2,7,3,3;7,2,3,3;3,3,2,7;3,3,7,2]>0.

It is R0: if x>=0, w=Gamma x>=0, and x_l w_l=0, then any nonzero w would
give x=Gamma^-1 w>0, forcing w=0, a contradiction. Thus w=0 and x=0.
At offset -one, a complementary solution has w=Gamma x-one>=0, hence
x=Gamma^-1(one+w)>0. Complementarity forces w=0, yielding the unique full
solution x=Gamma^-1 one=one. Its determinant index is+1, so the R0 degree
is1. Every singleton column has a negative entry and mutually negative pairs
exist. Every principal triple has determinant6 and a negative inverse
diagonal entry; hence there is no nonnegative-inverse triple child.

Nevertheless the game has an absorbing Nash profile: player2 quits surely
and everyone else continues. Players0,1 receive-1 and joining also pays-1;
player3 receives3 and joining pays0; player2 receives its own0 and cannot
gain by Never. Therefore the native absorbing SUM-debt gap is A=0. The point
(X) is not a subcritical global minimum of d_0+r nu for r>0, since the
absorbing zero-debt profile has objective0. No positive-gap example is claimed.

This blocks a universal finite-incoming theorem covering BOTH-LOW under
H/C/ALL-END/positive-Never/two-positive-cap hypotheses even with the stated
singleton screens. A further source-specific argument must use global
minimality, additional higher-reward structure, or a different operation.
