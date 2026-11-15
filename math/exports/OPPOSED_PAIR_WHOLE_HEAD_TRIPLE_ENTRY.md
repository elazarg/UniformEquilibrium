# Whole-head revision forces a triple entry in the opposed-pair source chain

## Exact statement

Four players0,1,2,3 use independent complete stopping laws on natural dates
plus a distinct Never point. One unilateral deviation may replace an entire
law. Native own-singleton, live and Never rewards are zero; every other
coalition reward is finite. Fix the singleton matrix

    Gamma=[0,-2,-5,4;-6,0,-4,6;1,3,0,-5;1,-1,4,0].

Require every participant reward of owners1,2 to be nonpositive. Fix

    Z0(01)=-1,Z0(03)=3,Z1(01)=-7,Z1(13)=-1,
    Z3(03)=2,Z3(13)=-2,Z0(013)=2,Z1(013)=-8,Z3(013)=0,
    Z2(01)=4,Z3(01)=0,Z1(03)=0,Z2(03)=-4.          (R)

The remaining31 nonsingleton entries are arbitrary subject to those signs.
For actual play retain prescribed payoff U, full behavioral response cap B,
literal-Never response e and ORIGINAL Never marginals N. Put
D=sum_i(B_i-U_i),nu=product_i N_i. Let C be the compact closure of these
bounded actual tuples and E={X in C:B=U}. Define

    A_Z=inf{D(P):P actual,nu(P)=0},
    m=min{nu(X):X in E,min_i U_i(X)<=0}.

AllNever supplies feasibility; source points need not be realized by actual
laws. Escaping finite mass is never renamed Never.

**Theorem.** Suppose A_Z>0 and X attains m with payoff

    U(X)=(-A0,-B0,C0,D0), A0,B0,C0,D0>0.

Starting at X, extract successive actual continuation rows. After finitely
many rows, an incoming support013 must occur. Before that first triple,
all rows alternate01,03 and owner2's cap stays strictly positive. A finite
exit at a zero1 tail is impossible, regardless of how long the preceding
head is. No minimizing property is assigned to any continuation.

The theorem excludes an entire remaining source-path mode on(R). It does
not settle the later013 continuation, the negative-owner2 source case,
nonnegative minimum sources, the whole opposed-pair arm or arbitrary Fin4.
It is ordinary mathematics, not a new Lean verification.

## Conjecture-facing change and strategic inputs

The new step varies a final actual singleton1 law and reconstructs EVERY
preceding Nash row. A same-tail comparison would give the wrong Never
change even in the exact boundary example below. Complete source access,
strict quiet margins and a sign for the WHOLE head's Never are proved;
none is supplied as a strategic certificate. A finite head is only the
actual configuration excluded by contradiction, not an assumed producer.
The polynomial certificate covers all possible lengths by a suffix bound,
not a selected finite search depth.

## Actual prefixes and the selected source

For first hazards q let h=product_i(1-q_i), H_i=product_(j!=i)(1-q_j),
Q_i be forced-Quit payoff and P_i the passive contribution on nonempty
opponent coalitions. Full behavioral caps and prescribed payoff satisfy

    B'_i=max(Q_i,P_i+H_i B_i),
    U'_i=q_i Q_i+(1-q_i)P_i+h U_i,N'_i=(1-q_i)N_i.

With d_i=B_i-U_i>=0 their nonnegative decomposition is

    d'_i=q_i(B'_i-Q_i)+(1-q_i)(B'_i-P_i-H_iB_i)+h d_i.

Thus every E point admits limiting incoming hazards with

    Q_i<=u_i,q_i(u_i-Q_i)=0.                     (IN)

For a proper row its actual conditional tails have an E limit and
u_i=P_i+H_i w_i. No law realizing a closure point is needed. A point with positive nu has h>=nu, so its incoming row is automatically
proper and the genuine tail retains original N by conditioning.

Moving a smallest original Never mass to one finite date gives an absorbing
profile. Its own cap stays fixed; four prescribed payoffs and three other
caps each change by at most twice the reward bound times that mass. Hence
A_Z<=D+14M nu^(1/4), also on C. Thus A_Z>0 makes nu>0 on E and m>0.
Prefixing any Nash root at U(X) gives another E point. A sure row would
contradict this positive-Never bound. A nonzero proper root with a
nonpositive successor coordinate would lower m; AllContinue is not Nash
at a negative input because solo Quit pays0. Therefore every root has
strictly positive successor payoffs.

Since Q1,Q2<=0, all these roots have q1=q2=0. Singletons have active
output0, and sure03 is excluded by its opposed joining comparisons:
sure0 makes3 Quit(2>1), then0 Continue(4>3); sure3 makes0 Continue.
Nash existence forces the proper03 root with odds(D0,A0). Its positive
quiet outputs give

    B0<6(A0-D0), C0>5A0+4A0D0-D0.               (AB)

On q2=0 the exact Quit polynomials are

    Q0=-q1+3q3,Q1=-7q0-q3,Q3=2q0-2q1.           (3)

At X, (IN) forces q2=0,q1>0,7q0+q3=B0. A positive q3 would require
B0>7A0+(7/2)D0, contrary to(AB). Hence the first row is01, uniquely
(B0/7,A0,0,0). At any later starting source(-A,-B,C,D) with all parameters
positive, the same algebra gives either013 or this unique01 row. Its
properness follows from positive original Never. The genuine01 tail is

    h=(1-B/7)(1-A),
    w=(A/(1-A),-B/(7-B),
       (C-B/7-3A)/h,(D+A-B/7)/h).               (4)

The first01 inequality B<=7A+(7/2)D gives w0,w3>0,w1<0. The next lemma
keeps w2>0 at EVERY such cut, not merely at the two-cut endpoints.

## A global nonlinear ledger forces finite escape from pair alternation

Start at X and rename its parameters A,B,C,D. At any later
source (-A,-B,C,D), all positive, whose first row is01, (IN) gives
B<=7A+(7/2)D and(4). If w2>0, its unique next incoming row has

    r1=max(0,(-2w0-6w1-21w3)/44),
    r0=w3/2+r1,r2=0,r3=(w0+r1)/3.

Thus either its support is013, or it is03. The latter pair is proper:
sure3 would make0 prefer passive4 to Quit3; sure0 and prescribed payoff3
would force sure3. It has r0=w3/2,r3=w0/3, so A<3/4,w3<2.
With k=(1-w3/2)(1-w0/3), its genuine E tail is

    u'=(-A',-B',C',D'),
    A'=A/(3-4A), D'=w3/(2-w3),
    -B'=(w1+3w3-2w0)/k,
    C'=(w2-w3/2+5w0/3)/k.                       (6)

No all-bad condition or minimum is assigned to this tail.
Let H=hk and R_n be the product of the preceding two-cut survivals,
R_0=1. Put f=5A/4+3B/8-5D/4 and W=C-f. Direct substitution in(4),(6)
gives the exact identities and bounds

    H W'=W-AB/56,
    H A'<=(1/3)A,H D'<=(A+D)/2,
    H B'=((4-3A)B)/7-A-3D>=-A-3D.              (7)

These use only proper pair cuts and positive A,B,D, even when B'<=0.
Write F_n=R_n A_n,E_n=R_n D_n. Then

    F_n<=A0/3^n,
    E_n<=D0/2^n+3A0(2^-n-3^-n),
    sum_(k<n)R_k A_k B_k/56<3A0/16.             (8)

The last bound uses B_k<7, which proper01 supplies. The initial(AB) bounds
give W0>3A0/2+5D0/2. Hence R_nW_n>21A0/16+5D0/2. At any endpoint n>=1,
including one with B_n<=0, the last two inequalities in(7) give

    R_nf_n>=-F_(n-1)-(7/4)E_(n-1)
             >=-29A0/24-7D0/4.

For the last inequality use(8); the A coefficient is
[21*2^-k-17*3^-k]/4, maximized at k=1. Consequently

    R_n C_n>5A0/48+3D0/4>0.                     (9)

The intermediate01 tail must also keep owner2 positive. For n>=1 and B_n>0,

    R_n(C_n-B_n/7-3A_n)
       =R_nW_n+(13/56)R_nB_n-(7/4)F_n-(5/4)E_n
       >5A0/48+15D0/8>0.                       (10)

Indeed(8) bounds its subtracted cost by5D0/8+29A0/24; its A coefficient
(15/4)2^-n-2*3^-n is maximized at n=1 on n>=1. At n=0 positivity follows
from(AB). Apply these estimates up to the first hypothetical loss of
owner2 positivity: all preceding pair formulas are valid, and(9),(10)
contradict either location of that first loss. This proves positivity at
EVERY cut, without an assumed invariant cone.

An infinite alternating path is impossible. Let M bound the fixed table
and all source payoffs. Equation(9) gives R_n>gamma/M with
 gamma=5A0/48+3D0/4>0. Since each H_n<=1-A_n, this forces sum A_n<infinity
and A_n->0, regardless of the source's original Never. Set b=B/A,d=D/A.
The first01 gate, B'>0 in(6), and the second03 quiet inequality imply

    (7+21d)/(4-3A)<b<=7+(7/2)d,
    0<d<3,0<b<35/2,(27-4A)b<=161+147d.

For ell=b-6d-6 these give ell>-24 and, when A<=1/20000, ell<=-1/54.
The exact recurrence is

    ell'-3ell=-3A P/Q,
    Q=2A^2b-Ab-7Ad-21A+14,
    P=2Ab^2-12Abd-14Ab-b^2-bd+5b+42d^2+56d+14.

On that small-A region Q>13 and |P|<1100 by the displayed b,d bounds.
Thus |ell'-3ell|<33/2600<1/54 and ell'<2ell. Eventually A remains in
this region, so ell tends to minus infinity, contradicting ell>-24.

At every two-cut endpoint, A',D'>0 and C'>0. An endpoint with B'<0 has
positive payoffs1,2 and negative payoff0, contradicting(IN). If B'=0 the
path has reached the stated zero1 exit. Otherwise the next incoming row is
01 or013 by(3). The only possible interruption at the intermediate tail
is013. This proves the finite triple-or-zero exit claimed for this source.


## Cofinal pure1-prefix lemma

Suppose w is a zero-debt ACTUAL closure point for this raw family, and

    w1=0, w0,w2,w3>0,
    S1=3w3-2w0>0,
    S2=w2-w3/2+5w0/3>0.                           (CF)

Then there are a genuine zero-debt closure point Y and g>0 such that

    w_i=g Gamma_i1+(1-g)U_i(Y),
    N1(w)=(1-g)N1(Y), Nj(w)=Nj(Y) for j!=1.        (CP)

Here g<1. This is only a prescribed-payoff/original-Never relation. The
lemma does not assert that the compressed pure1 row is Nash at Y.
No literal law realizing w is assumed, and escaping finite mass is not
identified with Never.

Proof. Fix a reward bound M>=4 and let kappa=min(w0,w2,w3)>0. Choose
small delta in(0,1/8) so that

    4M delta<kappa/8, 3delta<w2/2,
    delta<S1/2, delta<3S2.

Choose epsilon>0 so that3epsilon<kappa/16. For actual approximants P_n
to w let D_n be total debt, tending to0. Their initial payoffs0,2,3 are
at least3kappa/4 for sufficiently large n. Let q_i^n(t) be conditional
hazards. Let tau_n be the first date when either

* player1's UNCONDITIONAL cumulative finite stopping mass through that
  date reaches delta; or
* q0^n(t)>=epsilon or q3^n(t)>=epsilon.

A finite-initial-segment bootstrap gives the following uniform facts before
tau_n: the unconditional cumulative stopping mass of each of players0,2,3
is O(D_n), and their literal continuation payoffs and caps remain at least
kappa/2. The constants depend on w,M,delta,epsilon, not dates or n.
Here are the estimates giving this bootstrap, rather than an assumed
uniform tightness premise.

Stop provisionally also when any non1 cumulative mass first reaches delta.
Before that provisional stop, the probability of any absorption before a
date is at most4delta. The prescribed prefix identity therefore gives
U_i^n(t)>=U_i^n(0)-4Mdelta>=kappa/2 for i=0,2,3.
The full-cap debt telescopes as a sum of nonnegative reached terms,

    D_n>=sum_(t<T) h_n(t) q_i^n(t)[B_i^n(t)-Q_i(q^n(t))],

where h_n(t) is all-player survival to date t. On the provisional region
h_n(t)>1-4delta>1/2. Since Q2<=0 identically, the reached sum of q2, and
in particular every such q2, is O(D_n). Changing q2 to0 changes either
Q0 or Q3 by at most2M q2. Before a large0/3 hazard, the fixed formulas give

    Q0<=3epsilon+2M q2, Q3<=2epsilon+2M q2.

For large n these are below kappa/4. The same debt sum now bounds all
pre-stop q0,q3 by O(D_n). Unconditional finite mass is at most the sum of
hazards. Thus a provisional stop solely caused by a non1 mass reaching
delta cannot occur: its last stage satisfies the same estimates and the
entire mass is O(D_n)<delta. This proves the stated bootstrap up to tau_n.
The q2 estimate also holds at tau_n, since its payoff buffer depends only
on prior stopping mass. In particular q2^n(tau_n)->0.

The date tau_n must be finite for all sufficiently large n. Otherwise the
same bounds hold forever; all non1 finite stopping probabilities are
O(D_n). On the event none of those players ever stops, the only possible
terminal reward to0 is Gamma01=-2, or Never0. Hence
U0(P_n)<=M sum_(i=0,2,3)Pr(tau_i finite)=O(D_n), contradicting w0>0.
This also proves that the argument retains mass escaping every fixed date:
it chooses moving tau_n from complete laws rather than dropping that mass.

Pass to a subsequence. The pre-tau_n finite mass of1 converges to some
beta in[0,delta], the macro-date hazards converge to q, and the actual
tuple at tau_n converges to W. Since its reached survival is bounded below,
the literal debt inequality gives W in E. All other pre-date finite masses
vanish. Therefore the exact prescribed prefix formula and original Never
conditioning give

    W=((w0+2beta)/(1-beta),0,
       (w2-3beta)/(1-beta),(w3+beta)/(1-beta)),
    N1(w)=(1-beta)N1(W), Nj(w)=Nj(W) for j!=1.

The choices ensure W0,W2,W3>0, and

    3W3-2W0=(S1-beta)/(1-beta)>0,
    W2-W3/2+5W0/3=(S2-beta/6)/(1-beta)>0.           (GS)

The incoming rule at W forces q2=0. If q1>0, its equality Q1=0 forces
q0=q3=0. If q0 or q3 is positive, positivity of W0,W3 forces both
positive, and q1=0; their equalities give

    q0=W3/2, q3=W0/3.

These are proper: q3=1 would make owner0 prefer passive4 to Quit3;
q0=1 would make owner3's Continue payoff1 smaller than its active payoff2,
forcing q3=1 and the same contradiction. Extracting its genuine E tail
then gives payoff0<0 and payoffs1,2>0 by(GS). Its own incoming rule
would have hazards1=2=0 and Q0>=0, an impossibility. Thus q0=q3=0.
If q1=1, W3=-1 because player1 quits surely and owner3 Continues;
so q1<1. The proper macro row gives a genuine E tail Y, including the
AllContinue case q1=0.

The large0/3-hazard stopping alternative cannot persist along this
subsequence, since its hazard would have a positive limit. Consequently
player1's cumulative mass through tau_n reaches delta, so

    g=beta+(1-beta)q1>=delta>0.

Combining the pre-date and macro-date pure1 prescribed relations proves
(CP), with g<1. This completes the cofinal lemma.



## Every later zero1 endpoint has a strict singleton representation

Suppose the finite pair chain ends after n>=1 cycles at(-a,0,c,d),a,c,d>0.
The ledger above gives more than c>0. Its weighted bounds imply

    R_n(c-3a)>5A0/48+15D0/8>0,
    R_n(c-11a/6-d/2)>35A0/144+13D0/8>0.           (Z)

For the first use the intermediate bound with B_n=0. For the second write
R_n(c-11a/6-d/2)=R_nW_n-7F_n/12-7E_n/4; the subtracted cost is at most
7D0/8+77A0/72, by the displayed F,E estimates, maximized at n=1.
These are produced bounds at a genuine continuation, not a new minimum.

At this endpoint (IN) forces only owner1 to act, with hazard s>=a and s<1:
sure1 would give payoff3=-1. If s>a, its genuine E tail already gives a
strict-slack singleton representation. If s=a, that tail is

    w=(a/(1-a),0,(c-3a)/(1-a),(d+a)/(1-a)).

It satisfies(CF), because c>3a,
3w3-2w0=(a+3d)/(1-a)>0, and
w2-w3/2+5w0/3=(c-11a/6-d/2)/(1-a)>0. Apply the cofinal lemma.
Combining its positive pure1 mass with the initial s=a yields an E tail Y
and a single pure1 row G>a, G<1, with exactly the SAME endpoint payoff
and ORIGINAL Never tuple. This row is Nash at Y: owner1 endpoints are0,
Q0=-G<-a, Q2<=0<c, Q3=-2G<d. All quiet gaps are strict. The lemma's
prescribed relation is used to check these comparisons; it was not itself
assumed to preserve Nash. Thus every zero1 exit has this representation,
without declaring the endpoint minimizing.

## Exact backward head algebra and the finite certificate

Rebuild a chronological01,03 cycle backwards from a tail(-a,-b,c,d).
The unique proper03 root followed by the unique proper01 root gives

    e=(1+a)/(1+4a), K=1-5a+b+(7+a)d,
    A=3a/(1+4a), B=7(b+6d-6a)/K,
    D=e[b+(8-a)d-9a]/K, H=e/K.                  (F)

Here H is the two-row joint Continue multiplier. Both roots are Nash only
when their quiet comparisons hold; the necessary non2 quiet numerators are

    Q03=7a+d+8ad-b, Q01=9a+(5a-4)d-b.

All omitted denominator factors are positive on a genuine proper head.
Let the final zero1 endpoint have parameters(a,0,c,d). Its own incoming
singleton row proves0<a<1. Put m_j=3^j a,L_j=1+2(3^j-1)a. After j backward
cycles the negative0 parameter is a_j=m_j/L_j. Write
(b_j,d_j,1)=V_j/P_j with V_j=(X_j,Y_j,P_j), beginning V_0=(0,d,1).
Then V_(j+1)=N_j V_j, where, with L=L_j,m=m_j,

    N_j=[7(L+4m)L,42(L+4m)L,-42m(L+4m);
          (L+m)L,(L+m)(8L-m),-9m(L+m);
          (L+4m)L,(L+4m)(7L+m),(L+4m)(L-5m)].

This is a positive scalar multiple L(L+4m) of the projective matrix in(F).
Every P_j is positive on an actual head. All components are affine in d.
The quiet polynomials are

    C03_j=7m_jP_j+(L_j+8m_j)Y_j-L_jX_j,
    C01_j=9m_jP_j+(5m_j-4L_j)Y_j-L_jX_j.

The outer all-bad bound is exactly positivity of

    G_k=6m_kP_k-L_k(X_k+6Y_k)=g0+g1 d.

Also Y_k=t0+t1 d>0. The following finite sign facts are proved by the
complete rational-arithmetic certificate below.

First, NO seven-cycle suffix is possible, WITHOUT using outer all-bad.
Substitute d=a*z,z>0. In the following table write the indicated
Y_j=pz+q and quiet polynomial C=rz+t:

| a interval | Y_j | C | Sign facts |
| --- | --- | --- | --- |
| (0,1/39] | Y7 | C03_3 | q<0,t>0,qr-tp>0 |
| [1/39,1/5] | Y6 | C01_3 | q<0,t>0,qr-tp>0 |
| [1/5,1) | Y5 | C01_2 | q<0,t>0,qr-tp>0 |

The positive combination tY_j-qC=z(tp-qr)<0 contradicts Y_j>0,C>=0.
All interior subdivision endpoints are checked. Any longer zero-ending
head contains such a last seven-cycle suffix; no outer source property is
transferred to that suffix. Thus every candidate has k<=6.

Second, under G_k>0,Y_k>0, the certificate proves g0>0,t0<0. For k>=3
it proves g0t1-t0g1<=0 on [u_k,1], where

    u1=u2=1,u3=1/10,u4=1/100,u5=1/1000,u6=1/10000.

But g0Y_k-t0G_k=d(g0t1-t0g1)>0, so necessarily a<u_k. On(0,u_k),
g1<0, giving0<d<-g0/g1. For k<=5 every quiet C=q0+q1d has
q0>0 and -g1q0+g0q1>0: it is positive at both ends of this interval,
hence throughout. Thus ALL quiet1/3 comparisons are strict. Quiet2 is
strict separately because its cap stays positive at EVERY cut and Q2<=0.
For k=6, on(0,u6) the certificate gives t1>0 and, for C03_3=q0+q1d,
q1<0,q0t1-q1t0<0. From Y6>0, d>-t0/t1, forcing C03_3<0, impossible.
Therefore1<=k<=5 and every internal quiet comparison is strict.

Finally put E_k=product_(j<k)L_j(L_j+m_j). The total joint Continue factor
of the pair head is R_k=E_k/P_k, by telescoping its projective normalizations.
For a varying final singleton hazard G over the fixed E tail Y,

    a(G)=2G-(1-G)Y0,d(G)=-G+(1-G)Y3,
    (1-G)a'=2-a,(1-G)d'=-(1+d),
    nu_whole(G)=(1-G)nu(Y)R_k(a(G),d(G)).

The numerator of (1-G)d log nu_whole/dG, after multiplication by the
positive E_kP_k, is the affine polynomial

    J_k=-E_kP_k+(2-a)(E'_kP_k-E_k partial_a P_k)
                         +(1+d)E_k partial_d P_k=j0+j1 d.

For each k<=5 the certificate proves j0>0 and j0g1-j1g0<0 on(0,u_k).
Since g1<0, J is positive at0 and at -g0/g1, hence at the actual d.
Thus the derivative of the WHOLE original Never is strictly positive.
No sign for an isolated endpoint objective is substituted for this sign.

## Reconstruct the entire head and contradict the original minimum

Take the strict-slack G>a representation at the zero1 exit. Hold its E
tail Y fixed and vary G in a small open interval. Owner1 remains indifferent,
all three last-row quiet gaps stay strict, and the endpoint retains signs
(-,0,+,+). Reconstruct all k pair cycles by(F). Every previous active
hazard was proper and every quiet comparison was just proved strict,
including owner2 via the full-path ledger. All remain so on a sufficiently
small interval by continuity of the explicit rational root formulas.

Every row is therefore still a full Nash prefix. Applying these finite
continuous prefix maps to actual approximants of Y gives genuine E points.
At the baseline their whole payoff and original Never tuple equal X's;
the compressed endpoint preserved both. The whole payoffs0,1 remain
negative after a small perturbation. Since nu(Y)>0 and the whole Never
derivative is positive, choose a slightly SMALLER G: this gives an E
point with a negative payoff and original Never strictly below m.
Contradiction. The entire finite zero1 exit is excluded. Combining this
with the finite pair escape proved above forces the first013 row stated
in the theorem. No tail has been assigned minimum-Never status.

## Complete exact coefficient certificate

The following standalone Python uses only integer and Fraction arithmetic.
Every input polynomial is produced by the displayed recursion; there are no
data files, numerical roots, sampled inequalities or CAS dependencies.
It verifies104 Bernstein sign checks and every interior NO7 subdivision
endpoint. For p(l+(u-l)t)=sum c_j t^j, its degree-n Bernstein coefficients
are beta_i=sum_(j<=i)c_j binom(i,j)/binom(n,j). A nonzero list of
nonnegative coefficients proves strict positivity inside the interval.
Weak closed-interval signs suffice where they rule out a>=u_k; all actual
remaining parameters lie in open intervals. The NO7 boundary values are
checked separately by exact rational evaluation.

```python
"""Exact whole-head zero1 certificate: length, quiet slack and Never derivative."""
from fractions import Fraction as F
from math import comb

def norm(p):
    p=list(p)
    while len(p)>1 and p[-1]==0:p.pop()
    return tuple(p)
def add(p,q):
    return norm([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0)
                 for i in range(max(len(p),len(q)))])
def scale(c,p):return norm([c*x for x in p])
def sub(p,q):return add(p,scale(-1,q))
def mul(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return norm(r)
def affine_add(p,q):return tuple(add(x,y)for x,y in zip(p,q))
def affine_scale(c,p):return tuple(mul(c,x)for x in p)
def linear_combine(coeffs,vec):
    out=((0,),(0,))
    for c,v in zip(coeffs,vec):out=affine_add(out,affine_scale(c,v))
    return out

def bernstein(p,l,u):
    """Degree-n Bernstein coefficients after a=l+(u-l)t, exactly."""
    n=len(p)-1
    power=[sum(F(p[i])*comb(i,j)*l**(i-j)*(u-l)**j for i in range(j,n+1))
           for j in range(n+1)]
    return [sum(power[j]*F(comb(k,j),comb(n,j))for j in range(k+1))
            for k in range(n+1)]

checks=0

def sign(p,want,l=F(0),u=F(1)):
    global checks
    bs=bernstein(p,l,u)
    assert any(c!=0 for c in bs)
    assert all(want*c>=0 for c in bs),(want,l,u,p)
    checks+=1

one=(1,);aa=(0,1)
# Each payoff numerator is an affine polynomial in the final d.
vec=[((0,),(0,)),((0,),(1,)),((1,),(0,))]
vecs=[vec]
labels=[]
E=(1,);Es=[E]
for j in range(7):
    L=(1,2*(3**j-1));m=(0,3**j)
    L4=add(L,scale(4,m));Lm=add(L,m)
    N=[
        [scale(7,mul(L4,L)),scale(42,mul(L4,L)),scale(-42,mul(m,L4))],
        [mul(Lm,L),mul(Lm,sub(scale(8,L),m)),scale(-9,mul(Lm,m))],
        [mul(L4,L),mul(L4,add(scale(7,L),m)),mul(L4,sub(L,scale(5,m)))]]
    labels.append((L,m))
    vec=[linear_combine(row,vec)for row in N]
    vecs.append(vec)
    E=mul(E,mul(L,Lm));Es.append(E)

bounds={1:F(1),2:F(1),3:F(1,10),4:F(1,100),5:F(1,1000),6:F(1,10000)}
for k in range(1,7):
    X,Y,P=vecs[k];L=(1,2*(3**k-1));m=(0,3**k)
    G=linear_combine([scale(-1,L),scale(-6,L),scale(6,m)],[X,Y,P])
    g0,g1=G;t0,t1=Y;up=bounds[k]
    sign(g0,1);sign(t0,-1)
    if k>=3:
        # G>0 and Y>0 imply d*(g0*t1-t0*g1)>0.
        sign(sub(mul(g0,t1),mul(t0,g1)),-1,up,F(1))
    sign(g1,-1,F(0),up)
    quiet=[]
    for j in range(k):
        Xj,Yj,Pj=vecs[j];Lj,mj=labels[j]
        Q03=linear_combine([scale(-1,Lj),add(Lj,scale(8,mj)),scale(7,mj)],
                           [Xj,Yj,Pj])
        Q01=linear_combine([scale(-1,Lj),sub(scale(5,mj),scale(4,Lj)),scale(9,mj)],
                           [Xj,Yj,Pj])
        quiet.extend([(j,'03',Q03),(j,'01',Q01)])
    if k<=5:
        for j,kind,(q0,q1) in quiet:
            # Quiet margin is positive at d=0 and at G=0.
            sign(q0,1,F(0),up)
            sign(sub(mul(g0,q1),mul(g1,q0)),1,F(0),up)
        print('k=',k,'all',2*k,'quiet margins strictly positive; a<',up)
    else:
        # On the remaining small-a interval, Y>0 makes Q03 at state3 negative.
        q0,q1=next(Q for j,kind,Q in quiet if j==3 and kind=='03')
        sign(t1,1,F(0),up);sign(q1,-1,F(0),up)
        sign(sub(mul(q0,t1),mul(q1,t0)),-1,F(0),up)
        print('k=6 impossible: positive final D contradicts quiet03 at state3')
# Whole Never derivative after re-solving the complete head.
def derivative(p):return norm([j*p[j]for j in range(1,len(p))] or [0])
def value(p,x):
    out=F(0)
    for c in reversed(p):out=out*x+c
    return out
for k in range(1,6):
    X,Y,P=vecs[k];E=Es[k];up=bounds[k]
    L=(1,2*(3**k-1));m=(0,3**k)
    g0,g1=linear_combine([scale(-1,L),scale(-6,L),scale(6,m)],[X,Y,P])
    j0=add(sub(mul((2,-1),sub(mul(derivative(E),P[0]),mul(E,derivative(P[0])))),mul(E,P[0])),mul(E,P[1]))
    j1=mul((2,-1),sub(mul(derivative(E),P[1]),mul(E,derivative(P[1]))))
    sign(j0,1,F(0),up)
    sign(sub(mul(j0,g1),mul(j1,g0)),-1,F(0),up)
    print('k=',k,'whole Never derivative strictly positive')
# Seven-cycle suffix: no outer ALLBAD hypothesis is used here.
for dj,kind,j,l,u in [(7,'03',3,F(0),F(1,39)),
                       (6,'01',3,F(1,39),F(1,5)),
                       (5,'01',2,F(1,5),F(1))]:
    Xj,Yj,Pj=vecs[j];Lj,mj=labels[j]
    coeff=([scale(-1,Lj),add(Lj,scale(8,mj)),scale(7,mj)]if kind=='03'
           else[scale(-1,Lj),sub(scale(5,mj),scale(4,Lj)),scale(9,mj)])
    t,r=linear_combine(coeff,[Xj,Yj,Pj]);q,p=vecs[dj][1]
    p=mul(p,(0,1));r=mul(r,(0,1))  # endpoint d=a*z
    cross=sub(mul(q,r),mul(t,p))
    for poly in [scale(-1,q),t,cross]:
        sign(poly,1,l,u)
        if l>0:assert value(poly,l)>0
        if u<1:assert value(poly,u)>0
    print('NO7 interval',l,u,'D',dj,'quiet',kind,j)
print('Exact Bernstein sign checks passed:',checks)
```

## Exact boundary: endpoint and whole-head Never move oppositely

Actual zero debt, positive Never and all-bad roots alone do not rule out a
one-cycle zero1 exit. Complete(R) by setting all free entries0 except

    Z0(02)=-10,Z1(12)=-8,Z(23)=(244786/7,79978/7,-10,8),

and set all seven owner2 participant nonsingletons to-10. Owners0,1 Never
in a final tail; owners2,3 independently have date-n masses f_i2^(-n-1),
f2=7/225,f3=1/1000, and retain original Never masses1-f_i.
Pair rewards are twice their passive singletons, so every deadline and
Never gives owners2,3 values -1/200,28/225.
For an outsider let g_j=Gamma_ij,K=Z_i(23),J_j=Z_i(ij),J23=Z_i(i23)=0.
The exact geometric sums are

    e_i=g2f2+g3f3+(f2f3/3)(K-2g2-2g3),
    V_i(n)-e_i=2^-n L_i+f2f3*4^-n M_i,
    L_i=(J2/2-g2)f2(1-f3)+(J3/2-g3)f3(1-f2),
    M_i=(J2+J3+J23)/4-(g2+g3+K)/3.

They give e0=19/90,e1=0,
L=(-109/45000,-1417/225000),M=(-326421/28,-106719/28), all negative.
Thus the actual tail has U=B=e=(19/90,0,-1/200,28/225), covering every
behavioral replacement by mixture over deadlines and Never.
Prepend singleton1 hazard g=1/10, obtaining
z=(-1/100,0,591/2000,3/250). Its quiet Quit offers -1/10,-1,-1/5 are
strictly below the Continue payoffs. Next prepend03 hazards
(3/253,0,0,1/101), giving w=(3/101,-300/25553,12851/51106,6/253), then
01 hazards(300/25853,3/104,0,0), giving

    u=(-3/104,-2100/25853,1825705/5377424,14847/2688712),
    N=(25250/25853,909/1040,218/225,999/1010),
    nu=10997991/13443560>0.

The active equalities hold by(F). At03 the quiet1 gap is r0+7r3>0;
at01 the quiet3 output is positive and Q3=2p0-2p1<0. Both quiet2 outputs
are positive, so all three rows are actual full-cap Nash prefixes. This
is a genuine one-cycle zero1 exit. Its parent source margins are

    6(A-D)-B=1518/25853>0,
    C-(5A+4AD-D)=874561/4369157>0.

Every auxiliary root at u is bad. Owner2 strictly Continues, since its
endpoint Quit-minus-Continue gaps are -C,-11,-13,-5,-14,-6,-10,-10.
On q2=0, proper01/13 would need positive input0 or negative input3.
A proper013 root would satisfy x-y=D,x+7z'+8xz'=B, so z'<B/7<A,
contradicting y-z'+2yz'=-A. Sure3 forces1,0 then3 Continue;
sure0 forces3 Quit unless1 is sure, reducing to that case; sure1 forces
0 Quit and then1 Continue. Singletons and AllContinue fail at the nonzero
inputs. The unique remaining03 root has odds(D,A), with all outputs
positive by the two margins. This is the complete root census.

Hold the actual final tail fixed and vary g, recomputing both earlier rows.
All quiet comparisons are strict at1/10. The complete three-row Continue
multiplier is

    T(g)=10125(g-1)(199g+71)
             /[(398g+7)(50347g²+372886g-58733)],
    T'(1/10)=2073852353125/225911631842>0.

Decreasing g lowers the whole Never while preserving Nash and negative
parent payoffs, so this source is NONMINIMAL. Increasing g would lower the
isolated endpoint's Never while raising the whole profile's Never. This
checks the direction of the joint revision and demonstrates why the entire
head must be included. The game already has an absorbing pure3 Nash profile:
owners0,1 prefer passive4,6 to joining3,-1, owner2 prefers -5 to -10,
and owner3 gets solo0 either way. Thus A_Z=0; no new UE-class or positive-gap
counterexample claim is attached to this boundary test.

## Source correspondence, adapter and Lean handoff

Existing prefix ingredients are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`,
`quittingTerminalDeviationDebt_nonneg` and
`quittingTerminalDeviationDebt_rootThenContinuation_eq`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`), and
`quittingTerminalPayoff_rootThenContinuation_eq`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`).
They price every complete behavioral replacement. The cofinal proof
reproduces the positive-buffer charge-and-compress estimates it needs.
The new mathematics consumes the inherited zero1 exit by a produced
whole-head variation, including strict internal margins and its objective
sign; a frozen-head obstacle test does not supply that conclusion.

A formal theorem should take raw(R), A_Z>0 and a selected negative
minimum-Never source with the stated strict signs. It should derive(AB),
produce finite actual cuts and return the first013 branch. Intermediate
lemmas should expose the charged ledger, cofinal pure1 relation, polynomial
recurrence and exact finite coefficient certificates, then the continuous
whole-head reconstruction. Neither source realization, tail minimality,
a favorable derivative nor a finite head-length hypothesis belongs in the
raw assumptions. The suffix bound concerns only these alternating heads
ending at zero1; it is not a finite-period normal form for quitting games.
The semantic output is a strict narrowing of actual counterexample sources.
The013 continuation and all broader Fin4 obligations remain open.
