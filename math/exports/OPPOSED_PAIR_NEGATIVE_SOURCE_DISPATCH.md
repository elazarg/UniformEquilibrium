# Negative opposed-pair sources: two entry cases and finite pair escape

## Exact statement

There are four players0,1,2,3. Native rewards Z_i(S) are finite real numbers
on nonempty quitting coalitions S, with own-singleton rewards zero. Live
play and Never pay zero. Strategies are independent complete stopping laws
on natural dates plus a distinct Never point. One unilateral deviation may
replace an owner's entire law; no public correlation is used.

Fix the singleton matrix Gamma_ij=Z_i({j}) to be

    Gamma=[0,-2,-5,4;-6,0,-4,6;1,3,0,-5;1,-1,4,0].

Require Z_i(S)<=0 whenever i in S and i in{1,2}. Fix the following
thirteen nonsingleton entries; the other31 remain arbitrary subject to
these signs, with eleven sign-bounded and twenty unrestricted:

    Z0(01)=-1,Z0(03)=3,Z1(01)=-7,Z1(13)=-1,
    Z3(03)=2,Z3(13)=-2,Z0(013)=2,Z1(013)=-8,Z3(013)=0,
    Z2(01)=4,Z3(01)=0,Z1(03)=0,Z2(03)=-4.          (R)

For actual profiles retain prescribed terminal payoff U, full behavioral
response cap B, literal-Never response e and ORIGINAL marginal Never
probabilities N. Put D=sum_i(B_i-U_i), nu=product_i N_i. Let C be the
compact closure of these bounded tuples and E=C intersect{B=U}. Define

    A_Z=inf{D(P):P actual and nu(P)=0},
    m=min{nu(X):X in E,min_i U_i(X)<=0}.

AllNever makes the minimum feasible. No compact source is assumed attained
by an actual law. Original Never never includes finite mass escaping dates.

**Theorem.** Assume A_Z>0 and let X attain m with min_i U_i(X)<0.
Then u=U(X) satisfies exactly one of the following cases:

1. u=(-A,-B0,C0,D0), all four parameters positive,
   B0<6(A-D0), C0>5A+4AD0-D0. Its first incoming actual row is uniquely
   (B0/7,A,0,0), and its genuine zero-debt tail has signs(+,-,+,+).
2. u=(-A,B0,-C0,D0), where A,B0,D0>0,C0>=0,
   A<1/4 and D0>5A/(1-4A).

In particular a selected negative minimum-Never source cannot have u1=0;
the zero2 face C0=0 in case2 remains allowed. In case1, repeatedly cut
rows01 and03 whenever these are the incoming supports. After finitely many
cuts, a surviving path must encounter support013 or a two-cut starting
source with u1=0. The owner2 cap stays strictly positive at every cut.
Those later zero1 sources are NOT asserted minimizing and remain possible
exit cases. All statements hold for every free completion in(R).

This is a strict reduction of the negative minimum-Never source obligation,
not a UE existence theorem or a closure of the full opposed-pair arm.

## Conjecture-facing change and strategic inputs

A hypothetical native positive absorbing gap produces m>0 and the source
used in this theorem. The result excludes the entire owner1-zero negative
minimum face, removes013 as the first incoming support in case1, and rules
out infinite pair alternation and loss of the positive outsider along that
case's actual continuation chain. The proof follows moving dates and full
caps, including finite mass escaping every fixed date. No source realizer,
selected root, supplied tail, clock tightness or minimizing tail is assumed.
The cofinal charge-and-compress argument below is used to consume this
specific source face; it is not claimed as a new general compression method.

## Prefix identities and the produced all-bad condition

For product first hazards q let h=product_i(1-q_i),
H_i=product_(j!=i)(1-q_j), Q_i be the immediate forced-Quit payoff,
and P_i the passive payoff on nonempty opponent coalitions. Exact updates
against a literal actual tail are

    B'_i=max(Q_i,P_i+H_i B_i),
    U'_i=q_i Q_i+(1-q_i)P_i+h U_i,
    N'_i=(1-q_i)N_i.                             (1)

They compare all finite deadlines and Never, hence all complete behavioral
replacements. For d_i=B_i-U_i>=0,

    d'_i=q_i(B'_i-Q_i)+(1-q_i)(B'_i-P_i-H_iB_i)+h d_i. (2)

Every E point therefore has limiting incoming hazards satisfying

    Q_i<=u_i, q_i(u_i-Q_i)=0.                    (IN)

This follows from actual approximants and legal Quit-now/Continue-then-
prescribed deviations; it requires neither positive Never nor properness.
Only after a row is proved proper do its actual conditional tails have
an E limit, by(2), with u_i=P_i+H_i w_i. Original N divides by each
positive own Continue probability. Prefix maps also preserve C.

For completeness, moving a smallest owner's Never mass to one finite
date makes an actual profile absorbing. Its own cap stays unchanged,
while four prescribed payoffs and three other caps change by at most
2M times that mass, for M>=1 bounding rewards. Hence, also on C,

    A_Z<=D+14M nu^(1/4).

Thus A_Z>0 forces nu>0 on E and m>0. If q is any auxiliary Nash root at
u=U(X), prefixing X yields another E point. A sure row would have nu=0,
contradicting the preceding bound. If its successor had a nonpositive
coordinate, a nonzero proper q would lower nu below m. AllContinue cannot
be Nash at a negative annotation because unilateral solo Quit pays zero.
Therefore EVERY Nash root is proper and has all successor coordinates
strictly positive. This is the all-bad condition; it is produced by the
source selection, not an additional strategic premise.

## Exhaustive source signs and the first row

Since Q1,Q2<=0 globally, a bad Nash root cannot have positive hazard at
owners1,2. A singleton has active output0, and AllContinue is not bad.
The remaining support03 is proper: sure3 makes0 prefer Continue(4>3);
sure0 makes3 Quit(2>1), after which0 prefers Continue. Finite-game Nash
existence therefore forces a unique proper03 root. With odds x at0,z at3,
its indifference equations give u0=-z=-A<0,u3=x=D0>0. Its quiet outputs,
with h_*=[(1+A)(1+D0)]^-1, are

    h_*(u1+6A-6D0), h_*(u2+D0-5A-4AD0).

Their positivity gives

    u1>6(D0-A), u2>5A+4AD0-D0.                  (AB)

Both u1,u2 positive are impossible at an E source: (IN) forces q1=q2=0,
so Q0=3q3>=0 contradicts u0<0. Both nonpositive are impossible too:
u1<=0 implies D0<A, whereas u2<=0 implies A<1/4 and
D0>5A/(1-4A)>A. Exactly one is nonpositive. It remains to exclude u1=0.

For strict case1, q2=0 and the fixed polynomial cancellations give

    Q0=-q1+3q3,Q1=-7q0-q3,Q3=2q0-2q1.           (3)

Thus q1>0,7q0+q3=B0. If q3>0 then q0>0 and
B0>7A+(7/2)D0, incompatible with B0<6(A-D0). Hence the unique row is
p=(B0/7,A,0,0). It is proper. Indeed q0=1 would make owner1 prefer
Continue(-6) to its active Quit(-7); q1=1 would force q0=1 by prescribed
payoff0=-2+q0 versus active output-1. No off-path tail is used here.
Its genuine E tail is

    h=(1-B0/7)(1-A),
    w=(A/(1-A),-B0/(7-B0),
       (C0-B0/7-3A)/h,(D0+A-B0/7)/h).           (4)

The bounds(AB) make w0,w2,w3 positive and w1 negative.

If u1=0 instead, (IN) forces a singleton1 row q1=b>=A. It is proper:
b=1 would make u3=Gamma31=-1. Its E tail has w1=0,w0,w3>0. If b>A,
increasing b slightly keeps every quiet comparison strict, preserves
owner1 indifference and the negative0 payoff, and lowers positive nu,
contradicting m. Thus b=A and

    w=(A/(1-A),0,(C0-3A)/(1-A),(D0+A)/(1-A)).     (5)

Here(AB) gives D0<A and C0>5A+4AD0-D0>4A.

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


## The zero1 minimum-source face is impossible

Rename C0,D0 locally as C,D. Let X minimize original joint Never over E with min U<=0, and suppose
nu(X)=m>0, all its auxiliary roots are bad, and

    U(X)=(-A,0,C,D), A,C,D>0.

The preceding exact source argument gives first pure1 hazard A, with
0<A<1, and a genuine E tail w satisfying

    w=(A/(1-A),0,(C-3A)/(1-A),(D+A)/(1-A)).

The all-bad03 root inequalities imply D<A and C>5A+4AD-D. Thus(CF)
holds: S1=(A+3D)/(1-A)>0, while

    S2=[C-11A/6-D/2]/(1-A)>0,

because its numerator exceeds19A/6+4AD-3D/2>5A/3.
Apply the cofinal lemma to get g>0,Y in E and the prescribed relation(CP).
Combining the initial A-head gives a single pure1 row with

    G=A+(1-A)g>A

whose prescribed payoff equals U(X) and original Never coordinates equal
those of X. It is Nash at Y: owner1 has both endpoints0; for owner0 the
Quit offer is -G<-A=U0(X); owner2 has Q2<=0<C, and owner3 has
Q3=-2G<D. The Continue endpoints are exactly U(X) by(CP). The ordinary
continuous prefix map on actual approximants to Y therefore gives a new
E point with that same prescribed payoff and original Never tuple.

Now increase G slightly, holding Y fixed. All the displayed quiet gaps
are strict, the negative0 payoff remains negative, and owner1 still has
both endpoints0. Thus the new point remains in E with min U<0, while its
joint original Never strictly decreases because nu(X)>0. This contradicts
the definition of m. Hence this zero1 all-bad negative m-source cannot
occur. No minimizing property was assigned to w,W or Y.

## A global nonlinear ledger forces finite escape from pair alternation

Start in strict case1 and rename its parameters A,B,C,D. At any later
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
is013. This proves the finite triple-or-zero exit claimed in case1.

## Exact boundary tests

The sign bounds are nonvacuous as numerical constraints: for example
(-1/100,-1/100,1/10,1/200) satisfies the strict case1 bounds; the
case2 bounds permit (-1/10,6,-1/100,1). No E realization of these numerical
tests is asserted. The zero1 proof requires minimum-Never, as the following
exact actual source demonstrates.

Complete(R) by setting every free entry to0 except

    Z0(02)=-10,Z1(12)=-8,Z(23)=(254106/7,79708/7,-10,8),

and set all seven owner2 participant nonsingletons to-10. In a tail let0,1
Never, and let2,3 have independent date-n masses f_i*2^(-n-1), with
f2=7/240,f3=1/1000 and respective original Never masses1-f_i.
Their pair rewards equal twice their passive singleton rewards, so every
finite deadline and Never gives them -5f3 and4f2 respectively.
For outsider i let g_j=Gamma_ij,K=Z_i(23),J_j=Z_i(ij),J23=Z_i(i23)=0.
Summing the geometric laws gives

    e_i=g2 f2+g3 f3+(f2 f3/3)(K-2g2-2g3),
    V_i(n)-e_i=2^-n L_i+f2 f3*4^-n T_i,
    L_i=(J2/2-g2)f2(1-f3)+(J3/2-g3)f3(1-f2),
    T_i=(J2+J3+J23)/4-(g2+g3+K)/3.

Substitution yields e0=19/90,e1=0,
L=(-233/96000,-3029/480000),
T=(-1016543/84,-106359/28). Thus all finite outsider replies are below
Never, and the actual tail has U=B=e=(19/90,0,-1/200,7/60).
A singleton1 first row g=1/10 is Nash above it and gives

    u=(-1/100,0,591/2000,1/200),
    N=(1,9/10,233/240,999/1000),nu=698301/800000>0.

Its quiet Quit offers are -1/10,-1,-1/5 at0,2,3, all strictly below u.
Every auxiliary root at u is bad. Owner2's endpoint Quit-minus-Continue
gaps, at empty and opponent sets0,1,3,01,03,13,013, are
(-591/2000,-11,-13,-5,-14,-6,-10,-10), all negative. Hence q2=0. If
q0 or q3 is positive, owner1 strictly Continues since its gap is
-q0-7q3. If both vanish, owner0 has strictly positive gap
A+(1-A)q1, impossible for a root with q0=0. Thus q1=q2=0 at every root.
AllContinue, singletons and sure03 are excluded as above. The unique
proper root has odds(D0,A)=(1/200,1/100). Its four outputs are positive:
3A/(1+A),2D0/(1+D0),h_*6(A-D0),h_*(2503/10000).

This actual all-bad zero1 source is NONMINIMAL: its first g=1/10>A=1/100
has strict quiet0 slack, and increasing g slightly reduces nu while keeping
zero debt and payoff0 negative. The minimum premise therefore cannot be
replaced merely by actual zero debt, positive Never and all-bad roots.
The same completed game is already stationary-covered: f2=f3=1 gives
constant hazards1/2 at2,3; the outsider L terms vanish and T stays negative.
No new UE reward-class credit is assigned to this boundary example.

## Source correspondence, adapter and Lean handoff

The existing prefix ingredients are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`,
`quittingTerminalDeviationDebt_nonneg` and
`quittingTerminalDeviationDebt_rootThenContinuation_eq`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`), and
`quittingTerminalPayoff_rootThenContinuation_eq`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`).
They price complete behavioral replacements. The new ordinary mathematics
is their concrete selected-source consumption at zero1, the exhaustive
source signs and the nonlinear whole-path ledger. No Lean build is claimed.

A formal theorem should take raw(R), native A_Z>0 and a negative minimizer
of the compact nonpositive-payoff E restriction. It should derive all-bad,
produce the two-case dispatch, and exclude u1=0; no desired source property
or clock tightness belongs in the raw data. Separate lemmas should expose
moving-cut reached-debt estimates, pure1 compression with original N,
and the charged pair ledger. All continuations are actual closure limits.
The semantic consumer is restriction of every selected negative source in
a hypothetical counterexample. No UE producer for the remaining cases is
supplied. Case2, later013/zero1 exits, nonnegative source minima and arbitrary
Fin4 remain open. No global minimum is assigned to an extracted tail.
