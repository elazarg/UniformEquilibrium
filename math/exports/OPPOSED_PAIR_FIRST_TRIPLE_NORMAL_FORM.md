# Two first-triple histories and their remaining continuation caps

## Exact statement

Four players0,1,2,3 use independent complete stopping laws on natural dates
and a distinct Never point. The first nonempty quitting coalition ends play;
live play, Never and own-singleton rewards are zero. All coalition rewards
are finite. Write Z_i(S) for player i's reward at coalition S and
Gamma_ij=Z_i({j}). One unilateral deviation may replace an entire law. Fix

    Gamma=[0,-2,-5,4;-6,0,-4,6;1,3,0,-5;1,-1,4,0].

Require every participant reward of owners1,2 to be nonpositive, and fix

    Z0(01)=-1,Z0(03)=3,Z1(01)=-7,Z1(13)=-1,
    Z3(03)=2,Z3(13)=-2,Z0(013)=2,Z1(013)=-8,Z3(013)=0,
    Z2(01)=4,Z3(01)=0,Z1(03)=0,Z2(03)=-4.          (R)

All31 other nonsingleton entries are arbitrary subject to those signs.
For actual play retain prescribed payoff U, full behavioral response cap B,
literal-Never response e and ORIGINAL Never marginals N. Let C be their
compact closure and E={X in C:B=U}. Set

    D=sum_i(B_i-U_i), nu=product_i N_i,
    A_Z=inf{D(P):P actual,nu(P)=0},
    m=min{nu(X):X in E,min_i U_i(X)<=0}.

Consider A_Z>0 and a source X attaining m, with

    U(X)=(-A0,-B0,C0,D0), A0,B0,C0,D0>0.

The configuration classified here is ANY finite actual first013 entry from
X: proper incoming rows precede a first support013, all earlier rows
alternate01,03 beginning01, all two-cut starting payoffs have signs(-,-,+,+),
and owner2 remains strictly positive at EVERY preceding cut, including the
entrance to013. Every row and conditional tail belongs to the actual
zero-debt closure; no minimizing property is imposed on a tail.

**Theorem.** Every such configuration has exactly one of the words

    01 -> 013,                 01 -> 03 -> 01 -> 013.

Write its final013 hazards as(a,b,0,c) and its genuine tail payoff as
Y=(V,-E,T,F). Then a>b>0,c>0, all hazards are proper, E>F>0, and

    E=(a+7c)/[(1-a)(1-c)], F=(a-b)/[(1-a)(1-b)].

The following necessary bounds hold, without a separate quiet2 hypothesis:

    V<0          for 01 -> 013,
    V<3(E-F)     for 01 -> 03 -> 01 -> 013.       (CAP)

A first013 with negative0 at its entrance is impossible. The words refer
to consecutive physical dates, with the initial01 at date0.

## Conjecture-facing change and strategic inputs

This theorem strictly narrows the live first013 continuation obligation:
an unbounded collection of finite alternating heads reduces to two words,
and two entire continuation sectors of those words are excluded. The
immediate word must have NEGATIVE0 at its genuine tail: a low nonnegative0
tail forces a further actual013, after which one01 replacement absorbs
all three preceding rows. It also produces the passive-owner2 comparison
formerly needed by the explicit01 replacement. These are restrictions on genuine selected-source
configurations under a positive native absorbing gap, not a new reward-table
existence class or a complete013 consumer.

The input mode includes the finite first013 entry and preceding positive2
ledger. This packet classifies that mode; it does not independently prove
that every case1 source reaches it. It supplies all new bounds uniformly
for EVERY configuration in the mode, rather than assuming a favorable
strategy, stationary root, replacement row or variation. In particular
stationary shadow rows and the whole-head replacement are constructed below
from the raw entries and the genuine tail. Fin4, the negative-V immediate
and low-V four-row sectors, negative-owner2 sources and arbitrary other
reward families remain open.

## Actual-source semantics and the original minimum

There is one live history before absorption. Independent behavioral
randomization is therefore represented by independent stopping laws; there
is no mediator, public coin, observation of another owner's random seed,
or bounded-memory restriction. Complete deadlines and Never generate all
unilateral replies by mixtures and limits. All suprema below price these
full replies, rather than a selected finite collection of deadlines.

For a first hazard vector q write h=product_i(1-q_i),
H_i=product_(j!=i)(1-q_j), Q_i for forced-Quit payoff, and P_i for the
passive contribution on nonempty opponent coalitions. The prefix identities
are

    B'_i=max(Q_i,P_i+H_i B_i),
    U'_i=q_i Q_i+(1-q_i)P_i+h U_i,
    N'_i=(1-q_i)N_i.

With d_i=B_i-U_i>=0 the exact decomposition is

    d'_i=q_i(B'_i-Q_i)+(1-q_i)(B'_i-P_i-H_iB_i)+h d_i.

Every term is nonnegative. Hence any limiting incoming row at a point
u=U=B in E satisfies

    Q_i<=u_i, q_i(u_i-Q_i)=0.                   (IN)

A proper row has genuine E conditional tails and u_i=P_i+H_i w_i.
Conversely prefixing actual approximants of w by any Nash row at w gives
an E point, by the same cap identities and continuity. This applies to
finite reconstructed words as well as one row. Original N conditions
multiplicatively through each row. Escaping finite mass is not Never.

Choose M>=1 bounding all rewards. Move a smallest original Never mass to
one finite date. The resulting profile absorbs surely; its own cap does
not change, while four prescribed payoffs and three other caps change by
at most2M times that mass. Consequently

    A_Z<=D+14M nu^(1/4)

also on C. Under A_Z>0 every E point has nu>0 and m>0. At every row
retained here h>=nu>0, so conditioning is proper. Compactness is ordinary
finite-dimensional closure of bounded coordinates; it asserts no stopping
law realizing a closure point.

At X prefixing any auxiliary Nash root gives an E point. A sure root
contradicts positive Never; a nonzero proper root with any nonpositive
output lowers m. AllContinue is not Nash at a negative input. Thus all
roots at X are proper and have strictly positive output. Since Q1,Q2<=0,
these roots have q1=q2=0. A singleton has active output0. A sure03 root
is impossible: sure0 makes3 prefer joining2 to passive1, and then0 prefers
passive4 to joining3; sure3 makes0 prefer passive4. Finite-game Nash
existence therefore forces the proper03 root with odds(D0,A0). Its two
positive quiet outputs give

    B0<6(A0-D0), C0>5A0+4A0D0-D0.               (AB)

This is a bound at the ORIGINAL source only. On q2=0 the fixed Quit
polynomials are

    Q0=-q1+3q3, Q1=-7q0-q3, Q3=2q0-2q1.         (CORE)

Equations(IN),(AB) force the initial row01. A positive q3 would require
B0>7A0+(7/2)D0, contradicting(AB). The other actual rows in the theorem's
input mode are classified without importing(AB) to any tail.

## Exact core head algebra

At any two-cut starting source u=(-A,-B,C,D), parameters positive, whose
incoming support is01, its row is(B/7,A,0,0). Its genuine E tail w has

    h=(1-B/7)(1-A),
    w0=A/(1-A),w1=-B/(7-B),
    w2=(C-B/7-3A)/h,w3=(D+A-B/7)/h.

If its next incoming row is03, it has hazards(w3/2,0,0,w0/3), and its
genuine E tail again has negative0 and positive3. A later first013 can
therefore arise at a two-cut starting source(-a,-b,c,d), or at its next
01 tail(+,-,+,+).

Call these terminal predicates FIRST and SECOND respectively. The first-row
incoming equations give their necessary strict inequalities

    FIRST: b>7a+(7/2)d,
    SECOND: (27-4a)b>161a+147d.                    (T)

FIRST follows by solving the active013 equations Q0=-q1+3q3=-a,
Q1=-7q0-q3=-b,Q3=2q0-2q1=d, with q3>0. SECOND follows from positivity
of the extra owner1 hazard at the01 tail:
-2w0-6w1-21w3>0. The actual mode supplies w2>0, so q2=0 in
that calculation. Only necessity is used; every excluded terminal predicate
is weakened to a nonstrict inequality for the certificate.

At every terminal two-cut starting source a<1. Indeed Q0>=-1 since
q2=0; equality would force q1=1,q3=0. Prescribed payoff3 would then be
-(1-q0)<=0, contradicting d>0. Thus a lies in the entire open interval(0,1).

Reconstruct one01,03 cycle backwards from a terminal(-a,-b,c,d). Its
unique proper pair roots give

    e=(1+a)/(1+4a),K=1-5a+b+(7+a)d,
    A=3a/(1+4a),B=7(b+6d-6a)/K,
    D=e[b+(8-a)d-9a]/K.

The two necessary non2 quiet margins have positive-factor numerators

    Q03=7a+(1+8a)d-b,
    Q01=9a+(5a-4)d-b.                             (Q)

All denominators are positive along the genuine proper chain. These
identities use only the fixed core entries, not any free reward coordinate.

## Polynomial recurrence with arbitrary nonzero b

Normalize terminal b=a*beta,d=a*delta, with beta,delta>0. Put

    L_j=1+2(3^j-1)a,m_j=3^j a.

The scalar after j backward cycles is a_j=m_j/L_j. Let V_j be a3-by3
polynomial matrix acting on(beta,delta,1), with V_0=diag(a,a,1). Its rows
are the numerators of b_j,d_j and their common normalization. Set

    V_(j+1)=N_j V_j,
    N_j=[7(L+4m)L,42(L+4m)L,-42m(L+4m);
          (L+m)L,(L+m)(8L-m),-9m(L+m);
          (L+4m)L,(L+4m)(7L+m),(L+4m)(L-5m)].

Every denominator V_j[2] evaluated at the actual endpoint is positive.
Define the following rows of affine-polynomial inequalities in beta,delta:

    D_j=V_j[1],
    Q03_j=-L_j V_j[0]+(L_j+8m_j)V_j[1]+7m_jV_j[2],
    Q01_j=-L_j V_j[0]+(5m_j-4L_j)V_j[1]+9m_jV_j[2],
    AB_j=-L_jV_j[0]-6L_jV_j[1]+6m_jV_j[2],
    FIRST=(1,-7/2,-7),SECOND=(27-4a,-147,-161).

D_j is positive, the quiet rows are nonnegative, and AB_k is positive
ONLY when j=k is the original outer selected source. No AB statement is
imposed on an inherited suffix. FIRST and SECOND are nonnegative necessary
terminal predicates, after dividing(T) by positive a.

## Exact three-row Farkas certificates

For three rows R1,R2,R3, let p and q be their beta and delta columns. Set
lambda=sgn*(p cross q), with the orientation sgn in the table below.
The weighted beta and delta coefficients cancel exactly. On the indicated
rational interval every lambda_i is nonnegative (indeed strict inside),
and the weighted constant is STRICTLY negative. Hence three nonnegative
actual inequalities would sum with nonnegative weights to a negative
number, a contradiction. No signs of individual beta/delta slopes are
assumed. Every subdivision endpoint is checked exactly.

| Exclusion | a interval | Three rows | sgn |
|---|---|---|---:|
|NO4-FIRST, no outer AB|[0,1/4]|Q03_0,D4,FIRST|-1|
|same|[1/4,1/2]|Q01_0,D4,FIRST|-1|
|same|[1/2,1]|Q01_0,D4,FIRST|-1|
|NO3-SECOND, no outer AB|[0,1/4]|Q03_0,D3,SECOND|-1|
|same|[1/4,1]|Q01_0,D3,SECOND|-1|
|one cycle, outer AB, FIRST|[0,1]|D1,AB1,FIRST|+1|
|two cycles, outer AB, FIRST|[0,1]|D2,AB2,FIRST|+1|
|three cycles, outer AB, FIRST|[0,1/4]|Q03_0,D3,FIRST|-1|
|same|[1/4,1/2]|Q01_0,D3,FIRST|-1|
|same|[1/2,3/4]|Q01_0,D3,FIRST|-1|
|same|[3/4,1]|Q01_0,D3,AB3|-1|
|two cycles, outer AB, SECOND|[0,1/8]|Q03_0,D2,SECOND|-1|
|same|[1/8,1/4]|D2,AB2,SECOND|+1|
|same|[1/4,1/2]|D2,AB2,SECOND|+1|
|same|[1/2,1]|D2,AB2,SECOND|+1|

Only0<a<1 is actual; square-bracket endpoints0,1 in the table merely
specify the closed intervals used for coefficient checks. At interior
dyadic subdivisions the weights are nonnegative and the weighted constant
is strictly negative by direct rational substitution.

The complete stdlib-Fraction-only checker printed below constructs every input row by the raw recurrence above and verifies60
Bernstein sign certificates, the exact two-column cancellation, and every
subdivision endpoint. It has no data-file inputs, CAS dependency, removed
polynomial factors, numerical inequalities or sampled root decisions.
For a univariate polynomial p, exact Bernstein coefficients on an interval
are computed by first making its affine interval substitution and then
using beta_i=sum_(j<=i)c_j binom(i,j)/binom(n,j). Nonnegative coefficients,
not all zero, prove strict positivity inside; negative signs are checked
by applying this to -p. The displayed checker passed all15 certificate rows.

## Actual-source two-pattern consumer

Let k be the number of complete01,03 cycles before the two-cut starting
source at which the first013 occurs, or before the01 row immediately
preceding a first013 at its intermediate tail.

If the terminal predicate is FIRST and k>=4, the LAST four cycles give
exactly the NO4-FIRST forbidden suffix. No original AB bound is required
there. Therefore k<=3. If k=0, original AB already forces the first01
row, contradiction. If k=1,2,3, the corresponding finite certificates
use AB ONLY at the ORIGINAL outer source and exclude FIRST. Thus the
first013 cannot have negative0 at its entrance.

For SECOND, if k>=3 its LAST three cycles give the forbidden NO3-SECOND
suffix, again without importing AB to that suffix. Thus k<=2. The k=2
outer-AB certificate excludes that case. The only possibilities are k=0
or1, namely01->013 or01->03->01->013.

Every row here is a genuine actual-closure Nash continuation in the
classified first-entry mode. Original Never coordinates are conditioned
through proper rows, never replaced by escaped finite mass. The source
restrictions are finite raw equations and comparisons at the selected
minimum-Never source. The finite first-entry mode is explicit; no favorable
replacement or orientation is assumed. The result reduces an unbounded family of preceding
actual heads to two explicit heads. This classification alone does not consume
the two remaining013 continuations.

## Exact incoming relations and source geometry

Put k=Z0(13), l=Z2(13), R=Z2(013). On q2=0 the fixed Quit polynomials are

    Q0=-q1+3q3,Q1=-7q0-q3,Q3=2q0-2q1.

The intermediate output of the final row r=(a,b,0,c) has

    w0=-b+3c>0,w1=-7a-c<0,w3=2a-2b>0,w2>0,
    E=(a+7c)/[(1-a)(1-c)],
    F=(a-b)/[(1-a)(1-b)].

The01 row immediately before013 has odds(-w1,w0). Its quiet3
comparison gives w0+w1+w3>=0. For the immediate word this is strict by
(AB), but the weak inequality suffices throughout the stationary argument:

    S=-5a-3b+2c>=0,
    c>4b, b<1/4, a<2c/5<2/5.                  (S)

The strict bounds use a>b>0 even when S=0. Also

    E-F>=E-a/(1-a)=c(a+7)/[(1-a)(1-c)]
                            >=7c/(1-c)>0.       (EF)

If V>=E-F, the active0 tail formula

    V=[b-c+(2-k)bc]/[(1-b)(1-c)]

and(EF) yield

    k<=9+1/c-8/b<9-31/(4b)<-22.                (K)

The free completion entry k is therefore necessarily strongly negative in
this source-exit halfspace.

## Two stationary families on the013 child

For0<t<6/7 let d(t)>0 be the unique root of

    f_t(d)=(t-1)d^2+(7t^2-8t-6)d+t(6-7t)=0.    (F1)

The constant term is positive, both other coefficients negative, so d(t)
is positive, unique and continuous. Moreover

    0<d(t)<t-t^2/3<t<1.                         (DB)

For the sharper bound evaluate f_t at t-t^2/3:

    f_t(t-t^2/3)=t^2(t^3-28t^2+102t-126)/9<0.

The cubic is below1+102-126<0 for0<t<1. Strict decrease of f_t on
nonnegative arguments proves(DB).

At stationary hazards(q0,q1,q3)=(t,s,d(t)), owner1's indifference is
exactly(F1). Owner3's stationary indifference factors as

    (t-s)[2(1-t)(1-s)-1]=0.

Owner0's stationary indifference sets

    k=K(s,d),
    K(s,d)=s+4-3d+(2-s)/d+(3d-4)/s.             (KS)

Thus the following are two complete families of stationary013 child Nash
profiles (each is proper, has positive absorption and compares every
complete behavioral replacement):

1. Symmetric family: s=t,0<t<6/7,k=K(t,d(t)).
2. Hyperbola family: s=(1-2t)/[2(1-t)],0<t<1/2,
   k=K(s,d(t)).

To verify the full behavioral statement, their active prescribed payoff
coordinates equal their immediate Quit payoffs by the three displayed
stationary indifferences. Opponents absorb with positive hazard, so every
finite deadline and Never has that same value. The unique fixed point of
the affine prescribed update is therefore their literal terminal payoff.
The fourth owner2, if Never, has literal payoff P2/(1-h), where

    P2=t+3s-5d+2sd-tsd+sd[(1-t)l+tR],
    h=(1-t)(1-s)(1-d).

Its Quit offer Q2 is nonpositive by the raw participant signs. If P2>=0,
this is a full absorbing four-player Nash profile, giving A_Z=0.
Consequently the standing A_Z>0 hypothesis forces P2<0 at EVERY
stationary child profile just constructed. This is an old stationary
consumer, used as a necessary raw constraint; no new existence coverage
is counted for constructing its roots.

## Two stationary roots bracket the actual triple hazard

Assume(K). The symmetric k(t)=K(t,d(t)) tends to minus infinity as t
approaches0: d(t)/t tends to1, giving k(t)=-2/t+O(1). At t=b, because
d(b)<b,

    K(b,d(b))>-2/b+3-2b>k,

where the last inequality follows from k<9-31/(4b),b<1/4.
Continuity therefore supplies a stationary symmetric root with

    0<t_-<b<a.

For the hyperbola family at t=2/5 one has s=1/6 and d(2/5)<1/6,
since f_(2/5)(1/6)=-1/12<0. Hence

    K(1/6,d(2/5))>-11>k.

As t approaches1/2, s approaches0 and d(t)<1/2 stays positive, so its
K value tends to minus infinity. Continuity supplies a hyperbola root

    2/5<t_+<1/2.

The actual a<2/5 therefore lies strictly between t_- and t_+. No
monotonicity or uniqueness of either k-selection is assumed or required.
These are finite strategic objects produced from the raw k, not supplied
certificates.

## Stationary failure bounds the free passive jackpot

For any stationary child root(t,s,d), P2<0 gives

    (1-t)l+tR<J(t,s,d),
    J(t,s,d)=[5d-t-3s-2sd+tsd]/(sd).            (JB)

At BOTH bracketing roots, in fact

    J(t,s,d)<-k/2.                              (JP)

Here is a complete exact proof of that bound. Using(KS),

    2sd(J+k/2)
      =6d-2t-4s-s^2+d(2ts+s^2)+3d^2(1-s).       (NUM)

For the symmetric root s=t, this is

    6(d-t)-t^2+3t^2d+3d^2(1-t)
      <6(d-t)+2t^2<0

by(DB). For the hyperbola root t in(2/5,1/2), substitute
s=(1-2t)/[2(1-t)] and reduce d^2 by(F1). Expression(NUM) becomes

    [-8t^3-46t^2+56t-9
      +(8t^3+58t^2-96t-11)d]/[4(t-1)^2].        (NR)

On[2/5,1/2], d>3/20: f_t(3/20) is a concave quadratic with positive
endpoint values109/2000 and1/800. The coefficient of d in(NR) is
negative there. Thus the numerator in(NR) is less than

    P(t)/20, P(t)=-136t^3-746t^2+832t-213<0.

For the last inequality put u=1/2-t in[0,1/10]. Then

    P(t)=(272u^3-1900u^2+32u-1)/2
      <=(-1872u^2+32u-1)/2<0.

The last quadratic has negative leading coefficient and discriminant
1024-7488<0. This proves(JP), including the entire hyperbola interval.

The function L(t)=(1-t)l+tR is affine. Since t_-<a<t_+, its two strict
upper bounds(JP) imply

    (1-a)l+aR<-k/2.                             (PASS)

This is the exact source-dependent free-entry bound missing from the
pointwise incoming analysis. It holds for arbitrary l,R, with no sign
restriction on either one.

## Quiet2 for the replacement is automatic

The actual triple's passive2 offer is

    P2=a+3b-5c+2bc-abc+bc[(1-a)l+aR].

Using(PASS) and the active0 expression for V gives

    P2<a+(5/2)b-(9/2)c+bc(1-a)
                            +(V/2)(1-b)(1-c)
       <(V/2)(1-b)(1-c).                        (P)

Indeed(S) makes the first four terms at most
-41a/4-17b/4+bc(1-a)<0. Since the genuine intermediate cap w2 is positive,
its actual tail coordinate T satisfies

    T=(w2-P2)/[(1-a)(1-b)(1-c)]>-V/[2(1-a)].

As a<2/5, this implies

    T+E+3V+4EV
       >E+[3-1/(2(1-a))]V+4EV>0.               (Q2)

At the genuine tail Y use the explicit01 root with odds(E,V). Its active
coordinates are negative, its quiet3 gap is F-E+V>=0, and its quiet2
Continue payoff is positive by(Q2), whereas Q2<=0. Hence it is a FULL
Nash root. Prefixing actual approximants to Y gives an E point with
strictly negative payoffs0,1 and original Never

    nu_new=nu(Y)/[(1+E)(1+V)].                    (NEW)


## Whole two-head Never comparison and contradiction

For the immediate word the original two-row multiplier is

    H2=(1-a)(1-b)(1-c)/[(1+7a+c)(1-b+3c)].

The original(AB) makes S>0; by(S),(EF),

    H2(1+E)(1+E-F)
      >(1-2c/5)^2(1+6c)^2/[(1-c)(1+19c/5)(1+3c)]>1.

The last numerator minus denominator is

    9c(16c^3-43c^2+61c+15)/25>0,

since0<c<1 and61c-43c^2>18c. Since V>=E-F,

    nu_new<=nu(Y)/[(1+E)(1+E-F)]<H2 nu(Y)=m.

The replacement is zero-debt and negative, contradicting the ORIGINAL
minimum-Never source. This proves the complete immediate013 halfspace
exclusion. No continuation was declared minimizing or all-bad.


## A third actual row excludes every remaining nonnegative0 immediate tail

Continue with the immediate01,013 word and assume V>=0. The previous
consumer excludes V>=E-F, so only0<=V<E-F needs consideration.

### Strong original-source bounds and stationary shadows

Put H0=(1-a)(1-b)(1-c)/[(1+7a+c)(1-b+3c)],Z=(1+7a+c)(1-b+3c).
Exact reconstruction gives A=(3c-b)/(1-b+3c),B=7(7a+c)/(1+7a+c),
D=(9a-b-2c)/Z. Hence c<(9a-b)/2 and
G=Z[6(A-D)-B]=7ab+bc-21ac-3c²-103a+23c>0.
Also S=-5a-3b+2c>0. Since b<a,c>5a/2, the quadratic part of G is
<7a²-20ac-3c²<0, so c>103a/23>4a. The D bound now gives b<a/23.
That quadratic part is <-121a² while23c-103a<a/2, yielding a<1/242.

Write k=Z0(13),l=Z2(13),R=Z2(013),L(t)=(1-t)l+tR,κ=2-k.
The exact equation V(1-b)(1-c)=b-c+κbc and V>=0 imply
κ>=1/b-1/c>91/(4a), so k<-22. Use the stationary family identities and bound(JP) proved above,
bracketing the actual hazard a rather than b. The positive root d(t) of (t-1)d²+(7t²-8t-6)d+t(6-7t)=0
gives stationary013 families q0=t,q1=s,q3=d(t), with s=t or
s=(1-2t)/[2(1-t)], k=K(s,d)=s+4-3d+(2-s)/d+(3d-4)/s.
The full stationary cap test and(JP) force L(t)<-k/2 at every symmetric
k-root and every hyperbola
k-root with2/5<t<1/2, by their full stationary behavioral cap tests.
Here K(t,d(t))->-infinity at0 and K(a,d(a))>-2/a+3-2a>k;
there is a symmetric root t_-<a. The hyperbola has K(2/5,d(2/5))>-11>k
and tends to-infinity at1/2, giving t_+ in(2/5,1/2).
Thus L(t)<-k/2 throughout(t_-,t_+) by affine interpolation.

### Low V forces positive2 and one more actual triple

We now use0<=V<E-F, rather than assuming a favorable sign for T.
Using L(a)<-k/2 and the active0 equation, the actual passive2 offer obeys
P2<a+5b/2-9c/2+bc(1-a)+(V/2)(1-b)(1-c).
Replace V by E-F, where E=(a+7c)/[(1-a)(1-c)],F=(a-b)/[(1-a)(1-b)].
Twice(1-a) times this upper bound is
N=2a-2a²+6b-6ab+c[-2+10a-6b-4ab+2a²b]
 <2a+6b+c(-2+10a)<2a+6a/23-6a<0.
Thus P2<0 and w2=P2+(1-a)(1-b)(1-c)T>0 gives T>0.
Directly E>29a,E>29F and E<34a; the latter uses a<1/242,c<9a/2.
For that upper bound, (1-a)(1-c)>(199/200)(49/50), while a+7c<65a/2.

The incoming rule at Y has q2=0. It forces q0,q3>0 even whenV=0:
q0=0 with q3>0 contradicts positive F since Q3=-2q1; q0=q3=0
contradicts negative1. If q3=0, active0 forces V=q1=0, and then
E/7<=q0<=F/2, impossible. Solving the active0,3 equalities, q1=0
would require E<=7F/2+V/3<E/3+19F/6, again impossible by E>29F.
Thus the UNIQUE next row is(p,q,0,r), with
q=(6E-21F-2V)/44,p=q+F/2,r=(V+q)/3.
Indeed F>(a-b)>22a/23 and q>(4E-19F)/44>97F/44>97a/46>2a;
also q>97F/44>2F.
Also q<3E/22,F<E/29, so p<(1/58+3/22)E<E/6<1/40.
Thus p<5q/4,r>=q/3,
andκq>91/2. This proper actual row supplies a genuine E tail
Z1=(W,-E1,T1,F1). Put h=(1-p)(1-q)(1-r). Exact identities give
W=[q-r+κqr]/[(1-q)(1-r)], E1=(p+7r)/[(1-p)(1-r)],
F1=(p-q)/[(1-p)(1-q)]>0. Furthermore
hW=(1-p)[q+(κq-1)r]>(39/40)[q+89r/2]>=(247/16)q>15q.
Moreover W>E1-F1 since its positive-denominator difference has numerator
r[κq(1-p)-8(1-q)]>0. No minimum is assigned to Y or Z1.

### Full01 replacement and the ORIGINAL whole Never

Since p>2a and p<1/40<2/5, the SAME stationary interval contains p.
Thus L(p)<-k/2. Its passive2 offer Π satisfies
Π<p+5q/2-9r/2+qr(1-p)+(W/2)(1-q)(1-r)
 <19q/4+(W/2)(1-q)(1-r).
Since T>0, hT1=T-Π>-Π. Consequently
h[T1+E1+3W+4E1W]>2hW-19q/4>0, using p<1/40.
At genuine Z1, use the explicit01 odds(E1,W). Its active payoffs0,1
are negative; quiet3 gap F1-E1+W>0 and quiet2 Continue value is positive,
while its Quit offer<=0. This is FULL Nash, producing an E comparison.

The old head has THREE rows, survival H0h. Exactly
h(1+E1)(1+W)=(1+6r+pr)[1-2r+(κ+1)qr]/(1-r)
 >(1+7r)(1+87r/2)>1+(101/2)r>1+(101/3)a.
Meanwhile H0^-1 increases in b,c, so it is bounded by
U=(1+23a/2)(1+619a/46)/[(1-a)(1-a/23)(1-9a/2)]<1+33a.
Indeed (1+33a)*den(U)-num(U)
=a[5/2-(30631/92)a+(7185/46)a²-(297/46)a³]>a[5/2-7/5-1/10]>0.
Thus H0h(1+E1)(1+W)>1. The new original Never
nu(Z1)/[(1+E1)(1+W)] is strictly less than H0h nu(Z1)=m,
with negative payoff and zero full debt, contradiction. This closes V>=0.
Thus the immediate word necessarily has V<0. The four-row word still
needs its own whole-head comparison, proved next.

## The four-row absorption inequality

For the remaining word01,03,01,013 let H4 be the product of ALL four
joint Continue factors. We prove

    H4(1+E)[1+3(E-F)]>1.                         (K3)

This comparison is over the entire actual four-row mode; it does not assume
small hazards. Their needed smallness follows from the original(AB) below.

### Core geometry and an exact small-hazard guard

The final013 active output is

    w0=3c-b,w1=-7a-c,w3=2(a-b).

The preceding01 row gives a two-cut starting source u1=(-rho,-sigma,C1,tau),
where

    rho=w0/(1+w0),sigma=-7w1/(1-w1),
    tau=(w3-w0-w1)/[(1-w1)(1+w0)].

The necessary last01 quiet3 margin and positive tau imply

    2c>=5a+3b, 9a-b-2c>0.                       (S)

In particular if r=b/a and t=c/a, then0<r<1 and5/2<=t<9/2.
The source u1 has0<rho<1: its positive owner2 and owner3 caps, negative0
and IN rule exclude rho>=1.

We now prove rho<1/36 using ONLY the original outer all-bad bound, positive
outer D0, and the fact that the next013 has b>0. Normalize
beta=sigma/rho,delta=tau/rho. The three necessary rows are

    D=beta+(8-rho)delta-9>0,
    G=-(16rho+13)beta+(24rho^2-84rho-90)delta
                                      +132rho+114>0,
    L=(27-4rho)beta-147delta-161>0.

Here D is positive outer3 output and G is the original outer AB after
positive clearing factors. L is precisely the second013 terminal test.
Put J=4rho^2-59rho+363>0 and take weights

    lambda_G=1,
    lambda_L=(8rho^2+31rho+14)/J>0,
    lambda_D=3(32rho^3-328rho^2+1420rho+1447)/J>0.

Their beta and delta coefficients cancel exactly, leaving

    lambda_D D+G+lambda_L L
       =-[336rho^3-236rho^2+2141rho-59]/J.

The bracket is strictly increasing on(0,1), since its derivative is at
least2141-472>0, and at rho=1/36 it equals289/972>0. Therefore rho>=1/36
would make the positive left side negative. Thus rho<1/36.
Consequently

    3c-b=rho/(1-rho)<1/35.

Together with(S), this gives a<2/525 and b<a. These are proved bounds,
not additional smallness assumptions on the source.

## Four-row comparison polynomial

Define positive core expressions

    x=3c-b,u=1+x,v=1+2x,w=1+5x,
    h=7a+c,vh=1+h,j=9a-b-2c,
    Q=u[1-4x+h(8+3x)]+(7+8x)j.

Here x<1/35,j>0, so Q>0. Direct reconstruction of the three preceding
pair rows gives

    H4=(1-a)(1-b)(1-c)uv/(wQ).

Set

    Aplus=1+6c+ac,
    Lplus=(1-a)(1-b)(1-c)+3b(1-a)+3c(7+a-8b),
    N=uv Aplus Lplus-wQ(1-a)(1-c).

Then the left side of(K3) minus1 equals

    N/[wQ(1-a)(1-c)],

whose denominator is positive. The numerator of the original outer AB,
cleared with its positive wQ denominator, is

    Graw=18xQ
      -6v[7hu^2+(8u-x)j-9x vh u]
      -7wu[7hu+6j-6x vh]>0.

These two factorized definitions give every polynomial coefficient below;
no precomputed coefficient payload or numerical search is required.

Substitute b=a*r,c=a*t and divide N,Graw by positive a, obtaining
polynomials P,G. Their leading amplitude terms are

    P=36t-119+8r+O(a),
    G=431t-1447-24r+O(a).

Define the exact residual R=P-(36/431)G. The following two tensor-Bernstein
facts hold on the stated CLOSED boxes:

| Polynomial | a range | r range | t range | Multidegrees | Coefficients | Exact minimum |
|---|---|---|---|---|---:|---|
|-G|[0,2/525]|[0,1]|[5/2,11/4]|(3,3,4)|80|1047/4|
|R|[0,2/525]|[0,1]|[11/4,9/2]|(6,3,5)|168|18109529554673803/40746470625000000|

Both exact minima are strictly positive. The complete stdlib-Fraction
checker printed below builds P,G,R from the displayed
factorized expressions and verifies all248 coefficients and their minima.
It uses no CAS, input files, root isolation or floating-point arithmetic.
The tensor conversion is obtained by applying the one-variable Bernstein
conversion independently in each of a,r,t after its affine interval map.
Its basis is nonnegative throughout the cube and sums to1, so strictly
positive coefficients prove strict positivity including its boundary.

If t<=11/4, the first row would give G<0, contradicting original AB.
Therefore t>11/4. The second row gives R>0, and hence P>0 because G>0.
Thus N=aP>0. Its positive denominator proves(K3).


## Four-row replacement and completion of the bound

The preceding stationary argument gives the full01 replacement at the
genuine Y whenever V>=E-F. In particular it applies if V>=3(E-F).
Its quiet3 gap is then at least2(E-F)>0; quiet2 is automatic, including
arbitrary nonpositive participant entries on02,12,012. The new E point
has negative active payoffs and original joint Never

    nu_new=nu(Y)/[(1+E)(1+V)].

The old four-row source has m=H4 nu(Y). The proved(K3) gives

    1/[(1+E)(1+V)]<=1/[(1+E)(1+3(E-F))]<H4.

Because nu(Y)>0, this contradicts the ORIGINAL minimum. Neither the final
tail nor the two-cut intermediate source is minimizing. This proves(CAP)
for both possible histories, and completes the theorem.

## Complete exact coefficient checks

For a univariate polynomial p=sum_j c_j x^j on[0,1], its Bernstein
coefficient at i and degree n is sum_(j<=i)c_j binom(i,j)/binom(n,j).
The basis is nonnegative and sums to1. Nonnegative coefficients with at
least one positive coefficient prove positivity in the open interval;
strict endpoint claims are checked separately. An affine substitution
handles any rational interval. Tensor conversion repeats this argument
one variable at a time. The following two complete standard-library
programs verify respectively all60 signs in the first-entry classification
and all248 positive tensor coefficients in the four-row comparison.
They are exact finite proof certificates, not sampling experiments or
Lean verification. No data files or external package are required.

### First-entry classification checker

```python
"""Exact Farkas/Bernstein certificate for first opposed-triple head patterns.
All data come from the integer recurrence; standard library only.
"""
from fractions import Fraction as F
from math import comb

def trim(p):
    p=list(map(F,p))
    while len(p)>1 and not p[-1]:p.pop()
    return tuple(p)
def add(*ps):
    q=[F(0)]*max(map(len,ps))
    for p in ps:
        for j,v in enumerate(p):q[j]+=v
    return trim(q)
def scale(p,c):return trim([c*v for v in p])
def sub(p,q):return add(p,scale(q,-1))
def mul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return trim(r)
def value(p,x):
    z=F(0)
    for v in reversed(p):z=z*x+v
    return z
def combine(coeffs,rows):
    return tuple(add(*(mul(c,row[j])for c,row in zip(coeffs,rows)))for j in range(3))
def bernstein(p,l,u):
    n=len(p)-1
    power=[sum(p[i]*comb(i,j)*l**(i-j)*(u-l)**j for i in range(j,n+1))for j in range(n+1)]
    return [sum(power[j]*F(comb(k,j),comb(n,j))for j in range(k+1))for k in range(n+1)]
checks=0
def positive(p,l,u,strict=True):
    global checks
    bs=bernstein(p,l,u)
    assert all(v>=0 for v in bs)
    if strict:assert any(v>0 for v in bs)
    for t in (l,u):
        if 0<t<1:
            assert value(p,t)>0 if strict else value(p,t)>=0
    checks+=1

a=(0,1);one=(1,);zero=(0,)
# Rows are coefficients of (beta,delta,1), b=a*beta and d=a*delta.
V=[(a,zero,zero),(zero,a,zero),(zero,zero,one)]
records={};Vs=[V]
for j in range(4):
    L=(1,2*(3**j-1));m=(0,3**j);L4=add(L,scale(m,4));Lm=add(L,m)
    records[f'Q03_{j}']=combine([scale(L,-1),add(L,scale(m,8)),scale(m,7)],V)
    records[f'Q01_{j}']=combine([scale(L,-1),sub(scale(m,5),scale(L,4)),scale(m,9)],V)
    N=[[scale(mul(L4,L),7),scale(mul(L4,L),42),scale(mul(m,L4),-42)],
       [mul(Lm,L),mul(Lm,sub(scale(L,8),m)),scale(mul(Lm,m),-9)],
       [mul(L4,L),mul(L4,add(scale(L,7),m)),mul(L4,sub(L,scale(m,5)))]]
    V=[combine(row,V)for row in N];Vs.append(V)
    records[f'D{j+1}']=V[1]
    Lnext=(1,2*(3**(j+1)-1));mnext=(0,3**(j+1))
    records[f'AB{j+1}']=combine([scale(Lnext,-1),scale(Lnext,-6),scale(mnext,6)],V)
first=(one,(-F(7,2),),(-7,))
second=((27,-4),(-147,),(-161,))
# (case,interval,three nonnegative rows,orientation of cross-product weights)
certificates=[
 ('NO4_FIRST',F(0),F(1,4),('Q03_0','D4','FIRST'),-1),
 ('NO4_FIRST',F(1,4),F(1,2),('Q01_0','D4','FIRST'),-1),
 ('NO4_FIRST',F(1,2),F(1),('Q01_0','D4','FIRST'),-1),
 ('NO3_SECOND',F(0),F(1,4),('Q03_0','D3','SECOND'),-1),
 ('NO3_SECOND',F(1,4),F(1),('Q01_0','D3','SECOND'),-1),
 ('AB1_FIRST',F(0),F(1),('D1','AB1','FIRST'),1),
 ('AB2_FIRST',F(0),F(1),('D2','AB2','FIRST'),1),
 ('AB3_FIRST',F(0),F(1,4),('Q03_0','D3','FIRST'),-1),
 ('AB3_FIRST',F(1,4),F(1,2),('Q01_0','D3','FIRST'),-1),
 ('AB3_FIRST',F(1,2),F(3,4),('Q01_0','D3','FIRST'),-1),
 ('AB3_FIRST',F(3,4),F(1),('Q01_0','D3','AB3'),-1),
 ('AB2_SECOND',F(0),F(1,8),('Q03_0','D2','SECOND'),-1),
 ('AB2_SECOND',F(1,8),F(1,4),('D2','AB2','SECOND'),1),
 ('AB2_SECOND',F(1,4),F(1,2),('D2','AB2','SECOND'),1),
 ('AB2_SECOND',F(1,2),F(1),('D2','AB2','SECOND'),1)]
records.update(FIRST=first,SECOND=second)
for case,l,u,names,sgn in certificates:
    R=[records[n]for n in names]
    # Cross product of beta and delta columns cancels both free variables.
    weights=[scale(sub(mul(R[1][0],R[2][1]),mul(R[2][0],R[1][1])),sgn),
             scale(sub(mul(R[2][0],R[0][1]),mul(R[0][0],R[2][1])),sgn),
             scale(sub(mul(R[0][0],R[1][1]),mul(R[1][0],R[0][1])),sgn)]
    for w in weights:positive(w,l,u)
    total=combine(weights,R)
    assert total[0]==(F(0),) and total[1]==(F(0),)
    positive(scale(total[2],-1),l,u)
    print(case,'interval',l,u,'rows',','.join(names),'EXACT PASS')
print('PASS:',checks,'exact sign checks; all subdivision endpoints checked.')
```

### Four-row absorption checker

```python
"""Exact rational tensor-Bernstein proof of the four-head K=3 comparison.
No CAS, external inputs, sampled inequalities or stored coefficient payloads.
"""
from fractions import Fraction as F
from math import comb
from itertools import product

def clean(p):return {e:F(c)for e,c in p.items()if c}
def const(c):return {(0,0,0):F(c)}if c else {}
def add(*ps):
    out={}
    for p in ps:
        for e,c in p.items():out[e]=out.get(e,F(0))+c
    return clean(out)
def scale(p,c):return clean({e:c*v for e,v in p.items()})
def sub(p,q):return add(p,scale(q,-1))
def mul(*ps):
    out=const(1)
    for p in ps:
        acc={}
        for e,c in out.items():
            for f,d in p.items():
                g=tuple(x+y for x,y in zip(e,f));acc[g]=acc.get(g,F(0))+c*d
        out=clean(acc)
    return out
def divide_a(p):
    assert all(e[0]>=1 for e in p)
    return {(e[0]-1,e[1],e[2]):c for e,c in p.items()}
def bernstein(p,amax,tlo,thi):
    # Substitute a=amax*x,r=y,t=tlo+(thi-tlo)*z exactly.
    q={}
    for (i,j,k),c in p.items():
        for h in range(k+1):
            e=(i,j,h);cc=c*amax**i*comb(k,h)*tlo**(k-h)*(thi-tlo)**h
            q[e]=q.get(e,F(0))+cc
    q=clean(q);deg=tuple(max(e[k]for e in q)for k in range(3))
    out=[]
    for target in product(*[range(n+1)for n in deg]):
        val=F(0)
        for ex,cc in q.items():
            if all(e<=i for e,i in zip(ex,target)):
                val+=cc*F(comb(target[0],ex[0]),comb(deg[0],ex[0]))*F(comb(target[1],ex[1]),comb(deg[1],ex[1]))*F(comb(target[2],ex[2]),comb(deg[2],ex[2]))
        out.append(val)
    return deg,out
one=const(1);aa={(1,0,0):F(1)};r={(0,1,0):F(1)};t={(0,0,1):F(1)}
b=mul(aa,r);c=mul(aa,t);x=sub(scale(c,3),b)
u=add(one,x);v=add(one,scale(x,2));w=add(one,scale(x,5))
h=add(scale(aa,7),c);vh=add(one,h);j=sub(sub(scale(aa,9),b),scale(c,2))
Q=add(mul(u,add(sub(one,scale(x,4)),mul(h,add(const(8),scale(x,3))))),mul(add(const(7),scale(x,8)),j))
D=mul(sub(one,aa),sub(one,b),sub(one,c))
Aplus=add(one,scale(c,6),mul(aa,c))
L=add(D,scale(mul(b,sub(one,aa)),3),scale(mul(c,add(const(7),aa,scale(b,-8))),3))
N=sub(mul(u,v,Aplus,L),mul(w,Q,sub(one,aa),sub(one,c)))
Gnum=add(scale(mul(x,Q),18),scale(mul(v,add(scale(mul(h,u,u),7),mul(sub(scale(u,8),x),j),scale(mul(x,vh,u),-9))),-6),scale(mul(w,u,add(scale(mul(h,u),7),scale(j,6),scale(mul(x,vh),-6))),-7))
P=divide_a(N);G=divide_a(Gnum);R=sub(P,scale(G,F(36,431)))
for name,p,lo,hi,expected in [('minusG',scale(G,-1),F(5,2),F(11,4),F(1047,4)),('residual',R,F(11,4),F(9,2),F(18109529554673803,40746470625000000))]:
    deg,bs=bernstein(p,F(2,525),lo,hi)
    assert all(v>0 for v in bs)
    assert min(bs)==expected
    print(name,'degrees',deg,'strict-positive coefficients',len(bs),'minimum',min(bs))
# Critical guard polynomial from three-row Farkas identity.
z=F(1,36)
assert 336*z**3-236*z**2+2141*z-59==F(289,972)>0
print('PASS: all248 tensor coefficients strictly positive; exact guard endpoint checked.')
```

## Boundary tests

The hypotheses concern a selected positive-gap source, not every E point.
The classification only uses(AB) at the original outer source; the long
suffix certificates deliberately omit it. Applying outer(AB) to an
inherited suffix would invalidate the argument. All dyadic subdivision
endpoints in the first checker are evaluated exactly. The physical hazard
endpoints0 and1 are not extra source cases: positivity of original Never
and the asserted genuine support give strict proper hazards.

The stationary comparison uses S>=0, including a quiet3 equality in the
four-row case. Its resulting bounds c>4b and a<2/5 remain strict since
a>b>0. The first direct comparison includes V=E-F; the subsequent three-row
comparison includes V=0, where r=q/3 is allowed. Together they exclude
EVERY V>=0 for the immediate word. The four-row sector includes
V=3(E-F). Each exclusion has a STRICT whole-head Never inequality.
The coefficient certificate includes the boundary faces of its closed
boxes, although the actual source bounds are strict.

These are finite auxiliary-Nash head calculations. The terminal annotation
is NOT asserted to belong to the actual carrier. They are neither actual
minimum-Never sources nor A_Z>0 witnesses. Set all31 free reward entries
of(R) to0, in particular Z0(13)=Z2(13)=Z2(013)=0 and all participant
rewards of2 to0. Take terminal annotation Y=(V,-E,1,F), where

    E=(a+7c)/[(1-a)(1-c)],
    F=(a-b)/[(1-a)(1-b)],
    V=(b-c+2bc)/[(1-b)(1-c)].

Then(a,b,0,c) is a full proper013 Nash row: all three active endpoint
equalities hold, and owner2 has Q2=0 while its Continue output is positive.
The pair rows below are the unique proper roots reconstructed from that
output, so they form consistent full Nash heads over the single fixed
terminal annotation. Every owner2 Continue output in both examples exceeds
9/10; this is verified by exact rational arithmetic.

### Four rows: coefficient1 fails and coefficient3 succeeds

Use

    a=1/10000,b=1/1000000,c=21/62500.

Reconstruct01,03,01 before013. The original source is(-A,-B,C,D), with

    A=3021/1005035,
    B=346720002805449/19362793296916621,
    D=51793350038950204/19460284961166596186735,
    6(A-D)-B=2193493180102535307/19460284961166596186735>1/10000,
    D>1/500000.

The last01 quiet3 numerator is exactly169/1000000>0. The middle03
quiet1 numerator, in the normalized source formula, is
6463220000000/250763275400888691>1/40000. The outer01 quiet3 numerator is
226785217777382/250763275400888691>0. Thus all non2 quiet gaps are strict;
owner2 is strict separately because its cap is positive and Q2=0.
The positive2 output C also exceeds5A+4AD-D, so both original AB bounds hold.

Let L=153502216941201880097815778206250. The exact comparisons are

    H4(1+E)(1+E-F)=152815852017573486913257366578193/L<249/250<1,
    H4(1+E)(1+3(E-F))=153533637510740415095925333083193/L>5001/5000>1.

Thus coefficient1 cannot replace3 in the four-row theorem, even on a
strict original-AB core. This example also gives a low-V surviving core:

    V=-20937458/62478937521<0<E-F,
    E=1532500/624727521,F=10000/100999899.

It satisfies the new low-V side rather than being an exclusion witness.

### Two rows: the stronger coefficient1 comparison holds

Use

    a=1/10000,b=1/1000000,c=449/1000000,

and reconstruct only01 before013. Its source has

    6(A-D)-B=4242241/167082757759>0,
    D=500000/501248273277>0,
    S=79/200000>0.

Again every owner2 cap is greater than9/10 and the original C bound holds.
The complete two-row comparison is

    H2(1+E)(1+E-F)
       =48354743633616326500081/48193661421935391740000
       >501/500>1.

No original Never tuple, actual realization of Y, positive absorbing gap
or global minimum is assigned to either core example. Their role is exact
boundary testing of the head geometry and the coefficient distinction.

At the newly excluded boundary V=0 take the two-row hazards above and
change only the free entry k to2+1/c-1/b, leaving l=R=0 and T=1.
The checker below reconstructs the unique third013, its terminal annotation
and the full01 replacement, and verifies its STRICT entire-head absorption
comparison. This is another auxiliary Nash core, not an assertion that the
terminal annotation lies in the actual carrier or that A_Z>0.

The complete exact boundary checker is:

```python
from fractions import Fraction as F
from itertools import combinations
G=[[0,-2,-5,4],[-6,0,-4,6],[1,3,0,-5],[1,-1,4,0]]
fixed={(0,3):-1,(0,9):3,(1,3):-7,(1,10):-1,(3,9):2,
       (3,10):-2,(0,11):2,(1,11):-8,(3,11):0,(2,3):4,
       (3,3):0,(1,9):0,(2,9):-4}
def reward(i,S):
    if len(S)==1:return F(G[i][next(iter(S))])
    return F(fixed.get((i,sum(1<<j for j in S)),0))
def prefix(q,y):
    z=[]
    for i in range(4):
        others=[j for j in range(4)if j!=i];Q=F(0);P=F(0);H=F(1)
        for j in others:H*=1-q[j]
        for n in range(4):
            for sub in combinations(others,n):
                S=set(sub);mass=F(1)
                for j in others:mass*=q[j]if j in S else 1-q[j]
                Q+=mass*reward(i,S|{i})
                if S:P+=mass*reward(i,S)
        C=P+H*y[i]
        assert Q<=C if q[i]==0 else Q==C
        z.append(q[i]*Q+(1-q[i])*C)
    return z
def test(c,cycles):
    a=F(1,10000);b=F(1,1000000)
    E=(a+7*c)/((1-a)*(1-c));F3=(a-b)/((1-a)*(1-b))
    V=(b-c+2*b*c)/((1-b)*(1-c))
    y=[V,-E,F(1),F3];q=[a,b,F(0),c]
    H=(1-a)*(1-b)*(1-c);z=prefix(q,y);assert z[2]>F(9,10)
    pairs=['01']if cycles==0 else ['01','03','01']
    for pair in pairs:
        if pair=='01':q=[-z[1]/(1-z[1]),z[0]/(1+z[0]),F(0),F(0)]
        else:q=[z[3]/(1+z[3]),F(0),F(0),-z[0]/(1-z[0])]
        assert all(0<=x<1 for x in q)
        for x in q:H*=1-x
        z=prefix(q,z);assert z[2]>F(9,10)
    A=-z[0];B=-z[1];C=z[2];D=z[3]
    assert min(A,B,C,D)>0 and B<6*(A-D)and C>5*A+4*A*D-D
    return H*(1+E)*(1+E-F3),H*(1+E)*(1+3*(E-F3)),V
x,y,V=test(F(21,62500),1)
assert x<F(249,250)<1< F(5001,5000)<y and V<0
x,_,_=test(F(449,1000000),0)
assert x>F(501,500)>1
print('PASS: both exact Nash cores, all quiet and original-AB comparisons.')
# Exact V=0 boundary of the three-row replacement, with all other free entries0.
a=F(1,10000);b=F(1,1000000);c=F(449,1000000)
E=(a+7*c)/((1-a)*(1-c));F3=(a-b)/((1-a)*(1-b))
k=2+1/c-1/b;fixed[0,10]=k
q=(6*E-21*F3)/44;p=q+F3/2;r=q/3
h=(1-p)*(1-q)*(1-r)
W=(q-r+(2-k)*q*r)/((1-q)*(1-r))
E1=(p+7*r)/((1-p)*(1-r));F1=(p-q)/((1-p)*(1-q))
P2=p+3*q-5*r+2*q*r-p*q*r
Z1=[W,-E1,(1-P2)/h,F1]
assert prefix([p,q,F(0),r],Z1)==[0,-E,1,F3]
w=prefix([a,b,F(0),c],[0,-E,1,F3])
prefix([-w[1]/(1-w[1]),w[0]/(1+w[0]),F(0),F(0)],w)
new=prefix([E1/(1+E1),W/(1+W),F(0),F(0)],Z1)
assert new[0]<0 and new[1]<0
H0=(1-a)*(1-b)*(1-c)/((1+7*a+c)*(1-b+3*c))
assert H0*h*(1+E1)*(1+W)>1
print('PASS: V=0 forced third-row core and complete whole-head replacement.')
```


## Source correspondence, adapter and consumer

Exact source facts inspected in the implementation are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`,
`quittingTerminalDeviationDebt_nonneg`, and
`quittingTerminalDeviationDebt_rootThenContinuation_eq`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`), together with
`quittingTerminalPayoff_rootThenContinuation_eq`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`).
These identities concern the unrestricted behavioral cap and literal
terminal payoff, and justify the stopping-law prefix semantics above.
No additional Lean check is claimed here.

The classified incoming mode consists of ACTUAL finite first013 heads over
an original negative minimum-Never source with the explicit positive2
ledger. Its adapter is the incoming-row extraction and genuine conditioning
in(IN); its new output is the two-word normal form and the two strict
continuation bounds, including the additional forced third row when the
immediate tail has0<=V<E-F. It does not assume or verify a favorable supplied
replacement. Both stationary shadow roots are produced by continuity from
the raw k, and the single01 replacement is given explicitly at the same
genuine tail. The consumer contradicts the ORIGINAL selected source by
its full cap and original joint Never, retaining a negative coordinate.

A stationary child row with nonnegative passive2 already gives an absorbing
full Nash profile and A_Z=0. That is the elementary pre-existing stationary
mechanism, used here only as a necessary constraint under A_Z>0. It is not
counted as new reward-class coverage. No probability mode, sure absorption,
infinite-law realization or fixed target is inferred from the coefficient
checks alone. The theorem is ordinary mathematical source reduction.

## Lean handoff and remaining gap

Suggested theorem shapes quantify over a compact actual tuple carrier,
a selected original minimum-Never source, and a finite genuine first-entry
chain satisfying the stated mode. Prove the two-word conclusion, then the
whole-head survival inequalities, the stationary affine interpolation,
the additional genuine triple and the explicit Nash replacements. The
finite polynomial certificates can be separated from the game-semantic proof and normalized by rational
arithmetic; they must not become assumptions encoding the desired conclusion.
Reuse the named full-cap prefix declarations. No new strategy primitives or
changes to the deviation class are needed.

The theorem does not produce finite entry for arbitrary sources, settle
the remaining negative-V immediate continuation or low-V four-row
continuation, exclude negative-owner2 sources,
close the whole opposed-pair reward family, or solve Fin4. Its completed
contribution is a strict reduction of the finite first013 mode, including
automatically produced quiet2 comparisons and comparisons against
EVERY retained actual row, including the forced third row when needed.
