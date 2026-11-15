# A finite nine-row consumer for the low nonnegative four-row tail

## Exact statement

There are four players0,1,2,3. They use independent complete stopping
laws on natural dates and a separate Never point. The first nonempty
quitting coalition S absorbs at the finite reward Z_i(S); live play,
Never and own-singleton rewards are zero. One unilateral deviation may
replace its owner's entire law. Fix Gamma_ij=Z_i({j}) to be

    Gamma=[0,-2,-5,4;-6,0,-4,6;1,3,0,-5;1,-1,4,0].

Every participant reward of owners1,2 is nonpositive. Fix

    Z0(01)=-1,Z0(03)=3,Z1(01)=-7,Z1(13)=-1,
    Z3(03)=2,Z3(13)=-2,Z0(013)=2,Z1(013)=-8,Z3(013)=0,
    Z2(01)=4,Z3(01)=0,Z1(03)=0,Z2(03)=-4.          (R)

All other31 nonsingleton entries are arbitrary finite numbers subject
to those signs. For actual profiles retain prescribed payoff U, full
behavioral response cap B, literal-Never response e and ORIGINAL Never
marginals N. Let C be the compact closure of these tuples, E={B=U}, and

    D=sum_i(B_i-U_i), nu=product_i N_i,
    A_Z=inf{D(P):P actual,nu(P)=0},
    m=min{nu(X):X in E,min_i U_i(X)<=0}.

Assume A_Z>0 and let X attain m with
`U(X)=(-A0,-B0,C0,D0)`, all four parameters positive. Consider an ACTUAL
four-row head from this ORIGINAL source,

    01 -> 03 -> 01 -> 013,

with genuine conditional E tails, positive owner2 caps at every source
cut, signs(-,-,+,+) at the two01 sources and(+,-,+,+) at the intervening
and final013 sources. Write the final013 hazards as(a,b,0,c), its genuine
tail as Y=(V,-E0,T,F0), and k=Z0(13), kappa=2-k.

**Theorem.** This configuration cannot satisfy

    0<=V<E0-F0.                                (LOW)

The result consumes an entire actual source mode. It does not assert that
every game produces this head, exclude negative V, settle the remaining
four-row sectors or prove UE for the whole raw family. It requires no
tail minimum, favorable replacement, recurrent cone, continuous selector
or law realizing a closure point.

## Full caps, actual tails and the original minimum

Before absorption there is one live history. Independent behavioral
randomization is therefore represented by complete independent stopping
laws; every unilateral reply is a mixture or limit of deadlines and
Never. No public coin or additional observation is used.

For a row q put h=product_i(1-q_i), H_i=product_(j!=i)(1-q_j), Q_i its
forced-Quit offer and P_i its passive contribution on nonempty opponent
coalitions. The exact finite-prefix formulas are

    B'_i=max(Q_i,P_i+H_i B_i),
    U'_i=q_iQ_i+(1-q_i)P_i+h U_i,
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i.

Their nonnegative debt decomposition is

    d'_i=q_i(B'_i-Q_i)+(1-q_i)(B'_i-P_i-H_iB_i)+h d_i.

Thus every limiting incoming row at u=U=B obeys

    Q_i<=u_i, q_i(u_i-Q_i)=0.                  (IN)

Choose M>=1 bounding all rewards. Moving a smallest original Never
atom to one finite date changes four payoffs and three other caps by
at most2M times that atom, while its owner's cap is unchanged. Hence
`A_Z<=D+14M nu^(1/4)`, also on C. Every E point has positive original
Never. An incoming row has h>=nu>0; its actual conditional tails therefore
have E limits by the debt decomposition. Every fixed finite Nash prefix
of a genuine E tail gives another E point by prefixing actual approximants
and continuity. Original N multiplies through these finite maps; escaping
finite mass is never renamed Never.

There is a short direct producer for every further tail used here: its
owner1 cap is negative. Choose actual P_n converging to that E point.
Their original N_i stay bounded below, so the first rows and conditional
tail tuples have a subsequential limit with `1-q_i>=N_i>0`.
Since `Q1(q_n)<=B1(P_n)->-e<0`, the limiting row is nonzero.
The nonnegative decomposition with h>0 forces its tail into E and
makes the limiting row FULL Nash at that genuine tail. All prefix
coordinates, including N_i=(1-q_i)N_i(tail), pass exactly to the limit.
No moving-date or infinite-head source assumption is needed here.

At X any sure auxiliary Nash root contradicts positive Never. A nonzero
proper root with a nonpositive output would lower m. AllContinue is not
Nash at a negative input. Therefore every auxiliary root has positive
output. Since Q1,Q2<=0, such a root has q1=q2=0. Singletons have active
output0; finite Nash existence forces proper03 with odds(D0,A0). Its
quiet outputs yield the ORIGINAL bounds

    B0<6(A0-D0), C0>Cmin=5A0+4A0D0-D0.         (AB)

These bounds are never imposed on a continuation. All later comparisons
retain a negative output and compare their WHOLE original Never with m.

## Exact four-head geometry and its smallness guard

On q2=0 the fixed forced-Quit polynomials are

    Q0=-q1+3q3,Q1=-7q0-q3,Q3=2q0-2q1.

At the final013 source put

    x=3c-b, h0=7a+c, j=9a-b-2c,
    u=1+x, vfac=1+2x, w=1+5x, Delta=(1-a)(1-b)(1-c),
    Q=u[1-4x+h0(8+3x)]+(7+8x)j,
    Draw=7h0u²+(8u-x)j-9x(1+h0)u,
    BP=7h0u+6j-6x(1+h0),
    Graw=18xQ-6vfac*Draw-7wu*BP,
    Sraw=7u(x-h0)+(1+9x)j.

Proper inverse reconstruction of all three pair rows gives

    A0=3x/w, B0=7u*BP/Q, D0=vfac*Draw/(wQ),
    H4=Delta*u*vfac/(wQ),
    Graw=wQ[6(A0-D0)-B0]>0, Draw>0, Sraw>=0.    (GDS)

Here H4 is the survival of ALL FOUR rows. The last01 quiet3 comparison
and positive output3 give

    2c>=5a+3b, j>0, 0<b<a<1.

The final genuine tail coordinates and active0 identity are

    E0=(a+7c)/[(1-a)(1-c)],
    F0=(a-b)/[(1-a)(1-b)], E0>F0>0,
    V(1-b)(1-c)=b-c+kappa bc.                  (TAIL)

For completeness the needed amplitude guard uses the preceding01 source
`(-rho,-sigma,*,tau)`, with

    rho=x/u, sigma=7h0/(1+h0), tau=j/[(1+h0)u].

Normalize beta=sigma/rho,delta=tau/rho. Positive ORIGINAL output3,
ORIGINAL AB and the extra final owner1 hazard respectively imply

    D=beta+(8-rho)delta-9>0,
    G=-(16rho+13)beta+(24rho²-84rho-90)delta+132rho+114>0,
    L=(27-4rho)beta-147delta-161>0.

For0<rho<1 put J=4rho²-59rho+363>0. The positive weights

    lambda_G=1, lambda_L=(8rho²+31rho+14)/J,
    lambda_D=3(32rho³-328rho²+1420rho+1447)/J

give exactly

    lambda_D D+G+lambda_L L
       =-[336rho³-236rho²+2141rho-59]/J.

The bracket has derivative>2141-472>0 and value289/972>0 at1/36.
Thus rho<1/36, x<1/35, and `a<2/525` follows from
`x=3c-b>15a/2`. No extra tiny-hazard hypothesis is supplied.

## Original3 and middle quiet1 sharpen the ratios

Put r=b/a,t=c/a. Initially0<r<1,5/2<=t<9/2. Direct expansion of(GDS)
gives

    Draw/a=121+r-36t+a(3t-r)(98+2r-36t)
                         -2a²(7+t)(3t-r)²>0,
    Sraw/a=12t-8r-40+a(3t-r)(32-16r-4t)>=0.

For t>=7/2 the first is negative. For t<=13/4 the second is at most
`-1+(2/525)(741/4)=-103/350<0`; its quadratic product is maximal at
r=0,t=13/4 on that rectangle. Thus13/4<t<7/2.
If r>=1/10, their sum with weight3 is at most

    -13/10+(2/525)(32231/100)=-947/13125<0.

Indeed the relevant product `(3t-r)(194-46r-48t)` decreases in both
r,t on that rectangle. Therefore

    0<r<1/10, 13/4<t<7/2, 0<a<2/525.           (COARSE)

The nonlinear terms of Draw/a are negative, so t<(121+r)/36<1211/360.
Also x=a(3t-r)>(193/20)a gives a<4/1351. On the closed box
`a[0,4/1351],r[1/15,1/10],t[13/4,1211/360]`, the polynomial

    -[36Graw+(491-4800a)Draw+(180-14400a)Sraw]/a

has all80 homogeneous interval coefficients strictly positive. The
multipliers are positive. Program A regenerates the certificate, so(GDS)
excludes that box and proves

    r<1/15, a<4/1351, t<1211/360.              (SHARP)

## A four-row survival bound, without an imported proof

Define

    Aplus=1+6c+ac,
    Lplus=Delta+3b(1-a)+3c(7+a-8b),
    N=uvfac*Aplus*Lplus-wQ(1-a)(1-c).

Exact substitution gives

    H4(1+E0)[1+3(E0-F0)]-1=N/[wQ(1-a)(1-c)].

The denominator is positive: x<1/35,j>0 make Q>0. After b=ar,c=at,
put P=N/a,G=Graw/a. Program A proves -G>0 on
`a[0,2/525],r[0,1],t[5/2,11/4]` by80 positive coefficients. Since the
actual G>0, t>11/4. On `t[11/4,9/2]` it proves `431P-36G>0` by168
positive coefficients. Hence N>0. In particular(COARSE) gives

    E0<27a, H4^(-1)<(1+27a)(1+81a).            (COST4)

This is the old four-row comparison, reproduced here in the shared
polynomial regenerator rather than imported from another conference file.

## Produced stationary planes at every needed finite hazard

Write l=Z2(13), R2=Z2(013), L(t)=(1-t)l+tR2. For0<t<6/7 let d(t)>0
be the unique root of

    F_t(d)=(t-1)d²+(7t²-8t-6)d+t(6-7t)=0.

It is continuous and `0<d(t)<t-t²/3<t`: evaluate F_t at the middle
bound to obtain `t²(t³-28t²+102t-126)/9<0`. The stationary013 child
families have q0=t,q3=d(t) and either q1=t or
`q1=(1-2t)/[2(1-t)]`, the latter for0<t<1/2. The three active
indifferences are F_t(d)=0,
`(t-q1)[2(1-t)(1-q1)-1]=0`, and

    k=K(q1,d)=q1+4-3d+(2-q1)/d+(3d-4)/q1.

These are complete behavioral stationary Nash profiles on the child:
the active equations give P_i=(1-H_i)Q_i, so every deadline and Never
equals Q_i by telescoping, with H_i<1. The prescribed affine fixed point
is the same literal terminal payoff. Owner2's
Never value is P2/(1-h), where

    P2=t+3q1-5d+2q1*d-t*q1*d+q1*d*L(t).

If P2>=0, its Quit offer<=0 makes this a full absorbing four-player
Nash profile, contradicting A_Z>0. Thus at EVERY matching-k stationary
root the raw entries satisfy

    L(t)<J(t,q1,d)=[5d-t-3q1-2q1*d+t*q1*d]/(q1*d).

In fact `J+K/2<-7` on symmetric0<t<2/5 and hyperbola2/5<t<1/2.
For the symmetric family the reduced numerator2td[J+K/2+7] is
`(24t²-10t-12)d+12t-22t²`. Its coefficient of d is negative, and at
`b=t(12-22t)/(12+10t-24t²)` one has

    F_t(b)=-12t³(7t³+10t²+14t-28)/(12t²-5t-6)²>0.

Since F_t decreases, d>b proves the strict sign. For the hyperbola the
reduced numerator is `[A(t)d+B(t)]/[4(t-1)²]`, where

    A=8t³+114t²-180t+17<0,
    B=-8t³-46t²+56t-9>0,
    F_t(-B/A)=-P7(t)/A²,
    P7=3872t^7+46328t^6-210836t^5+326040t^4
                       -243096t³+93396t²-17031t+999.

For the displayed signs A'<=-60 and B'>=4 on[2/5,1/2], while
A(2/5)<0 and B(2/5)>0. The symmetric cubic is increasing and negative
at2/5, giving its asserted sign as well.
Program B verifies all8 positive coefficients of -P7 under the interval
map from[2/5,1/2], so F_t(-B/A)>0 and d>-B/A.

Here is a useful finite bracket producer. If k<-22,0<x<2/5 and
kappa*x>2, then symmetric K(t,d(t)) tends to-infinity at0, while
`K(x,d(x))>-2/x+3-2x>2-kappa=k`. A matching root lies below x.
At t=2/5 the hyperbola has q1=1/6,d<1/6 and K>-11>k; it tends
to-infinity at1/2, giving another matching root above2/5. Affinity gives

    L(x)<-k/2-7=kappa/2-8<-k/2.                (PASS7)

This produces, rather than assumes, every plane used below. There is
no claim that one bracket persists forever.

## The first extra actual triple and a full01 comparison

Under(LOW), (TAIL),(COARSE) imply
`kappa>=1/b-1/c>126/(13a)`, so k<-22 and kappa*a>2. Thus PASS7 applies
at a. Its weaker bound L(a)<-k/2 gives

    P2<a+5b/2-9c/2+bc(1-a)+(V/2)(1-b)(1-c).

Replace V by E0-F0. Twice1-a times the upper bound is

    2a-2a²+6b-6ab+c[-2+10a-6b-4ab+2a²b]
       <2a+6b+c(-2+10a)<13a/5-13a/4<0.

The positive incoming owner2 cap therefore gives T>0. Also
`E0>95a/4`, `E0/F0>95/4`, `E0<27a`, and `F0<41a/40`.

At Y, positive2 suppresses its hazard. If q0=0 and q3>0, active3 would
have Q3<=0, contrary to F0>0. If q0=q3=0, quiet1 would have
Q1=0>-E0. If q3=0 and q0>0, active0 gives V=-q1>=0, so V=q1=0;
quiet1 and quiet3 then require E0/7<=q0<=F0/2, impossible.
Thus owners0,3 are active, including at V=0. If owner1 were absent,
the two active equations give q3=V/3,q0=F0/2, and quiet1 requires
`E0<=7F0/2+V/3<E0/3+19F0/6`, again impossible since E0/F0>95/4.
Thus the next actual row is uniquely013, with

    q=(6E0-21F0-2V)/44, p=q+F0/2, s=(V+q)/3.

Its genuine tail is Z5=(v5,-e5,T5,f5), with

    v5=[q-s+kappa*qs]/[(1-q)(1-s)],
    e5=(p+7s)/[(1-p)(1-s)],
    f5=(p-q)/[(1-p)(1-q)], h5=(1-p)(1-q)(1-s).

The elementary bounds are

    q>19F0/11>3a/2, p<4q/3, p<E0/6<1/40,
    s>=q/3, kappa*q>189/13>14.

Hence p>a,kappa*p>2, and PASS7 is produced at p. Moreover

    h5*v5>(39/40)(q+13s)>=26q/5,
    h5(v5+f5-e5)=s[kappa*q*(1-p)-8(1-q)]>0.

The passive2 offer Pi at this row satisfies
`Pi<29q/6+(v5/2)(1-q)(1-s)`. Since T>0,

    h5[T5+e5+3v5+4e5v5]>2h5*v5-29q/6>0.

Therefore the explicit01 root at genuine Z5 with odds(e5,v5) is FULL
Nash: quiet3 is strict, quiet2 has positive Continue against Quit<=0,
and the active outputs are negative. ORIGINAL minimum forces

    Xi5=H4*h5*(1+e5)*(1+v5)-1<=0.              (N5)

## The ORIGINAL source budget produces T5 and an account

Put Cshadow=-k/2=kappa/2-1. Comparing the two free passive entries
with this common shadow is legitimate because the SAME table satisfies
PASS7 at a and p. Its old four-row passive2 contribution is strictly
smaller than the shadow contribution. By ORIGINAL C0>Cmin,

    T>Tstar=(Cmin-Pold_shadow)/H4,
    h5*T5>Tstar-Pi_max=:Bstar,
    Pi_max=p+3q-5s+qs-pqs+(kappa/2)qs.

Here is a complete finite formula for Tstar. The functional
`Lambda(U)=U2+U0/2+U1/2+2U3` on the shadow table annihilates
singleton coalitions0,1,3 and01, pays3/2 at03,-9/2 at13,and kappa/2-4 at013.
Consequently

    Qfinal=2ac-(9/2)bc-abc-ab/2+(aV/2)(1-b)(1-c),
    Lambda0=(9/2)A0-B0/2+D0+4A0D0,
    Tstar=Lambda0/H4-[(3/2)jx/u+Qfinal]/Delta-V/2+E0/2-2F0.

The middle03 collision has normalized charge(3/2)jx/u; both01
charges vanish. These identities reconstruct the ENTIRE original source.
For checking the printed integer numerator, put

    AN=27xQw-7uw²BP+2vfac(1+17x)Draw-3jx*vfac*w
                       -2u*vfac*w*Qfinal.

Then the part of Tstar before `-V/2+E0/2-2F0` is exactly
`AN/(2Delta*u*vfac*w)`. This gives the direct denominator-clearing
identity used by Program A, with no inferred polynomial payload.

Let A2=1+6s+ps and eta=(1-s)/(2H4*A2)>0. Exact kappa cancellation gives

    J=Bstar+eta*Xi5
      =Tstar-p-3q+4s-qs/2+pqs+1/2-(1-s)/(2H4*A2).

Program A proves `J-(4007/18964)Graw>0` throughout(COARSE) and
`0<=V/a<=27`, by29484 strictly positive generated coefficients. It clears
only the positive denominator `6Delta*u*vfac*w*d³*Abig`, with
`d=44Delta`, `Abig=3d²+6Rn*d+Pn*Rn` and the exact numerators defined
in the program. Hence J>0. Since Xi5<=0,

    h5*T5>Bstar=J-eta*Xi5>0,

so T5>0 is PRODUCED. In fact the stronger ORIGINAL account holds:

    R5(1+e5)(1+v5+2alpha5*T5)>1,
    R5=H4*h5, alpha5=1-p.                     (ACCOUNT5)

Indeed its excess over1 is exactly
`[h5*T5+eta*Xi5]/eta>J/eta>0`. No continuation minimum is introduced.

## Failed five-row descent produces a compact original box

Define `z=V/a`. Initially0<=z<27. With

    d=44Delta,
    En=(a+7c)(1-b), Fn=(a-b)(1-c),
    Qn=6En-21Fn-2VDelta, Pn=Qn+22Fn, Rn=dV+Qn,
    Kn=V(1-b)(1-c)-b+c=kappa*bc,
    An=3d²+6Rn*d+PnRn,
    Bn=3d²bc-2Rn*d*bc+(Kn+bc)QnRn,

the numerator of Xi5 after positive denominator clearing is

    Delta*u*vfac*An*Bn-3wQd³bc(3d-Rn).

After b=ar,c=at,V=az it is divisible by a³. Program A proves its
quotient strictly positive by11880 coefficients on EACH closed box

    a[0,4/1351],r[0,1/40],t[13/4,1211/360],z[0,27];
    a[0,4/1351],r[0,1/15],t[13/4,1211/360],z[2,27].

Thus(N5) forces r>1/40 and z<2, including both boundary exclusions.
These are original-source guards, not discovery-driven cutoffs.

## The produced Z5 return cone and its raw coupling

The preceding bounds sharpen to

    4e5<v5<15e5, f5<e5/19, v5<21/50.           (CONE5)

Here are the finite derivations. The product kappa(V)q(V) is concave
in V. At V=E0-F0, exactly
`kappa=8(1-b)/[b(1-a)]` and `q>19a/11`, so its value exceeds100.
At V=0 it decreases in b and
increases in c; substitute b=a/15,c=13a/4 to obtain
`kappa*q>234739/5720` on the whole interval. The derivative check in b
is `b²(kappa0*q0)'=-q0+b(1-b/c)q0_b< -2a+b/2<0`.
Also kappa0*a>191/13 and, at those substituted bounds,

    q0/a=[(285/2)/(1-13a/4)-(98/5)/(1-a/15)]/[44(1-a)]
         >1229/440.

The numerator increases from its value at0, and division by1-a only
increases it. This proves the claimed exact endpoint product.

The positive-denominator numerator of v5-4e5, divided by s, is greater
than

    kappa*q*(1-p)-29-3(3q+2F0)/(V+q).

The last ratio decreases in V; at0, F0/q0<88/243. Since
`p<18/1351<1/75`, the expression exceeds
`(234739/5720)(74/75)-3254/81=1843261/5791500>0`.

The ratio e5/f5 equals
`[1+2q/F0+14s/F0]*(1-q)/(1-s)`. Both factors increase with V.
At V=0 use q/F0>243/88,s=q/3,q<1/40 to obtain
`e5/f5>(427/22)(117/119)>19`.

Finally q<81a/22,p<3691a/880,s<225a/22, so their sum<37a/2.
Using(COST4),

    R5^(-1)<(1+27a)(1+81a)/(1-37a/2)<1+141a.

The last inequality is equivalent to a<29/9591, supplied by(SHARP).
The exact e5 formula increases with V: its numerator has derivative24/11
and its positive denominator has derivative(-6-s+7p)/22<0. At0,
`e5>(10/3)q0+F0/2>189a/20` using q0>27a/10,F0>9a/10.
Thus(N5) implies `v5<141a<15e5` and `v5<564/1351<21/50`.
It also gives `R5^(-1)<1+15e5`.

The fact that Z5 came from the preceding actual triple supplies the
additional RAW relation, writing rho=v5/e5,

    kappa*e5>(100/3)rho-250/37.                (COUPLE)

Indeed `(p+7s)²/(qs)>=100/3` from p>=q,s>=q/3, with favorable proper
denominators, gives
`kappa*e5²>(100/3)[v5-(q-s)/((1-q)(1-s))]`.
The subtracted term is at most(15/74)e5, since q<1/75. This proves
(COUPLE); no arbitrary recurring cone is inferred.

## Three more actual rows, positive2, and the ORIGINAL account

For this section abbreviate Z5=(v,-e,T,f),R=R5. Since v>4e,T>0, the
next actual row is03; its genuine source has

    A=v/(3-v), B=(e-3f+2v)/[(1-f/2)(1-v/3)], D=f/(2-f).

The next row is01: the sign of `2B-14A-7D` is that of
`12e+21fv-57f-4v<0`, excluding013 there. Put

    Abar=3-2v, Bbar=3-v, L=42-26v-6e+f(7v-3),
    hp=Abar*L/(42Bbar),
    x=v/Abar, y=6(e-3f+2v)/L,
    z=Bbar[2v-6e+(39-14v)f]/(Abar*L).

This is the genuine pair return(x,-y,Tpair,z), with x,y,z>0 and
g_pair=x+z-y>=0 by its actual01 quiet3 comparison. Owner2 stays positive
at BOTH pair tails: its03 contribution is f/2-5v/3<0, and the ENTIRE
pair contribution is

    Ppair=e/7+f/14-8v/21-fv/2<0.

Thus Tpair=(T-Ppair)/hp>0. The formal next013 hazard1 has numerator

    Qret=(486-186v)e+(1923v-308v²-2781)f+6v-50v²

over positive44Abar*L. The f coefficient is negative; substituting
f<=e/19 gives coefficient `(6453-1611v-308v²)/19>300`. Hence
`Qret>300e+6v-50v²>5v>0`. The next actual row is therefore013,
proper by original Never. Denote its hazards(P,Q,S).

Its tail Z8=(v8,-e8,T8,f8) is STRONG, with a produced stationary plane.
Indeed L>30 gives `P<y/7<v/15<2/5`. Put rho=v/e and

    F=[(100/3)rho-250/37]
         *{[6453-1611v-308v²]/19+rho(6-50v)},
    Dret=44(3-2v)(42-26v).

By(COUPLE), `kappa*Q>F/Dret`. Program B proves
`(15-v)F-120Dret>0` on `v[0,21/50],rho[4,15]` by12 coefficients.
Therefore `kappa*Q(1-P)>8>8(1-Q)`, so
`g8=v8+f8-e8>0`. Also kappa*P>8>2; the finite bracket criterion
produces PASS7 at P.

For clarity the following exact account transport keeps ORIGINAL R.
For any strong-input triple(p,q,s) with its produced weaker plane
L(p)<-k/2, put beta=(1-p)(1+e') and Pi_max as above. Then

    Dsingle=beta-(1+e_input)
       =[8ps-7p+s²+6s]/(1-s)>0,
    Csingle=h(1+e')(1+v')-2beta*Pi_max
                       -(1+e_input)(1+v_input)=Nsingle/(1-s),
    Nsingle=(11s-9p-5q)+(49s²-25ps-37qs)
       +(3s³+29ps²-7qs²-11pqs-2p²s)+7pq+11pqs²+2p²qs²>0.

Use s>=(5p+3q)/2,p<=2s/5,q<=s/4: the first two groups are at least
`37p/2+23q/2` and `119s²/4`, the third at least
`3s³+(369/20)ps²`. This needs no sign of the new tail's2 coordinate.

For the JOINT03->01->013 block define, at its last triple,

    Dpair=beta-(1+e),
    Cpair=hp*[Csingle+(1+y)(1+x)]-2beta*Ppair-(1+e)(1+v).

Program B proves Dpair>0 and Cpair>0 on the larger cone
`0<v<=1,0<e<=v/4,0<f<=e/8`, by84 and576 positive coefficients.
All denominators are positive at the produced actual rows. If alpha<=1,
the new account minus the old one, divided by ORIGINAL R, is greater
than `Cpair+2[beta-alpha(1+e)]T>0`. For the printed certificate, its Nn is exactly9d^5*Nsingle after
substitution(p,q,s)=(Pn/d,Qn/d,Sn/(3d)), Kn=42Ppair, and
Bn/(d*Tn)=beta. Consequently Cn is the numerator of Cpair over
positive5544*Abar*Bbar*d^3*Tn, and Dn is that of Dpair over d*Tn.
Thus(ACCOUNT5) gives

    R8(1+e8)(1+v8+2alpha8*T8)>1,
    R8=R5*hp*h8, alpha8=1-P.                  (ACCOUNT8)

A strong-input triple with T_input>0 and its plane has a FULL01 root
at every strong output, even before T_output is known positive. Its quiet2
numerator, after multiplication by h, is greater than

    -pq-5q/2+23s/2-8qs+pqs
         +h*v'[3-1/(2(1-p))+4e']>0.

Here p<2/5,q<1/4,s>=4q. The first group and the second coefficient
are strictly positive; quiet3 is g'>=0. At every such proper triple,
`h(e'-f')=q(1-p)+s(7+p-8q)>0`, so a strong output also has v'>0.
Apply the full-root conclusion at the actual eighth triple with Tpair>0. Original minimum forces

    R8(1+e8)(1+v8)<=1.                         (N8)

Together with(ACCOUNT8) this PRODUCES T8>0. No subsequent positive2
sign or a minimizing Z8 was assumed.

## Exact compact bounds at Z8 and a cost for the WHOLE old head

Use the pair numerators

    C=Abar*L, Vn=vL, En=6Abar(e-3f+2v),
    Fn=Bbar[2v-6e+(39-14v)f], D=44C,
    Nb=6En-21Fn-2Vn, Na=Nb+22Fn, Nc=2En-7Fn+14Vn.

The eighth hazards are(Na,Nb,Nc)/D, and

    e8=D(Na+7Nc)/[(D-Na)(D-Nc)],
    f8=D(Na-Nb)/[(D-Na)(D-Nb)].

Put e=vu,f=vur. On `v[0,21/50],u[1/15,1/4],r[0,1/19]`, Program B
proves positivity of the following polynomials, with the indicated counts:

* `[(Na+7Nc)(D-Nb)-35(Na-Nb)(D-Nc)]/v`:54;
* `2(D-Na)(D-Nc)-3D(Na+7Nc)`:63;
* `[(3700-750u)D(Na+7Nc)-44400vu²(D-Na)(D-Nc)]/v`:105;
* `{C[(D-Na)(D-Nb)(D-Nc)+8D(Na+7Nc)(D-Nb)]
      -42Bbar*D³(1+15e)}/v`:300.

The third consumes(COUPLE), the fourth `R5^(-1)<1+15e`.
Only positive actual denominators are cleared. Consequently

    e8>35f8>0, e8<2/3, kappa*e8>400,
    R8^(-1)<1+8e8.                             (BOUNDS8)

## A finite exact classifier supplies the missing ORIGINAL ratio

Program C proves

    v8<(9/4)e8                                 (RATIO8)

on the ENTIRE original residual source domain(GDS),(N5),(N8), not on a
supplied recurring cone. Its initial box is precisely

    a[0,4/1351],r[1/40,1/15],t[13/4,1211/360],z=V/a[0,2].

Set K=kappa*a, so
`K=[z(1-ar)(1-at)-r+t]/(rt)`. Every subsequent core payoff is a times
a rational scaled value; no division by a occurs. For
`Cj=(Rj^(-1)-1)/a`, the exact row cost update is
`Cnew=[Cold+sum H_i-a sum H_iH_j+a²sum H_iH_jH_k-...]/h`
for scaled hazards H_i. The exact joint pair cost and the direct cancelled
eighth hazard are printed in the program. It tests(N5),(N8) by the exact
normalized triple factor minus the previous normalized cost.

The ratio's direct numerator, in scaled eighth hazards(P,Q,S), is

    N8=9(P+7S)(1-aQ)-4(1-aP)[Q-S+KQS]
      =4h8[(9/4)e8_scaled-v8_scaled].

All interval arithmetic is OUTWARD-rounded integer/Fraction arithmetic
on the grid2^-48. The source contractions use interval upper bounds dc,sc,gc
on the nonlinear corrections of D,S,G:

    t>=(40+8r_low-sc_high)/12,
    t>=(1447+24r_low-gc_high)/431,
    t<=(121+r_high+dc_high)/36.

They use no derivative signs or floating data. At each leaf the program
proves a necessary raw/produced constraint impossible, proves an earlier
original whole gain positive, or proves N8>0. Produced-cone intersections
are conditional on the residual original-source mode; they are not new
claims about arbitrary points of the rectangle.

The deterministic exact traversal exhausts35087 nodes:13932 ratio leaves,
1916 eight-row closures,95 five-row closures,1601 residual-cone exclusions,
ZERO pending and ZERO unresolved leaves. The common ratio-numerator lower
bound on proved leaves is at least131510252969/140737488355328>0.
The program ASSERTS completeness; a limited or partial run is not a proof.

## A ninth actual013 and strict ORIGINAL Never descent

Write x=e8,r=f8/e8,rho=v8/e8. By strong g8 and(BOUNDS8),(RATIO8),
`34/35<rho<9/4`, `0<r<1/35`, `0<x<2/3`, `kappa*x>400`.
Positive2 is quiet. Positive0,3 and the failed03 quiet1 comparison force
the unique ninth actual013 row, with

    q=xA, p=xB, s=xC,
    A=(6-21r-2rho)/44>0,
    B=(6+r-2rho)/44, C=(rho+A)/3.

It is proper by original Never. Also
`p>3x/88`, `kappa*p>150/11>2`, `p<211/2310<1/10`.
The finite bracket criterion produces PASS7 at p.

The ninth output is strong. Indeed

    kappa*q(1-p)-8(1-q)
       >400A(1-xB)-8(1-xA)>859/8470>0.

For the last bound the expression decreases in rho and r on their
closed rectangle, and at those upper endpoints decreases in x. The
corner value is859/8470; derivative signs follow from A+B<=3/11 and
B<1/7. Program B also evaluates the exact corner. Thus its genuine
tail Z9=(v9,-e9,T9,f9) has v9>0 and g9>0. The strong-input quiet2
inequality already proved, with T8>0, supplies a FULL01 root at Z9
without assuming T9>=0. Its active outputs are strictly negative.

Put F9=h9(1+e9)(1+v9). Exactly

    (F9-1)/x=
      {C(5+kappa*x*A)+x[C(A+B)+6C²(kappa*x*A-2)]
       +x²[6AC²+BC²(kappa*x*A-2)]+x³ABC²}/(1-xC).

All omitted terms are positive since kappa*q>90/11>2. Therefore
`(F9-1)/x>C(5+400A)>=9657/968>8`. The expression decreases in r;
at r=1/35 it is concave in rho on[34/35,9/4], with endpoint values
51/4 and9657/968. Combining with(BOUNDS8) gives

    R8*F9>1.

The old source has ORIGINAL Never `m=R8*h9*nu(Z9)`. The full01
replacement has negative outputs and zero full debt, but original Never
`nu(Z9)/[(1+e9)(1+v9)]<m`. This contradicts the ORIGINAL restricted
minimum. All nine old rows are charged; no tail was minimizing.

## Exact finite-core boundary test

The weak boundary V=0 is included, not handled by division by V. A
complete auxiliary Nash core exercising BOTH failed early comparisons is

    a=3/2000,b=9/100000,c=1005951/200000000,V=0,
    kappa=(c-b)/(bc), k=2-kappa.

Set all31 free entries of(R) to0 except this k. Reconstruct the original
three pair rows, the forced extra013, the03->01->013 return and the ninth013.
At the final core annotation choose T9=1. Program D prices BOTH actions of
all four players at every reconstructed row by exact coalition enumeration.
It verifies all quiet comparisons, positive2 throughout, original AB,
negative outputs of the final01 comparison, and the exact signs

    R5(1+e5)(1+v5)-1<0,
    R8(1+e8)(1+v8)-1<0,
    R9(1+e9)(1+v9)-1>1.

Thus the last finite step does work beyond both earlier failed comparisons.
This is an AUXILIARY terminal-annotation test: no genuine E realization,
original Never tuple, positive absorbing gap or selected minimum is assigned
to the annotation. It is not a UE counterexample or new existence-class
witness. The class exclusion itself is proved by the universal exact
certificates and actual-source consumer above.

## Exact proof programs

Every coefficient program uses the exact homogeneous interval substitution
`t=(l+uX)/(d(1+X))` on an axis[l/d,u/d], multiplying by the positive
`d^n(1+X)^n`. Its coefficients have the interval Bernstein signs.
Strict positivity of all generated coefficients proves positivity on the
entire closed box, including upper faces. No payload, numerical root
decision, external data file or CAS is used. Program C instead uses
finite exact interval subdivision and asserts that every leaf is discharged.

Each program is standalone and runs in a fresh Python process.

### Program A: original-source and global budget checks

```python
"""Self-contained exact finite-nine initial source and budget certificates.
Integer polynomial arithmetic only; no CAS, input files or coefficient payloads.
"""
from math import comb

def clean(p):return {e:c for e,c in p.items()if c}
def C(c):return {(0,0,0,0):c}if c else {}
def add(*ps):
 out={}
 for p in ps:
  for e,c in p.items():out[e]=out.get(e,0)+c
 return clean(out)
def sc(p,c):return clean({e:c*v for e,v in p.items()})
def sub(p,q):return add(p,sc(q,-1))
def mul(*ps):
 out=C(1)
 for p in ps:
  z={}
  for e,c in out.items():
   for f,d in p.items():
    g=tuple(x+y for x,y in zip(e,f));z[g]=z.get(g,0)+c*d
  out=clean(z)
 return out
def pw(p,n):return mul(*([p]*n))
a={(1,0,0,0):1};rr={(0,1,0,0):1};tt={(0,0,1,0):1};vv={(0,0,0,1):1};one=C(1)
b=mul(a,rr);c=mul(a,tt);V=mul(a,vv)
x=sub(sc(c,3),b);u=add(one,x);v=add(one,sc(x,2));w=add(one,sc(x,5))
h=add(sc(a,7),c);vh=add(one,h);j=sub(sub(sc(a,9),b),sc(c,2))
Q=add(mul(u,add(sub(one,sc(x,4)),mul(h,add(C(8),sc(x,3))))),mul(add(C(7),sc(x,8)),j))
Dr=add(sc(mul(h,u,u),7),mul(sub(sc(u,8),x),j),sc(mul(x,vh,u),-9))
BP=add(sc(mul(h,u),7),sc(j,6),sc(mul(x,vh),-6))
G=add(sc(mul(x,Q),18),sc(mul(v,Dr),-6),sc(mul(w,u,BP),-7))
D=mul(sub(one,a),sub(one,b),sub(one,c));d=sc(D,44)
En=mul(add(a,sc(c,7)),sub(one,b));Fn=mul(sub(a,b),sub(one,c))
Qn=add(sc(En,6),sc(Fn,-21),sc(mul(V,D),-2));Pn=add(Qn,sc(Fn,22));Rn=add(mul(d,V),Qn)
Abig=add(sc(pw(d,2),3),sc(mul(Rn,d),6),mul(Pn,Rn))
twice_charge=add(sc(mul(a,c),4),sc(mul(b,c),-9),sc(mul(a,b,c),-2),sc(mul(a,b),-1),mul(a,V,sub(one,b),sub(one,c)))
AN=add(sc(mul(x,Q,w),27),sc(mul(u,w,w,BP),-7),sc(mul(v,add(one,sc(x,17)),Dr),2),sc(mul(j,x,v,w),-3),sc(mul(u,v,w,twice_charge),-1))
Den=sc(mul(D,u,v,w,pw(d,3),Abig),6)
N=add(sc(mul(pw(d,3),Abig,AN),3),sc(mul(u,v,w,pw(d,3),Abig,add(mul(D,sub(one,V)),En,sc(Fn,-4))),3),sc(mul(D,u,v,w,pw(d,2),Abig,add(sc(Pn,-3),sc(Qn,-9),sc(Rn,4))),2),mul(D,u,v,w,Abig,Qn,Rn,sub(sc(Pn,2),d)),sc(mul(w,w,Q,pw(d,4),sub(sc(d,3),Rn)),-3))
res=sub(sc(N,18964),sc(mul(G,Den),4007))
assert all(e[0]>=1 for e in res)
P={(e[0]-1,e[1],e[2],e[3]):c for e,c in res.items()}
def strip(p,axis,n):
 assert all(e[axis]>=n for e in p)
 return {e[:axis]+(e[axis]-n,)+e[axis+1:]:c for e,c in p.items()}
def transform(p,box):
 deg=tuple(max(e[k] for e in p) for k in range(4))
 for axis,(lo,up,den) in enumerate(box):
  n=deg[axis]
  T=[[den**(n-j)*sum(comb(j,h)*lo**(j-h)*up**h*comb(n-j,i-h)
    for h in range(max(0,i-n+j),min(i,j)+1)) for j in range(n+1)]for i in range(n+1)]
  groups={}
  for e,c in p.items():
   key=e[:axis]+e[axis+1:];groups.setdefault(key,[0]*(n+1))[e[axis]]=c
  out={}
  for key,vec in groups.items():
   for i,row in enumerate(T):
    z=sum(t*v for t,v in zip(row,vec))
    if z: out[key[:axis]+(i,)+key[axis:]]=z
  p=out
 return deg,p

def check(name,p,box,expected):
 deg,transformed=transform(p,box)
 assert len(transformed)==expected==(deg[0]+1)*(deg[1]+1)*(deg[2]+1)*(deg[3]+1)
 assert all(c>0 for c in transformed.values())
 print(name,'PASS',deg,expected,'strict positive coefficients',flush=True)
check('Original global quiet2 budget',P,[(0,2,525),(0,1,10),(13,14,4),(0,27,1)],29484)
Sraw=add(sc(mul(u,sub(x,h)),7),mul(add(one,sc(x,9)),j))
ratio=sc(add(sc(G,36),mul(sub(C(491),sc(a,4800)),Dr),mul(sub(C(180),sc(a,14400)),Sraw)),-1)
check('Original b<a/15',strip(ratio,0,1),[(0,4,1351),(2,3,30),(1170,1211,360),(0,1,1)],80)
Kn=add(mul(V,sub(one,b),sub(one,c)),sub(c,b));bc=mul(b,c)
Bn=add(sc(mul(pw(d,2),bc),3),sc(mul(Rn,d,bc),-2),mul(add(Kn,bc),Qn,Rn))
gain5=strip(sub(mul(D,u,v,Abig,Bn),sc(mul(w,Q,pw(d,3),bc,sub(sc(d,3),Rn)),3)),0,3)
check('Original r>1/40',gain5,[(0,4,1351),(0,1,40),(1170,1211,360),(0,27,1)],11880)
check('Original V/a<2',gain5,[(0,4,1351),(0,1,15),(1170,1211,360),(2,27,1)],11880)
Aplus=add(one,sc(c,6),mul(a,c))
Lplus=add(D,sc(mul(b,sub(one,a)),3),sc(mul(c,add(C(7),a,sc(b,-8))),3))
Ntarget=sub(mul(u,v,Aplus,Lplus),mul(w,Q,sub(one,a),sub(one,c)))
check('Old four-row low-t exclusion',strip(sc(G,-1),0,1),[(0,2,525),(0,1,1),(10,11,4),(0,1,1)],80)
check('Old four-row K3 residual',strip(sub(sc(Ntarget,431),sc(G,36)),0,1),[(0,2,525),(0,1,1),(11,18,4),(0,1,1)],168)
```

### Program B: stationary, joint return and ninth-row checks

```python
"""Exact joint03→01→013 account certificate, factorized integer regenerator.
No CAS, coefficient payloads, input files or floating point.
"""
from math import comb

def clean(p):return {e:c for e,c in p.items()if c}
def C(c):return {(0,0,0):c}if c else {}
def add(*ps):
 out={}
 for p in ps:
  for e,c in p.items():out[e]=out.get(e,0)+c
 return clean(out)
def sc(p,c):return clean({e:c*v for e,v in p.items()})
def sub(p,q):return add(p,sc(q,-1))
def mul(*ps):
 out=C(1)
 for p in ps:
  z={}
  for e,c in out.items():
   for f,d in p.items():
    g=tuple(x+y for x,y in zip(e,f));z[g]=z.get(g,0)+c*d
  out=clean(z)
 return out
def pw(p,n):return mul(*([p]*n))
def check(name,p,box,expected,divide=True):
 if divide:
  assert all(e[0]>=1 for e in p)
  p={(e[0]-1,e[1],e[2]):c for e,c in p.items()}
 deg=tuple(max(e[k]for e in p)for k in range(3))
 for axis,(lo,up,den)in enumerate(box):
  n=deg[axis];out={}
  for e,c in p.items():
   k=e[axis]
   for j in range(k+1):
    for h in range(n-k+1):
     ee=list(e);ee[axis]=j+h;ee=tuple(ee)
     out[ee]=out.get(ee,0)+c*comb(k,j)*lo**(k-j)*up**j*comb(n-k,h)*den**(n-k)
  p=clean(out)
 assert len(p)==expected==(deg[0]+1)*(deg[1]+1)*(deg[2]+1)
 assert all(c>0 for c in p.values())
 print(name,'PASS',deg,expected,'strict positive coefficients',flush=True)
v={(1,0,0):1};r={(0,1,0):1};z={(0,0,1):1};one=C(1)
e=mul(v,r);f=mul(e,z)
A=sub(C(3),sc(v,2));B=sub(C(3),v)
L=add(C(42),sc(v,-26),sc(e,-6),mul(f,sub(sc(v,7),C(3))))
En=sc(mul(A,add(e,sc(f,-3),sc(v,2))),6)
Fn=mul(B,add(sc(v,2),sc(e,-6),mul(sub(C(39),sc(v,14)),f)))
d=sc(mul(A,L),44)
Qn=add(sc(En,6),sc(Fn,-21),sc(mul(v,L),-2))
Pn=add(Qn,sc(Fn,22));Sn=add(sc(mul(v,L),44),Qn)
T=sub(sc(d,3),Sn)
Bn=add(sc(pw(d,2),3),sc(mul(Sn,d),6),mul(Pn,Sn))
Kn=add(sc(e,6),sc(f,3),sc(v,-16),sc(mul(f,v),-21))
Nn=add(sc(mul(pw(d,4),add(sc(Sn,11),sc(Pn,-27),sc(Qn,-15))),3),mul(pw(d,3),add(sc(pw(Sn,2),49),sc(mul(Pn,Sn),-75),sc(mul(Qn,Sn),-111))),mul(pw(d,2),add(pw(Sn,3),sc(mul(Pn,pw(Sn,2)),29),sc(mul(Qn,pw(Sn,2)),-7),sc(mul(Pn,Qn,Sn),-33),sc(mul(pw(Pn,2),Sn),-6))),sc(mul(pw(d,3),Pn,Qn),63),sc(mul(d,Pn,Qn,pw(Sn,2)),11),sc(mul(pw(Pn,2),Qn,pw(Sn,2)),2))
Cn=add(mul(A,Nn),sc(mul(B,pw(d,3),T,add(mul(A,L),En)),132),sc(mul(A,B,pw(d,2),Bn,Kn),-264),sc(mul(A,B,pw(d,3),T,add(one,e),add(one,v)),-5544))
Dn=sub(Bn,mul(d,T,add(one,e)))

check('Joint account constant',Cn,[(0,1,1),(0,1,4),(0,1,8)],576)
check('Joint account T coefficient',Dn,[(0,1,1),(0,1,4),(0,1,8)],84)
Knum=sub(sc(r,3700),C(750))
Anum=add(C(6453),sc(v,-1611),sc(pw(v,2),-308),sc(mul(r,sub(C(6),sc(v,50))),19))
P12=sub(mul(sub(C(15),v),Knum,Anum),sc(mul(sub(C(3),sc(v,2)),sub(C(42),sc(v,26))),120*2109*44))
check('Eighth strong return',P12,[(0,21,50),(4,15,1),(0,1,1)],12,False)
Nc=add(sc(En,2),sc(Fn,-7),sc(mul(v,L),14))
ratio=sub(mul(add(Pn,sc(Nc,7)),sub(d,Qn)),sc(mul(sub(Pn,Qn),sub(d,Nc)),35))
upper=sub(sc(mul(sub(d,Pn),sub(d,Nc)),2),sc(mul(d,add(Pn,sc(Nc,7))),3))
scale=sub(mul(sub(C(3700),sc(r,750)),d,add(Pn,sc(Nc,7))),sc(mul(v,pw(r,2),sub(d,Pn),sub(d,Nc)),44400))
cost=sub(mul(A,L,add(mul(sub(d,Pn),sub(d,Qn),sub(d,Nc)),sc(mul(d,add(Pn,sc(Nc,7)),sub(d,Qn)),8))),sc(mul(B,pw(d,3),add(one,sc(e,15))),42))
cone=[(0,21,50),(4,15,60),(0,1,19)]
check('Eighth ratio35',ratio,cone,54)
check('Eighth e<2/3',upper,cone,63,False)
check('Eighth kappa e>400',scale,cone,105)
check('Original inverse survival cost<1+8e8',cost,cone,300)
P7=add(sc(pw(v,7),3872),sc(pw(v,6),46328),sc(pw(v,5),-210836),sc(pw(v,4),326040),sc(pw(v,3),-243096),sc(pw(v,2),93396),sc(v,-17031),C(999))
check('Quantitative stationary plane',sc(P7,-1),[(4,5,10),(0,1,1),(0,1,1)],8,False)
from fractions import Fraction as F
r0,rho,x0=F(1,35),F(9,4),F(2,3)
A0,B0=(6-21*r0-2*rho)/44,(6+r0-2*rho)/44
assert 400*A0*(1-x0*B0)-8*(1-x0*A0)==F(859,8470)>0
margins=[]
for rho in (F(34,35),F(9,4)):
 A0=(6-21*r0-2*rho)/44
 margins.append((rho+A0)*(5+400*A0)/3)
assert margins==[F(51,4),F(9657,968)] and min(margins)>8
print('PASS: exact ninth strong and whole-head gain margins.',flush=True)
```

### Program C: complete exact original-box ratio classifier

```python
"""Exact interval exploration of the original nine-row absorption route.

All proof decisions use Fraction intervals. A budget-limited run is only
diagnostic; completeness requires an empty remaining stack. No data inputs.

The certified population is the RESIDUAL original-source mode with failed
gain5 and gain8 comparisons. Produced-cone intersections are necessary for
that population, not assertions about every arbitrary point of the box.
"""
from fractions import Fraction as F
import argparse

# Every operation rounds OUTWARD to this exact dyadic grid. This prevents
# nested rational divisions from growing denominators without using floats.
PREC=1<<48

class I:
    __slots__=('lo','hi')
    def __init__(self,a,b=None):
        a=F(a);b=F(a if b is None else b)
        self.lo=F((a.numerator*PREC)//a.denominator,PREC)
        self.hi=F(-((-b.numerator*PREC)//b.denominator),PREC)
    def __add__(self,y):
        y=cv(y);return I(self.lo+y.lo,self.hi+y.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,y):return self+-cv(y)
    def __rsub__(self,y):return cv(y)+-self
    def __mul__(self,y):
        y=cv(y);v=[self.lo*y.lo,self.lo*y.hi,self.hi*y.lo,self.hi*y.hi]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,y):
        y=cv(y)
        if y.lo<=0<=y.hi:raise ZeroDivisionError
        return self*I(1/y.hi,1/y.lo)
    def __rtruediv__(self,y):return cv(y)/self
    def __pow__(self,n):
        assert n>=0
        if n==0:return I(1)
        if n%2==0:
            lo=0 if self.lo<=0<=self.hi else min(self.lo**n,self.hi**n)
            return I(lo,max(self.lo**n,self.hi**n))
        return I(self.lo**n,self.hi**n)
    def intersect(self,lo=None,hi=None):
        l=self.lo if lo is None else max(self.lo,F(lo))
        h=self.hi if hi is None else min(self.hi,F(hi))
        if l>h:raise Empty
        return I(l,h)
    def __repr__(self):return f'[{self.lo},{self.hi}]'
def cv(x):return x if isinstance(x,I) else I(x)
class Empty(Exception):pass

def update(cost,hs,a):
    # (R_new^-1-1)/a, with actual hazards a*hs.
    h=I(1);coeff=[I(1)]
    for x in hs:
        h*=1-a*x
        cc=[I(0)]*(len(coeff)+1)
        for i,c in enumerate(coeff):cc[i]+=c;cc[i+1]-=c*x
        coeff=cc
    n=cost
    for i in range(1,len(coeff)):n-=coeff[i]*(a**(i-1))
    return n/h,h

def triple_factor(P,Q,S,K,a):
    # [h(1+e_tail)(1+v_tail)-1]/a; no cancellation at a=0.
    kk=K*Q-2
    return (S*(5+K*Q)+a*(S*(P+Q)+6*S*S*kk)
            +a*a*(6*Q*S*S+P*S*S*kk)+a**3*P*Q*S*S)/(1-a*S)

def evaluate(box):
    a,r,t,z=[I(*x)for x in box]
    # Necessary interval contractions from D>0,S>=0,G>0. The discarded
    # portions cannot contain an actual source; no root sampling is used.
    for _ in range(3):
        X=3*t-r;H=7+t
        dc=a*X*(98+2*r-36*t)-2*a*a*H*X*X
        sc=a*X*(32-16*r-4*t)
        gc=a*(r-3*t)*(96*r-1337*t+4273)
        gc-=a*a*(r-3*t)**2*(96*r-901*t+2309)
        gc-=43*a**3*(r-3*t)**3*(t+7)
        t=t.intersect(lo=max((40+8*r.lo-sc.hi)/12,
                             (1447+24*r.lo-gc.hi)/431),
                      hi=(121+r.hi+dc.hi)/36)
    X=3*t-r;H=7+t;JJ=9-r-2*t
    D=121+r-36*t+a*X*(98+2*r-36*t)-2*a*a*H*X*X
    S=12*t-8*r-40+a*X*(32-16*r-4*t)
    G=-24*r+431*t-1447+a*(r-3*t)*(96*r-1337*t+4273)
    G-=a*a*(r-3*t)**2*(96*r-901*t+2309)
    G-=43*a**3*(r-3*t)**3*(t+7)
    if D.hi<=0 or G.hi<=0 or S.hi<0:return 'source',None
    dd=(1-a)*(1-a*r)*(1-a*t)*(1+a*X)*(1+2*a*X)
    cs=[-5*r-8*t+120,
        19*r*r+37*r*t-748*r-285*t*t+2240*t,
        -18*r**3+31*r*r*t+771*r*r+309*r*t*t-4613*r*t-720*t**3+6903*t*t,
        -(r-3*t)*(17*r*r*t+107*r*r-96*r*t*t-631*r*t+135*t**3+939*t*t),
        2*r*t*(r-3*t)**2]
    C4=sum(c*(a**i)for i,c in enumerate(cs))/dd
    E=(1+7*t)/((1-a)*(1-a*t))
    FF=(1-r)/((1-a)*(1-a*r))
    K=(z*(1-a*r)*(1-a*t)-r+t)/(r*t)
    q=(6*E-21*FF-2*z)/44;p=q+FF/2;s=(z+q)/3
    gate5=triple_factor(p,q,s,K,a)-C4
    if gate5.lo>0:return 'gain5',None
    C5,h5=update(C4,[p,q,s],a)
    V5=(q-s+K*q*s)/((1-a*q)*(1-a*s))
    E5=(p+7*s)/((1-a*p)*(1-a*s))
    F5=(FF/2)/((1-a*p)*(1-a*q))
    # Produced cone, used only as safe interval intersections.
    V5=V5.intersect(lo=4*E5.lo,hi=15*E5.hi)
    E5=E5.intersect(lo=V5.lo/15,hi=V5.hi/4)
    F5=F5.intersect(lo=0,hi=E5.hi/19)
    av=(a*V5).intersect(lo=0,hi=F(21,50))
    af=a*F5
    AA=3-2*av;BB=3-av
    LL=42-26*av-6*a*E5+af*(7*av-3)
    C7=(42*BB*C5+120*V5+18*E5+9*F5
        -a*(52*V5*V5+12*E5*V5+27*F5*V5)
        +14*a*a*F5*V5*V5)/(AA*LL)
    V7=V5/AA
    E7=6*(E5-3*F5+2*V5)/LL
    F7=BB*(2*V5-6*E5+(39-14*av)*F5)/(AA*LL)
    F7=F7.intersect(lo=0)
    q8=((486-186*av)*E5+(1923*av-308*av*av-2781)*F5
         +6*V5-50*a*V5*V5)/(44*AA*LL)
    # Actual produced 013 row; positivity is already proved by its producer.
    q8=q8.intersect(lo=0);p8=q8+F7/2;s8=(V7+q8)/3
    gate8=triple_factor(p8,q8,s8,K,a)-C7
    if gate8.lo>0:return 'gain8',None
    ratio=9*(p8+7*s8)*(1-a*q8)-4*(1-a*p8)*(q8-s8+K*q8*s8)
    ratio_alt=9*p8-4*q8+67*s8-4*K*q8*s8
    ratio_alt+=a*(-5*p8*q8-63*q8*s8-4*p8*s8+4*K*p8*q8*s8)
    if max(ratio.lo,ratio_alt.lo)>0:
        return 'proved',(max(ratio.lo,ratio_alt.lo),)
    C8,h8=update(C7,[p8,q8,s8],a)
    V8=(q8-s8+K*q8*s8)/((1-a*q8)*(1-a*s8))
    E8=(p8+7*s8)/((1-a*p8)*(1-a*s8))
    F8=(F7/2)/((1-a*p8)*(1-a*q8))
    E8=E8.intersect(lo=400/K.hi)
    F8=F8.intersect(lo=0,hi=E8.hi/35)
    V8=V8.intersect(lo=E8.lo-F8.hi)
    # Failed eighth gain supplies a stronger safe cap on V8.
    V8=V8.intersect(hi=((C8-E8)/(1+a*E8)).hi)
    ratio=F(9,4)*E8-V8
    if ratio.lo>0 and h8.lo>0:return 'proved',(4*h8.lo*ratio.lo,)
    return 'split',(ratio,gate5,gate8,t.lo,t.hi)

INITIAL=[(F(0),F(4,1351)),(F(1,40),F(1,15)),
         (F(13,4),F(1211,360)),(F(0),F(2))]

def main():
    pa=argparse.ArgumentParser();pa.add_argument('--nodes',type=int,default=100000)
    pa.add_argument('--depth',type=int,default=64);args=pa.parse_args()
    stack=[(INITIAL,0)];counts={};n=0;mins=None;unresolved=[]
    while stack and n<args.nodes:
        box,depth=stack.pop();n+=1
        try:tag,data=evaluate(box)
        except Empty:tag,data='cone',None
        except ZeroDivisionError:tag,data='split',None
        if n%1000==0:print('nodes',n,'pending',len(stack),'counts',counts,flush=True)
        if tag!='split':
            counts[tag]=counts.get(tag,0)+1
            if tag=='proved':mins=data if mins is None else tuple(min(x,y)for x,y in zip(mins,data))
            continue
        if depth>=args.depth:unresolved.append((box,data));continue
        if data is not None:
            # Discard only the t region excluded by the necessary source
            # contractions; subsequent bisection covers the retained region.
            box=list(box)
            box[2]=(max(box[2][0],data[-2]),min(box[2][1],data[-1]))
        # Exact normalized-width split; deterministic and independent of samples.
        sizes=[(hi-lo)/(INITIAL[i][1]-INITIAL[i][0])for i,(lo,hi)in enumerate(box)]
        j=max(range(4),key=lambda i:sizes[i]);lo,hi=box[j];mid=(lo+hi)/2
        left=list(box);right=list(box);left[j]=(lo,mid);right[j]=(mid,hi)
        stack.append((right,depth+1));stack.append((left,depth+1))
    print('NODES',n,'COUNTS',counts,'PENDING',len(stack),'UNRESOLVED',len(unresolved),flush=True)
    if mins:print('MIN_CERTIFIED_RATIO_NUMERATOR',mins,flush=True)
    for box,data in (unresolved[:2]or stack[:2]):print('BOX',box,'DETAIL',data,flush=True)
    print('COMPLETE',not stack and not unresolved,flush=True)
    assert not stack and not unresolved, 'Incomplete search is not a proof.'
if __name__=='__main__':main()
```


### Program D: exact nine-row auxiliary-core boundary test

```python
"""Exact finite Nash-core boundary test. No actual E/minimum is asserted."""
from fractions import Fraction as F
from itertools import combinations

G=[[0,-2,-5,4],[-6,0,-4,6],[1,3,0,-5],[1,-1,4,0]]
a=F(3,2000);b=F(9,100000);c=F(1005951,200000000)
kappa=(c-b)/(b*c)
fixed={(0,3):-1,(0,9):3,(1,3):-7,(1,10):-1,(3,9):2,
       (3,10):-2,(0,11):2,(1,11):-8,(3,11):0,(2,3):4,
       (3,3):0,(1,9):0,(2,9):-4,(0,10):2-kappa}
def reward(i,S):
    if len(S)==1:return F(G[i][next(iter(S))])
    return F(fixed.get((i,sum(1<<j for j in S)),0))
def offers(i,q):
    others=[j for j in range(4)if j!=i];Q=P=F(0);H=F(1)
    for j in others:H*=1-q[j]
    for n in range(4):
        for sub in combinations(others,n):
            S=set(sub);mass=F(1)
            for j in others:mass*=q[j]if j in S else 1-q[j]
            Q+=mass*reward(i,S|{i})
            if S:P+=mass*reward(i,S)
    return Q,P,H
def prefix(q,y,check=False):
    out=[]
    for i in range(4):
        Q,P,H=offers(i,q);C=P+H*y[i]
        if check:assert Q==C if q[i]>0 else Q<=C
        out.append(q[i]*Q+(1-q[i])*C)
    return out
def tail(q,y):
    h=F(1)
    for x in q:h*=1-x
    immediate=prefix(q,[F(0)]*4)
    return [(y[i]-immediate[i])/h if i!=2 else F(0)for i in range(4)]
def triple(y):
    v,e,f=y[0],-y[1],y[3]
    q=(6*e-21*f-2*v)/44;p=q+f/2;s=(v+q)/3
    row=[p,q,F(0),s];assert min(p,q,s)>0 and max(p,q,s)<1
    return row,tail(row,y)
E=(a+7*c)/((1-a)*(1-c));F0=(a-b)/((1-a)*(1-b))
Y=[F(0),-E,F(0),F0];q4=[a,b,F(0),c]
w=prefix(q4,Y)
q3=[-w[1]/(1-w[1]),w[0]/(1+w[0]),F(0),F(0)]
w=prefix(q3,w)
q2=[w[3]/(1+w[3]),F(0),F(0),-w[0]/(1-w[0])]
w=prefix(q2,w)
q1=[-w[1]/(1-w[1]),w[0]/(1+w[0]),F(0),F(0)]
rows=[q1,q2,q3,q4];states={}
q5,Y5=triple(Y);rows.append(q5);states[5]=Y5
q6=[Y5[3]/2,F(0),F(0),Y5[0]/3];Y6=tail(q6,Y5);rows.append(q6)
q7=[-Y6[1]/7,-Y6[0],F(0),F(0)];Y7=tail(q7,Y6);rows.append(q7)
q8,Y8=triple(Y7);rows.append(q8);states[8]=Y8
q9,Y9=triple(Y8);rows.append(q9);states[9]=Y9
R=F(1);gains={}
for n,row in enumerate(rows,1):
    assert all(0<=x<1 for x in row)
    for x in row:R*=1-x
    if n in states:
        y=states[n];gains[n]=R*(1-y[1])*(1+y[0])-1
assert gains[5]<0 and gains[8]<0 and gains[9]>1
assert Y8[0]<F(9,4)*(-Y8[1])
y=[Y9[0],Y9[1],F(1),Y9[3]]
new=prefix([-y[1]/(1-y[1]),y[0]/(1+y[0]),F(0),F(0)],y,True)
assert new[0]<0 and new[1]<0
for row in reversed(rows):
    y=prefix(row,y,True);assert y[2]>0
A0,B0,C0,D0=-y[0],-y[1],y[2],y[3]
assert min(A0,B0,C0,D0)>0
assert B0<6*(A0-D0)and C0>5*A0+4*A0*D0-D0
print('PASS: exact V=0 nine-row Nash core; gains5,8<0<gain9; all quiet and original-AB tests.')
```

## Source correspondence and boundary of the result

The full-cap and debt source declarations are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`,
`quittingTerminalDeviationDebt_nonneg`, and
`quittingTerminalDeviationDebt_rootThenContinuation_eq`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`), together
with `quittingTerminalPayoff_rootThenContinuation_eq`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`).
The general approximate-profile decomposition used here follows directly
from the first two prefix identities; a Nash-specific theorem is not
applied to a non-Nash approximant. Finite auxiliary Nash existence is
the usual finite-game theorem, whose source declaration is
`exists_isZeroQuittingRootNash`
(`UniformEquilibrium/Quitting/Root/NashExistence.lean`). This is ordinary
mathematics, not a new Lean verification.

The only input mode is the actual four-row head over the ORIGINAL
selected source. Every new tail sign, stationary bracket, continuation
support, account and competitor used in the consumer is produced.
No executed infinite head, extrapolated stationary plane, unknown
recurrent cone or successful root is supplied as a premise.

This closes the low nonnegative four-row mode and includes V=0. It
does not consume negative V or any other original source class, the
other four-row tail sectors, negative-owner2 sources, arbitrary rewards
or Fin4. The conclusion is a finite actual-source-mode exclusion, not
a reward-table existence theorem or an unrestricted strategy-class claim.

## Lean handoff

Use a compact carrier C of actual-profile tuples(U,B,e,N), retaining the
ORIGINAL Never vector N as a separate coordinate, and define E by B=U.
A theorem such as `no_low_nonnegative_four_row_source` should quantify
the raw table satisfying(R), A_Z>0, an ORIGINAL restricted minimizer
X in E with nu(X)=m and signs(-,-,+,+), and its genuine four-row
factorization01->03->01->013 with the stated source signs and positive2
caps. For final hazards(a,b,0,c) and genuine E tail(V,-E0,T,F0), its
conclusion is `not (0<=V and V<E0-F0)`.

The further actual finite-cut compiler is proved from negative owner1,
compactness and the full debt decomposition. The stationary brackets,
positive2 signs, additional rows and full-cap roots are subsequent
outputs. Formalize the exact polynomial identities and positive interval
coefficient transforms, then the exhaustive rational interval certificate
with coverage and strict positivity. Completeness must be proved, not
assumed from a reported node count. None of these produced strategies,
rates, brackets or successful comparisons is an input structure field.

Reuse `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`,
`quittingTerminalDeviationDebt_nonneg`,
`quittingTerminalPayoff_rootThenContinuation_eq`, and
`exists_isZeroQuittingRootNash` from the tracked sources named above.
Keep the general approximant debt identity distinct from the
Nash-specific `quittingTerminalDeviationDebt_rootThenContinuation_eq`.
The last step is the finite full-cap prefix construction and strict
decrease of the retained ORIGINAL nu, contradicting the input minimum.
