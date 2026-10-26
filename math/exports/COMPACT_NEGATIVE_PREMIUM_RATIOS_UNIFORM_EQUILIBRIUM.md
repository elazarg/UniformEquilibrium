# Uniform equilibria on every compact negative-premium ratio band

This packet gives an actual equilibrium producer on every compact strictly
negative ratio band of a canonical two-premium family. It uses finite
support selection and a connected terminal-phase argument. It is ordinary
mathematics, not checked in Lean. Arbitrary signed Fin4 remains open.

## 1. Raw theorem

There are four players0,1,2,3 choosing Continue or Quit independently at
each live date. The first nonempty quitting coalitionD absorbs at rewardr(D).
Live play and literal AllNever payzero. Putkappa_i=r_i({i}) and define
Z_i(D)=r_i(D)-kappa_i only for nonemptyD. Native own-singletons arezero.
Fix the following native entries:

```
D       Z0     Z1     Z2     Z3
0        0      2      2     -1
1        3      0     -2     -2
2       -1      1      0      1
3        3     -3     -1      0
12     -12     -K      p     -6
13       2   -100     -1      0
23      -6      9      3   -100
123     -8     11      2      1
```

The seven row0 rewards on nonsingleton coalitions containing0 are at mostzero.
The other21 entries on those coalitions and all four original own levels are
arbitrary independently.

**Theorem.** For every fixed0<q_-<=q_+<infinity there is one finiteC>=100
such that every game in this family with

    K>=C, -q_+ K<=p<=-q_- K

has a uniform-equilibrium payoff against all unilateral behavioral replacements.
The target is fixed before accuracy. C is independent of the21 unrestricted
joining entries and the original own levels. No numericalC and no coefficient
perturbation extension are asserted.

Writealpha=1/K andbeta=p/K=-q<0. The proof first builds a local producer
near eachq>0, then takes a finite cover of[q_-,q_+]. Its essential boundary
is exact current row2 valuezero; it never treats a discrete negative crossing
as an equilibrium entrance.

## 2. The negative selector at alpha zero

A supplied successor has native coordinates(T0,-L,X,W alpha). At alpha0,
assume

    L>0, X>=0, L+3X<=1, 97X<4L, -100L<=W<=0.       (1)

Set u=w/(1-w). For u in[X/4,L/97] define

    Z=L-97u, Y=(X-4u)/beta,
    f(u)=2Y-101Z.

Both hazards Y,Z are nonnegative. The derivative is

    f'(u)=9797-8/beta=9797+8/q>0.

At the upper endpointZ=0 andY>0, so f(L/97)>0>=W.
If W<=f(X/4), use pair23:

    u=X/4, Y=0, Z=-W/101.

Otherwise use the unique triple rootf(u)=W in(X/4,L/97).
At the switch the roots coincide. The pair23 quiet1 condition is
Z>=L-97u, which is exactlyW<=f(X/4). Thus this is a continuous actual
support selector, not an infeasible triple extrapolation.

In both branches the actual current values obey

    L'=(L+3u)/(1+u), X'=(X-u)/(1+u), W'=-100Z.      (2)

As long asX'>=0, L increases, X decreases, L+3X decreases, and the ratio
97X<4L persists. The quantityv=W+100L remains nonnegative. On triple,

    v'=u[9700+100(3-L)/(1+u)]>=0;

on pair23,

    v'=(100/101)v+(100/101)L+100(L'-L)>=0.

AlsoW'<=0. Consequently the selector can always be iterated while the
suppliedX is nonnegative; its final output may haveX'<0.

There is a UNIFORM positive step size on compact negative-ratio bands.
On triple,

    u=[101L+W+2X/q]/[9797+8/q]>=L/[9797+8/q].       (3)

On pair23 its selection andW>=-100L imply
9797X/4>=L, so u=X/4>=L/9797, which is stronger. Thus ifL>=L_min>0,
X decreases at each step by at least a fixed positive constant depending
only onL_min,q_-. The first crossingX<=0 occurs after finitely many steps,
uniformly on compactq bands. This crossing does NOT itself give exactzero;
Sections3--5 supply the connected phase parameter that does.

The exact invariant is

    H=(L+3X)/(1+X),
    L=H-(3-H)X.                                   (4)

The desired entranceX=0 therefore hasL=H. Notice that no pair12 tail with
negativeX is used or needed.

## 3. A terminal phase arc and its exact endpoint identification

First fixalpha0 and H near3/4. A terminal triple root must haveY=101Z/2.
Its current values satisfy(4) precisely when

    u=[H-AZ]/D,
    A=1-(101/2)(3-H)q, D=109-4H.                  (5)

Its successor has

    x=Z+97u, E2=4u-(101/2)qZ, W_successor=0.

The wash surplus is

    E2-(3/100)x=(109/100)u-[(3/100)+(101/2)q]Z.     (6)

LetZ run from0 to

    Z_wash=(109/100)H
      /[(109/100)A+D((3/100)+(101/2)q)].            (7)

Its denominator is

    4.36-.12H+(101/2)(105.73-2.91H)q>0.

Thus the arc is physical, with positiveu, nonnegativeY,Z, and nonnegative
wash surplus, strict except atZ=Z_wash. Its currentX is positive: at the
wash endpoint it is at least1.91u/(1+u), and the numerator is affine along
the arc. The endpoint formulas give

    Z<=1.09H/(4.36-.12H), u<=H/(105.73-2.91H).

For H near.75 these implyZ<.21,u<.008, henceX<.024 andx<1. Then
L=H-(3-H)X gives97X<4L andL+3X=H(1+X)<1. All initial cone margins
except the permitted terminalZ=0 are uniform on compactq bands.

AtZ=0 this is the pure3 root P_w with

    w=H/(109-3H), L=100w, X=3w, W=0.

Apply the negative selectorB once to this actual current state. Its predecessor
is an interior triple withf=0, becauseW=0 and its upper endpoint hasf>0.
Its successor coordinates arex=100w,E2=3w, hence its wash surplus is EXACTLY
zero. It belongs to the same invariantH surface and therefore is precisely
theZ=Z_wash endpoint of(5)--(7). In short,

    B(P_w)=the wash endpoint.                      (8)

This identity is the needed phase gluing. Takingn predecessors of the wash
endpoint andn+1 predecessors of the pure3 endpoint gives identical entrance
states and identical core words after deleting the final pure3 root.

## 4. A connected phase arc must hit exact entranceX=0

For each integern>=0 take the terminal phase arc above and prependn roots
usingB. Glue its wash endpoint to the pure3 endpoint of the(n+1)st arc by(8).
This produces a connected, piecewise smooth one-dimensional phase chain;
the relevant entrance values are continuous at every identification.

Initially the entranceX is positive. At the integer endpoints the states
areB^n(P_w), and Section2 proves that theirX values cross zero after finitely
many steps. Every predecessor is physical while its successorX is nonnegative.
A small formal extension pastX=0 is available: at an entrance-zero root,
u is bounded below by(3), so its successorX is strictly positive; the root
is an interior triple, since a pair23 root withu=X_successor/4 would have
positive currentX. ItsY,Z,w are therefore strictly positive. The preceding
internal roots remain legal by the same selector, including exact quiet1
comparisons at support switches.

For clarity, this yields a compact phase subarc with strictly opposite signs
at its two endpoints and legal internal states throughout. In the finite
chain ending at the first STRICTLY NEGATIVE integer endpoint, take the connected
component where every INTERNAL suppliedX is positive. If the first
nonpositive integer endpoint is exactlyzero, take one more predecessor: it
is legal fromX=0 and(3) makes its output strictly negative. If that component
ends before the integer endpoint, all internal limitingX values are
nonnegative. A zero at any internal state other than the last supplied state
would force its next predecessor to be strictly negative by(3), contradicting
nonnegativity of the next internal limit. Thus only the last supplied state
can first reachzero; its entrance output is already strictly negative. The
component therefore contains both positive and negative entrance values.
Near an entrance-zero point every internalX has a positive margin. Choose
a sufficiently small epsilon>0 and take the portion from the last entrance
value+epsilon before the first value-epsilon. On this compact subarc
|X_entrance|<=epsilon, all internal suppliedX values are positive, and all
roots are physical. It uses only finitely many adjacent phase pieces.

No derivative or monotonicity ofX with respect to terminal phase is required.
The argument is topological and survives an exact support switch or an exact
integer endpoint zero. On a small neighborhood of the selectedq andH=.75,
the strict internal margins and endpoint signs persist.

## 5. The actual finite-alpha selector and exact finite-alpha gluing

Fix the compact subarc just obtained and a small compactq neighborhood.
Foralpha>0 use the exact backward equations

    Dz=1+alpha(1+L-99u), Dy=beta+alpha(2+X-u),
    Z=(L-97u)/Dz, Y=(X-4u)/Dy,
    f=[2Y-101Z+106alphaYZ]/[(1-alphaY)(1-alphaZ)].   (9)

Foralphasmall, Dy<0 uniformly andf is strictly increasing on the same
physical interval[X/4,L/97], by continuity from its positivealpha0 derivative.
Its upper endpoint hasZ=0,Y>0 andf>0. Keep the same selector: ifW<=f(X/4),
use pair23 withu=X/4,Y=0,Z=-W/(101-alphaW); otherwise takef(u)=W.
The exact quiet1 comparison is

    -{Dz Z-(L-97u)}/(1+u)<=0

on pair23. At a switch both root formulas agree. The actual current equations
are

    L'=[L+3u-alpha Z(1+L+12u)]/(1+u),
    X'=[X-u-alpha Y(2+X)]/(1+u),
    W'=-100Z+101alphaYZ,                            (10)

withY=0 on pair23. Every finite iterate depends continuously on the data,
including across the support switches, and converges uniformly to itsalpha0
counterpart. Its hazards remain proper and nonnegative. W'<=0 foralphasmall;
the lowerW bound and all required input-cone margins persist on the finitely
many relevant roots. At the entrance root all three hazards are strictly
positive. These are finite-dimensional statements with no long-orbit limit.

The phase endpoints can be made EXACT at finitealpha. Keep the pure3 state
P_w, independent ofalpha. Let(u_1,Z_1) be the rootB_alpha(P_w), which is an
interior triple withf=0 and henceY_1=101Z_1/(2+106alphaZ_1). For phase
s in[0,1] set

    u(s)=(1-s)u_pure+s u_1, Z(s)=s Z_1,
    Y(s)=101Z(s)/(2+106alpha Z(s)).                 (11)

The resulting terminal roots have successorW=0. They converge inC1 to the
alpha0 arc. The wash surplus is zero at s=1 EXACTLY, positive at s=0,
and has a uniformly negative derivative atalpha0; therefore it is nonnegative
on the entire actual arc for sufficiently smallalpha. All other terminal
hazard guards persist, with the permittedY=Z=0 at s=0.

At s=1,n predecessors giveB_alpha^n(B_alpha(P_w)); at s=0,n+1 predecessors
giveB_alpha^(n+1)(P_w). Thus their entrance states match EXACTLY for the
original rawalpha,beta. Deleting the final pure3 root identifies the words.
This construction supplies the same compact connected phase subarc for every
sufficiently smallalpha and nearbyq,H, with strict opposite entranceX signs.
No unsupported interpolation between physical predecessor roots is used:
only the final terminal root is parameterized by(11), and every predecessor
is produced by the exact selector(9)--(10).

## 6. Outer equations by a continuous degree argument

Choose the entrance row0 valueT near5/4. For every actual finite core,
choose its terminalE0 by its exact affine row0 identity so that the entrance
row0 is exactlyT. The survival coefficientS_core is positive and bounded
away fromzero on the finite family. Let its entrance be(T,-L,X,alphaW),
its exitE=(E0,-x,E2,0), and define the usual outer quantities

    b=T/(1+T), B1=(T-L)/(1+T), B3=(T+alphaW)/(1+T),
    a=B3/(1+B3), A1=2a+(1-a)B1, A2=2a.

Define the actual uncorrected outer residuals

    R1=A1(3-E0)-3(E0-x),
    R2=A2(3-E0)-3E2-E0.

The entrance conditionX=0 together withR1=R2=0 gives exactly the common
negative-core return calendar. To select them simultaneously, put

    H_ent=(L+3X)/(1+X),
    G1=S_core R1+7T(3-H_ent)X/(1+2T),
    G2=S_core R2+3X.                               (12)

Atalpha0, passive row identities give

    S_core R1=T(6-9T+7L)/(1+2T),
    S_core R2=T(5-4T)/(1+2T)-3X.

The invariantH_ent=H andL=H-(3-H)X therefore give

    G1=T(6-9T+7H)/(1+2T),
    G2=T(5-4T)/(1+2T).                             (13)

These are independent of phase and core length. Their unique nearby root
isT=5/4,H=3/4. In variables(H,T) the Jacobian is

    [[5/2,-45/14],[0,-10/7]],

with determinant-25/7. Every finite-alphaG converges uniformly to(13) on
the chosen compact parameter box and phase subarc. Differentiability across
support switches is unnecessary.

The G residuals glue EXACTLY at every finite-alpha terminal deletion.
Indeed removing a last pure3 root of hazardw replaces its successor values
by

    E0'=3w+(1-w)E0, x'=3w+(1-w)x,
    E2'=-w+(1-w)E2.

ThusR_i'=(1-w)R_i, whileS_core'=S_core/(1-w). EntranceT,L,X,W andH_ent
are unchanged. Both expressions in(12), andX itself, are therefore identical
on the two sides of the phase identification.

Choose a small disk in(H,T) around(.75,1.25). The limitingG has a simple
zero and does not vanish on its boundary. Choose the phase subarc endpoints
with uniform strict oppositeX signs over this disk and nearbyq. A standard
product-degree argument gives a simultaneous zero of(G1,G2,X) for every
sufficiently smallalpha. Explicitly, homotopeG to(13) while keeping the
phase-sideX signs and avoidingG=0 on the disk boundary; then homotopeX
to a linear function of the phase coordinate. The boundary remains zero-free,
and the resulting product degree is nonzero. At the resulting zeroX=0,
(12) givesR1=R2=0 exactly.

All other guards are strict or built into the exact selector. Atalpha0,
T-L is near1/2, x<1, and

    S_core(E0-x)=T-L>0,
    (E0-x)/(3-x)=(T-L)/(3-L) in(0,1).

Row0 values are positive solo3 mixtures, and remain positive on the finite
actual family. B1,B3,a,b have positive strict margins. The terminal wash
surplus is nonnegative by(11), including its exact endpoint equality.
Each fixedq consequently has a neighborhood with one uniformK threshold.
A finite cover proves the asserted uniform threshold on every compactq band.

## 7. Full behavioral and fixed-target consumer

Fix one raw game and one finite core selected by the preceding degree argument.
Its entrance is C=(T,-L,0,alphaW), its exit is E=(E0,-x,E2,0), and its actual
outer residuals vanish. These data are chosen ONCE, before accuracy. Set

    b=T/(1+T), B1=b-(1-b)L, B3=b+(1-b)alphaW,
    a=B3/(1+B3), A1=2a+(1-a)B1, A2=2a,
    R=1-x/3, V0=(E0-x)/R, V2=(E2+x/3)/R, h=V0/3.

The proved guards giveT>0,B1>0,B3>0,0<x<3,E0>x,E2>=3x/100 and0<h<1.
The two exact returns are equivalent to

    A1(1-h)=3h, A2(1-h)=V2+h.

The finite periodic calendar is

    A=(0,A1,A2,0) --solo0--> B=(0,B1,0,B3)
      --solo2--> C --selected finite core--> E
      --solo3 wash--> V=(V0,0,V2,0) --solo3--> A.

Every prescribed and Continue payoff identity is exact. At a root with
independent hazardsq, writeQ_i for Quit now, P_i for the passive contribution
from nonempty opponent coalitions, andH_i=product_(j!=i)(1-q_j). Continue
has valueP_i+H_i v_i when the successor annotation isv_i. Every core player
who quits with positive probability is indifferent; the only extra quiet
comparison, player1 at pair23 roots, was proved explicitly. Player0's joining
offers are nonpositive by the seven raw caps and lie below its positive
core annotation.

Here are all remaining local comparisons. Along solo0 at cumulative quitting
probabilityu in[0,a], the native annotation is

    (0,(A1-2u)/(1-u),(2a-2u)/(1-u),u/(1-u)).

All observer coordinates are nonnegative. For anydelta>0 subdividea into
finitely many conditional hazards at mostdelta. Fori=1,2,3 put
J_i=Z_i({0,i}). Its joining offer at one such root is at mostdelta(J_i)_+;
there is no assumption on these arbitrary raw rewards. Owner0 is indifferent.
At the solo2 rootb, owner2 is indifferent. Player0's joining offer is
nonpositive; players1 and3 have offers-Kb and-100b, belowB1 andB3.

The solo3 wash is finite. From(s,-v,z,0), with0<v<3,s>=v,z>=3v/100, choose
q=v/100. Its successor is

    ((s-3q)/(1-q),(-v+3q)/(1-q),(z+q)/(1-q),0).

Player1's joining offer is-100q=-v, player2's is3q<=z, and player0's is
nonpositive. All guards persist. Withr=97/100, after n regular roots,

    S_n=1-x/3+(x/3)r^n,
    v_n=xr^n/S_n, z_n=(E2+1-S_n)/S_n.

Take43 regular roots, then a final hazardv_43/3. The exact inequality
(97/100)^43<109/400<=(3E2+x)/(4x) givesz_43>=v_43, making that last root
legal and setting row1 tozero. Its total survival is1-x/3 and its endpoint
is exactlyV above. This works also at the exact wash equality.

The final solo3 aggregateh closes the return. At cumulative quitting
probabilityu in[0,h] its annotations are

    ((V0-3u)/(1-u),3u/(1-u),(V2+u)/(1-u),0).

They are nonnegative. Split the aggregate into conditional hazards at most
min(1/2,V2/6); then row2's joining offer3q lies below its current coordinate,
and the other quiet joining offers are nonpositive. Owner3 is indifferent.
All blocks are finite and depend only on the requested meshdelta and the
fixed selected core.

We now price unrestricted behavioral deviations. Before absorption there is
only one surviving public history. Any private behavioral replacement is a
law on finite first-quitting dates and Never. Its full cap therefore obeys

    B_i^*=max(Q_i,P_i+H_i B_i^*(next)).

Letu_i denote the reference annotation. All its Continue identities and
prescribed identities are exact; every immediate Quit surplus is at most
e=delta max(0,J1,J2,J3). A fixed opponents-only absorption chance per period
is at leastrho=min(a,b)>0: deviator0 faces the solo2 root, while every other
deviator faces the complete solo0 aggregate. Unrolling the cap recursion
over one period therefore bounds its maximal excess by
max(e,(1-rho)excess), and hence by e. This prices every finite stopping date
and Never; the latter limit is justified by the same geometric absorption.
Prescribed terminal payoff equals its annotation because prescribed period
survival also decays geometrically. Thus the terminal strategy is e-Nash
against every behavioral replacement and has the exact targetA.

For a period of lengthm, the expected absorption time under any unilateral
replacement is at mostm/rho+1, uniformly over that replacement. IfM bounds
the absolute ORIGINAL rewards, terminal payoff and average payoff over the
firstN dates differ by at most2M(m/rho+2)/N. Proper opponents imply that the
native translation adds exactlykappa_i to every prescribed or deviating
terminal payoff. Choose the meshdelta for the requested accuracy and then
chooseN large enough for this uniform horizon error. The resulting profile
works for every larger horizon and has the one fixed targetkappa+A. No core,
outer root, or payoff target is selected anew as accuracy changes.

An optional exact boundary identity relates this producer to a pair-prefix
calendar. At entranceX=0, decreasealpha below1/100 and append pureplayer2 predecessors
withq1=w=0,Z=L/[1+alpha(1+L)]. Their row3 guard followsW>=-100L and
f0=-101L/(1+alpha)<-100L. Their limiting native entrance is

    ((T-L)/(1+L),0,0,(alphaW+L)/(1+L)).

Its outerB1=(T-L)/(1+T) andB3=(T+alphaW)/(1+T) are exactly those above,
including at finitealpha. Thus the target and return equations are unchanged.
The proof uses the direct finite core, so this optional identity introduces
no infinite chronological prefix or additional accuracy dependence.

## 8. Exact stationary and sure-root separator

### 8.1. Exact exclusion statement

Players are 0,1,2,3. Original nonempty absorbing rewards are r_i(D)=1+Z_i(D),
live and AllNever rewards are zero. In coalition-mask order 0,...,15, use

```
Z0: 0  0  3   0  -1   0  -12 -13   3 -3    2  -7   -6  -7  -8   -5
Z1: 0  2  0  -1   1   5   -K   6  -3  3 -100   8    9  -8  11   -9
Z2: 0  2 -2 -10   0 -10    p  -9  -1 -5   -1  10    3  -3   2    8
Z3: 0 -1 -2 -12   1   7   -6  11   0  1    0 -10 -100 15/2  1 21/2
```

Mask zero is only a polynomial placeholder. For EVERY K>=100 and
-K/10<=p<=0:

1. There is no exact stationary terminal Nash equilibrium against full
   behavioral replacements.
2. There is no exact terminal Nash equilibrium whose first live round has
   a sure quitter, even with arbitrary behavioral continuation after all
   Continue.

The exact ray p=-K/10 therefore gives an unbounded separator. The compact
negative-ratio theorem covers its sufficiently large-K tail. This ray lies
outside the old central negative condition K>=C0(1+|p|/6) for every C0>=100,
and outside the old negative outer cone p<=-max(200,2K). Its singleton matrix
rigidly fixes the labels and positive row scales by the census in Section9, so varying K cannot become the fixed K=100 family by those operations.
The full exclusions above handle complete stationary and sure-root selections,
not just one proposed witness.

### 8.2. Necessary polynomial systems

For independent hazards x=(x0,x1,x2,x3), define

    H_i=product_(j!=i)(1-x_j),
    P_i=sum_(nonempty S subset opponents) Pr_x(S) Z_i(S),
    Q_i=sum_(S subset opponents) Pr_x(S) Z_i(S union{i}),
    F_i=(1-H_i)Q_i-P_i.

Stationary terminal Nash requires F_i<=0 at x_i=0, F_i>=0 at x_i=1,
and F_i=0 at 0<x_i<1. These conditions remain necessary when a player's
opponents never quit, though then they can be weaker. AllNever itself is
excluded because a singleton quit pays 1 rather than 0.

For a sure-root profile use

    L=(-12,-8,-10,-12), G_i=Q_i-P_i-H_i L_i.

L_i is the minimum of -1 and native nonparticipant rewards. A continuation
best response is at least 1+L_i by Never. If there is a unique sure quitter,
replacing its continuation cap by this lower bound increases its Quit-minus-
Continue comparison and preserves its necessary nonnegative sign. All other
players have H_i=0. With several sure quitters every H_i=0. Hence the same
three signs for G are necessary for every sure-root pattern, with unrestricted
continuations and behavioral deviations.

Write p=-qK with 0<=q<=1/10, Delta=K-100>=0, and let superscript b mean
K=100,p=-100q. Then

    F1=F1b-Delta(1-H1)(1-x0)x2(1-x3),
    F2=F2b-q Delta(1-H2)(1-x0)x1(1-x3),
    G1=G1b-Delta(1-x0)x2(1-x3),
    G2=G2b-q Delta(1-x0)x1(1-x3).

For each decreasing coordinate, when its coefficient is not identically zero
on the support pattern, retain the baseline nonnegative condition for an
active or sure owner and drop the quiet condition. If the coefficient is
identically zero retain its original sign. Treating the row-2 coefficient as
possibly nonzero at q=0 only weakens the system and is safe.

The correlated combinations cancel Delta EXACTLY:

    CF=-q(1-H2)x1 F1b+(1-H1)x2 F2b
      =-q(1-H2)x1 F1 +(1-H1)x2 F2,
    CG=-q x1 G1b+x2 G2b=-q x1 G1+x2 G2.

The row-1 multiplier is nonpositive and the row-2 multiplier nonnegative.
Use a sign for the sum only when all nonzero terms, with those signs included,
have compatible original sign requirements; otherwise omit it. Terms whose
multipliers vanish identically on the pattern contribute nothing. Equality
is retained when all contributing original conditions are equalities.

Set s=10q in [0,1]. All baseline and correlated polynomials are affine in s.
Their exact endpoint interpolation supplies one extra Bernstein coordinate,
so the finite calculation checks the whole wedge simultaneously.

### 8.3. Analytic shortcuts

A pattern records quiet=0, sure=1, strictly mixed=2. There are 80 nonzero
stationary patterns and 65 containing a sure quitter. Free mixed coordinates
are checked on their closed unit cube, a safe enlargement.

On support contained in12 with both owners nonquiet,

    F1=-x2-K x2^2<0,

contradicting player1's mixed or sure condition. If x0=x2=0, x1>0 and
player3 is mixed, then F3=2x1>0, also impossible. These shortcuts refer to
strict support patterns and therefore can exclude cases whose enlarged
closed cube contains lower-support boundary points.

A single mixed owner j with no sure owner is excluded by an outsider i with
Gamma_ij<0 and Z_i({i,j})>=0, since its quiet comparison is
F_i=x_j(x_j Z_i({i,j})-Gamma_ij)>0. Such an outsider exists for every j
uniformly on this wedge; for j=2 choose i=0.

### 8.4. The linked-parameter origin repair for support123

This is the necessary additional argument when both row1 and row2 decrease
with K. Independent baseline relaxations alone do not yield an origin bound
on this support, and they leave a spurious boundary x1=x2=0,x3>0.

Put y=x1,z=x2,w=x3 and x0=0, and write

    A=z+w-zw, B=y+w-yw,
    F1b=A[-100z(1-w)-100w+111zw]-(z-3w+11zw),
    F2b=B[-100q y(1-w)+3w-yw]+2y+w-2yw,
    F3=(y+z-yz)(-100z+101yz)+2y-z+5yz.

Define the exact polynomial

    R=1+95y-101y^2+100z-201yz+101y^2 z,

so F3=2y-zR. Define

    D=-q R B F1b+2A F2b,
    P=D+(y-z)F3.

On the strictly mixed support123, CF=0 and F3=0 imply P=0. In fact

    yD=R CF+A F2b F3.

This is an exact polynomial identity. Since y>0, the new equality is a
necessary consequence. No division is made at a potentially zero mixed
coordinate in the checker; it simply appends the necessary polynomial P.
As a continuous polynomial condition, it remains valid on closures of actual
feasible sequences. It removes the irrelevant boundary noted above, because
there P(0,0,w)=w^2[(2-3q)+(100q+6)w]>0 for w>0.

P has no terms of degree below two in (y,z,w). Its exact quadratic part is

    2y^2+z^2+(1+q)yz+(4-3q)yw+(2+q)zw+(2-3q)w^2.

For 0<=q<=1/10 every mixed coefficient is nonnegative and every diagonal
coefficient is at least one. Thus this quadratic part is at least
max(y,z,w)^2. After q=s/10, the sum of absolute coefficients of all terms
of (y,z,w)-degree at least three, viewed as a polynomial in (y,z,w,s), is

    C=1122506/5.

For 0<=y,z,w,s<=1 those terms have absolute total at most C M^3,
M=max(y,z,w). Hence P=0 at a nonzero feasible point implies M>=1/C.
In particular the entire nonzero origin cube of side 2^-18=1/262144 is
excluded because 2^-18<5/1122506. The checker recomputes the polynomial,
quadratic coefficient inequalities, exact high-degree coefficient sum,
and the least strictly admissible dyadic exponent.

The polynomial identity and coefficient bound are finite exact expansions.
The reproducing checker uses only rational arithmetic and the standard library.

### 8.5. Other origin bounds and exact finite calculation

For every other no-sure pattern with at least two mixed coordinates S, write
its active baseline equations F_S^b=-Gamma_SS x+R_S. The checker verifies
that every monomial of R_S has mixed-coordinate degree at least two, including
all parameter-dependent terms. Every relevant principal is invertible.
Choose the lexicographically first ell in {1,...,8}^|S| for which
ell^T Gamma_SS^-1 has nonnegative coefficients on each relaxed active row.
Then at a feasible point

    min(ell)||x||inf <= ell.x
       <= sum_j |(ell^T Gamma_SS^-1)_j| C_j ||x||inf^2,

where C_j is the absolute coefficient sum of R_j in (x,s). This supplies a
uniform positive lower bound on ||x||inf. The checker uses its least strict
dyadic origin cube. The special support123 instead uses P above.

Original polynomials are retained in player order, followed by CF or CG,
then P when applicable, then valid inverse-row combinations of the active
baseline polynomials. An inverse-row combination is added only when its
necessary sign follows from the retained row signs. The high-degree P needs
no additional inverse combination.

For each pattern use maximum coordinate degrees across these polynomials,
with minimum degree one, and compute exact tensor Bernstein coefficients

    b_k=sum_(m<=k) a_m product_i binom(k_i,m_i)/binom(d_i,m_i).

Clear their common positive least denominator. Reject a closed box only when
an asserted equality or inequality has uniformly strict coefficients of a
forbidden sign, or when the box lies inside the proved origin cube.
Otherwise bisect the mixed coordinate with minimum current subdivision depth,
breaking ties by ascending player index. If there is no mixed coordinate,
bisect s. For degree d the integer-scaled child coefficients are

    left_r=2^(d-r) sum_(j=0)^r binom(r,j)b_j,
    right_r=2^r sum_(j=0)^(d-r) binom(d-r,j)b_(r+j).

The positive common scale is harmless, and the children cover the parent.
Enumerate support patterns and tensor indices lexicographically; use depth
first left-child-first traversal, test strict signs before the origin rule,
and abort without a claim at 100000 visited nodes or subdivision depth 35.
Every analytic shortcut counts as one node. The s coordinate is retained on
its full interval unless it is the only coordinate.

The deterministic exact calculation finishes with

    80 stationary patterns excluded, 1230 nodes;
    65 sure-root patterns excluded, 369 nodes.

No unresolved box, numerical rootfinder, floating-point sign test, or stored
subdivision payload is used.


## 9. Comparison with the existing producers

Use the exact completion in Section8 and the rayp=-K/10, withK tending to
infinity. The new theorem supplies every sufficiently large member, while
Section8 excludes every exact stationary terminal Nash and every exact
terminal Nash with a sure first-round quitter, including arbitrary subsequent
behavioral continuations. Thus every producer of either of those strategy
classes is excluded, independent of its witness, active support, relabeling,
or positive recipient scaling. These exclusions do not claim a gap against
all approximate stationary profiles at a singular limit.

There is one essential qualification. The raw singleton geometry DOES satisfy
the explicit singleton-chamber criterion: its computed values are
C=5/4,b=5/9,a=5/14,L0=2/7,A10=15/14,J=3/4, and its last singleton guard is2/9.
A=100,c=3,u=0,v=-100,q0=0 satisfy the other fixed-data requirements. That
result provesK>=M(1+|p|) with an unspecified finiteM; its statement supplies
an unspecified central cone and does not certify the fixed ratio1/10.
No lower boundM>=100 or necessary failure of an unverified short-core extension
is asserted. The new theorem has the stronger quantified scope of EVERY
compact strictly negative ratio band. Its role is to complete those bands,
not to give another unspecified central cone.

The normalized central-negative theorem separately statesC>=100 and
K>=C(1+|p|/6). On this ray its right side is at least100+(5/3)K, so that
explicit inequality is impossible. The negative outer cone needs|p|>=2K;
the nonnegative-premium regions needp>=0. Both fail. The canonical singleton
matrix has only the identity positive-row-scaled self-relabeling: its unique
row with two equal positive entries fixes0, its negative entry fixes2, and
the signs distinguish1 from3; nonzero entries then force all row scales1.
Thus this growing ray cannot become the fixedK=100 scalar or bridge family.

Here are the complete finite-data checks for the other accepted raw selectors.
The singleton matrix and its inverse are

```
Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0], det Gamma=25,
Gamma^-1=[8/25,1/5,9/25,3/25;
           3/25,1/5,-6/25,-2/25;
           14/25,3/5,-3/25,24/25;
           2/5,0,1/5,2/5].
```

The positive directed graph is strongly connected. Its only mutually positive
pair is01 and its only mutually negative pair is13; these intersect.
The participant vector on123 is(11,2,1), whereas the entire vector on12 is
(-12,-K,-K/10,-6), strictly negative. The directed joining-gap matrix is

    c_ij=Z_i(ij)-Gamma_ij,
    c=[0,-3,1,-6;-3,0,-K-1,-97;-12,2-K/10,0,4;2,2,-101,0].

These give the following full selections, not just one unsuccessful witness.

- Strong connectivity forces the marked set of an ordered nonpositive-anchor
  selection to be all players. Its first block meeting123 has a positive
  participant-weighted sum. Calendar-polytopes fail the same participant
  condition. The vector(11,2,1) also excludes every nonzero nonnegative
  upper-average weight. The upper-face chargeZ3(123)-Z3(12)=7>0 defeats the
  boxed-charge alternative, hence the mixed-support upper/charge and
  mixed-premium-trap criteria.
- Every nonzero nonnegative ledger givesH(12)<0. This excludes the
  full-proper-coalition hypotheses in marked-orientation, same-sign-pair,
  and sink/receiver cap-chamber ledgers. For support-filtered ledgers,
  singleton constraints prohibit a nonzero ledger supported in{1,2}, since
  column3 would require-3a1-a2>=0. Thus12 is necessarily safe, and its
  required nonnegativeH remains impossible, even for families of ledgers.
- The three pair partitions fail their weak mate prerequisites at
  c01=-3 for01|23,c20=-12 for02|13,c03=-6 for03|12. No proof weights repair
  these signs. Every unordered pair has a negative joining gap, excluding
  triples requiring six positive joining gaps and contact-preserving bonus
  pairs requiring both gaps positive.
- Matching/favorite and polynomial-row-weight templates need two disjoint
  mutually positive pairs. Negative-pair-funded, mixed-premium positive-passive,
  and three-weak-quitter templates need a vertex with two mutually negative
  neighbors. Neither exists. Signed four-cycle and negative-chord Hamiltonian
  templates need every same-sign reciprocal pair to be an opposite chord;
  the intersecting pairs01 and13 make that impossible. The no-mutually-negative-
  pair theorem fails at13.
- The only nonnegative-inverse principal triple is023, whose outside inverse
  row is(-3,6,2)/5. Thus complete passive-child selection fails. The attached
  negative-pair sign census permits only roles(3,1,0,2), where the required
  nonnegative participant premium isZ1(13)=-100. The both-premiums-arbitrary
  alternative instead needsm=Gamma21=-2 nonnegative.
- The new negative-pair outer dichotomy has no admissible sign labeling.
  For its free parameter s<=0 there would be no mutually positive pair.
  For s>0 its positive pair12 and negative pair13 force roles(2,1,0,3),
  where its required positiveGamma01 is ourGamma21=-2. This exhausts all24
  permutations and uses no unknown threshold.
- The scalar singular-circuit guards force its two negative-contact roles
  to be actual pair13; the required positive participant reward is then
  either-100 or0. Two-contracting-blocks' general chamber needs a recipient
  with two positive participant pair premiums, whereas every actual recipient
  has at mostone. Its arbitrary-positive-pair branch needs two nonnegative
  participant premiums, whereas every actual pair has a negative participant.
  The flexible crossing-transport branch also needs positive crossing-pair
  participant premiums and fails for the same reason.
- In the three-passive-poles template only roles(0,1,3,2),(0,3,1,2) pass
  A0>0,B0<0 forK>20. Both haveA0=1,B0=-1; theirB2 values are1/2 and1,
  contradictingB2<0. Repeated-solo-exit, two-outsider-buffer, and global
  two-joint cyclic-child templates need a strictly negative outsider
  singleton column; none of the four columns has that sign.
- Same-singleton diffuse-flow, unequal-premium, nine-core, unordered-nine-core,
  and additive fixed-core families impose the incompatible passive entry
  Z0(12)=2, versus-12 here. The singleton self-relabeling census prevents
  removing the mismatch. FixedK=100 and fixed(K,p)=(100,0) branches cannot
  cover the growing ray.

For completeness the full strict active-support column census is

| Support | Recipient/sign | Positive inverse vector | Outside image |
|---|---|---|---|
|023|2,+|(3,3,1)/5|6/5|
|023|3,+|(1,6,2)/5|2/5|
|123|2,-|(3,6,2)/8|9/8|
|0123|0,+|(8,3,14,10)/25|none|

There are no other eligible columns or pairs. In literal canonical row units,
the weighted collision-dominance atlas has favorable scaleG<=5 on023,
G=K/10 on123, andG=12 on the full support, while its adverse scaleB>=K
in every case. Its retainedc<=1 therefore cannot satisfyB<=cG forK>=100.
This checks every eligible recipient subset. Arbitrary row rescaling also
changes the atlas constants; its transformed stationary outputs are instead
excluded directly by the complete certificate in Section8. The all-column
signed-inverse criterion fails the mixed-sign column2. A bounded-remainder
single-column theorem cannot absorb the other linearly growing adverse pole.

A conditional source reduction or consumer without a supplied strategic source
is not treated as an existence theorem. No failure of stationary repetition
alone is used to exclude a general punishment tail: Section8 prices the exact
stationary and sure-root classes it states, and the remaining entries above
are failures of their explicit raw prerequisites.

## 10. Semantic source and remaining scope

The named semantic sources inspected are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Section7 supplies the complete behavioral and fixed-target proof directly.
No Lean checking or formalization is claimed.

The Lean handoff is a raw-family predicate containing exactly Section1
and a finite-core record carrying physical hazards, native annotations,
all local comparisons, the zero row2 entrance, and the two outer returns.
Sections2--6 construct that record from the raw data; it is not an assumed
strategic witness. The theorem shape is: for every compact positiveq band
there existsC such that every admitted game withK>=C has one targetW, and
for everyepsilon>0 there exist one behavioral profile and a horizon threshold
whose payoffs stay within epsilon ofW and whose unilateral gains are at most
epsilon at every larger horizon. Section7 is the full-agency consumer for
that constructed record. The formalization targets are the monotone selector,
finite connected-phase hitting, exact deletion identities, and product degree.

The new mathematical mechanism is the monotone negative support selector,
finite hitting, a connected physical terminal-phase chain, exact finite-alpha
endpoint deletion, and the corrected product-degree outer solve. The theorem
closes every compact strictly negative ratio band of the stated raw family.
It does not settle arbitrary Fin4 or the remaining bounded-K region of this
family, and it does not claim maximal coverage of the older central mechanisms.
