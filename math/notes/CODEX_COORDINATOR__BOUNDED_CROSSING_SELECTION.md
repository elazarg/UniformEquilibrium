# Closed actual geometry and bounded recovery of positive crossings

Owner: CODEX_COORDINATOR. Ordinary mathematics, not Lean checked.
This is the canonical internal record for actual continuation geometry and
bounded Nash-word recovery. The
[selected mixed-core theorem](../exports/PASSIVE_BOUND_TRIPLE_SELECTION_UNIFORM_EQUILIBRIUM.md)
contains the closed-passive selected-root consumer. The arguments below retain
its useful extensions without duplicating that proof or claiming another
independent reward-class exclusion for the recovery example.

For the numerical core, write a=-K. The selected theorem covers all real a
when p=0, and a<=0 or a>=1/2 when p>=0. The opposed-pair strip 0<a<1/2,p>0 permits pair12 with positive ambient
index. Sections6–9 show that exact actual realizability and full zero debt do
not supply universal Nash-prefix return. The binding example is now
classified over ALL finite exact calendars: its nonsolo component has a
positive minimum Never product and an exact barrier through AllNever.
Section10 nevertheless approximates every compact minimizing source on a
finite calendar while preserving its payoff, Never response and original
Never masses EXACTLY. Only full caps incur error. The exact-profile
classification does not apply to these positive-debt approximants;
global extremality remains a separate constraint. Exact cap compression
is unavailable.

## 1. Closed actual domains replace arbitrary virtual boxes

Players are I={0,1,2,3}. Native own and live/Never rewards are zero. Define
Gamma_ij=Z_i({j}) for ALL i,j in I; its diagonal is zero. Each owner
independently chooses its first Quit time among natural dates and Never;
one deviator can replace the complete law. Retain prescribed terminal payoff U, full response cap B, pure
Never response payoff e, and ORIGINAL marginal Never masses N. For a root q,
let h=product(1-q_i), H_i=product_(j!=i)(1-q_j), Q_i its forced-Quit offer,
P_i its nonempty-opponent passive payoff, and E_i=q_i Q_i+(1-q_i)P_i. Then

    U'=E+hU, B'_i=max(Q_i,P_i+H_iB_i),
    e'_i=P_i+H_ie_i, N'_i=(1-q_i)N_i.                    (1)

Every actual profile satisfies B>=e and d_i=B_i-U_i>=N_i(B_i-e_i).
Virtual seeds(U,B,e,N)=(z,z,z,1) satisfy the same inequalities, preserved by
EVERY prefix. The exact nonnegative residual decomposition is

 d'_i-N'_i(B'_i-e'_i)=q_i(B'_i-Q_i)
 +(1-q_i)(1-N_i)(B'_i-P_i-H_iB_i)
 +(1-q_i)H_i[d_i-N_i(B_i-e_i)].                         (2)

Thus zero debt at positive survival forces U=B=e. This assertion does not
bound arbitrary positive-debt intermediate U by passive rewards.

Let K be a compact set of(U,e) pairs containing all actual annotations and
preserved by every prefix map(1). Call a Nash root good if it has a sure
quitter or a nonpositive output coordinate. If every v with(v,v) in K and
min v<=0 has a good root, then the absorbing native debt infimum A_Z is0.
For nonnegative original own offsets this gives a fixed UE payoff through
the complete terminal consumer in the linked theorem.

Here is the exact closed-domain change to that proof. At a local stall
v>=0 with zero set S, a signed separator w Gamma_SS>>0 needs a nearby
marked seed with positive separator value. Choose j in S and set

    z=(1-t)v+t Gamma[:,j], t>0 small.                   (3)

Then z_j=0, w z_S=t w Gamma_SS[:,j]>0, and positive outsiders stay positive.
A solo-j prefix sends the pair(v,v) EXACTLY to(z,z), so the seed lies in K
without any interior or neighborhood assumption. Initialize its cap virtually
as B=z; this is not claimed to be the actual cap of the solo prefix.
Every budgeted zero-debt minimum has U=e by(2) and hence remains on K's
diagonal. Compact closure preserves K. Smaller zero sets use the same seed
construction. The remainder of the selected good-root induction, including
length-independent cap nonexpansiveness and the ORIGINAL Never-product
minimum, is unchanged. Strictly negative seeds are unnecessary; z_j=0 suffices.

One choice is a full-reward payoff box times the CLOSED passive box
[L_i,R_i], where L_i,R_i are the minimum/maximum of0 and all Z_i(A) with
i notin A. Another is the convex hull of deterministic calendar(U,e) vectors,
a correlated outer relaxation. The next section supplies the exact independent
annotation domain instead of that relaxation.

## 2. Exact independent annotations have a 32-date representation

For Fin4 let K_ind be the image of all actual independent profiles under(U,e),
WITHOUT B. Every such vector is realized on at most32 finite dates plus Never.

Fix opponents' laws and vary owner i's law. The eight coordinates(U,e) are
affine in it, but e_i is constant because forcing i Never removes its law.
Only seven coordinates vary. Their conditional vectors at each finite deadline
or Never are bounded. A countable average belongs to their convex hull, not
merely its closure: if the average is on a supporting face of the closed
convex hull, every positive-weight vector lies on that face, reducing affine
dimension; otherwise the relative interiors of the convex hull and its closure
coincide. Induction on dimension proves the assertion. Caratheodory therefore
replaces owner i's law by at most8 old support points, preserving ALL(U,e).

Apply this successively to all four owners. Every replacement preserves the
same eight annotations, including those depending on earlier owners. The
union of the four supports contains at most32 finite dates. Relabel them in
increasing order into{1,...,32}, retaining ties and Never. All prescribed and
counterfactual first-coalition outcomes, hence(U,e), stay unchanged.

Conversely every product law on{1,...,32,Never} is actual. Its probability
space is a product of four33-point simplexes, and its(U,e) map is polynomial.
Its compact image therefore equals K_ind. Prefixing gives another actual
profile, compressible again, so K_ind satisfies Section1 exactly; caps are not preserved.
For an exact warning, set all native rewards0 except Z1(01)=1. AllNever has
U=e=B=0. Having0 quit surely at date1 while all others Never also gives U=e=0,
but B1=1 by joining that date. Equal(U,e) does not determine Nash status.

## 3. Finite actual-data crossing tests

A counterexample with nonnegative own levels must admit v with(v,v) in K_ind,
min v<0, and NO good Nash root. Otherwise Section1 proves A_Z=0. This is a
finite real-algebraic existential/universal condition once K_ind is represented
by Section2; it is stronger than assuming one selected bad root exists.

A simpler necessary test asks for ONE proper fully positive crossing at such
an actual diagonal v. Empty and singleton active supports cannot cross, so
there are11 supports S of sizes2,3,4. Set q_j=0 off S,0<q_i<1 on S, and impose

    Q_i=P_i+H_i v_i>0                  for i in S,
    P_j+H_j v_j>=Q_j, P_j+H_j v_j>0    for j outside S,
    v_i=U_i=e_i for every i, min_i v_i<=0.              (4)

Use probabilities p_i,t>=0 summing to1 over{1,...,32,Never}, and define
S_i(t)=sum_(finite s>t or s=Never)p_i,s for FINITE t. Both sums below run
only over t=1,...,32, excluding Never:

 U_i=sum_t sum_(A nonempty) Z_i(A)
                   product_(j in A)p_j,t product_(k notin A)S_k(t),
 e_i=sum_t sum_(A nonempty,i notin A) Z_i(A)
                   product_(j in A)p_j,t product_(k notin A,k!=i)S_k(t).

Expanding the four choices of a nonpositive v_i gives at most44 systems in
at most140 variables, of degree at most4. Infeasibility proves A_Z=0;
feasibility is not a no-UE conclusion. No expanded generated payload is needed.
The cheaper passive-box relaxation eliminates v: active owners require
Q_i>0 and L_iH_i<=Q_i-P_i<=R_iH_i; quiet owners require
P_j+R_jH_j>0 and P_j+R_jH_j>=Q_j. An anchor requires Q_i-P_i<=0 for an active
owner, or P_j>0 and Q_j<=P_j for a quiet owner. Boundary inequalities are weak
where the passive interval is closed. This relaxation has only four hazards.

## 4. A bounded Nash-word consumer

Keep the closed domain K of Section1. Suppose a fixed finite L has this
property: every diagonal v in K with min v<=0 has a NONEMPTY word of1,...,L
Nash prefixes, each Nash at its current continuation, whose final payoff has
a nonpositive coordinate OR whose joint survival is0. Words are written in
prefix order; physical dates have the reverse order. Then A_Z=0.

The word correspondence is the finite DISJOINT UNION of lengths1,...,L.
Each fixed-length Nash graph and its good endpoint condition are closed.
An empty word is excluded; padding by zero roots is not assumed Nash.
At the least original-Never source, every nontrivial good word would lower
the same minimum or give zero absorbing debt. Thus all good words there
are all-zero. Compactness then makes every nearby good word uniformly small,
even if unrelated large bad roots remain. Zero words are Nash only at
nonnegative inputs. Positive outsiders strictly Continue throughout such
small words because L is fixed.

In the local separator fiber, replace one selected root by one selected good
word. Choose the root bound delta and c0 so
(1-4delta)^L(1-c0)>1-eta. Every intermediate root is supported on the same
zero set, preserves zero debt, and preserves the ORIGINAL separator inequality.
A nontrivial small good word returns to the marked fiber with less survival.
At a stall, the weighted inequality gives a proper smaller zero set. Apply
induction there, using the same L and closed-domain seeds(3). Kernel words,
compact endpoint extraction, and nonexpansive seed removal are unchanged.
This is the complete modification to the linked one-root consumer. The
length bound is essential to this compactness argument.

## 5. A raw02-to-023 recovery branch

The following produces an exact second prefix from certain positive outputs.
Assume every player0 participant reward is nonpositive and define

 d0=Z0(02)-Gamma02>0, d2=Z2(02)-Gamma20>0,
 A0=Gamma03-Z0(03)>0,
 D0=Z0(023)-Z0(03)-Z0(23)+Gamma03>A0,
 A=Z2(23)-Gamma23>0, D=A-Z2(023)+Z2(03)>A.

Require Z3(23)<Gamma32. Choose U>0 and put
X=A/D, B=max(U/(U+d0),A0/D0), both in(0,1). Let J(x,b,z) be the product
expectation of c_empty=0 and c_T=Z1(T)-Z1(T union{1}), for nonempty
T subset{0,2,3}, under hazards(q0,q2,q3)=(x,b,z). Require J>=0 at all eight
corners x in{0,X},b in{0,B},z in{0,1}.

Every positive v with v0<=U and v2<A*d2/(D-A) then has a proper nonzero Nash
root with nonpositive player0 output. Start at z=0 with
x=v2/(d2+v2), b=v0/(d0+v0), making owners0,2 indifferent. Quiet1 prefers
Continue by its comparison J+(1-x)(1-b)v1>=0. If quiet3 also Continues,
this is already the desired root. Otherwise continue the active equations via

 z*=v2/(v2+A),
 x(z)=[v2(1-z)-Az]/[(d2+v2)(1-z)-Dz],
 b(z)=[v0(1-z)+A0z]/[(d0+v0)(1-z)+D0z], 0<=z<=z*.

The first denominator stays positive through z*: its endpoint numerator is
A*d2-(D-A)v2>0. The derivative of x has negative numerator(D-A)v2-A*d2, so
x decreases from a value below X to0. The ratio b lies between
v0/(v0+d0) and A0/D0, hence in(0,B]. Multiaffine interpolation gives
J+(1-x)(1-b)(1-z)v1>=0 along the entire branch.

Player3's Quit-minus-Continue gap is continuous, positive at z=0 in the
remaining case, and at z* equals b[Z3(23)-Gamma32]-(1-b)v3<0.
An interior IVT zero makes owners0,2,3 indifferent, while1 Continues.
All hazards are proper and q0>0, so its supported Quit value is nonpositive.
No recovery branch or strategic root was assumed.

## 6. The complete table and an actual two-date profile

Native own and live/Never rewards are zero. For nonempty A subset{1,2,3}, use

| A | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
| 1 | 100 | 0 | -2 | -2 |
| 2 | -3 | 1/2 | 0 | 1 |
| 3 | 100 | -3 | -1 | 0 |
| 12 | -3 | 1/4 | 1 | -6 |
| 13 | 100 | -100 | -1 | 10 |
| 23 | -3 | 9 | 3 | -100 |
| 123 | -3 | 11 | 2 | 1 |

Put gamma=(gamma1,gamma2,gamma3)=(-194/3599,13203/7198,6).
For every coalition A containing0, set Z0(A)=0, and for i=1,2,3 set
Zi(A)=-1 if i belongs to A, and Zi(A)=gamma_i otherwise. This specifies
all sixty coordinates. Every gamma_i>-1. Row0 participant rewards are zero,
and every row2 passive reward is at most13203/7198<2<10. The table belongs
to the precise remaining fixed-core strip 0<a<1/2,p>0.

Here date1 and date2 mean the FIRST and SECOND available decision periods
(physical natural times0 and1). No earlier decision date is omitted.
Use independent laws with date1 hazards

    s=(0,1/5,0,1/3600),

and, conditional on reaching date2, hazards t=(1/2,0,0,0), then Never.
Equivalently player0 chooses date2 or Never equally, player1 chooses date1
with probability1/5, player2 always Never, and player3 chooses date1 with
probability1/3600. All random choices are independent.

The date2 tail, initialized at AllNever, is exact native Nash and has

    c=U=B=e=(0,-97/3599,13203/14396,3).

Indeed each core player's immediate Quit offer is -1/2 while its Continue
and Never payoff is gamma_i/2>-1/2; player0 is indifferent at zero. All later
pure deadlines and Never give gamma_i/2 to a core player, so these are the
full caps, not merely one-step bounds.

At continuation c, the date1 pair13 prefix is exact Nash. Its active
indifference equations are

    c1=-97*(1/3600)/(1-1/3600)=-97/3599,
    c3=12*(1/5)/(1-1/5)=3.

Quiet0 has Quit0 and positive Continue901/45. Quiet2 has

    Q2=3613/18000 < C2=1/3.

The choice c2=13203/14396 makes C2=1/3 exactly. Exact full-cap prefixing and
indifference therefore give actual

    v=U=B=e=(901/45,-1/36,1/3,2),
    N=(1/2,4/5,1,3599/3600), product N=3599/9000>0.       (1)

In particular the continuation is on the actual independent diagonal and
on the FULL zero-debt carrier. It is also strictly inside the passive box
[-3,100] x [-3,9] x [-2,13203/7198] x [-6,6].

### Complete uniqueness of the first Nash prefix

For core players let g_i^core be Quit-minus-Continue with q0=0 and terminal
continuation v. Because the rows involving0 have the prescribed constant
passive/participant structure, their full gaps are exactly

    g_i=(1-q0)g_i^core-(1+gamma_i)q0.                    (2)

If q0=1, all core players strictly Continue; then player0 strictly Continues
because v0>0. Hence q0<1 at every Nash root, and a core player with positive
hazard must have g_i^core>=0.

Suppose q1=0. Then g3^core=-101q2-2(1-q2)<0, so q3=0. Next
 g2^core=-1/3<0, so q2=0. Player0 then strictly Continues, giving q0=0,
after which player1 strictly Quits since -v1=1/36>0. This contradiction
proves q1>0.

The exact player1 core gap is

    g1^core=(1-q3)(1-10q2)/36+q3(-97+99q2).             (3)

It is strictly negative whenever 1/10<q2<97/99. Since q1>0, (2) excludes
that interval. On the high branch q2>=97/99, player0's Continue value is at
most100(1-q2)-3q2<=-91/99<0: conditional on player2 continuing, every
payoff including v0 is at most100; conditional on its Quit, it is -3.
Player0's Quit offer is0, so Nash would force q0=1, already impossible.
Therefore q2<=1/10.

On this low branch player0's exact Continue value is

    C0=(1-q2)[100-(100-v0)(1-q1)(1-q3)]-3q2
       >=(1-q2)v0-3q2 >=443/25>0.                     (4)

Thus q0=0. As q2<1, its Continue action must be optimal, so

    0>=g2^core=3q1+4(1-q1)q3-(1-q1)(1-q3)/3
                >=3q1-(1-q1)/3.

Hence q1<=1/10. At these q1 the affine-in-q2 player3 gap has endpoint bounds

    q2=0: 12q1-2(1-q1)<=-3/5,
    q2=1: -101(1-q1)+7q1<=-451/5.

Both are strictly negative, so q3=0. If q2=0, player1 strictly Quits, contrary
to q1<=1/10. Thus 0<q2<1, and its indifference equation gives q1=1/10.
Player1 is now properly mixed, and (3) forces q2=1/10. Every pure, mixed
and sure-owner pattern has been included. The UNIQUE Nash prefix is

    q=(0,1/10,1/10,0).

Direct substitution yields

    u=F(q,v)=(12459/500,1/40,1/10,147/100)>>0.          (5)

The inactive0 comparison is C0=12459/500>Q0=0; for inactive3 it is
C3=147/100>Q3=-809/100. The joint survival is81/100.

### Complete uniqueness of AllContinue after the crossing

More generally let u>>0 with u0<=100. Equation (2) still holds, with the
core gaps now evaluated at u. A sure0 again makes every core player strictly
Continue, then makes0 strictly Continue; impossible. So q0<1.

If q1=0, then g3^core=-101q2-u3(1-q2)<0, followed by g2^core=-u2<0.
Thus any nonzero core support requires q1>0. But its gap is

 g1^core=(1-q3)[-q2/4-u1(1-q2)]+q3(-97+99q2).

The bracket is strictly negative, so q1>0 forces q2>=97/99. The row0 upper
bound used above again gives C0<=-91/99<0, forcing q0=1, contradiction.
Hence every core hazard is zero. Since u0>0, player0 strictly Continues too.
AllContinue is therefore the unique Nash prefix, and it preserves u.

Starting from (1), every nonempty finite Nash word first uses q just computed
and then only AllContinue. Its output is (5), and its survival is81/100.
No word of ANY finite length is good in the low-or-sure sense. This statement
is about exact Nash prefixes, not approximate prefixes or arbitrary strategies.

The table has an absorbing exact equilibrium: player0 quits at the first
period and everyone else Never. Every quiet player prefers gamma_i>-1 to
joining. Its row1 payoff is negative and its Never product is zero. The
positive-Never source above is therefore not a GLOBAL minimum on the marked
zero-debt carrier. This is a complete actual-source obstruction to universal
Nash-word recovery, not an obstruction to UE or to a proof using global
least-Never extremality.

## 7. Joint reselection gives an exact path to absorption

The same table admits a smooth zero-debt path that no added Nash word can
follow. For 0<r<=1 replace the last solo0 hazard by r and the first hazards by

    q1=r/(r+2), q3=2r/(3599+2r), q0=q2=0.

With D=(r+2)(2r+3599), the actual full zero-debt annotations are

    U=B=e=v(r),
    v0=100(1-7198/D), v1=-200r/(3599+2r),
    v2=r(6001-2r)/D, v3=10r/(r+2),
    nu=7198(1-r)/D.

Indeed the last tail is (0,r*gamma); the first active equations are
c1=-97*q3/(1-q3) and c3=12*q1/(1-q1). Quiet0 has positive Continue value,
and quiet2 has Continue-minus-Quit slack 2r(1195-3r)/D>0. Exact cap prefixing
therefore proves full zero debt, including r=1. The marked condition v1<0
holds throughout, while

    nu'=7198(2r^2-4r-10801)/D^2<0.

The point in Section6 is r=1/2; r=1 absorbs surely. Thus its two prescribed
periods can be reselected jointly to reach zero Never mass exactly.

Every v(r) nevertheless retains the finite-word trap. Write A=-v1,B=v2,
C=v3,V=v0. Directly, 0<A<1/4,0<B<1,V<=100 and

    V-12A=100r(3555-22r)/D>0,
    C-4B=2r(5993+14r)/D>0.

The Section6 proof now excludes 4A/(1+4A)<q2<97/99. The high branch
forces the impossible sure0. On the low branch row0 Continue is at least
(V-12A)/(1+4A)>0, so q0=0. Player2 Continue gives q1<=B/(B+3);
C>4B and B<1 make both endpoint gaps of player3 negative. The unique root is

    q=(0,B/(B+3),4A/(1+4A),0).

Its active outputs and row0 output are positive. Row3 output has the sign of
C-2B/3+4A-8AB>4B/3+4A>0, using A<1/4. Row0 output is at most100, so
only AllContinue can follow. Exact reselection of existing periods escapes
this trap; adding any finite number of exact Nash prefixes does not.

## 8. The complete marked geometry on every finite calendar

Change only the completion parameter gamma2 in Section6 to5408/3599,
throughout its coalition rule. Write a=194/3599, g=5408/3599,
B=2/3599, gamma=(-a,g,6). The same two physical dates and hazards give

    U=B_cap=e=(901/45,-1/36,3613/18000,2),
    N=(1/2,4/5,1,3599/3600), nu=3599/9000.

Here B_cap denotes the response vector; the scalar B above is2/3599.
The first quiet2 comparison binds. This point is a global minimum of nu
across the ENTIRE nonsolo marked finite-calendar class, not just a local
minimum on its two prescribed dates.

Precisely, every finite-calendar exact native Nash profile with positive
joint Never probability and min U<=0 has the same FULL(U,B_cap,e,N)
annotations as one of: AllNever; a solo0 root of hazard0<r<1; one pair13
root over a solo0 tail with0<r<=1/2; or one triple123 root over a solo0
tail with0<r<1/2. Every nonsolo form has nu>=3599/9000, with equality
only at the displayed binding annotations. Every continuous marked exact
finite-calendar path from these annotations to a smaller nu must pass
through AllNever, where nu=1. The calendar length and active supports may
vary arbitrarily along that path. The exact annotation set is a loop of
the pair and triple arcs, with the solo0 interval attached at AllNever.
This classifies finite exact profiles, not infinite calendars or limits
of profiles with positive debt. The table already has pure0 UE.

### Exhaustive roots over a solo0 tail

Write v(r)=(0,-ar,gr,6r), 0<=r<=1. For any one-stage Nash root q,

    g_i=(1-q0) g_i^core-(1+gamma_i) q0,  i=1,2,3,
    C0=100(1-q2)(q1+q3-q1*q3)-3q2, Q0=0.

A sure0 forces all core players quiet, and is Nash. If q1=0 then
`g3^core=-101q2-6r(1-q2)` forces q3=0 except possibly r=q2=0;
in that exception q3>0 makes g2^core=4q3>0 and forces q2=1,
a contradiction. Then q2>0 would either have g2^core=-gr<0 or,
when r=0, make C0=-3q2<0 and force the impossible sure0 with core
activity. Consequently either every core player is quiet or q1>0.

If core players are quiet, the exact roots are solo0 hazards satisfying

    q0 >= ar/(1-a+ar),

including q0=0 when r=0. Their aggregate tail is again v(r') with
r'=q0+(1-q0)r.

Assume now q1>0. Necessarily q0<1 and g1^core>=0. Its exact expression is

 g1^core=(1-q3)[ar(1-q2)-q2/4]+q3(-97+99q2).

It excludes the entire interval

    b(r)<q2<97/99,  b(r)=4ar/(1+4ar).

The high branch q2>=97/99 gives C0<=100(1-q2)-3q2<0 and forces
sure0, contradiction. Hence q2<=b(r)<1/4.

If q2=0 then C0>0 and q0=0. Otherwise g2^core>=0. Put S=q1+q3.
Since g2^core=3q1+4(1-q1)q3-gr(1-q1)(1-q3),

    S>=gr/(4+gr),
    C0>=50(1-q2)S-3q2
       >= [50gr/(4+gr)-12ar]/(1+4ar)>0.

The last inequality holds for 0<r<=1 since 50g/(4+g)>12a;
at r=0 the bound q2<=b(r)=0 excludes this case. Therefore q0=0.
Moreover q1=1 forces q2=1 by g2^core=3, and q3=1 makes
g1^core=-97+99q2<0. Thus q1,q2,q3 are all proper, and q1>0.
No singleton1 root is possible: if q2=q3=0 then g1^core=ar>0,
forcing q1=1; at r=0, quiet2 again prohibits q1>0.
All remaining roots have supports12,13,123, as follows.

#### Pair12

For r>0 its odds are x=gr/3, y=4ar, z=0. The quiet3 gap times
(1+x)(1+y) is

    r(4g-404a-6)+(28/3)ga r^2<0, 0<r<=1.

Its outputs for rows1 and2 are positive by the participant rewards a_core=1/4
and p=1. Row0 is positive by the preceding argument. The row3 output has
positive numerator

    r[6-2g/3+4a-8ga r]>0.

So this root leaves the marked set and has all-positive output.

#### Pair13

Its odds are x=r/2,y=0,z=Br. The quiet2 gap multiplied by (1+x)(1+z) is

    F(r,0)=3r(2r-1)/7198.

It exists exactly for 0<r<=1/2. With D=(r+2)(3599+2r), its binding-table
output (V,-A,C2,C3) is

 (100(1-7198/D), -200r/(3599+2r), r(3614-2r)/D, 10r/(r+2)).

This is the row2 formula for gamma2=5408/3599; the earlier Section7 uses
a different completion and has a different row2 payoff.

#### Triple123

With odds y of owner2, the active1 and active3 equations force

    x=(6r+101y)/(12+7y),
    z=(194r/3599-y/4)/(97-2y).

Proper positive roots therefore require 0<y<776r/3599. The remaining
active2 equation is

    F(r,y)=3x+4z+3xz-gr=0.

On 0<=r<=1, 0<=y<=776r/3599, z>=0,

    x_y=(1212-42r)/(12+7y)^2,
    z_y=97(16r-3599)/[14396(97-2y)^2].

Since y<1/4, x_y>61/10, -1/300<z_y<0, and x<3, it follows
that F_y=(3+3z)x_y+(4+3x)z_y>18. Also

 F(r,776r/3599)
    =13r(32531361-1129856r)/[7198(1358r+10797)]>0,  0<r<=1.

Therefore a unique triple root exists exactly for 0<r<1/2. At r=1/2
it meets pair13 at y=0. For this range y<1/8 and the same estimates
sharpen to x_y>7, x<4/3, and F_y>20.

### Every core-marked output has the same one-step trap

For the triple branch put delta=1/2-r. By F_y>20 and the value F(r,0),

    0<y<3r*delta/71980,
    y<r/47000,  y<delta/47000.

Also x_y<9 and z_y>-1/380 on the relevant rectangle, so

    r/2<=x<501r/1000,
    r/1800<z<=2r/3599<r/1799.

Write the triple output (V,-A,C2,C3). Exact participant formulas are

    A=(100z-y/4-11yz)/[(1+y)(1+z)],
    C2=(x+3z+2xz)/[(1+x)(1+z)],
    C3=(10x-100y+xy)/[(1+x)(1+y)],
    V=[100(x+z+xz)-3y(1+x)(1+z)]/[(1+x)(1+y)(1+z)].

The displayed elementary bounds imply

    0<A<1/4, 0<C2<51r/100<1, C3>3r>4C2,
    V>39r>12A,  V<=100.

For example A<100r/1799; C2<x+3z+2xz<503r/1000;
C3>(5-1/470)r/[(1+251/1000)(1+1/1000)]>3r;
and V>[50r-4r/47000]/[(1+251/1000)(1+1/1000)^2]>39r.
A>0 follows from z>r/1800 and y<r/47000.

The canonical Section7 support proof applies to any vector
(V,-A,C2,C3) satisfying these inequalities: its unique Nash root has
support12, odds x=C2/3,y=4A, and all-positive output. At every all-positive
output with row0<=100 only AllContinue is Nash. The pair13 outputs satisfy
the same inequalities by their binding-table formulas above. Thus no further
nonzero marked prefix can follow either13 or123.

### The minimum is global within the nonsolo finite class

Pair13 has nu=(1-r)/[(1+r/2)(1+Br)], strictly decreasing for r<=1/2.
Its minimum is 3599/9000 at r=1/2.

For a triple root, delta=1/2-r>0 and y<delta/47000. Since x<=r/2+9y,

 (1+x)(1+y)
   <=1+r/2+(10+r/2)y+9y^2
   <5/4-delta/2+(41/4+9/94000)delta/47000
   <5/4.

Also 1+z<=1+B/2 and 1-r>1/2. Hence

    nu=(1-r)/[(1+x)(1+y)(1+z)] >3599/9000.

Every positive-Never actual exact equilibrium on a finite calendar is a
finite word of Nash roots initialized at AllNever, by conditional optimality
at each all-Continue history, all of which have positive probability because
nu>0. An empty period is Nash only when its continuation is nonnegative,
so empty periods cannot be silently prepended to a negative tail. At AllNever the exhaustive classification
above permits only solo0 (or the zero root). Induction now gives exactly
the four marked forms claimed. All solo0 stages combine to aggregate r,
preserving the four actual U,e,B,N coordinates; replacing them by one
solo0 stage preserves equilibrium. This proves all-support/all-finite-date
scope, including support changes and arbitrary subdivisions.

### An exact nonlocal barrier for continuous finite-calendar deformations

Let a continuous path of full annotations consist pointwise of exact native
Nash profiles on finite calendars, with a nonpositive payoff coordinate.
Calendar lengths may be unbounded along the path. Suppose it starts at the
binding trap and ends with nu<3599/9000 (in particular, at an absorbing
profile). Then the path passes through the AllNever annotation nu=1.

Indeed, until the first time it can reach a smaller Never product, every
positive-Never point belongs to the exhaustive classification. The union of
the pair13 and triple123 images has nu>=3599/9000. Its closure meets the
solo0 image only at r=0: at every r>0 both core hazards q1 and q3 are positive,
while the solo0 image has N1=N2=N3=1. Conversely any sequence on the core
branches with those Never masses tending to1 has x,z tending to0, hence r
tending to0, and all four Never masses tend to1. The core-branch closure
has nu>=3599/9000, so it cannot meet an absorbing annotation. Continuity
therefore forces the path from the core branch through its sole intersection
with the solo0 image, namely AllNever. The barrier is sharp: decrease r
from1/2 to0 along pair13, then increase a solo0 hazard from0 to1 at the
FIRST physical date. Keeping that hazard behind an empty earlier date
would fail Nash because row1's continuation is negative.

More precisely, N0=1-r identifies the parameter on both core arcs, and
N2 distinguishes their interiors. The strict F_y bound and y<3r(1/2-r)/71980
make the triple arc continuous with the same two endpoints as the pair arc.
Thus their full annotation images form an embedded circle; the solo0
interval0<=r<1 attaches to it only at AllNever.

This is stronger than a fixed-calendar local-minimum obstruction. It does
not apply if the deformation allows positive debt, loses the marked condition,
uses genuinely infinite-calendar equilibria, or jumps discontinuously between
components. A global marked minimum compares all components and is not
constrained by this path barrier.

## 9. Even one full cap prevents exact finite compression

Section2 compresses(U,e), not caps. An elementary control sharpens the
existing [full-cap obstruction](CODEX_TARSKI_PREMIUM__FINITE_CALENDAR_PRESCRIBED_OUTCOME_REALIZATION.md):
set Z0(A)=2 if0,1 belong to A, 1 if1 belongs and0 does not, and0 otherwise;
set every other row to0. These rules specify all native rewards.
For 0<alpha<1 let players0,2,3 Never, and let player1 quit at physical date
t=0,1,... with probability alpha*2^(-t-1), and Never with probability1-alpha.
Every pure deadline of0 gives alpha, as does Never. Thus

    U=B=e=(alpha,0,0,0), N=(1,1-alpha,1,1).

Now allow ANY independent replacement of all four laws. Define effective
opponent atoms m_t=p1(t)Pr(T2>=t)Pr(T3>=t), including simultaneous dummy
quits. Then exactly

    e0=sum_t m_t,
    V0(t)=sum_(s<t)m_s+2m_t,
    V0(t)-e0=m_t-sum_(s>t)m_s.

If a finite calendar preserves e0=alpha>0, its last positive effective atom
gives V0(t)>alpha. No finite-calendar replacement preserves even(e0,B0),
regardless of whether other caps or Never masses must be preserved. Response
attainment is not the issue: all finite deadlines attain the original cap.

More sharply, if at most m>=1 effective atoms are positive, put delta=B0-e0.
Their chronological masses a_j satisfy a_j<=delta+sum_(l>j)a_l. Backward
induction gives alpha<=(2^m-1)delta, hence

    B0-e0>=alpha/(2^m-1).

Equality is achieved with players0,2,3 Never and
p1(t)=delta*2^(m-1-t) for t=0,...,m-1, delta=alpha/(2^m-1).
These laws preserve U,e,N EXACTLY; their total debt is delta. This game
already has the pure0 absorbing equilibrium. The result is a sharp semantic
compression boundary, not another UE exclusion.

## 10. Exact continuation fibres with approximated full caps

Let n>=2 owners independently choose times in Nat union {Never}; the first
finite coalition is paid by an arbitrary real reward table of absolute bound
M>=0, with AllNever value zero. U_i is prescribed payoff, e_i is the response
payoff when i always Never, B_i is the supremum over every behavioral response,
and N_i is the original marginal Never mass. Write C for the Euclidean closure
of all actual annotations (U,B,e,N).

For every integer k>=1 and every Y=(u,b,e,N) in C, there is an actual independent
profile q with all finite atoms on the literal calendar {0,...,L_k-1}, where

    L_k = 2 n(n+1) k + 4 n^2,

such that

    U(q)=u, e(q)=e, N(q)=N,
    max_i |B_i(q)-b_i| <= n(n-1) M/k.                 (A)

For Fin4: L_k=40k+64 and cap error 12M/k. The statement allows arbitrary
signed own singleton rewards. The exact equalities hold simultaneously;
q is one product law, not a correlated mixture. The finite calendar retains
enough empty gaps to preserve the entire pure-reply menu during retiming.

If u=b=e=v at Y, then exactly

    U(q)=e(q)=v, N(q)=N,
    0<=B_i(q)-v_i<=n(n-1)M/k.                        (B)

Thus an abstract zero-debt compact source admits arbitrarily accurate actual
approximants on its EXACT prescribed/Never-payoff and original-Never-mass fibre.
No payoff-mark drift or Never-product drift is needed in this approximation.

### Common small-mass cells

For each original marginal p_i, mark its first finite crossing of each level
j/k, j=1,...,k, whenever that level is attained at a finite date. Let F be the
union of marks, m=|F|<=nk. Partition Nat into its m marked singletons and its
at most m+1 nonempty intervening gaps, and add {Never} as a separate cell.
Every owner's mass in any gap is at most 1/k.

Indeed a gap mass greater than 1/k gives a grid level strictly between the
cumulative mass preceding the gap and the cumulative mass through some finite
date in the gap. Its first crossing would be marked inside the gap. The same
argument treats the unbounded final gap by taking a finite partial sum. Zero
or absent gaps cause no problem. Never is not part of the final finite gap.

### Sparse exact moment matching without changing cell masses

Fix all other current marginals and replace p_i. The vector (U,e) is affine
in p_i; e_i is constant. At most 2n-1 coordinates therefore change. Let K_i
be the number of partition cells with positive p_i mass. Adjoin the K_i
cell indicators, whose sum is one, to those 2n-1 conditional reward vectors.
Their affine dimension is at most (K_i-1)+(2n-1).

The countable barycentre belongs to the ordinary convex hull of its positive
support vectors. For completeness: it belongs to the closed convex hull;
if it lies on a relative supporting hyperplane, the nonnegative distance to
that hyperplane has mean zero, so every positive-mass vector lies there.
Reduce affine dimension. If no supporting hyperplane remains, the point lies
in the relative interior, which agrees with that of the ordinary convex
hull. Dimension induction proves the assertion. Caratheodory now replaces
p_i by at most K_i+2n-1 of its existing positive-mass actions while preserving
all (U,e) and every cell mass exactly.

Perform this once for each owner, using the CURRENT opponents. Every step
preserves the entire (U,e) vector; each owner's cell masses remain its original
ones. In particular all N_i are exactly retained. The final independent
profile q0 is finitely supported. Each occupied cell needs at least one
support point, so each owner has at most 2n-1 extra points beyond one per
occupied cell. Marked cells and Never have only one possible point anyway.
Writing g_i for the number of its occupied finite gaps, its finite gap support
has at most g_i+2n-1 points. Taking the union over players and then adding the
m common marked dates, the total number d of occupied finite dates satisfies

    d <= m + sum_i (g_i+2n-1)
      <= m+n(m+1+2n-1) = (n+1)m+2n^2
      <= n(n+1)k+2n^2.                               (C)

Some marked dates may disappear from a particular player's support; their
cell masses across all owners remain fixed. Using m as an upper bound is safe.

### Uniform approximation of EVERY response

Couple each owner's original and reduced times by first selecting their
common cell and then coupling their conditional draws arbitrarily. Make
these couplings independent across owners. Against a fixed deviator i at
one deterministic deadline t, terminal coalitions can differ only if:

(a) two opponents' cell labels coincide in one finite gap; or
(b) an opponent occupies the finite gap containing t.

Away from (a),(b), opponent clocks have identical weak order and ties,
and identical comparison with t, in the original and reduced profiles.
Marked singleton times are literally equal. Never remains Never.

For an opponent pair j,l, independence and small gap masses give

    P(same finite gap)=sum_G p_j(G)p_l(G)<=1/k.

There are choose(n-1,2) opponent pairs. For finite t in a gap, each of the
n-1 opponents is in that gap with probability at most 1/k. Thus the exceptional
probability is at most

    [choose(n-1,2)+(n-1)]/k = n(n-1)/(2k).

For t=Never or a marked singleton, clause(b) is absent, so the same upper
bound remains valid. Every response payoff differs by at most 2M times this
probability. Hence uniformly over ALL finite deadlines and Never,

    |V_i^q0(t)-V_i^p(t)|<=n(n-1)M/k.

Behavioral responses are mixtures of these pure times. Taking suprema gives
|B_i(q0)-B_i(p)|<=n(n-1)M/k. This is not merely comparison of the supported
responses or the compressed timing game's restricted Nash inequalities.

### Retiming preserves all gaps and all caps

List the d occupied finite dates as t_1<...<t_d. If d=0 use AllNever.
Otherwise set s_1=0 if t_1=0, and s_1=1 if t_1>0. Recursively set

    s_(j+1)-s_j = 1 if t_(j+1)=t_j+1, and 2 otherwise.

Then 0<=s_j<=2d-1. Push every marginal through t_j ->s_j, fixing Never.
This preserves prescribed terminal coalitions and all Never-counterfactual
coalitions, hence U,e,N. It also preserves every pure-response payoff in
both directions: a deadline is either an occupied atom, in a nonempty gap
before/between atoms, after the last atom, or Never. Exactly the same classes
exist after retiming. Select the matching atom or any point of the matching
gap. The weak comparisons with every occupied opponent time agree.
The after-last finite class and Never are distinct and both retained.
Therefore ALL B_i are exactly preserved by retiming.

This uses the union of every player's occupied dates. An atom occupied only
by the deviator is harmless: an extra response class relative to the larger
union either coincides with an opponent-menu class or subdivides it into
identical payoffs. No response option is added or removed.

By(C), the finite atoms lie in {0,...,L_k-1}. This proves(A) for actual Y.
The gap rule is essential for arbitrary singleton rewards; blindly ranking
occupied dates can remove the initial or intermediate profitable response.

### Compact-closure points and exact-fibre recovery

Take actual annotations Y_r converging to Y in C. For a fixed k, apply the
construction to every Y_r and place the resulting laws on the SAME literal
calendar {0,...,L_k-1,Never}. The product of n finite probability simplexes
is compact, so select a convergent subsequence of these laws, with limit q.

On that fixed calendar U,e,N are polynomials in the law masses. Each B_i is
the maximum of finitely many polynomial response payoffs, using the menu
{0,...,L_k,Never}. Every later finite deadline is outcome-equivalent to L_k.
Consequently the full caps are continuous on this compact simplex, even
when occupied dates vanish at the limit. The finite menus use all possible
dates, not a support-dependent menu. Passing to the limit proves(A) exactly.
Since B_i(q)>=U_i(q), zero-debt sources give(B).

The order of quantifiers is important: fix k, compress the whole approximating
sequence with one uniform calendar bound, and only then take the finite-law
limit. Truncating each source at an uncontrolled cutoff would not prove this
exact-fibre conclusion.

### Exact marked-source consumer

Specialize now to Fin4. Assume native own rewards are zero, and use the
existing compact marked minimum source: minimize nu=product_i N_i over Y in C with U=B and min_i U_i<=0.
If the absorbing native debt infimum A_Z>0, its repair estimate gives

    A_Z<=sum_i(B_i-U_i)+14M nu^(1/4),

so its minimum m is positive. Every N_i>0, and the exact actual inequality
B_i-U_i>=N_i(B_i-e_i), extended to C, yields U=B=e=v.
The theorem then supplies, for EACH k, an actual finite law q_k with

    U(q_k)=e(q_k)=v, N(q_k)=N*, min v<=0,
    product_i N_i(q_k)=m,
    total debt(q_k)<=48M/k                            (Fin4).

This is a stronger normal form for the SAME globally selected source. It
preserves its marked payoff and original Never product exactly. It does not
make q_k exact Nash, select a different minimum, or prove that a finite
calendar has an exact marked minimizer. The exact finite-calendar obstruction
in Section9 remains consistent with it.

A rigorous practical consequence is a hierarchy of finite real-algebraic
necessary tests for a proposed selected source (v,N): for every k, there must
exist a point of the L_k-date product simplex satisfying U=e=v, marginal
Never masses N, and every pure reply payoff <=v_i+12M/k. Those are finitely
many polynomial weak inequalities of degree at most n, plus exact moments.
Failure at ANY level rules out that candidate source. Passing all levels is
EXACTLY equivalent to (v,v,v,N) lying in C: the reverse direction follows
by taking these actual annotations to their stated zero-debt limit.
This equivalence is a countable hierarchy, not a finite UE decision procedure.

No finite level is shown to remove an entire new raw reward class. This
is a stronger representation of the same actual source. Global marked minimality is not
replaced by its finite-calendar local version.

## Verification and remaining target

The [exact geometry checker](../experiments/CODEX_COORDINATOR__ACTUAL_CONTINUATION_GEOMETRY_CHECK.py)
reconstructs full caps and Never masses and checks the source, crossing,
reselection, complete finite-calendar classification, and survival bounds.
The all-support exhaustion and exact-fibre approximation are mathematical
proofs, not conclusions from numerical root searches.

Section10 sharpens the implemented common-quantile approximation, which
retains N and controls caps but changes U and e. The new step is simultaneous
exact moment matching inside its common cells, before fixed-calendar
compactness. Relevant declarations inspected without running Lean are
`hasEscapeAwareQuantileClockCompressionAtBound` and
`HasEscapeAwareQuantileClockPayoffTransportAtBound`
(`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`),
`quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw`
(`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`),
`quittingPureClockOrderEquivalent_finiteCalendarRetiming`
(`UniformEquilibrium/Quitting/Paths/CommonStoppingCalendarRetiming.lean`), and
`exists_mem_quittingFiniteOpponentAtomGapReplyMenu_payoff_eq_cap`
(`UniformEquilibrium/Quitting/Terminal/FiniteOpponentAtomGapReplyMenu.lean`).
The quantile cells are defined in `MathUE/Probability/QuantileClock.lean`.
These checked ingredients do not already state the simultaneous exact-fibre
conclusion proved here. No fresh Lean certification is claimed.

The live target is GLOBAL marked least-Never extremality, retaining the
full cap constraints. Its selected payoff and original Never masses can
now be fixed exactly across finite actual approximants. Those approximants
have small positive debt; Section8's exact-profile classification cannot
be applied to them. Even unrestricted finite-calendar exact deformations
can encounter a barrier requiring a nonlocal move through AllNever.
A source-consuming descent argument or a new strategy construction is
still needed. Fin4 remains open.
