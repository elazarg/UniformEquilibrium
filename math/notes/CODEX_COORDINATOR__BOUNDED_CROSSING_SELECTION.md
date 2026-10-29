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
index. Sections6–9 show that exact actual realizability, full zero debt,
positive Never masses, and even local Never minimality on a fixed calendar
do not supply
universal Nash-prefix return. A global least-Never argument must use its
extremality; finite exact cap compression is unavailable.

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

## 8. A binding comparison creates a full two-date local minimum

Change only the completion parameter gamma2 in Section6 to5408/3599,
throughout its coalition rule. The same two physical dates and hazards give

    U=B=e=(901/45,-1/36,3613/18000,2),
    N=(1/2,4/5,1,3599/3600), nu=3599/9000.

The first period's quiet2 comparison is now exactly binding. All last-period
quiet comparisons and the first-period quiet0 comparison are strict. We
classify ALL nearby two-date zero-debt laws, not just the original supports.
Positive marginal Never masses persist. Every conditional tail is then
exact Nash: a profitable conditional replacement could be used after that
positive-probability all-Continue history. Conversely backward Nash prefixing
from Never preserves zero debt.

Put A=1/2,B=2/3599,r0=1/2. Strict comparisons force the last support to be
{0}, with hazard r, and the first support to be13 or123. Let x,y,z be the
first-period odds of owners1,2,3. Active indifference for1 and3 gives

    x=(12Ar+101y)/(12+7y),
    z=(97Br-y/4)/(97-2y).

The remaining comparison is F(r,y)<=0 for y=0, and F(r,y)=0 for y>0, where

    F(r,y)=3x+4z+3xz-(5408/3599)r.

On the pair arc, F(r,0)=3ABr(r-r0), so locally r<=r0. Its Never product
(1-r)/[(1+Ar)(1+Br)] strictly decreases in r, hence increases when departing
from r0 along the feasible pair arc. On the triple arc F_r(r0,0)=3/7198>0,
so the implicit function theorem produces the unique nearby branch r(y).
At y=0 exact differentiation gives

    r'=-46188057/776, x'=-69262831/2328,
    z'=-11547912/349103,
    (log nu)'=-r'/(1-r)-x'/(1+x)-1-z'/(1+z)
             =4157665811/29100>0.

Thus the source is a STRICT local minimum of nu on the entire two-date
zero-debt set, including the adjacent triple branch. Its negative row1
persists, so this is also a strict local minimum with min U<=0 imposed.

The Section6 support proof still applies: v2=3613/18000 replaces1/3,
q1=3613/57613 replaces1/10, and every player3 bound only becomes stricter.
The unique external root is (0,3613/57613,1/10,0), with positive output

    (12809661/576130,1/40,3613/57613,469644/288065).

Only AllContinue follows. That prefix decreases Never mass but leaves the
marked set; it does not contradict marked local minimality. The pure0
absorbing equilibrium still exists and is marked. Hence this point is not
a global marked minimum, and no positive absorbing debt gap is established.

A finite support-grammar extension is also exact. Allow arbitrarily many
Nash periods, initialized at Never, with positive joint Never mass. Delete
zero roots and require each remaining root to have EXACT support{0} or{1,3}. Every13 prefix gives positive row0 payoff, precluding a
later prefix supported on0. All solo0 periods therefore come later in
physical time and aggregate to one hazard r. With D=(r+2)(2r+3599), the first13 root has quiet2
slack 3r(1-2r)/D, so it exists exactly when0<r<=1/2. Its output is

    v0=100(1-7198/D), -v1=a=200r/(3599+2r),
    v2=c=r(3614-2r)/D, v3=b=10r/(r+2).

A second13 root would need c>=b/4+4a/97+ab/388. Instead

    c-b/4-4a/97-ab/388=-r(3958r+1047599)/(194D)<0.

Every nonempty reduced word is consequently solo0 alone, or one13 root over an
aggregate solo0 tail with r<=1/2. The binding point minimizes nu on the
latter component. Extra periods in this grammar do not escape; another
support or a nonlocal change of component is required. This statement does
not quantify arbitrary larger calendars with unrestricted supports.

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

## Verification and remaining target

The [exact geometry checker](../experiments/CODEX_COORDINATOR__ACTUAL_CONTINUATION_GEOMETRY_CHECK.py)
reconstructs full caps and Never masses, checks the source and crossing,
and verifies the reselection and binding-branch identities. The all-support
uniqueness, local exhaustion, and finite-compression impossibility arguments
are the proofs above, not numerical root searches.

The actual-domain test of Section3 remains a necessary condition. Its source
can no longer be eliminated merely by adding full-cap equality or positive
Never masses: Section6 meets both. Even a local minimum on a fixed calendar
is insufficient by Section8. The live target is to exploit a GLOBAL marked
least-Never source (or its positive-gap provenance), with either unrestricted
calendar reselection or a genuinely new strategy construction. Exact finite
compression of its caps cannot be assumed. Fin4 remains open.
