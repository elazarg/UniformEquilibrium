# Repairing opposed pairs closes a mixed-core collision cylinder

## 1. Exact statement and conjecture-facing change

This is ordinary mathematics, not a Lean-checked theorem. It proves uniform
equilibrium on an explicit four-player reward class. Its new step replaces
every opposed-pair Nash crossing by a three-owner root at the SAME
continuation. The construction preserves the quiet owner's comparison by
a finite convexity test and finds the joining owner's indifference by the intermediate
value theorem. Combined with the outer parameter cases proved below, it
closes an entire two-parameter collision cylinder under stated completion
conditions. Arbitrary Fin4 remains open.

All coalition rewards are finite, the live reward is zero, and strategies
use independent private randomization. The conclusion quantifies every
complete unilateral behavioral replacement. The equilibrium payoff is fixed
before the requested accuracy; strategies and horizon thresholds may depend
on that accuracy.

Players are I={0,1,2,3}. Let kappa_i=r_i({i})>=0 and
Z_i(A)=r_i(A)-kappa_i, with native own, live and Never rewards zero.
Define Gamma_ij=Z_i({j}) for all i,j in I; its diagonal is zero.
On coalitions contained in S={1,2,3}, fix the core recipient entries

| A | Z1 | Z2 | Z3 |
|---|---:|---:|---:|
| 1 | 0 | -2 | -2 |
| 2 | 1/2 | 0 | 1 |
| 3 | -3 | -1 | 0 |
| 12 | a | p | -6 |
| 13 | -100 | -1 | 10 |
| 23 | 9 | 3 | -100 |
| 123 | 11 | 2 | 1 |

Assume 0<a<1/2 and p>=0. Write

    s=1/2-a>0, c=p+2>=2,
    W=max(0,max_{A nonempty,2 notin A} Z2(A)).

Require the finite raw conditions

    Z0(A)<=0 whenever 0 belongs to A;
    Z0(02)-Z0(2)>=0, Z0(012)-Z0(12)>=0;
    W<=5c.                                              (R)

Read four independent joining increments from the table:

    d0=Z1(01)-Z1(0)>=0, d1=Z1(012)-Z1(02)>0,
    e0=Z2(0)-Z2(02)>=0, e1=Z2(01)-Z2(012)>=0.          (J)

Let L1=min(0,min_{A nonempty,1 notin A} Z1(A)). For a real scalar f require

    Z3(T union{3})-Z3(T)<=-f
                  for T={0},{0,1},{0,2},{0,1,2}.       (Q3)

Put tau=s/d1, Delta_d=d1-d0, Delta_e=e1-e0, and

 K(v1,v2)=-12e0*d1+101d0*e1+7e0*d0-60e1*d1
              +f[(s-v1)Delta_e+(c+v2)Delta_d].

Require e1*tau<=c and the following eight finite corner inequalities:

 K(v1,v2)-3f*Delta_d*Delta_e*alpha>=0
 for v1 in{L1,0}, v2 in{0,W}, alpha in{0,tau}.          (CVX)

Finally require

 max(7-f*tau,0)W+101e1*tau+7e0*tau
             -(101+f*tau)c+f*tau^2*Delta_e<=0.         (E)

Repeated corners are harmless. These are raw finite reward tests, with no
continuation or strategy supplied. The scalar f is also an ordinary raw
parameter: its four bounds (Q3) and eight tests (CVX) are affine inequalities
in f, and (E) is equivalent to its two affine endpoint tests at v2=0,W.
Thus its existence is exactly intersection of fourteen explicitly computed
closed half-lines on the real line, with a constant test giving all of R or
the empty set. Empty or degenerate intersections are included; no strategic feasibility oracle is assumed.

**Theorem.** Under these conditions the infimum A_Z of total full native
terminal Nash debt over absorbing independent profiles is zero. Hence the
original game has one fixed uniform-equilibrium payoff, against every
complete unilateral behavioral replacement. No root, continuation, strategy,
calendar or equilibrium is a premise.

**Constant-increment specialization.** If d0=d1=d>0 and e0=e1=e>=0,
(CVX) reduces identically to36de>=0. Then the only extra scalar guards are

    e*tau<=c,
    max(7-f*tau,0)W+108e*tau-(101+f*tau)c<=0,
    tau=s/d.

For d=e=f=1 these hold for EVERY 0<a<1/2,p>=0 under W<=5c, since

    e*tau=s<1/2<c,
    (7-s)W+108s-(101+s)c
       <=-(66+6s)c+108s<=-132+96s<-84.

The main theorem permits unequal d0,d1 and unequal e0,e1. All unlisted
coordinates are arbitrary subject to the finite tests. Row0 need not vanish
on participant coalitions, and passive row3 rewards have no upper bound.
The inequalities include equality cases, e0=e1=0, and some f<0.

**Whole-cylinder corollary.** Keep the displayed core, but allow every real
a and every p>=0. Impose the row0 conditions in (R), W<=10,
d0=d1=e0=e1=1, and (Q3) with f=1. Then A_Z=0 and the original game has a
fixed uniform-equilibrium payoff for every such a,p. The completion
restrictions remain in force throughout this corollary; it is not a
statement about all completions of the singleton matrix. Section5 proves
both outer parameter cases as well as the opposed strip.

There are no strategic inputs: the finite reward tests produce the repair
path, the selected roots, the local escape words, and the actual profiles
with vanishing debt. None of these is an assumed certificate. Original own
levels may be arbitrary nonnegative numbers. The separating example below
uses own levels all equal to one.

## 2. Complete deviations and the closed passive domain

A prescribed behavioral strategy is an independent private law of its first
Quit time, including Never. Before absorption there is just the all-Continue
live history. Thus any complete unilateral behavioral replacement is a law
of its first Quit time, and its payoff is a mixture of pure-deadline and
literal-Never payoffs. Let U_i be prescribed native payoff, B_i their full
supremum, e_i the literal-Never response payoff, and N_i the original
marginal Never mass. Put d_i=B_i-U_i and nu=product_i N_i.

For a product prefix q define

    h(q)=product_i(1-q_i), H_i(q)=product_{j!=i}(1-q_j),
    Q_i(q)=E[Z_i(A union{i})],
    P_i(q)=E[Z_i(A) 1_{A nonempty}],
    E_i(q)=q_i Q_i(q)+(1-q_i)P_i(q),

where A is the independently sampled opponent quitter set. Exact prefixing
updates the full semantic data by

    U'_i=E_i+h U_i,
    B'_i=max(Q_i,P_i+H_i B_i),
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i.                (P)

The two terms in B' account for quitting now and continuing with an arbitrary
complete deviation. In particular (P) includes every finite deadline and
Never. The payoff and cap maps are coordinatewise 1-Lipschitz in their
terminal annotations, independently of finite-word length.

An exact root is Nash at v when its used actions maximize Q_i and
P_i+H_i v_i. Its output is F_i(q,v)=E_i+h v_i. Starting U=B=v, a Nash
root preserves U=B. A root is proper if every q_i<1. Call a root good when

    some q_i=1, OR min_i F_i(q,v)<=0.                 (G)

The root correspondence is nonempty by finite mixed Nash existence and has
closed graph. The good-root graph is closed too, since (G) is a finite union
of closed conditions. A bad root is therefore proper with all outputs
strictly positive.

Define the literal closed passive box

    L_i=min(0,min_{A nonempty,i notin A} Z_i(A)),
    R_i=max(0,max_{A nonempty,i notin A} Z_i(A)),
    D=product_i[L_i,R_i].                            (D)

Every actual e belongs to D. The e-map in (P) preserves D under every root:
it is a convex combination of its old coordinate and passive rewards.
In particular v_2<=W for v in D. The row1 and row3 intervals contain zero
in their interiors by the fixed core; the other intervals may be one-sided or degenerate.
No interior assumption on the whole box is needed.

Actual laws, and virtual words initialized at U=B=e=z and N_i=1, satisfy

    B_i>=e_i, d_i>=N_i(B_i-e_i).                     (C)

For actual laws, split the prescribed own law into finite deadlines and its
Never atom: U_i<=(1-N_i)B_i+N_i e_i. For virtual words, (C) starts at
equality and is preserved by each prefix. The exact residual identity is

 d'_i-N'_i(B'_i-e'_i)
 =q_i(B'_i-Q_i)
 +(1-q_i)(1-N_i)(B'_i-P_i-H_i B_i)
 +(1-q_i)H_i[d_i-N_i(B_i-e_i)] >=0.

Consequently a zero-debt point with nu>0 satisfies U=B=e in D. This remains
true on compact closures. Passive bounds are used at these zero-debt points,
not as bounds on arbitrary positive-debt prescribed payoffs. A common finite
full-reward bound M bounds all payoff and cap coordinates needed below.

The raw part of the proof will establish

    for every v in D with min v<=0, a good Nash root exists.       (V)

Section 6 proves that this selected property, on the closed domain (D),
produces actual absorbing profiles with vanishing complete terminal debt.

On the face q3=0 the exact full gap identities and upper bound are

    g1=(1-q0)g1^core+q0[d0(1-q2)+d1*q2],
    g2=(1-q0)g2^core-q0[e0(1-q1)+e1*q1],
    g3<=(1-q0)g3^core-f*q0,                           (J-gap)

where the core gaps set q0=0. Conditioning on owner0 quitting and then on
the other active owner's action gives these formulas directly. The unused
owner1 and owner2 joining increments when3 is present remain unrestricted,
subject to the passive bounds. No gap identity outside this face is needed:
every bad root has q0=0, and the repair keeps q3=0.

## 3. Every bad pair12 supplies a good root on012

Suppose v in D admits a bad root with exact support12. Its active odds are

    x1=v2/c>0, x2=-v1/s>0.

Thus v2>0 and v1<0. The input coordinate v0 can have either sign.
The quiet3 Nash comparison holds, possibly at equality. Quiet0 is strict:
its Continue value is its positive output, whereas Q0<=0 by (R).

For alpha in[0,tau], set q3=0 and

    q0=alpha/(1+alpha),
    D1=s-v1-alpha*Delta_d, D2=c+v2-alpha*Delta_e,
    q1=y(alpha)=(v2+e0*alpha)/D2,
    q2=b(alpha)=(d0*alpha-v1)/D1.                      (Path)

Both denominators are affine and positive at both endpoints: at tau,
D1=d0*tau-v1>0 and D2>=v2+e0*tau>0. Therefore they stay positive. Moreover

    1-b=(s-d1*alpha)/D1, 1-y=(c-e1*alpha)/D2.

Both hazards are positive and proper before tau; b(tau)=1 and y(tau)<=1.
At alpha=0 this is the original bad pair. Direct substitution gives

    -s*b-v1(1-b)+alpha[d0+(d1-d0)b]=0,
    c*y-v2(1-y)-alpha[e0+(e1-e0)y]=0.

By (J-gap), owners1,2 remain exactly indifferent along the entire path.
No equality between the two d increments or between the two e increments
has been assumed.

The full gap of3, multiplied by1+alpha, is at most its core gap minus
f*alpha. Multiplying this upper bound by the positive product D1*D2 gives

 N(alpha)=12(v2+e0*alpha)(s-d1*alpha)
  -101(d0*alpha-v1)(c-e1*alpha)
  +7(v2+e0*alpha)(d0*alpha-v1)
  -v3(c-e1*alpha)(s-d1*alpha)-f*alpha*D1*D2.            (N)

This is cubic. No upper bound on v3 is needed. At the initial pair, its
quiet3 comparison is v3>=12x1-101x2+7x1x2. Since x1=v2/c<=W/c<=5 and
x2>0, that threshold is strictly less than12x1<=60. Put v3hat=min(v3,60),
and let Nhat be (N) with v3 replaced by v3hat. It still has Nhat(0)<=0
because v3hat is at least the initial quiet threshold. Throughout[0,tau],
(c-e1*alpha)(s-d1*alpha)>=0 and v3>=v3hat, so N<=Nhat.

The exact second derivative satisfies

 Nhat''(alpha)/2=-12e0*d1+101d0*e1+7e0*d0-v3hat*e1*d1
       +f[(s-v1)Delta_e+(c+v2)Delta_d]
       -3f*Delta_d*Delta_e*alpha
    >=K(v1,v2)-3f*Delta_d*Delta_e*alpha.

The last inequality uses v3hat<=60 and e1*d1>=0. The right side is affine
in each of v1,v2,alpha. Every needed triple belongs to
[L1,0]x[0,W]x[0,tau]; convex interpolation from its eight corners and (CVX)
therefore make it nonnegative. Thus Nhat is convex, including affine and
degenerate cases. At tau the continuation term vanishes, and exactly

 Nhat(tau)=N(tau)=(d0*tau-v1)[(7-f*tau)v2+101e1*tau+7e0*tau
                   -(101+f*tau)c+f*tau^2*Delta_e]<=0.  (End)

This follows from0<v2<=W and (E). A convex function lies below its endpoint
chord, so N<=Nhat<=0 throughout the path. The upper bound (J-gap) then
keeps owner3 quiet, including an initial tie. This clips only an auxiliary
scalar bound; every actual root comparison uses the ORIGINAL continuation v.

Owner0's full gap is continuous along (Path). At alpha=0 it is strictly
negative by the bad pair's positive quiet output and Q0<=0. At alpha=tau,
owner2 quits surely, so owner0's continuation term vanishes. Its gap is

    (1-y(tau))[Z0(02)-Z0(2)]
       +y(tau)[Z0(012)-Z0(12)]>=0.                   (O0)

The intermediate value theorem yields 0<alpha*<=tau where this gap is
zero. Owners0,1,2 are indifferent and owner3 prefers Continue. If alpha*<tau
all three active hazards are proper; if alpha*=tau, owner2 quits surely
and owner1 may also be sure. Thus this is a whole-game exact Nash root in
either case, with owner0 output Q0<=0. It is the required good root. In particular every bad opposed pair has an explicit one-dimensional
repair route; an actual continuation or cap assumption was not used.

## 4. Exhausting the other possible bad roots

Fix v in D with min v<=0. If min v=0, AllContinue is good, so take min v<0.
A proper bad root cannot activate0, whose output would be Q0<=0. A singleton
active owner has output its own reward0. Pair13 has Q1<0 and pair23 has
Q3<0. Thus only pair12 and triple123 can be bad. If a bad pair occurs,
Section3 already supplies a good root. Assume no bad pair occurs.

For completeness, the passive-bound triple calculation is as follows.
On a positive triple use odds x1,x2,x3. The active equations are v=phi(x):

    phi1=-s*x2-97x3+2x2x3,
    phi2=c*x1+4x3+3x1x3,
    phi3=12x1-101x2+7x1x2.                            (T)

If W=0, phi2>0 is impossible. Otherwise set X=W/c<=5. Then x1<X.
At a bad triple, Q3>0 gives x2<10x1/(100-x1). Since 101-7x1>0,
substitution in phi3 gives

    v3>x1(190+58x1)/(100-x1)>0.

At every positive triple candidate at this same v2,v3, whether bad or not,

    x1<X<=5, x2<12x1/(101-7x1)<10/11.                (Bounds)

Its active Jacobian has form

 Dphi=[[0,A,-B],[C,0,D],[E,-F,0]],
 A=-s+2x3, B=97-2x2, C=c+3x3,
 D=4+3x1, E=12+7x2, F=101-7x1.

We have B>95,C>=2,F>66,D<19,E<19, and s<1/2. Therefore

    det Dphi=A*D*E+B*C*F
             >95*2*66-(1/2)*19*19=24719/2>0.          (Det)

Solving phi2=v2 and phi3=v3 gives

    x2=(12x1-v3)/(101-7x1),
    x3=(v2-c*x1)/(4+3x1).

The positive feasible x1 form one interval. Along it, (Bounds)--(Det) hold and

    d(phi1)/dx1=det(Dphi)/[(4+3x1)(101-7x1)]>0.

There is consequently at most one bad triple. It is regular. Its inactive0
comparison is strict because its output is positive while Q0<=0. For the
full clipped Nash map T_i(q)=clip(q_i+g_i(q,v)), its ambient index is
sign((-1)^3 det Dphi)=-1: inactive coordinates contribute identity rows,
and active rows are the negative gap Jacobian up to positive factors.

If no good root existed, every Nash root would therefore be that one bad
triple. The clipped map takes ambient space into the unit cube, so
Id-T has degree+1 on(-1,2)^4, by a straight-line homotopy to the cube center.
Degree additivity would instead give -1, a contradiction. Finite Nash
existence rules out an empty root set as well. Thus a good root always
exists. No perturbation of v or of the game is required anywhere.

This proves (V) on the opposed strip, including weak quiet comparisons and
all boundary inputs. Section6 supplies its complete actual-data consumer.

## 5. The whole unit-gap cylinder

For d0=d1=e0=e1=f=1, Section1 verifies (CVX) and (E) whenever
0<a<1/2,p>=0. Thus Sections3–4 already cover that strip. We prove both outer cases without assuming another
reward-table theorem.

For any real a the active triple equations are those in (T), with -s=a-1/2.
The passive bound and a bad triple's positive third output still give
v3>0,x1<5,x2<10/11, independently of a. If a<=0, pair12 cannot be bad
because its owner1 Quit output is nonpositive. The numerator of owner1's
Quit offer at a bad triple would be

    a*x2+(-100+11*x2)*x3<0,

also impossible. Every root is good in this case.

If a>=1/2, the triple Jacobian entry A=a-1/2+2x3 is nonnegative, so its
determinant and uniqueness bounds only improve. Bad triples are still
unique and have ambient index -1. When a>1/2, a bad pair12 solves
v1=(a-1/2)x2,v2=(p+2)x1 and is unique. Its active Jacobian determinant is
-(a-1/2)(p+2)<0, so its ambient index is -1 when the inactive comparisons
are strict. Inactive0 is automatically strict by its nonpositive Quit cap.
Perturb v3 slightly within D to avoid the unique possible inactive3 tie.
When a=1/2, pair12 requires v1=0; perturb v1 within D to avoid that equality.
Both permitted intervals are nondegenerate because the fixed singleton
rewards have both signs in rows1 and3. These perturbations can preserve
min v<0, including at boundary inputs.

At each such generic point, the only possible bad roots are at most one
pair and one triple, both regular and of index -1. If every root were bad,
degree additivity would contradict total degree +1. A good root therefore
exists. Compactness and the closed Nash/good graphs remove the perturbation.
At min v=0, AllContinue is directly good. This proves (V) for all real a
and p>=0 under the corollary's conditions.

## 6. Closed-domain selection produces vanishing actual debt

We give the complete local-to-actual argument because (V) supplies a selected
low-or-sure root and only on the closed passive domain.

First consider v in D with v>=0 and min v=0 at which AllContinue is the
only good root. Put S_0={i:v_i=0}. Compactness and closedness of the good-root
graph imply that all good roots at nearby points of D with min<=0 are
arbitrarily small. There are no nearby sure roots. At small roots every
outsider with v_i>0 strictly prefers Continue, so these good roots are
supported on S_0. Other, bad roots need not be small.

We prove by induction on |S_0| the following local assertion. Given a positive
hazard bound and any eta in (0,1), there are finite words supported on S_0,
with each root below that hazard bound and survival in [1-eta,1-c] for some
fixed c>0, whose full debt from U=B=e=v tends to zero and whose payoff
minimum has limsup<=0. Their retained original survival factors are used;
no conditional-tail reset is made.

If Gamma_{S_0 S_0} has a nonzero nonnegative kernel vector x, normalize
sum x=1 and repeat q=epsilon x for floor(T/epsilon) roots, with a fixed
sufficiently small T>0. On S_0, P_i=O(epsilon^2), Q_i=O(epsilon), and
E_i=O(epsilon^2). Formula (P) then bounds both core payoffs and core cap
errors by O(epsilon) over the whole word. Positive outsiders retain their
Continue buffers for small T; their cap and payoff updates coincide.
Survival tends to exp(-T)<1, and choose T so this limit exceeds 1-eta.
This proves the local assertion in the kernel case, including |S_0|=1.

Otherwise zero is outside the convex hull of the columns of
Gamma_{S_0 S_0}. Strict separation gives a signed row w with
w Gamma_{S_0 S_0} strictly positive in every coordinate. For all sufficiently
small S_0-supported hazards,

    w E_{S_0}(q)>=gamma sum_i q_i>=0                 (W)

for some gamma>0. Choose a positive delta below the requested hazard bound,
below the bound for (W), and below eta/16. By the preceding graph argument
there is rho>0 such that every good root at an input within rho of v in D
with min<=0 is S_0-supported and has each hazard below delta. Shrink rho
so every coordinate positive at v remains positive within rho of v.
Take M>=1 bounding all native rewards and the relevant domain coordinates,
and fix, before choosing any seed,

    c_0=min(eta/4,rho/(8M),1/4)>0.                   (Budget)

Choose j in S_0 and t>0 so small that

    z=(1-t)v+t Gamma[:,j], ||z-v||_infinity<rho/4.

The solo-j prefix has identical prescribed and Never annotations equal to z:
for j both are zero, and for other rows both are the displayed affine
combination. Hence z belongs to D, z_j=0, and
w z_{S_0}=t w Gamma_{S_0,j}>0. This provides an exact closed-domain seed.
Initialize the virtual annotations U=B=e=z,N_i=1. These initial caps are
virtual; they are not asserted to be the actual caps of that solo prefix.

Close the outputs of all finite words of S_0-supported roots with hazards
at most delta and survival h>=1-eta. This is a compact set of bounded
(U,B,e,N). Minimize h on its closed subset

    B=U, min U<=0, w U_{S_0}>=h w z_{S_0}.           (Fiber)

The empty word is feasible. Coherence (C) forces U=e in D at each feasible
point. Every word also satisfies the displacement bound

    ||U-v||_infinity<=||z-v||_infinity+2M(1-h).        (Move)

If a minimizing h satisfies h>1-c_0, (Budget)--(Move) place its payoff within
rho/2 of v. Property (V) supplies a good root there, which is S_0-supported
and has hazards below delta. A nonzero such root preserves zero debt and
the nonpositive minimum. It preserves the original weighted inequality in
(Fiber) by (W). Moreover,

    h(q)h>(1-4delta)(1-c_0)>1-eta,

so the prefixed point remains inside the survival constraint and has smaller
h, a contradiction. Therefore AllContinue is the only good root there,
which forces U>=0. Its zero set T is nonempty, while (Fiber) and w z_{S_0}>0
show U_{S_0} is not identically zero. Thus T is a proper subset of S_0.

Apply induction at U, using hazard bound delta and a survival budget eta_1
small enough that h(1-eta_1)>1-eta. Its words are T-supported and therefore
S_0-supported. Inequality (W) preserves the ORIGINAL row w inequality
through every such word. A compact endpoint has zero debt, nonpositive
minimum, and survival strictly below h, still in the same minimizing fiber.
To realize this endpoint in the original closure, approximate the minimizing
state by its seed-generated finite words, append each finite extension, and
choose the approximation closely enough for that extension. Prefix maps
are continuous and the survival slack is strict. This contradicts minimality.

Every seed minimum consequently has h<=1-c_0. Approximate it by its defining
finite words and let t tend to zero. Applying those same words to v changes
both payoff and cap coordinates by at most ||z-v||, independently of length.
A diagonal sequence therefore has debt tending to zero, payoff minimum with
limsup<=0, and eventually survival at most 1-c_0/2. This proves the local
assertion. At every recursive minimum, (C) supplies membership in the same
closed passive domain; no unsupported interior or actual-tail claim enters.

Now take the compact closure of all actual finite-dimensional data
(U,B,e,N). Finite prefixes act continuously and preserve this closure.
Moving an owner's Never mass to one finite date makes that owner quit surely
and hence gives an absorbing profile. Its own cap is unchanged, since its
opponents are unchanged. Four prescribed payoffs and three other cap values
each change by at most twice the reward bound times that moved mass.
Moving a smallest original Never mass gives, also on the closure,

    A_Z<=sum_i(B_i-U_i)+14M nu^(1/4).                (Repair)

Minimize nu over B=U,min U<=0 in this closure. AllNever makes the set
nonempty: its native payoff, cap and Never response are all zero. If A_Z>0,
(Repair) implies that the minimum m is positive. At a minimizer (C) gives
U=B=e=v in D. Every nonzero good root contradicts minimality: a sure root
has zero debt and nu'=0, contradicting (Repair); a proper good root keeps
min U'<=0 and decreases nu. Thus only good AllContinue remains, forcing
v>=0,min v=0. The local assertion gives a compact zero-debt endpoint with
min U<=0 and original Never product at most m(1-c)<m. This final
contradiction proves A_Z=0.

For kappa>=0, an absorbing prescribed profile receives the full own shift,
whereas a deviator receives at most that shift. Thus original regret is at
most native regret. Terminal approximate Nash profiles at every accuracy
select one fixed uniform-equilibrium payoff by the standard terminal-to-
uniform endpoint cited in Section 8. No public correlation, deviation signal,
or restricted deviation class was used.

## 7. Exact examples and boundaries

Here is a complete native table. Set r_i(A)=1+Z_i(A), so every original own
level is one.

| A | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
| 0 | 0 | 2 | 5 | -3 |
| 1 | 3 | 0 | -2 | -2 |
| 2 | -1 | 1/2 | 0 | 1 |
| 3 | 3 | -3 | -1 | 0 |
| 01 | -20 | 3 | -10 | -1 |
| 02 | -1/10 | 5 | 4 | -1000 |
| 03 | -1000 | 10 | 0 | -4 |
| 12 | -12 | 1/4 | 1 | -6 |
| 13 | 2 | -100 | -1 | 10 |
| 23 | -25 | 9 | 3 | -100 |
| 012 | -1 | 6 | -11 | -1 |
| 013 | -5 | 11 | -2 | -2 |
| 023 | -10 | 10 | -1 | -1001 |
| 123 | -10000 | 11 | 2 | 1 |
| 0123 | -20 | 11 | -3 | -2 |

The opposed parameters are a=1/4,p=1. The four increments in
(J) are d0=d1=e0=e1=1, and (Q3) holds at equality with f=1. Here W=5,
tau=1/4, and all eight (CVX) expressions equal36>0. The two owner0 joining gains
in (R) are9/10 and11. The endpoint expression is

    (7-1/4)*5+108/4-(101+1/4)*3=-243<0.

All raw hypotheses therefore hold. Unequal increments also have an exact
control: replace only Z1(012)=6 by601/100. Then d0=1,d1=101/100,
e0=e1=1 and tau=25/101. With f=1 the minimum of the eight (CVX) expressions
is3531/100>0 and the endpoint expression is-24568/101<0. With f=1/2 they
are7059/200>0 and-24468/101<0, respectively; all four (Q3) bounds then hold
strictly. The remaining nontrivial raw guards are strict as well. Continuity gives a
neighborhood in the unlisted completion coordinates, with the numerical
core fixed, accepted by the main theorem. The completion entries vary independently here; the fixed-core
restriction remains.

The previous negative-index pair condition fails: both pair participant rewards are positive, but their
joining product is (-1/4)*3<0. The new construction handles this positive
index rather than assigning it a false negative sign.

The table also refutes universal marked-coordinate invariance, even on
arbitrarily small passive neighborhoods of zero. For the full marked set use

    q=(0,epsilon,epsilon,0),
    v=(0,-epsilon/[4(1-epsilon)],3epsilon/(1-epsilon),2epsilon).

The active equations hold exactly. The prescribed output is

    (2epsilon-14epsilon^2,epsilon/4,epsilon,
     epsilon-9epsilon^2+2epsilon^3)>>0

for all sufficiently small positive epsilon. Quiet0's Quit offer is
-201epsilon/10+191epsilon^2/10<0 and quiet3's is
-90epsilon+91epsilon^2<0, so both quiet comparisons are strict. For every
proper nonempty marked set C, one of the safe positive edges

    0->2, 2->1, 1->0, 2->3, 3->0

enters C: their graph is strongly connected. An edge j->i means
Gamma_ij>0 and Z_i(ij)<=Gamma_ij. Put q_j=epsilon, other hazards zero,
v_i=v_j=0, and v_k=epsilon*(1+|Gamma_kj|+|Z_k(kj)|) for other k.
This is exact Nash, with min_C v=0 and all C outputs strictly positive.
Each passive interval contains zero in its interior, so all these inputs
belong to D for small epsilon. Selection is therefore essential.

A complete finite comparison of this literal table with the other accepted
raw producers includes all stationary patterns, all sure-first patterns with
arbitrary actual punishment tails, every withdrawal child and weight, all
return/reset roles, and the singleton and weighted selectors. Such coverage
exclusions distinguish this existence class from those named producer
families. They are not premises or steps in the UE proof and do not assert
an unrestricted positive behavioral gap.

The affine quiet-gap case is real, not merely a formal endpoint. In the
same literal table, replace the owner2 entries for coalitions containing0,2
by the corresponding reward without2 (so e=0). Replace the owner3 entries
for coalitions containing0,3 by the corresponding reward without3 plus1
(so f=-1). Set Z3(0)=1000 and consequently Z3(03)=1001. Keep all remaining
entries fixed. Then d0=d1=1,e0=e1=0,W=5 and tau=1/4, while the passive
row3 maximum is1000. Its endpoint expression is
(7+1/4)*5-(101-1/4)*3=-266<0. Section3 still applies because N is affine;
the same absence of a passive row3 bound holds for positive e0,e1 by the
clipped-continuation argument above.

The weak boundaries are realized by an exact variation of the first table.
Set Z0(02)=Z0(2)=-1 and Z0(012)=Z0(12)=-12. For each coalition containing0,2,
set its owner2 reward to the corresponding reward without2 minus12; for
each coalition containing0,3 set its owner3 reward to the corresponding
reward without3 minus28. Keep all other entries fixed. Then d0=d1=1,e0=e1=12,f=28,
c=3,tau=1/4,W=5; both owner0 joining gains are zero, e1*tau=c, and (E) is
108*3-(101+7)*3=0. All eight corner expressions equal432>0. In fact
q=(1/5,1,1,0) has all four gaps zero at every continuation, with output
(-12,7/5,-18/5,-5); its sure owners make it a good root directly.

The condition e1*tau<=c keeps owner1 proper before the far endpoint. Weak
owner0 joining gains give a nonnegative endpoint gap. The intermediate root
may be the endpoint itself, where owner2 is sure and the root is still good.
Equality in (E) is also allowed, and the auxiliary clipped value may equal60.
Conditions beyond these weak bounds are not justified by this proof, and no
necessity or maximality is claimed.

## 8. Source correspondence, adapter, and Lean handoff

The exact cap update is already represented by
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The actual-data adapter here augments it by the Never response e and the
ORIGINAL masses N, proves coherence, and uses only the literal closed
passive box at zero-debt minima. Section6 produces absorbing approximate
native Nash profiles; nonnegative own shifts preserve their regret bound.
The semantic endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
It selects one fixed original payoff target and covers all behavioral
deviations, all sufficiently long horizons, and every positive accuracy.

The implemented conditional index selector
`exists_exactRoot_singletonSublevel_of_badRoot_negative_derivatives` in
`UniformEquilibrium/Quitting/Root/NegativeBadRootSelectedReturn.lean`
uses `Math.Topology.not_all_fixedPoints_have_negative_det_finite` in
`MathUE/Topology/AmbientDegreeNegativeFixedPointObstruction.lean`.
It cannot directly discard the opposed pair, whose index is positive.
The new content is the raw three-owner repair in Section3 and the resulting
whole-cylinder selection in Sections4–5. Section6 reproduces the complete
closed-domain consumer needed to carry this selection to actual strategies;
that consumer is not claimed as a new mathematical result.
The existing boxed consumer
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn` in
`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`
requires a selected low output. Section6 supplies the proof for the closed
passive domain and the additional sure-owner alternative.

The joining-attractive and mixed-sign triple raw sources in
`UniformEquilibrium/Quitting/Classification/JoiningAttractiveCoreGenericReturn.lean`
and `UniformEquilibrium/Quitting/Classification/MixedSignTripleCoreSelectedReturn.lean`
require different joining signs. Here the opposed pair has negative joining
product, as do13 and23, while the greatest premium core is123. The signed
pair-core source in
`UniformEquilibrium/Quitting/Classification/SignedPairCoreBadRoot.lean`
requires greatest-core cardinality2. These are source-hypothesis comparisons,
not claims that an assumed strategic return certificate has been ruled out.

For formalization, first define the four joining increments and the raw
corner tests,
and verify the identities and upper bound (J-gap) on q3=0. Formalize the
rational path, the cubic second derivative, finite-box interpolation, and
the endpoint inequalities, then apply a one-variable intermediate value
theorem. State the result as a good-root producer from the raw rewards and
an arbitrary v in D with min v<=0. Implement the finite support exhaustion
and degree argument, followed by the closed-domain(U,B,e,N) consumer.
No desired strategy or return conclusion belongs in the raw data structure.
The final theorem has parameters for all rewards and nonnegative own levels,
finite raw hypotheses, and concludes existence of a uniform-equilibrium
payoff. No new Lean check is claimed by this mathematical packet.
