# Exact opposed-pair path tests produce uniform equilibrium

Ordinary mathematics, not a Lean-checked theorem. Players are I={0,1,2,3}.
A finite reward table r pays at the first nonempty quitting coalition; live
and Never rewards are zero. Assume kappa_i=r_i({i})>=0 and put
Z_i(A)=r_i(A)-kappa_i, with native live and Never rewards zero.
All randomization is independent and private. A unilateral deviation may
replace the player's entire behavioral strategy.

**Theorem.** The explicit raw reward conditions in Sections1--4 imply that
the infimum A_Z of total native terminal Nash debt over absorbing profiles
is zero. Consequently the original game has one fixed uniform-equilibrium
payoff: for every positive error a behavioral profile approaches that payoff
and bounds every unilateral deviation over all sufficiently long horizons.
No strategy, continuation, punishment, or return certificate is assumed.
The conditions may be tested after any permutation of the four owners.

The new mechanism retains all four actual quiet-player joining differences
and eliminates its continuation using the initial Nash inequality. Four
quadratic tests characterize that path's binding-continuation envelope
exactly. The endpoint test allows either active player to become sure first,
and allows a negative individual joining gain for owner0. Core rewards are
arbitrary subject to explicit inequalities; no numerical core is fixed.
These are sufficient UE conditions, not necessary conditions for UE.

A literal separating table in Section7 passes these tests and fails the
previous frozen convexity producer and the audited stationary, sure-first,
withdrawal, weighted, return/reset, and matrix-source families. The complete
closed-domain strategy consumer is reproduced in Sections5--6; it is an
inherited result, not another novelty claim. The Fin4 conjecture remains open.

For a stage root q and continuation v, Q_i is the payoff from Quit now,
C_i the payoff from Continue now followed by v. Nash means every used action
maximizes these two quantities. A root is proper if all q_i<1, and good if
some q_i=1 or its output has a nonpositive coordinate. A bad root is proper
with strictly positive output in every coordinate.

## 1. Pair geometry and all quantities

Players are 0,1,2,3; native own, live and Never rewards are zero. Write
Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}), c_ij=J_ij-Gamma_ij and
b3=Z3(123)-Z3(12). Suppose c12=-s<0, c21=c>0, and put
l=c31, m=c32, n=b3. For this local lemma l,m,n may be arbitrary.
Assume Z0(A)<=0 whenever 0 belongs to A. On the face q3=0 set

 d0=Z1(01)-Z1(0)>=0, d1=Z1(012)-Z1(02)>0,
 e0=Z2(0)-Z2(02)>=0, e1=Z2(01)-Z2(012)>=0,
 delta00=Z3(03)-Z3(0), delta10=Z3(013)-Z3(01),
 delta01=Z3(023)-Z3(02), delta11=Z3(0123)-Z3(012).

The four delta entries are arbitrary real numbers. There is no common bound
or sign assumption on them. Set

 tau=min(s/d1,c/e1) if e1>0, and tau=s/d1 if e1=0.

Take any proper Nash root at continuation v with exact support12 and with
all four outputs positive. Write x=-v1/s>0 and y=v2/c>0 for its pair odds
(the odds of owner2 and owner1, respectively). Its quiet3 comparison is

 v3 >= phi(x,y):=l*y+m*x+n*x*y.

For 0<=alpha<=tau put

 A=s*x+d0*alpha, B=c*y+e0*alpha,
 C=s-d1*alpha, D=c-e1*alpha,
 q0=alpha/(1+alpha), q1=B/(B+D), q2=A/(A+C), q3=0.       (Path)

The two denominators are strictly positive for x,y>0, and all three active
hazards are proper before tau. At tau at least one of1,2 is sure. The two
active gaps vanish identically:

 -s*q2-v1*(1-q2)+alpha[d0*(1-q2)+d1*q2]=0,
 c*q1-v2*(1-q1)-alpha[e0*(1-q1)+e1*q1]=0.

Thus the path retains exact indifference for owners1,2. At alpha0 it is the
original pair. The EXACT quiet3 gap, multiplied by the positive denominator
(1+alpha)(A+C)(B+D), is

 N_v(alpha)=l*B*C+m*A*D+n*A*B-v3*C*D
       +alpha[delta00*C*D+delta10*B*C+delta01*A*D+delta11*A*B].    (N)

This follows by conditioning on owner0's action. No comparison outside the
q3=0 face enters. Since C,D>=0 and v3>=phi, one has

 N_v(alpha)<=N_phi(alpha)=alpha*R(alpha;x,y).            (E)

The right side is exact when the original quiet comparison is binding.

## 2. Four quadratic tests replace continuation quantifiers

Write R=r0+r1*alpha+r2*alpha^2, where

 r0=c*(d0+d1*x)*(m+n*y)+s*(e0+e1*y)*(l+n*x)
                       +c*s*(delta00+delta10*y+delta01*x+delta11*x*y),

 r1=n*d0*e0-m*d0*e1-l*d1*e0-d1*e1*(l*y+m*x+n*x*y)
       +delta00*(-c*d1-s*e1)
       +delta10*(s*e0-c*y*d1)
       +delta01*(c*d0-s*x*e1)
       +delta11*(c*y*d0+s*x*e0),

 r2=delta00*e1*d1-delta10*e0*d1-delta01*e1*d0+delta11*e0*d0.    (Q)

For a quadratic p(t)=a+b*t+d*t^2 define TEST_tau(p) by the finite conditions

 p(0)<=0 and p(tau)<=0;
 if d<0 and 0<-b/(2*d)<tau, also p(-b/(2*d))<=0.       (T)

Equivalently the last comparison is 4*d*a-b^2>=0. TEST is NECESSARY AND
SUFFICIENT for p<=0 on [0,tau]: a convex quadratic maximizes at an endpoint,
and a concave quadratic has only its single vertex to check. Linear and
constant cases are included.

Bounded-odds version: choose H,X>0. Require TEST_tau of the FOUR polynomials
R(alpha;x,y) at (x,y) in{0,H}x{0,X}. Because R is multiaffine in(x,y),
these tests are exactly equivalent to

 R(alpha;x,y)<=0 for every alpha in[0,tau], x in[0,H], y in[0,X].

Unbounded-negative-continuation version: choose X>0. Write
R(alpha;x,y)=R0(alpha;y)+x*R1(alpha;y). Require TEST_tau on the FOUR
polynomials R0,R1 at y=0,X. Then, and only then,

 R(alpha;x,y)<=0 for every alpha in[0,tau], x>=0, y in[0,X].

Here R1 is only affine in alpha, so two of the tests use only endpoints.
The equivalence follows because an affine function of x is nonpositive on
[0,infinity) exactly when its constant and slope are nonpositive, followed
by affine interpolation in y. These are exact equivalences for (E)'s
binding-continuation upper envelope. They are not claimed necessary for
repair at every ACTUAL bad pair: the binding value can lie outside the
actual continuation domain, and an actual inequality can be strict.

There is no auxiliary f. Decreasing any individual delta weakly improves
all tests: before division by alpha the four coefficient multipliers are
alpha*CD, alpha*BC, alpha*AD, alpha*AB, all nonnegative throughout the path.
If a common bound delta<=-f is preferred, using its largest permitted
f=min(-delta00,-delta10,-delta01,-delta11) is valid here. This monotonicity
was lost by the earlier sufficient second-derivative test.

## 3. The endpoint closes the whole-game Nash root

At the initial bad pair, owner0's gap is strictly negative: its Continue
output is positive while its Quit offer is nonpositive. Write

 g01=Z0(01)-Z0(1), g02=Z0(02)-Z0(2),
 g012=Z0(012)-Z0(12).

No separate nonnegativity of these gains is needed. Use the EXACT endpoint
numerator test corresponding to the first sure owner:

 (i) C(tau)=0: require E2(y)=g02*(c-e1*tau)
                  +g012*(c*y+e0*tau)>=0 at y=0,X;
 (ii) D(tau)=0: require E1(x)=g01*(s-d1*tau)
                  +g012*(s*x+d0*tau)>=0 at x=0,H,
      or require E1(0)>=0 and g012>=0 for the unbounded-x version.

At least one case applies. If both C(tau)=D(tau)=0, either test simply
reduces to g012>=0. In case(i), q2(tau)=1 and owner0's gap is exactly
E2(y)/(B(tau)+D(tau)); case(ii) is the symmetric expression
E1(x)/(A(tau)+C(tau)). The denominators are positive at actual pair odds.
Affine interpolation proves the endpoint gap is nonnegative throughout the
required initial-odds domain. These are necessary and sufficient for that
uniform endpoint property, including zero endpoint numerators. Individual
g01 or g02 can therefore be negative.

If Section2's quadratic tests hold, (E) proves quiet3 continues throughout.
The intermediate value theorem gives alpha* in(0,tau] where owner0 is
indifferent. Owners1,2 remain indifferent, so all four comparisons are Nash.
Owner0's output is Q0<=0. This is the required good low-or-sure root at the
SAME v. The first-sure alternatives remove the earlier restriction
e1*s/d1<=c; weak comparisons and simultaneous certainty are included.

## 4. Raw mixed-core conditions and the remaining supports

Combine Sections1--3 with the following finite raw conditions.
They control every possible remaining bad support. Native own levels are0 and original
own offsets kappa_i>=0. Let S=123, T_i=Zi(S),
b_i=T_i-Zi(S without i). In addition to Section1's assumptions require

 J13<0, J32<0, J31>0, T3>=0;
 c21,c23,c31>0, c13,c32<0, b1,b2,b3>=0.

Put W=max(0, all passive row2 rewards). If W=0 no additional tests are
needed: both a pair12 and a triple123 candidate require v2>0. If W>0 put

 X=W/c21, F=-c32-b3*X, G=-J32-T3*X,
 Y=c31*X/F, Bstar=-c13-b1*Y,
 a_star=c31*(-J32)-(-c32)*J31,
 Delta=Bstar*c21*F-s*(c23+b2*X)*(c31+b3*Y).

Require

 F>0,G>0,Bstar>0,Delta>0,
 a_star>=0, a_star+(b3*J31-c31*T3)*X>=0,                 (Triple)

and either Section2 test version, with H=-L1/s when bounded, where
L1=min(0, all passive row1 rewards), plus the Section3 endpoint comparisons.
If H=0 there is no bad pair and its tests are unnecessary.

Then every continuation v in the closed passive payoff box with min v<=0
has a good root. Indeed bad roots cannot activate0. Singletons have zero
active output; pair13 has Q1<0 and pair23 has Q3<0. Thus only pair12 and
triple123 can be bad. Every bad pair is repaired by Sections1–3.

For triples the active equations in positive odds are

 phi1=-s*x2+c13*x3+b1*x2*x3,
 phi2=c21*x1+c23*x3+b2*x1*x3,
 phi3=c31*x1+c32*x2+b3*x1*x2.

One has x1<X. At a bad triple, Q3>0 implies

 x2 < J31*x1/(-J32-T3*x1).

The denominator is positive by G>0. Substitution into phi3 gives

 v3 > x1*[a_star+(b3*J31-c31*T3)*x1]/(-J32-T3*x1) >=0.

The last inequality follows by affine interpolation of the two a_star tests.
At the same v2,v3 every positive triple candidate therefore satisfies
0<x1<X and 0<x2<c31*x1/(-c32-b3*x1)<Y. Put
A=-s+b1*x3, B=-c13-b1*x2, C=c21+b2*x3,
D=c23+b2*x1, E=c31+b3*x2, F'=-c32-b3*x1. Then

 det(Dphi)=A*D*E+B*C*F'>=Delta>0.

Solve phi2=v2,phi3=v3:

 x2=(c31*x1-v3)/(-c32-b3*x1),
 x3=(v2-c21*x1)/(c23+b2*x1).

The positive feasible x1 form one interval, and d(phi1)/dx1=det(Dphi)/(D*F')>0.
So at most one bad triple exists, regular with ambient index-1 and strict
inactive0 comparison. If no good root existed, there would be no bad pair
(by its repair), and every Nash root would be this one negative-index
triple. For completeness set g_i=Q_i-C_i and
T(q)_i=clip_[0,1](q_i+g_i). Fixed points of T are precisely Nash roots.
On (-1,2)^4, both T and its straight-line homotopy to the cube center take
values in [0,1]^4, so degree(Id-T)=+1. At the hypothetical bad triple,
quiet0 is strict because Q0<=0<C0. Its local row is an identity row;
the active gap Jacobian is Dphi multiplied on the left and right by
positive diagonal matrices (opponent survival and the odds derivatives).
The three active rows of Id-T have the negative of this Jacobian. Its
local index is therefore sign((-1)^3 det Dphi)=-1. The root is isolated
and is the only root under the no-good-root assumption, contradicting
the total degree+1.

This proves the selected-root property (V) used in Sections5--6. All
inequalities hold on the closed passive box, including its boundary.
No perturbation of the continuation is required: every opposed bad pair
has a direct repair and the only remaining hypothetical bad root is regular.

## 5. Complete deviations and the closed passive domain

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
In particular v_2<=W for v in D. These intervals may be one-sided or degenerate.
No interior assumption on the box or any of its intervals is needed.

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

## 7. Exact separating table and independent boundary controls

### A. Small-gain change with prior-producer coverage checks

Use the following complete native table, with original rewards r_i(A)=1+Z_i(A).
A concatenation denotes the corresponding player coalition.

| A | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
| 0 | 0 | 2 | 5 | -3 |
| 1 | 3 | 0 | -2 | -2 |
| 2 | -1 | 1/2 | 0 | 1 |
| 3 | 3 | -3 | -1 | 0 |
| 01 | -20 | 3 | -10 | -1 |
| 02 | -1/10 | 5 | 4 | -1000 |
| 12 | -12 | 1/4 | 1 | -6 |
| 03 | -1000 | 10 | 0 | -4 |
| 13 | 2 | -100 | -1 | 10 |
| 23 | -25 | 9 | 3 | -100 |
| 012 | -1 | 33/5 | -58/5 | -1 |
| 013 | -5 | 11 | -2 | -2 |
| 023 | -10 | 10 | -1 | -1001 |
| 123 | -10000 | 11 | 2 | 1 |
| 0123 | -20 | 11 | -3 | -2 |

The core, singleton matrix and passive row2 bound remain unchanged:
s=1/4,c=3,l=12,m=-101,n=7,W=5,X=5/3. Now

 d0=e0=1,d1=e1=8/5, all four delta=-1, tau=5/32.

For the UNBOUNDED x test the four exact polynomials are

 y=0:   R0=-3*(12*alpha^2-5045*alpha+10025)/100,
        R1=41*(631*alpha-1180)/100;
 y=5/3: R0=-(36*alpha^2-10315*alpha+25900)/100,
        R1=(68653*alpha-127315)/300.

Both quadratic vertices exceed5/32. Their endpoint pairs are
(-1203/4,-283761/1024) and(-259,-248721/1024). The affine endpoint pairs are
(-2419/5,-283761/640) and(-25463/60,-248721/640). All are strictly negative.
The row0 gains remain g02=9/10,g012=11, so its endpoint test passes strictly.
The inherited triple quantities are

 F=268/3, G=295/3, Y=15/67, Bstar=6469/67,
 Delta=6926587/268, a_star=190, a_star+(b3*J31-c31*T3)*X=860/3,

all positive. Hence this is a complete raw UE certificate, uniform over
ALL x>=0. This does not rely on any bound for the negative continuation.

In contrast, any common bound in the frozen convexity theorem requires
f<=1. At its corner(v1,v2,alpha)=(0,0,5/32), the CVX expression is

 -21/5+(57/32)*f <= -387/160 <0.

Thus no permitted f makes that theorem apply in its numerical labeling;
its whole-cylinder unit-increment corollary fails too. An exact rational census excludes all80 stationary patterns in1343
Bernstein subdivision nodes, and all65 sure-first patterns in162 nodes.
For stationary roots it tests F_i=(1-H_i)Q_i-P_i with signs <=0,=0,>=0
for quiet, mixed, sure owners. For sure-first roots with arbitrary actual
punishment tails it uses G_i=Q_i-P_i-H_i L_i, where the native lower caps
for original own levels1 are L=(-10000,-3,-10,-1000). A sure owner's
condition is G_i>=0; another sure owner makes H_i=0 for all remaining
players, so their necessary Nash signs are exact. Every actual original
punishment cap minus1 is at least this L_i, by the literal Never response.
Thus the latter census includes arbitrary actual punishment tails.

Each polynomial has degree at most2 in each free hazard. On every rational
box, convert to tensor Bernstein coefficients of that degree. Strictly
wrong-signed coefficients reject a necessary inequality; a strict uniform
sign rejects an equality. Otherwise bisect a longest side at its midpoint.
Faces with zero free variables are checked directly. For no-sure patterns,
origin boxes are separately excluded from F_S=-Gamma_SS q+O(||q||^2): every
principal Gamma_SS of size>=2 is nonsingular, and its exact inverse times
the coefficient-sum bound gives an explicit positive radius containing no
nonzero root. The single-owner supports reduce to affine interval tests.
For q0=0 with owner2 mixed and q1+q3>0, Q2>=0>P2 gives F2>0 directly.
All comparisons and all terminal nodes are rational; none is unresolved.

The singleton matrix is

 [0,3,-1,3; 2,0,1/2,-3; 5,-2,0,-1; -3,-2,1,0],

with determinant53/2. Its principal inverse/sign tests, all role permutations,
all14 proper withdrawal children with arbitrary nonnegative weights, three
coefficientwise weighted producers, all24 return roles and all12 reset
macros, and all15 marked-invariance candidates fail the corresponding
complete raw producer tests. The only ordered return role surviving the
weak sign requirements is(0,1,2,3), where K=-1/4 fails. The only pair with
both participant rewards positive is12, with opposed joining gains(-1/4,3).
Only owner0 has all participant rewards nonpositive; the inherited passive
INDEX branch therefore fails on that pair, and BLOCK fails on J12>0.
The fixed numerical core has no other admissible role permutation in the
frozen convexity class. Its all-real-a unit-gain corollary fails d1=e1=8/5.
These coverage exclusions do not assert a positive unrestricted regret gap;
the theorem above proves UE for this table.

### B. Four separate increments cannot be replaced by their common bound

For the next controls, first replace row012 in the displayed table by
(-1,6,-11,-1), so d0=d1=e0=e1=1. Then change only Z3(03)=147. Then delta00=150 and the other three delta equal-1. The four
UNBOUNDED x tests still pass: the two R0 quadratics are convex with common
quadratic coefficient151, and the R1 polynomials are affine. Their endpoint
pairs (ordered y0 constant/slope, yX constant/slope) are

 (-375/2,-1107/4), (-302,-1107/4),
 (-595/4,-243), (-796/3,-243).

All are negative. Every common bound instead requires f<=-150, while its
endpoint inequality becomes -241-2*f<=0 and therefore fails by at least59.
Even the arbitrary-core cubic-convexity version fails its endpoint test.
This exhibits a permitted POSITIVE quiet joining increment; other events
keep the exact path quiet. It is a path-comparison control, not an audited
new reward-class exclusion: stationary or other old producers may cover it.

### C. The other active owner can become sure first

Starting from the same control table with row012=(-1,6,-11,-1),
set d0=d1=1,e0=e1=16 and all four delta=-1000.
These are realized by Z2(02)=-11,Z2(012)=-26 and replacing each row3
participant-with0 entry by its passive-with0 value minus1000. Then

 tau=3/16<1/4, so OWNER1 becomes sure first.

The unbounded-x tests are affine, with endpoint pairs

 (-1005,-717), (-1025,-722),
 (-2140,-1912), (-6580/3,-5776/3).

The displayed row0 entries have g01=-23 and g012=11. Although one individual
joining gain is negative, the exact endpoint numerator is

 E1(x)=11*x/4+5/8>0 for every x>=0.

Thus the full whole-game repair works in a branch excluded by the older
endpoint order and by a requirement that both endpoint gains be nonnegative.
Again this is an exact boundary control, not a separate prior-producer audit.

## 8. Source correspondence and Lean handoff

The actual prefix cap identity is represented by
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). The debt transport
is represented by `quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect`
and `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`
(`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`).
The fixed-payoff endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).

The conditional index source
`exists_exactRoot_singletonSublevel_of_badRoot_negative_derivatives`
(`UniformEquilibrium/Quitting/Root/NegativeBadRootSelectedReturn.lean`)
uses `Math.Topology.not_all_fixedPoints_have_negative_det_finite`
(`MathUE/Topology/AmbientDegreeNegativeFixedPointObstruction.lean`).
It cannot discard the positive-index opposed pair. Sections1--3 produce a
replacement root directly. Section4 treats the remaining triple by degree;
Sections5--6 produce the actual absorbing approximate equilibria.

The selected boxed consumer
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn`
(`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`)
has a different input domain and a low-output return premise. The proof
above supplies the closed passive-domain and sure-owner variants it needs.
No desired strategic witness is a raw hypothesis in this packet.

For formalization, define the four actual delta entries, the path(A,B,C,D),
and the finite quadratic maximum test, including concave interior vertices.
Prove the exact factor N_phi=alpha*R and affine interpolation in initial
odds. Then formalize the finite endpoint comparisons and apply the
intermediate value theorem. This yields a good root from every bad pair.
Combine with the explicit triple determinant bound, the full degree argument,
and the reproduced closed-domain consumer. The final theorem quantifies
all original rewards and nonnegative own levels and concludes one fixed
uniform-equilibrium payoff. No new Lean check is claimed here.
