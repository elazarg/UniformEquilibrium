# Passive bounds select a return through a mixed three-player core

## 1. Statement and mathematical change

This is ordinary mathematics, not a Lean-checked theorem. It gives a raw
reward-table producer of uniform equilibrium for a four-player class with a
mixed three-player joining pattern. Positive-output Nash roots can occur
arbitrarily close to continuation zero; the proof selects another root using
its index and carries that selection through a closed passive-payoff domain.
The full Fin4 conjecture remains open.

Players are I={0,1,2,3}. Every nonempty quitting coalition A has a finite
reward r_i(A), and the live reward is zero. Assume the own rewards
kappa_i=r_i({i}) are nonnegative and define native rewards
Z_i(A)=r_i(A)-kappa_i. Thus Z_i({i})=0; native live and Never rewards are zero.
All strategies use independent private randomization. Every complete
unilateral behavioral replacement is included in the conclusion.

Define Gamma_ij=Z_i({j}) for all i,j in I; its diagonal is zero.
Let S={1,2,3}, and for distinct i,j in S write

    J_ij=Z_i({i,j}), c_ij=J_ij-Gamma_ij,
    T_i=Z_i(S), b_i=T_i-Z_i(S\{i}),
    W=max(0,max_{A nonempty,2 notin A} Z_2(A)).

Require the common raw conditions

    Z_0(A)<=0 whenever 0 belongs to A;
    J_13<0, J_32<0, J_31>0, T_3>=0;
    c_21,c_23,c_31>0; c_13,c_32<0; b_1,b_2,b_3>=0;
    Gamma_13<0<Gamma_12 and Gamma_31<0<Gamma_32.          (R)

When W=0 there are no further conditions. When W>0 put

    X=W/c_21, F=-c_32-b_3 X, G=-J_32-T_3 X,
    Y=c_31 X/F, B_*=-c_13-b_1 Y,
    alpha=c_31(-J_32)-(-c_32)J_31,
    Delta=B_* c_21 F+min(c_12,0)(c_23+b_2 X)(c_31+b_3 Y).

Require

    F>0, G>0, alpha>=0,
    alpha+(b_3 J_31-c_31 T_3)X>=0,                    (Q0)

and either of the following two branches:

    BLOCK: J_12<=0 and J_13+max(T_1,0)Y<=0; or
    INDEX: B_*>0, Delta>0, and
           (J_12>0 and J_21>0 together imply c_12>=0). (Q1)

**Theorem.** Under (R), and (Q0)--(Q1) when W>0, the infimum A_Z of total
native terminal Nash debt over absorbing independent behavioral profiles is
zero. The original table consequently has one fixed uniform-equilibrium
payoff. The payoff is fixed before the requested accuracy; the profile and
uniform horizon threshold may depend on that accuracy. No strategy,
continuation, certificate, punishment, or root is supplied as a premise.
Unlisted reward coordinates are arbitrary subject to these finite conditions.

The INDEX branch permits opposite signs in the reciprocal joining products
on 13 and 23. The BLOCK branch extends the resulting numerical class through
an additional whole half-space. Section 6 states that class and Section 7
gives a strict sixty-coordinate example, including an exact obstruction to
all one-step marked-set invariants on neighborhoods of zero.

## 2. Complete deviations, closed passive data, and selected roots

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
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i.                (1)

The two terms in B' account for quitting now and continuing with an arbitrary
complete deviation. In particular (1) includes every finite deadline and
Never. The payoff and cap maps are coordinatewise 1-Lipschitz in their
terminal annotations, independently of finite-word length.

An exact root is Nash at v when its used actions maximize Q_i and
P_i+H_i v_i. Its output is F_i(q,v)=E_i+h v_i. Starting U=B=v, a Nash
root preserves U=B. A root is proper if every q_i<1. Call a root good when

    some q_i=1, OR min_i F_i(q,v)<=0.                 (2)

The root correspondence is nonempty by finite mixed Nash existence and has
closed graph. The good-root graph is closed too, since (2) is a finite union
of closed conditions. A bad root is therefore proper with all outputs
strictly positive.

Define the literal closed passive box

    L_i=min(0,min_{A nonempty,i notin A} Z_i(A)),
    R_i=max(0,max_{A nonempty,i notin A} Z_i(A)),
    D=product_i[L_i,R_i].                            (3)

Every actual e belongs to D. The e-map in (1) preserves D under every root:
it is a convex combination of its old coordinate and passive rewards.
In particular v_2<=W for v in D. The row1 and row3 intervals contain zero
in their interiors by (R); the other intervals may be one-sided or degenerate.
No interior assumption on the whole box is needed.

Actual laws, and virtual words initialized at U=B=e=z and N_i=1, satisfy

    B_i>=e_i, d_i>=N_i(B_i-e_i).                     (4)

For actual laws, split the prescribed own law into finite deadlines and its
Never atom: U_i<=(1-N_i)B_i+N_i e_i. For virtual words, (4) starts at
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

Section 5 proves that this selected property, on the closed domain (3),
produces actual absorbing profiles with vanishing complete terminal debt.

## 3. The passive bound controls bad triples

Fix v in D with min v<=0. AllContinue is not bad. If player0 is active
in a proper root, its output equals Q_0<=0 by its participant caps. A
singleton active set cannot be bad because its owner's Quit reward is zero.
Pair13 cannot be bad because Q_1<0, and pair23 cannot be bad because Q_3<0.
Thus only pair12 and triple123 require consideration.

Use positive odds x_i=q_i/(1-q_i) on the active set. For pair12 the active
indifference equations are

    v_1=c_12 x_2, v_2=c_21 x_1.                     (5)

For triple123 they are v_i=phi_i(x), with

    phi_1=c_12 x_2+c_13 x_3+b_1 x_2 x_3,
    phi_2=c_21 x_1+c_23 x_3+b_2 x_1 x_3,
    phi_3=c_31 x_1+c_32 x_2+b_3 x_1 x_2.            (6)

These equations follow by dividing Q_i-P_i=H_i v_i by H_i>0. If W=0,
the strict positivity of both expressions for v_2 excludes (5) and (6).
Every Nash root is then good, proving (V). Hence suppose W>0.

At every positive triple candidate, (6) and v_2<=W imply x_1<X. At a
bad candidate Q_3>0 is equivalent to

    J_31 x_1-(-J_32-T_3 x_1)x_2>0.

Its denominator -J_32-T_3 x_1 is positive by G>0. Since
-c_32-b_3 x_1>0, substitution into the last equation of (6) gives

    v_3>x_1[alpha+(b_3 J_31-c_31 T_3)x_1]
                /(-J_32-T_3 x_1)>=0.               (7)

The affine numerator is nonnegative on [0,X] by its two endpoint bounds in
(Q0). The first inequality is strict even if that numerator vanishes.
Thus a bad triple forces v_3>0. At any positive triple candidate at these
same v_2<=W and v_3>0, whether or not it is bad,

    0<x_1<X, 0<x_2<c_31 x_1/(-c_32-b_3 x_1)<Y.      (8)

Under BLOCK, pair12 cannot be bad because J_12<=0. The numerator of Q_1
at a bad triple would be

    J_12 x_2+(J_13+T_1 x_2)x_3<=0,

by (8) and BLOCK. This contradicts Q_1>0. Hence no bad root exists in this
branch, proving (V). In the rest of this section assume INDEX.

At a positive triple candidate with v_3>0, set

    A=c_12+b_1 x_3, B'=-c_13-b_1 x_2, C=c_21+b_2 x_3,
    D'=c_23+b_2 x_1, E'=c_31+b_3 x_2, F'=-c_32-b_3 x_1.

Then

    Dphi=[[0,A,-B'],[C,0,D'],[E',-F',0]],
    det Dphi=A D'E'+B'C F'>=Delta>0.                (9)

Indeed B'>=B_*, C>=c_21, F'>=F, D'<=c_23+b_2 X and E'<=c_31+b_3 Y.
If c_12<0, the first product is at least
c_12(c_23+b_2 X)(c_31+b_3 Y); if c_12>=0 it is nonnegative.

There is at most one bad triple at a fixed v. None exists when v_3<=0 by
(7). Otherwise solve the second and third equations of (6):

    x_2=(c_31 x_1-v_3)/(-c_32-b_3 x_1),
    x_3=(v_2-c_21 x_1)/(c_23+b_2 x_1).               (10)

The positive feasible domain of x_1 is an interval inside (0,X). Along it,
x_2'=E'/F', x_3'=-C/D', and

    d phi_1/dx_1=det Dphi/(D'F')>0.                 (11)

All positive candidates on that interval obey (8), so (9) applies throughout.
Equation phi_1=v_1 has at most one solution.

## 4. Index selection, including ties and boundary inputs

A bad pair12 requires J_12,J_21>0, hence c_12>=0 by INDEX. If c_12>0,
(5) has at most one positive solution and its active Jacobian is
[[0,c_12],[c_21,0]], of determinant -c_12 c_21<0. If c_12=0, it has
no candidate at v_1!=0.

Here is the index convention and the entire degree argument. Put

    g_i(q,v)=Q_i-P_i-H_i v_i,
    T(q)_i=clip_[0,1](q_i+g_i(q,v)).

Fixed points of T are exactly the one-stage Nash roots. On the ambient box
(-1,2)^4, T and its straight-line homotopy to the cube center take values
in [0,1]^4. Thus degree(Id-T,(-1,2)^4,0)=+1.
At a strict inactive coordinate the corresponding row of Id-T is an identity
row. At an active coordinate it is the negative root-gap Jacobian. At an
indifference point the latter is obtained from Dphi by multiplying rows by
positive H_i and columns by positive derivatives dx_j/dq_j. Therefore a
regular root with k active owners and strict inactive comparisons has index
sign((-1)^k det Dphi). Every bad triple has index -1 by (9). Every bad pair
with c_12>0 has index -1 when its inactive comparisons are strict.

Inactive0 is automatically strict at every bad root: its Continue payoff is
its strictly positive current output, while Q_0<=0. Thus every bad triple
is already regular with no inactive tie. For pairs, make arbitrarily small
perturbations of v_1 and v_3 within D while leaving v_0,v_2 fixed and
preserving min v<0. If c_12=0, choose v_1!=0. If c_12>0, the unique
candidate is independent of v_3; avoid its single inactive3 tie, whose
coefficient in v_3 is -H_3!=0. The mixed singleton signs in (R) ensure
that both permitted coordinate intervals are nondegenerate, so these generic
points are dense even at box boundary points. If no bad pair is possible,
no perturbation is required.

At such a generic input, if all Nash roots were bad, there would be at most
two roots, both isolated and of index -1. Degree additivity contradicts
total degree +1. Hence a good root exists. Taking a compact convergent
subsequence of roots removes the perturbation because the Nash and good
conditions are closed. If min v=0, AllContinue is itself a good Nash root.
This proves (V), including equality cases in the raw inequalities and
one-sided or degenerate passive intervals for players0 and2.

## 5. Closed-domain selection produces vanishing actual debt

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
E_i=O(epsilon^2). Formula (1) then bounds both core payoffs and core cap
errors by O(epsilon) over the whole word. Positive outsiders retain their
Continue buffers for small T; their cap and payoff updates coincide.
Survival tends to exp(-T)<1, and choose T so this limit exceeds 1-eta.
This proves the local assertion in the kernel case, including |S_0|=1.

Otherwise zero is outside the convex hull of the columns of
Gamma_{S_0 S_0}. Strict separation gives a signed row w with
w Gamma_{S_0 S_0} strictly positive in every coordinate. For all sufficiently
small S_0-supported hazards,

    w E_{S_0}(q)>=gamma sum_i q_i>=0                 (12)

for some gamma>0. Choose a positive delta below the requested hazard bound,
below the bound for (12), and below eta/16. By the preceding graph argument
there is rho>0 such that every good root at an input within rho of v in D
with min<=0 is S_0-supported and has each hazard below delta. Shrink rho
so every coordinate positive at v remains positive within rho of v.
Take M>=1 bounding all native rewards and the relevant domain coordinates,
and fix, before choosing any seed,

    c_0=min(eta/4,rho/(8M),1/4)>0.                   (13)

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

    B=U, min U<=0, w U_{S_0}>=h w z_{S_0}.           (14)

The empty word is feasible. Coherence (4) forces U=e in D at each feasible
point. Every word also satisfies the displacement bound

    ||U-v||_infinity<=||z-v||_infinity+2M(1-h).        (15)

If a minimizing h satisfies h>1-c_0, (13)--(15) place its payoff within
rho/2 of v. Property (V) supplies a good root there, which is S_0-supported
and has hazards below delta. A nonzero such root preserves zero debt and
the nonpositive minimum. It preserves the original weighted inequality in
(14) by (12). Moreover,

    h(q)h>(1-4delta)(1-c_0)>1-eta,

so the prefixed point remains inside the survival constraint and has smaller
h, a contradiction. Therefore AllContinue is the only good root there,
which forces U>=0. Its zero set T is nonempty, while (14) and w z_{S_0}>0
show U_{S_0} is not identically zero. Thus T is a proper subset of S_0.

Apply induction at U, using hazard bound delta and a survival budget eta_1
small enough that h(1-eta_1)>1-eta. Its words are T-supported and therefore
S_0-supported. Inequality (12) preserves the ORIGINAL row w inequality
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
assertion. At every recursive minimum, (4) supplies membership in the same
closed passive domain; no unsupported interior or actual-tail claim enters.

Now take the compact closure of all actual finite-dimensional data
(U,B,e,N). Finite prefixes act continuously and preserve this closure.
Moving an owner's Never mass to one finite date makes that owner quit surely
and hence gives an absorbing profile. Its own cap is unchanged, since its
opponents are unchanged. Four prescribed payoffs and three other cap values
each change by at most twice the reward bound times that moved mass.
Moving a smallest original Never mass gives, also on the closure,

    A_Z<=sum_i(B_i-U_i)+14M nu^(1/4).                (16)

Minimize nu over B=U,min U<=0 in this closure. AllNever makes the set
nonempty: its native payoff, cap and Never response are all zero. If A_Z>0,
(16) implies that the minimum m is positive. At a minimizer (4) gives
U=B=e=v in D. Every nonzero good root contradicts minimality: a sure root
has zero debt and nu'=0, contradicting (16); a proper good root keeps
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

## 6. Numerical specialization and the remaining opposed-pair strip

Keep only the following core recipient entries fixed, with arbitrary real a
and p>=0:

| Coalition | Z_1 | Z_2 | Z_3 |
|---|---:|---:|---:|
| 1 | 0 | -2 | -2 |
| 2 | 1/2 | 0 | 1 |
| 3 | -3 | -1 | 0 |
| 12 | a | p | -6 |
| 13 | -100 | -1 | 10 |
| 23 | 9 | 3 | -100 |
| 123 | 11 | 2 | 1 |

Require Z_0(A)<=0 when 0 belongs to A and Z_2(A)<=10 when 2 does not
belong to A. All other native coordinates are arbitrary finite. In particular
all row1 and row3 entries involving0, all row2 participant entries involving0,
and all seven passive row0 entries are unrestricted.

Here c_12=a-1/2, (c_21,c_23,c_31,c_13,c_32)=(p+2,4,12,-97,-101),
b=(2,3,7), (J_13,J_32,J_31,T_1,T_3)=(-100,-100,10,11,1), and W<=10.
For W>0, X<=5, F>=66, G>=95, Y<=10/11, alpha=190, and the slope
in its affine endpoint test is58. Also B_*>95. BLOCK holds whenever a<=0.
INDEX holds whenever a>=1/2, or whenever a>=0 and p=0: in the latter
case the bad pair is impossible, and in both cases

    Delta>95*2*66-(1/2)*19*19=24719/2>0.

The W=0 case is already covered without these calculations. Consequently
this whole numerical class has UE whenever

    p>=0 and (a<=0 OR a>=1/2 OR p=0).                (17)

In particular p=0 allows EVERY real a and every unlisted coordinate under
the two raw caps. In the usual canonical parameters a=-K,
eta=Z_2(02)-2, R=Z_0(23), t=Z_3(023), the entire p=0 cylinder is closed
for all real K,eta,R,t, and arbitrary passive Z_0(123).
Within p>=0, only 0<a<1/2,p>0 lies outside this producer. In that strip,
a positive pair12 has c_12<0<c_21 and index +1; Section 7 gives an exact
control. This is a boundary of the stated producer, not a remaining-case
classification of arbitrary Fin4 games.

## 7. A strict example and exact architecture boundaries

The following table lists all sixty native rewards. Set each original own
level kappa_i=1, so original coalition rewards are 1+Z_i(A).

| Coalition | Z_0 | Z_1 | Z_2 | Z_3 |
|---|---:|---:|---:|---:|
| 0 | 0 | 2 | 2 | -1 |
| 1 | 3 | 0 | -2 | -2 |
| 2 | -1 | 1/2 | 0 | 1 |
| 3 | 3 | -3 | -1 | 0 |
| 01 | -1/100 | -1 | -10 | -12 |
| 02 | -1/10 | 5 | -1 | -219/29 |
| 03 | -20 | 3 | -5 | 1 |
| 12 | -12 | 1/4 | -1/10000 | -6 |
| 13 | 2 | -100 | -1 | 10 |
| 23 | -25 | 9 | 3 | -100 |
| 012 | -20 | 6 | -100 | 11 |
| 013 | -20 | 8 | 10 | -10 |
| 023 | -20 | -8 | -100 | 987 |
| 123 | -1000 | 11 | 2 | 1 |
| 0123 | -5 | -9 | -100 | 21/2 |

This table satisfies the abstract INDEX criterion strictly. Indeed W=10,
c_21=19999/10000>19/10, c_12=-1/4, and J_21<0 robustly excludes a
bad pair12. The remaining core quantities are as in Section 6. The bounds

    X<6, F>59, G>94, Y<72/59<2, B_*>93,
    c_23+b_2 X<22, c_31+b_3 Y<26,
    Delta>93*(19/10)*59-(1/4)*22*26>0

verify all quantitative inequalities directly. The alpha tests have constant
190 and slope58. All nontrivial row0 participant caps are strict; the core
signs, b_i>0, T_3>0 and mixed singleton signs are strict as well. Continuity
therefore gives an open neighborhood in the original sixty reward
coordinates, with own levels still positive, to which the same theorem
applies. No maximal neighborhood or quantitative radius is asserted.

Despite this UE conclusion, every open continuation neighborhood of zero
fails every one-step marked-set Nash invariant. Here that invariant would
say: at any Nash root, a nonpositive minimum over a fixed nonempty marked
set remains nonpositive over that set. We give exact witnesses for all
fifteen marked choices.

For a proper nonempty marked set C, use a safe-positive edge j->i entering C,
where j is outside C, i is inside C, Gamma_ij>0 and Z_i({i,j})<=Gamma_ij.
The literal table has edges

    0->1, 1->0, 0->2, 2->1, 2->3, 3->0,

which form a strongly connected directed graph. Every proper nonempty C
therefore has such an entering edge. Put q_j=epsilon and all other hazards
zero, set v_j=v_i=0, and set v_k=c_k epsilon for other owners, where
c_k>1+|Gamma_kj|+|Z_k({k,j})|. For sufficiently small positive epsilon this is
a whole-game Nash root: j is indifferent, i's Continue value is
Gamma_ij epsilon>=Z_i({i,j}) epsilon, and every other quiet owner's Continue
comparison is strict. Every C output is strictly positive, while min_C v=0.
All inputs tend to zero.

For C=I take

    q=(0,11epsilon,epsilon,epsilon/800), v_0=-epsilon,
    v_i=(Q_i-P_i)/H_i for i=1,2,3.                  (18)

These are exact active indifference equations. Expanding the finite
coalition expectations from the displayed table gives

    Q_1=(1/8)epsilon+O(epsilon^2),
    Q_2=(53/20000)epsilon+O(epsilon^2),
    Q_3=10epsilon+O(epsilon^2),
    F_0=(24803/800)epsilon+O(epsilon^2),
    Q_0=-(47/200)epsilon+O(epsilon^2).               (19)

Every leading margin has the required strict sign. The remainders are
literal finite polynomials, so for every sufficiently small positive epsilon
all active outputs are positive, quiet0 strictly prefers Continue, v_0<0,
and every output is positive. The active inputs in (18) tend to zero since
H_i tends to1. One can obtain an explicit epsilon bound by dividing half
each leading margin by the sum of absolute higher coefficients; if that sum
is zero, it imposes no restriction. Thus (18)--(19) are exact small-parameter
witnesses, not numerical evidence.

Every passive interval of this table contains zero in its interior. These
crossings therefore occur within the closed passive box itself when epsilon
is small, and within every open neighborhood of zero. Positive recipient
scaling preserves them. They exclude universal one-step marked invariance,
while the theorem uses only selected good roots. The continuation witnesses
are virtual; actual independent realizability is not asserted.

For a positive-index boundary control, change just the table entry J_21 from
-1/10000 to1. With

    q=(0,1/10,1/10,0), v=(3,-1/36,1/3,10),

the exact Nash output is

    F=(249/100,1/40,1/10,159/20)>0.

The quiet Quit offers are Q_0=-2099/10000 and Q_3=-809/100, so both
inactive comparisons are strict. The active joining product is
(-1/4)*3=-3/4, hence this pair has ambient index +1. The input has a
negative coordinate. This demonstrates why the pair condition in INDEX
cannot simply be dropped; it does not refute selected return by some other
root, and it is not a counterexample to UE.

## 8. Existing interfaces, coverage scope, and formalization handoff

Negative-index selection itself is already implemented by
`exists_exactRoot_singletonSublevel_of_badRoot_negative_derivatives` in
`UniformEquilibrium/Quitting/Root/NegativeBadRootSelectedReturn.lean`, using
`Math.Topology.not_all_fixedPoints_have_negative_det_finite` in
`MathUE/Topology/AmbientDegreeNegativeFixedPointObstruction.lean`.
The new raw calculation is the passive bound (7)--(9), its uniqueness
argument, and its use with the closed-domain low-or-sure consumer in Section 5.

The previously implemented joining-attractive source
`exists_exactRoot_singletonSublevel_of_joiningAttractive_generic_tail` in
`UniformEquilibrium/Quitting/Classification/JoiningAttractiveCoreGenericReturn.lean`
requires positive core joining gaps. The signed-pair source in
`UniformEquilibrium/Quitting/Classification/SignedPairCoreBadRoot.lean`
requires a premium core of cardinality2. The source in
`UniformEquilibrium/Quitting/Classification/MixedSignTripleCoreSelectedReturn.lean`
requires positive reciprocal joining products. The displayed example has
premium core123, c_12=-1/4, and reciprocal products
c_13*c_31=-97*12 and c_23*c_32=4*(-101). These raw source hypotheses fail
under every relabeling. The one-step invariant failure in Section 7 concerns
the invariant itself, rather than merely a sufficient raw sign test.

A separate finite coverage audit of this literal table compares the other
accepted raw producers, including stationary and sure-first profiles,
withdrawal child lifts, return/reset roles and weighted criteria. Such
exclusions establish separation from those named producer families; they do
not prove an unrestricted behavioral exploitability gap. They are not
premises or steps in the present UE proof.

The exact cap update (1) corresponds to
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The fixed-target endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The existing boxed selected-sublevel consumer
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn` in
`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`
has a low-output premise; the present proof explicitly handles the alternative
of a sure owner and supplies its own actual closed-domain adapter.

For formalization, retain (U,B,e,N), prove coherence (4), implement the
closed-domain selected local lemma with exact solo seeds, and then the actual
minimum/repair argument. The raw algebra, pair tie removal and ambient degree
calculation supply (V). No theorem in this packet is claimed Lean checked,
and no new Lean command is part of this mathematical result.
