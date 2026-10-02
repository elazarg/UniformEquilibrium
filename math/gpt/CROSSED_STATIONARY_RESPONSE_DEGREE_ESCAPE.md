# Half-ceiling crossed-response degree escape for quitting games

## Status and contribution

This note gives an ordinary mathematical proof of a raw-table sufficient
criterion for four-player uniform equilibrium. Its strict case produces an
exact stationary equilibrium against every behavioral deviation. The proof
is not Lean-checked. The accompanying standard-library Python script verifies
all finite arithmetic in the example and its comparisons, not the general
topological theorem.

The construction swaps two stationary residuals in an auxiliary fixed-point
map and clips their hazards at **one half**, not at one. Explicit raw-table
inequalities exclude every artificial ceiling root. Consequently every
nonzero fixed point is an equilibrium of the original, unrestricted game.
The swap changes the all-Continue LCP index from +1 to -1 in the example;
the global fixed-point degree remains +1.

This is not a response-invariant quotient: all four hazards remain independent
coordinates, the two selected hazards need not agree, and no residual identity
between players is imposed. The example has no nontrivial response-invariant
partition, fails every proper-child raw domination test in the supplied
frontier, and has no pure equilibrium. The criterion holds on a full
sixty-dimensional reward neighborhood. It does not settle all remaining
four-player tables or the general UE conjecture.

## 1. Game, evaluations, and stationary residuals

Let I={0,1,2,3}. For every nonempty coalition S, specify r(S) in R^4.
Live play and Never pay zero. Players use independent private behavioral
randomization, and every complete unilateral behavioral replacement is
allowed. Before absorption the only history is all-Continue. Thus each
strategy is equivalently a private law on N union {Never}, and the first
finite minimum determines the entire quitting coalition. There is no public
correlation or observation of other players' future private clocks.

Write

    s_i = r_i({i}),       Gamma_ij = r_i({j}) - s_i.

Rows are payoff recipients; columns are singleton quitters. Gamma has zero
diagonal. Matrix inequalities below are entrywise.

For a stationary hazard vector q, let

    alpha_i(q) = product_{j!=i}(1-q_j),
    pi_{-i,q}(T) = product_{j in T}q_j
                   product_{j not in T, j!=i}(1-q_j),
    Q_i(q) = sum_{T subset I\{i}} pi_{-i,q}(T) r_i(T union {i}),
    H_i(q) = sum_{empty!=T subset I\{i}} pi_{-i,q}(T) r_i(T),
    Delta_i(q) = (1-alpha_i(q))Q_i(q) - H_i(q).             (1)

These polynomial formulas extend to all of R^4. Delta_i is independent of
q_i. No empty-coalition terminal reward is introduced. Direct expansion gives

    Delta(q) = -Gamma q + O(||q||^2)                       (2)

on an ambient real neighborhood of zero.

For q!=0 in the strategy cube put

    C(q)=product_i(1-q_i),     a(q)=1-C(q),
    R_i(q)=q_i Q_i(q)+(1-q_i)H_i(q),
    v_i(q)=R_i(q)/a(q).                                   (3)

Repeating q has actual terminal payoff v: its Bellman recursion is
v=R+Cv and its geometric surviving remainder tends to zero. Since
C=(1-q_i)alpha_i, exact algebra gives

    a(q)[Q_i-H_i-alpha_i v_i(q)] = Delta_i(q).             (4)

Accordingly, the stationary Nash–Bellman conditions are

    q_i=0       ==> Delta_i<=0,
    0<q_i<1     ==> Delta_i=0,
    q_i=1       ==> Delta_i>=0.                           (5)

These finite endpoint conditions require a separate Never check for a
negative sole owner. Our strict construction has at least three positive
hazards, so that exception never occurs.

For an actual profile sigma, let U_i be its terminal payoff, B_i the supremum
over every complete i-replacement, and E=max_i(B_i-U_i). Under the repository
stage convention, absorption at date t has H-stage evaluation weight
max(H-t-1,0)/H. A uniform-equilibrium payoff is one fixed vector v such that,
for every positive error, one profile delivers v and has at most that regret
for every sufficiently large horizon. All such expectations and suprema
use the full behavioral class, including Never.

## 2. A finite raw-table theorem

Distinguish players 0 and 1 and put J={2,3}. For i in {0,1}, let j=1-i.
Define the **lower ranking condition**

    max_{empty!=T subset J} r_i(T)
       <= min_{T subset J} r_i(T union {i}).              (L)

This means twelve linear comparisons per selected recipient. The minimum
includes T=empty, hence includes s_i.

Next define f_i(x,y) by evaluating Delta_i at

    q_j=1/2,       q_2=x,       q_3=y.

The value of q_i is immaterial. The polynomial f_i has degree at most two
separately in x and y. Write its unique tensor Bernstein expansion

    f_i(x,y) = sum_{a,b=0}^2 c^i_ab B_a(x) B_b(y),
    B_0(x)=(1-x)^2,   B_1(x)=2x(1-x),   B_2(x)=x^2.

The **half-ceiling condition** is

    c^i_ab <= 0       for every a,b in {0,1,2}, i=0,1.    (B)

Each coefficient is a rational linear combination of the fifteen raw
rewards in that recipient's row. This is eighteen more finite linear tests,
not an assumed strategic root. To compute them without symbolic algebra,
evaluate f_i at the nine points in {0,1/2,1}^2 and apply in each variable

    c_0=f(0),   c_2=f(1),
    c_1=2f(1/2)-(f(0)+f(1))/2.                           (6)

The Bernstein factors are nonnegative and their sum is one. Thus (B) gives
f_i<=0 everywhere on the full outsider-hazard square. Strictly negative
coefficients give a strict negative margin everywhere. Coefficientwise
nonpositivity is sufficient, not necessary, for that polynomial sign.

### Theorem 1: weak inequalities, stationary approximants

Suppose

    det Gamma > 0,           Gamma^{-1} >= 0,             (M)

and (L),(B) hold for both selected recipients. Then the original game has a
fixed uniform-equilibrium payoff. It admits stationary profiles with full
terminal regret tending to zero, and a subsequence delivers that fixed target
uniformly over all sufficiently long horizons. All singleton signs are
allowed. Neither a punishment plan nor an equilibrium is an input.

### Theorem 2: strict inequalities, exact stationary equilibrium

Suppose Gamma^{-1}>0, both comparisons in (L) are strict, and all eighteen
coefficients in (B) are strictly negative, while det Gamma>0. Then there is
an exact stationary terminal equilibrium q with

    0<q_0<1/2,        0<q_1<1/2,        q_2+q_3>0.        (7)

The same profile is uniform at its actual terminal payoff. Every complete
response cap equals its prescribed payoff, including signed Never values.

The half ceilings restrict only the auxiliary fixed-point map. **They do
not restrict the deviator's actions, hazards, timing menu, or laws.** The
proof obtains strict interiority at those ceilings and then checks the
original Quit and Continue endpoints.

### Reciprocity is derived, not an extra hypothesis

Condition (L) implies Gamma_i2,Gamma_i3<=0 for i=0,1. If also Gamma_ij<=0,
the entire row i of Gamma would be nonpositive. Multiplication by the
nonnegative inverse would give (Gamma Gamma^{-1})_ii<=0, contradicting one.
Hence the raw hypotheses themselves give

    Gamma_01>0,             Gamma_10>0.                   (8)

## 3. The more general guarded-degree statement

The strict proof actually needs only the following polynomial face signs:

    q_j=0, (q_2,q_3)!=(0,0) ==> Delta_i(q)>0,
    q_j=1/2                ==> Delta_i(q)<0,    i=0,1,    (G)

for all outsider hazards in [0,1]^2, together with (8) and an LCP condition
specified below. Strict (L) implies the first guard. Indeed, with q_j=0,
put beta=(1-q_2)(1-q_3), ell=min_T r_i(T+i), and b=max_{T!=empty}r_i(T).
Then Q_i>=ell, H_i<=(1-beta)b, and

    Delta_i >= (1-beta)(ell-b)>0

when the outsiders have positive joint absorption. Strict (B) implies the
second guard by the Bernstein expansion.

Let P swap coordinates 0 and 1, fixing 2 and 3, and put A=P Gamma. For an
R0 matrix A, let kappa(A) be the integer degree of the whole-space min map
x -> min(x,Ax) around its sole zero. R0 means that x>=0, Ax>=0 and
x_i(Ax)_i=0 force x=0.

**Theorem 3.** Guards (G), the reciprocal signs (8), and

    A is R0,               kappa(A)!=1                  (9)

produce the equilibrium in (7). The nonzero fixed-point set of the crossed
map below has total degree 1-kappa(A). Theorem 2 is its case kappa(A)=-1.

All of (G) is a finite real-algebraic condition on the reward table: it
quantifies over two bounded real variables in explicit polynomial
inequalities. It is a raw sign test, not a supplied-root premise. Conditions
(L),(B) give the simpler finite linear sufficient test.

## 4. The crossed map and complete exclusion of artificial roots

Let R=[0,1/2]^2 x [0,1]^2. Extend (1) polynomially to the whole ambient
space and define

    T(q)=clip_R(q+P Delta(q)),       Z(q)=q-T(q).          (10)

Thus coordinate 0 is driven by Delta_1, and coordinate 1 by Delta_0.
Coordinates 2 and 3 retain their own residuals. Every fixed point lies in R.
The map is an auxiliary topological object, not a behavioral response
transition or a payoff-preserving relabeling of players.

### 4.1 Nonzero outsider hazards force pair interiority

Suppose q is a fixed point and q_2+q_3>0. If q_0=0, its crossed fixed-point
condition is Delta_1<=0. But the lower guard for recipient 1 gives
Delta_1>0. If q_0=1/2, its crossed condition is Delta_1>=0, whereas the
upper guard gives Delta_1<0. Hence 0<q_0<1/2. The same proof gives
0<q_1<1/2. Their fixed-point equations now imply

    Delta_0=Delta_1=0.                                  (11)

Thus both ORIGINAL individual endpoint conditions hold. Coordinates 2,3
satisfy their original conditions directly from (10), including sure-quit
faces and indifferent endpoints. No joint deviation of the pair is used.

### 4.2 The outsider-zero face contains only the origin

Set q_2=q_3=0. For recipient i in the pair and partner hazard t,

    Delta_i(t)=t[(1-t)(s_i-r_i({j}))
                         +t(r_i({i,j})-r_i({j}))].       (12)

The bracket is affine in t. At t=0 it is strictly negative by (8). At
 t=1/2 it is strictly negative by the upper guard. It is therefore negative
for every 0<=t<=1/2, so Delta_i(t)<0 whenever 0<t<=1/2.

If q_0>0, equation (12) makes Delta_1<0. But a positive crossed fixed-point
coordinate q_0 requires Delta_1=0 below its ceiling or Delta_1>=0 at the
ceiling. This is impossible. Similarly q_1=0. Thus this face has only q=0.

Every nonzero fixed point of (10) consequently satisfies (7) and all the
original conditions (5). All possible fake lower-face, half-ceiling and
outsider-zero fixed points have been accounted for.

## 5. Global degree +1 and local degree -1

We use the classical integer Brouwer-degree properties: normalization,
homotopy invariance, additivity, excision, stability under a boundary-small
perturbation, and local sign of a nonsingular Jacobian. The LCP convention
is the componentwise minimum convention of Gowda [1]. The game-specific
construction and its fixed-point fidelity are proved here.

### 5.1 Global degree

Take Omega=(-1,2)^4. The whole image of T belongs to R, a compact subset
of Omega. Homotope T to the center (1/4,1/4,1/2,1/2) of R. Every image
remains inside Omega, so the displacement has no zero on its boundary.
Normalization and homotopy invariance give

    deg(Z,Omega,0)=1.                                   (13)

The expanded ambient box is essential. A strategy-interior domain would
omit legitimate boundary solutions of coordinates 2 and 3.

### 5.2 Local comparison

Equation (2) gives P Delta(q)=-Aq+O(||q||^2). Near zero the upper clips
are inactive, including at negative ambient coordinates; the lower clips
are retained. Consequently

    Z(q)=min(q,-P Delta(q))
        =min(q,Aq+O(||q||^2)).                          (14)

If A is R0, f_0(q)=min(q,Aq) has no nonzero zero. Positive homogeneity
and compactness of the sup-norm unit sphere give c_A>0 with

    ||f_0(q)||_infinity >= c_A ||q||_infinity.

Minimum is 1-Lipschitz in its second argument. Thus for some finite K,
||Z(q)-f_0(q)||<=K||q||^2 near zero. On a sufficiently small punctured
closed box, K||q||<c_A. This proves that zero is isolated, and the straight
homotopy between Z and f_0 has no zero on the small boundary. Therefore

    ind(Z,0)=kappa(A).                                 (15)

Subtracting (15) from (13), excision and additivity give a nonzero root
set of degree 1-kappa(A). If this is nonzero, existence of a zero and
Section 4 produce (7). This proves Theorem 3 without isolated or regular
absorbing roots being assumed.

### 5.3 Computing the crossed degree from the strict inverse

Under Theorem 2,

    A^{-1}=Gamma^{-1}P>0,       det A=-det Gamma<0.

A is R0. Indeed, if x,w>=0, w=Ax and x_iw_i=0, then w!=0 would imply
x=A^{-1}w>0, forcing w=0. If w=0, invertibility gives x=0.

At right-hand side -1, any LCP solution satisfies

    x=A^{-1}(1+w)>=A^{-1}1>0.

Complementarity forces w=0. Thus there is exactly one solution,
x=A^{-1}1. In its neighborhood, the min map selects Ax-1 in every
coordinate; its local degree is sign det A=-1.

For completeness, R0 makes all LCP solutions uniformly bounded when the
right-hand side ranges over a bounded set. Otherwise normalize an unbounded
sequence x_n by its norm, pass to a nonzero nonnegative limit, and divide
slack inequalities and complementarity by the appropriate powers of that
norm. The result is a nonzero homogeneous complementary vector, contradiction.
A right-hand-side homotopy consequently has all its zeros in one large
box. Homotopy invariance and excision identify its total degree with that
of min(x,Ax). Therefore

    kappa(A)=-1,       deg(nonzero crossed roots)=2.      (16)

This is a set degree, not an assertion that there are exactly two roots.
Together with Section 4 it proves the strategic root assertion of Theorem 2.

## 6. Unrestricted behavioral caps, uniformity, and finite laws

At the produced q, each player's opponent survival alpha_i is strictly
less than one: the pair contains two distinct positive hazards. Hence,
against these stationary opponents, a pure quit at date t pays

    H_i(1-alpha_i^t)/(1-alpha_i)+alpha_i^t Q_i,

and Never pays H_i/(1-alpha_i). Every complete behavioral replacement is
a mixture of these pure stopping laws. Its full cap is therefore

    B_i=max(Q_i,H_i/(1-alpha_i)).                        (17)

Equations (4)-(5) bound both terms by v_i, while prescribed play attains
v_i. Thus B_i=U_i=v_i. This includes the actual signed Never payoff, not
zero substituted for it.

Let |r_i(S)|<=M. Under any i-deviation, absorption occurs no later than
the first opponent quit date L_i, whose expected value plus one is
1/(1-alpha_i). On an absorbed path, the absolute difference between
terminal and H-stage average payoff is at most M(L_i+1)/H. Uniformly
over every complete response, including prescribed play,

    |U_i^H-U_i| <= M/[H(1-alpha_i)].                     (18)

Thus horizon regret is at most 2M/[H(1-alpha_i)]. The same fixed q is
uniform at v. No punishment or singleton-sign hypothesis is needed.

There is also a finite-law construction. Keep K dates of the independent
geometric clocks and send each remaining tail to Never. For each player,

    p_i(t)=q_i(1-q_i)^t  (0<=t<K),
    p_i(Never)=(1-q_i)^K.

Let rho=max_i alpha_i<1. The censored prescribed payoff is

    U_i^K=(1-C^K)v_i.

Couple unchanged and censored opponent clocks separately under every fixed
complete i-response. Different first outcomes require that all opponents
survive K dates, an event of probability alpha_i^K. Therefore

    B_i^K<=v_i+2M alpha_i^K,
    E(p^K)<=3M rho^K,       ||U^K-v||_infinity<=M C^K.    (19)

This is a bound on the unrestricted cap, including every after-support
deadline and Never. The censoring does not restrict deviations.

For rational tables passing the strict tests, a real-algebraic root exists
because the finite root system is semialgebraic. An alternative accuracy-only
producer enumerates rational hazards with 0<q_0,q_1<1/2 and computes (17)
exactly, accepting full regret below the requested tolerance. Near the root,
all denominators remain positive and the cap/payoff formulas are continuous,
so rational density proves termination. Subsequent independent censoring
uses (19), with the small initial regret added. This is not a complexity
bound or an oracle for a previously specified real target.

## 7. Weak inverse and weak guards: proof of Theorem 1

### 7.1 Strictifying a nonnegative inverse

For an invertible n-by-n Gamma, n>=3, with B=Gamma^{-1}>=0, put
K=J_n-I_n and Gamma_e=Gamma-eK. For sufficiently small e>0,

    Gamma_e^{-1}=B+eBKB+e^2BKBKB+... >0.                 (20)

The series converges when e||BK||<1. Every term is nonnegative. Fix entry
(i,j). If B_ij>0 or (BKB)_ij>0, positivity follows. Otherwise

    (BKB)_ij=sum_{u!=v}B_iu B_vj=0

forces the nonempty supports of row i and column j of B to be the same
singleton {k}. There is B_uv>0 with u,v!=k: otherwise at least two rows
outside k would be supported only in column k, contradicting invertibility.
The product B_ik K_ku B_uv K_vk B_kj is a positive contribution to the
second-order term. This proves (20). The diagonal of Gamma is unchanged,
and the determinant keeps its sign by continuity and nonsingularity along
the sufficiently short perturbation segment.

### 7.2 A literal reward perturbation that also strictifies half ceilings

Preserve every own singleton and Never. Make precisely these changes:

- Subtract e from every off-own singleton reward.
- In each of rows i=0,1, subtract e from the reward at {2,3}.
- In each of those rows subtract 3e from every coalition containing both
  0 and 1.
- Leave all other entries unchanged.

The reward distance is at most 3e, and its singleton matrix is Gamma_e.
Every external-only reward in (L) decreased by e and every own-plus-external
reward there stayed fixed. Thus its lower ranking gap increases by e.

Fix i, let beta=(1-q_2)(1-q_3), and set partner hazard to 1/2. The exact
changes in the one-stage quantities are

    delta Q_i=-3e/2,       delta H_i=-e/2,
    delta Delta_i=-e+(3e/4)beta <= -e/4.                 (21)

The change in H consists of external-only absorption of weight
(1-beta)/2 and partner-only absorption of weight beta/2. No empty terminal
payoff has been altered.

Moreover the tensor Bernstein coefficients of beta are
(1-a/2)(1-b/2), lying in [0,1]. Equation (21) strictly decreases every
coefficient by at least e/4. Thus even coefficientwise weak (B) becomes
strict (B). Reciprocal positivity follows either from (8) and continuity
or directly from the perturbed lower test and inverse positivity.

For all sufficiently small e, the perturbed table meets Theorem 2 and
has an exact stationary equilibrium q^e with contracting deleted clocks.
All required perturbations are finite raw-coordinate changes, not strategic
translations of the Never payoff.

### 7.3 Fixed-target return to the original game

For two tables at reward distance delta, every prescribed or deviated
profile has exactly the same terminal outcome law. Its expected payoff
changes by at most delta. Taking the complete response supremum and then
subtracting gives

    |E_r(p)-E_{r'}(p)|<=2delta.                          (22)

Use the same q^e in the original game. Its full regret is at most 6e.
Its original prescribed payoff lies in the fixed bounded reward cube.
Choose e_n decreasing to zero and a subsequence of those payoff vectors
converging to one v.

For each member of the subsequence, every alpha_i<1. Estimate (18), now
using the ORIGINAL reward bound, still holds uniformly over every deviation;
it does not require that q^e be Nash at that table. The finite-horizon
regret is at most

    6e + max_i 2M/[H(1-alpha_i(q^e))].

Given a final accuracy, first choose one subsequence member with small
terminal regret and small target error, then choose H large enough for
this fixed member's contraction denominators. This proves exactly the UE
quantifier order, with stationary implementing profiles. It does not take
a limit of strategies or claim the limiting cap is continuous. This proves
Theorem 1.

The same proof permits weak polynomial guards directly, instead of weak
Bernstein signs: (21) makes those weak face inequalities strict as well.
The Bernstein test is simply a finite linear sufficient version.

## 8. Exact rational single-pivot example

Coalition strings denote sets, and columns are payoff recipients.

| Coalition | r_0 | r_1 | r_2 | r_3 |
|---|---:|---:|---:|---:|
| 0 | 1 | 3 | -1 | -1 |
| 1 | 4 | 0 | -1 | -1 |
| 01 | 5 | 4 | 178/7 | 2 |
| 2 | 0 | -1 | 0 | 3 |
| 02 | 7/3 | 0 | 8 | -1 |
| 12 | 1 | 83/91 | -2 | 2 |
| 012 | -5 | -6 | 199/7 | -4 |
| 3 | 0 | -1 | 3 | 0 |
| 03 | 2 | 0 | 4 | -4 |
| 13 | 1 | 1 | 3 | 6 |
| 013 | -5 | -6 | 7 | 0 |
| 23 | 0 | -1 | 3 | 0 |
| 023 | 2 | 0 | -5 | 7 |
| 123 | 1 | 1 | 8 | -3 |
| 0123 | -5 | -6 | -3 | -4 |

Here s=(1,0,0,0) and

    Gamma=[ 0  3 -1 -1
            3  0 -1 -1
           -1 -1  0  3
           -1 -1  3  0 ],

    Gamma^{-1}=(1/15)[2 7 3 3; 7 2 3 3; 3 3 2 7; 3 3 7 2],
    det Gamma=45.

The lower ranking gaps are both one. The two half-ceiling Bernstein arrays
(rows index the x basis, columns the y basis) are

    c^0=[ -1/2    -1/8     -2
          -1/12   -49/48   -2
          -11/6   -23/12   -2 ],

    c^1=[ -1/2      -1/8        -2
          -99/728   -1563/1456  -2
          -186/91   -184/91     -2 ].

Every entry is negative; the smallest absolute margin is 1/12.

The produced class contains the following exact rational root:

    q=(2/9,1/4,1/3,0),
    Delta(q)=(0,0,0,-271/1944),
    U(q)=B(q)=(3/2,5/13,53/21,15/22).                   (23)

In particular q_0!=q_1, both are below one half, and every payoff is strictly
above its own singleton. The joint survival is C=7/18. The four opponent
survivals are

    (1/2,14/27,7/12,7/18).

With M=199/7, (18)-(19) give

    horizon-H regret <= 4776/(35H),
    censored K-date regret <= (597/7)(7/12)^K.            (24)

These are exact rational identities and inequalities, checked by the script.
No floating-point equilibrium computation enters their verification.

### 8.1 Why the half ceiling is substantive

At a pure partner, joining gains one for EACH selected player:

    r_0(01)-r_0(1)=1,       r_1(01)-r_1(0)=1.

Thus Delta_i at partner hazard one and outsider hazards zero is positive,
not negative. These tables do not satisfy upper guards at a sure partner.

This distinction matters. With upper guards at ONE, a direct construction
can fix one selected player sure and the other Never, then use finite Nash
existence for the remaining two players. The lower guard makes the sure
owner's stationary endpoint acceptable, and the upper guard makes its
partner quiet. When the sure owner's singleton is nonnegative this is
already an exact behavioral equilibrium. That stronger face assumption
therefore does not establish a new UE class just by using a degree proof.

The half-ceiling hypotheses do not license that shortcut. The crossed map
instead proves an interior root below an auxiliary ceiling, even though the
original player can deviate to certain Quit. Its true endpoint indifference
is established in (11), not inferred from optimality under a hazard cap.

## 9. Separation from the named frontier tests

These comparisons concern the exact displayed table, not all earlier
sufficient classes or worldwide priority. They distinguish raw producers
from an existing stationary compiler once a root such as (23) is supplied.

### 9.1 Full degree +1 and no usable response-invariant quotient

The strict inverse proves Gamma is R0. The unique solution of
LCP(Gamma,-1) is Gamma^{-1}1>0 and has local degree sign det Gamma=+1.
Thus kappa(Gamma)=+1. In contrast, the crossed matrix has degree -1.

There are fifteen partitions of four players. Eight nondiscrete partitions
already fail the necessary first-order block row-sum identities. The other
six have these explicit block-constant hazard witnesses, with the displayed
nonzero difference Delta_j-Delta_i:

| Partition | q | (i,j) | Difference |
|---|---|---|---:|
| 01 / 2 / 3 | (0,0,1/2,0) | (0,1) | -115/1092 |
| 12 / 03 | (1/2,0,0,1/2) | (1,2) | 5/16 |
| 02 / 13 | (0,1/2,0,1/2) | (0,2) | 9/8 |
| 0 / 1 / 23 | (0,0,1/2,1/2) | (2,3) | -3/4 |
| 01 / 23 | (0,0,1/2,1/2) | (0,1) | -115/1456 |
| 0123 | (1/2,1/2,1/2,1/2) | (0,1) | -115/2496 |

Hence only the discrete partition is response-invariant. Every admissible
quotient is R0 of degree +1, yet the new half-ceiling producer applies.

### 9.2 Every proper-child raw domination test fails

Use the supplied child-extension notation: for S proper and k outside S,
the inequalities are V lambda>=b with lambda>=0. Rows N,F_A,J_A are

    N:   V_i=s_i,                         b=s_k;
    F_A: V_i=s_i-r_i(A),                  b=s_k-r_k(A);
    J_A: V_i=r_i(A+i)-r_i(A),             b=r_k(A+k)-r_k(A).

A nonnegative combination with V<=0 and b>0 refutes that outside row.
If 0 is not in S, use outsider 0 and row N: V=0 and b=1. All those child
singletons are zero, so the positive-child-singleton relaxation is unavailable.
For the seven other proper child sets, the following exact certificates
suffice. V is ordered by increasing child label.

| Child S | Outsider | Row combination | V | b |
|---|---:|---|---|---:|
| 0 | 1 | J_0 | (0) | 1 |
| 01 | 2 | F_0 | (0,-3) | 1 |
| 02 | 1 | J_0+2F_02 | (-8/3,-7) | 1 |
| 012 | 3 | F_02 | (-4/3,0,-8) | 1 |
| 03 | 1 | J_0 | (0,-3) | 1 |
| 013 | 2 | J_01 | (0,0,-2) | 3 |
| 023 | 1 | J_0+2F_02 | (-8/3,-7,-1) | 1 |

These latter certificates use only F and J, so omitting N does not repair
them. All fourteen proper-child raw tests fail. This does not rule out a
successful extension of a particular child profile: (23) itself has player
3 Never. It rules out the specified universal raw domination certificates.

### 9.3 No pure equilibrium, no payoff-exclusion entrance

In coalition bitmask order 1,...,15, an improving toggle is supplied by owners

    1,0,2,0,3,2,0,0,3,2,0,0,2,3,0,

with respective gains

    1,1,3,7/3,8,1,6,2,3,5,6,2,9,5,6.

Every deletion retains a nonempty coalition, and for singleton coalitions
we use an outside join. Thus these deviations work at the earliest date of
any deterministic profile, regardless of hidden later clocks. All Never
is defeated by player 0. There is no pure terminal equilibrium.

The vector in (23) is strictly above s coordinatewise. It therefore refutes
strict deficit, every weak-subset payoff exclusion, and nonconcentrated
weighted payoff exclusion. The paired Gamma has reciprocal comparisons of
the same sign, so it also fails the escort sign necessity for balanced
singleton cycles identified in the supplied child-extension manuscript.
The direct computation, not a numerical grid failure, establishes each
listed comparison.

## 10. A full reward neighborhood and the new remaining condition

Every table at entrywise distance delta<1/100 from the displayed table
satisfies the strict theorem. Here is a quantitative check.

Its new singleton matrix is Gamma+E with ||E||_infinity<=6delta in induced
row-sum norm. Since ||Gamma^{-1}||_infinity=1, the Neumann estimate gives

    ||(Gamma+E)^{-1}-Gamma^{-1}||_infinity
        <=6delta/(1-6delta)<2/15.

Every original inverse entry is at least 2/15, so the inverse remains
strictly positive. The same bound along the perturbation segment preserves
the positive determinant sign.

The lower ranking margins lose at most 2delta. Each half-ceiling Bernstein
coefficient has raw reward l1 coefficient norm at most two. More explicitly,
those nine norms are

    [1,3/2,2; 3/2,7/4,2; 2,2,2].

This follows by applying (6) to each of the fifteen reward-coordinate basis
vectors, and is checked exactly by the script. The negative coefficient
margin is at least 1/12 and therefore loses at most 2delta<1/12. Thus every
strict condition survives. No symmetry is preserved or required.

With the paired singleton matrix fixed, recipients 2 and 3 have twenty-two
wholly unrestricted nonsingleton coordinates. The remaining twenty-two
collision coordinates may range over the nonempty open polyhedron defined
by strict (L),(B). All four singleton levels may be any signed numbers:
adding a constant to an entire recipient's terminal row preserves these
raw tests and Delta algebraically. This statement uses the theorem afresh
and is not an assertion that terminal-only translations preserve arbitrary
strategy payoffs with Never fixed.

The counterexample-facing consequence is exact: in the positive-determinant,
nonnegative-inverse matrix region, every hypothetical counterexample must
fail the weak half-ceiling raw test for every choice of the selected pair.
For the paired Gamma above, in particular, it must fail for both 01 and 23.
The stronger polynomial-face version is available when the Bernstein test
fails but the actual face sign can still be proved.

No argument here proves those guards, or an alternative consumer when they
fail, for every remaining table. The strict pivot-pressure nonmover-cap
problem is not solved by this construction. The advance is a guarded
row-permutation producer inside the full-degree-one, no-useful-quotient
region, not an unrestricted four-player existence theorem.

## 11. Sources, proof boundary, and Lean handoff

[1] M. Seetharama Gowda, *Applications of Degree Theory to Linear
Complementarity Problems*, Mathematics of Operations Research 18(4), 1993,
868–879, Section 2, printed pages 869–870. The componentwise-min convention,
R0 degree, right-hand-side invariance, and elementary Brouwer-degree
properties are classical inputs. Author-hosted original:
https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf.

The supplied manuscript *Stationary-response quotient degree escape for
quitting games* provides the comparison notion Delta_i(Ex)=Delta_j(Ex),
block-sum matrices, and its distinct quotient producer. The present proof
does not assume that identity. The supplied *Capped-clock deviation
domination and quiet extension* provides precisely the N,F,J tests rejected
above. The strict-inverse approximation in Section 7.1 is also proved in the
supplied inverse-positive and cycle-extension manuscripts; it is reproduced
here to keep the weak guard perturbation self-contained.

The repository source
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` was inspected
at commit `5aac30ad2553dadd5895dc79fbc4f1f5680d7570`. In particular:

- `quittingTerminalPayoff_stationary_eq_of_fixedPoint` identifies an
  absorbing fixed point with its actual terminal payoff;
- `quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash`
  gives exact full-cap equality with the boundary condition retained; and
- `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate` consumes
  an actual fixed point, endpoint Nash, and that boundary condition.

All boundary conditions are vacuous for the strict roots here because every
deleted opponent clock contracts. These declarations are existing consumers;
they do not supply the new crossed root. No compilation or axiom audit of a
new theorem was performed in this work, and no repository changes were made.

A narrow implementation would separate: the half-ceiling polynomial test;
the two lower/upper guards and reciprocal sign derivation; whole-space
crossed clipping; exclusion of every artificial boundary root; local R0
norm control and total degree; original stationary endpoint adaptation;
and the literal weak-table perturbation and full-cap reward estimate.
The root-existence conclusion must be proved by the degree argument, not
stored as an assumed certificate field.

The files `VERIFY_CROSSED_RESPONSE.py` and `EXACT_VERIFICATION_OUTPUT.txt`
record the actual finite checks. Running `python VERIFY_CROSSED_RESPONSE.py`
uses exact fractions and requires no third-party package. It verifies matrix
identities, the raw inequalities, the half-ceiling Bernstein arrays, the
rational root and complete caps, every partition comparison, every child
LP refutation, and the pure-toggle and payoff-exclusion comparisons. It
neither samples an infinite deviation class nor claims to mechanically
prove the Brouwer-degree existence argument.
